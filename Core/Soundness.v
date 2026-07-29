(** * Soundness — paper Theorem 4.1: every derivable triple is valid.

        Σ ⊢ₚ {{ Q }} P {{ R }}   ⟹   Σ ⊨ {{ Q }} P {{ R }}

    Per-rule obligations:
      1. conseq_sound        (proven)
      2. comm_done_sound     (proven)
      3. par_disjoint_sound
      4. comm_select_sound
      5. par_comp_sound
      6. branch_accum_sound
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Reals.Reals Lra.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import
  Syntax QuantumActions SemanticDomain Semantics Assertions WellFormed Rules
  TraceFacts.
Import ListNotations.

Section Soundness.
  Context {dim : nat} (Σ : interp dim).

  (* Keep assertion-level constants folded under simpl: the degree lemmas
     below rewrite against their folded forms. *)
  Local Arguments degree : simpl never.
  Local Arguments and_guard : simpl never.
  Local Arguments wp_unitary : simpl never.
  Local Arguments assertion_subst : simpl never.
  Local Arguments and_eq : simpl never.
  Local Arguments wp_meas : simpl never.
  Local Arguments total_degree : simpl never.

  (** ** 0. Execution preserves state legitimacy (term_preservation) ******

      [valid] promises the INPUT is a genuine state (WF + hermitian + PSD,
      paper p.4); the POST side of every rule needs the same for every
      member of the terminal ensembles the semantics produces.  This section
      proves the invariant: quantum actions are (sums of) K·ρ·K† maps and
      everything else never touches ρ.
  ********************************************************************)

  (** "r is a genuine quantum state", the three components bundled. **)
  Definition state_ok (st : cqstate dim) : Prop :=
    @WF_Matrix (2 ^ dim) (2 ^ dim) (snd st) /\
    @hermitian (2 ^ dim) (snd st) /\
    @positive_semidefinite (2 ^ dim) (snd st).

  Definition ensemble_ok (E : ensemble dim) : Prop := Forall state_ok E.
  Definition config_ok {A} (G : list (A * ensemble dim)) : Prop :=
    Forall (fun c => ensemble_ok (snd c)) G.

  (** The paper's quantum structure interprets U/M symbols by operators on
      the register (p.4); the [interp] record does not enforce that they are
      well-formed matrices, so preservation assumes it. **)
  Definition wf_interp : Prop :=
    (forall U qs, WF_Matrix (i_uu Σ U qs)) /\
    (forall M qs m, WF_Matrix (snd (i_mm Σ M qs) m)) /\
    (* the paper's measurement is the finite family {M_m}_{m∈T_M} (p.4):
       outside T_M there is no operator — Zero is its total-function
       rendering — and T_M is a set *)
    (forall M qs m, ~ In m (fst (i_mm Σ M qs)) ->
                    snd (i_mm Σ M qs) m = Zero) /\
    (forall M qs, NoDup (fst (i_mm Σ M qs))).

  (** Plumbing: ensembles/configs stay legitimate under map / flat_map /
      filter when the action on each member does. **)
  Lemma ensemble_ok_map : forall (g : cqstate dim -> cqstate dim) E,
      (forall st, state_ok st -> state_ok (g st)) ->
      ensemble_ok E -> ensemble_ok (map g E).
  Proof.
    intros g E Hg HE. unfold ensemble_ok in *. rewrite Forall_map.
    eapply Forall_impl; [| exact HE]. auto.
  Qed.

  Lemma ensemble_ok_flat_map : forall (g : cqstate dim -> list (cqstate dim)) E,
      (forall st, state_ok st -> Forall state_ok (g st)) ->
      ensemble_ok E -> ensemble_ok (flat_map g E).
  Proof.
    intros g E Hg HE. unfold ensemble_ok in *.
    induction HE; simpl; [constructor |].
    apply Forall_app; split; auto.
  Qed.

  Lemma Forall_filter_keep : forall {A} (P : A -> Prop) f (l : list A),
      Forall P l -> Forall P (filter f l).
  Proof.
    intros A P f l H. rewrite Forall_forall in *.
    intros x Hx. apply filter_In in Hx as [Hx _]. auto.
  Qed.

  Lemma config_ok_map :
    forall {A B} (h : A * ensemble dim -> B * ensemble dim) G,
      (forall c, ensemble_ok (snd c) -> ensemble_ok (snd (h c))) ->
      config_ok G -> config_ok (map h G).
  Proof.
    intros A B h G Hh HG. unfold config_ok in *. rewrite Forall_map.
    eapply Forall_impl; [| exact HG]. auto.
  Qed.

  (** Per-action closure, using the TraceFacts closure lemmas. **)
  Lemma state_ok_super : forall (K : Square (2 ^ dim)) s s' (r : qstate dim),
      WF_Matrix K -> state_ok (s, r) -> state_ok (s', super K r).
  Proof.
    intros K s s' r HK (H1 & H2 & H3). simpl in *.
    repeat split.
    - apply super_WF; auto.
    - apply super_hermitian; auto.
    - apply super_psd; auto.
  Qed.

  Lemma state_ok_init : forall q s (r : qstate dim),
      state_ok (s, r) -> state_ok (s, apply_init q r).
  Proof.
    intros q s r (H1 & H2 & H3). simpl in *. unfold apply_init.
    repeat split.
    - apply WF_plus; apply super_WF; auto with wf_db.
    - apply hermitian_plus; apply super_hermitian; auto.
    - apply psd_plus; apply super_psd; auto with wf_db.
  Qed.

  (** Preservation, one layer of the semantics at a time. **)
  Lemma local_step_preserves :
    wf_interp ->
    forall (L : lblock) (E : ensemble dim) (Gl : local_config dim),
      Σ ⊳ ‹ L, E › →ₗ Gl -> ensemble_ok E -> config_ok Gl.
  Proof.
    intros interp_ok L E Gl Hstep. induction Hstep; intros HokE.
    - (* skip *)   constructor; [exact HokE | constructor].
    - (* assign *) constructor; [| constructor]. simpl.
      apply ensemble_ok_map; auto. intros [s r] H. exact H.
    - (* init *)   constructor; [| constructor]. simpl.
      apply ensemble_ok_map; auto. intros [s r] H.
      apply state_ok_init; auto.
    - (* ugate *)  constructor; [| constructor]. simpl.
      apply ensemble_ok_map; auto. intros [s r] H.
      unfold apply_unitary. eapply state_ok_super; eauto.
      apply (proj1 interp_ok).
    - (* meas *)   constructor; [| constructor]. simpl.
      apply ensemble_ok_flat_map; auto. intros [s r] H.
      rewrite Forall_map. apply Forall_forall. intros m _.
      unfold apply_meas. eapply state_ok_super; eauto.
      apply (proj2 interp_ok).
    - (* seq *)    apply config_ok_map; auto.
      intros c Hc. destruct (fst c); exact Hc.
    - (* if *)     simpl. constructor; [| constructor; [| constructor]];
        simpl; apply Forall_filter_keep; exact HokE.
  Qed.

  Lemma distri_step_preserves :
    wf_interp ->
    forall (D : program) (E : ensemble dim) (G : distri_config dim),
      Σ ⊳ ‹ D, E › ⇝ G -> ensemble_ok E -> config_ok G.
  Proof.
    intros interp_ok D E G Hstep; induction Hstep; intros HokE.
    - (* ds_local *) apply config_ok_map.
      + intros c Hc. exact Hc.
      + eapply local_step_preserves; eauto.
    - (* ds_par_l *) apply config_ok_map; auto.
    - (* ds_par_r *) apply config_ok_map; auto.
    - (* ds_comm_lr — a classical store update never touches ρ *)
      constructor; [| constructor]. simpl.
      apply ensemble_ok_map; auto. intros [s0 r0] Hst. exact Hst.
    - (* ds_comm_rl *)
      constructor; [| constructor]. simpl.
      apply ensemble_ok_map; auto. intros [s0 r0] Hst. exact Hst.
  Qed.

  Lemma mixed_step_preserves :
    wf_interp ->
    forall G1 G2 : distri_config dim,
      mixed_step Σ G1 G2 -> config_ok G1 -> config_ok G2.
  Proof.
    intros interp_ok G1 G2 Hstep Hok.
    destruct Hstep as [G D E G0 G1' Hperm Hd].
    unfold config_ok in *.
    pose proof (Permutation_Forall Hperm Hok) as Hok'.
    inversion Hok' as [| ? ? HE HG0]; subst.
    apply Forall_filter_keep.
    apply Forall_app; split; auto.
    eapply distri_step_preserves; eauto.
  Qed.

  Lemma step_star_preserves :
    wf_interp ->
    forall G1 G2 : distri_config dim,
      step_star Σ G1 G2 -> config_ok G1 -> config_ok G2.
  Proof.
    intros interp_ok G1 G2 Hstar; induction Hstar; auto.
    intros Hok. apply IHHstar. eapply mixed_step_preserves; eauto.
  Qed.

  Lemma config_ok_collapse : forall G : distri_config dim,
      config_ok G -> ensemble_ok (collapse G).
  Proof.
    intros G HG. unfold collapse, ensemble_ok.
    induction HG; simpl; [constructor |].
    apply Forall_app; split; auto.
  Qed.

  (** The preservation lemma itself: legitimate in ⟹ legitimate out. **)
  Lemma term_preservation :
    wf_interp ->
    forall (P : program) s (r : qstate dim) (E : ensemble dim),
      @WF_Matrix (2 ^ dim) (2 ^ dim) r ->
      @hermitian (2 ^ dim) r ->
      @positive_semidefinite (2 ^ dim) r ->
      Term Σ P (s, r) E ->
      ensemble_ok E.
  Proof.
    intros interp_ok P s r E H1 H2 H3 (G & Hstar & _ & Hcoll).
    rewrite <- Hcoll. apply config_ok_collapse.
    eapply step_star_preserves; eauto.
    constructor; [| constructor]. simpl.
    constructor; [| constructor]. repeat split; assumption.
  Qed.

  (** ** 1. Conseq  ** **)
  Lemma conseq_sound :
    wf_interp ->
    forall (Q Q' R R' : assertion dim) (P : program),
      wf_assertion Σ R' ->
      Q' ⊨[Σ] Q ->
      Σ ⊨ {{ Q }} P {{ R }} ->
      R ⊨[Σ] R' ->
      Σ ⊨ {{ Q' }} P {{ R' }}.
  Proof.
    intros interp_ok Q Q' R R' P HwfR' Hpre Hv Hpost
           s r HWFr Hherm Hpsd Hh' Hd' E HTerm.
    assert (Hh : formula_holds Σ s (classical_part Q) = true)
      by (apply (proj1 Hpre); exact Hh').
    assert (Hd : defined_in Σ Q s)
      by (apply (proj1 (proj2 Hpre)); assumption).
    pose proof (Hv s r HWFr Hherm Hpsd Hh Hd E HTerm) as Hmain.
    pose proof (degree_entails_defined Σ Q' Q s r Hpre Hh' Hd' HWFr Hherm Hpsd)
      as Hin.
    pose proof (term_preservation interp_ok P s r E HWFr Hherm Hpsd HTerm) as HE.
    pose proof (total_degree_entails Σ R R' E Hpost HwfR' HE) as Hout.
    lra.
  Qed.

  (** ** 2. Comm-Done — {Q} ε_K ∥ … ∥ ε_K {Q}.  Every ⟨ₖ []⟩ leaf reads as
         ↓, so the row is stuck and already terminal: E = {(s,r)} and the
         trace inequality is an equality. *)

  Lemma all_comm_done_leaf :
    forall (a b : component) (P P' : program),
      replace_leaf a b P P' -> all_comm_done P -> a = comp_comm nil.
  Proof.
    intros a b P P' Hrl; induction Hrl; intro Hacd; inversion Hacd; subst; auto.
  Qed.

  Lemma comm_done_stuck :
    forall (PK : program),
      all_comm_done PK ->
      forall (E0 : ensemble dim) (G : distri_config dim),
        Σ ⊳ ‹ PK, E0 › ⇝ G -> False.
  Proof.
    intros PK Hacd; induction Hacd as [| P1 P2 Hacd1 IH1 Hacd2 IH2];
      intros E0 G Hstep.
    - (* leaf: reads as ↓, no rule applies *)
      inversion Hstep; subst; simpl in *; congruence.
    - (* ∥ node: subtree step (IH) or a rendezvous whose sender must be ε *)
      inversion Hstep; subst; eauto.
      + match goal with
        | Hrl : replace_leaf _ _ P1 _ |- _ =>
            pose proof (all_comm_done_leaf _ _ _ _ Hrl Hacd1); subst
        end;
        match goal with
        | Hrd : read_component (comp_comm nil) = _ |- _ =>
            simpl in Hrd; discriminate Hrd
        end.
      + match goal with
        | Hrl : replace_leaf _ _ P2 _ |- _ =>
            pose proof (all_comm_done_leaf _ _ _ _ Hrl Hacd2); subst
        end;
        match goal with
        | Hrd : read_component (comp_comm nil) = _ |- _ =>
            simpl in Hrd; discriminate Hrd
        end.
  Qed.

  Lemma comm_done_no_mixed_step :
    forall (PK : program) (E0 : ensemble dim) (G2 : distri_config dim),
      all_comm_done PK ->
      mixed_step Σ ({|| PK, E0 ||}) G2 -> False.
  Proof.
    intros PK E0 G2 Hacd Hstep.
    inversion Hstep as [G D E G0 G1 Hperm Hd]; subst.
    apply Permutation_length_1_inv in Hperm.
    injection Hperm as HD HE HG0. subst.
    eapply comm_done_stuck; eauto.
  Qed.

  Lemma comm_done_star_id :
    forall (PK : program) (E0 : ensemble dim) (G : distri_config dim),
      all_comm_done PK ->
      step_star Σ ({|| PK, E0 ||}) G -> G = {|| PK, E0 ||}.
  Proof.
    intros PK E0 G Hacd Hstar.
    inversion Hstar; subst; auto.
    exfalso. eapply comm_done_no_mixed_step; eauto.
  Qed.

  Lemma comm_done_sound : forall (Q : assertion dim) (PK : program),
      all_comm_done PK ->
      Σ ⊨ {{ Q }} PK {{ Q }}.
  Proof.
    intros Q PK Hacd s r HWFr Hherm Hpsd Hh Hd E HTerm.
    destruct HTerm as (G & Hstar & Hterm & Hcoll).
    apply comm_done_star_id in Hstar; auto. subst G.
    simpl in Hcoll. subst E.
    unfold total_degree. simpl. lra.
  Qed.

  (** ** 3a. Denotational ensemble semantics of local blocks — the bridge
         for [local_sound]: a one-leaf run collapses to [denote L E]
         (each case mirrors the corresponding [local_step] rule). *)

  Fixpoint denote (L : lblock) (E : ensemble dim) : ensemble dim :=
    match L with
    | l_skip       => E
    | l_assign x e => map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E
    | l_init q     => map (fun '(s,r) => (s, apply_init q r)) E
    | l_ugate U qs => map (fun '(s,r) => (s, apply_unitary (i_uu Σ U qs) r)) E
    | l_meas x M qs =>
        flat_map (fun '(s,r) =>
          map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r))
              (fst (i_mm Σ M qs))) E
    | l_seq L1 L2  => denote L2 (denote L1 E)
    | l_if b L1 L0 =>
        denote L1 (ensemble_filter (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E)
        ++ denote L0 (ensemble_filter (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E)
    end.

  Definition residual_denote (R : residual) (E : ensemble dim) : ensemble dim :=
    match R with r_done => E | r_more L => denote L E end.

  Lemma denote_nil : forall L, denote L nil = nil.
  Proof.
    induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      simpl; try reflexivity.
    - now rewrite IH1, IH2.
    - unfold ensemble_filter; simpl. fold (cqstate dim).
      now rewrite IH1, IH0.
  Qed.

  Lemma permutation_filter :
    forall (A : Type) (f : A -> bool) (l l' : list A),
      Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof.
    intros A f l l' Hp; induction Hp; simpl.
    - apply Permutation_refl.
    - destruct (f x); auto using perm_skip.
    - destruct (f x), (f y); simpl; auto using perm_swap, Permutation_refl.
    - eauto using Permutation_trans.
  Qed.

  Lemma permutation_flat_map :
    forall (A B : Type) (f : A -> list B) (l l' : list A),
      Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
  Proof.
    intros A B f l l' Hp; induction Hp; simpl.
    - apply Permutation_refl.
    - now apply Permutation_app_head.
    - apply Permutation_app_swap_app.
    - eauto using Permutation_trans.
  Qed.

  Lemma denote_perm : forall L (E E' : ensemble dim),
      Permutation E E' -> Permutation (denote L E) (denote L E').
  Proof.
    induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intros E E' Hp; simpl.
    - exact Hp.
    - now apply Permutation_map.
    - now apply Permutation_map.
    - now apply Permutation_map.
    - now apply permutation_flat_map.
    - now apply IH2, IH1.
    - apply Permutation_app; [apply IH1 | apply IH0];
        unfold ensemble_filter; now apply permutation_filter.
  Qed.

  Lemma denote_app : forall L (E1 E2 : ensemble dim),
      Permutation (denote L (E1 ++ E2)) (denote L E1 ++ denote L E2).
  Proof.
    induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intros E1 E2; simpl.
    - apply Permutation_refl.
    - rewrite map_app; apply Permutation_refl.
    - rewrite map_app; apply Permutation_refl.
    - rewrite map_app; apply Permutation_refl.
    - rewrite flat_map_app; apply Permutation_refl.
    - eapply Permutation_trans; [apply denote_perm, IH1 | apply IH2].
    - unfold ensemble_filter; rewrite !filter_app.
      eapply Permutation_trans.
      + apply Permutation_app; [apply IH1 | apply IH0].
      + rewrite <- !app_assoc. apply Permutation_app_head.
        apply Permutation_app_swap_app.
  Qed.

  Lemma denote_flat_map :
    forall L (G : local_config dim),
      Permutation
        (flat_map (fun c => denote L (residual_denote (fst c) (snd c))) G)
        (denote L (flat_map (fun c => residual_denote (fst c) (snd c)) G)).
  Proof.
    intros L G; induction G as [| c G' IH]; simpl.
    - rewrite denote_nil. apply Permutation_refl.
    - eapply Permutation_trans.
      + apply Permutation_app_head, IH.
      + apply Permutation_sym, denote_app.
  Qed.

  (** One local step preserves the denotation. *)
  Lemma local_step_denote :
    forall (L : lblock) (E : ensemble dim) (Gl : local_config dim),
      Σ ⊳ ‹ L, E › →ₗ Gl ->
      Permutation (flat_map (fun c => residual_denote (fst c) (snd c)) Gl)
                  (denote L E).
  Proof.
    intros L E Gl Hstep; induction Hstep; simpl.
    - rewrite app_nil_r. apply Permutation_refl.
    - rewrite app_nil_r. apply Permutation_refl.
    - rewrite app_nil_r. apply Permutation_refl.
    - rewrite app_nil_r. apply Permutation_refl.
    - rewrite app_nil_r. apply Permutation_refl.
    - (* seq *)
      rewrite flat_map_concat_map, map_map.
      rewrite map_ext_in with
        (g := fun c => denote L2 (residual_denote (fst c) (snd c))).
      2:{ intros [R E'] _. destruct R; reflexivity. }
      rewrite <- flat_map_concat_map.
      eapply Permutation_trans.
      + apply denote_flat_map.
      + apply denote_perm. exact IHHstep.
    - (* if *)
      rewrite app_nil_r. apply Permutation_refl.
  Qed.

  Lemma total_degree_perm :
    forall (A : assertion dim) (E E' : ensemble dim),
      Permutation E E' -> total_degree Σ A E = total_degree Σ A E'.
  Proof.
    intros A E E' Hp; unfold total_degree; induction Hp; simpl; lra.
  Qed.

  (** ** 3b. One-leaf adequacy: a solo local block's terminal collapse IS
         its denotation.  [leaf_shape] is the execution invariant of
         one-leaf programs; [pdenote] runs a component to completion. *)

  Definition leaf_shape (P : program) : Prop :=
    exists C, P = pg_comp C /\
      (read_component C = terminated \/
       exists L', read_component C = phase (r_more L') nil terminated).

  Definition pdenote (P : program) (E : ensemble dim) : ensemble dim :=
    match P with
    | pg_comp C =>
        match read_component C with
        | terminated            => E
        | phase r_done _ _      => E
        | phase (r_more L') _ _ => denote L' E
        end
    | pg_par _ _ => E
    end.

  Definition cdenote (G : distri_config dim) : ensemble dim :=
    flat_map (fun c => pdenote (fst c) (snd c)) G.

  Lemma pdenote_nil : forall P, pdenote P nil = nil.
  Proof.
    intros [C | P1 P2]; simpl; [| reflexivity].
    destruct (read_component C) as [| R K S]; [reflexivity |].
    destruct R as [| L']; [reflexivity | apply denote_nil].
  Qed.

  Lemma cdenote_norm : forall G, cdenote (norm G) = cdenote G.
  Proof.
    intros G; induction G as [| [P E] G' IH]; [reflexivity |].
    unfold norm, cdenote in *; simpl.
    destruct E as [| st E']; simpl.
    - rewrite IH, pdenote_nil. reflexivity.
    - now rewrite IH.
  Qed.

  Lemma cdenote_app : forall G1 G2 : distri_config dim,
      cdenote (G1 ⊎ G2) = cdenote G1 ++ cdenote G2.
  Proof. intros; unfold cdenote; apply flat_map_app. Qed.

  Lemma one_leaf_mixed_denote :
    forall (G G' : distri_config dim),
      mixed_step Σ G G' ->
      Forall (fun c => leaf_shape (fst c)) G ->
      Forall (fun c => leaf_shape (fst c)) G'
      /\ Permutation (cdenote G') (cdenote G).
  Proof.
    intros G G' Hstep Hleafy.
    destruct Hstep as [G D E G0 G1 Hperm Hd].
    pose proof (Permutation_Forall Hperm Hleafy) as Hleafy'.
    inversion Hleafy' as [| c G0' HD HG0]; subst.
    simpl in HD. destruct HD as (C & HDC & Hread). subst D.
    inversion Hd; subst.
    match goal with
    | Hr : read_component _ = phase (r_more _) _ _ |- _ => rename Hr into Hrd
    end.
    match goal with
    | Hl : Σ ⊳ ‹ _, _ › →ₗ _ |- _ => rename Hl into Hloc
    end.
    destruct Hread as [Hread | (L' & Hread)]; rewrite Hread in Hrd;
      [discriminate |].
    injection Hrd as HL HK HS. subst.
    assert (HG1 : forall Gl0 : local_config dim,
               cdenote (map (fun c =>
                 (pg_comp (comp_proc (advance (fst c) nil terminated)), snd c)) Gl0)
               = flat_map (fun c => residual_denote (fst c) (snd c)) Gl0).
    { intros Gl0. unfold cdenote. rewrite flat_map_concat_map, map_map.
      rewrite map_ext_in with (g := fun c => residual_denote (fst c) (snd c)).
      2:{ intros [R E'] _. destruct R; reflexivity. }
      now rewrite <- flat_map_concat_map. }
    split.
    - apply Forall_filter_keep. apply Forall_app. split; [| exact HG0].
      rewrite Forall_map. apply Forall_forall. intros [R E'] _. simpl.
      eexists. split; [reflexivity |].
      destruct R; simpl.
      + left. reflexivity.
      + right. eexists. reflexivity.
    - rewrite cdenote_norm, cdenote_app, HG1.
      eapply Permutation_trans.
      + apply Permutation_app_tail. eapply local_step_denote; eassumption.
      + apply Permutation_sym.
        eapply Permutation_trans.
        * unfold cdenote; apply permutation_flat_map; exact Hperm.
        * unfold cdenote; simpl. rewrite Hread. apply Permutation_refl.
  Qed.

  Lemma one_leaf_star_denote :
    forall (G G' : distri_config dim),
      step_star Σ G G' ->
      Forall (fun c => leaf_shape (fst c)) G ->
      Forall (fun c => leaf_shape (fst c)) G'
      /\ Permutation (cdenote G') (cdenote G).
  Proof.
    intros G G' Hstar; induction Hstar as [G | G1 G2 G3 Hmix Hstar IH];
      intros Hl.
    - split; [assumption | apply Permutation_refl].
    - destruct (one_leaf_mixed_denote _ _ Hmix Hl) as [Hl2 Hp2].
      destruct (IH Hl2) as [Hl3 Hp3].
      split; [assumption | eapply Permutation_trans; eauto].
  Qed.

  Lemma terminal_cdenote :
    forall (G : distri_config dim),
      terminal G -> cdenote G = collapse G.
  Proof.
    intros G Hterm; unfold terminal in Hterm.
    induction Hterm as [| [P E] G' HP HF IH]; [reflexivity |].
    unfold cdenote, collapse in *; simpl. rewrite IH. f_equal.
    destruct P as [C | P1 P2]; simpl; [| reflexivity].
    simpl in HP. unfold comp_terminated in HP. now rewrite HP.
  Qed.

  Lemma one_leaf_adequacy :
    forall (L : lblock) (st : cqstate dim) (E : ensemble dim),
      Term Σ (⟨ₗ L ⟩) st E ->
      Permutation E (denote L (st :: nil)).
  Proof.
    intros L st E (G & Hstar & Hterm & Hcoll).
    assert (Hl0 : Forall (fun c => leaf_shape (fst c))
                    ({|| ⟨ₗ L ⟩, st :: nil ||})).
    { constructor; [| constructor]. simpl.
      exists (comp_local L). split; [reflexivity |].
      right. exists L. reflexivity. }
    destruct (one_leaf_star_denote _ _ Hstar Hl0) as [_ Hp].
    rewrite (terminal_cdenote _ Hterm) in Hp.
    rewrite Hcoll in Hp.
    unfold cdenote in Hp; simpl in Hp.
    rewrite app_nil_r in Hp. exact Hp.
  Qed.

  (** ** 3. Par-Disjoint-MP.  Route: [local_sound] is the one-leaf base
         case; then wf ⟹ DisjMP (Thm 2.1) ⟹ interference freedom (Lemma 1)
         normalises every interleaving to the [locals_seq]
         sequentialisation. *)

  (** [denote] preserves state legitimacy — the seq case of [denote_sound]
      threads [ensemble_ok] through the intermediate ensemble. *)
  Lemma denote_ok :
    wf_interp ->
    forall (L : lblock) (E : ensemble dim),
      ensemble_ok E -> ensemble_ok (denote L E).
  Proof.
    intros interp_ok L;
      induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intros E HokE; simpl.
    - exact HokE.
    - apply ensemble_ok_map; auto. intros [s r] H. exact H.
    - apply ensemble_ok_map; auto. intros [s r] H. apply state_ok_init; auto.
    - apply ensemble_ok_map; auto. intros [s r] H.
      unfold apply_unitary. eapply state_ok_super; eauto.
      apply (proj1 interp_ok).
    - apply ensemble_ok_flat_map; auto. intros [s r] H.
      rewrite Forall_map. apply Forall_forall. intros m _.
      unfold apply_meas. eapply state_ok_super; eauto.
      apply (proj2 interp_ok).
    - apply IH2, IH1, HokE.
    - unfold ensemble_ok. apply Forall_app. split.
      + apply IH1. unfold ensemble_ok, ensemble_filter.
        apply Forall_filter_keep. exact HokE.
      + apply IH0. unfold ensemble_ok, ensemble_filter.
        apply Forall_filter_keep. exact HokE.
  Qed.

  (** Ensemble-level degree bookkeeping for [denote_sound]. *)
  Lemma total_degree_app : forall (Q : assertion dim) (E1 E2 : ensemble dim),
      total_degree Σ Q (E1 ++ E2)
      = (total_degree Σ Q E1 + total_degree Σ Q E2)%R.
  Proof.
    intros Q E1 E2; unfold total_degree;
      induction E1 as [| st E1' IH]; simpl; [lra | rewrite IH; lra].
  Qed.

  Lemma total_degree_nonneg : forall (Q : assertion dim) (E : ensemble dim),
      wf_assertion Σ Q -> ensemble_ok E -> (0 <= total_degree Σ Q E)%R.
  Proof.
    intros Q E Hwf Hok; unfold total_degree;
      induction Hok as [| [s r] E' Hst Hok' IH]; simpl; [lra |].
    destruct Hst as (H1 & H2 & H3).
    apply Rplus_le_le_0_compat; [| exact IH].
    apply degree_nonneg; assumption.
  Qed.

  (** The If split: an ensemble's degree against Q is the sum of the two
      guarded degrees on the two filtered halves. *)
  Lemma total_degree_guard_split :
    forall (Q : assertion dim) (b : bexpr) (E : ensemble dim),
      total_degree Σ Q E
      = (total_degree Σ (and_guard Q b true)
           (ensemble_filter (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E)
         + total_degree Σ (and_guard Q b false)
             (ensemble_filter (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E))%R.
  Proof.
    intros Q b E; unfold total_degree, ensemble_filter;
      induction E as [| [s r] E' IH]; simpl; [ring |].
    destruct (eval_bool (i_fn Σ) (i_rl Σ) s b) eqn:Hb; simpl.
    - assert (Hd : degree Σ (and_guard Q b true) (s, r) = degree Σ Q (s, r)).
      { unfold degree, and_guard; simpl. rewrite Hb.
        destruct (formula_holds Σ s (classical_part Q)); reflexivity. }
      rewrite Hd, IH. ring.
    - assert (Hd : degree Σ (and_guard Q b false) (s, r) = degree Σ Q (s, r)).
      { unfold degree, and_guard; simpl. rewrite Hb.
        destruct (formula_holds Σ s (classical_part Q)); reflexivity. }
      rewrite Hd, IH. ring.
  Qed.

  (** Assign / Unitary transport, pointwise lemmas summed over E. *)
  Lemma total_degree_subst_map :
    forall (Q : assertion dim) (x : var) (e : expr) (E : ensemble dim),
      total_degree Σ (assertion_subst Q x e) E
      = total_degree Σ Q
          (map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E).
  Proof.
    intros Q x e E; unfold total_degree;
      induction E as [| [s r] E' IH]; simpl; [reflexivity |].
    rewrite IH, degree_subst. reflexivity.
  Qed.

  Lemma degree_wp_unitary :
    forall (Q : assertion dim) (U : Square (2 ^ dim)) (s : store) (r : qstate dim),
      degree Σ (wp_unitary U Q) (s, r) = degree Σ Q (s, apply_unitary U r).
  Proof.
    intros Q U s r. unfold degree, wp_unitary; simpl.
    destruct (formula_holds Σ s (classical_part Q)); [| reflexivity].
    destruct (qpred_denote Σ s (quantum_part Q)) as [M|]; simpl; [| reflexivity].
    f_equal. unfold apply_unitary, super.
    rewrite !Mmult_assoc. rewrite trace_mmult_comm. rewrite !Mmult_assoc.
    reflexivity.
  Qed.

  Lemma total_degree_wp_unitary_map :
    forall (Q : assertion dim) (U : Square (2 ^ dim)) (E : ensemble dim),
      total_degree Σ (wp_unitary U Q) E
      = total_degree Σ Q (map (fun '(s,r) => (s, apply_unitary U r)) E).
  Proof.
    intros Q U E; unfold total_degree;
      induction E as [| [s r] E' IH]; simpl; [reflexivity |].
    rewrite IH, degree_wp_unitary. reflexivity.
  Qed.

  (** The Conseq split.  [guards_pass Q st]: both of Q's guards pass at st
      (formula holds, predicate defined); elsewhere Q's degree is 0. *)
  Definition guards_pass (Q : assertion dim) (st : cqstate dim) : bool :=
    formula_holds Σ (fst st) (classical_part Q)
    && match qpred_denote Σ (fst st) (quantum_part Q) with
       | Some _ => true | None => false end.

  Lemma filter_split_perm : forall (A : Type) (f : A -> bool) (l : list A),
      Permutation l (filter f l ++ filter (fun a => negb (f a)) l).
  Proof.
    intros A f l; induction l as [| a l' IH]; simpl; [apply Permutation_refl |].
    destruct (f a); simpl.
    - apply perm_skip, IH.
    - eapply Permutation_trans; [apply perm_skip, IH |].
      apply Permutation_middle.
  Qed.

  Lemma total_degree_guards_fail :
    forall (Q : assertion dim) (E : ensemble dim),
      total_degree Σ Q (filter (fun st => negb (guards_pass Q st)) E) = 0%R.
  Proof.
    intros Q E; unfold total_degree;
      induction E as [| [s r] E' IH]; simpl; [reflexivity |].
    destruct (guards_pass Q (s, r)) eqn:Hl; simpl; [exact IH |].
    assert (Hd : degree Σ Q (s, r) = 0%R).
    { unfold guards_pass in Hl; simpl in Hl. unfold degree.
      destruct (formula_holds Σ s (classical_part Q)); simpl in Hl;
        [| reflexivity].
      destruct (qpred_denote Σ s (quantum_part Q)) as [M|];
        [discriminate | reflexivity]. }
    rewrite Hd, IH. ring.
  Qed.

  Lemma total_degree_entails_pass :
    forall (Q' Q : assertion dim) (E : ensemble dim),
      Q' ⊨[Σ] Q ->
      ensemble_ok E ->
      total_degree Σ Q' (filter (guards_pass Q') E)
      <= total_degree Σ Q (filter (guards_pass Q') E).
  Proof.
    intros Q' Q E Hent Hok; unfold total_degree.
    induction Hok as [| [s r] E' Hst Hok' IH]; simpl; [lra |].
    destruct (guards_pass Q' (s, r)) eqn:Hl; simpl; [| exact IH].
    unfold guards_pass in Hl; simpl in Hl.
    apply andb_prop in Hl as [Hφ Hd].
    destruct Hst as (H1 & H2 & H3).
    assert (Hdef : defined_in Σ Q' s).
    { unfold defined_in.
      destruct (qpred_denote Σ s (quantum_part Q')) as [M|];
        [eauto | discriminate]. }
    apply Rplus_le_compat; [| exact IH].
    apply degree_entails_defined; assumption.
  Qed.

  Lemma total_degree_cons : forall (Q : assertion dim) st (E : ensemble dim),
      total_degree Σ Q (st :: E) = (degree Σ Q st + total_degree Σ Q E)%R.
  Proof. reflexivity. Qed.

  (** Meas case.  A branch whose outcome m differs from s y fails the x = y
      guard, so it contributes exactly 0. *)
  Lemma degree_and_eq_miss :
    forall (Q : assertion dim) (x y : var) (s : store) (m : nat)
           (r' : qstate dim),
      y <> x -> m <> s y ->
      degree Σ (and_eq Q x y) (s [ x |-> m ], r') = 0%R.
  Proof.
    intros Q x y s m r' Hyx Hm.
    unfold degree, and_eq; simpl.
    unfold store_update. rewrite Nat.eqb_refl.
    rewrite (proj2 (Nat.eqb_neq x y))
      by (intro He; apply Hyx; symmetry; exact He).
    rewrite (proj2 (Nat.eqb_neq m (s y)) Hm), andb_false_r.
    reflexivity.
  Qed.

  Lemma total_degree_and_eq_miss :
    forall (Q : assertion dim) (x y : var) (M : msym) (qs : list qvar)
           (s : store) (r : qstate dim) (lst : list nat),
      y <> x ->
      (forall m, In m lst -> m <> s y) ->
      total_degree Σ (and_eq Q x y)
        (map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r)) lst)
      = 0%R.
  Proof.
    intros Q x y M qs s r lst Hyx Hmiss;
      induction lst as [| m lst' IH]; [reflexivity |].
    cbn [map]. rewrite total_degree_cons.
    rewrite (degree_and_eq_miss Q x y s m _ Hyx (Hmiss m (or_introl eq_refl))).
    rewrite IH; [ring | intros m' Hm'; apply Hmiss; right; exact Hm'].
  Qed.

  (** The branch whose outcome IS s y balances the pre-effect exactly. *)
  Lemma degree_meas_hit :
    forall (Q : assertion dim) (x y : var) (M : msym) (qs : list qvar)
           (s : store) (r : qstate dim),
      y <> x ->
      degree Σ (and_eq Q x y)
        (s [ x |-> s y ], apply_meas (i_mm Σ M qs) (s y) r)
      = degree Σ (wp_meas Σ M qs y (assertion_subst Q x (e_var y))) (s, r).
  Proof.
    intros Q x y M qs s r Hyx.
    unfold degree, and_eq, wp_meas, assertion_subst; simpl.
    rewrite formula_holds_subst, qpred_denote_subst. simpl.
    assert (Hx : (s [ x |-> s y ]) x = s y)
      by (unfold store_update; rewrite Nat.eqb_refl; reflexivity).
    assert (Hy : (s [ x |-> s y ]) y = s y)
      by (unfold store_update;
          rewrite (proj2 (Nat.eqb_neq x y))
            by (intro He; apply Hyx; symmetry; exact He);
          reflexivity).
    rewrite Hx, Hy, Nat.eqb_refl, andb_true_r.
    destruct (formula_holds Σ (s [ x |-> s y ]) (classical_part Q));
      [| reflexivity].
    destruct (qpred_denote Σ (s [ x |-> s y ]) (quantum_part Q)) as [N|];
      [| reflexivity].
    f_equal. unfold apply_meas, super.
    rewrite !Mmult_assoc.
    rewrite (trace_mmult_comm ((snd (i_mm Σ M qs) (s y))†)).
    rewrite !Mmult_assoc. reflexivity.
  Qed.

  (** Pointwise: pre-effect degree = summed branch degrees.  If s y ∉ T_M
      both sides are 0 (the off-family operator is Zero); if s y ∈ T_M the
      matching branch balances and the rest vanish (T_M is a set). *)
  Lemma degree_meas_pointwise :
    wf_interp ->
    forall (Q : assertion dim) (x y : var) (M : msym) (qs : list qvar)
           (s : store) (r : qstate dim),
      y <> x ->
      degree Σ (wp_meas Σ M qs y (assertion_subst Q x (e_var y))) (s, r)
      = total_degree Σ (and_eq Q x y)
          (map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r))
               (fst (i_mm Σ M qs))).
  Proof.
    intros interp_ok Q x y M qs s r Hyx.
    destruct interp_ok as (HU & HM & Hzero & Hnodup).
    destruct (in_dec Nat.eq_dec (s y) (fst (i_mm Σ M qs))) as [Hin | Hout].
    - destruct (in_split _ _ Hin) as (T1 & T2 & HT).
      pose proof (Hnodup M qs) as Hnd. rewrite HT in Hnd.
      pose proof (NoDup_remove_2 _ _ _ Hnd) as Hnotin.
      assert (Hm1 : forall m, In m T1 -> m <> s y).
      { intros m Hm He; subst m; apply Hnotin, in_or_app; left; exact Hm. }
      assert (Hm2 : forall m, In m T2 -> m <> s y).
      { intros m Hm He; subst m; apply Hnotin, in_or_app; right; exact Hm. }
      rewrite HT, map_app, total_degree_app.
      change (@map nat) with (@map val).
      cbn [map]. rewrite total_degree_cons.
      rewrite (total_degree_and_eq_miss Q x y M qs s r T1 Hyx Hm1).
      rewrite (total_degree_and_eq_miss Q x y M qs s r T2 Hyx Hm2).
      rewrite (degree_meas_hit Q x y M qs s r Hyx).
      ring.
    - rewrite (total_degree_and_eq_miss Q x y M qs s r _ Hyx).
      2:{ intros m Hm He; subst m; exact (Hout Hm). }
      unfold degree, wp_meas, assertion_subst; simpl.
      rewrite (Hzero M qs (s y) Hout).
      destruct (formula_holds Σ s
                  (formula_subst (classical_part Q) x (e_var y)));
        [| reflexivity].
      destruct (qpred_denote Σ s
                  (qpred_subst (quantum_part Q) x (e_var y))) as [N|];
        [| reflexivity].
      rewrite zero_adjoint_eq, Mmult_0_l, Mmult_0_r, Mmult_0_l, trace_0_r.
      reflexivity.
  Qed.

  Lemma total_degree_meas_flat :
    wf_interp ->
    forall (Q : assertion dim) (x y : var) (M : msym) (qs : list qvar)
           (E : ensemble dim),
      y <> x ->
      total_degree Σ (wp_meas Σ M qs y (assertion_subst Q x (e_var y))) E
      = total_degree Σ (and_eq Q x y)
          (flat_map (fun '(s,r) =>
             map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r))
                 (fst (i_mm Σ M qs))) E).
  Proof.
    intros interp_ok Q x y M qs E Hyx;
      induction E as [| [s r] E' IH]; simpl; [reflexivity |].
    rewrite total_degree_cons, total_degree_app.
    rewrite <- (degree_meas_pointwise interp_ok Q x y M qs s r Hyx).
    rewrite IH. reflexivity.
  Qed.

  (** The Hoare half of [local_sound], at the ensemble level. *)
  Lemma denote_sound :
    wf_interp ->
    forall (Q R : assertion dim) (L : lblock),
      Σ ⊢ₗ {{ Q }} L {{ R }} ->
      forall E, ensemble_ok E ->
        total_degree Σ Q E <= total_degree Σ R (denote L E).
  Proof.
    intros interp_ok Q R L Hd.
    induction Hd as
      [ Q0
      | Q0 x e
      | Q0 U qs
      | Q0 x M qs y Hyx Hyfree
      | Q1 Q2 Q3 L1 L2 D1 IH1 D2 IH2
      | Q0 R0 b L1 L0 D1 IH1 D0 IH0
      | Q0 Q' R0 R' L0 Hent1 D IH Hent2 Hwf
      ]; intros E HokE; simpl.
    - (* skip *) apply Rle_refl.
    - (* assign *) rewrite total_degree_subst_map. apply Rle_refl.
    - (* unitary *) rewrite total_degree_wp_unitary_map. apply Rle_refl.
    - (* meas *)
      rewrite (total_degree_meas_flat interp_ok Q0 x y M qs E Hyx).
      apply Rle_refl.
    - (* seq *)
      eapply Rle_trans; [apply IH1; exact HokE |].
      apply IH2, denote_ok; auto.
    - (* if *)
      rewrite (total_degree_guard_split Q0 b E), total_degree_app.
      apply Rplus_le_compat.
      + apply IH1. unfold ensemble_ok, ensemble_filter.
        apply Forall_filter_keep. exact HokE.
      + apply IH0. unfold ensemble_ok, ensemble_filter.
        apply Forall_filter_keep. exact HokE.
    - (* conseq — split E on Q''s guards; the guard-failing part costs
         nothing on the left and is ≥ 0 on the right by wf_assertion R' *)
      pose proof (filter_split_perm _ (guards_pass Q') E) as Hsplit.
      set (Epass := filter (guards_pass Q') E) in *.
      set (Efail := filter (fun st => negb (guards_pass Q' st)) E) in *.
      assert (HokEpass : ensemble_ok Epass)
        by (unfold Epass, ensemble_ok; apply Forall_filter_keep; exact HokE).
      assert (HokEfail : ensemble_ok Efail)
        by (unfold Efail, ensemble_ok; apply Forall_filter_keep; exact HokE).
      assert (Hd0 : total_degree Σ Q' Efail = 0%R)
        by (unfold Efail; apply total_degree_guards_fail).
      assert (Hpre : (total_degree Σ Q' Epass <= total_degree Σ Q0 Epass)%R)
        by (unfold Epass; apply total_degree_entails_pass; assumption).
      pose proof (IH Epass HokEpass) as Hmid.
      pose proof (total_degree_entails Σ R0 R' (denote L0 Epass) Hent2 Hwf
                    (denote_ok interp_ok L0 Epass HokEpass)) as Hpost.
      pose proof (total_degree_nonneg R' (denote L0 Efail) Hwf
                    (denote_ok interp_ok L0 Efail HokEfail)) as Hdead.
      rewrite (total_degree_perm Q' _ _ Hsplit), total_degree_app, Hd0.
      rewrite (total_degree_perm R' _ _ (denote_perm L0 _ _ Hsplit)).
      rewrite (total_degree_perm R' _ _ (denote_app L0 Epass Efail)).
      rewrite total_degree_app.
      rewrite Rplus_0_r.
      eapply Rle_trans; [exact Hpre |].
      eapply Rle_trans; [exact Hmid |].
      eapply Rle_trans; [exact Hpost |].
      rewrite <- (Rplus_0_r (total_degree Σ R' (denote L0 Epass))) at 1.
      apply Rplus_le_compat_l. exact Hdead.
  Qed.

  Lemma local_sound :
    wf_interp ->
    forall (Q R : assertion dim) (L : lblock),
      Σ ⊢ₗ {{ Q }} L {{ R }} ->
      Σ ⊨ {{ Q }} (⟨ₗ L ⟩) {{ R }}.
  Proof.
    intros interp_ok Q R L Hd s r HWFr Hherm Hpsd Hh Hdef E HTerm.
    apply one_leaf_adequacy in HTerm.
    rewrite (total_degree_perm R _ _ HTerm).
    assert (Hok : ensemble_ok ((s, r) :: nil))
      by (constructor; [repeat split; assumption | constructor]).
    pose proof (denote_sound interp_ok Q R L Hd ((s, r) :: nil) Hok) as Hle.
    unfold total_degree in Hle |- *. cbn [fold_right map] in Hle.
    rewrite Rplus_0_r in Hle. exact Hle.
  Qed.

  Lemma par_disjoint_sound :
    forall (Q R : assertion dim) (PD : program) (Dseq : lblock),
      wf_program PD ->
      locals_seq PD Dseq ->
      Σ ⊢ₗ {{ Q }} Dseq {{ R }} ->
      Σ ⊨ {{ Q }} PD {{ R }}.
  Admitted.

  (** ** 4. Comm-Select-MP.  One rendezvous c!e ⋈ c?x behaves as x := e;
         Lemma 2 commutes the selected rendezvous first. *)
  Lemma comm_select_sound :
    forall (Q R : assertion dim) (PK P1 PK' : program)
           (Ki Ki' Kj Kj' : cblock) (c : chan) (e : expr) (x : var),
      wf_program PK ->
      replace_leaf (comp_comm Ki) (comp_comm Ki') PK P1 ->
      replace_leaf (comp_comm Kj) (comp_comm Kj') P1 PK' ->
      selects Ki (c_send c e) Ki' ->
      selects Kj (c_recv c x) Kj' ->
      Σ ⊨ {{ Q }} PK' {{ R }} ->
      Σ ⊨ {{ assertion_subst Q x e }} PK {{ R }}.
  Admitted.

  (** ** 5. Par-Comp-MP.  Every terminating run factors through the three
         aligned stages (Lemma 2 normalises runs to prefix-phase-tail
         order). *)
  Lemma par_comp_sound :
    forall (Q0 Q1 Q2 Q3 : assertion dim) (PD PK PT P : program),
      zip3 PD PK PT P ->
      wf_program P ->
      Σ ⊨ {{ Q0 }} PD {{ Q1 }} ->
      Σ ⊨ {{ Q1 }} PK {{ Q2 }} ->
      Σ ⊨ {{ Q2 }} PT {{ Q3 }} ->
      Σ ⊨ {{ Q0 }} P {{ Q3 }}.
  Admitted.

  (** ** 6. Branch-Accum — finite additivity over the family. *)
  Lemma branch_accum_sound :
    forall (phi : formula) (B : qpred dim) (P : program)
           (A0 : qpred dim) (psi0 : formula)
           (fam : list (qpred dim * formula)),
      Σ ⊨ {{ mk_assertion phi A0 }} P {{ mk_assertion psi0 B }} ->
      Forall (fun Api =>
                Σ ⊨ {{ mk_assertion phi (fst Api) }} P
                    {{ mk_assertion (snd Api) B }}) fam ->
      ForallOrdPairs (exclusive Σ) (psi0 :: map snd fam) ->
      Σ ⊨ {{ mk_assertion phi (qsum A0 (map fst fam)) }} P
          {{ mk_assertion (fdisj psi0 (map snd fam)) B }}.
  Admitted.

  (** ** Well-formedness is inherited by the sub-programs appearing in rule
         premises — needed to thread [wf_program] through the induction. *)
  Lemma wf_comm_select_residual :
    forall (PK P1 PK' : program) (Ki Ki' Kj Kj' : cblock)
           (c : chan) (e : expr) (x : var),
      wf_program PK ->
      replace_leaf (comp_comm Ki) (comp_comm Ki') PK P1 ->
      replace_leaf (comp_comm Kj) (comp_comm Kj') P1 PK' ->
      selects Ki (c_send c e) Ki' ->
      selects Kj (c_recv c x) Kj' ->
      wf_program PK'.
  Admitted.

  Lemma wf_zip3_prefix : forall PD PK PT P : program,
      zip3 PD PK PT P -> wf_program P -> wf_program PD.
  Admitted.

  Lemma wf_zip3_comm : forall PD PK PT P : program,
      zip3 PD PK PT P -> wf_program P -> wf_program PK.
  Admitted.

  Lemma wf_zip3_tail : forall PD PK PT P : program,
      zip3 PD PK PT P -> wf_program P -> wf_program PT.
  Admitted.

  (** ** Theorem 4.1 (Soundness of the proof system).
         Assembled from the per-rule lemmas by induction on the derivation —
         the wiring below is machine-checked. *)
  Theorem soundness :
    wf_interp ->
    forall (Q R : assertion dim) (P : program),
      wf_program P ->
      Σ ⊢ₚ {{ Q }} P {{ R }} ->
      Σ ⊨ {{ Q }} P {{ R }}.
  Proof.
    intros interp_ok Q R P Hwf Hd. revert Hwf. induction Hd; intro Hwf.
    - (* Par-Disjoint-MP *) eapply par_disjoint_sound; eassumption.
    - (* Comm-Done *)       apply comm_done_sound; assumption.
    - (* Comm-Select-MP *)  eapply comm_select_sound; try eassumption.
      apply IHHd. eapply wf_comm_select_residual; eassumption.
    - (* Par-Comp-MP *)     eapply par_comp_sound; try eassumption.
      + apply IHHd1. eapply wf_zip3_prefix; eassumption.
      + apply IHHd2. eapply wf_zip3_comm; eassumption.
      + apply IHHd3. eapply wf_zip3_tail; eassumption.
    - (* Branch-Accum *)    apply branch_accum_sound.
      + apply IHHd; assumption.
      + (* the family premise, pointwise — the auto-generated induction
           principle provides no IH inside the Forall (nested occurrence);
           discharging this needs a manual nested induction *) admit.
      + assumption.
    - (* Conseq — wf_assertion now supplied by the rule itself *)
      eapply conseq_sound.
      + exact interp_ok.
      + eassumption.
      + eassumption.
      + apply IHHd; assumption.
      + assumption.
  Admitted.

End Soundness.
