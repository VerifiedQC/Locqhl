(** * SoundnessFacts — the machinery behind Theorem 4.1.

    Nothing here is a statement of the paper; these are the invariants and
    bridges the per-rule soundness proofs run on:

      state legitimacy is preserved by execution   (term_preservation)
      an all-ε communication row is stuck          (comm_done chain)
      a local block's ensemble denotation          (denote, one_leaf_adequacy)
      degree bookkeeping over ensembles            (total_degree_* )
      the three rows cut by zip3                   (zip3_* )
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Reals.Reals Lra.
From Stdlib Require Import Lia.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import
  Syntax QuantumActions SemanticDomain Semantics Assertions WellFormed Rules
  TraceFacts.
Import ListNotations.

Section SoundnessFacts.
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

  Lemma zip3_prefix_footprints : forall PD PK PT P, zip3 PD PK PT P ->
      incl (program_change PD) (program_change P)
      /\ incl (program_cvar PD) (program_cvar P)
      /\ incl (program_qvar PD) (program_qvar P).
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2].
    - unfold program_change, program_cvar, program_qvar, comp_change, comp_cvar,
        comp_qvar, process_cvar; simpl.
      rewrite !app_nil_r. repeat split.
      + apply incl_appl, incl_refl.
      + apply incl_app;
          [ eapply incl_tran; [apply incl_appl, incl_refl | apply incl_appl, incl_refl]
          | eapply incl_tran; [apply incl_appl, incl_refl | apply incl_appr, incl_refl] ].
      + apply incl_appl, incl_refl.
    - destruct IH1 as (C1 & V1 & Q1); destruct IH2 as (C2 & V2 & Q2); simpl.
      repeat split; apply incl_app;
        [ apply incl_appl, C1 | apply incl_appr, C2
        | apply incl_appl, V1 | apply incl_appr, V2
        | apply incl_appl, Q1 | apply incl_appr, Q2 ].
  Qed.

  Lemma zip3_prefix_ownership : forall PD PK PT P, zip3 PD PK PT P ->
      wf_ownership P -> wf_ownership PD.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl.
    - intros _; constructor.
    - intros (H1 & H2 & Ha & Hb & Hq).
      destruct (zip3_prefix_footprints _ _ _ _ Hz1) as (C1 & V1 & Q1).
      destruct (zip3_prefix_footprints _ _ _ _ Hz2) as (C2 & V2 & Q2).
      split; [apply IH1, H1 | split; [apply IH2, H2 |]].
      split; [| split].
      + eapply disjoint_incl; [exact Ha | exact C1 | exact V2].
      + eapply disjoint_incl; [exact Hb | exact C2 | exact V1].
      + eapply disjoint_incl; [exact Hq | exact Q1 | exact Q2].
  Qed.

  (** The D-row carries no communication at all: every leaf reads as
      [phase (r_more D) ε ↓], so the channel and phase conditions are
      vacuous on it. *)
  Lemma zip3_prefix_chan : forall PD PK PT P, zip3 PD PK PT P ->
      program_chan PD = nil.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl;
      [reflexivity | now rewrite IH1, IH2].
  Qed.

  Lemma zip3_prefix_actions : forall PD PK PT P, zip3 PD PK PT P ->
      forall k, concat (phase_at PD k) = nil.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; intro k; simpl.
    - destruct k; reflexivity.
    - rewrite concat_app, IH1, IH2; reflexivity.
  Qed.

  (** ** The K- and T-rows: phase indices shift, actions split.
         The K-row exposes exactly phase 0 and nothing after it; the T-row
         exposes phase (k+1) as its own phase k. *)

  Lemma zip3_comm_phase0 : forall PD PK PT P, zip3 PD PK PT P ->
      phase_at PK 0 = phase_at P 0.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl.
    - destruct K; reflexivity.
    - now rewrite IH1, IH2.
  Qed.

  Lemma zip3_comm_later : forall PD PK PT P, zip3 PD PK PT P ->
      forall k, concat (phase_at PK (S k)) = nil.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; intro k;
      simpl.
    - destruct K; reflexivity.
    - rewrite concat_app, IH1, IH2; reflexivity.
  Qed.

  Lemma zip3_tail_phase : forall PD PK PT P, zip3 PD PK PT P ->
      forall k, phase_at PT k = phase_at P (S k).
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; intro k;
      simpl; [reflexivity | now rewrite IH1, IH2].
  Qed.

  Lemma perm_app_shuffle : forall {A} (a b c d : list A),
      Permutation ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d)).
  Proof.
    intros A a b c d. rewrite <- !app_assoc.
    apply Permutation_app_head, Permutation_app_swap_app.
  Qed.

  Lemma zip3_actions_split : forall PD PK PT P, zip3 PD PK PT P ->
      Permutation (program_actions P) (program_actions PK ++ program_actions PT).
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl.
    - destruct K; simpl;
        [apply Permutation_refl | rewrite app_nil_r; apply Permutation_refl].
    - eapply Permutation_trans;
        [apply Permutation_app; [exact IH1 | exact IH2] | apply perm_app_shuffle].
  Qed.

  Lemma zip3_comm_actions : forall PD PK PT P, zip3 PD PK PT P ->
      program_actions PK = concat (phase_at P 0).
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl.
    - destruct K; reflexivity.
    - rewrite concat_app, IH1, IH2; reflexivity.
  Qed.

  (** Counting endpoints: the split above turns any endpoint filter on P into
      the sum of its K- and T-row counts. *)
  Lemma zip3_filter_count : forall PD PK PT P (g : caction -> bool),
      zip3 PD PK PT P ->
      length (filter g (program_actions P))
      = (length (filter g (program_actions PK))
         + length (filter g (program_actions PT)))%nat.
  Proof.
    intros PD PK PT P g Hz.
    rewrite (Permutation_length (permutation_filter _ g _ _ (zip3_actions_split _ _ _ _ Hz))).
    rewrite filter_app, length_app. reflexivity.
  Qed.

  (** Row footprints, as for the D-row. *)
  Lemma zip3_comm_footprints : forall PD PK PT P, zip3 PD PK PT P ->
      incl (program_change PK) (program_change P)
      /\ incl (program_cvar PK) (program_cvar P)
      /\ incl (program_qvar PK) (program_qvar P).
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2].
    - unfold program_change, program_cvar, program_qvar, comp_change, comp_cvar,
        comp_qvar, process_cvar.
      rewrite comm_leaf_change, comm_leaf_read, comm_leaf_qvar. cbn.
      repeat split;
        auto 15 using incl_app, incl_appl, incl_appr, incl_refl, incl_nil_l.
    - destruct IH1 as (C1 & V1 & Q1); destruct IH2 as (C2 & V2 & Q2); simpl.
      repeat split; apply incl_app;
        [ apply incl_appl, C1 | apply incl_appr, C2
        | apply incl_appl, V1 | apply incl_appr, V2
        | apply incl_appl, Q1 | apply incl_appr, Q2 ].
  Qed.

  Lemma zip3_tail_footprints : forall PD PK PT P, zip3 PD PK PT P ->
      incl (program_change PT) (program_change P)
      /\ incl (program_cvar PT) (program_cvar P)
      /\ incl (program_qvar PT) (program_qvar P).
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2].
    - unfold program_change, program_cvar, program_qvar, comp_change, comp_cvar,
        comp_qvar, process_cvar; simpl.
      repeat split;
        auto 15 using incl_app, incl_appl, incl_appr, incl_refl, incl_nil_l.
    - destruct IH1 as (C1 & V1 & Q1); destruct IH2 as (C2 & V2 & Q2); simpl.
      repeat split; apply incl_app;
        [ apply incl_appl, C1 | apply incl_appr, C2
        | apply incl_appl, V1 | apply incl_appr, V2
        | apply incl_appl, Q1 | apply incl_appr, Q2 ].
  Qed.

  Lemma zip3_comm_ownership : forall PD PK PT P, zip3 PD PK PT P ->
      wf_ownership P -> wf_ownership PK.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl.
    - intros _; constructor.
    - intros (H1 & H2 & Ha & Hb & Hq).
      destruct (zip3_comm_footprints _ _ _ _ Hz1) as (C1 & V1 & Q1).
      destruct (zip3_comm_footprints _ _ _ _ Hz2) as (C2 & V2 & Q2).
      split; [apply IH1, H1 | split; [apply IH2, H2 |]].
      split; [| split].
      + eapply disjoint_incl; [exact Ha | exact C1 | exact V2].
      + eapply disjoint_incl; [exact Hb | exact C2 | exact V1].
      + eapply disjoint_incl; [exact Hq | exact Q1 | exact Q2].
  Qed.

  Lemma zip3_tail_ownership : forall PD PK PT P, zip3 PD PK PT P ->
      wf_ownership P -> wf_ownership PT.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; simpl.
    - intros _; constructor.
    - intros (H1 & H2 & Ha & Hb & Hq).
      destruct (zip3_tail_footprints _ _ _ _ Hz1) as (C1 & V1 & Q1).
      destruct (zip3_tail_footprints _ _ _ _ Hz2) as (C2 & V2 & Q2).
      split; [apply IH1, H1 | split; [apply IH2, H2 |]].
      split; [| split].
      + eapply disjoint_incl; [exact Ha | exact C1 | exact V2].
      + eapply disjoint_incl; [exact Hb | exact C2 | exact V1].
      + eapply disjoint_incl; [exact Hq | exact Q1 | exact Q2].
  Qed.

  (** Party counts transfer to a row once the OTHER row carries no endpoint on
      the channel: then a leaf mentions c in the row exactly when it does in P. *)
  Lemma zip3_parties_comm : forall PD PK PT P c, zip3 PD PK PT P ->
      filter (fun a => Nat.eqb (caction_chan a) c) (program_actions PT) = nil ->
      parties PK c = parties P c.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; intro Hnil.
    - apply comm_leaf_parties. rewrite process_chan_actions.
      apply filter_chan_nil_iff. exact Hnil.
    - cbn [program_actions] in Hnil. rewrite filter_app in Hnil.
      apply app_eq_nil in Hnil as [Hn1 Hn2].
      cbn [parties]. rewrite IH1, IH2 by assumption. reflexivity.
  Qed.

  Lemma zip3_parties_tail : forall PD PK PT P c, zip3 PD PK PT P ->
      filter (fun a => Nat.eqb (caction_chan a) c) (program_actions PK) = nil ->
      parties PT c = parties P c.
  Proof.
    induction 1 as [D K T | d1 d2 k1 k2 t1 t2 z1 z2 Hz1 IH1 Hz2 IH2]; intro Hnil.
    - apply tail_leaf_parties. rewrite <- comm_leaf_chan, process_chan_actions.
      apply filter_chan_nil_iff. exact Hnil.
    - cbn [program_actions] in Hnil. rewrite filter_app in Hnil.
      apply app_eq_nil in Hnil as [Hn1 Hn2].
      cbn [parties]. rewrite IH1, IH2 by assumption. reflexivity.
  Qed.

  (** The endpoint arithmetic shared by both rows: c has exactly two endpoints
      in P, split between the rows; whichever row holds them holds one send and
      one receive. *)
  Lemma endpoints_two : forall (X : program) (c : chan),
      length (filter is_send (endpoints_of X c)) = 1%nat ->
      length (filter (fun a => negb (is_send a)) (endpoints_of X c)) = 1%nat ->
      length (endpoints_of X c) = 2%nat.
  Proof.
    intros X c Hs Hr.
    rewrite (filter_length_split is_send (endpoints_of X c)), Hs, Hr. reflexivity.
  Qed.


  (** ** Comm-Select's residual: one comm leaf K becomes K minus one endpoint.
         Footprints shrink; the program's action multiset loses exactly that
         endpoint, in phase 0 and nowhere else. *)

  Lemma selects_flat_incl : forall {B} (f : caction -> list B) K a K',
      selects K a K' -> incl (flat_map f K') (flat_map f K).
  Proof.
    intros B f K a K' (pre & post & -> & ->).
    rewrite !flat_map_app; simpl.
    intros y Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app;
      [left; exact Hy | right; apply in_or_app; right; exact Hy].
  Qed.

  Lemma selects_chan_incl : forall K a K',
      selects K a K' -> incl (cblock_chan K') (cblock_chan K).
  Proof.
    intros K a K' (pre & post & -> & ->). unfold cblock_chan.
    rewrite !map_app; simpl.
    intros y Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app;
      [left; exact Hy | right; right; exact Hy].
  Qed.

  (** For any OTHER channel the leaf's channel set is unchanged. *)
  Lemma selects_chan_iff : forall K a K' d,
      selects K a K' -> d <> caction_chan a ->
      (In d (cblock_chan K') <-> In d (cblock_chan K)).
  Proof.
    intros K a K' d (pre & post & -> & ->) Hne. unfold cblock_chan.
    rewrite !map_app; simpl. split.
    - intro H; apply in_app_or in H as [H | H]; apply in_or_app;
        [left; exact H | right; right; exact H].
    - intro H; apply in_app_or in H as [H | [H | H]]; apply in_or_app;
        [left; exact H | exfalso; exact (Hne (eq_sym H)) | right; exact H].
  Qed.

  Lemma comm_leaf_footprint_incl : forall K a K', selects K a K' ->
      incl (comp_change (comp_comm K')) (comp_change (comp_comm K))
      /\ incl (comp_cvar (comp_comm K')) (comp_cvar (comp_comm K))
      /\ incl (comp_qvar (comp_comm K')) (comp_qvar (comp_comm K)).
  Proof.
    intros K a K' Hs.
    unfold comp_change, comp_cvar, comp_qvar, process_cvar.
    rewrite !comm_leaf_change, !comm_leaf_read, !comm_leaf_qvar.
    repeat split.
    - apply (selects_flat_incl caction_change _ _ _ Hs).
    - apply incl_app;
        [ apply incl_appl, (selects_flat_incl caction_change _ _ _ Hs)
        | apply incl_appr, (selects_flat_incl caction_read _ _ _ Hs) ].
    - apply incl_nil_l.
  Qed.

  Lemma comm_leaf_chan_iff : forall K a K' d,
      selects K a K' -> d <> caction_chan a ->
      (In d (comp_chan (comp_comm K')) <-> In d (comp_chan (comp_comm K))).
  Proof.
    intros K a K' d Hs Hne. unfold comp_chan. rewrite !comm_leaf_chan.
    apply (selects_chan_iff _ _ _ _ Hs Hne).
  Qed.

  (** ** Consuming one endpoint from a communication phase.
         [comm_sel] matches the phase leaf by leaf, so each fact below is a
         plain induction on the derivation. *)

  Lemma comm_sel_none_eq : forall oa P P',
      comm_sel oa P P' -> oa = None -> P = P'.
  Proof.
    intros oa P P' H; induction H; intro Hn; try discriminate; try reflexivity.
    - f_equal; [apply IHcomm_sel1, Hn | apply IHcomm_sel2; reflexivity].
    - f_equal; [apply IHcomm_sel1; reflexivity | apply IHcomm_sel2, Hn].
  Qed.

  Lemma comm_sel_footprints : forall oa P P', comm_sel oa P P' ->
      incl (program_change P') (program_change P)
      /\ incl (program_cvar P') (program_cvar P)
      /\ incl (program_qvar P') (program_qvar P).
  Proof.
    intros oa P P' H; induction H.
    - repeat split; apply incl_refl.
    - apply (comm_leaf_footprint_incl _ _ _ H).
    - destruct IHcomm_sel1 as (C1 & V1 & Q1);
        destruct IHcomm_sel2 as (C2 & V2 & Q2); simpl.
      repeat split; apply incl_app;
        [ apply incl_appl, C1 | apply incl_appr, C2
        | apply incl_appl, V1 | apply incl_appr, V2
        | apply incl_appl, Q1 | apply incl_appr, Q2 ].
    - destruct IHcomm_sel1 as (C1 & V1 & Q1);
        destruct IHcomm_sel2 as (C2 & V2 & Q2); simpl.
      repeat split; apply incl_app;
        [ apply incl_appl, C1 | apply incl_appr, C2
        | apply incl_appl, V1 | apply incl_appr, V2
        | apply incl_appl, Q1 | apply incl_appr, Q2 ].
  Qed.

  Lemma comm_sel_ownership : forall oa P P', comm_sel oa P P' ->
      wf_ownership P -> wf_ownership P'.
  Proof.
    intros oa P P' H; induction H; simpl.
    - intros _; constructor.
    - intros _; constructor.
    - intros (H1 & H2 & Ha & Hb & Hq).
      destruct (comm_sel_footprints _ _ _ H) as (C1 & V1 & Q1).
      destruct (comm_sel_footprints _ _ _ H0) as (C2 & V2 & Q2).
      split; [apply IHcomm_sel1, H1 | split; [apply IHcomm_sel2, H2 |]].
      split; [| split].
      + eapply disjoint_incl; [exact Ha | exact C1 | exact V2].
      + eapply disjoint_incl; [exact Hb | exact C2 | exact V1].
      + eapply disjoint_incl; [exact Hq | exact Q1 | exact Q2].
    - intros (H1 & H2 & Ha & Hb & Hq).
      destruct (comm_sel_footprints _ _ _ H) as (C1 & V1 & Q1).
      destruct (comm_sel_footprints _ _ _ H0) as (C2 & V2 & Q2).
      split; [apply IHcomm_sel1, H1 | split; [apply IHcomm_sel2, H2 |]].
      split; [| split].
      + eapply disjoint_incl; [exact Ha | exact C1 | exact V2].
      + eapply disjoint_incl; [exact Hb | exact C2 | exact V1].
      + eapply disjoint_incl; [exact Hq | exact Q1 | exact Q2].
  Qed.

  Lemma comm_sel_actions : forall oa P P' a, comm_sel oa P P' -> oa = Some a ->
      Permutation (program_actions P) (a :: program_actions P').
  Proof.
    intros oa P P' a H; induction H; intro Ha; try discriminate.
    - injection Ha as ->. destruct H as (pre & post & -> & ->).
      cbn [program_actions]; rewrite !comm_leaf_actions.
      apply Permutation_sym, Permutation_middle.
    - rewrite <- (comm_sel_none_eq _ _ _ H0 eq_refl).
      cbn [program_actions].
      change (a :: (program_actions P1' ++ program_actions P2))
        with ((a :: program_actions P1') ++ program_actions P2).
      apply Permutation_app_tail, IHcomm_sel1, Ha.
    - rewrite <- (comm_sel_none_eq _ _ _ H eq_refl).
      cbn [program_actions].
      eapply Permutation_trans;
        [apply Permutation_app_head, (IHcomm_sel2 Ha) |].
      apply Permutation_sym, Permutation_middle.
  Qed.

  Lemma comm_sel_phase0 : forall oa P P' a, comm_sel oa P P' -> oa = Some a ->
      Permutation (concat (phase_at P 0%nat)) (a :: concat (phase_at P' 0%nat)).
  Proof.
    intros oa P P' a H; induction H; intro Ha; try discriminate.
    - injection Ha as ->. destruct H as (pre & post & -> & ->).
      cbn [phase_at concat]; rewrite !comm_leaf_comm_at0, !app_nil_r.
      apply Permutation_sym, Permutation_middle.
    - rewrite <- (comm_sel_none_eq _ _ _ H0 eq_refl).
      cbn [phase_at]; rewrite !concat_app.
      change (a :: (concat (phase_at P1' 0%nat) ++ concat (phase_at P2 0%nat)))
        with ((a :: concat (phase_at P1' 0%nat)) ++ concat (phase_at P2 0%nat)).
      apply Permutation_app_tail, IHcomm_sel1, Ha.
    - rewrite <- (comm_sel_none_eq _ _ _ H eq_refl).
      cbn [phase_at]; rewrite !concat_app.
      eapply Permutation_trans;
        [apply Permutation_app_head, (IHcomm_sel2 Ha) |].
      apply Permutation_sym, Permutation_middle.
  Qed.

  Lemma comm_sel_phase_later : forall oa P P', comm_sel oa P P' ->
      forall k, phase_at P' (S k) = phase_at P (S k).
  Proof.
    intros oa P P' H; induction H; intro k; cbn [phase_at].
    - reflexivity.
    - rewrite !comm_leaf_comm_at_S; reflexivity.
    - rewrite IHcomm_sel1, IHcomm_sel2; reflexivity.
    - rewrite IHcomm_sel1, IHcomm_sel2; reflexivity.
  Qed.

  Lemma comm_sel_parties : forall oa P P' a d, comm_sel oa P P' ->
      oa = Some a -> d <> caction_chan a -> parties P' d = parties P d.
  Proof.
    intros oa P P' a d H; induction H; intros Ha Hne; try discriminate.
    - injection Ha as ->. apply parties_leaf_eq.
      apply (comm_leaf_chan_iff _ _ _ _ H Hne).
    - rewrite <- (comm_sel_none_eq _ _ _ H0 eq_refl).
      cbn [parties]; rewrite (IHcomm_sel1 Ha Hne); reflexivity.
    - rewrite <- (comm_sel_none_eq _ _ _ H eq_refl).
      cbn [parties]; rewrite (IHcomm_sel2 Ha Hne); reflexivity.
  Qed.


  (** Removing two endpoints from an action list: kept by a filter that matches
      both (count drops by two), or invisible to a filter that matches neither. *)
  Lemma filter_perm_cons2_keep : forall (g : caction -> bool) l l' a b,
      Permutation l (a :: b :: l') -> g a = true -> g b = true ->
      length (filter g l) = S (S (length (filter g l'))).
  Proof.
    intros g l l' a b Hp Ha Hb.
    rewrite (Permutation_length (permutation_filter _ g _ _ Hp)).
    simpl. rewrite Ha, Hb. reflexivity.
  Qed.

  Lemma filter_perm_cons2_drop : forall (g : caction -> bool) l l' a b,
      Permutation l (a :: b :: l') -> g a = false -> g b = false ->
      Permutation (filter g l) (filter g l').
  Proof.
    intros g l l' a b Hp Ha Hb.
    eapply Permutation_trans; [apply (permutation_filter _ g _ _ Hp) |].
    simpl. rewrite Ha, Hb. apply Permutation_refl.
  Qed.

  Lemma flat_map_perm_incl : forall {B} (f : caction -> list B) l l' a b,
      Permutation l (a :: b :: l') -> incl (flat_map f l') (flat_map f l).
  Proof.
    intros B f l l' a b Hp y Hy.
    apply (Permutation_in _
             (Permutation_sym (permutation_flat_map _ _ f _ _ Hp))).
    simpl. apply in_or_app; right. apply in_or_app; right. exact Hy.
  Qed.


  (** ** Branch-Accum: finite additivity of the degree.
         A sum of pre-effects splits the input degree; mutually exclusive
         guards split the output degree. *)

  Lemma qpred_add_defined : forall s A1 A2 M,
      qpred_denote Σ s (q_add A1 A2) = Some M ->
      exists M1 M2, qpred_denote Σ s A1 = Some M1
                 /\ qpred_denote Σ s A2 = Some M2
                 /\ M = (M1 .+ M2)%M.
  Proof.
    intros s A1 A2 M H. cbn [qpred_denote] in H.
    destruct (qpred_denote Σ s A1) as [M1 |]; [| discriminate].
    destruct (qpred_denote Σ s A2) as [M2 |]; [| discriminate].
    injection H as H. exists M1, M2. repeat split. symmetry; exact H.
  Qed.

  Lemma qsum_denote_parts : forall s A0 As M,
      qpred_denote Σ s (qsum A0 As) = Some M ->
      (exists M0, qpred_denote Σ s A0 = Some M0)
      /\ Forall (fun A => exists MA, qpred_denote Σ s A = Some MA) As.
  Proof.
    intros s A0 As; induction As as [| A As IH]; intros M HM.
    - split; [exists M; exact HM | constructor].
    - apply qpred_add_defined in HM as (M1 & M2 & HA & HQ & _).
      destruct (IH _ HQ) as (H0 & HAs).
      split; [exact H0 | constructor; [exists M1; exact HA | exact HAs]].
  Qed.

  Lemma degree_add : forall phi A1 A2 s (r : qstate dim),
      (exists M, qpred_denote Σ s (q_add A1 A2) = Some M) ->
      degree Σ (mk_assertion phi (q_add A1 A2)) (s, r)
      = (degree Σ (mk_assertion phi A1) (s, r)
         + degree Σ (mk_assertion phi A2) (s, r))%R.
  Proof.
    intros phi A1 A2 s r (M & HM).
    pose proof (qpred_add_defined _ _ _ _ HM) as (M1 & M2 & H1 & H2 & Heq).
    unfold degree, mk_assertion; cbn [classical_part quantum_part].
    destruct (formula_holds Σ s phi); [| lra].
    rewrite HM, H1, H2, Heq.
    rewrite Mmult_plus_distr_r, trace_plus_dist, fst_Cplus. reflexivity.
  Qed.

  Lemma degree_qsum : forall phi A0 As s (r : qstate dim) M,
      qpred_denote Σ s (qsum A0 As) = Some M ->
      degree Σ (mk_assertion phi (qsum A0 As)) (s, r)
      = fold_right Rplus (degree Σ (mk_assertion phi A0) (s, r))
          (map (fun A => degree Σ (mk_assertion phi A) (s, r)) As).
  Proof.
    intros phi A0 As s r; induction As as [| A As IH]; intros M HM.
    - reflexivity.
    - pose proof (qpred_add_defined _ _ _ _ HM) as (M1 & M2 & H1 & H2 & _).
      assert (Hex : exists M', qpred_denote Σ s (q_add A (qsum A0 As)) = Some M')
        by (exists M; exact HM).
      cbn [map fold_right].
      change (qsum A0 (A :: As)) with (q_add A (qsum A0 As)).
      rewrite (degree_add phi A (qsum A0 As) s r Hex).
      rewrite (IH M2 H2). reflexivity.
  Qed.

  Lemma exclusive_sym : forall p q, exclusive Σ p q -> exclusive Σ q p.
  Proof. intros p q H s Hq Hp. exact (H s Hp Hq). Qed.

  Lemma formula_holds_fdisj : forall s psi0 ps,
      formula_holds Σ s (fdisj psi0 ps) = true ->
      formula_holds Σ s psi0 = true
      \/ Exists (fun p => formula_holds Σ s p = true) ps.
  Proof.
    intros s psi0 ps; induction ps as [| p ps IH]; cbn [fdisj fold_right]; intro H.
    - left; exact H.
    - cbn [formula_holds] in H. apply Bool.orb_true_iff in H as [H | H].
      + right; constructor; exact H.
      + destruct (IH H) as [H' | H'];
          [left; exact H' | right; apply Exists_cons_tl, H'].
  Qed.

  Lemma exclusive_fdisj : forall p psi0 ps,
      exclusive Σ p psi0 -> Forall (exclusive Σ p) ps ->
      exclusive Σ p (fdisj psi0 ps).
  Proof.
    intros p psi0 ps H0 Hps s Hp Hd.
    apply formula_holds_fdisj in Hd as [Hd | Hd].
    - exact (H0 s Hp Hd).
    - rewrite Forall_forall in Hps. apply Exists_exists in Hd as (q & Hq & Hqh).
      exact (Hps q Hq s Hp Hqh).
  Qed.

  Lemma degree_or_exclusive : forall p q B st,
      exclusive Σ p q ->
      degree Σ (mk_assertion (f_or p q) B) st
      = (degree Σ (mk_assertion p B) st + degree Σ (mk_assertion q B) st)%R.
  Proof.
    intros p q B [s r] Hex.
    unfold degree, mk_assertion; cbn [classical_part quantum_part formula_holds].
    destruct (formula_holds Σ s p) eqn:Hp; destruct (formula_holds Σ s q) eqn:Hq;
      cbn [orb].
    - exfalso; exact (Hex s Hp Hq).
    - destruct (qpred_denote Σ s B); lra.
    - destruct (qpred_denote Σ s B); lra.
    - lra.
  Qed.

  Lemma total_degree_or_exclusive : forall p q B E,
      exclusive Σ p q ->
      total_degree Σ (mk_assertion (f_or p q) B) E
      = (total_degree Σ (mk_assertion p B) E
         + total_degree Σ (mk_assertion q B) E)%R.
  Proof.
    intros p q B E Hex. unfold total_degree.
    induction E as [| st E IH]; cbn [fold_right map]; [lra |].
    rewrite (degree_or_exclusive p q B st Hex), IH. lra.
  Qed.

  Lemma total_degree_fdisj_exclusive : forall psi0 ps B E,
      ForallOrdPairs (exclusive Σ) (psi0 :: ps) ->
      total_degree Σ (mk_assertion (fdisj psi0 ps) B) E
      = fold_right Rplus (total_degree Σ (mk_assertion psi0 B) E)
          (map (fun p => total_degree Σ (mk_assertion p B) E) ps).
  Proof.
    intros psi0 ps B E; revert psi0;
      induction ps as [| p ps IH]; intros psi0 Hex.
    - reflexivity.
    - inversion Hex as [| ? ? Hhd Htl]; subst.
      inversion Htl as [| ? ? Hhd2 Htl2]; subst.
      inversion Hhd as [| ? ? Hp0 Hps0]; subst.
      assert (Hep : exclusive Σ p (fdisj psi0 ps))
        by (apply exclusive_fdisj; [apply exclusive_sym, Hp0 | exact Hhd2]).
      change (fdisj psi0 (p :: ps)) with (f_or p (fdisj psi0 ps)).
      rewrite (total_degree_or_exclusive p (fdisj psi0 ps) B E Hep).
      cbn [map fold_right].
      assert (Hrec : ForallOrdPairs (exclusive Σ) (psi0 :: ps))
        by (constructor; [exact Hps0 | exact Htl2]).
      rewrite (IH psi0 Hrec). reflexivity.
  Qed.

  Lemma fold_right_Rplus_le : forall (l1 l2 : list R) (b1 b2 : R),
      b1 <= b2 -> Forall2 Rle l1 l2 ->
      fold_right Rplus b1 l1 <= fold_right Rplus b2 l2.
  Proof.
    intros l1 l2 b1 b2 Hb H; induction H; cbn [fold_right]; [exact Hb | lra].
  Qed.


  (** ** Comm-Select-MP, step 1: a communication phase only rendezvouses.

      Stepping turns a ⟨ₖ K ⟩ leaf into [comp_proc (advance ↓ K' ↓)] — a
      different component with the SAME reading — so the runtime invariant is
      stated on the reading, as [leaf_shape] is. *)

  Definition comm_leafy (C : component) : Prop :=
    read_component C = terminated
    \/ exists K, K <> nil /\ read_component C = phase r_done K terminated.

  Fixpoint comm_shape (P : program) : Prop :=
    match P with
    | pg_comp C    => comm_leafy C
    | pg_par P1 P2 => comm_shape P1 /\ comm_shape P2
    end.

  Lemma comm_leafy_comm : forall K, comm_leafy (comp_comm K).
  Proof.
    destruct K as [| a K]; [left; reflexivity |].
    right; exists (a :: K); split; [discriminate | reflexivity].
  Qed.

  Lemma comm_sel_shape : forall oa P P',
      comm_sel oa P P' -> comm_shape P /\ comm_shape P'.
  Proof.
    intros oa P P' H; induction H; simpl.
    - split; apply comm_leafy_comm.
    - split; apply comm_leafy_comm.
    - destruct IHcomm_sel1, IHcomm_sel2; split; split; assumption.
    - destruct IHcomm_sel1, IHcomm_sel2; split; split; assumption.
  Qed.

  Lemma replace_leaf_in_shape : forall a b P P',
      replace_leaf a b P P' -> comm_shape P -> comm_leafy a.
  Proof.
    intros a b P P' H; induction H; simpl.
    - intro Hc; exact Hc.
    - intros (H1 & _); apply IHreplace_leaf, H1.
    - intros (_ & H2); apply IHreplace_leaf, H2.
  Qed.

  Lemma replace_leaf_keeps_shape : forall a b P P',
      replace_leaf a b P P' -> comm_leafy b -> comm_shape P -> comm_shape P'.
  Proof.
    intros a b P P' H Hb; induction H; simpl.
    - intros _; exact Hb.
    - intros (H1 & H2); split; [apply IHreplace_leaf, H1 | exact H2].
    - intros (H1 & H2); split; [exact H1 | apply IHreplace_leaf, H2].
  Qed.

  (** The rendezvous residual of a comm leaf is again one. *)
  Lemma advance_done_comm_leafy : forall K',
      comm_leafy (comp_proc (advance r_done K' terminated)).
  Proof.
    destruct K' as [| a K']; [left; reflexivity |].
    right; exists (a :: K'); split; [discriminate | reflexivity].
  Qed.

  (** The structural heart: one step of a communication phase is one
      rendezvous — a SINGLE branch whose ensemble is the input mapped by the
      classical update x := e, with the residual still a phase. *)
  Lemma comm_shape_step : forall P E G,
      comm_shape P -> Σ ⊳ ‹ P, E › ⇝ G ->
      exists P' (e : expr) (x : var),
        G = {|| P', map (fun '(s,r) =>
                          (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
        /\ comm_shape P'.
  Proof.
    intros P E G Hsh Hstep; induction Hstep.
    - (* ds_local — impossible: a phase leaf has no local block left *)
      exfalso. simpl in Hsh. destruct Hsh as [Ht | (K0 & _ & Ht)];
        rewrite H in Ht; discriminate.
    - (* ds_par_l *)
      simpl in Hsh. destruct Hsh as (H1 & H2).
      destruct (IHHstep H1) as (P1' & e & x & -> & Hs1).
      exists (pg_par P1' P2), e, x. split; [reflexivity | split; assumption].
    - (* ds_par_r *)
      simpl in Hsh. destruct Hsh as (H1 & H2).
      destruct (IHHstep H2) as (P2' & e & x & -> & Hs2).
      exists (pg_par P1 P2'), e, x. split; [reflexivity | split; assumption].
    - (* ds_comm_lr *)
      simpl in Hsh. destruct Hsh as (Hs1 & Hs2).
      pose proof (replace_leaf_in_shape _ _ _ _ H3 Hs1) as HCs.
      pose proof (replace_leaf_in_shape _ _ _ _ H4 Hs2) as HCr.
      destruct HCs as [Ht | (K0 & _ & Ht)]; rewrite H in Ht; [discriminate |].
      injection Ht as _ ->.
      destruct HCr as [Ht' | (K1 & _ & Ht')]; rewrite H0 in Ht'; [discriminate |].
      injection Ht' as _ ->.
      exists (pg_par P1' P2'), e, x. split; [reflexivity |]. split.
      + eapply replace_leaf_keeps_shape;
          [exact H3 | apply advance_done_comm_leafy | exact Hs1].
      + eapply replace_leaf_keeps_shape;
          [exact H4 | apply advance_done_comm_leafy | exact Hs2].
    - (* ds_comm_rl *)
      simpl in Hsh. destruct Hsh as (Hs1 & Hs2).
      pose proof (replace_leaf_in_shape _ _ _ _ H4 Hs1) as HCr.
      pose proof (replace_leaf_in_shape _ _ _ _ H3 Hs2) as HCs.
      destruct HCs as [Ht | (K0 & _ & Ht)]; rewrite H in Ht; [discriminate |].
      injection Ht as _ ->.
      destruct HCr as [Ht' | (K1 & _ & Ht')]; rewrite H0 in Ht'; [discriminate |].
      injection Ht' as _ ->.
      exists (pg_par P1' P2'), e, x. split; [reflexivity |]. split.
      + eapply replace_leaf_keeps_shape;
          [exact H4 | apply advance_done_comm_leafy | exact Hs1].
      + eapply replace_leaf_keeps_shape;
          [exact H3 | apply advance_done_comm_leafy | exact Hs2].
  Qed.


  (** ** Comm-Select-MP, step 2: a communication phase always makes progress,
         and every rendezvous shortens it. *)

  Lemma phase_leaf_actions : forall C K,
      read_component C = phase r_done K terminated ->
      process_actions (read_component C) = K.
  Proof. intros C K H; rewrite H; cbn; apply app_nil_r. Qed.

  Lemma advance_done_actions : forall K',
      process_actions (advance r_done K' terminated) = K'.
  Proof. destruct K'; cbn; rewrite ?app_nil_r; reflexivity. Qed.

  (** Any exposed endpoint can be located: which leaf holds it, and what the
      leaf becomes once it is consumed. *)
  Lemma comm_shape_locate : forall P a,
      comm_shape P -> In a (program_actions P) ->
      exists C K K' P',
        read_component C = phase r_done K terminated
        /\ selects K a K'
        /\ replace_leaf C (comp_proc (advance r_done K' terminated)) P P'.
  Proof.
    induction P as [C | P1 IH1 P2 IH2]; intros a Hsh Hin.
    - destruct Hsh as [Ht | (K & _ & Ht)];
        cbn [program_actions] in Hin; rewrite Ht in Hin; cbn in Hin;
        [destruct Hin |].
      rewrite app_nil_r in Hin. apply in_split in Hin as (pre & post & ->).
      exists C, (pre ++ a :: post), (pre ++ post), (pg_comp (comp_proc
        (advance r_done (pre ++ post) terminated))).
      repeat split; [exact Ht | exists pre, post; split; reflexivity
                    | constructor].
    - destruct Hsh as (Hs1 & Hs2). cbn [program_actions] in Hin.
      apply in_app_or in Hin as [Hin | Hin].
      + destruct (IH1 a Hs1 Hin) as (C & K & K' & P1' & H1 & H2 & H3).
        exists C, K, K', (pg_par P1' P2). repeat split;
          [exact H1 | exact H2 | apply rl_left, H3].
      + destruct (IH2 a Hs2 Hin) as (C & K & K' & P2' & H1 & H2 & H3).
        exists C, K, K', (pg_par P1 P2'). repeat split;
          [exact H1 | exact H2 | apply rl_right, H3].
  Qed.

  (** Locating one endpoint drops exactly it from the program's actions. *)
  Lemma locate_actions : forall C K K' a P P',
      read_component C = phase r_done K terminated ->
      selects K a K' ->
      replace_leaf C (comp_proc (advance r_done K' terminated)) P P' ->
      Permutation (program_actions P) (a :: program_actions P').
  Proof.
    intros C K K' a P P' HC Hsel Hr; induction Hr; cbn [program_actions].
    - change (read_component (comp_proc (advance r_done K' terminated)))
        with (advance r_done K' terminated).
      rewrite (phase_leaf_actions _ _ HC), advance_done_actions.
      destruct Hsel as (pre & post & -> & ->).
      apply Permutation_sym, Permutation_middle.
    - change (a :: (program_actions P' ++ program_actions Q))
        with ((a :: program_actions P') ++ program_actions Q).
      apply Permutation_app_tail, IHHr.
    - eapply Permutation_trans; [apply Permutation_app_head, IHHr |].
      apply Permutation_sym, Permutation_middle.
  Qed.

  Lemma parties_zero_iff : forall P c,
      parties P c = 0%nat <-> ~ In c (program_chan P).
  Proof.
    induction P as [C | P1 IH1 P2 IH2]; intro c; cbn [parties program_chan].
    - destruct (existsb (Nat.eqb c) (comp_chan C)) eqn:E.
      + split; [discriminate |].
        intro H; exfalso; apply H, (proj1 (existsb_eqb_true_iff _ _) E).
      + split; [intros _ | reflexivity].
        intro Hin. apply (proj2 (existsb_eqb_true_iff c (comp_chan C))) in Hin.
        rewrite E in Hin; discriminate.
    - rewrite Nat.eq_add_0, IH1, IH2. split.
      + intros (H1 & H2) H. apply in_app_or in H as [H | H]; auto.
      + intro H; split; intro Hin; apply H, in_or_app; auto.
  Qed.

  (** A channel is a closed point-to-point pair of P — the body of
      [wf_channels] at one channel. *)
  Definition chan_paired (P : program) (c : chan) : Prop :=
    length (filter is_send (endpoints_of P c)) = 1%nat
    /\ length (filter (fun a => negb (is_send a)) (endpoints_of P c)) = 1%nat
    /\ parties P c = 2%nat.

  Lemma filter_len1_in : forall {A} (f : A -> bool) (l : list A),
      length (filter f l) = 1%nat -> exists a, In a l /\ f a = true.
  Proof.
    intros A f l H.
    destruct (filter f l) as [| a rest] eqn:E; [discriminate |].
    assert (Hin : In a (filter f l)) by (rewrite E; left; reflexivity).
    apply filter_In in Hin as (H1 & H2). exists a; split; assumption.
  Qed.

  Lemma send_of_chan : forall P c,
      length (filter is_send (endpoints_of P c)) = 1%nat ->
      exists e, In (c_send c e) (program_actions P).
  Proof.
    intros P c H. apply filter_len1_in in H as (a & Hin & Hs).
    unfold endpoints_of in Hin. apply filter_In in Hin as (Hin & Hc).
    apply Nat.eqb_eq in Hc. destruct a as [c0 e | c0 x]; [| discriminate].
    cbn in Hc; subst c0. exists e; exact Hin.
  Qed.

  Lemma recv_of_chan : forall P c,
      length (filter (fun a => negb (is_send a)) (endpoints_of P c)) = 1%nat ->
      exists x, In (c_recv c x) (program_actions P).
  Proof.
    intros P c H. apply filter_len1_in in H as (a & Hin & Hs).
    unfold endpoints_of in Hin. apply filter_In in Hin as (Hin & Hc).
    apply Nat.eqb_eq in Hc. destruct a as [c0 e | c0 x]; [discriminate |].
    cbn in Hc; subst c0. exists x; exact Hin.
  Qed.


  Lemma endpoints_of_par : forall P1 P2 c,
      endpoints_of (pg_par P1 P2) c = endpoints_of P1 c ++ endpoints_of P2 c.
  Proof.
    intros P1 P2 c; unfold endpoints_of; cbn [program_actions].
    apply filter_app.
  Qed.

  Lemma no_endpoints_parties_zero : forall P c,
      length (filter is_send (endpoints_of P c)) = 0%nat ->
      length (filter (fun a => negb (is_send a)) (endpoints_of P c)) = 0%nat ->
      parties P c = 0%nat.
  Proof.
    intros P c H1 H2.
    assert (Hnil : endpoints_of P c = nil).
    { apply length_zero_iff_nil.
      rewrite (filter_length_split is_send (endpoints_of P c)), H1, H2.
      reflexivity. }
    apply parties_zero_iff. rewrite program_chan_actions.
    apply (proj1 (filter_chan_nil_iff c (program_actions P))). exact Hnil.
  Qed.

  (** Progress: a phase whose channel c is a closed point-to-point pair can
      fire.  The two endpoints sit in different leaves (parties c = 2), so
      somewhere above them is a ∥ node with one on each side. *)
  Lemma comm_progress : forall P E c,
      comm_shape P -> chan_paired P c -> exists G, Σ ⊳ ‹ P, E › ⇝ G.
  Proof.
    induction P as [C | P1 IH1 P2 IH2]; intros E c Hsh (Hs & Hr & Hp).
    - exfalso; cbn [parties] in Hp.
      destruct (existsb (Nat.eqb c) (comp_chan C)); discriminate.
    - destruct Hsh as (Hsh1 & Hsh2).
      rewrite endpoints_of_par, !filter_app, !length_app in Hs, Hr.
      destruct (length (filter is_send (endpoints_of P1 c))) as [| ns] eqn:Es;
        destruct (length (filter (fun a => negb (is_send a))
                            (endpoints_of P1 c))) as [| nr] eqn:Er.
      + (* both endpoints on the right *)
        assert (Hz : parties P1 c = 0%nat) by (apply no_endpoints_parties_zero; auto).
        cbn [parties] in Hp; rewrite Hz in Hp; cbn in Hp.
        destruct (IH2 E c Hsh2) as (G2 & HG2);
          [repeat split; [lia | lia | exact Hp] |].
        exists (map (fun c0 => (pg_par P1 (fst c0), snd c0)) G2).
        apply ds_par_r, HG2.
      + (* send on the right, receive on the left *)
        assert (Hs2 : length (filter is_send (endpoints_of P2 c)) = 1%nat) by lia.
        assert (Hr1 : length (filter (fun a => negb (is_send a))
                                (endpoints_of P1 c)) = 1%nat) by lia.
        destruct (send_of_chan P2 c Hs2) as (e & Hine).
        destruct (recv_of_chan P1 c Hr1) as (x & Hinx).
        destruct (comm_shape_locate P2 (c_send c e) Hsh2 Hine)
          as (Cs & Ks & Ks' & P2' & HCs & Hsel & Hrep2).
        destruct (comm_shape_locate P1 (c_recv c x) Hsh1 Hinx)
          as (Cr & Kr & Kr' & P1' & HCr & Hrel & Hrep1).
        eexists. eapply ds_comm_rl;
          [exact HCs | exact HCr | exact Hsel | exact Hrel
          | exact Hrep2 | exact Hrep1].
      + (* send on the left, receive on the right *)
        assert (Hs1 : length (filter is_send (endpoints_of P1 c)) = 1%nat) by lia.
        assert (Hr2 : length (filter (fun a => negb (is_send a))
                                (endpoints_of P2 c)) = 1%nat) by lia.
        destruct (send_of_chan P1 c Hs1) as (e & Hine).
        destruct (recv_of_chan P2 c Hr2) as (x & Hinx).
        destruct (comm_shape_locate P1 (c_send c e) Hsh1 Hine)
          as (Cs & Ks & Ks' & P1' & HCs & Hsel & Hrep1).
        destruct (comm_shape_locate P2 (c_recv c x) Hsh2 Hinx)
          as (Cr & Kr & Kr' & P2' & HCr & Hrel & Hrep2).
        eexists. eapply ds_comm_lr;
          [exact HCs | exact HCr | exact Hsel | exact Hrel
          | exact Hrep1 | exact Hrep2].
      + (* both endpoints on the left *)
        assert (Hz : parties P2 c = 0%nat)
          by (apply no_endpoints_parties_zero; lia).
        cbn [parties] in Hp; rewrite Hz, Nat.add_0_r in Hp.
        destruct (IH1 E c Hsh1) as (G1 & HG1);
          [repeat split; [lia | lia | exact Hp] |].
        exists (map (fun c0 => (pg_par (fst c0) P2, snd c0)) G1).
        apply ds_par_l, HG1.
  Qed.


  Lemma advance_done_chan : forall K',
      process_chan (advance r_done K' terminated) = cblock_chan K'.
  Proof. destruct K'; cbn; rewrite ?app_nil_r; reflexivity. Qed.

  Lemma locate_parties : forall C K K' a P P' d,
      read_component C = phase r_done K terminated ->
      selects K a K' ->
      replace_leaf C (comp_proc (advance r_done K' terminated)) P P' ->
      d <> caction_chan a -> parties P' d = parties P d.
  Proof.
    intros C K K' a P P' d HC Hsel Hne Hr; induction Hne; cbn [parties].
    - apply parties_leaf_eq. unfold comp_chan.
      change (read_component (comp_proc (advance r_done K' terminated)))
        with (advance r_done K' terminated).
      rewrite advance_done_chan, HC. cbn [process_chan]. rewrite app_nil_r.
      apply (selects_chan_iff _ _ _ _ Hsel Hr).
    - rewrite IHHne; reflexivity.
    - rewrite IHHne; reflexivity.
  Qed.

  (** Everything one rendezvous does, in one statement: a single branch, the
      ensemble mapped by x := e, the two endpoints gone, every other channel's
      party count untouched. *)
  Lemma comm_step_facts : forall P E G,
      comm_shape P -> Σ ⊳ ‹ P, E › ⇝ G ->
      exists P' (c : chan) (e : expr) (x : var),
        G = {|| P', map (fun '(s,r) =>
                          (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
        /\ comm_shape P'
        /\ Permutation (program_actions P)
              (c_send c e :: c_recv c x :: program_actions P')
        /\ (forall d, d <> c -> parties P' d = parties P d).
  Proof.
    intros P E G Hsh Hstep; induction Hstep.
    - exfalso. simpl in Hsh. destruct Hsh as [Ht | (K0 & _ & Ht)];
        rewrite H in Ht; discriminate.
    - simpl in Hsh. destruct Hsh as (H1 & H2).
      destruct (IHHstep H1) as (P1' & c & e & x & -> & Hs1 & Hperm & Hpar).
      exists (pg_par P1' P2), c, e, x. split; [reflexivity |].
      split; [split; assumption | split].
      + cbn [program_actions].
        change (c_send c e :: c_recv c x
                :: (program_actions P1' ++ program_actions P2))
          with ((c_send c e :: c_recv c x :: program_actions P1')
                ++ program_actions P2).
        apply Permutation_app_tail, Hperm.
      + intros d Hd; cbn [parties]; rewrite (Hpar d Hd); reflexivity.
    - simpl in Hsh. destruct Hsh as (H1 & H2).
      destruct (IHHstep H2) as (P2' & c & e & x & -> & Hs2 & Hperm & Hpar).
      exists (pg_par P1 P2'), c, e, x. split; [reflexivity |].
      split; [split; assumption | split].
      + cbn [program_actions].
        eapply Permutation_trans; [apply Permutation_app_head, Hperm |].
        eapply Permutation_trans; [apply Permutation_sym, Permutation_middle |].
        apply perm_skip.
        apply Permutation_sym, Permutation_middle.
      + intros d Hd; cbn [parties]; rewrite (Hpar d Hd); reflexivity.
    - simpl in Hsh. destruct Hsh as (Hs1 & Hs2).
      pose proof (replace_leaf_in_shape _ _ _ _ H3 Hs1) as HCs.
      pose proof (replace_leaf_in_shape _ _ _ _ H4 Hs2) as HCr.
      destruct HCs as [Ht | (K0 & _ & Ht)]; rewrite H in Ht; [discriminate |].
      injection Ht as _ ->.
      destruct HCr as [Ht' | (K1 & _ & Ht')]; rewrite H0 in Ht'; [discriminate |].
      injection Ht' as _ ->.
      exists (pg_par P1' P2'), c, e, x. split; [reflexivity |]. split.
      + split; [ eapply replace_leaf_keeps_shape;
                   [exact H3 | apply advance_done_comm_leafy | exact Hs1]
               | eapply replace_leaf_keeps_shape;
                   [exact H4 | apply advance_done_comm_leafy | exact Hs2] ].
      + split.
        * cbn [program_actions].
          eapply Permutation_trans;
            [apply Permutation_app;
              [apply (locate_actions _ _ _ _ _ _ H H1 H3)
              |apply (locate_actions _ _ _ _ _ _ H0 H2 H4)] |].
          cbn [app]. apply perm_skip.
          apply Permutation_sym, Permutation_middle.
        * intros d Hd; cbn [parties].
          rewrite (locate_parties _ _ _ _ _ _ _ H H1 H3 Hd).
          rewrite (locate_parties _ _ _ _ _ _ _ H0 H2 H4 Hd). reflexivity.
    - simpl in Hsh. destruct Hsh as (Hs1 & Hs2).
      pose proof (replace_leaf_in_shape _ _ _ _ H4 Hs1) as HCr.
      pose proof (replace_leaf_in_shape _ _ _ _ H3 Hs2) as HCs.
      destruct HCs as [Ht | (K0 & _ & Ht)]; rewrite H in Ht; [discriminate |].
      injection Ht as _ ->.
      destruct HCr as [Ht' | (K1 & _ & Ht')]; rewrite H0 in Ht'; [discriminate |].
      injection Ht' as _ ->.
      exists (pg_par P1' P2'), c, e, x. split; [reflexivity |]. split.
      + split; [ eapply replace_leaf_keeps_shape;
                   [exact H4 | apply advance_done_comm_leafy | exact Hs1]
               | eapply replace_leaf_keeps_shape;
                   [exact H3 | apply advance_done_comm_leafy | exact Hs2] ].
      + split.
        * cbn [program_actions].
          eapply Permutation_trans;
            [apply Permutation_app;
              [apply (locate_actions _ _ _ _ _ _ H0 H2 H4)
              |apply (locate_actions _ _ _ _ _ _ H H1 H3)] |].
          cbn [app].
          eapply Permutation_trans;
            [apply perm_skip, Permutation_sym, Permutation_middle |].
          apply perm_swap.
        * intros d Hd; cbn [parties].
          rewrite (locate_parties _ _ _ _ _ _ _ H0 H2 H4 Hd).
          rewrite (locate_parties _ _ _ _ _ _ _ H H1 H3 Hd). reflexivity.
  Qed.


  (** Consuming a matched pair keeps the channel condition: c loses both of
      its endpoints so it drops out, and every other channel is untouched. *)
  Lemma wf_channels_drop_pair : forall P P' c e x,
      wf_channels P ->
      Permutation (program_actions P)
        (c_send c e :: c_recv c x :: program_actions P') ->
      (forall d, d <> c -> parties P' d = parties P d) ->
      wf_channels P'.
  Proof.
    intros P P' c e x Hch HPK Hpar.
    assert (HinPc : In c (program_chan P)).
    { rewrite program_chan_actions. apply (in_map caction_chan _ (c_send c e)).
      apply (Permutation_in _ (Permutation_sym HPK)); left; reflexivity. }
    destruct (Hch c HinPc) as (Hsc & Hrc & _).
    assert (HcA : filter (fun a => Nat.eqb (caction_chan a) c)
                    (program_actions P') = nil).
    { pose proof (endpoints_two _ _ Hsc Hrc) as H2. unfold endpoints_of in H2.
      pose proof (filter_perm_cons2_keep
                    (fun a => Nat.eqb (caction_chan a) c) _ _ _ _ HPK
                    (Nat.eqb_refl c) (Nat.eqb_refl c)) as Hcnt.
      apply length_zero_iff_nil. rewrite H2 in Hcnt. lia. }
    intros d Hd.
    assert (HdP : In d (program_chan P)).
    { rewrite program_chan_actions in Hd |- *.
      revert Hd. apply incl_map. intros y Hy.
      apply (Permutation_in _ (Permutation_sym HPK)); right; right; exact Hy. }
    assert (Hdc : d <> c).
    { intro Heq; subst d.
      apply (proj1 (filter_chan_nil_iff c (program_actions P')) HcA).
      rewrite <- program_chan_actions. exact Hd. }
    assert (Hgf : (fun a => Nat.eqb (caction_chan a) d) (c_send c e) = false)
      by (apply Nat.eqb_neq; intro H; exact (Hdc (eq_sym H))).
    assert (Hgf' : (fun a => Nat.eqb (caction_chan a) d) (c_recv c x) = false)
      by (apply Nat.eqb_neq; intro H; exact (Hdc (eq_sym H))).
    pose proof (filter_perm_cons2_drop _ _ _ _ _ HPK Hgf Hgf') as Hperm.
    destruct (Hch d HdP) as (Hsd & Hrd & Hpd).
    unfold endpoints_of in *. repeat split.
    - rewrite <- (Permutation_length (permutation_filter _ is_send _ _ Hperm)).
      exact Hsd.
    - rewrite <- (Permutation_length
                    (permutation_filter _ (fun a => negb (is_send a)) _ _ Hperm)).
      exact Hrd.
    - rewrite (Hpar d Hdc). exact Hpd.
  Qed.

  Lemma comm_no_actions_terminal : forall P,
      comm_shape P -> program_actions P = nil -> prog_terminated P.
  Proof.
    induction P as [C | P1 IH1 P2 IH2]; cbn [program_actions prog_terminated];
      intros Hsh Hnil.
    - destruct Hsh as [Ht | (K & Hne & Ht)]; [exact Ht |].
      exfalso; apply Hne. rewrite Ht in Hnil; cbn in Hnil.
      rewrite app_nil_r in Hnil; exact Hnil.
    - destruct Hsh as (H1 & H2). apply app_eq_nil in Hnil as (N1 & N2).
      split; [apply IH1 | apply IH2]; assumption.
  Qed.

  (** Termination: each rendezvous drops two endpoints, and progress says one
      is always available until none are left. *)
  Lemma comm_reaches_terminal : forall n P E,
      (length (program_actions P) <= n)%nat ->
      comm_shape P -> wf_channels P ->
      exists G, step_star Σ {|| P, E ||} G /\ terminal G.
  Proof.
    induction n as [| n IH]; intros P E Hlen Hsh Hch.
    - exists ({|| P, E ||}). split; [constructor |].
      constructor; [| constructor]. cbn [fst].
      apply comm_no_actions_terminal; [exact Hsh |].
      destruct (program_actions P) as [| a l0] eqn:Ea; [reflexivity |].
      exfalso; cbn [length] in Hlen; lia.
    - destruct (program_actions P) as [| a rest] eqn:Ea.
      + exists ({|| P, E ||}). split; [constructor |].
        constructor; [| constructor].
        apply comm_no_actions_terminal; assumption.
      + assert (HinA : In a (program_actions P))
          by (rewrite Ea; left; reflexivity).
        assert (Hc : In (caction_chan a) (program_chan P))
          by (rewrite program_chan_actions; apply in_map, HinA).
        destruct (comm_progress P E (caction_chan a) Hsh (Hch _ Hc))
          as (G1 & HG1).
        destruct (comm_step_facts _ _ _ Hsh HG1)
          as (P' & c & e & x & -> & Hsh' & Hperm & Hpar).
        assert (Hlen' : (length (program_actions P') <= n)%nat).
        { pose proof (Permutation_length Hperm) as HL.
          rewrite Ea in HL. cbn [length] in HL, Hlen. lia. }
        pose proof (wf_channels_drop_pair _ _ _ _ _ Hch Hperm Hpar) as Hch'.
        destruct E as [| st E0].
        * exists nil. split; [| constructor].
          eapply star_step; [| constructor].
          apply (mixed_lift Σ ({|| P, nil ||}) P nil nil
                   ({|| P', nil ||})); [apply Permutation_refl | exact HG1].
        * destruct (IH P' (map (fun '(s,r) =>
                     (s [ x |-> eval_expr (i_fn Σ) s e ], r)) (st :: E0))
                     Hlen' Hsh' Hch') as (G & Hstar & Hterm).
          exists G. split; [| exact Hterm].
          eapply star_step; [| exact Hstar].
          apply (mixed_lift Σ ({|| P, st :: E0 ||}) P (st :: E0) nil
                   ({|| P', map (fun '(s,r) =>
                     (s [ x |-> eval_expr (i_fn Σ) s e ], r)) (st :: E0) ||}));
            [apply Permutation_refl | exact HG1].
  Qed.

End SoundnessFacts.
