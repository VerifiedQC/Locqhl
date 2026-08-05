(** * SoundnessFacts — the machinery behind Theorem 4.1.

    Nothing here is a statement of the paper; these are the invariants and
    bridges the per-rule soundness proofs run on:

      state legitimacy is preserved by execution   (term_preservation)
      an all-ε communication row is stuck          (comm_done chain)
      a local block's ensemble denotation          (denote, one_leaf_adequacy)
      degree bookkeeping over ensembles            (total_degree_* )
      non-interfering blocks commute               (denote_comm, paper Lemma 1)
      every interleaving of a row normalises       (prog_adequacy)
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Reals.Reals Lra.
From Stdlib Require Import Lia.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import
  Syntax Names QuantumActions SemanticDomain Semantics Assertions WellFormed
  Rules TraceFacts.
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

  (** The operators one quantum primitive may apply, tagged with the quantum
      variables the primitive names:

        U[q̄]        the unitary       i_uu Σ U q̄
        x := M[q̄]   any member of the family  i_mm Σ M q̄
        q := |0>    the two Kraus operators of [apply_init]

      This is the only place a footprint [lblock_qvar] and an operator meet,
      so it is what [local_ops] below quantifies over. **)
  Inductive acts_on : Square (2 ^ dim) -> list qvar -> Prop :=
  | acts_ugate : forall U qs,   acts_on (i_uu Σ U qs) qs
  | acts_meas  : forall M qs m, acts_on (snd (i_mm Σ M qs) m) qs
  | acts_init0 : forall q,      acts_on (pad_u dim q (∣0⟩⟨0∣)) (q :: nil)
  | acts_init1 : forall q,      acts_on (pad_u dim q (∣0⟩⟨1∣)) (q :: nil).

  (** Locality of the quantum structure.  The paper interprets U[q̄] by an
      operator ON THE REGISTER q̄ (p.4), so two primitives naming disjoint
      quantum variables act on disjoint registers and commute.  The [interp]
      record only records the padded operator, which loses that information —
      [lblock_qvar] disjointness alone says nothing about the matrices — so
      the commutation is assumed here.  Without it Par-Disjoint-MP is FALSE:
      U[q₀] ∥ V[q₁] would have two terminal collapses, UVρV†U† and VUρU†V†,
      and the rule pins only the first. **)
  Definition local_ops : Prop :=
    forall K1 qs1 K2 qs2,
      acts_on K1 qs1 -> acts_on K2 qs2 -> disjoint qs1 qs2 ->
      (K1 × K2 = K2 × K1)%M.

  (** The paper's quantum structure interprets U/M symbols by operators on
      the register (p.4); the [interp] record does not enforce that they are
      well-formed matrices, nor that they are local, so preservation and
      Par-Disjoint-MP assume it. **)
  Definition wf_interp : Prop :=
    (forall U qs, WF_Matrix (i_uu Σ U qs)) /\
    (forall M qs m, WF_Matrix (snd (i_mm Σ M qs) m)) /\
    (* the paper's measurement is the finite family {M_m}_{m∈T_M} (p.4):
       outside T_M there is no operator — Zero is its total-function
       rendering — and T_M is a set *)
    (forall M qs m, ~ In m (fst (i_mm Σ M qs)) ->
                    snd (i_mm Σ M qs) m = Zero) /\
    (forall M qs, NoDup (fst (i_mm Σ M qs))) /\
    local_ops.

  Lemma wf_interp_local : wf_interp -> local_ops.
  Proof. intros H; exact (proj2 (proj2 (proj2 (proj2 H)))). Qed.

  (** A sufficient condition for [local_ops], in the shape a case study
      actually writes its structure down: every operator is QuantumLib's
      padding of a one- or two-qubit gate AT the quantum variables the
      primitive names (or Zero, or the identity — the junk a total [interp]
      must return off-pattern).  Padded operators at disjoint positions
      commute, so a case study only has to classify its own operators. **)
  Inductive padded : Square (2 ^ dim) -> list qvar -> Prop :=
  | padded_zero : forall qs, padded (@Zero (2 ^ dim) (2 ^ dim)) qs
  | padded_id   : forall qs, padded (I (2 ^ dim)) qs
  | padded_u    : forall a (A : Square 2),
      WF_Matrix A -> padded (pad_u dim a A) (a :: nil)
  | padded_ctrl : forall a b (A : Square 2),
      WF_Matrix A -> padded (pad_ctrl dim a b A) (a :: b :: nil).

  Lemma padded_WF : forall K qs, padded K qs -> WF_Matrix K.
  Proof.
    intros K qs H; destruct H as [qs | qs | a A HA | a b A HA];
      try (apply (WF_pad_u dim); assumption);
      try (apply (WF_pad_ctrl dim); assumption);
      auto with wf_db.
  Qed.

  Lemma disjoint_neq : forall (x y : nat) (l m : list nat),
      disjoint l m -> In x l -> In y m -> x <> y.
  Proof. intros x y l m H Hx Hy Hxy; subst; exact (H _ Hx Hy). Qed.

  Lemma disjoint_neq' : forall (x y : nat) (l m : list nat),
      disjoint l m -> In x l -> In y m -> y <> x.
  Proof. intros x y l m H Hx Hy Hxy; subst; exact (H _ Hx Hy). Qed.

  Lemma padded_commute : forall K1 qs1 K2 qs2,
      padded K1 qs1 -> padded K2 qs2 -> disjoint qs1 qs2 ->
      (K1 × K2 = K2 × K1)%M.
  Proof.
    intros K1 qs1 K2 qs2 H1 H2 Hd.
    assert (HW2 : WF_Matrix K2) by (eapply padded_WF; eassumption).
    assert (HW1 : WF_Matrix K1) by (eapply padded_WF; eassumption).
    destruct H1 as [q1 | q1 | a A HA | a b A HA].
    1: now rewrite Mmult_0_l, Mmult_0_r.
    1: now rewrite Mmult_1_l, Mmult_1_r.
    - destruct H2 as [q2 | q2 | c C HC | c d C HC].
      + now rewrite Mmult_0_l, Mmult_0_r.
      + now rewrite Mmult_1_l, Mmult_1_r.
      + apply pad_A_B_commutes;
          [ eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | assumption | assumption ].
      + apply pad_A_ctrl_commutes;
          [ eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | assumption | assumption ].
    - destruct H2 as [q2 | q2 | c C HC | c d C HC].
      + now rewrite Mmult_0_l, Mmult_0_r.
      + now rewrite Mmult_1_l, Mmult_1_r.
      + symmetry; apply pad_A_ctrl_commutes;
          [ eapply disjoint_neq'; [exact Hd | simpl; auto | simpl; auto]
          | eapply disjoint_neq'; [exact Hd | simpl; auto | simpl; auto]
          | assumption | assumption ].
      + apply pad_ctrl_ctrl_commutes;
          [ eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | eapply disjoint_neq; [exact Hd | simpl; auto | simpl; auto]
          | assumption | assumption ].
  Qed.

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

  (** ** 2. A terminated program is stuck.  Every leaf is ↓, so no rule of
         the distributed semantics applies: E stays {(s,r)} and the trace
         inequality of Done (and of Comm-Done, whose row is terminated after
         the ε_K erasure) is an equality. *)

  Lemma replace_leaf_terminated :
    forall (a b : process) (P P' : program),
      replace_leaf a b P P' -> prog_terminated P -> a = terminated.
  Proof.
    intros a b P P' Hrl; induction Hrl; intro Ht;
      [exact Ht | destruct Ht as [H1 _] | destruct Ht as [_ H2]]; auto.
  Qed.

  Lemma terminated_stuck :
    forall (P : program), prog_terminated P ->
      forall (E0 : ensemble dim) (G : distri_config dim),
        Σ ⊳ ‹ P, E0 › ⇝ G -> False.
  Proof.
    intros P; induction P as [T | P1 IH1 P2 IH2]; intros Ht E0 G Hstep.
    - (* a ↓ leaf matches no step rule *)
      cbn in Ht; subst; inversion Hstep.
    - destruct Ht as [Ht1 Ht2].
      inversion Hstep; subst; eauto;
        match goal with
        | Hrl : replace_leaf (phase _ _ _) _ ?Q _ |- _ =>
            pose proof (replace_leaf_terminated _ _ _ _ Hrl
                          ltac:(assumption)) as Hbad; discriminate Hbad
        end.
  Qed.

  Lemma terminated_no_mixed_step :
    forall (P : program) (E0 : ensemble dim) (G2 : distri_config dim),
      prog_terminated P ->
      mixed_step Σ ({|| P, E0 ||}) G2 -> False.
  Proof.
    intros P E0 G2 Ht Hstep.
    inversion Hstep as [G D E G0 G1 Hperm Hd]; subst.
    apply Permutation_length_1_inv in Hperm.
    injection Hperm as HD HE HG0. subst.
    eapply terminated_stuck; eauto.
  Qed.

  Lemma terminated_star_id :
    forall (P : program) (E0 : ensemble dim) (G : distri_config dim),
      prog_terminated P ->
      step_star Σ ({|| P, E0 ||}) G -> G = {|| P, E0 ||}.
  Proof.
    intros P E0 G Ht Hstar.
    inversion Hstar; subst; auto.
    exfalso. eapply terminated_no_mixed_step; eauto.
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
         one-leaf programs; [pdenote] runs the leaf to completion. *)

  Definition leaf_shape (P : program) : Prop :=
    exists T, P = leaf T /\
      (T = terminated \/ exists L', T = phase (r_more L') nil terminated).

  Definition pdenote (P : program) (E : ensemble dim) : ensemble dim :=
    match P with
    | leaf terminated              => E
    | leaf (phase r_done _ _)      => E
    | leaf (phase (r_more L') _ _) => denote L' E
    | par _ _                      => E
    end.

  Definition cdenote (G : distri_config dim) : ensemble dim :=
    flat_map (fun c => pdenote (fst c) (snd c)) G.

  Lemma pdenote_nil : forall P, pdenote P nil = nil.
  Proof.
    intros [T | P1 P2]; simpl; [| reflexivity].
    destruct T as [| R K S]; [reflexivity |].
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
    simpl in HD. destruct HD as (T0 & HDC & Hread). subst D.
    inversion Hd; subst.
    match goal with
    | Hl : Σ ⊳ ‹ _, _ › →ₗ _ |- _ => rename Hl into Hloc
    end.
    destruct Hread as [Hread | (L' & Hread)]; [discriminate |].
    injection Hread as HL HK HS. subst.
    assert (HG1 : forall Gl0 : local_config dim,
               cdenote (map (fun c =>
                 (leaf (advance (fst c) nil terminated), snd c)) Gl0)
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
        * unfold cdenote; simpl. apply Permutation_refl.
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
    destruct P as [T | P1 P2]; simpl; [| reflexivity].
    simpl in HP. now rewrite HP.
  Qed.

  Lemma one_leaf_adequacy :
    forall (L : lblock) (st : cqstate dim) (E : ensemble dim),
      Term Σ (⟨ phase (r_more L) nil terminated ⟩) st E ->
      Permutation E (denote L (st :: nil)).
  Proof.
    intros L st E (G & Hstar & Hterm & Hcoll).
    assert (Hl0 : Forall (fun c => leaf_shape (fst c))
                    ({|| ⟨ phase (r_more L) nil terminated ⟩, st :: nil ||})).
    { constructor; [| constructor]. simpl.
      exists (phase (r_more L) nil terminated). split; [reflexivity |].
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
    destruct interp_ok as (HU & HM & Hzero & Hnodup & Hloc).
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

  (** The single-list [qsum]/[fdisj] of the simplified Branch-Accum: their
      units are [q_zero] and false, so the empty family is the vacuous
      triple.  Restated for the new signatures; the proofs are the same
      inductions with the base case now at the unit. *)

  Lemma qsum_denote_parts : forall s As M,
      qpred_denote Σ s (qsum As) = Some M ->
      Forall (fun A => exists MA, qpred_denote Σ s A = Some MA) As.
  Proof.
    intros s As; induction As as [| A As IH]; intros M HM.
    - constructor.
    - apply qpred_add_defined in HM as (M1 & M2 & HA & HQ & _).
      constructor; [exists M1; exact HA | exact (IH _ HQ)].
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

  Lemma degree_qsum : forall phi As s (r : qstate dim) M,
      qpred_denote Σ s (qsum As) = Some M ->
      degree Σ (mk_assertion phi (qsum As)) (s, r)
      = fold_right Rplus 0%R
          (map (fun A => degree Σ (mk_assertion phi A) (s, r)) As).
  Proof.
    intros phi As s r; induction As as [| A As IH]; intros M HM.
    - unfold degree, mk_assertion; cbn [classical_part quantum_part].
      destruct (formula_holds Σ s phi); [| reflexivity].
      cbn [qpred_denote qsum fold_right].
      rewrite Mmult_0_l. unfold trace, Zero.
      rewrite big_sum_0 by reflexivity. reflexivity.
    - pose proof (qpred_add_defined _ _ _ _ HM) as (M1 & M2 & H1 & H2 & _).
      assert (Hex : exists M', qpred_denote Σ s (q_add A (qsum As)) = Some M')
        by (exists M; exact HM).
      cbn [map fold_right].
      change (qsum (A :: As)) with (q_add A (qsum As)).
      rewrite (degree_add phi A (qsum As) s r Hex).
      rewrite (IH M2 H2). reflexivity.
  Qed.

  Lemma formula_holds_fdisj : forall s ps,
      formula_holds Σ s (fdisj ps) = true ->
      Exists (fun p => formula_holds Σ s p = true) ps.
  Proof.
    intros s ps; induction ps as [| p ps IH]; cbn [fdisj fold_right]; intro Hd.
    - cbn [formula_holds] in Hd. discriminate.
    - cbn [formula_holds] in Hd. apply Bool.orb_true_iff in Hd as [Hd | Hd].
      + constructor; exact Hd.
      + apply Exists_cons_tl, (IH Hd).
  Qed.

  Lemma exclusive_sym : forall p q, exclusive Σ p q -> exclusive Σ q p.
  Proof. intros p q Hpq s Hq Hp. exact (Hpq s Hp Hq). Qed.

  Lemma exclusive_fdisj : forall p ps,
      Forall (exclusive Σ p) ps -> exclusive Σ p (fdisj ps).
  Proof.
    intros p ps Hps s Hp Hd.
    apply formula_holds_fdisj in Hd.
    rewrite Forall_forall in Hps. apply Exists_exists in Hd as (q & Hq & Hqh).
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

  Lemma total_degree_false : forall B E,
      total_degree Σ (mk_assertion (f_bexp b_false) B) E = 0%R.
  Proof.
    intros B E. unfold total_degree.
    induction E as [| [s r] E IH]; cbn [fold_right map]; [reflexivity |].
    rewrite IH.
    unfold degree, mk_assertion;
      cbn [classical_part quantum_part formula_holds eval_bool].
    lra.
  Qed.

  Lemma total_degree_fdisj_exclusive : forall ps B E,
      ForallOrdPairs (exclusive Σ) ps ->
      total_degree Σ (mk_assertion (fdisj ps) B) E
      = fold_right Rplus 0%R
          (map (fun p => total_degree Σ (mk_assertion p B) E) ps).
  Proof.
    intros ps B E Hex; induction ps as [| p ps IH].
    - apply total_degree_false.
    - inversion Hex as [| ? ? Hhd Htl]; subst.
      assert (Hep : exclusive Σ p (fdisj ps)) by (apply exclusive_fdisj; exact Hhd).
      change (fdisj (p :: ps)) with (f_or p (fdisj ps)).
      rewrite (total_degree_or_exclusive p (fdisj ps) B E Hep).
      cbn [map fold_right].
      rewrite (IH Htl). reflexivity.
  Qed.

  Lemma fold_right_Rplus_le : forall (l1 l2 : list R) (b1 b2 : R),
      b1 <= b2 -> Forall2 Rle l1 l2 ->
      fold_right Rplus b1 l1 <= fold_right Rplus b2 l2.
  Proof.
    intros l1 l2 b1 b2 Hb H; induction H; cbn [fold_right]; [exact Hb | lra].
  Qed.

  (* ================================================================ *)
  (* Aux-Subst groundwork: updating a variable the program neither    *)
  (* reads nor writes commutes with every operational step.           *)
  (* ================================================================ *)

  Lemma store_update_comm : forall (s : store) x y a v,
      x <> y ->
      (s [ x |-> a ]) [ y |-> v ] = (s [ y |-> v ]) [ x |-> a ].
  Proof.
    intros s x y a v Hxy.
    apply functional_extensionality; intro z.
    unfold store_update.
    destruct (Nat.eqb y z) eqn:Ey; destruct (Nat.eqb x z) eqn:Ex;
      try reflexivity.
    apply Nat.eqb_eq in Ey. apply Nat.eqb_eq in Ex. congruence.
  Qed.

  Fixpoint eval_expr_update_notin (fn : funsym -> list val -> val)
      (s : store) (y : var) (v : val) (e : expr) {struct e} :
      ~ In y (expr_vars e) ->
      eval_expr fn (s [ y |-> v ]) e = eval_expr fn s e.
  Proof.
    destruct e as [w | x | f es]; simpl; intro Hy.
    - reflexivity.
    - unfold store_update. destruct (Nat.eqb y x) eqn:Ey.
      + apply Nat.eqb_eq in Ey; subst; exfalso; apply Hy; left; reflexivity.
      + reflexivity.
    - f_equal. induction es as [| e0 es' IHes]; simpl; [reflexivity |].
      simpl in Hy. f_equal.
      + apply eval_expr_update_notin.
        intro Hin; apply Hy, in_or_app; left; exact Hin.
      + apply IHes.
        intro Hin; apply Hy, in_or_app; right; exact Hin.
  Qed.

  Lemma eval_bool_update_notin :
    forall (fn : funsym -> list val -> val) (rl : relsym -> list val -> bool)
           (s : store) (y : var) (v : val) (b : bexpr),
      ~ In y (bexpr_vars b) ->
      eval_bool fn rl (s [ y |-> v ]) b = eval_bool fn rl s b.
  Proof.
    intros fn rl s y v b; induction b; simpl; intro Hy;
      try reflexivity.
    - f_equal. apply map_ext_in. intros e0 He0.
      apply eval_expr_update_notin.
      intro Hin. apply Hy. apply in_flat_map. eauto.
    - now rewrite IHb.
    - rewrite IHb1, IHb2; [reflexivity | |];
        intro Hin; apply Hy, in_or_app; auto.
    - rewrite IHb1, IHb2; [reflexivity | |];
        intro Hin; apply Hy, in_or_app; auto.
  Qed.

  Definition upd_st (y : var) (v : val) (st : cqstate dim) : cqstate dim :=
    ((fst st) [ y |-> v ], snd st).

  Definition upd_ens (y : var) (v : val) (E : ensemble dim) : ensemble dim :=
    map (upd_st y v) E.

  Lemma upd_ens_app : forall y v (E1 E2 : ensemble dim),
      upd_ens y v (E1 ++ E2) = upd_ens y v E1 ++ upd_ens y v E2.
  Proof. intros; unfold upd_ens; apply map_app. Qed.

  Lemma upd_ens_assign_comm : forall y v x e (E : ensemble dim),
      x <> y -> ~ In y (expr_vars e) ->
      upd_ens y v
        (map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E)
      = map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r))
            (upd_ens y v E).
  Proof.
    intros y v x e E Hxy Hye. unfold upd_ens.
    rewrite !map_map. apply map_ext. intros [s r].
    unfold upd_st; cbn [fst snd].
    rewrite (eval_expr_update_notin _ _ _ _ e Hye).
    f_equal. apply store_update_comm. exact Hxy.
  Qed.

  Lemma upd_ens_qmap_comm : forall y v (g : qstate dim -> qstate dim)
                                   (E : ensemble dim),
      upd_ens y v (map (fun '(s,r) => (s, g r)) E)
      = map (fun '(s,r) => (s, g r)) (upd_ens y v E).
  Proof.
    intros. unfold upd_ens. rewrite !map_map. apply map_ext.
    intros [s r]. reflexivity.
  Qed.

  Lemma ensemble_filter_upd : forall y v (p : store -> bool)
                                     (E : ensemble dim),
      (forall s, p (s [ y |-> v ]) = p s) ->
      ensemble_filter p (upd_ens y v E)
      = upd_ens y v (ensemble_filter p E).
  Proof.
    intros y v p E Hp. unfold upd_ens, ensemble_filter.
    induction E as [| [s r] E IH]; cbn [map filter fst upd_st]; [reflexivity |].
    cbn [fst]. rewrite Hp. destruct (p s); cbn [map]; rewrite IH; reflexivity.
  Qed.

  Lemma local_step_upd :
    forall y v (L : lblock) (E : ensemble dim) (G : local_config dim),
      ~ In y (lblock_change L) ->
      ~ In y (lblock_read L) ->
      Σ ⊳ ‹ L, E › →ₗ G ->
      Σ ⊳ ‹ L, upd_ens y v E › →ₗ
        map (fun c => (fst c, upd_ens y v (snd c))) G.
  Proof.
    intros y v L E G Hc Hr Hstep; induction Hstep; cbn [map fst snd].
    - apply local_step_skip.
    - (* assign *)
      rewrite upd_ens_assign_comm;
        [ apply local_step_assign
        | intro He; apply Hc; cbn [lblock_change]; left; exact He
        | intro He; apply Hr; cbn [lblock_read]; exact He ].
    - (* init *)
      rewrite upd_ens_qmap_comm. apply local_step_init.
    - (* ugate *)
      rewrite upd_ens_qmap_comm. apply local_step_ugate.
    - (* meas *)
      assert (Hxy : x <> y).
      { intro; subst. apply Hc. cbn [lblock_change]. left. reflexivity. }
      replace (upd_ens y v
                 (flat_map (fun '(s,r) =>
                    map (fun m => (s [ x |-> m ],
                                   apply_meas (i_mm Σ M qs) m r))
                        (fst (i_mm Σ M qs))) E))
        with (flat_map (fun '(s,r) =>
                map (fun m => (s [ x |-> m ],
                               apply_meas (i_mm Σ M qs) m r))
                    (fst (i_mm Σ M qs))) (upd_ens y v E)).
      + apply local_step_meas.
      + unfold upd_ens. rewrite !flat_map_concat_map, !map_map.
        rewrite concat_map, map_map. f_equal. apply map_ext. intros [s r].
        unfold upd_st; cbn [fst snd].
        rewrite !map_map. apply map_ext. intro m.
        f_equal. symmetry. apply store_update_comm. exact Hxy.
    - (* seq *)
      assert (Hc1 : ~ In y (lblock_change L1)).
      { intro Hin; apply Hc; cbn [lblock_change]; apply in_or_app; auto. }
      assert (Hr1 : ~ In y (lblock_read L1)).
      { intro Hin; apply Hr; cbn [lblock_read]; apply in_or_app; auto. }
      specialize (IHHstep Hc1 Hr1).
      rewrite !map_map.
      match goal with
      | |- Σ ⊳ ‹ _, _ › →ₗ ?RHS =>
          replace RHS
            with (map (fun c => match fst c with
                                | r_done => (r_more L2, snd c)
                                | r_more L1' => (r_more <{ L1' ; L2 }>, snd c)
                                end)
                      (map (fun c => (fst c, upd_ens y v (snd c))) G))
      end.
      + apply local_step_seq. exact IHHstep.
      + rewrite map_map. apply map_ext. intros [rd Ee].
        cbn [fst snd]. destruct rd; reflexivity.
    - (* if *)
      cbn [map app fst snd].
      rewrite <- (ensemble_filter_upd y v
                    (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E)
        by (intro s; apply eval_bool_update_notin;
            intro Hin; apply Hr; cbn [lblock_read];
            apply in_or_app; left; exact Hin).
      rewrite <- (ensemble_filter_upd y v
                    (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E)
        by (intro s;
            rewrite (eval_bool_update_notin _ _ _ _ _ b);
            [ reflexivity
            | intro Hin; apply Hr; cbn [lblock_read];
              apply in_or_app; left; exact Hin ]).
      apply local_step_if.
  Qed.

  (* ---- Lifting the update through distributed steps --------------- *)

  Definition upd_cfg (y : var) (v : val) (G : distri_config dim)
    : distri_config dim :=
    map (fun c => (fst c, upd_ens y v (snd c))) G.

  Lemma picks_in : forall (K K' : cblock) (a : caction),
      K ∋ a □ K' -> In a K.
  Proof.
    intros K K' a Hp; induction Hp; [left; reflexivity | right; assumption].
  Qed.

  Lemma replace_leaf_flat_incl :
    forall {A B} (f : A -> list B) (a b : A) (r r' : row A),
      replace_leaf a b r r' -> incl (f a) (row_flat f r).
  Proof.
    intros A B f a b r r' Hrl; induction Hrl; cbn [row_flat].
    - apply incl_refl.
    - intros z Hz; apply in_or_app; left; apply IHHrl, Hz.
    - intros z Hz; apply in_or_app; right; apply IHHrl, Hz.
  Qed.

  Lemma distri_step_upd :
    forall y v (P : program) (E : ensemble dim) (G : distri_config dim),
      ~ In y (program_change P) ->
      ~ In y (program_read P) ->
      Σ ⊳ ‹ P, E › ⇝ G ->
      Σ ⊳ ‹ P, upd_ens y v E › ⇝ upd_cfg y v G.
  Proof.
    intros y v P E G Hc Hr Hstep; induction Hstep.
    - (* ds_local *)
      assert (HcL : ~ In y (lblock_change L)).
      { intro Hin; apply Hc.
        cbn [program_cvar program_change row_flat process_change
             residual_change].
        apply in_or_app; left; exact Hin. }
      assert (HrL : ~ In y (lblock_read L)).
      { intro Hin; apply Hr.
        cbn [program_read row_flat process_read residual_read].
        apply in_or_app; left; exact Hin. }
      unfold upd_cfg. rewrite map_map. cbn [fst snd].
      replace (map (fun c => (⟨ advance (fst c) K T ⟩, upd_ens y v (snd c))) Gl)
        with (map (fun c => (⟨ advance (fst c) K T ⟩, snd c))
                  (map (fun c => (fst c, upd_ens y v (snd c))) Gl))
        by (rewrite map_map; apply map_ext; intros [rd Ee]; reflexivity).
      apply ds_local. apply local_step_upd; assumption.
    - (* ds_par_l *)
      assert (Hc1 : ~ In y (program_change P1)).
      { intro Hin; apply Hc; cbn [program_change row_flat];
          apply in_or_app; auto. }
      assert (Hr1 : ~ In y (program_read P1)).
      { intro Hin; apply Hr; cbn [program_read row_flat];
          apply in_or_app; auto. }
      specialize (IHHstep Hc1 Hr1).
      unfold upd_cfg in *. rewrite map_map. cbn [fst snd].
      replace (map (fun c => (fst c ∥ P2, upd_ens y v (snd c))) G1)
        with (map (fun c => (fst c ∥ P2, snd c))
                  (map (fun c => (fst c, upd_ens y v (snd c))) G1))
        by (rewrite map_map; apply map_ext; intros [Pp Ee]; reflexivity).
      apply ds_par_l. exact IHHstep.
    - (* ds_par_r *)
      assert (Hc2 : ~ In y (program_change P2)).
      { intro Hin; apply Hc; cbn [program_change row_flat];
          apply in_or_app; auto. }
      assert (Hr2 : ~ In y (program_read P2)).
      { intro Hin; apply Hr; cbn [program_read row_flat];
          apply in_or_app; auto. }
      specialize (IHHstep Hc2 Hr2).
      unfold upd_cfg in *. rewrite map_map. cbn [fst snd].
      replace (map (fun c => (P1 ∥ fst c, upd_ens y v (snd c))) G2)
        with (map (fun c => (P1 ∥ fst c, snd c))
                  (map (fun c => (fst c, upd_ens y v (snd c))) G2))
        by (rewrite map_map; apply map_ext; intros [Pp Ee]; reflexivity).
      apply ds_par_r. exact IHHstep.
    - (* ds_comm_lr : sender in P1, receiver in P2 *)
      assert (Hxy : x <> y).
      { intro; subst. apply Hc.
        cbn [program_change row_flat]. apply in_or_app; right.
        eapply (replace_leaf_flat_incl process_change); [eassumption |].
        cbn [process_change residual_change cblock_change app].
        apply in_or_app; left.
        apply <- in_flat_map. exists (c_recv c y). split.
        - eapply picks_in; eassumption.
        - cbn [caction_change]. left. reflexivity. }
      assert (Hye : ~ In y (expr_vars e)).
      { intro Hin. apply Hr.
        cbn [program_read row_flat]. apply in_or_app; left.
        eapply (replace_leaf_flat_incl process_read); [eassumption |].
        cbn [process_read residual_read cblock_read app].
        apply in_or_app; left.
        apply <- in_flat_map. exists (c_send c e). split.
        - eapply picks_in; eassumption.
        - cbn [caction_read]. exact Hin. }
      unfold upd_cfg. cbn [map fst snd].
      rewrite upd_ens_assign_comm by assumption.
      eapply ds_comm_lr; eassumption.
    - (* ds_comm_rl : sender in P2, receiver in P1 *)
      assert (Hxy : x <> y).
      { intro; subst. apply Hc.
        cbn [program_change row_flat]. apply in_or_app; left.
        eapply (replace_leaf_flat_incl process_change); [eassumption |].
        cbn [process_change residual_change cblock_change app].
        apply in_or_app; left.
        apply <- in_flat_map. exists (c_recv c y). split.
        - eapply picks_in; eassumption.
        - cbn [caction_change]. left. reflexivity. }
      assert (Hye : ~ In y (expr_vars e)).
      { intro Hin. apply Hr.
        cbn [program_read row_flat]. apply in_or_app; right.
        eapply (replace_leaf_flat_incl process_read); [eassumption |].
        cbn [process_read residual_read cblock_read app].
        apply in_or_app; left.
        apply <- in_flat_map. exists (c_send c e). split.
        - eapply picks_in; eassumption.
        - cbn [caction_read]. exact Hin. }
      unfold upd_cfg. cbn [map fst snd].
      rewrite upd_ens_assign_comm by assumption.
      eapply ds_comm_rl; eassumption.
  Qed.

  (* ---- Footprints only shrink along steps -------------------------- *)

  Lemma picks_incl : forall (K K' : cblock) (a : caction),
      K ∋ a □ K' -> incl K' K.
  Proof.
    intros K K' a Hp; induction Hp.
    - intros z Hz; right; exact Hz.
    - intros z [Hz | Hz]; [left; exact Hz | right; apply IHHp, Hz].
  Qed.

  Lemma replace_leaf_flat_incl_rev :
    forall {A B} (f : A -> list B) (a b : A) (r r' : row A),
      replace_leaf a b r r' -> incl (f b) (f a) ->
      incl (row_flat f r') (row_flat f r).
  Proof.
    intros A B f a b r r' Hrl Hba; induction Hrl; cbn [row_flat].
    - exact Hba.
    - intros z Hz; apply in_app_or in Hz; apply in_or_app;
        destruct Hz; [left; apply IHHrl |]; auto.
    - intros z Hz; apply in_app_or in Hz; apply in_or_app;
        destruct Hz; [| right; apply IHHrl]; auto.
  Qed.

  Lemma advance_change_incl : forall R K T,
      incl (process_change (advance R K T))
           (residual_change R ++ cblock_change K ++ process_change T).
  Proof.
    intros R K T; destruct R; destruct K; apply incl_refl.
  Qed.

  Lemma advance_read_incl : forall R K T,
      incl (process_read (advance R K T))
           (residual_read R ++ cblock_read K ++ process_read T).
  Proof.
    intros R K T; destruct R; destruct K; apply incl_refl.
  Qed.

  Lemma flat_map_incl : forall {A B} (f : A -> list B) (l l' : list A),
      incl l' l -> incl (flat_map f l') (flat_map f l).
  Proof.
    intros A B f l l' Hl z Hz.
    apply in_flat_map in Hz as (a & Ha & Hz).
    apply in_flat_map. exists a. split; [apply Hl, Ha | exact Hz].
  Qed.

  Lemma advance_comm_change_incl : forall Ks Ks' (a : caction) Ts,
      Ks ∋ a □ Ks' ->
      incl (process_change (advance ↓ Ks' Ts)) (process_change (phase ↓ Ks Ts)).
  Proof.
    intros Ks Ks' a Ts Hp z Hz.
    apply (advance_change_incl ↓ Ks' Ts) in Hz.
    cbn [process_change residual_change app] in *.
    apply in_app_or in Hz; apply in_or_app; destruct Hz as [Hz | Hz].
    - left. eapply flat_map_incl; [eapply picks_incl; eassumption | exact Hz].
    - right; exact Hz.
  Qed.

  Lemma advance_comm_read_incl : forall Ks Ks' (a : caction) Ts,
      Ks ∋ a □ Ks' ->
      incl (process_read (advance ↓ Ks' Ts)) (process_read (phase ↓ Ks Ts)).
  Proof.
    intros Ks Ks' a Ts Hp z Hz.
    apply (advance_read_incl ↓ Ks' Ts) in Hz.
    cbn [process_read residual_read app] in *.
    apply in_app_or in Hz; apply in_or_app; destruct Hz as [Hz | Hz].
    - left. eapply flat_map_incl; [eapply picks_incl; eassumption | exact Hz].
    - right; exact Hz.
  Qed.

  Lemma local_step_residual_incl :
    forall (L : lblock) (E : ensemble dim) (G : local_config dim),
      Σ ⊳ ‹ L, E › →ₗ G ->
      Forall (fun c => incl (residual_change (fst c)) (lblock_change L)
                       /\ incl (residual_read (fst c)) (lblock_read L)) G.
  Proof.
    intros L E G Hstep; induction Hstep;
      cbn [residual_change residual_read lblock_change lblock_read].
    - constructor; [split; apply incl_nil_l | constructor].
    - constructor; [split; apply incl_nil_l | constructor].
    - constructor; [split; apply incl_nil_l | constructor].
    - constructor; [split; apply incl_nil_l | constructor].
    - constructor; [split; apply incl_nil_l | constructor].
    - (* seq *)
      rewrite Forall_map. eapply Forall_impl; [| exact IHHstep].
      intros [rd Ee] [Hch Hrd]; cbn [fst] in *.
      destruct rd; cbn [residual_change residual_read
                        lblock_change lblock_read] in *; split;
        intros z Hz.
      + apply in_or_app; right; exact Hz.
      + apply in_or_app; right; exact Hz.
      + apply in_app_or in Hz; apply in_or_app;
          destruct Hz; [left; apply Hch | right]; auto.
      + apply in_app_or in Hz; apply in_or_app;
          destruct Hz; [left; apply Hrd | right]; auto.
    - (* if *)
      constructor; [| constructor; [| constructor]];
        cbn [fst residual_change residual_read]; split; intros z Hz.
      + apply in_or_app; left; exact Hz.
      + apply in_or_app; right; apply in_or_app; left; exact Hz.
      + apply in_or_app; right; exact Hz.
      + apply in_or_app; right; apply in_or_app; right; exact Hz.
  Qed.

  Lemma distri_step_footprint :
    forall (P : program) (E : ensemble dim) (G : distri_config dim),
      Σ ⊳ ‹ P, E › ⇝ G ->
      Forall (fun c => incl (program_change (fst c)) (program_change P)
                       /\ incl (program_read (fst c)) (program_read P)) G.
  Proof.
    intros P E G Hstep; induction Hstep.
    - (* ds_local *)
      pose proof (local_step_residual_incl _ _ _ H) as HG.
      rewrite Forall_map. eapply Forall_impl; [| exact HG].
      intros [rd Ee] [Hch Hrd]; cbn [fst] in *.
      cbn [program_change program_read row_flat].
      split; intros z Hz.
      + apply (advance_change_incl rd K T) in Hz.
        cbn [process_change].
        apply in_app_or in Hz; apply in_or_app;
          destruct Hz as [Hz | Hz]; [left; apply Hch; exact Hz | right; exact Hz].
      + apply (advance_read_incl rd K T) in Hz.
        cbn [process_read].
        apply in_app_or in Hz; apply in_or_app;
          destruct Hz as [Hz | Hz]; [left; apply Hrd; exact Hz | right; exact Hz].
    - (* ds_par_l *)
      rewrite Forall_map. eapply Forall_impl; [| exact IHHstep].
      intros [Pp Ee] [Hch Hrd]; cbn [fst] in *.
      cbn [program_change program_read row_flat]; split; intros z Hz;
        apply in_app_or in Hz; apply in_or_app;
        destruct Hz; [left; apply Hch | right | left; apply Hrd | right]; auto.
    - (* ds_par_r *)
      rewrite Forall_map. eapply Forall_impl; [| exact IHHstep].
      intros [Pp Ee] [Hch Hrd]; cbn [fst] in *.
      cbn [program_change program_read row_flat]; split; intros z Hz;
        apply in_app_or in Hz; apply in_or_app;
        destruct Hz; [left | right; apply Hch | left | right; apply Hrd]; auto.
    - (* ds_comm_lr *)
      constructor; [| constructor]. cbn [fst].
      cbn [program_change program_read row_flat]; split; intros z Hz;
        apply in_app_or in Hz; apply in_or_app; destruct Hz as [Hz | Hz].
      + left.
        eapply (replace_leaf_flat_incl_rev process_change);
          [eassumption | eapply advance_comm_change_incl; eassumption
          | exact Hz].
      + right.
        eapply (replace_leaf_flat_incl_rev process_change);
          [eassumption | eapply advance_comm_change_incl; eassumption
          | exact Hz].
      + left.
        eapply (replace_leaf_flat_incl_rev process_read);
          [eassumption | eapply advance_comm_read_incl; eassumption
          | exact Hz].
      + right.
        eapply (replace_leaf_flat_incl_rev process_read);
          [eassumption | eapply advance_comm_read_incl; eassumption
          | exact Hz].
    - (* ds_comm_rl *)
      constructor; [| constructor]. cbn [fst].
      cbn [program_change program_read row_flat]; split; intros z Hz;
        apply in_app_or in Hz; apply in_or_app; destruct Hz as [Hz | Hz].
      + left.
        eapply (replace_leaf_flat_incl_rev process_change);
          [eassumption | eapply advance_comm_change_incl; eassumption
          | exact Hz].
      + right.
        eapply (replace_leaf_flat_incl_rev process_change);
          [eassumption | eapply advance_comm_change_incl; eassumption
          | exact Hz].
      + left.
        eapply (replace_leaf_flat_incl_rev process_read);
          [eassumption | eapply advance_comm_read_incl; eassumption
          | exact Hz].
      + right.
        eapply (replace_leaf_flat_incl_rev process_read);
          [eassumption | eapply advance_comm_read_incl; eassumption
          | exact Hz].
  Qed.

  (* ---- The update lifts through whole executions ------------------- *)

  Definition cfg_avoid (y : var) (G : distri_config dim) : Prop :=
    Forall (fun c => ~ In y (program_change (fst c))
                     /\ ~ In y (program_read (fst c))) G.

  Lemma Forall_perm : forall {A} (P : A -> Prop) (l l' : list A),
      Permutation l l' -> Forall P l -> Forall P l'.
  Proof.
    intros A P l l' Hp Hf. rewrite Forall_forall in *.
    intros x Hx. apply Hf. eapply Permutation_in; [apply Permutation_sym|]; eassumption.
  Qed.

  Lemma norm_upd_cfg : forall y v (G : distri_config dim),
      norm (upd_cfg y v G) = upd_cfg y v (norm G).
  Proof.
    intros y v G. unfold norm, upd_cfg.
    induction G as [| [P E] G IH]; cbn [map filter fst snd]; [reflexivity |].
    destruct E as [| st E']; cbn [upd_ens map]; rewrite IH; reflexivity.
  Qed.

  Lemma upd_cfg_app : forall y v (G1 G2 : distri_config dim),
      upd_cfg y v (G1 ++ G2) = upd_cfg y v G1 ++ upd_cfg y v G2.
  Proof. intros; unfold upd_cfg; apply map_app. Qed.

  Lemma mixed_step_upd :
    forall y v (G G' : distri_config dim),
      cfg_avoid y G ->
      mixed_step Σ G G' ->
      mixed_step Σ (upd_cfg y v G) (upd_cfg y v G') /\ cfg_avoid y G'.
  Proof.
    intros y v G G' Hav Hstep; destruct Hstep as [G D E G0 G1 Hperm Hd].
    assert (HavD : ~ In y (program_change D) /\ ~ In y (program_read D)).
    { pose proof (Forall_perm _ _ _ Hperm Hav) as Hav'.
      inversion Hav'; assumption. }
    assert (HavG0 : cfg_avoid y G0).
    { pose proof (Forall_perm _ _ _ Hperm Hav) as Hav'.
      inversion Hav'; assumption. }
    destruct HavD as [HcD HrD].
    split.
    - replace (upd_cfg y v (norm (G1 ⊎ G0)))
        with (norm (upd_cfg y v G1 ⊎ upd_cfg y v G0))
        by (rewrite <- upd_cfg_app, norm_upd_cfg; reflexivity).
      apply (mixed_lift Σ (upd_cfg y v G) D (upd_ens y v E)
                        (upd_cfg y v G0) (upd_cfg y v G1)).
      + change ((D, upd_ens y v E) :: upd_cfg y v G0)
          with (upd_cfg y v ((D, E) :: G0)).
        apply Permutation_map. exact Hperm.
      + apply distri_step_upd; assumption.
    - apply Forall_filter_keep. apply Forall_app. split.
      + pose proof (distri_step_footprint _ _ _ Hd) as HF.
        eapply Forall_impl; [| exact HF].
        intros [Pp Ee] [Hch Hrd]; cbn [fst] in *; split;
          intro Hin; [apply HcD, Hch | apply HrD, Hrd]; exact Hin.
      + exact HavG0.
  Qed.

  Lemma step_star_upd :
    forall y v (G G' : distri_config dim),
      cfg_avoid y G ->
      step_star Σ G G' ->
      step_star Σ (upd_cfg y v G) (upd_cfg y v G').
  Proof.
    intros y v G G' Hav Hstar; induction Hstar.
    - apply star_refl.
    - destruct (mixed_step_upd y v _ _ Hav H) as [Hs Hav2].
      eapply star_step; [exact Hs | apply IHHstar, Hav2].
  Qed.

  Lemma collapse_upd_cfg : forall y v (G : distri_config dim),
      collapse (upd_cfg y v G) = upd_ens y v (collapse G).
  Proof.
    intros y v G. unfold collapse, upd_cfg, upd_ens.
    rewrite !flat_map_concat_map, !map_map.
    rewrite concat_map, !map_map.
    reflexivity.
  Qed.

  Lemma terminal_upd_cfg : forall y v (G : distri_config dim),
      terminal G -> terminal (upd_cfg y v G).
  Proof.
    intros y v G Ht. unfold terminal, upd_cfg in *.
    rewrite Forall_map. eapply Forall_impl; [| exact Ht].
    intros [P E] HP; cbn [fst] in *; exact HP.
  Qed.

  Lemma Term_upd :
    forall y v (P : program) (s : store) (r : qstate dim) (E : ensemble dim),
      ~ In y (program_change P) ->
      ~ In y (program_read P) ->
      Term Σ P (s, r) E ->
      Term Σ P (s [ y |-> v ], r) (upd_ens y v E).
  Proof.
    intros y v P s r E Hc Hr (G & Hstar & Hterm & Hcoll).
    exists (upd_cfg y v G). split; [| split].
    - change ({|| P, [(s [ y |-> v ], r)] ||})
        with (upd_cfg y v ({|| P, [(s, r)] ||})).
      apply step_star_upd; [| exact Hstar].
      constructor; [split; assumption | constructor].
    - apply terminal_upd_cfg, Hterm.
    - rewrite collapse_upd_cfg, Hcoll. reflexivity.
  Qed.


  (** ** 4. Interference freedom — the paper's Lemma 1. *****************

      Par-Disjoint-MP reads the row D₁∥…∥D_N as the single block [lseq d],
      but the semantics interleaves the leaves arbitrarily.  What closes the
      gap is that two non-interfering blocks COMMUTE denotationally, so any
      interleaving normalises to the displayed order.

      The commutation is proved once, at the level of a generic ATOMIC
      ACTION — a branch set J, a store map and a state map per branch.  All
      five atomic local blocks have that shape, so the pairs collapse to two
      independent obligations: the store maps commute (disjoint classical
      footprints) and the state maps commute (disjoint quantum footprints,
      plus [local_ops]).
  *********************************************************************)

  (* ---- list plumbing: reassociating a double flat_map --------------- *)

  Lemma flat_map_flat_map :
    forall {A B C} (f : B -> list C) (g : A -> list B) (l : list A),
      flat_map f (flat_map g l) = flat_map (fun a => flat_map f (g a)) l.
  Proof.
    induction l as [| a l IH]; simpl; [reflexivity |].
    rewrite flat_map_app, IH; reflexivity.
  Qed.

  Lemma flat_map_map :
    forall {A B C} (f : B -> list C) (g : A -> B) (l : list A),
      flat_map f (map g l) = flat_map (fun a => f (g a)) l.
  Proof. induction l as [| a l IH]; simpl; [reflexivity | now rewrite IH]. Qed.

  Lemma flat_map_ext' : forall {A B} (f g : A -> list B) (l : list A),
      (forall a, f a = g a) -> flat_map f l = flat_map g l.
  Proof.
    intros A B f g l H; induction l as [| a l IH]; simpl;
      [reflexivity | rewrite H, IH; reflexivity].
  Qed.

  Lemma flat_map_const_nil : forall {A B} (l : list A),
      flat_map (fun _ : A => @nil B) l = nil.
  Proof. induction l; simpl; [reflexivity | assumption]. Qed.

  Lemma flat_map_cons_split :
    forall {A B} (h : A -> B) (g : A -> list B) (l : list A),
      Permutation (flat_map (fun a => h a :: g a) l) (map h l ++ flat_map g l).
  Proof.
    intros A B h g l; induction l as [| a l IH]; simpl; [apply Permutation_refl |].
    apply perm_skip.
    eapply Permutation_trans; [apply Permutation_app_head, IH |].
    apply Permutation_app_swap_app.
  Qed.

  (** Transposing a product: running J₂ inside J₁ lists the same pairs as
      running J₁ inside J₂ — in a different order, hence [Permutation]. **)
  Lemma flat_map_map_swap :
    forall {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B),
      Permutation (flat_map (fun a => map (f a) l2) l1)
                  (flat_map (fun b => map (fun a => f a b) l1) l2).
  Proof.
    intros A B C f l1; induction l1 as [| a l1 IH]; intros l2; simpl.
    - rewrite (flat_map_const_nil l2). apply Permutation_refl.
    - eapply Permutation_trans; [apply Permutation_app_head, IH |].
      apply Permutation_sym,
        (flat_map_cons_split (fun b => f a b)
                             (fun b => map (fun a' => f a' b) l1) l2).
  Qed.

  Lemma Permutation_flat_map_ext :
    forall {A} (f g : A -> ensemble dim) (l : list A),
      (forall a, Permutation (f a) (g a)) ->
      Permutation (flat_map f l) (flat_map g l).
  Proof.
    intros A f g l H; induction l as [| a l IH]; simpl;
      [apply Permutation_refl | apply Permutation_app; [apply H | exact IH]].
  Qed.

  Lemma Permutation_flat_map_in :
    forall {A} (f g : A -> ensemble dim) (l : list A),
      (forall a, In a l -> Permutation (f a) (g a)) ->
      Permutation (flat_map f l) (flat_map g l).
  Proof.
    intros A f g l; induction l as [| a l IH]; intros H; simpl;
      [apply Permutation_refl |].
    apply Permutation_app; [apply H; left; reflexivity |].
    apply IH; intros b Hb; apply H; right; exact Hb.
  Qed.

  (* ---- the generic atomic action ------------------------------------ *)

  Definition act (J : list nat) (sf : nat -> store -> store)
                 (qf : nat -> qstate dim -> qstate dim) (E : ensemble dim)
    : ensemble dim :=
    flat_map (fun st => map (fun j => (sf j (fst st), qf j (snd st))) J) E.

  Lemma act_comm : forall J1 sf1 qf1 J2 sf2 qf2,
      (forall j1 j2 s, sf1 j1 (sf2 j2 s) = sf2 j2 (sf1 j1 s)) ->
      (forall j1 j2 r, qf1 j1 (qf2 j2 r) = qf2 j2 (qf1 j1 r)) ->
      forall E, Permutation (act J1 sf1 qf1 (act J2 sf2 qf2 E))
                            (act J2 sf2 qf2 (act J1 sf1 qf1 E)).
  Proof.
    intros J1 sf1 qf1 J2 sf2 qf2 Hs Hq E.
    unfold act; rewrite !flat_map_flat_map.
    apply Permutation_flat_map_ext; intros [s r].
    rewrite !flat_map_map; cbn [fst snd].
    rewrite (flat_map_ext'
               (fun j1 => map (fun j2 => (sf2 j2 (sf1 j1 s), qf2 j2 (qf1 j1 r))) J2)
               (fun j1 => map (fun j2 => (sf1 j1 (sf2 j2 s), qf1 j1 (qf2 j2 r))) J2) J1)
      by (intros j1; apply map_ext; intros j2; rewrite Hs, Hq; reflexivity).
    apply Permutation_sym, flat_map_map_swap.
  Qed.

  (* ---- the five atomic blocks, read as [act] ------------------------ *)

  Definition atomic (L : lblock) : Prop :=
    match L with l_seq _ _ => False | l_if _ _ _ => False | _ => True end.

  Definition abranch (L : lblock) : list nat :=
    match L with l_meas _ M qs => fst (i_mm Σ M qs) | _ => 0%nat :: nil end.

  Definition astore (L : lblock) : nat -> store -> store :=
    match L with
    | l_assign x e => fun _ s => s [ x |-> eval_expr (i_fn Σ) s e ]
    | l_meas x _ _ => fun m s => s [ x |-> m ]
    | _            => fun _ s => s
    end.

  Definition aqmap (L : lblock) : nat -> qstate dim -> qstate dim :=
    match L with
    | l_init q      => fun _ => apply_init q
    | l_ugate U qs  => fun _ => apply_unitary (i_uu Σ U qs)
    | l_meas _ M qs => fun m => apply_meas (i_mm Σ M qs) m
    | _             => fun _ r => r
    end.

  Lemma denote_atomic : forall L, atomic L ->
      forall E, denote L E = act (abranch L) (astore L) (aqmap L) E.
  Proof.
    intros L HL E; destruct L as [| x e | q | U qs | x M qs | L1 L2 | b L1 L0];
      try contradiction; unfold act; cbn [abranch astore aqmap].
    all: induction E as [| [s r] E IH]; simpl in *;
      [reflexivity | rewrite <- IH; reflexivity].
  Qed.

  (* ---- obligation 1: the store maps commute ------------------------- *)

  Lemma disjoint_sym : forall l1 l2, disjoint l1 l2 -> disjoint l2 l1.
  Proof. intros l1 l2 H x Hx Hy; exact (H x Hy Hx). Qed.

  Lemma disjoint_single : forall (x : nat) (l : list nat),
      disjoint (x :: nil) l -> ~ In x l.
  Proof. intros x l H; apply H; left; reflexivity. Qed.

  Lemma disjoint_singles : forall x y : nat,
      disjoint (x :: nil) (y :: nil) -> x <> y.
  Proof.
    intros x y H Hxy; subst.
    apply (disjoint_single y (y :: nil) H); left; reflexivity.
  Qed.

  Lemma astore_comm : forall L1 L2,
      atomic L1 -> atomic L2 ->
      disjoint (lblock_change L1) (lblock_change L2) ->
      disjoint (lblock_change L1) (lblock_read L2) ->
      disjoint (lblock_change L2) (lblock_read L1) ->
      forall j1 j2 s, astore L1 j1 (astore L2 j2 s) = astore L2 j2 (astore L1 j1 s).
  Proof.
    intros L1 L2 H1 H2 Hcc Hcr Hrc j1 j2 s;
      destruct L1 as [| x1 e1 | q1 | U1 qs1 | x1 M1 qs1 | ? ? | ? ? ?];
      destruct L2 as [| x2 e2 | q2 | U2 qs2 | x2 M2 qs2 | ? ? | ? ? ?];
      try contradiction; cbn [astore lblock_change lblock_read] in *;
      try reflexivity.
    - (* x₁ := e₁  ‖  x₂ := e₂ *)
      rewrite (eval_expr_update_notin _ _ _ _ e1 (disjoint_single x2 _ Hrc)).
      rewrite (eval_expr_update_notin _ _ _ _ e2 (disjoint_single x1 _ Hcr)).
      apply store_update_comm.
      intro Hxy; apply (disjoint_single x1 _ Hcc); left; auto.
    - (* x₁ := e₁  ‖  x₂ := M₂[q̄] *)
      rewrite (eval_expr_update_notin _ _ _ _ e1 (disjoint_single x2 _ Hrc)).
      apply store_update_comm.
      intro Hxy; apply (disjoint_single x1 _ Hcc); left; auto.
    - (* x₁ := M₁[q̄]  ‖  x₂ := e₂ *)
      rewrite (eval_expr_update_notin _ _ _ _ e2 (disjoint_single x1 _ Hcr)).
      apply store_update_comm.
      intro Hxy; apply (disjoint_single x1 _ Hcc); left; auto.
    - (* x₁ := M₁[q̄]  ‖  x₂ := M₂[q̄] *)
      apply store_update_comm.
      intro Hxy; apply (disjoint_single x1 _ Hcc); left; auto.
  Qed.

  (* ---- obligation 2: the state maps commute ------------------------- *)

  Lemma super_super : forall (A B : Square (2 ^ dim)) (r : qstate dim),
      super A (super B r) = super (A × B)%M r.
  Proof.
    intros A B r; unfold super.
    rewrite Mmult_adjoint, !Mmult_assoc; reflexivity.
  Qed.

  Lemma super_comm : forall (A B : Square (2 ^ dim)) (r : qstate dim),
      (A × B = B × A)%M -> super A (super B r) = super B (super A r).
  Proof. intros A B r H; rewrite !super_super, H; reflexivity. Qed.

  Lemma super_plus : forall (A : Square (2 ^ dim)) (X Y : qstate dim),
      super A (X .+ Y)%M = (super A X .+ super A Y)%M.
  Proof.
    intros A X Y; unfold super.
    rewrite Mmult_plus_distr_l, Mmult_plus_distr_r; reflexivity.
  Qed.

  Lemma apply_init_eq : forall q (r : qstate dim),
      apply_init q r
      = (super (pad_u dim q (∣0⟩⟨0∣)) r .+ super (pad_u dim q (∣0⟩⟨1∣)) r)%M.
  Proof. reflexivity. Qed.

  Lemma apply_init_plus : forall q (X Y : qstate dim),
      @apply_init dim q (X .+ Y)%M = (apply_init q X .+ apply_init q Y)%M.
  Proof. intros q X Y; rewrite !apply_init_eq, !super_plus; lma. Qed.

  Lemma super_init_comm : local_ops ->
    forall (A : Square (2 ^ dim)) (qs : list qvar) (q : qvar) (r : qstate dim),
      acts_on A qs -> disjoint qs (q :: nil) ->
      super A (apply_init q r) = apply_init q (super A r).
  Proof.
    intros Hloc A qs q r HA Hd.
    rewrite !apply_init_eq, super_plus.
    rewrite (super_comm _ _ _ (Hloc _ _ _ _ HA (acts_init0 q) Hd)).
    rewrite (super_comm _ _ _ (Hloc _ _ _ _ HA (acts_init1 q) Hd)).
    reflexivity.
  Qed.

  Lemma apply_init_comm : local_ops -> forall q1 q2 (r : qstate dim),
      disjoint (q1 :: nil) (q2 :: nil) ->
      apply_init q1 (apply_init q2 r) = apply_init q2 (apply_init q1 r).
  Proof.
    intros Hloc q1 q2 r Hd.
    rewrite (apply_init_eq q1 (apply_init q2 r)).
    rewrite (super_init_comm Hloc _ (q1 :: nil) q2 r (acts_init0 q1) Hd).
    rewrite (super_init_comm Hloc _ (q1 :: nil) q2 r (acts_init1 q1) Hd).
    rewrite <- apply_init_plus, <- apply_init_eq. reflexivity.
  Qed.

  Lemma aqmap_comm : local_ops -> forall L1 L2,
      atomic L1 -> atomic L2 -> disjoint (lblock_qvar L1) (lblock_qvar L2) ->
      forall j1 j2 r, aqmap L1 j1 (aqmap L2 j2 r) = aqmap L2 j2 (aqmap L1 j1 r).
  Proof.
    intros Hloc L1 L2 H1 H2 Hq j1 j2 r;
      destruct L1 as [| x1 e1 | q1 | U1 qs1 | x1 M1 qs1 | ? ? | ? ? ?];
      destruct L2 as [| x2 e2 | q2 | U2 qs2 | x2 M2 qs2 | ? ? | ? ? ?];
      try contradiction; cbn [aqmap lblock_qvar] in *; try reflexivity;
      unfold apply_unitary, apply_meas.
    - (* q₁ := |0>  ‖  q₂ := |0> *) apply apply_init_comm; assumption.
    - (* q₁ := |0>  ‖  U₂[q̄₂] *)
      symmetry.
      apply (super_init_comm Hloc _ qs2 q1 r (acts_ugate U2 qs2)
               (disjoint_sym _ _ Hq)).
    - (* q₁ := |0>  ‖  x₂ := M₂[q̄₂] *)
      symmetry.
      apply (super_init_comm Hloc _ qs2 q1 r (acts_meas M2 qs2 j2)
               (disjoint_sym _ _ Hq)).
    - (* U₁[q̄₁]  ‖  q₂ := |0> *)
      apply (super_init_comm Hloc _ qs1 q2 r (acts_ugate U1 qs1) Hq).
    - (* U₁[q̄₁]  ‖  U₂[q̄₂] *)
      apply super_comm.
      exact (Hloc _ _ _ _ (acts_ugate U1 qs1) (acts_ugate U2 qs2) Hq).
    - (* U₁[q̄₁]  ‖  x₂ := M₂[q̄₂] *)
      apply super_comm.
      exact (Hloc _ _ _ _ (acts_ugate U1 qs1) (acts_meas M2 qs2 j2) Hq).
    - (* x₁ := M₁[q̄₁]  ‖  q₂ := |0> *)
      apply (super_init_comm Hloc _ qs1 q2 r (acts_meas M1 qs1 j1) Hq).
    - (* x₁ := M₁[q̄₁]  ‖  U₂[q̄₂] *)
      apply super_comm.
      exact (Hloc _ _ _ _ (acts_meas M1 qs1 j1) (acts_ugate U2 qs2) Hq).
    - (* x₁ := M₁[q̄₁]  ‖  x₂ := M₂[q̄₂] *)
      apply super_comm.
      exact (Hloc _ _ _ _ (acts_meas M1 qs1 j1) (acts_meas M2 qs2 j2) Hq).
  Qed.

  (* ---- a filter sees through a block that never writes its guard ---- *)

  Definition store_indep (p : store -> bool) (xs : list var) : Prop :=
    forall s x v, In x xs -> p (s [ x |-> v ]) = p s.

  Lemma store_indep_app : forall p xs ys,
      store_indep p (xs ++ ys) -> store_indep p xs /\ store_indep p ys.
  Proof.
    intros p xs ys H; split; intros s x v Hx; apply H, in_or_app;
      [left | right]; exact Hx.
  Qed.

  Lemma store_indep_guard : forall b xs,
      disjoint xs (bexpr_vars b) ->
      store_indep (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) xs.
  Proof.
    intros b xs Hd s x v Hx.
    apply eval_bool_update_notin, Hd, Hx.
  Qed.

  Lemma store_indep_negb : forall p xs,
      store_indep p xs -> store_indep (fun s => negb (p s)) xs.
  Proof. intros p xs H s x v Hx; cbn; rewrite H; [reflexivity | exact Hx]. Qed.

  Lemma filter_comm : forall {A} (f g : A -> bool) (l : list A),
      filter f (filter g l) = filter g (filter f l).
  Proof.
    intros A f g l; induction l as [| a l IH]; simpl; [reflexivity |].
    destruct (f a) eqn:Ef; destruct (g a) eqn:Eg; simpl;
      rewrite ?Ef, ?Eg, IH; reflexivity.
  Qed.

  Lemma ensemble_filter_comm : forall (p q : store -> bool) (E : ensemble dim),
      ensemble_filter p (ensemble_filter q E)
      = ensemble_filter q (ensemble_filter p E).
  Proof. intros; unfold ensemble_filter; apply filter_comm. Qed.

  Lemma ensemble_filter_app : forall (p : store -> bool) (E1 E2 : ensemble dim),
      ensemble_filter p (E1 ++ E2)
      = ensemble_filter p E1 ++ ensemble_filter p E2.
  Proof. intros; unfold ensemble_filter; apply filter_app. Qed.

  Lemma denote_filter_comm :
    forall (p : store -> bool) (L : lblock) (E : ensemble dim),
      store_indep p (lblock_change L) ->
      ensemble_filter p (denote L E) = denote L (ensemble_filter p E).
  Proof.
    intros p L;
      induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intros E H; cbn [denote lblock_change] in *.
    - (* skip *) reflexivity.
    - (* x := e *)
      unfold ensemble_filter;
        induction E as [| [s r] E IH]; cbn [map filter fst]; [reflexivity |].
      rewrite (H s x (eval_expr (i_fn Σ) s e) (or_introl eq_refl)).
      destruct (p s); cbn [map filter fst]; rewrite IH; reflexivity.
    - (* q := |0> *)
      unfold ensemble_filter;
        induction E as [| [s r] E IH]; cbn [map filter fst]; [reflexivity |].
      destruct (p s); cbn [map filter fst]; rewrite IH; reflexivity.
    - (* U[q̄] *)
      unfold ensemble_filter;
        induction E as [| [s r] E IH]; cbn [map filter fst]; [reflexivity |].
      destruct (p s); cbn [map filter fst]; rewrite IH; reflexivity.
    - (* x := M[q̄] *)
      unfold ensemble_filter;
        induction E as [| [s r] E IH]; cbn [flat_map filter fst]; [reflexivity |].
      assert (Hgrp : forall (T : list nat) (g : nat -> qstate dim),
                 filter (fun st => p (fst st))
                        (map (fun m => (s [ x |-> m ], g m)) T)
                 = if p s then map (fun m => (s [ x |-> m ], g m)) T else nil).
      { induction T as [| m T IHT]; intros g; cbn [map filter fst];
          [destruct (p s); reflexivity |].
        rewrite (H s x m (or_introl eq_refl)), (IHT g).
        destruct (p s); reflexivity. }
      rewrite filter_app, (Hgrp (fst (i_mm Σ M qs))), IH.
      destruct (p s); cbn [flat_map]; reflexivity.
    - (* L1 ; L2 *)
      destruct (store_indep_app _ _ _ H) as [Ha Hb].
      rewrite IH2, IH1; [reflexivity | exact Ha | exact Hb].
    - (* if b then L1 else L0 *)
      destruct (store_indep_app _ _ _ H) as [Ha Hb].
      rewrite ensemble_filter_app, IH1, IH0; [| exact Hb | exact Ha].
      rewrite (ensemble_filter_comm p (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E).
      rewrite (ensemble_filter_comm p
                 (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E).
      reflexivity.
  Qed.

  (* ---- non-interference is symmetric and inherited by sub-blocks ----- *)

  Lemma non_interfering_sym : forall L1 L2,
      non_interfering L1 L2 -> non_interfering L2 L1.
  Proof.
    intros L1 L2 (H1 & H2 & H3 & H4); repeat split;
      auto using disjoint_sym.
  Qed.

  Lemma non_interfering_incl : forall L L' M,
      incl (lblock_change L') (lblock_change L) ->
      incl (lblock_read L') (lblock_read L) ->
      incl (lblock_qvar L') (lblock_qvar L) ->
      non_interfering L M -> non_interfering L' M.
  Proof.
    intros L L' M Hc Hr Hq (H1 & H2 & H3 & H4); repeat split.
    - eapply disjoint_incl; [exact H1 | exact Hc | apply incl_refl].
    - eapply disjoint_incl; [exact H2 | exact Hc | apply incl_refl].
    - eapply disjoint_incl; [exact H3 | apply incl_refl | exact Hr].
    - eapply disjoint_incl; [exact H4 | exact Hq | apply incl_refl].
  Qed.

  Lemma non_interfering_seq : forall A B M,
      non_interfering (l_seq A B) M -> non_interfering A M /\ non_interfering B M.
  Proof.
    intros A B M H; split; eapply non_interfering_incl; try exact H;
      cbn [lblock_change lblock_read lblock_qvar];
      auto using incl_appl, incl_appr, incl_refl.
  Qed.

  Lemma non_interfering_if : forall b A B M,
      non_interfering (l_if b A B) M ->
      non_interfering A M /\ non_interfering B M.
  Proof.
    intros b A B M H; split; eapply non_interfering_incl; try exact H;
      cbn [lblock_change lblock_read lblock_qvar];
      auto using incl_appl, incl_appr, incl_refl.
  Qed.

  Lemma non_interfering_guard : forall b A B M,
      non_interfering (l_if b A B) M ->
      disjoint (lblock_change M) (bexpr_vars b).
  Proof.
    intros b A B M (_ & _ & H3 & _).
    eapply disjoint_incl; [exact H3 | apply incl_refl |].
    cbn [lblock_read]; apply incl_appl, incl_refl.
  Qed.

  (** Two non-interfering ATOMIC blocks commute. **)
  Lemma denote_atom_comm : local_ops ->
    forall L1 L2, atomic L1 -> atomic L2 -> non_interfering L1 L2 ->
      forall E, Permutation (denote L1 (denote L2 E)) (denote L2 (denote L1 E)).
  Proof.
    intros Hloc L1 L2 H1 H2 (Hcc & Hcr & Hrc & Hq) E.
    rewrite !(denote_atomic L1 H1), !(denote_atomic L2 H2).
    apply act_comm.
    - apply astore_comm; assumption.
    - apply aqmap_comm; assumption.
  Qed.

  (** …then an atomic block commutes with an arbitrary one, by induction on
      the arbitrary one.  [if] is where the classical footprint earns its
      keep: the guard must read the same store on both sides. **)
  Lemma denote_comm_atom : local_ops ->
    forall L2 L1, atomic L1 -> non_interfering L1 L2 ->
      forall E, Permutation (denote L1 (denote L2 E)) (denote L2 (denote L1 E)).
  Proof.
    intros Hloc L2;
      induction L2 as [| x e | q | U qs | x M qs | A IHA B IHB | b A IHA B IHB];
      intros L1 H1 Hni E.
    1-5: apply denote_atom_comm; [exact Hloc | exact H1 | constructor | exact Hni].
    - (* A ; B *)
      destruct (non_interfering_seq A B L1 (non_interfering_sym _ _ Hni))
        as [HA HB].
      cbn [denote].
      eapply Permutation_trans;
        [ apply (IHB L1 H1 (non_interfering_sym _ _ HB)) |].
      apply denote_perm, (IHA L1 H1 (non_interfering_sym _ _ HA)).
    - (* if b then A else B *)
      destruct (non_interfering_if b A B L1 (non_interfering_sym _ _ Hni))
        as [HA HB].
      pose proof (non_interfering_guard b A B L1
                    (non_interfering_sym _ _ Hni)) as Hg.
      cbn [denote].
      eapply Permutation_trans; [apply denote_app |].
      eapply Permutation_trans.
      { apply Permutation_app;
          [ apply (IHA L1 H1 (non_interfering_sym _ _ HA))
          | apply (IHB L1 H1 (non_interfering_sym _ _ HB)) ]. }
      rewrite (denote_filter_comm _ L1 E (store_indep_guard b _ Hg)).
      rewrite (denote_filter_comm _ L1 E
                 (store_indep_negb _ _ (store_indep_guard b _ Hg))).
      apply Permutation_refl.
  Qed.

  (** Paper Lemma 1: two non-interfering local blocks commute. **)
  Lemma denote_comm : local_ops ->
    forall L1 L2, non_interfering L1 L2 ->
      forall E, Permutation (denote L1 (denote L2 E)) (denote L2 (denote L1 E)).
  Proof.
    intros Hloc L1;
      induction L1 as [| x e | q | U qs | x M qs | A IHA B IHB | b A IHA B IHB];
      intros L2 Hni E.
    1-5: apply (denote_comm_atom Hloc L2); [constructor | exact Hni].
    - (* A ; B *)
      destruct (non_interfering_seq A B L2 Hni) as [HA HB].
      cbn [denote].
      eapply Permutation_trans; [apply denote_perm, (IHA L2 HA) |].
      apply (IHB L2 HB).
    - (* if b then A else B *)
      destruct (non_interfering_if b A B L2 Hni) as [HA HB].
      pose proof (non_interfering_guard b A B L2 Hni) as Hg.
      cbn [denote].
      rewrite (denote_filter_comm _ L2 E (store_indep_guard b _ Hg)).
      rewrite (denote_filter_comm _ L2 E
                 (store_indep_negb _ _ (store_indep_guard b _ Hg))).
      eapply Permutation_trans;
        [ apply Permutation_app; [apply (IHA L2 HA) | apply (IHB L2 HB)] |].
      apply Permutation_sym, denote_app.
  Qed.

  (** ** 5. Normalising an interleaving ********************************

      A program all of whose leaves are communication-free denotes as the
      sequentialisation of the blocks its leaves still owe.  Every step
      preserves that denotation — Lemma 1 is what pays for a step taken out
      of displayed order — so a terminal collapse IS it.
  *********************************************************************)

  (* ---- footprints of a sequentialised row --------------------------- *)

  Lemma lblock_change_lseq : forall d,
      lblock_change (lseq d) = row_flat lblock_change d.
  Proof. induction d as [D | d1 IH1 d2 IH2]; simpl; congruence. Qed.

  Lemma lblock_read_lseq : forall d,
      lblock_read (lseq d) = row_flat lblock_read d.
  Proof. induction d as [D | d1 IH1 d2 IH2]; simpl; congruence. Qed.

  Lemma lblock_qvar_lseq : forall d,
      lblock_qvar (lseq d) = row_flat lblock_qvar d.
  Proof. induction d as [D | d1 IH1 d2 IH2]; simpl; congruence. Qed.

  Lemma disjoint_flat_map : forall {A} (f g : A -> list nat) (l1 l2 : list A),
      (forall a b, In a l1 -> In b l2 -> disjoint (f a) (g b)) ->
      disjoint (flat_map f l1) (flat_map g l2).
  Proof.
    intros A f g l1 l2 H z Hz1 Hz2.
    apply in_flat_map in Hz1 as (a & Ha & Hza).
    apply in_flat_map in Hz2 as (b & Hb & Hzb).
    exact (H a b Ha Hb z Hza Hzb).
  Qed.

  (** Pairwise non-interference of the leaves is non-interference of the
      two sequentialisations — the step from DisjMP to Lemma 1. **)
  Lemma non_interfering_lseq : forall d1 d2,
      (forall D1 D2, In D1 (row_leaves d1) -> In D2 (row_leaves d2) ->
                     non_interfering D1 D2) ->
      non_interfering (lseq d1) (lseq d2).
  Proof.
    intros d1 d2 H; split; [| split; [| split]].
    - rewrite !lblock_change_lseq, !row_flat_leaves.
      apply disjoint_flat_map; intros a b Ha Hb; exact (proj1 (H a b Ha Hb)).
    - rewrite lblock_change_lseq, lblock_read_lseq, !row_flat_leaves.
      apply disjoint_flat_map; intros a b Ha Hb.
      exact (proj1 (proj2 (H a b Ha Hb))).
    - rewrite lblock_change_lseq, lblock_read_lseq, !row_flat_leaves.
      apply disjoint_flat_map; intros a b Ha Hb.
      exact (proj1 (proj2 (proj2 (H b a Hb Ha)))).
    - rewrite !lblock_qvar_lseq, !row_flat_leaves.
      apply disjoint_flat_map; intros a b Ha Hb.
      exact (proj2 (proj2 (proj2 (H a b Ha Hb)))).
  Qed.

  Lemma ForallOrdPairs_app_inv : forall {A} (R : A -> A -> Prop) (l1 l2 : list A),
      ForallOrdPairs R (l1 ++ l2) ->
      ForallOrdPairs R l1 /\ ForallOrdPairs R l2
      /\ (forall x y, In x l1 -> In y l2 -> R x y).
  Proof.
    intros A R l1; induction l1 as [| a l1 IH]; intros l2 H; simpl in H.
    - split; [constructor | split; [exact H | intros x y []]].
    - inversion H as [| a' l' Hhd Htl]; subst.
      destruct (IH l2 Htl) as (H1 & H2 & H3).
      apply Forall_app in Hhd as [Hh1 Hh2].
      split; [constructor; assumption | split; [exact H2 |]].
      intros x y [Hx | Hx] Hy;
        [subst x; rewrite Forall_forall in Hh2; apply Hh2, Hy
        | apply H3; assumption].
  Qed.

  (* ---- a step only shrinks a leaf's footprint ----------------------- *)

  Definition footprint_le (D' D : lblock) : Prop :=
    incl (lblock_change D') (lblock_change D)
    /\ incl (lblock_read D') (lblock_read D)
    /\ incl (lblock_qvar D') (lblock_qvar D).

  Definition blocks_le (d' d : lrow) : Prop :=
    Forall2 footprint_le (row_leaves d') (row_leaves d).

  Lemma blocks_le_refl : forall d, blocks_le d d.
  Proof.
    intro d; unfold blocks_le.
    induction (row_leaves d) as [| D l IH]; constructor;
      [repeat split; apply incl_refl | exact IH].
  Qed.

  Lemma blocks_le_par : forall a' a b' b,
      blocks_le a' a -> blocks_le b' b -> blocks_le (par a' b') (par a b).
  Proof.
    intros a' a b' b Ha Hb; unfold blocks_le; simpl; apply Forall2_app; assumption.
  Qed.

  Lemma non_interfering_le : forall D1' D1 D2' D2,
      footprint_le D1' D1 -> footprint_le D2' D2 ->
      non_interfering D1 D2 -> non_interfering D1' D2'.
  Proof.
    intros D1' D1 D2' D2 (Hc1 & Hr1 & Hq1) (Hc2 & Hr2 & Hq2) (H1 & H2 & H3 & H4);
      split; [| split; [| split]].
    - eapply disjoint_incl; [exact H1 | exact Hc1 | exact Hc2].
    - eapply disjoint_incl; [exact H2 | exact Hc1 | exact Hr2].
    - eapply disjoint_incl; [exact H3 | exact Hc2 | exact Hr1].
    - eapply disjoint_incl; [exact H4 | exact Hq1 | exact Hq2].
  Qed.

  Lemma Forall2_In : forall {A B} (R : A -> B -> Prop) (l : list A) (m : list B) a,
      Forall2 R l m -> In a l -> exists b, In b m /\ R a b.
  Proof.
    intros A B R l m a H; induction H as [| x y l m Hxy Hl IH]; intros Hin.
    - destruct Hin.
    - destruct Hin as [Heq | Hin];
        [subst x; exists y; split; [left; reflexivity | exact Hxy] |].
      destruct (IH Hin) as (b & Hb & HRb).
      exists b; split; [right; exact Hb | exact HRb].
  Qed.

  Lemma Forall2_Forall_ni : forall (D' D : lblock) (l' l : list lblock),
      footprint_le D' D -> Forall2 footprint_le l' l ->
      Forall (non_interfering D) l -> Forall (non_interfering D') l'.
  Proof.
    intros D' D l' l HD H; induction H as [| a' a l1' l1 Ha Hl IH]; intros Hf.
    - constructor.
    - inversion Hf as [| ? ? Hh Ht]; subst.
      constructor; [eapply non_interfering_le; eassumption | apply IH, Ht].
  Qed.

  Lemma blocks_le_disj : forall d' d, blocks_le d' d -> lrow_disj d -> lrow_disj d'.
  Proof.
    unfold lrow_disj, DisjMP, blocks_le.
    intros d' d H; revert H; generalize (row_leaves d') (row_leaves d); clear d' d.
    intros l' l H; induction H as [| a' a l1' l1 Ha Hl IH]; intros Hop.
    - constructor.
    - inversion Hop as [| x xs Hf Hrest]; subst.
      constructor; [eapply Forall2_Forall_ni; eassumption | apply IH, Hrest].
  Qed.

  (** The cross condition survives a step on one side. **)
  Lemma blocks_le_cross : forall d1 d2' d2,
      blocks_le d2' d2 ->
      (forall D1 D2, In D1 (row_leaves d1) -> In D2 (row_leaves d2) ->
                     non_interfering D1 D2) ->
      forall D2' D1, In D2' (row_leaves d2') -> In D1 (row_leaves d1) ->
                     non_interfering D2' D1.
  Proof.
    intros d1 d2' d2 Hle Hcross D2' D1 H2' H1.
    destruct (Forall2_In _ _ _ _ Hle H2') as (D2 & HD2 & Hfp).
    eapply non_interfering_le;
      [ exact Hfp | repeat split; apply incl_refl
      | apply non_interfering_sym, Hcross; assumption ].
  Qed.

  (* ---- the blocks a program still owes ------------------------------ *)

  Definition proc_block (T : process) : lblock :=
    match T with terminated => l_skip | phase R _ _ => residual_lblock R end.

  Definition prog_blocks (P : program) : lrow := row_map proc_block P.
  Definition prog_lseq (P : program) : lblock := lseq (prog_blocks P).

  (** The execution invariant of a communication-free row: every leaf is ↓
      or a single local block with an exhausted phase behind it. **)
  Definition dleaf (T : process) : Prop :=
    T = terminated \/ exists L, T = phase (r_more L) nil terminated.
  Definition dshape (P : program) : Prop := row_all dleaf P.

  Lemma row_all_map : forall {A B} (Q : B -> Prop) (f : A -> B) (r : row A),
      (forall a, Q (f a)) -> row_all Q (row_map f r).
  Proof. intros A B Q f r H; induction r; simpl; auto. Qed.

  Lemma row_all_in : forall {A} (Q : A -> Prop) (r : row A) (a : A),
      row_all Q r -> In a (row_leaves r) -> Q a.
  Proof.
    intros A Q r; induction r as [b | r1 IH1 r2 IH2]; intros a H Hin; simpl in *.
    - destruct Hin as [Heq | []]; subst; exact H.
    - destruct H as [H1 H2]; apply in_app_or in Hin as [Hin | Hin];
        [apply IH1 | apply IH2]; assumption.
  Qed.

  Lemma replace_leaf_in : forall {A} (a b : A) (r r' : row A),
      replace_leaf a b r r' -> In a (row_leaves r).
  Proof.
    intros A a b r r' H; induction H; simpl;
      [left; reflexivity | apply in_or_app; left | apply in_or_app; right];
      assumption.
  Qed.

  Lemma prog_blocks_map : forall (f : lblock -> process),
      (forall D, proc_block (f D) = D) -> forall d, prog_blocks (row_map f d) = d.
  Proof.
    intros f Hf d; unfold prog_blocks;
      induction d as [D | d1 IH1 d2 IH2]; simpl; congruence.
  Qed.

  Lemma prog_lseq_par : forall P1 P2,
      prog_lseq (par P1 P2) = l_seq (prog_lseq P1) (prog_lseq P2).
  Proof. reflexivity. Qed.

  Lemma proc_block_advance : forall R,
      proc_block (advance R nil terminated) = residual_lblock R.
  Proof. intros [| L]; reflexivity. Qed.

  Lemma denote_residual_lblock : forall R E,
      denote (residual_lblock R) E = residual_denote R E.
  Proof. intros [| L] E; reflexivity. Qed.

  Lemma residual_lblock_change : forall R,
      lblock_change (residual_lblock R) = residual_change R.
  Proof. intros [| L]; reflexivity. Qed.

  Lemma residual_lblock_read : forall R,
      lblock_read (residual_lblock R) = residual_read R.
  Proof. intros [| L]; reflexivity. Qed.

  Lemma residual_lblock_qvar : forall R,
      lblock_qvar (residual_lblock R) = residual_qvar R.
  Proof. intros [| L]; reflexivity. Qed.

  Lemma prog_terminated_lseq : forall P E,
      prog_terminated P -> denote (prog_lseq P) E = E.
  Proof.
    intros P; induction P as [T | P1 IH1 P2 IH2]; intros E HT.
    - cbn in HT; subst T; reflexivity.
    - destruct HT as [H1 H2]; rewrite prog_lseq_par; cbn [denote].
      rewrite IH1, IH2; auto.
  Qed.

  (* ---- a step preserves the shape and shrinks the blocks ------------ *)

  Lemma local_step_residual_qvar :
    forall (L : lblock) (E : ensemble dim) (G : local_config dim),
      Σ ⊳ ‹ L, E › →ₗ G ->
      Forall (fun c => incl (residual_qvar (fst c)) (lblock_qvar L)) G.
  Proof.
    intros L E G Hstep; induction Hstep;
      cbn [residual_qvar lblock_qvar].
    1-5: constructor; [apply incl_nil_l | constructor].
    - (* seq *)
      rewrite Forall_map. eapply Forall_impl; [| exact IHHstep].
      intros [rd Ee] Hq; cbn [fst] in *.
      destruct rd; cbn [residual_qvar lblock_qvar] in *; intros z Hz.
      + apply in_or_app; right; exact Hz.
      + apply in_app_or in Hz; apply in_or_app;
          destruct Hz; [left; apply Hq | right]; auto.
    - (* if *)
      constructor; [| constructor; [| constructor]];
        cbn [fst residual_qvar]; intros z Hz; apply in_or_app;
        [left | right]; exact Hz.
  Qed.

  Lemma dstep_shape_blocks :
    forall (P : program) (E : ensemble dim) (G : distri_config dim),
      Σ ⊳ ‹ P, E › ⇝ G -> dshape P ->
      Forall (fun c => dshape (fst c)
                       /\ blocks_le (prog_blocks (fst c)) (prog_blocks P)) G.
  Proof.
    intros P E G Hstep; induction Hstep; intros Hsh.
    - (* ds_local *)
      cbn [row_all] in Hsh; destruct Hsh as [Hbad | (L0 & HL0)]; [discriminate |].
      inversion HL0; subst.
      pose proof (local_step_residual_incl _ _ _ H) as Hcr.
      pose proof (local_step_residual_qvar _ _ _ H) as Hqv.
      rewrite Forall_map. eapply Forall_impl with
        (P := fun c => (incl (residual_change (fst c)) (lblock_change L0)
                        /\ incl (residual_read (fst c)) (lblock_read L0))
                       /\ incl (residual_qvar (fst c)) (lblock_qvar L0)).
      2:{ apply Forall_and; assumption. }
      intros [rd Ee] [[Hc Hr] Hq]; cbn [fst] in *; split.
      + cbn [row_all]; destruct rd; cbn [advance];
          [left; reflexivity | right; eexists; reflexivity].
      + unfold blocks_le, prog_blocks; cbn [row_map row_leaves].
        constructor; [| constructor].
        unfold footprint_le; rewrite proc_block_advance.
        cbn [proc_block residual_lblock].
        rewrite residual_lblock_change, residual_lblock_read,
                residual_lblock_qvar.
        repeat split; assumption.
    - (* ds_par_l *)
      destruct Hsh as [Hs1 Hs2].
      rewrite Forall_map. eapply Forall_impl; [| exact (IHHstep Hs1)].
      intros [Pp Ee] [Hs Hb]; cbn [fst] in *; split.
      + split; assumption.
      + apply blocks_le_par; [exact Hb | apply blocks_le_refl].
    - (* ds_par_r *)
      destruct Hsh as [Hs1 Hs2].
      rewrite Forall_map. eapply Forall_impl; [| exact (IHHstep Hs2)].
      intros [Pp Ee] [Hs Hb]; cbn [fst] in *; split.
      + split; assumption.
      + apply blocks_le_par; [apply blocks_le_refl | exact Hb].
    - (* ds_comm_lr — an all-ε row has no ↓;K leaf *)
      exfalso; destruct Hsh as [Hs1 _].
      destruct (row_all_in _ _ _ Hs1 (replace_leaf_in _ _ _ _ H1))
        as [Hbad | (L0 & Hbad)]; discriminate.
    - (* ds_comm_rl *)
      exfalso; destruct Hsh as [Hs1 _].
      destruct (row_all_in _ _ _ Hs1 (replace_leaf_in _ _ _ _ H2))
        as [Hbad | (L0 & Hbad)]; discriminate.
  Qed.

  (* ---- the denotation of a mixed configuration ---------------------- *)

  Definition ddenote (G : distri_config dim) : ensemble dim :=
    flat_map (fun c => denote (prog_lseq (fst c)) (snd c)) G.

  Definition dcfg_ok (G : distri_config dim) : Prop :=
    Forall (fun c => dshape (fst c) /\ lrow_disj (prog_blocks (fst c))) G.

  Lemma ddenote_app : forall G1 G2 : distri_config dim,
      ddenote (G1 ⊎ G2) = ddenote G1 ++ ddenote G2.
  Proof. intros; unfold ddenote; apply flat_map_app. Qed.

  Lemma ddenote_norm : forall G, ddenote (norm G) = ddenote G.
  Proof.
    intros G; induction G as [| [P E] G IH]; [reflexivity |].
    unfold norm, ddenote in *; simpl.
    destruct E as [| st E']; simpl;
      [rewrite IH, denote_nil | rewrite IH]; reflexivity.
  Qed.

  Lemma denote_flat_map_gen :
    forall {A} (L : lblock) (f : A -> ensemble dim) (l : list A),
      Permutation (flat_map (fun a => denote L (f a)) l) (denote L (flat_map f l)).
  Proof.
    intros A L f l; induction l as [| a l IH]; simpl.
    - rewrite denote_nil; apply Permutation_refl.
    - eapply Permutation_trans; [apply Permutation_app_head, IH |].
      apply Permutation_sym, denote_app.
  Qed.

  Lemma dstep_denote : local_ops ->
    forall (P : program) (E : ensemble dim) (G : distri_config dim),
      Σ ⊳ ‹ P, E › ⇝ G -> dshape P -> lrow_disj (prog_blocks P) ->
      Permutation (ddenote G) (denote (prog_lseq P) E).
  Proof.
    intros Hloc P E G Hstep; induction Hstep; intros Hsh Hdisj.
    - (* ds_local: the leaf's own block steps, in place *)
      cbn [row_all] in Hsh; destruct Hsh as [Hbad | (L0 & HL0)]; [discriminate |].
      inversion HL0; subst.
      unfold ddenote; rewrite flat_map_map; cbn [fst snd].
      rewrite (flat_map_ext' _ (fun c => residual_denote (fst c) (snd c)) Gl)
        by (intros [rd Ee]; cbn [fst snd];
            unfold prog_lseq, prog_blocks; cbn [row_map lseq];
            rewrite proc_block_advance; apply denote_residual_lblock).
      eapply local_step_denote; eassumption.
    - (* ds_par_l: the step is already leftmost *)
      destruct Hsh as [Hs1 Hs2].
      unfold lrow_disj in Hdisj; cbn [prog_blocks row_map row_leaves] in Hdisj.
      destruct (ForallOrdPairs_app_inv _ _ _ Hdisj) as (Hd1 & Hd2 & Hcross).
      rewrite prog_lseq_par; cbn [denote].
      unfold ddenote; rewrite flat_map_map; cbn [fst snd].
      rewrite (flat_map_ext' _
                 (fun c => denote (prog_lseq P2) (denote (prog_lseq (fst c)) (snd c)))
                 G1)
        by (intros c; rewrite prog_lseq_par; reflexivity).
      eapply Permutation_trans; [apply denote_flat_map_gen |].
      apply denote_perm, (IHHstep Hs1 Hd1).
    - (* ds_par_r: the step is out of displayed order — Lemma 1 pays *)
      destruct Hsh as [Hs1 Hs2].
      unfold lrow_disj in Hdisj; cbn [prog_blocks row_map row_leaves] in Hdisj.
      destruct (ForallOrdPairs_app_inv _ _ _ Hdisj) as (Hd1 & Hd2 & Hcross).
      pose proof (dstep_shape_blocks _ _ _ Hstep Hs2) as Hbl.
      rewrite prog_lseq_par; cbn [denote].
      unfold ddenote; rewrite flat_map_map; cbn [fst snd].
      rewrite (flat_map_ext' _
                 (fun c => denote (prog_lseq (fst c)) (denote (prog_lseq P1) (snd c)))
                 G2)
        by (intros c; rewrite prog_lseq_par; reflexivity).
      rewrite Forall_forall in Hbl.
      eapply Permutation_trans.
      { apply Permutation_flat_map_in; intros c Hc.
        apply denote_comm; [exact Hloc |].
        apply non_interfering_lseq.
        eapply blocks_le_cross;
          [ exact (proj2 (Hbl c Hc)) | exact Hcross ]. }
      eapply Permutation_trans; [apply denote_flat_map_gen |].
      eapply Permutation_trans;
        [ apply denote_perm, (IHHstep Hs2 Hd2) |].
      apply denote_comm; [exact Hloc |].
      apply non_interfering_lseq, Hcross.
    - (* ds_comm_lr — ruled out: no leaf carries a pending endpoint *)
      exfalso; destruct Hsh as [Hs1 _].
      destruct (row_all_in _ _ _ Hs1 (replace_leaf_in _ _ _ _ H1))
        as [Hbad | (L0 & Hbad)]; discriminate.
    - (* ds_comm_rl *)
      exfalso; destruct Hsh as [Hs1 _].
      destruct (row_all_in _ _ _ Hs1 (replace_leaf_in _ _ _ _ H2))
        as [Hbad | (L0 & Hbad)]; discriminate.
  Qed.

  Lemma mixed_denote : local_ops -> forall (G G' : distri_config dim),
      mixed_step Σ G G' -> dcfg_ok G ->
      dcfg_ok G' /\ Permutation (ddenote G') (ddenote G).
  Proof.
    intros Hloc G G' Hstep Hok.
    destruct Hstep as [G D E G0 G1 Hperm Hd].
    pose proof (Permutation_Forall Hperm Hok) as Hok'.
    inversion Hok' as [| c G0' HD HG0]; subst.
    destruct HD as [Hsh Hdisj]; cbn [fst] in Hsh, Hdisj.
    split.
    - apply Forall_filter_keep, Forall_app; split; [| exact HG0].
      pose proof (dstep_shape_blocks _ _ _ Hd Hsh) as Hbl.
      eapply Forall_impl; [| exact Hbl].
      intros c0 [Hs Hb]; split; [exact Hs | eapply blocks_le_disj; eassumption].
    - rewrite ddenote_norm, ddenote_app.
      eapply Permutation_trans.
      + apply Permutation_app_tail. eapply dstep_denote; eassumption.
      + apply Permutation_sym.
        eapply Permutation_trans.
        * unfold ddenote; apply permutation_flat_map; exact Hperm.
        * unfold ddenote; simpl; apply Permutation_refl.
  Qed.

  Lemma star_denote : local_ops -> forall (G G' : distri_config dim),
      step_star Σ G G' -> dcfg_ok G ->
      dcfg_ok G' /\ Permutation (ddenote G') (ddenote G).
  Proof.
    intros Hloc G G' Hstar; induction Hstar as [G | G1 G2 G3 Hmix Hstar IH];
      intros Hok.
    - split; [assumption | apply Permutation_refl].
    - destruct (mixed_denote Hloc _ _ Hmix Hok) as [Hok2 Hp2].
      destruct (IH Hok2) as [Hok3 Hp3].
      split; [assumption | eapply Permutation_trans; eauto].
  Qed.

  Lemma terminal_ddenote : forall (G : distri_config dim),
      terminal G -> ddenote G = collapse G.
  Proof.
    intros G Hterm; unfold terminal in Hterm.
    induction Hterm as [| [P E] G' HP HF IH]; [reflexivity |].
    unfold ddenote, collapse in *; simpl. rewrite IH. f_equal.
    cbn [fst snd] in HP |- *. apply prog_terminated_lseq, HP.
  Qed.

  (** Adequacy for a communication-free row: the terminal collapse of ANY
      interleaving is the denotation of the DISPLAYED sequentialisation. **)
  Lemma prog_adequacy : local_ops ->
    forall (P : program) (st : cqstate dim) (E : ensemble dim),
      dshape P -> lrow_disj (prog_blocks P) ->
      Term Σ P st E -> Permutation E (denote (prog_lseq P) (st :: nil)).
  Proof.
    intros Hloc P st E Hsh Hdisj (G & Hstar & Hterm & Hcoll).
    assert (Hok0 : dcfg_ok ({|| P, st :: nil ||}))
      by (constructor; [split; assumption | constructor]).
    destruct (star_denote Hloc _ _ Hstar Hok0) as [_ Hp].
    rewrite (terminal_ddenote _ Hterm), Hcoll in Hp.
    unfold ddenote in Hp; simpl in Hp. rewrite app_nil_r in Hp. exact Hp.
  Qed.


End SoundnessFacts.
