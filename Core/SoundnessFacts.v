(** * SoundnessFacts — the machinery behind Theorem 4.1.

    Nothing here is a statement of the paper; these are the invariants and
    bridges the per-rule soundness proofs run on:

      state legitimacy is preserved by execution   (term_preservation)
      an all-ε communication row is stuck          (comm_done chain)
      a local block's ensemble denotation          (denote, one_leaf_adequacy)
      degree bookkeeping over ensembles            (total_degree_* )
      non-interfering blocks commute               (denote_comm, paper Lemma 1)
      every interleaving of a row normalises       (prog_adequacy)
      the pair combinatorics of a phase            (comm_pair_unique,
                                                    kpair_confluent)
      every run of a phase reorders                (comm_reorder)
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

  (** ** 3c. Degree bookkeeping over ensembles, up to [denote_sound] — the
         Hoare half of Par-Disjoint-MP, which §4 and §5 then feed every
         interleaving into. *)

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

  (** ** 6. Comm-Select-MP — the combinatorics of one matched pair ******

      A communication phase steps only by rendezvous, and a rendezvous is the
      assignment x := e.  What the rule needs is that the SELECTED pair can be
      commuted to the front of any terminating run; [wf_phase] is exactly what
      pays for that.  This section is the syntactic half — picks/kpick against
      the phase's action list — and §7 is the semantic half. *)

  (** A pick removes exactly its action. *)
  Lemma picks_perm : forall K a K', K ∋ a □ K' -> Permutation K (a :: K').
  Proof.
    intros K a K' H; induction H as [a K | a b K K' H IH]; simpl.
    - apply Permutation_refl.
    - eapply Permutation_trans; [apply perm_skip, IH | apply perm_swap].
  Qed.

  (** The action list splits along the row, and reduces at a leaf.  Kept as
      lemmas rather than [unfold]ed: an unfolded [row_flat] no longer matches
      the folded [krow_actions] of the other hypotheses, and [lia] then fails
      on what look like two different terms. *)
  Lemma krow_actions_leaf : forall K, krow_actions (leaf K) = K.
  Proof. reflexivity. Qed.

  Lemma krow_actions_par : forall k1 k2,
      krow_actions (par k1 k2) = krow_actions k1 ++ krow_actions k2.
  Proof. reflexivity. Qed.

  Lemma kpick_perm : forall k a k',
      k ∋ₖ a □ k' -> Permutation (krow_actions k) (a :: krow_actions k').
  Proof.
    intros k a k' H;
      induction H as [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH];
      unfold krow_actions in *; cbn [row_flat].
    - apply picks_perm, Hp.
    - eapply Permutation_trans; [apply Permutation_app_tail, IH | ].
      apply Permutation_refl.
    - eapply Permutation_trans; [apply Permutation_app_head, IH | ].
      apply Permutation_sym, Permutation_middle.
  Qed.

  Lemma krow_endpoints_perm : forall k a k' c,
      k ∋ₖ a □ k' -> caction_chan a = c ->
      Permutation (krow_endpoints k c) (a :: krow_endpoints k' c).
  Proof.
    intros k a k' c Hp Hc. unfold krow_endpoints.
    eapply Permutation_trans.
    - apply (permutation_filter _ (fun b => Nat.eqb (caction_chan b) c)).
      apply kpick_perm, Hp.
    - cbn. rewrite Hc, Nat.eqb_refl. apply Permutation_refl.
  Qed.

  Lemma krow_endpoints_par : forall k1 k2 c,
      krow_endpoints (par k1 k2) c
      = krow_endpoints k1 c ++ krow_endpoints k2 c.
  Proof.
    intros; unfold krow_endpoints, krow_actions; cbn [row_flat].
    apply filter_app.
  Qed.

  Lemma krow_chan_actions : forall k,
      krow_chan k = map caction_chan (krow_actions k).
  Proof.
    unfold krow_chan, krow_actions.
    induction k as [K | k1 IH1 k2 IH2]; cbn [row_flat].
    - reflexivity.
    - rewrite map_app, IH1, IH2; reflexivity.
  Qed.

  Lemma krow_endpoints_in_chan : forall k c a,
      In a (krow_endpoints k c) -> In c (krow_chan k).
  Proof.
    intros k c a Hin. unfold krow_endpoints in Hin.
    apply filter_In in Hin as [Hin Hc]. apply Nat.eqb_eq in Hc.
    rewrite krow_chan_actions, <- Hc. apply in_map, Hin.
  Qed.

  Lemma krow_endpoints_nil_parties : forall k c,
      krow_endpoints k c = [] -> row_parties cblock_chan k c = 0%nat.
  Proof.
    intros k c; induction k as [K | k1 IH1 k2 IH2]; cbn [row_parties].
    - unfold krow_endpoints, krow_actions; cbn [row_flat]; intro Hnil.
      destruct (existsb (Nat.eqb c) (cblock_chan K)) eqn:Ex; [| reflexivity].
      exfalso. apply existsb_exists in Ex as (c0 & Hin & Heq).
      apply Nat.eqb_eq in Heq; subst c0.
      unfold cblock_chan in Hin. apply in_map_iff in Hin as (a & Ha & HaK).
      assert (Hmem : In a (filter (fun b => Nat.eqb (caction_chan b) c) K)).
      { apply filter_In; split; [exact HaK | apply Nat.eqb_eq, Ha]. }
      rewrite Hnil in Hmem; exact Hmem.
    - rewrite krow_endpoints_par. intro Hnil.
      apply app_eq_nil in Hnil as [H1 H2].
      rewrite (IH1 H1), (IH2 H2); reflexivity.
  Qed.

  Lemma krow_endpoints_nil_notin : forall k c,
      krow_endpoints k c = [] -> ~ In c (krow_chan k).
  Proof.
    intros k c Hnil Hin.
    rewrite krow_chan_actions in Hin.
    apply in_map_iff in Hin as (a & Ha & HaIn).
    assert (Hmem : In a (krow_endpoints k c)).
    { unfold krow_endpoints. apply filter_In; split;
        [exact HaIn | apply Nat.eqb_eq, Ha]. }
    rewrite Hnil in Hmem; exact Hmem.
  Qed.

  (** What [wf_phase] says about the selected channel: two endpoints, in two
      distinct leaves.  The second half is what forbids a rendezvous with
      oneself, which [kpick] twice does not by itself rule out. *)
  Definition chan_pair (k : krow) (c : chan) : Prop :=
    length (krow_endpoints k c) = 2%nat /\ row_parties cblock_chan k c = 2%nat.

  Lemma wf_kchannels_chan_pair : forall k c,
      wf_kchannels k -> In c (krow_chan k) -> chan_pair k c.
  Proof.
    intros k c Hwf Hin.
    destruct (Hwf c Hin) as (Hs & Hr & Hp).
    split; [| exact Hp].
    rewrite (filter_length_split is_send (krow_endpoints k c)), Hs, Hr.
    reflexivity.
  Qed.

  Lemma wf_phase_chan_pair : forall k kmid c e,
      wf_phase k -> k ∋ₖ c_send c e □ kmid -> chan_pair k c.
  Proof.
    intros k kmid c e (Hwf & _ & _) Hpick.
    apply (wf_kchannels_chan_pair _ _ Hwf).
    apply (krow_endpoints_in_chan k c (c_send c e)).
    pose proof (krow_endpoints_perm _ _ _ c Hpick eq_refl) as Hperm.
    apply Permutation_sym in Hperm.
    eapply Permutation_in; [exact Hperm | left; reflexivity].
  Qed.

  (** Picking an action removes exactly it from every footprint. *)
  Lemma kpick_recv_perm : forall k a k',
      k ∋ₖ a □ k' ->
      Permutation (phase_recv k) (caction_change a ++ phase_recv k').
  Proof.
    intros k a k' H. unfold phase_recv.
    exact (permutation_flat_map _ _ caction_change _ _ (kpick_perm _ _ _ H)).
  Qed.

  Lemma kpick_oread_perm : forall k a k',
      k ∋ₖ a □ k' ->
      Permutation (phase_oread k) (caction_read a ++ phase_oread k').
  Proof.
    intros k a k' H. unfold phase_oread.
    exact (permutation_flat_map _ _ caction_read _ _ (kpick_perm _ _ _ H)).
  Qed.

  (** Off the picked channel, endpoints and party counts are untouched. *)
  Lemma kpick_endpoints_other : forall k a k' c,
      k ∋ₖ a □ k' -> caction_chan a <> c ->
      Permutation (krow_endpoints k c) (krow_endpoints k' c).
  Proof.
    intros k a k' c H Hne. unfold krow_endpoints.
    eapply Permutation_trans.
    - apply (permutation_filter _ (fun b => Nat.eqb (caction_chan b) c)).
      apply kpick_perm, H.
    - cbn. destruct (Nat.eqb (caction_chan a) c) eqn:Ec.
      + apply Nat.eqb_eq in Ec; contradiction.
      + apply Permutation_refl.
  Qed.

  Lemma kpick_parties_other : forall k a k' c,
      k ∋ₖ a □ k' -> caction_chan a <> c ->
      row_parties cblock_chan k' c = row_parties cblock_chan k c.
  Proof.
    intros k a k' c H Hne;
      induction H as [K a K' Hp | kA kA' kB a H IH | kA kB kB' a H IH];
      cbn [row_parties].
    - assert (Hperm : Permutation (cblock_chan K)
                        (caction_chan a :: cblock_chan K')).
      { unfold cblock_chan. rewrite <- map_cons.
        apply Permutation_map, picks_perm, Hp. }
      destruct (existsb (Nat.eqb c) (cblock_chan K)) eqn:E1;
        destruct (existsb (Nat.eqb c) (cblock_chan K')) eqn:E2;
        try reflexivity; exfalso.
      + apply existsb_exists in E1 as (c0 & Hin & Heq).
        apply Nat.eqb_eq in Heq; subst c0.
        eapply Permutation_in in Hin; [| exact Hperm].
        destruct Hin as [Heq | Hin]; [contradiction |].
        assert (Htrue : existsb (Nat.eqb c) (cblock_chan K') = true)
          by (apply existsb_exists; exists c;
              split; [exact Hin | apply Nat.eqb_refl]).
        rewrite E2 in Htrue; discriminate.
      + apply existsb_exists in E2 as (c0 & Hin & Heq).
        apply Nat.eqb_eq in Heq; subst c0.
        assert (HinK : In c (cblock_chan K)).
        { eapply Permutation_in; [apply Permutation_sym, Hperm | right; exact Hin]. }
        assert (Htrue : existsb (Nat.eqb c) (cblock_chan K) = true)
          by (apply existsb_exists; exists c;
              split; [exact HinK | apply Nat.eqb_refl]).
        rewrite E1 in Htrue; discriminate.
    - rewrite IH; [reflexivity | exact Hne].
    - rewrite IH; [reflexivity | exact Hne].
  Qed.

  (** [wf_phase] survives consuming one matched PAIR — not one endpoint:
      after a single [kpick] the channel carries one endpoint, and
      [wf_kchannels] would already be false. *)
  Lemma wf_phase_pair : forall k c e x kmid k',
      wf_phase k ->
      k    ∋ₖ c_send c e □ kmid ->
      kmid ∋ₖ c_recv c x □ k' ->
      wf_phase k'.
  Proof.
    intros k c e x kmid k' (Hch & Hnd & Hdj) H1 H2.
    pose proof (kpick_recv_perm _ _ _ H1) as R1.
    pose proof (kpick_recv_perm _ _ _ H2) as R2.
    pose proof (kpick_oread_perm _ _ _ H1) as O1.
    pose proof (kpick_oread_perm _ _ _ H2) as O2.
    cbn [caction_change caction_read app] in R1, R2, O1, O2.
    assert (Hnd' : NoDup (phase_recv k')).
    { rewrite R1 in Hnd. rewrite R2 in Hnd. cbn in Hnd.
      inversion Hnd; assumption. }
    assert (Hdj' : disjoint (phase_recv k') (phase_oread k')).
    { intros y Hy Hy'.
      assert (Hy1 : In y (phase_recv k)).
      { eapply Permutation_in; [apply Permutation_sym, R1 |].
        eapply Permutation_in; [apply Permutation_sym, R2 | cbn; right; exact Hy]. }
      assert (Hy2 : In y (phase_oread k)).
      { eapply Permutation_in; [apply Permutation_sym, O1 |].
        cbn. apply in_or_app. right.
        eapply Permutation_in; [apply Permutation_sym, O2 | cbn; exact Hy']. }
      exact (Hdj y Hy1 Hy2). }
    split; [| split; assumption].
    intros c0 Hin0.
    assert (Hc0 : c0 <> c).
    { intro; subst c0.
      apply (krow_endpoints_nil_notin k' c); [| exact Hin0].
      pose proof (krow_endpoints_perm _ _ _ c H1 eq_refl) as P1.
      pose proof (krow_endpoints_perm _ _ _ c H2 eq_refl) as P2.
      assert (Hinc : In c (krow_chan k)).
      { apply (krow_endpoints_in_chan k c (c_send c e)).
        eapply Permutation_in; [apply Permutation_sym, P1 | left; reflexivity]. }
      destruct (Hch c Hinc) as (Hs & Hr & _).
      pose proof (filter_length_split is_send (krow_endpoints k c)) as Hsplit.
      rewrite Hs, Hr in Hsplit.
      apply Permutation_length in P1, P2. cbn in P1, P2.
      destruct (krow_endpoints k' c); [reflexivity | cbn in *; lia]. }
    assert (Hne1 : caction_chan (c_send c e) <> c0) by (cbn; congruence).
    assert (Hne2 : caction_chan (c_recv c x) <> c0) by (cbn; congruence).
    pose proof (kpick_endpoints_other _ _ _ _ H1 Hne1) as E1.
    pose proof (kpick_endpoints_other _ _ _ _ H2 Hne2) as E2.
    assert (Hin : In c0 (krow_chan k)).
    { rewrite krow_chan_actions in Hin0 |- *.
      apply in_map_iff in Hin0 as (a0 & Ha0 & Hmem).
      apply in_map_iff. exists a0. split; [exact Ha0 |].
      eapply Permutation_in; [apply Permutation_sym, (kpick_perm _ _ _ H1) |].
      right.
      eapply Permutation_in; [apply Permutation_sym, (kpick_perm _ _ _ H2) |].
      right. exact Hmem. }
    destruct (Hch c0 Hin) as (Hs & Hr & Hp).
    split; [| split].
    - pose proof (Permutation_length (permutation_filter _ is_send _ _ E1)) as L1.
      pose proof (Permutation_length (permutation_filter _ is_send _ _ E2)) as L2.
      congruence.
    - pose proof (Permutation_length
                    (permutation_filter _ (fun a => negb (is_send a)) _ _ E1)) as L1.
      pose proof (Permutation_length
                    (permutation_filter _ (fun a => negb (is_send a)) _ _ E2)) as L2.
      congruence.
    - rewrite (kpick_parties_other _ _ _ _ H2 Hne2).
      rewrite (kpick_parties_other _ _ _ _ H1 Hne1). exact Hp.
  Qed.

  (** ** 6b. Occurrence uniqueness.

      [wf_kchannels] gives ONE send and ONE receive on the selected channel,
      so any two ways of picking them coincide — which is what identifies the
      pair the scheduler consumes with the pair the rule selected. *)

  Definition ends_on (p : caction -> bool) (l : list caction) (c : chan)
    : list caction :=
    filter p (filter (fun a => Nat.eqb (caction_chan a) c) l).

  Lemma ends_on_cons : forall p a l c,
      ends_on p (a :: l) c
      = if andb (Nat.eqb (caction_chan a) c) (p a)
        then a :: ends_on p l c else ends_on p l c.
  Proof.
    intros p a l c; unfold ends_on; cbn.
    destruct (Nat.eqb (caction_chan a) c); cbn;
      [destruct (p a); cbn; reflexivity | reflexivity].
  Qed.

  Lemma ends_on_app : forall p l1 l2 c,
      ends_on p (l1 ++ l2) c = ends_on p l1 c ++ ends_on p l2 c.
  Proof.
    intros; unfold ends_on; rewrite !filter_app; reflexivity.
  Qed.

  Lemma ends_on_endpoints : forall p k c,
      ends_on p (krow_actions k) c = filter p (krow_endpoints k c).
  Proof. reflexivity. Qed.

  Lemma ends_on_ge1 : forall p l c a,
      In a l -> caction_chan a = c -> p a = true ->
      (1 <= length (ends_on p l c))%nat.
  Proof.
    intros p l c a Hin Hc Hp.
    assert (Hmem : In a (ends_on p l c)).
    { unfold ends_on; apply filter_In; split; [| exact Hp].
      apply filter_In; split; [exact Hin | apply Nat.eqb_eq, Hc]. }
    destruct (ends_on p l c); [contradiction | cbn; lia].
  Qed.

  (* The channel is written [caction_chan a1] rather than bound to a variable
     c: with a hypothesis [caction_chan a1 = c] in scope, [subst] treats c as
     the defined side and eliminates it, taking the hypothesis with it. *)
  Lemma picks_unique : forall p K a1 K1,
      K ∋ a1 □ K1 ->
      forall a2 K2,
        length (ends_on p K (caction_chan a1)) = 1%nat ->
        p a1 = true -> p a2 = true ->
        caction_chan a1 = caction_chan a2 ->
        K ∋ a2 □ K2 -> a1 = a2 /\ K1 = K2.
  Proof.
    intros p K a1 K1 H1.
    induction H1 as [a K0 | a b K0 K0' H1 IH];
      intros a2 K2 Hlen Hp1 Hp2 Hc H2.
    - inversion H2 as [| ax bx Kx Kx' H2' Eq1 Eq2]; subst.
      + split; reflexivity.
      + exfalso.
        rewrite ends_on_cons, Nat.eqb_refl, Hp1 in Hlen; cbn in Hlen.
        assert (1 <= length (ends_on p K0 (caction_chan a)))%nat
          by (eapply ends_on_ge1;
              [apply (picks_in _ _ _ H2') | symmetry; exact Hc | exact Hp2]).
        lia.
    - assert (Hb : andb (Nat.eqb (caction_chan b) (caction_chan a))
                        (p b) = false).
      { destruct (andb (Nat.eqb (caction_chan b) (caction_chan a)) (p b)) eqn:Eb;
          [| reflexivity]. exfalso.
        rewrite ends_on_cons, Eb in Hlen; cbn in Hlen.
        assert (1 <= length (ends_on p K0 (caction_chan a)))%nat
          by (eapply ends_on_ge1;
              [apply (picks_in _ _ _ H1) | reflexivity | exact Hp1]).
        lia. }
      rewrite ends_on_cons, Hb in Hlen.
      inversion H2 as [| ax bx Kx Kx' H2' Eq1 Eq2]; subst.
      + exfalso. rewrite <- Hc, Nat.eqb_refl, Hp2 in Hb; cbn in Hb; discriminate.
      + destruct (IH _ _ Hlen Hp1 Hp2 Hc H2') as [Ha HK].
        split; [exact Ha | rewrite HK; reflexivity].
  Qed.

  Lemma kpick_ends_ge1 : forall p k a k' c,
      k ∋ₖ a □ k' -> caction_chan a = c -> p a = true ->
      (1 <= length (ends_on p (krow_actions k) c))%nat.
  Proof.
    intros p k a k' c H Hc Hp.
    eapply ends_on_ge1; [| exact Hc | exact Hp].
    eapply Permutation_in; [apply Permutation_sym, (kpick_perm _ _ _ H) |].
    left; reflexivity.
  Qed.

  Lemma kpick_unique : forall p k a1 k1,
      k ∋ₖ a1 □ k1 ->
      forall a2 k2,
        length (ends_on p (krow_actions k) (caction_chan a1)) = 1%nat ->
        p a1 = true -> p a2 = true ->
        caction_chan a1 = caction_chan a2 ->
        k ∋ₖ a2 □ k2 -> a1 = a2 /\ k1 = k2.
  Proof.
    intros p k a1 k1 H1.
    induction H1 as [K a K' Hpk | kA kA' kB a H1 IH | kA kB kB' a H1 IH];
      intros a2 k2 Hlen Hp1 Hp2 Hc H2.
    - inversion H2 as [Kx ax Kx' Hpk2 Eq1 Eq2 | |]; subst.
      rewrite krow_actions_leaf in Hlen.
      destruct (picks_unique _ _ _ _ Hpk _ _ Hlen Hp1 Hp2 Hc Hpk2)
        as [Ha HK]; subst.
      split; reflexivity.
    - rewrite krow_actions_par, ends_on_app, length_app in Hlen.
      inversion H2 as [| kX kX' kY ax H2' Eq1 Eq2 | kX kY kY' ax H2' Eq1 Eq2]; subst.
      + pose proof (kpick_ends_ge1 p _ _ _ _ H1 eq_refl Hp1) as G1.
        assert (Hl : length (ends_on p (krow_actions kA) (caction_chan a)) = 1%nat)
          by lia.
        destruct (IH _ _ Hl Hp1 Hp2 Hc H2') as [Ha Hk]; subst.
        split; reflexivity.
      + exfalso.
        pose proof (kpick_ends_ge1 p _ _ _ _ H1 eq_refl Hp1) as G1.
        pose proof (kpick_ends_ge1 p _ _ _ _ H2' (eq_sym Hc) Hp2) as G2.
        lia.
    - rewrite krow_actions_par, ends_on_app, length_app in Hlen.
      inversion H2 as [| kX kX' kY ax H2' Eq1 Eq2 | kX kY kY' ax H2' Eq1 Eq2]; subst.
      + exfalso.
        pose proof (kpick_ends_ge1 p _ _ _ _ H1 eq_refl Hp1) as G1.
        pose proof (kpick_ends_ge1 p _ _ _ _ H2' (eq_sym Hc) Hp2) as G2.
        lia.
      + pose proof (kpick_ends_ge1 p _ _ _ _ H1 eq_refl Hp1) as G1.
        assert (Hl : length (ends_on p (krow_actions kB) (caction_chan a)) = 1%nat)
          by lia.
        destruct (IH _ _ Hl Hp1 Hp2 Hc H2') as [Ha Hk]; subst.
        split; reflexivity.
  Qed.

  Lemma comm_pair_unique : forall k c e x kmid k' e0 x0 kmid0 k0,
      wf_phase k ->
      k     ∋ₖ c_send c e  □ kmid  -> kmid  ∋ₖ c_recv c x  □ k' ->
      k     ∋ₖ c_send c e0 □ kmid0 -> kmid0 ∋ₖ c_recv c x0 □ k0 ->
      e = e0 /\ x = x0 /\ k' = k0.
  Proof.
    intros k c e x kmid k' e0 x0 kmid0 k0 Hwf Hs1 Hr1 Hs2 Hr2.
    destruct Hwf as (Hch & _ & _).
    assert (Hin : In c (krow_chan k)).
    { apply (krow_endpoints_in_chan k c (c_send c e)).
      eapply Permutation_in;
        [apply Permutation_sym, (krow_endpoints_perm _ _ _ c Hs1 eq_refl) |].
      left; reflexivity. }
    destruct (Hch c Hin) as (Hsend & Hrecv & _).
    destruct (kpick_unique is_send k _ _ Hs1 (c_send c e0) kmid0
                Hsend eq_refl eq_refl eq_refl Hs2) as [Hae Hmid].
    injection Hae as He. subst e0. subst kmid0.
    assert (Hrecv' : length (ends_on (fun a => negb (is_send a))
                               (krow_actions kmid) c) = 1%nat).
    { rewrite ends_on_endpoints.
      pose proof (krow_endpoints_perm _ _ _ c Hs1 eq_refl) as P1.
      pose proof (Permutation_length
                    (permutation_filter _ (fun a => negb (is_send a)) _ _ P1)) as L.
      cbn in L. lia. }
    destruct (kpick_unique (fun a => negb (is_send a)) kmid _ _ Hr1
                (c_recv c x0) k0
                Hrecv' eq_refl eq_refl eq_refl Hr2) as [Hax Hk].
    injection Hax as Hx. subst x0.
    split; [reflexivity | split; [reflexivity | exact Hk]].
  Qed.

  (** ** 6c. Confluence.  The two pairs FORK from the same row (the scheduler
      took one, the rule selected the other), so what is needed is that they
      can be joined — not that two consecutive picks can be swapped. *)

  Lemma picks_confluent : forall K a K1,
      K ∋ a □ K1 ->
      forall b K2, K ∋ b □ K2 ->
        caction_chan a <> caction_chan b ->
        exists K12, K1 ∋ b □ K12 /\ K2 ∋ a □ K12.
  Proof.
    intros K a K1 H1.
    induction H1 as [a K0 | a b0 K0 K0' H1 IH]; intros b K2 H2 Hne.
    - inversion H2 as [| ax bx Kx Kx' H2' Eq1 Eq2]; subst.
      + exfalso; apply Hne; reflexivity.
      + exists Kx'. split; [exact H2' | apply pick_here].
    - inversion H2 as [| ax bx Kx Kx' H2' Eq1 Eq2]; subst.
      + exists K0'. split; [apply pick_here | exact H1].
      + destruct (IH _ _ H2' Hne) as (K12 & Hb & Ha).
        exists (b0 :: K12). split; apply pick_there; assumption.
  Qed.

  Lemma kpick_confluent : forall k a k1,
      k ∋ₖ a □ k1 ->
      forall b k2, k ∋ₖ b □ k2 ->
        caction_chan a <> caction_chan b ->
        exists k12, k1 ∋ₖ b □ k12 /\ k2 ∋ₖ a □ k12.
  Proof.
    intros k a k1 H1.
    induction H1 as [K a K' Hpk | kA kA' kB a H1 IH | kA kB kB' a H1 IH];
      intros b k2 H2 Hne.
    - inversion H2 as [Kx bx Kx' Hpk2 Eq1 Eq2 | |]; subst.
      destruct (picks_confluent _ _ _ Hpk _ _ Hpk2 Hne) as (K12 & Hb & Ha).
      exists (leaf K12). split; apply kp_here; assumption.
    - inversion H2 as [| kX kX' kY bx H2' Eq1 Eq2 | kX kY kY' bx H2' Eq1 Eq2]; subst.
      + destruct (IH _ _ H2' Hne) as (k12 & Hb & Ha).
        exists (par k12 kB). split; apply kp_left; assumption.
      + exists (par kA' kY').
        split; [apply kp_right, H2' | apply kp_left, H1].
    - inversion H2 as [| kX kX' kY bx H2' Eq1 Eq2 | kX kY kY' bx H2' Eq1 Eq2]; subst.
      + exists (par kX' kB').
        split; [apply kp_left, H2' | apply kp_right, H1].
      + destruct (IH _ _ H2' Hne) as (k12 & Hb & Ha).
        exists (par kA k12). split; apply kp_right; assumption.
  Qed.

  (** One matched pair, as a relation on rows. *)
  Definition kpair (k : krow) (c : chan) (e : expr) (x : var) (k' : krow)
    : Prop :=
    exists kmid, k ∋ₖ c_send c e □ kmid /\ kmid ∋ₖ c_recv c x □ k'.

  Lemma kpair_confluent : forall k c1 e1 x1 k1 c2 e2 x2 k2,
      c1 <> c2 ->
      kpair k c1 e1 x1 k1 -> kpair k c2 e2 x2 k2 ->
      exists k12, kpair k1 c2 e2 x2 k12 /\ kpair k2 c1 e1 x1 k12.
  Proof.
    intros k c1 e1 x1 k1 c2 e2 x2 k2 Hc (m1 & Hs1 & Hr1) (m2 & Hs2 & Hr2).
    assert (N12 : c1 <> c2) by exact Hc.
    assert (N21 : c2 <> c1) by (intro; apply Hc; symmetry; assumption).
    destruct (kpick_confluent _ _ _ Hs1 _ _ Hs2 N12) as (n & Hn1 & Hn2).
    destruct (kpick_confluent _ _ _ Hr1 _ _ Hn1 N12) as (p & Hp1 & Hp2).
    destruct (kpick_confluent _ _ _ Hr2 _ _ Hn2 N21) as (q & Hq1 & Hq2).
    destruct (kpick_confluent _ _ _ Hp2 _ _ Hq2 N12) as (k12 & Hk1 & Hk2).
    exists k12. split.
    - exists p. split; [exact Hp1 | exact Hk1].
    - exists q. split; [exact Hq1 | exact Hk2].
  Qed.

  Lemma kpair_actions_perm : forall k c e x k',
      kpair k c e x k' ->
      Permutation (krow_actions k)
                  (c_send c e :: c_recv c x :: krow_actions k').
  Proof.
    intros k c e x k' (kmid & Hs & Hr).
    eapply Permutation_trans; [apply (kpick_perm _ _ _ Hs) |].
    apply perm_skip, (kpick_perm _ _ _ Hr).
  Qed.

  (** ** 6d. The store half: two rendezvous on different channels commute. *)

  Lemma rendezvous_store_comm : forall fn (s : store) x1 e1 x2 e2,
      x1 <> x2 ->
      ~ In x1 (expr_vars e2) -> ~ In x2 (expr_vars e1) ->
      (s [ x1 |-> eval_expr fn s e1 ])
        [ x2 |-> eval_expr fn (s [ x1 |-> eval_expr fn s e1 ]) e2 ]
      = (s [ x2 |-> eval_expr fn s e2 ])
          [ x1 |-> eval_expr fn (s [ x2 |-> eval_expr fn s e2 ]) e1 ].
  Proof.
    intros fn s x1 e1 x2 e2 Hx H12 H21.
    rewrite (eval_expr_update_notin fn s x1 _ e2 H12).
    rewrite (eval_expr_update_notin fn s x2 _ e1 H21).
    apply store_update_comm, Hx.
  Qed.

  (** …and [wf_phase]'s last two clauses are exactly its side conditions. *)
  Lemma two_pairs_indep : forall k c0 e0 x0 k1 c e x k12,
      wf_phase k ->
      kpair k c0 e0 x0 k1 -> kpair k1 c e x k12 ->
      x <> x0 /\ ~ In x (expr_vars e0) /\ ~ In x0 (expr_vars e).
  Proof.
    intros k c0 e0 x0 k1 c e x k12 (_ & Hnd & Hdj) Hp0 Hp1.
    pose proof (kpair_actions_perm _ _ _ _ _ Hp0) as Q0.
    pose proof (kpair_actions_perm _ _ _ _ _ Hp1) as Q1.
    assert (Q : Permutation (krow_actions k)
                  (c_send c0 e0 :: c_recv c0 x0 ::
                   c_send c e :: c_recv c x :: krow_actions k12)).
    { eapply Permutation_trans; [exact Q0 |].
      apply perm_skip, perm_skip, Q1. }
    assert (HR : Permutation (phase_recv k) (x0 :: x :: phase_recv k12)).
    { unfold phase_recv.
      exact (permutation_flat_map _ _ caction_change _ _ Q). }
    assert (HO : Permutation (phase_oread k)
                   (expr_vars e0 ++ expr_vars e ++ phase_oread k12)).
    { unfold phase_oread.
      eapply Permutation_trans;
        [exact (permutation_flat_map _ _ caction_read _ _ Q) |].
      cbn [flat_map caction_read]. apply Permutation_refl. }
    assert (Hnd' : NoDup (x0 :: x :: phase_recv k12))
      by (eapply Permutation_NoDup; [exact HR | exact Hnd]).
    inversion Hnd' as [| y ys Hy Hnd'' ]; subst.
    split; [| split].
    - intro Hxx; subst x0. apply Hy; left; reflexivity.
    - intro Hin. apply (Hdj x).
      + eapply Permutation_in; [apply Permutation_sym, HR |].
        right; left; reflexivity.
      + eapply Permutation_in; [apply Permutation_sym, HO |].
        apply in_or_app; left; exact Hin.
    - intro Hin. apply (Hdj x0).
      + eapply Permutation_in; [apply Permutation_sym, HR |].
        left; reflexivity.
      + eapply Permutation_in; [apply Permutation_sym, HO |].
        apply in_or_app; right; apply in_or_app; left; exact Hin.
  Qed.

  (** ** 7. Comm-Select-MP — the semantic half **************************

      A communication phase runs as a program whose leaves are
      [advance ↓ K ↓].  Such a program can ONLY step by rendezvous, its
      configuration stays a single component over a single state, and — by
      §6 — the selected pair commutes to the front of any terminating run. *)

  (** The K-row read as a program.  Same body as [Soundness.krow_prog], which
      cannot be used here: it is defined downstream.  The two are convertible,
      and Soundness.v bridges them by [reflexivity]. *)
  Definition kprog (k : krow) : program :=
    row_map (fun K => advance r_done K terminated) k.

  Lemma kprog_leaf_inv : forall k T,
      kprog k = leaf T -> exists K, k = leaf K /\ T = advance r_done K terminated.
  Proof.
    intros [K | k1 k2] T H; unfold kprog in H; cbn [row_map] in H.
    - injection H as HT. exists K. split; [reflexivity | symmetry; exact HT].
    - discriminate.
  Qed.

  Lemma kprog_par_inv : forall k P1 P2,
      kprog k = par P1 P2 ->
      exists k1 k2, k = par k1 k2 /\ P1 = kprog k1 /\ P2 = kprog k2.
  Proof.
    intros [K | k1 k2] P1 P2 H; unfold kprog in H; cbn [row_map] in H.
    - discriminate.
    - injection H as H1 H2. exists k1, k2.
      split; [reflexivity | split; symmetry; assumption].
  Qed.

  Lemma kpick_not_terminated : forall k a k',
      k ∋ₖ a □ k' -> ~ prog_terminated (kprog k).
  Proof.
    intros k a k' H;
      induction H as [K a K' Hp | kA kA' kB a H IH | kA kB kB' a H IH];
      unfold prog_terminated, kprog in *; cbn [row_map row_all].
    - destruct K as [| a0 K0]; [inversion Hp |]. cbn [advance]. discriminate.
    - intros [H1 _]; exact (IH H1).
    - intros [_ H2]; exact (IH H2).
  Qed.

  (** [kpick] and [replace_leaf] are the same selection, one on the row and
      one on the program. *)
  Lemma kpick_replace : forall k a k',
      k ∋ₖ a □ k' ->
      exists K K', K ∋ a □ K' /\
        replace_leaf (phase r_done K terminated)
                     (advance r_done K' terminated) (kprog k) (kprog k').
  Proof.
    intros k a k' H;
      induction H as [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH].
    - exists K, K'. split; [exact Hp |].
      unfold kprog; cbn [row_map].
      destruct K as [| a0 K0]; [inversion Hp |].
      cbn [advance]. apply rl_here.
    - destruct IH as (K & K' & Hp & Hr).
      exists K, K'. split; [exact Hp |].
      unfold kprog in *; cbn [row_map]. apply rl_left, Hr.
    - destruct IH as (K & K' & Hp & Hr).
      exists K, K'. split; [exact Hp |].
      unfold kprog in *; cbn [row_map]. apply rl_right, Hr.
  Qed.

  Lemma replace_kpick : forall k K K' T a P',
      K ∋ a □ K' ->
      replace_leaf (phase r_done K T)
                   (advance r_done K' T) (kprog k) P' ->
      exists k'', k ∋ₖ a □ k'' /\ P' = kprog k''.
  Proof.
    intros k K K' T a P' Hp Hr.
    remember (kprog k) as P eqn:HP. revert k HP.
    induction Hr as [| P Q R Hr IH | P Q R Hr IH]; intros k HP.
    - (* a kprog leaf forces the continuation to be ↓ *)
      symmetry in HP. apply kprog_leaf_inv in HP as (K0 & Hk & HT).
      destruct K0 as [| a0 K0]; cbn [advance] in HT; [discriminate |].
      inversion HT; subst.
      exists (leaf K'). split; [| reflexivity].
      apply kp_here. exact Hp.
    - symmetry in HP. apply kprog_par_inv in HP as (k1 & k2 & Hk & H1 & H2).
      subst k. destruct (IH k1 H1) as (k1'' & Hpk & HP').
      exists (par k1'' k2). split; [apply kp_left, Hpk |].
      rewrite HP', H2. unfold kprog; cbn [row_map]. reflexivity.
    - symmetry in HP. apply kprog_par_inv in HP as (k1 & k2 & Hk & H1 & H2).
      subst k. destruct (IH k2 H2) as (k2'' & Hpk & HP').
      exists (par k1 k2''). split; [apply kp_right, Hpk |].
      rewrite HP', H1. unfold kprog; cbn [row_map]. reflexivity.
  Qed.

  (** Every step of a communication-only row is a rendezvous, and lands on
      another communication-only row.  [ds_local] is impossible: a kprog leaf
      has residual ↓. *)
  Lemma kprog_step_inv : forall k E G,
      Σ ⊳ ‹ kprog k, E › ⇝ G ->
      exists c e x kmid k',
        k ∋ₖ c_send c e □ kmid /\ kmid ∋ₖ c_recv c x □ k' /\
        G = {|| kprog k',
               map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}.
  Proof.
    intros k E G Hstep.
    remember (kprog k) as P eqn:HP. revert k HP.
    induction Hstep as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 G1 Hs IH
      | P1 P2 E0 G2 Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ];
      intros k HP.
    - exfalso. symmetry in HP. apply kprog_leaf_inv in HP as (K0 & _ & HT).
      destruct K0; cbn [advance] in HT; discriminate.
    - symmetry in HP. apply kprog_par_inv in HP as (k1 & k2 & Hk & H1 & H2).
      subst k. destruct (IH k1 H1) as (c & e & x & kmid & k' & Hs1 & Hs2 & HG).
      exists c, e, x, (par kmid k2), (par k' k2).
      split; [apply kp_left, Hs1 | split; [apply kp_left, Hs2 |]].
      subst G1. cbn [map fst snd]. rewrite H2.
      unfold kprog; cbn [row_map]. reflexivity.
    - symmetry in HP. apply kprog_par_inv in HP as (k1 & k2 & Hk & H1 & H2).
      subst k. destruct (IH k2 H2) as (c & e & x & kmid & k' & Hs1 & Hs2 & HG).
      exists c, e, x, (par k1 kmid), (par k1 k').
      split; [apply kp_right, Hs1 | split; [apply kp_right, Hs2 |]].
      subst G2. cbn [map fst snd]. rewrite H1.
      unfold kprog; cbn [row_map]. reflexivity.
    - symmetry in HP. apply kprog_par_inv in HP as (k1 & k2 & Hk & H1 & H2).
      subst k. rewrite H1 in HrS. rewrite H2 in HrR.
      destruct (replace_kpick k1 Ks Ks' Ts _ _ HpS HrS) as (kS & HkS & HPS).
      destruct (replace_kpick k2 Kr Kr' Tr _ _ HpR HrR) as (kR & HkR & HPR).
      exists c, e, x, (par kS k2), (par kS kR).
      split; [apply kp_left, HkS | split; [apply kp_right, HkR |]].
      rewrite HPS, HPR. unfold kprog; cbn [row_map]. reflexivity.
    - symmetry in HP. apply kprog_par_inv in HP as (k1 & k2 & Hk & H1 & H2).
      subst k. rewrite H2 in HrS. rewrite H1 in HrR.
      destruct (replace_kpick k2 Ks Ks' Ts _ _ HpS HrS) as (kS & HkS & HPS).
      destruct (replace_kpick k1 Kr Kr' Tr _ _ HpR HrR) as (kR & HkR & HPR).
      exists c, e, x, (par k1 kS), (par kR kS).
      split; [apply kp_right, HkS | split; [apply kp_left, HkR |]].
      rewrite HPS, HPR. unfold kprog; cbn [row_map]. reflexivity.
  Qed.

  (** The converse: the selected pair really steps.  [chan_pair]'s party
      count is what puts the two endpoints in different leaves — [ds_comm]
      needs them on opposite sides of a ∥, and two [kpick]s alone do not
      give that. *)
  Lemma comm_pair_step : forall k a kmid,
      k ∋ₖ a □ kmid ->
      forall c e x k',
        a = c_send c e ->
        chan_pair k c ->
        kmid ∋ₖ c_recv c x □ k' ->
        forall E, Σ ⊳ ‹ kprog k, E › ⇝
          {|| kprog k',
            map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}.
  Proof.
    intros k a kmid H1.
    induction H1 as [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH];
      intros c e x k' Ha Hcp H2 E; subst a.
    - (* both endpoints in ONE leaf: excluded by row_parties = 2 *)
      exfalso. destruct Hcp as [_ Hpar]; cbn [row_parties] in Hpar.
      destruct (existsb (Nat.eqb c) (cblock_chan K)); discriminate.
    - inversion H2 as [| kA kA' kB aa HL EqA EqB | kA kB kB' aa HR EqA EqB]; subst.
      + (* receiver also on the left: sink the step with ds_par_l *)
        assert (Hcp1 : chan_pair k1 c).
        { destruct Hcp as [Hlen Hpar].
          rewrite krow_endpoints_par in Hlen.
          pose proof (krow_endpoints_perm _ _ _ c H eq_refl) as P1.
          pose proof (krow_endpoints_perm _ _ _ c HL eq_refl) as P2.
          rewrite length_app in Hlen.
          apply Permutation_length in P1, P2. cbn in P1, P2.
          assert (Hk2 : krow_endpoints k2 c = []).
          { destruct (krow_endpoints k2 c); [reflexivity | cbn in Hlen; lia]. }
          split; [lia |].
          cbn [row_parties] in Hpar.
          rewrite (krow_endpoints_nil_parties _ _ Hk2) in Hpar. lia. }
        pose proof (IH c e x _ eq_refl Hcp1 HL E) as Hstep.
        pose proof (ds_par_l Σ (kprog k1) (kprog k2) E _ Hstep) as Hd.
        unfold kprog in *; cbn [row_map] in *; cbn [map fst snd] in Hd.
        exact Hd.
      + (* a genuine ds_comm_lr *)
        destruct (kpick_replace _ _ _ H) as (Ks & Ks' & HpS & HrS).
        destruct (kpick_replace _ _ _ HR) as (Kr & Kr' & HpR & HrR).
        unfold kprog in *; cbn [row_map] in *.
        eapply (ds_comm_lr Σ _ _ _ _ Ks Ks' Kr Kr' terminated terminated
                  c e x E HpS HpR HrS HrR).
    - inversion H2 as [| kA kA' kB aa HL EqA EqB | kA kB kB' aa HR EqA EqB]; subst.
      + destruct (kpick_replace _ _ _ H) as (Ks & Ks' & HpS & HrS).
        destruct (kpick_replace _ _ _ HL) as (Kr & Kr' & HpR & HrR).
        unfold kprog in *; cbn [row_map] in *.
        eapply (ds_comm_rl Σ _ _ _ _ Ks Ks' Kr Kr' terminated terminated
                  c e x E HpS HpR HrS HrR).
      + assert (Hcp2 : chan_pair k2 c).
        { destruct Hcp as [Hlen Hpar].
          rewrite krow_endpoints_par in Hlen.
          pose proof (krow_endpoints_perm _ _ _ c H eq_refl) as P1.
          pose proof (krow_endpoints_perm _ _ _ c HR eq_refl) as P2.
          rewrite length_app in Hlen.
          apply Permutation_length in P1, P2. cbn in P1, P2.
          assert (Hk1 : krow_endpoints k1 c = []).
          { destruct (krow_endpoints k1 c); [reflexivity | cbn in Hlen; lia]. }
          split; [lia |].
          cbn [row_parties] in Hpar.
          rewrite (krow_endpoints_nil_parties _ _ Hk1) in Hpar. lia. }
        pose proof (IH c e x _ eq_refl Hcp2 HR E) as Hstep.
        pose proof (ds_par_r Σ (kprog k1) (kprog k2) E _ Hstep) as Hd.
        unfold kprog in *; cbn [row_map] in *; cbn [map fst snd] in Hd.
        exact Hd.
  Qed.

  (** The ensemble action of one rendezvous. *)
  Definition rmap (x : var) (e : expr) (E : ensemble dim) : ensemble dim :=
    map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E.

  Lemma rmap_comm : forall x1 e1 x2 e2 E,
      x1 <> x2 -> ~ In x1 (expr_vars e2) -> ~ In x2 (expr_vars e1) ->
      rmap x2 e2 (rmap x1 e1 E) = rmap x1 e1 (rmap x2 e2 E).
  Proof.
    intros x1 e1 x2 e2 E Hx H12 H21.
    unfold rmap; rewrite !map_map. apply map_ext.
    intros [s r]; cbn. f_equal.
    apply rendezvous_store_comm; assumption.
  Qed.

  Lemma kprog_mixed_inv : forall k st G,
      mixed_step Σ ({|| kprog k, st :: nil ||}) G ->
      exists c e x kmid k',
        k ∋ₖ c_send c e □ kmid /\ kmid ∋ₖ c_recv c x □ k' /\
        G = {|| kprog k', rmap x e (st :: nil) ||}.
  Proof.
    intros k st G Hstep.
    inversion Hstep as [Gx D E Grest G1 Hperm Hd HeqG HeqG2]; subst.
    apply Permutation_length_1_inv in Hperm.
    inversion Hperm; subst.
    destruct (kprog_step_inv _ _ _ Hd) as (c & e & x & kmid & k' & Hs & Hr & HG).
    exists c, e, x, kmid, k'. split; [exact Hs | split; [exact Hr |]].
    rewrite HG. unfold norm, rmap; cbn [app filter snd map]. reflexivity.
  Qed.

  Lemma kpair_mixed_step : forall k c e x k' (E : ensemble dim),
      chan_pair k c -> E <> nil ->
      kpair k c e x k' ->
      mixed_step Σ ({|| kprog k, E ||}) ({|| kprog k', rmap x e E ||}).
  Proof.
    intros k c e x k' E Hcp Hne (kmid & Hs & Hr).
    pose proof (comm_pair_step _ _ _ Hs c e x k' eq_refl Hcp Hr E) as Hd.
    (* norm drops nothing: the ensemble is non-empty, so it computes away *)
    destruct E as [| st E0]; [exfalso; apply Hne; reflexivity |].
    exact (mixed_lift Σ _ (kprog k) (st :: E0) nil _ (Permutation_refl _) Hd).
  Qed.

  (** Paper p.15: the selected rendezvous can be commuted to the FRONT of any
      terminating run of the phase, leaving the terminal collapse alone. *)
  Lemma comm_reorder : forall G Gt,
      step_star Σ G Gt -> terminal Gt ->
      forall k (st : cqstate dim), G = {|| kprog k, st :: nil ||} ->
      forall c e x k', wf_phase k -> kpair k c e x k' ->
      exists Gt',
        step_star Σ ({|| kprog k', rmap x e (st :: nil) ||}) Gt'
        /\ terminal Gt' /\ collapse Gt' = collapse Gt.
  Proof.
    intros G Gt Hstar. induction Hstar as [G | G1 G2 G3 Hmix Hstar IH];
      intros Hterm k st HG c e x k' Hwf Hpair.
    - (* a terminal configuration cannot still owe an endpoint *)
      exfalso. subst G.
      destruct Hpair as (kmid & Hs & _).
      apply (kpick_not_terminated _ _ _ Hs).
      inversion Hterm as [| cc GG Hhd Htl]; subst. exact Hhd.
    - subst G1.
      destruct (kprog_mixed_inv _ _ _ Hmix)
        as (c0 & e0 & x0 & kmid0 & k1 & Hs0 & Hr0 & HG2).
      assert (Hpair0 : kpair k c0 e0 x0 k1) by (exists kmid0; split; assumption).
      destruct (Nat.eq_dec c0 c) as [Hcc | Hcc].
      + (* the scheduler took OUR pair — by uniqueness it really is ours *)
        subst c0. destruct Hpair as (kmid & Hs & Hr).
        destruct (comm_pair_unique k c e x kmid k' e0 x0 kmid0 k1
                    Hwf Hs Hr Hs0 Hr0) as (He & Hx & Hk).
        subst e0 x0 k1.
        exists G3. split; [| split; [exact Hterm | reflexivity]].
        rewrite <- HG2. exact Hstar.
      + (* a different pair: commute ours to the front *)
        destruct (kpair_confluent k c0 e0 x0 k1 c e x k' Hcc Hpair0 Hpair)
          as (k12 & Hp1 & Hp2).
        destruct (two_pairs_indep k c0 e0 x0 k1 c e x k12 Hwf Hpair0 Hp1)
          as (Hxx & Hxe0 & Hx0e).
        assert (Hwf1 : wf_phase k1) by (eapply wf_phase_pair; eassumption).
        destruct st as [s r].
        pose proof (IH Hterm k1 (s [ x0 |-> eval_expr (i_fn Σ) s e0 ], r)
                      ltac:(rewrite HG2; unfold rmap; cbn [map]; reflexivity)
                      c e x k12 Hwf1 Hp1) as (Gt1 & Hst1 & Ht1 & Hc1).
        assert (Hwf' : wf_phase k').
        { destruct Hpair as (m & A & B).
          exact (wf_phase_pair k c e x m k' Hwf A B). }
        assert (Hcp' : chan_pair k' c0).
        { destruct Hp2 as (m2 & A2 & _).
          exact (wf_phase_chan_pair k' m2 c0 e0 Hwf' A2). }
        exists Gt1. split; [| split; [exact Ht1 | exact Hc1]].
        eapply star_step.
        * apply (kpair_mixed_step k' c0 e0 x0 k12
                   (rmap x e ((s,r) :: nil)) Hcp'
                   ltac:(unfold rmap; cbn [map]; discriminate) Hp2).
        * rewrite (rmap_comm x e x0 e0 ((s,r) :: nil) Hxx Hxe0 Hx0e).
          unfold rmap in Hst1 |- *; cbn [map] in Hst1 |- *. exact Hst1.
  Qed.


(** ** 8. Par-Comp-MP — ensemble additivity *****************************

    Par-Comp is the one rule that composes three stages, so it is the one
    whose validity has to SUM over an intermediate ensemble: the premises
    speak about single states, while the middle of the chain starts from
    whatever the previous stage produced.  §8 is what makes that legal — a
    run from an appended ensemble splits into runs from the two halves.

    Layer 1 is one step ([distri_step_app]); layer 2 lifts it to a whole run
    ([Term_ens_app]).  The lifting is not routine, because [mixed_step]
    permutes the configuration and [norm]s away empty components, and a
    positional pairing survives neither.
*********************************************************************)

  (** Componentwise append of two configurations of the same shape. *)
  Fixpoint cfg_zip {A} (G1 G2 : list (A * ensemble dim))
    : list (A * ensemble dim) :=
    match G1, G2 with
    | (a, Ea) :: G1', (_, Eb) :: G2' => (a, Ea ++ Eb) :: cfg_zip G1' G2'
    | _, _ => nil
    end.

  (** Relabelling the residuals commutes with zipping — the [seq] case.  The
      hypothesis is "f rewrites the residual and carries the ensemble
      through", which is what every relabelling in the semantics does. *)
  Lemma cfg_zip_map : forall {A B} (f : A * ensemble dim -> B * ensemble dim),
      (forall a E, f (a, E) = (fst (f (a, nil)), E)) ->
      forall G1 G2, cfg_zip (map f G1) (map f G2) = map f (cfg_zip G1 G2).
  Proof.
    (* [cfg_zip] cannot reduce on an abstract [f (a, Ea)]: its pattern needs
       the head to be a literal pair, so [Hf] has to fire first. *)
    intros A B f Hf G1; induction G1 as [| [a Ea] G1' IH]; intros [| [b Eb] G2'];
      cbn [map].
    - reflexivity.
    - reflexivity.
    - rewrite (Hf a Ea); cbn [cfg_zip]; reflexivity.
    - rewrite (Hf a Ea), (Hf b Eb); cbn [cfg_zip map].
      f_equal; [symmetry; apply Hf | apply IH].
  Qed.

  Lemma local_step_app : forall L E1 E2 G1 G2,
      Σ ⊳ ‹ L, E1 › →ₗ G1 -> Σ ⊳ ‹ L, E2 › →ₗ G2 ->
      Σ ⊳ ‹ L, E1 ++ E2 › →ₗ cfg_zip G1 G2.
  Proof.
    intros L E1 E2 G1 G2 H1; revert E2 G2.
    induction H1 as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      intros E2 G2 H2;
      inversion H2 as
        [ Eb | x' e' Eb | q' Eb | U' qs' Eb | x' M' qs' Eb
        | L1' L2' Eb Gb Hs' | b' L1' L0' Eb ]; subst;
      cbn [cfg_zip app].
    - apply local_step_skip.
    - rewrite <- map_app. apply local_step_assign.
    - rewrite <- map_app. apply local_step_init.
    - rewrite <- map_app. apply local_step_ugate.
    - rewrite <- flat_map_app. apply local_step_meas.
    - (* seq *)
      rewrite cfg_zip_map by (intros [| L1'] E; reflexivity).
      apply local_step_seq, IH, Hs'.
    - (* if: the two filtered halves each split *)
      unfold ensemble_filter. rewrite <- !filter_app.
      apply local_step_if.
  Qed.

  (** A local step always exists and is unique, which is what turns the
      composition lemma above into the DECOMPOSITION the factorisation
      needs. *)
  Lemma local_step_total : forall L E, exists G, Σ ⊳ ‹ L, E › →ₗ G.
  Proof.
    intro L;
      induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intro E.
    - eexists; apply local_step_skip.
    - eexists; apply local_step_assign.
    - eexists; apply local_step_init.
    - eexists; apply local_step_ugate.
    - eexists; apply local_step_meas.
    - destruct (IH1 E) as (G & HG). eexists; apply local_step_seq, HG.
    - eexists; apply local_step_if.
  Qed.

  Lemma local_step_det : forall L E G G',
      Σ ⊳ ‹ L, E › →ₗ G -> Σ ⊳ ‹ L, E › →ₗ G' -> G = G'.
  Proof.
    intros L E G G' H1; revert G'.
    induction H1 as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      intros G' H2; inversion H2; subst; try reflexivity.
    match goal with H : Σ ⊳ ‹ L1, Ea › →ₗ ?Gb |- _ => rewrite (IH _ H) end.
    reflexivity.
  Qed.

  (** The residual SHAPE of a local step depends only on the block, never on
      the ensemble — which is what lets the two halves be paired up. *)
  Lemma local_step_shape : forall L E1 E2 G1 G2,
      Σ ⊳ ‹ L, E1 › →ₗ G1 -> Σ ⊳ ‹ L, E2 › →ₗ G2 ->
      map fst G1 = map fst G2.
  Proof.
    intros L E1 E2 G1 G2 H1; revert E2 G2.
    induction H1 as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      intros E2 G2 H2;
      inversion H2 as
        [ Eb | x' e' Eb | q' Eb | U' qs' Eb | x' M' qs' Eb
        | L1' L2' Eb Gb Hs' | b' L1' L0' Eb ]; subst; try reflexivity.
    assert (Hg : forall G : local_config dim,
               map (fun c : residual * ensemble dim =>
                      fst (match fst c with
                           | r_done => (r_more L2, snd c)
                           | r_more L1'' => (r_more (l_seq L1'' L2), snd c)
                           end)) G
               = map (fun R : residual =>
                        match R with
                        | r_done => r_more L2
                        | r_more L1'' => r_more (l_seq L1'' L2)
                        end) (map fst G)).
    { induction G as [| [R E'] G' IHG]; cbn [map fst]; [reflexivity |].
      destruct R; cbn [fst]; rewrite IHG; reflexivity. }
    rewrite !map_map, !Hg, (IH _ _ Hs'). reflexivity.
  Qed.

  Lemma map_fst_map : forall {A B} (f : A -> B) (G : list (A * ensemble dim)),
      map fst (map (fun c => (f (fst c), snd c)) G) = map f (map fst G).
  Proof.
    intros A B f G; induction G as [| [a E] G' IH]; cbn [map fst];
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma cfg_zip_shape : forall {A} (G1 G2 : list (A * ensemble dim)),
      map fst G1 = map fst G2 -> map fst (cfg_zip G1 G2) = map fst G1.
  Proof.
    intros A G1; induction G1 as [| [a Ea] G1' IH]; intros [| [b Eb] G2'] Hs;
      cbn [cfg_zip map fst] in *; try reflexivity; try discriminate.
    injection Hs as Hab Hs'. rewrite (IH _ Hs'); reflexivity.
  Qed.

  Lemma distri_step_app : forall P E1 E2 G,
      Σ ⊳ ‹ P, E1 ++ E2 › ⇝ G ->
      exists G1 G2, Σ ⊳ ‹ P, E1 › ⇝ G1 /\ Σ ⊳ ‹ P, E2 › ⇝ G2
                    /\ map fst G1 = map fst G2 /\ G = cfg_zip G1 G2.
  Proof.
    intros P E1 E2 G H. remember (E1 ++ E2) as E eqn:HE.
    revert E1 E2 HE.
    induction H as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 Ga Hs IH
      | P1 P2 E0 Gb Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ];
      intros E1 E2 HE; subst E0.
    - (* ds_local: decompose the local step by totality + determinacy *)
      destruct (local_step_total L E1) as (Gl1 & Hl1).
      destruct (local_step_total L E2) as (Gl2 & Hl2).
      exists (map (fun c => (leaf (advance (fst c) K T), snd c)) Gl1),
             (map (fun c => (leaf (advance (fst c) K T), snd c)) Gl2).
      split; [apply ds_local, Hl1 | split; [apply ds_local, Hl2 | split]].
      + rewrite !(map_fst_map (fun R => leaf (advance R K T))),
                (local_step_shape _ _ _ _ _ Hl1 Hl2); reflexivity.
      + rewrite cfg_zip_map by (intros [| L'] E; reflexivity).
        f_equal.
        exact (local_step_det _ _ _ _ Hloc (local_step_app _ _ _ _ _ Hl1 Hl2)).
    - (* ds_par_l *)
      destruct (IH E1 E2 eq_refl) as (G1 & G2 & H1 & H2 & Hsh & HG).
      exists (map (fun c => (fst c ∥ P2, snd c)) G1),
             (map (fun c => (fst c ∥ P2, snd c)) G2).
      split; [apply ds_par_l, H1 | split; [apply ds_par_l, H2 | split]].
      + rewrite !(map_fst_map (fun p => p ∥ P2)), Hsh; reflexivity.
      + rewrite cfg_zip_map by (intros a E; reflexivity).
        f_equal; exact HG.
    - (* ds_par_r *)
      destruct (IH E1 E2 eq_refl) as (G1 & G2 & H1 & H2 & Hsh & HG).
      exists (map (fun c => (P1 ∥ fst c, snd c)) G1),
             (map (fun c => (P1 ∥ fst c, snd c)) G2).
      split; [apply ds_par_r, H1 | split; [apply ds_par_r, H2 | split]].
      + rewrite !(map_fst_map (fun p => P1 ∥ p)), Hsh; reflexivity.
      + rewrite cfg_zip_map by (intros a E; reflexivity).
        f_equal; exact HG.
    - (* ds_comm_lr: the rendezvous is a map, so it splits outright *)
      eexists; eexists.
      split; [eapply ds_comm_lr; eassumption
             | split; [eapply ds_comm_lr; eassumption | split]].
      + reflexivity.
      + cbn [cfg_zip]. rewrite map_app. reflexivity.
    - eexists; eexists.
      split; [eapply ds_comm_rl; eassumption
             | split; [eapply ds_comm_rl; eassumption | split]].
      + reflexivity.
      + cbn [cfg_zip]. rewrite map_app. reflexivity.
  Qed.

  Definition matching : Type := list (program * (ensemble dim * ensemble dim)).

  Definition mjoin (L : matching) : distri_config dim :=
    map (fun t => (fst t, fst (snd t) ++ snd (snd t))) L.
  Definition mleft (L : matching) : distri_config dim :=
    map (fun t => (fst t, fst (snd t))) L.
  Definition mright (L : matching) : distri_config dim :=
    map (fun t => (fst t, snd (snd t))) L.

  Definition splits (G GA GB : distri_config dim) : Prop :=
    exists L, Permutation (norm G)  (norm (mjoin L))
           /\ Permutation (norm GA) (norm (mleft L))
           /\ Permutation (norm GB) (norm (mright L)).

  (** Empty components contribute nothing, so [norm] is invisible to
      [collapse]. *)
  Lemma collapse_norm : forall G : distri_config dim,
      collapse (norm G) = collapse G.
  Proof.
    induction G as [| [P E] G IH]; [reflexivity |].
    unfold norm, collapse in *; cbn [filter flat_map snd].
    destruct E as [| st E']; cbn [flat_map app]; [exact IH |].
    rewrite IH; reflexivity.
  Qed.

  Lemma collapse_perm : forall G G' : distri_config dim,
      Permutation G G' -> Permutation (collapse G) (collapse G').
  Proof. intros; unfold collapse; apply permutation_flat_map; assumption. Qed.

  Lemma collapse_mjoin : forall L : matching,
      Permutation (collapse (mjoin L))
                  (collapse (mleft L) ++ collapse (mright L)).
  Proof.
    induction L as [| [P [Ea Eb]] L IH].
    - apply Permutation_refl.
    - unfold mjoin, mleft, mright in *; cbn [map].
      unfold collapse in *; cbn [flat_map fst snd].
      eapply Permutation_trans; [apply Permutation_app_head, IH |].
      (* (Ea ⊎ Eb) ⊎ (X ⊎ Y)  ~  (Ea ⊎ X) ⊎ (Eb ⊎ Y): swap the middle two *)
      rewrite <- !app_assoc.
      apply Permutation_app_head.
      rewrite !app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
  Qed.

  (** The only thing the factorisation actually consumes. *)
  Lemma splits_collapse : forall G GA GB,
      splits G GA GB ->
      Permutation (collapse G) (collapse GA ++ collapse GB).
  Proof.
    intros G GA GB (L & HG & HA & HB).
    apply collapse_perm in HG, HA, HB.
    rewrite !collapse_norm in HG, HA, HB.
    eapply Permutation_trans; [exact HG |].
    eapply Permutation_trans; [apply collapse_mjoin |].
    apply Permutation_app; [apply Permutation_sym, HA | apply Permutation_sym, HB].
  Qed.

  (** [splits] only ever looks at configurations through [norm], so it is
      stable under permutation on the nose. *)
  Lemma splits_perm : forall G G' GA GA' GB GB',
      splits G GA GB ->
      Permutation G G' -> Permutation GA GA' -> Permutation GB GB' ->
      splits G' GA' GB'.
  Proof.
    intros G G' GA GA' GB GB' (L & HG & HA & HB) PG PA PB.
    exists L. split; [| split].
    - eapply Permutation_trans; [apply Permutation_sym, permutation_filter, PG | exact HG].
    - eapply Permutation_trans; [apply Permutation_sym, permutation_filter, PA | exact HA].
    - eapply Permutation_trans; [apply Permutation_sym, permutation_filter, PB | exact HB].
  Qed.

  (** ** norm, componentwise *)

  Lemma norm_app : forall G1 G2 : distri_config dim,
      norm (G1 ++ G2) = norm G1 ++ norm G2.
  Proof. intros; unfold norm; apply filter_app. Qed.

  Lemma norm_idem : forall G : distri_config dim, norm (norm G) = norm G.
  Proof.
    induction G as [| [P E] G IH]; [reflexivity |].
    unfold norm in *; cbn [filter snd].
    destruct E; cbn [filter snd]; [exact IH | rewrite IH; reflexivity].
  Qed.

  Lemma norm_perm : forall G G' : distri_config dim,
      Permutation G G' -> Permutation (norm G) (norm G').
  Proof. intros; apply permutation_filter; assumption. Qed.

  (** ** a step over the empty ensemble does nothing *)

  Lemma local_step_nil : forall L G,
      Σ ⊳ ‹ L, nil › →ₗ G -> Forall (fun c => snd c = nil) G.
  Proof.
    intros L G H. remember (@nil (cqstate dim)) as E eqn:HE. revert HE.
    induction H as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ]; intro HE; subst Ea;
      cbn [map flat_map ensemble_filter filter].
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
    - apply Forall_forall. intros c Hc.
      apply in_map_iff in Hc as ([R E'] & Heq & Hin).
      pose proof (IH eq_refl) as HG. rewrite Forall_forall in HG.
      specialize (HG _ Hin); cbn in HG.
      subst c; destruct R; cbn [snd]; exact HG.
    - repeat constructor.
  Qed.

  Lemma distri_step_nil : forall P G,
      Σ ⊳ ‹ P, nil › ⇝ G -> Forall (fun c => snd c = nil) G.
  Proof.
    intros P G H. remember (@nil (cqstate dim)) as E eqn:HE. revert HE.
    induction H as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 Ga Hs IH
      | P1 P2 E0 Gb Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ];
      intro HE; subst E0.
    - apply Forall_forall. intros c Hc.
      apply in_map_iff in Hc as ([R E'] & Heq & Hin).
      pose proof (local_step_nil _ _ Hloc) as HG. rewrite Forall_forall in HG.
      specialize (HG _ Hin); cbn in HG. subst c; cbn [snd]; exact HG.
    - apply Forall_forall. intros c Hc.
      apply in_map_iff in Hc as ([P' E'] & Heq & Hin).
      pose proof (IH eq_refl) as HG. rewrite Forall_forall in HG.
      specialize (HG _ Hin); cbn in HG. subst c; cbn [snd]; exact HG.
    - apply Forall_forall. intros c Hc.
      apply in_map_iff in Hc as ([P' E'] & Heq & Hin).
      pose proof (IH eq_refl) as HG. rewrite Forall_forall in HG.
      specialize (HG _ Hin); cbn in HG. subst c; cbn [snd]; exact HG.
    - repeat constructor.
    - repeat constructor.
  Qed.

  Lemma norm_empty : forall G : distri_config dim,
      Forall (fun c => snd c = nil) G -> norm G = nil.
  Proof.
    induction G as [| [P E] G IH]; [reflexivity |].
    intro HF; inversion HF as [| c G' Hc HG']; subst; cbn [snd] in Hc; subst E.
    unfold norm; cbn [filter snd]. apply IH; exact HG'.
  Qed.

  (** ** pairing two configurations of the same shape into a matching *)

  Fixpoint mzip (G1 G2 : distri_config dim) : matching :=
    match G1, G2 with
    | (P, Ea) :: G1', (_, Eb) :: G2' => (P, (Ea, Eb)) :: mzip G1' G2'
    | _, _ => nil
    end.

  (* peel one component without unfolding the projection itself, so the
     induction hypotheses keep matching *)
  Lemma mleft_cons : forall P Ea Eb (L : matching),
      mleft ((P, (Ea, Eb)) :: L) = (P, Ea) :: mleft L.
  Proof. reflexivity. Qed.

  Lemma mright_cons : forall P Ea Eb (L : matching),
      mright ((P, (Ea, Eb)) :: L) = (P, Eb) :: mright L.
  Proof. reflexivity. Qed.

  Lemma mjoin_cons : forall P Ea Eb (L : matching),
      mjoin ((P, (Ea, Eb)) :: L) = (P, Ea ++ Eb) :: mjoin L.
  Proof. reflexivity. Qed.

  Lemma mzip_left : forall G1 G2,
      map fst G1 = map fst G2 -> mleft (mzip G1 G2) = G1.
  Proof.
    intros G1; induction G1 as [| [P Ea] G1' IH]; intros [| [Q Eb] G2'] Hs;
      cbn [mzip map fst] in *; try reflexivity; try discriminate.
    injection Hs as HPQ Hs'.
    rewrite mleft_cons, (IH _ Hs'); reflexivity.
  Qed.

  Lemma mzip_right : forall G1 G2,
      map fst G1 = map fst G2 -> mright (mzip G1 G2) = G2.
  Proof.
    intros G1; induction G1 as [| [P Ea] G1' IH]; intros [| [Q Eb] G2'] Hs;
      cbn [mzip map fst] in *; try reflexivity; try discriminate.
    injection Hs as HPQ Hs'.
    rewrite mright_cons, (IH _ Hs'), HPQ; reflexivity.
  Qed.

  Lemma mzip_join : forall G1 G2,
      map fst G1 = map fst G2 -> mjoin (mzip G1 G2) = cfg_zip G1 G2.
  Proof.
    intros G1; induction G1 as [| [P Ea] G1' IH]; intros [| [Q Eb] G2'] Hs;
      cbn [mzip cfg_zip map fst] in *; try reflexivity; try discriminate.
    injection Hs as HPQ Hs'.
    rewrite mjoin_cons, (IH _ Hs'); reflexivity.
  Qed.

  Lemma mjoin_app : forall L1 L2 : matching,
      mjoin (L1 ++ L2) = mjoin L1 ++ mjoin L2.
  Proof. intros; unfold mjoin; apply map_app. Qed.

  Lemma mleft_app : forall L1 L2 : matching,
      mleft (L1 ++ L2) = mleft L1 ++ mleft L2.
  Proof. intros; unfold mleft; apply map_app. Qed.

  Lemma mright_app : forall L1 L2 : matching,
      mright (L1 ++ L2) = mright L1 ++ mright L2.
  Proof. intros; unfold mright; apply map_app. Qed.


  Lemma norm_cons_keep : forall (P : program) E (G : distri_config dim),
      E <> nil -> norm ((P, E) :: G) = (P, E) :: norm G.
  Proof. intros P [| st E'] G HE; [contradiction | reflexivity]. Qed.

  Lemma norm_cons_nil : forall (P : program) (G : distri_config dim),
      norm ((P, nil) :: G) = norm G.
  Proof. reflexivity. Qed.

  (** One side of the split, in isolation.  If that side's half of the chosen
      component is empty it simply does not move — [norm] has already deleted
      the component, so there is nothing there to select. *)
  Lemma splits_side_step :
    forall (GS : distri_config dim) (D : program) (Ea : ensemble dim)
           (S1 S2 GS1 : distri_config dim),
      Permutation (norm GS) (norm (S1 ++ (D, Ea) :: S2)) ->
      Σ ⊳ ‹ D, Ea › ⇝ GS1 ->
      exists GS',
        Permutation (norm GS') (norm (GS1 ++ (S1 ++ S2)))
        /\ (mixed_step Σ GS GS' \/ GS' = GS).
  Proof.
    intros GS D Ea S1 S2 GS1 Hperm Hd.
    destruct Ea as [| st Ea'].
    - (* empty half: stay put *)
      exists GS. split; [| right; reflexivity].
      rewrite norm_app, (norm_empty _ (distri_step_nil _ _ Hd)); cbn [app].
      eapply Permutation_trans; [exact Hperm |].
      rewrite norm_app, norm_cons_nil, <- norm_app.
      apply Permutation_refl.
    - (* non-empty half: it survives norm, so it can be selected *)
      assert (HinN : In (D, st :: Ea') (norm GS)).
      { eapply Permutation_in; [apply Permutation_sym, Hperm |].
        rewrite norm_app, norm_cons_keep by discriminate.
        apply in_or_app; right; left; reflexivity. }
      assert (Hin : In (D, st :: Ea') GS)
        by (unfold norm in HinN; apply filter_In in HinN as [Hx _]; exact Hx).
      apply in_split in Hin as (GSx & GSy & HGS).
      exists (norm (GS1 ++ (GSx ++ GSy))). split.
      + rewrite norm_idem, !norm_app.
        apply Permutation_app_head.
        assert (Hg : Permutation (norm (GSx ++ (D, st :: Ea') :: GSy))
                                 (norm (S1 ++ (D, st :: Ea') :: S2)))
          by (rewrite <- HGS; exact Hperm).
        rewrite !norm_app in Hg.
        rewrite !norm_cons_keep in Hg by discriminate.
        exact (Permutation_app_inv _ _ _ _ _ Hg).
      + left. apply (mixed_lift Σ GS D (st :: Ea') (GSx ++ GSy) GS1);
          [| exact Hd].
        rewrite HGS. apply Permutation_sym, Permutation_middle.
  Qed.

  (** THE layer-2 lemma: one step of the joined run is one step (or a stall)
      on each half. *)
  Lemma mixed_step_splits : forall G G' GA GB,
      mixed_step Σ G G' -> splits G GA GB ->
      exists GA' GB',
        splits G' GA' GB'
        /\ (mixed_step Σ GA GA' \/ GA' = GA)
        /\ (mixed_step Σ GB GB' \/ GB' = GB).
  Proof.
    intros G G' GA GB Hstep Hsp.
    destruct Hsp as (L & HG & HA & HB).
    inversion Hstep as [Gx D E G0 G1 Hperm Hd HeqGx HeqG']; subst.
    destruct E as [| st E0].
    - (* the selected component is empty: nothing moves anywhere *)
      exists GA, GB. split; [| split; right; reflexivity].
      exists L. split; [| split; assumption].
      rewrite norm_idem, norm_app,
              (norm_empty _ (distri_step_nil _ _ Hd)); cbn [app].
      eapply Permutation_trans; [| exact HG].
      apply Permutation_sym.
      eapply Permutation_trans; [apply norm_perm, Hperm |].
      rewrite norm_cons_nil. apply Permutation_refl.
    - (* locate the selected component inside the matching *)
      assert (HinG : In (D, st :: E0) (norm G)).
      { unfold norm; apply filter_In; split; [| reflexivity].
        eapply Permutation_in;
          [apply Permutation_sym, Hperm | left; reflexivity]. }
      assert (HinL : In (D, st :: E0) (mjoin L)).
      { pose proof (Permutation_in _ HG HinG) as Hx.
        unfold norm in Hx; apply filter_In in Hx as [Hx _]; exact Hx. }
      unfold mjoin in HinL.
      apply in_map_iff in HinL as ([D0 [Ea Eb]] & Heq & HinLt).
      cbn [fst snd] in Heq. injection Heq as HD HE; subst D0.
      apply in_split in HinLt as (L1 & L2 & HL).
      destruct (distri_step_app D Ea Eb G1)
        as (GA1 & GB1 & HdA & HdB & Hshape & HG1); [rewrite HE; exact Hd |].
      (* each half either steps or stalls *)
      assert (HAs : Permutation (norm GA)
                      (norm (mleft L1 ++ (D, Ea) :: mleft L2))).
      { eapply Permutation_trans; [exact HA |].
        rewrite HL, mleft_app, mleft_cons. apply Permutation_refl. }
      destruct (splits_side_step GA D Ea (mleft L1) (mleft L2) GA1 HAs HdA)
        as (GA' & HA' & HstepA).
      assert (HBs : Permutation (norm GB)
                      (norm (mright L1 ++ (D, Eb) :: mright L2))).
      { eapply Permutation_trans; [exact HB |].
        rewrite HL, mright_app, mright_cons. apply Permutation_refl. }
      destruct (splits_side_step GB D Eb (mright L1) (mright L2) GB1 HBs HdB)
        as (GB' & HB' & HstepB).
      exists GA', GB'. split; [| split; assumption].
      exists (mzip GA1 GB1 ++ (L1 ++ L2)). split; [| split].
      + (* the joined side: strip the selected component from both *)
        rewrite norm_idem, mjoin_app, (mzip_join _ _ Hshape), <- HG1, !norm_app.
        apply Permutation_app_head.
        assert (Hg : Permutation (norm ((D, st :: E0) :: G0))
                       (norm (mjoin L1 ++ (D, st :: E0) :: mjoin L2))).
        { eapply Permutation_trans; [apply Permutation_sym, norm_perm, Hperm |].
          eapply Permutation_trans; [exact HG |].
          rewrite HL, mjoin_app, mjoin_cons, HE. apply Permutation_refl. }
        rewrite norm_cons_keep in Hg by discriminate.
        rewrite norm_app, norm_cons_keep in Hg by discriminate.
        pose proof (Permutation_cons_app_inv _ _ Hg) as Hg'.
        rewrite mjoin_app, norm_app. exact Hg'.
      + rewrite !mleft_app, (mzip_left _ _ Hshape). exact HA'.
      + rewrite !mright_app, (mzip_right _ _ Hshape). exact HB'.
  Qed.

  (** A half may stall on some steps, so its run is a [step_star], not a
      step-for-step image. *)
  Lemma step_star_splits : forall G Gt GA GB,
      step_star Σ G Gt -> splits G GA GB ->
      exists GA' GB',
        splits Gt GA' GB' /\ step_star Σ GA GA' /\ step_star Σ GB GB'.
  Proof.
    intros G Gt GA GB Hstar; revert GA GB.
    induction Hstar as [G | Ga Gb Gc Hmix Hstar IH]; intros GA GB Hsp.
    - exists GA, GB. split; [exact Hsp | split; apply star_refl].
    - destruct (mixed_step_splits _ _ _ _ Hmix Hsp)
        as (GA1 & GB1 & Hsp1 & HA & HB).
      destruct (IH _ _ Hsp1) as (GA' & GB' & Hsp' & HstarA & HstarB).
      exists GA', GB'. split; [exact Hsp' | split].
      + destruct HA as [HA | HA];
          [eapply star_step; eassumption | subst GA1; exact HstarA].
      + destruct HB as [HB | HB];
          [eapply star_step; eassumption | subst GB1; exact HstarB].
  Qed.

  (** Every configuration reached after at least one step is already
      normalised, and a run that never moves leaves its start alone — so
      "no empty component" is an invariant of a run. *)
  Lemma step_star_norm_free : forall G G',
      step_star Σ G G' -> norm G = G -> norm G' = G'.
  Proof.
    intros G G' Hstar; induction Hstar as [G | Ga Gb Gc Hmix Hstar IH];
      intro Hn; [exact Hn |].
    apply IH. inversion Hmix; subst. apply norm_idem.
  Qed.


  (** A half's surviving components are exactly the joined ones that were
      non-empty on that side, so they inherit terminality. *)
  Lemma splits_terminal : forall Gt GA GB,
      splits Gt GA GB -> terminal Gt -> norm GA = GA -> terminal GA.
  Proof.
    intros Gt GA GB (L & HGt & HA & HB) Hterm Hnf.
    unfold terminal in *. rewrite <- Hnf.
    eapply Forall_perm; [apply Permutation_sym, HA |].
    apply Forall_forall. intros [P Ea] Hin.
    unfold norm in Hin; apply filter_In in Hin as [HinL HEa].
    unfold mleft in HinL.
    apply in_map_iff in HinL as ([P0 [Ea0 Eb0]] & Heq & Ht).
    cbn [fst snd] in Heq. injection Heq as HP HEq; subst P0 Ea0.
    assert (Hin2 : In (P, Ea ++ Eb0) (norm (mjoin L))).
    { unfold norm; apply filter_In; split.
      - unfold mjoin; apply in_map_iff.
        exists (P, (Ea, Eb0)); split; [reflexivity | exact Ht].
      - cbn [snd]. destruct Ea; [cbn in HEa; discriminate | reflexivity]. }
    pose proof (Permutation_in _ (Permutation_sym HGt) Hin2) as Hin3.
    unfold norm in Hin3; apply filter_In in Hin3 as [Hin4 _].
    rewrite Forall_forall in Hterm. exact (Hterm _ Hin4).
  Qed.

  (* [splits] is NOT symmetric: mjoin builds Ea ⊎ Eb, and swapping the halves
     would build Eb ⊎ Ea, a different configuration.  So the right half needs
     its own copy. *)
  Lemma splits_terminal_right : forall Gt GA GB,
      splits Gt GA GB -> terminal Gt -> norm GB = GB -> terminal GB.
  Proof.
    intros Gt GA GB (L & HGt & HA & HB) Hterm Hnf.
    unfold terminal in *. rewrite <- Hnf.
    eapply Forall_perm; [apply Permutation_sym, HB |].
    apply Forall_forall. intros [P Eb] Hin.
    unfold norm in Hin; apply filter_In in Hin as [HinL HEb].
    unfold mright in HinL.
    apply in_map_iff in HinL as ([P0 [Ea0 Eb0]] & Heq & Ht).
    cbn [fst snd] in Heq. injection Heq as HP HEq; subst P0 Eb0.
    assert (Hin2 : In (P, Ea0 ++ Eb) (norm (mjoin L))).
    { unfold norm; apply filter_In; split.
      - unfold mjoin; apply in_map_iff.
        exists (P, (Ea0, Eb)); split; [reflexivity | exact Ht].
      - cbn [snd]. destruct Eb as [| st Eb']; [cbn in HEb; discriminate |].
        destruct (Ea0 ++ st :: Eb') eqn:Eapp; [| reflexivity].
        apply app_eq_nil in Eapp as [_ Hbad]; discriminate. }
    pose proof (Permutation_in _ (Permutation_sym HGt) Hin2) as Hin3.
    unfold norm in Hin3; apply filter_In in Hin3 as [Hin4 _].
    rewrite Forall_forall in Hterm. exact (Hterm _ Hin4).
  Qed.

  (** ** The layer-2 payoff: a run from an appended ensemble splits. *)

  Definition Term_ens (P : program) (E E' : ensemble dim) : Prop :=
    exists G, step_star Σ ({|| P, E ||}) G /\ terminal G /\ collapse G = E'.

  Lemma splits_start : forall (P : program) (E1 E2 : ensemble dim),
      splits ({|| P, E1 ++ E2 ||}) ({|| P, E1 ||}) ({|| P, E2 ||}).
  Proof.
    intros P E1 E2. exists ((P, (E1, E2)) :: nil).
    cbn [mjoin mleft mright map fst snd].
    split; [| split]; apply Permutation_refl.
  Qed.

  Lemma Term_ens_app : forall P E1 E2 E',
      E1 <> nil -> E2 <> nil ->
      Term_ens P (E1 ++ E2) E' ->
      exists E1' E2',
        Term_ens P E1 E1' /\ Term_ens P E2 E2' /\ Permutation E' (E1' ++ E2').
  Proof.
    intros P E1 E2 E' HE1 HE2 (Gt & Hstar & Hterm & Hcoll).
    destruct (step_star_splits _ _ _ _ Hstar (splits_start P E1 E2))
      as (GA & GB & Hsp & HstarA & HstarB).
    assert (HnfA : norm ({|| P, E1 ||}) = {|| P, E1 ||})
      by (destruct E1; [contradiction | reflexivity]).
    assert (HnfB : norm ({|| P, E2 ||}) = {|| P, E2 ||})
      by (destruct E2; [contradiction | reflexivity]).
    exists (collapse GA), (collapse GB).
    split; [| split].
    - exists GA. split; [exact HstarA | split; [| reflexivity]].
      eapply splits_terminal; [exact Hsp | exact Hterm |].
      eapply step_star_norm_free; eassumption.
    - exists GB. split; [exact HstarB | split; [| reflexivity]].
      eapply splits_terminal_right; [exact Hsp | exact Hterm |].
      eapply step_star_norm_free; eassumption.
    - rewrite <- Hcoll. apply splits_collapse, Hsp.
  Qed.


  (** ** 9. Par-Comp-MP — a rendezvous commutes past a local block *********

      A rendezvous acts on the ensemble as [rmap x e]: it rewrites the store
      and leaves the quantum state ALONE.  So unlike Lemma 1, whose quantum
      half rests on [local_ops], this commutation is free on the quantum side
      and reduces to three classical checks — read off by treating the
      rendezvous as a block whose change is [x] and whose read is the
      variables of e.

      This is the computational core of Par-Comp's reordering.  Deciding that
      the two steps sit on DIFFERENT leaves is a separate matter, and belongs
      with the staging invariant. *)

  (** The rendezvous [x := e] does not interfere with the block L. *)
  Definition rdv_indep (L : lblock) (x : var) (e : expr) : Prop :=
    ~ In x (lblock_read L)
    /\ ~ In x (lblock_change L)
    /\ disjoint (lblock_change L) (expr_vars e).

  Lemma rdv_indep_seq : forall L1 L2 x e,
      rdv_indep (l_seq L1 L2) x e -> rdv_indep L1 x e /\ rdv_indep L2 x e.
  Proof.
    intros L1 L2 x e (Hr & Hc & Hd); cbn [lblock_read lblock_change] in *.
    split; (split; [| split]).
    - intro Hz; apply Hr, in_or_app; left; exact Hz.
    - intro Hz; apply Hc, in_or_app; left; exact Hz.
    - intros z Hz Hy; apply (Hd z); [apply in_or_app; left; exact Hz | exact Hy].
    - intro Hz; apply Hr, in_or_app; right; exact Hz.
    - intro Hz; apply Hc, in_or_app; right; exact Hz.
    - intros z Hz Hy; apply (Hd z); [apply in_or_app; right; exact Hz | exact Hy].
  Qed.

  Lemma rdv_indep_if : forall b L1 L0 x e,
      rdv_indep (l_if b L1 L0) x e ->
      rdv_indep L1 x e /\ rdv_indep L0 x e /\ ~ In x (bexpr_vars b).
  Proof.
    intros b L1 L0 x e (Hr & Hc & Hd); cbn [lblock_read lblock_change] in *.
    split; [| split].
    - split; [| split].
      + intro Hz; apply Hr, in_or_app; right; apply in_or_app; left; exact Hz.
      + intro Hz; apply Hc, in_or_app; left; exact Hz.
      + intros z Hz Hy;
          apply (Hd z); [apply in_or_app; left; exact Hz | exact Hy].
    - split; [| split].
      + intro Hz; apply Hr, in_or_app; right; apply in_or_app; right; exact Hz.
      + intro Hz; apply Hc, in_or_app; right; exact Hz.
      + intros z Hz Hy;
          apply (Hd z); [apply in_or_app; right; exact Hz | exact Hy].
    - intro Hz; apply Hr, in_or_app; left; exact Hz.
  Qed.

  Lemma filter_map_comm : forall {A B} (f : A -> B) (g : B -> bool) (l : list A),
      filter g (map f l) = map f (filter (fun a => g (f a)) l).
  Proof.
    intros A B f g l; induction l as [| a l' IH]; cbn [map filter];
      [reflexivity |].
    destruct (g (f a)); cbn [map]; rewrite IH; reflexivity.
  Qed.

  Lemma map_flat_map : forall {A B C} (h : B -> C) (g : A -> list B) (l : list A),
      map h (flat_map g l) = flat_map (fun a => map h (g a)) l.
  Proof.
    intros A B C h g l; induction l as [| a l' IH]; cbn [flat_map map];
      [reflexivity | rewrite map_app, IH; reflexivity].
  Qed.

  (** THE core: running L after the rendezvous is running it before, with the
      rendezvous applied to every branch. *)
  Lemma local_step_rmap : forall L x e E G,
      rdv_indep L x e ->
      Σ ⊳ ‹ L, E › →ₗ G ->
      Σ ⊳ ‹ L, rmap x e E › →ₗ
        map (fun c => (fst c, rmap x e (snd c))) G.
  Proof.
    intros L x e E G Hind Hstep; revert Hind.
    induction Hstep as
      [ Ea | x' e' Ea | q Ea | U qs Ea | x' M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      intro Hind; cbn [map fst snd].
    - apply local_step_skip.
    - (* assign: the two store updates commute *)
      destruct Hind as (Hr & Hc & Hd);
        cbn [lblock_read lblock_change] in Hr, Hc, Hd.
      replace (rmap x e
                 (map (fun '(s, r) => (s [x' |-> eval_expr (i_fn Σ) s e'], r)) Ea))
        with (map (fun '(s, r) => (s [x' |-> eval_expr (i_fn Σ) s e'], r))
                (rmap x e Ea));
        [apply local_step_assign |].
      unfold rmap; rewrite !map_map; apply map_ext; intros [s r]; cbn.
      f_equal. apply rendezvous_store_comm.
      + intro; subst x'; apply Hc; left; reflexivity.
      + exact Hr.
      + intro Hy; apply (Hd x'); [left; reflexivity | exact Hy].
    - (* init: touches only the quantum state *)
      replace (rmap x e (map (fun '(s, r) => (s, apply_init q r)) Ea))
        with (map (fun '(s, r) => (s, apply_init q r)) (rmap x e Ea));
        [apply local_step_init |].
      unfold rmap; rewrite !map_map; apply map_ext; intros [s r]; reflexivity.
    - (* unitary: likewise *)
      replace (rmap x e
                 (map (fun '(s, r) => (s, apply_unitary (i_uu Σ U qs) r)) Ea))
        with (map (fun '(s, r) => (s, apply_unitary (i_uu Σ U qs) r))
                (rmap x e Ea));
        [apply local_step_ugate |].
      unfold rmap; rewrite !map_map; apply map_ext; intros [s r]; reflexivity.
    - (* measurement: store update plus a branch, both commute *)
      destruct Hind as (Hr & Hc & Hd);
        cbn [lblock_read lblock_change] in Hr, Hc, Hd.
      replace (rmap x e
                 (flat_map (fun '(s, r) =>
                    map (fun m => (s [x' |-> m], apply_meas (i_mm Σ M qs) m r))
                        (fst (i_mm Σ M qs))) Ea))
        with (flat_map (fun '(s, r) =>
                map (fun m => (s [x' |-> m], apply_meas (i_mm Σ M qs) m r))
                    (fst (i_mm Σ M qs))) (rmap x e Ea));
        [apply local_step_meas |].
      unfold rmap; rewrite flat_map_map, map_flat_map.
      apply flat_map_ext'; intros [s r]; rewrite map_map.
      apply map_ext; intro m; cbn. f_equal.
      rewrite (eval_expr_update_notin _ _ x' m e)
        by (intro Hy; apply (Hd x'); [left; reflexivity | exact Hy]).
      apply store_update_comm.
      intro; subst x'; apply Hc; left; reflexivity.
    - (* seq: the relabelling and the rendezvous touch different components *)
      destruct (rdv_indep_seq _ _ _ _ Hind) as (H1 & _).
      replace (map (fun c => (fst c, rmap x e (snd c)))
                 (map (fun c => match fst c with
                                | r_done => (r_more L2, snd c)
                                | r_more L1' => (r_more (l_seq L1' L2), snd c)
                                end) Ga))
        with (map (fun c => match fst c with
                            | r_done => (r_more L2, snd c)
                            | r_more L1' => (r_more (l_seq L1' L2), snd c)
                            end)
                (map (fun c => (fst c, rmap x e (snd c))) Ga));
        [apply local_step_seq, IH, H1 |].
      rewrite !map_map; apply map_ext; intros [R E']; destruct R; reflexivity.
    - (* if: the guard cannot see x, so the split is unchanged.
         [⊎] is [app], which cbn [map] will not push through. *)
      cbn [app map fst snd].
      destruct (rdv_indep_if _ _ _ _ _ Hind) as (_ & _ & Hb).
      assert (Hf : forall p : bexpr,
                 ~ In x (bexpr_vars p) ->
                 ensemble_filter
                   (fun s => eval_bool (i_fn Σ) (i_rl Σ) s p) (rmap x e Ea)
                 = rmap x e
                     (ensemble_filter
                        (fun s => eval_bool (i_fn Σ) (i_rl Σ) s p) Ea)).
      { intros p Hp. unfold ensemble_filter, rmap.
        rewrite filter_map_comm. f_equal.
        apply filter_ext; intros [s r]; cbn.
        apply eval_bool_update_notin, Hp. }
      assert (Hnb : ~ In x (bexpr_vars (b_not b)))
        by (cbn [bexpr_vars]; exact Hb).
      replace (rmap x e
                 (ensemble_filter
                    (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) Ea))
        with (ensemble_filter
                (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) (rmap x e Ea))
        by (apply (Hf b Hb)).
      replace (rmap x e
                 (ensemble_filter
                    (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) Ea))
        with (ensemble_filter
                (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b))
                (rmap x e Ea))
        by (apply (Hf (b_not b) Hnb)).
      apply local_step_if.
  Qed.

(** ** 10. Par-Comp-MP — positions, so that "different leaves" can be said ***

    The reordering has to know that two steps act on DIFFERENT leaves, and
    the semantics does not record it: [ds_par_l]/[ds_par_r] nest, and
    [replace_leaf] only says "some leaf equal to a".  A [path] makes the
    position explicit; [step_at] is [distri_step] carrying it; and then
    "different leaves" is just [p <> q], with the footprints supplied by
    [wf_ownership_paths].
*********************************************************************)


  Inductive path : Type :=
  | ph_here : path
  | ph_l    : path -> path
  | ph_r    : path -> path.

  Fixpoint leaf_at {A} (r : row A) (p : path) : option A :=
    match r, p with
    | leaf a,    ph_here => Some a
    | par r1 _,  ph_l p' => leaf_at r1 p'
    | par _ r2,  ph_r p' => leaf_at r2 p'
    | _,         _       => None
    end.

  (* off-path (or off-shape) writes are the identity, which is what makes
     [set_at_comm] hold with no well-formedness side condition *)
  Fixpoint set_at {A} (r : row A) (p : path) (a : A) : row A :=
    match r, p with
    | leaf _,     ph_here => leaf a
    | par r1 r2,  ph_l p' => par (set_at r1 p' a) r2
    | par r1 r2,  ph_r p' => par r1 (set_at r2 p' a)
    | _,          _       => r
    end.

  Lemma set_at_here : forall {A} (r : row A) a b,
      leaf_at r ph_here = Some a -> set_at r ph_here b = leaf b.
  Proof. intros A [x | r1 r2] a b H; [reflexivity | discriminate]. Qed.

  Lemma leaf_at_set_same : forall {A} (r : row A) p a b,
      leaf_at r p = Some a -> leaf_at (set_at r p b) p = Some b.
  Proof.
    intros A r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] a b H;
      cbn in *; try discriminate; try reflexivity.
    - apply (IH1 _ _ _ H).
    - apply (IH2 _ _ _ H).
  Qed.

  Lemma leaf_at_set_other : forall {A} (r : row A) p q a,
      p <> q -> leaf_at (set_at r q a) p = leaf_at r p.
  Proof.
    intros A r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] [| q' | q'] a Hne;
      cbn; try reflexivity.
    - exfalso; apply Hne; reflexivity.
    - apply IH1; congruence.
    - apply IH2; congruence.
  Qed.

  (** Writes at different positions commute. *)
  Lemma set_at_comm : forall {A} (r : row A) p q a b,
      p <> q -> set_at (set_at r p a) q b = set_at (set_at r q b) p a.
  Proof.
    intros A r; induction r as [x | r1 IH1 r2 IH2];
      intros [| p' | p'] [| q' | q'] a b Hne; cbn; try reflexivity.
    - exfalso; apply Hne; reflexivity.
    - rewrite IH1 by congruence; reflexivity.
    - rewrite IH2 by congruence; reflexivity.
  Qed.

  (** [replace_leaf] is "there is a position holding a". *)
  Lemma replace_leaf_path : forall {A} (a b : A) (r r' : row A),
      replace_leaf a b r r' ->
      exists p, leaf_at r p = Some a /\ r' = set_at r p b.
  Proof.
    intros A a b r r' H; induction H as [| r r' q Hr IH | r q q' Hr IH].
    - exists ph_here. split; reflexivity.
    - destruct IH as (p & Hl & Hs). exists (ph_l p).
      split; [exact Hl | cbn; rewrite <- Hs; reflexivity].
    - destruct IH as (p & Hl & Hs). exists (ph_r p).
      split; [exact Hl | cbn; rewrite <- Hs; reflexivity].
  Qed.

  Lemma path_replace_leaf : forall {A} (a b : A) (r : row A) p,
      leaf_at r p = Some a -> replace_leaf a b r (set_at r p b).
  Proof.
    intros A a b r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] H;
      cbn in *; try discriminate.
    - injection H as Hx; subst x. apply rl_here.
    - apply rl_left, IH1, H.
    - apply rl_right, IH2, H.
  Qed.

  (* the result is given by an equation rather than in the conclusion, so
     that both directions of the bridge can [apply] these and discharge the
     shape separately *)
  Inductive step_at : program -> ensemble dim -> distri_config dim -> Prop :=
  | sa_local : forall p L K T P E Gl G,
      leaf_at P p = Some (phase (r_more L) K T) ->
      Σ ⊳ ‹ L, E › →ₗ Gl ->
      G = map (fun c => (set_at P p (advance (fst c) K T), snd c)) Gl ->
      step_at P E G
  | sa_comm : forall ps pr P E c e x Ks Ks' Kr Kr' Ts Tr G,
      ps <> pr ->
      leaf_at P ps = Some (phase r_done Ks Ts) ->
      leaf_at P pr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send c e □ Ks' ->
      Kr ∋ c_recv c x □ Kr' ->
      G = {|| set_at (set_at P ps (advance r_done Ks' Ts)) pr
                (advance r_done Kr' Tr),
              rmap x e E ||} ->
      step_at P E G.

  (** ** step_at implies distri_step *)

  Lemma sa_local_step : forall p L K T P E Gl,
      leaf_at P p = Some (phase (r_more L) K T) ->
      Σ ⊳ ‹ L, E › →ₗ Gl ->
      Σ ⊳ ‹ P, E › ⇝
        map (fun c => (set_at P p (advance (fst c) K T), snd c)) Gl.
  Proof.
    intros p; induction p as [| p' IH | p' IH];
      intros L K T P E Gl Hleaf Hloc.
    - destruct P as [S | P1 P2]; cbn in Hleaf; [| discriminate].
      injection Hleaf as HS; subst S; cbn [set_at].
      apply ds_local, Hloc.
    - destruct P as [S | P1 P2]; cbn in Hleaf; [discriminate |].
      cbn [set_at].
      pose proof (ds_par_l Σ P1 P2 E _ (IH _ _ _ _ _ _ Hleaf Hloc)) as Hd.
      rewrite map_map in Hd; cbn [fst snd] in Hd. exact Hd.
    - destruct P as [S | P1 P2]; cbn in Hleaf; [discriminate |].
      cbn [set_at].
      pose proof (ds_par_r Σ P1 P2 E _ (IH _ _ _ _ _ _ Hleaf Hloc)) as Hd.
      rewrite map_map in Hd; cbn [fst snd] in Hd. exact Hd.
  Qed.

  Lemma sa_comm_step : forall ps pr P E c e x Ks Ks' Kr Kr' Ts Tr,
      ps <> pr ->
      leaf_at P ps = Some (phase r_done Ks Ts) ->
      leaf_at P pr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send c e □ Ks' ->
      Kr ∋ c_recv c x □ Kr' ->
      Σ ⊳ ‹ P, E › ⇝
        {|| set_at (set_at P ps (advance r_done Ks' Ts)) pr
              (advance r_done Kr' Tr),
            rmap x e E ||}.
  Proof.
    intros ps; induction ps as [| ps' IH | ps' IH];
      intros pr P E c e x Ks Ks' Kr Kr' Ts Tr Hne Hs Hr HpS HpR.
    - (* the sender is the whole row, so there is no second leaf *)
      destruct P as [S | P1 P2]; cbn in Hs, Hr; [| discriminate].
      destruct pr; cbn in Hr; [exfalso; apply Hne; reflexivity
                              | discriminate | discriminate].
    - destruct P as [S | P1 P2]; cbn in Hs; [discriminate |].
      destruct pr as [| pr' | pr']; cbn in Hr; [discriminate | |].
      + (* both on the left: sink with ds_par_l *)
        cbn [set_at].
        pose proof (ds_par_l Σ P1 P2 E _
                      (IH pr' P1 E c e x Ks Ks' Kr Kr' Ts Tr
                         ltac:(congruence) Hs Hr HpS HpR)) as Hd.
        cbn [map fst snd] in Hd. exact Hd.
      + (* sender left, receiver right: a genuine ds_comm_lr *)
        cbn [set_at].
        apply (ds_comm_lr Σ P1 _ P2 _ Ks Ks' Kr Kr' Ts Tr c e x E HpS HpR).
        * apply path_replace_leaf, Hs.
        * apply path_replace_leaf, Hr.
    - destruct P as [S | P1 P2]; cbn in Hs; [discriminate |].
      destruct pr as [| pr' | pr']; cbn in Hr; [discriminate | |].
      + (* sender right, receiver left: ds_comm_rl *)
        cbn [set_at].
        apply (ds_comm_rl Σ P1 _ P2 _ Ks Ks' Kr Kr' Ts Tr c e x E HpS HpR).
        * apply path_replace_leaf, Hs.
        * apply path_replace_leaf, Hr.
      + cbn [set_at].
        pose proof (ds_par_r Σ P1 P2 E _
                      (IH pr' P2 E c e x Ks Ks' Kr Kr' Ts Tr
                         ltac:(congruence) Hs Hr HpS HpR)) as Hd.
        cbn [map fst snd] in Hd. exact Hd.
  Qed.

  Lemma step_at_distri : forall P E G, step_at P E G -> Σ ⊳ ‹ P, E › ⇝ G.
  Proof.
    intros P E G H; destruct H; subst.
    - eapply sa_local_step; eassumption.
    - eapply sa_comm_step; eassumption.
  Qed.

  (** ** distri_step implies step_at *)

  Lemma distri_step_at : forall P E G, Σ ⊳ ‹ P, E › ⇝ G -> step_at P E G.
  Proof.
    intros P E G H; induction H as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 Ga Hs IH
      | P1 P2 E0 Gb Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ].
    - eapply (sa_local ph_here L K T); [reflexivity | exact Hloc | reflexivity].
    - (* ds_par_l: shift every position under ph_l *)
      inversion IH as
        [p L K T Px Ex Gl Gx Hleaf Hloc Heq
        | ps pr Px Ex c e x Ks Ks' Kr Kr' Ts Tr Gx Hne Hsn Hrc HpS HpR Heq];
        subst.
      + eapply (sa_local (ph_l p) L K T); [cbn; exact Hleaf | exact Hloc |].
        cbn [set_at]; rewrite map_map; reflexivity.
      + eapply (sa_comm (ph_l ps) (ph_l pr));
          [ congruence | cbn; exact Hsn | cbn; exact Hrc
          | exact HpS | exact HpR |].
        cbn [set_at map fst snd]. reflexivity.
    - (* ds_par_r *)
      inversion IH as
        [p L K T Px Ex Gl Gx Hleaf Hloc Heq
        | ps pr Px Ex c e x Ks Ks' Kr Kr' Ts Tr Gx Hne Hsn Hrc HpS HpR Heq];
        subst.
      + eapply (sa_local (ph_r p) L K T); [cbn; exact Hleaf | exact Hloc |].
        cbn [set_at]; rewrite map_map; reflexivity.
      + eapply (sa_comm (ph_r ps) (ph_r pr));
          [ congruence | cbn; exact Hsn | cbn; exact Hrc
          | exact HpS | exact HpR |].
        cbn [set_at map fst snd]. reflexivity.
    - (* ds_comm_lr: sender left, receiver right, so the paths differ *)
      apply replace_leaf_path in HrS as (ps & Hsn & HP1').
      apply replace_leaf_path in HrR as (pr & Hrc & HP2').
      eapply (sa_comm (ph_l ps) (ph_r pr));
        [ discriminate | cbn; exact Hsn | cbn; exact Hrc
        | exact HpS | exact HpR |].
      cbn [set_at]. rewrite HP1', HP2'. reflexivity.
    - (* ds_comm_rl *)
      apply replace_leaf_path in HrS as (ps & Hsn & HP2').
      apply replace_leaf_path in HrR as (pr & Hrc & HP1').
      eapply (sa_comm (ph_r ps) (ph_l pr));
        [ discriminate | cbn; exact Hsn | cbn; exact Hrc
        | exact HpS | exact HpR |].
      cbn [set_at]. rewrite HP1', HP2'. reflexivity.
  Qed.


  Lemma leaf_at_flat_incl : forall {A B} (f : A -> list B) (r : row A) p a,
      leaf_at r p = Some a -> incl (f a) (row_flat f r).
  Proof.
    intros A B f r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] a H;
      cbn in *; try discriminate.
    - injection H as Hx; subst x. apply incl_refl.
    - eapply incl_tran; [apply (IH1 _ _ H) | apply incl_appl, incl_refl].
    - eapply incl_tran; [apply (IH2 _ _ H) | apply incl_appr, incl_refl].
  Qed.

  Lemma wf_ownership_paths : forall (P : program) p q Sp Sq,
      wf_ownership P -> p <> q ->
      leaf_at P p = Some Sp -> leaf_at P q = Some Sq ->
      disjoint (process_change Sp) (process_cvar Sq)
      /\ disjoint (process_change Sq) (process_cvar Sp)
      /\ disjoint (process_qvar Sp) (process_qvar Sq).
  Proof.
    intros P; induction P as [S | P1 IH1 P2 IH2];
      intros [| p' | p'] [| q' | q'] Sp Sq Hown Hne Hp Hq;
      cbn in Hp, Hq; try discriminate.
    - exfalso; apply Hne; reflexivity.
    - (* both in the left subtree *)
      destruct Hown as (Ho1 & _ & _).
      apply (IH1 p' q' Sp Sq Ho1); [congruence | exact Hp | exact Hq].
    - (* p left, q right: this is exactly cross_disjoint *)
      destruct Hown as (_ & _ & Hc12 & Hc21 & Hq12).
      repeat split.
      + eapply disjoint_incl;
          [ exact Hc12
          | apply (leaf_at_flat_incl process_change _ _ _ Hp)
          | apply (leaf_at_flat_incl process_cvar _ _ _ Hq) ].
      + eapply disjoint_incl;
          [ exact Hc21
          | apply (leaf_at_flat_incl process_change _ _ _ Hq)
          | apply (leaf_at_flat_incl process_cvar _ _ _ Hp) ].
      + eapply disjoint_incl;
          [ exact Hq12
          | apply (leaf_at_flat_incl process_qvar _ _ _ Hp)
          | apply (leaf_at_flat_incl process_qvar _ _ _ Hq) ].
    - (* p right, q left *)
      destruct Hown as (_ & _ & Hc12 & Hc21 & Hq12).
      repeat split.
      + eapply disjoint_incl;
          [ exact Hc21
          | apply (leaf_at_flat_incl process_change _ _ _ Hp)
          | apply (leaf_at_flat_incl process_cvar _ _ _ Hq) ].
      + eapply disjoint_incl;
          [ exact Hc12
          | apply (leaf_at_flat_incl process_change _ _ _ Hq)
          | apply (leaf_at_flat_incl process_cvar _ _ _ Hp) ].
      + intros z Hz Hy.
        apply (Hq12 z);
          [ apply (leaf_at_flat_incl process_qvar _ _ _ Hq); exact Hy
          | apply (leaf_at_flat_incl process_qvar _ _ _ Hp); exact Hz ].
    - (* both in the right subtree *)
      destruct Hown as (_ & Ho2 & _).
      apply (IH2 p' q' Sp Sq Ho2); [congruence | exact Hp | exact Hq].
  Qed.


(** ** 11. Par-Comp-MP — normalising away the d-stage ********************

    Rather than bubbling every d-step to the front of a run, map the run into
    one where they have already happened.  [ndrop t P] is P with the D part
    of every leaf that is still [before] its tail removed, and
    [nlseq t P] is the displayed sequence of those D parts.

    Which leaves are still in D cannot be read off their SHAPE — [advance ↓ ε
    T] drops a leaf straight into T, and T may itself be a phase.  The
    discriminator is the TAIL: a leaf still in D/K has T literally as its
    tail, and once it falls through, its tail is a proper subterm of T.  That
    test is decidable, which is what lets the normalisation be a function.
*********************************************************************)


  (** ** Decidable equality, so that the stage test is a function *)

  Lemma expr_eq_dec : forall e1 e2 : expr, {e1 = e2} + {e1 <> e2}.
  Proof.
    fix REC 1.
    destruct e1 as [v1 | x1 | f1 es1]; destruct e2 as [v2 | x2 | f2 es2];
      try (right; discriminate).
    - destruct (Nat.eq_dec v1 v2); [left; congruence | right; congruence].
    - destruct (Nat.eq_dec x1 x2); [left; congruence | right; congruence].
    - destruct (Nat.eq_dec f1 f2); [| right; congruence].
      destruct (list_eq_dec REC es1 es2); [left; congruence | right; congruence].
  Defined.

  Lemma bexpr_eq_dec : forall b1 b2 : bexpr, {b1 = b2} + {b1 <> b2}.
  Proof.
    decide equality; try apply Nat.eq_dec.
    apply (list_eq_dec expr_eq_dec).
  Defined.

  Lemma lblock_eq_dec : forall L1 L2 : lblock, {L1 = L2} + {L1 <> L2}.
  Proof.
    decide equality; try apply Nat.eq_dec; try apply expr_eq_dec;
      try apply bexpr_eq_dec; apply (list_eq_dec Nat.eq_dec).
  Defined.

  Lemma caction_eq_dec : forall a1 a2 : caction, {a1 = a2} + {a1 <> a2}.
  Proof. decide equality; try apply Nat.eq_dec; apply expr_eq_dec. Defined.

  Lemma residual_eq_dec : forall R1 R2 : residual, {R1 = R2} + {R1 <> R2}.
  Proof. decide equality; apply lblock_eq_dec. Defined.

  Lemma process_eq_dec : forall S1 S2 : process, {S1 = S2} + {S1 <> S2}.
  Proof.
    decide equality; try apply residual_eq_dec;
      apply (list_eq_dec caction_eq_dec).
  Defined.

  (** ** The stage test *)

  Fixpoint proc_size (S : process) : nat :=
    match S with
    | terminated  => 0
    | phase _ _ T => Datatypes.S (proc_size T)
    end.

  (** "S has not yet fallen through into T". *)
  Definition before (T S : process) : Prop := exists R K, S = phase R K T.

  Definition beforeb (T S : process) : bool :=
    match S with
    | terminated  => false
    | phase _ _ T' => if process_eq_dec T' T then true else false
    end.

  Lemma beforeb_spec : forall T S, beforeb T S = true <-> before T S.
  Proof.
    intros T [| R K T']; cbn.
    - split; [discriminate | intros (R & K & H); discriminate].
    - destruct (process_eq_dec T' T) as [He | Hne]; subst.
      + split; [intros _; exists R, K; reflexivity | reflexivity].
      + split; [discriminate |].
        intros (R0 & K0 & H); injection H as _ _ HT; contradiction.
  Qed.

  (** A leaf that is [before T] is strictly bigger than T, which is what makes
      the two stages exclusive: nothing is [before] itself, and once a leaf has
      fallen through, its tail can never grow back to T. *)
  Lemma before_size : forall T S, before T S -> proc_size S = Datatypes.S (proc_size T).
  Proof. intros T S (R & K & H); subst; reflexivity. Qed.

  Lemma not_before_self : forall T, ~ before T T.
  Proof. intros T H; apply before_size in H; lia. Qed.

  (** Falling through: after a step a leaf is [advance R K T'], which is
      [before T'] unless the phase is exhausted, in which case it IS T'. *)
  Lemma advance_before : forall R K T,
      before T (advance R K T) \/ advance R K T = T.
  Proof.
    intros [| L] [| a K'] T; cbn [advance];
      try (left; eexists; eexists; reflexivity).
    right; reflexivity.
  Qed.


  (** ** Two rows of the same shape *)

  Fixpoint same_shape {A B} (r1 : row A) (r2 : row B) : Prop :=
    match r1, r2 with
    | leaf _,     leaf _     => True
    | par x1 y1,  par x2 y2  => same_shape x1 x2 /\ same_shape y1 y2
    | _,          _          => False
    end.

  Lemma same_shape_refl : forall {A} (r : row A), same_shape r r.
  Proof. intros A r; induction r; cbn; [exact Logic.I | split; assumption]. Qed.

  Lemma same_shape_map : forall {A B} (f : A -> B) (r : row A),
      same_shape r (row_map f r).
  Proof. intros A B f r; induction r; cbn; [exact Logic.I | split; assumption]. Qed.

  Lemma same_shape_set_at : forall {A B} (r1 : row A) (r2 : row B) p a,
      same_shape r1 r2 -> same_shape r1 (set_at r2 p a).
  Proof.
    intros A B r1; induction r1 as [x | x1 IH1 y1 IH2];
      intros [y | x2 y2] [| p' | p'] a Hs; cbn in *; try contradiction;
      try exact Logic.I; try (destruct Hs; split; auto).
  Qed.

  Fixpoint row_zip {A B C} (dflt : C) (f : A -> B -> C)
                   (r1 : row A) (r2 : row B) : row C :=
    match r1, r2 with
    | leaf a,     leaf b     => leaf (f a b)
    | par x1 y1,  par x2 y2  => par (row_zip dflt f x1 x2) (row_zip dflt f y1 y2)
    | _,          _          => leaf dflt
    end.

  (** ** Per-leaf: the D part, and the leaf with its D part removed *)

  Definition dk_block (T S : process) : lblock :=
    if beforeb T S
    then match S with
         | phase R _ _ => residual_lblock R
         | terminated  => l_skip
         end
    else l_skip.

  Definition dk_drop (T S : process) : process :=
    if beforeb T S
    then match S with
         | phase _ K T' => advance r_done K T'
         | terminated   => terminated
         end
    else S.

  Definition ndrop (t P : program) : program := row_zip terminated dk_drop t P.
  Definition nblocks (t P : program) : lrow := row_zip l_skip dk_block t P.
  Definition nlseq (t P : program) : lblock := lseq (nblocks t P).

  Lemma beforeb_phase : forall T R K, beforeb T (phase R K T) = true.
  Proof.
    intros T R K; cbn [beforeb].
    destruct (process_eq_dec T T); [reflexivity | contradiction].
  Qed.

  (* the boundary case: once a leaf falls through into T, it is no longer
     [before T] — nothing is [before] itself *)
  Lemma beforeb_self : forall T, beforeb T T = false.
  Proof.
    intro T; destruct (beforeb T T) eqn:E; [| reflexivity].
    exfalso; apply (not_before_self T), beforeb_spec, E.
  Qed.

  Lemma dk_drop_phase : forall T R K,
      dk_drop T (phase R K T) = advance r_done K T.
  Proof. intros; unfold dk_drop; rewrite beforeb_phase; reflexivity. Qed.

  (** ** A d-step leaves [ndrop] alone.

      That is the whole point of the map: whichever residual the step leaves
      behind, the leaf's K and tail are untouched, so dropping the D part gives
      the same thing — including the boundary case where the phase is exhausted
      and the leaf falls through into its tail. *)
  Lemma dk_drop_advance : forall T R K R',
      dk_drop T (phase R K T) = dk_drop T (advance R' K T).
  Proof.
    intros T R K R'. rewrite dk_drop_phase.
    destruct R' as [| L']; destruct K as [| a K0]; cbn [advance].
    - unfold dk_drop; rewrite beforeb_self; reflexivity.
    - rewrite dk_drop_phase; reflexivity.
    - rewrite dk_drop_phase; reflexivity.
    - rewrite dk_drop_phase; reflexivity.
  Qed.

  (** Lifted to the whole row: rewriting one leaf in a way that [dk_drop]
      cannot see leaves [ndrop] alone. *)
  Lemma ndrop_set : forall t P p T S S',
      same_shape t P ->
      leaf_at t p = Some T ->
      leaf_at P p = Some S ->
      dk_drop T S' = dk_drop T S ->
      ndrop t (set_at P p S') = ndrop t P.
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S S' Hsh Ht Hp Hd;
      cbn in Hsh, Ht, Hp; try contradiction; try discriminate.
    - injection Ht as HT; injection Hp as HS; subst.
      unfold ndrop; cbn [row_zip set_at]. rewrite Hd. reflexivity.
    - destruct Hsh as [Hs1 Hs2].
      unfold ndrop in *; cbn [row_zip set_at].
      rewrite (IH1 P1 p' T S S' Hs1 Ht Hp Hd). reflexivity.
    - destruct Hsh as [Hs1 Hs2].
      unfold ndrop in *; cbn [row_zip set_at].
      rewrite (IH2 P2 p' T S S' Hs2 Ht Hp Hd). reflexivity.
  Qed.

  (** The d-step case of the above: the step rewrote a leaf that was [before]
      its tail, and left the K and the tail untouched. *)
  Corollary ndrop_dstep : forall t P p T R K R',
      same_shape t P ->
      leaf_at t p = Some T ->
      leaf_at P p = Some (phase R K T) ->
      ndrop t (set_at P p (advance R' K T)) = ndrop t P.
  Proof.
    intros. eapply ndrop_set; try eassumption.
    symmetry; apply dk_drop_advance.
  Qed.

  (** A leaf that has already fallen through is invisible to [ndrop] too, so a
      tail step leaves the dropped program alone as well — except at the leaf
      itself, where it steps. *)
  Lemma dk_drop_not_before : forall T S,
      beforeb T S = false -> dk_drop T S = S.
  Proof. intros T S H; unfold dk_drop; rewrite H; reflexivity. Qed.

  Lemma ndrop_leaf_at : forall t P p T S,
      same_shape t P ->
      leaf_at t p = Some T ->
      leaf_at P p = Some S ->
      leaf_at (ndrop t P) p = Some (dk_drop T S).
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S Hsh Ht Hp;
      cbn in Hsh, Ht, Hp; try contradiction; try discriminate.
    - injection Ht as HT; injection Hp as HS; subst.
      unfold ndrop; cbn [row_zip leaf_at]. reflexivity.
    - destruct Hsh as [Hs1 _]. unfold ndrop; cbn [row_zip leaf_at].
      apply (IH1 P1 p' T S Hs1 Ht Hp).
    - destruct Hsh as [_ Hs2]. unfold ndrop; cbn [row_zip leaf_at].
      apply (IH2 P2 p' T S Hs2 Ht Hp).
  Qed.

  Lemma ndrop_set_other : forall t P p T S',
      same_shape t P ->
      leaf_at t p = Some T ->
      ndrop t (set_at P p S') = set_at (ndrop t P) p (dk_drop T S').
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S' Hsh Ht;
      cbn in Hsh, Ht; try contradiction; try discriminate.
    - injection Ht as HT; subst.
      unfold ndrop; cbn [row_zip set_at]. reflexivity.
    - destruct Hsh as [Hs1 _]. unfold ndrop in *; cbn [row_zip set_at].
      rewrite (IH1 P1 p' T S' Hs1 Ht). reflexivity.
    - destruct Hsh as [_ Hs2]. unfold ndrop in *; cbn [row_zip set_at].
      rewrite (IH2 P2 p' T S' Hs2 Ht). reflexivity.
  Qed.


  Lemma leaf_at_In : forall {A} (r : row A) p a,
      leaf_at r p = Some a -> In a (row_leaves r).
  Proof.
    intros A r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] a H;
      cbn in *; try discriminate.
    - injection H as Hx; subst; left; reflexivity.
    - apply in_or_app; left; apply (IH1 _ _ H).
    - apply in_or_app; right; apply (IH2 _ _ H).
  Qed.

  (** The displayed sequence with one leaf's block pulled to the front. *)
  Lemma lseq_pull : local_ops ->
    forall (dd : lrow) p L E,
      leaf_at dd p <> None ->
      lrow_disj (set_at dd p L) ->
      Permutation (denote (lseq (set_at dd p L)) E)
                  (denote (lseq (set_at dd p l_skip)) (denote L E)).
  Proof.
    intros Hloc dd; induction dd as [D0 | d1 IH1 d2 IH2];
      intros [| p' | p'] L E Hsome Hdisj; cbn in Hsome; try congruence.
    - (* the whole row is this leaf *)
      cbn [set_at lseq]. cbn [denote]. apply Permutation_refl.
    - (* left subtree: the block is already in front *)
      cbn [set_at lseq] in *; cbn [denote].
      unfold lrow_disj in Hdisj; cbn [row_leaves] in Hdisj.
      destruct (ForallOrdPairs_app_inv _ _ _ Hdisj) as (Hd1 & _ & _).
      apply denote_perm, (IH1 p' L E Hsome Hd1).
    - (* right subtree: the block has to cross the left one *)
      cbn [set_at lseq] in *; cbn [denote].
      unfold lrow_disj in Hdisj; cbn [row_leaves] in Hdisj.
      destruct (ForallOrdPairs_app_inv _ _ _ Hdisj) as (_ & Hd2 & Hcross).
      (* L is a single block; read it as the one-leaf row so that
         [non_interfering_lseq] applies *)
      assert (HniL : non_interfering (lseq d1) (lseq (leaf L))).
      { apply non_interfering_lseq. intros D1 D2 HD1 HD2.
        cbn [row_leaves] in HD2. destruct HD2 as [HD2 | []]; subst D2.
        apply Hcross; [exact HD1 |].
        apply (leaf_at_In _ p').
        destruct (leaf_at d2 p') as [D |] eqn:Ed; [| congruence].
        apply (leaf_at_set_same d2 p' D L Ed). }
      cbn [lseq] in HniL.
      eapply Permutation_trans; [apply (IH2 p' L _ Hsome Hd2) |].
      apply denote_perm.
      apply (denote_comm Hloc _ _ (non_interfering_sym _ _ HniL)).
  Qed.

  (** [dk_block] sees a step exactly as the new residual. *)
  Lemma dk_block_advance : forall T R' K,
      dk_block T (advance R' K T) = residual_lblock R'.
  Proof.
    intros T [| L'] [| a K0]; cbn [advance].
    - unfold dk_block; rewrite beforeb_self; reflexivity.
    - unfold dk_block; rewrite beforeb_phase; reflexivity.
    - unfold dk_block; rewrite beforeb_phase; reflexivity.
    - unfold dk_block; rewrite beforeb_phase; reflexivity.
  Qed.

  Lemma dk_block_phase : forall T R K,
      dk_block T (phase R K T) = residual_lblock R.
  Proof. intros; unfold dk_block; rewrite beforeb_phase; reflexivity. Qed.

  Lemma nblocks_set : forall t P p T S',
      same_shape t P ->
      leaf_at t p = Some T ->
      nblocks t (set_at P p S') = set_at (nblocks t P) p (dk_block T S').
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S' Hsh Ht;
      cbn in Hsh, Ht; try contradiction; try discriminate.
    - injection Ht as HT; subst.
      unfold nblocks; cbn [row_zip set_at]. reflexivity.
    - destruct Hsh as [Hs1 _]. unfold nblocks in *; cbn [row_zip set_at].
      rewrite (IH1 P1 p' T S' Hs1 Ht). reflexivity.
    - destruct Hsh as [_ Hs2]. unfold nblocks in *; cbn [row_zip set_at].
      rewrite (IH2 P2 p' T S' Hs2 Ht). reflexivity.
  Qed.

  Lemma nblocks_leaf_at : forall t P p T S,
      same_shape t P ->
      leaf_at t p = Some T ->
      leaf_at P p = Some S ->
      leaf_at (nblocks t P) p = Some (dk_block T S).
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S Hsh Ht Hp;
      cbn in Hsh, Ht, Hp; try contradiction; try discriminate.
    - injection Ht as HT; injection Hp as HS; subst.
      unfold nblocks; cbn [row_zip leaf_at]. reflexivity.
    - destruct Hsh as [Hs1 _]. unfold nblocks; cbn [row_zip leaf_at].
      apply (IH1 P1 p' T S Hs1 Ht Hp).
    - destruct Hsh as [_ Hs2]. unfold nblocks; cbn [row_zip leaf_at].
      apply (IH2 P2 p' T S Hs2 Ht Hp).
  Qed.

  Lemma denote_residual : forall R E,
      denote (residual_lblock R) E = residual_denote R E.
  Proof. intros [| L] E; reflexivity. Qed.

  Lemma set_at_same : forall {A} (r : row A) p a,
      leaf_at r p = Some a -> set_at r p a = r.
  Proof.
    intros A r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] a H;
      cbn in *; try discriminate.
    - injection H as Hx; subst; reflexivity.
    - rewrite (IH1 _ _ H); reflexivity.
    - rewrite (IH2 _ _ H); reflexivity.
  Qed.

  (** THE absorption lemma: after [lseq_pull] every branch shares the same
      tail sequence, so the branches collapse back into one [denote]. *)
  Lemma norm_absorb_d : local_ops ->
    forall t P p T R K E Gl,
      same_shape t P ->
      leaf_at t p = Some T ->
      leaf_at P p = Some (phase R K T) ->
      (forall R', lrow_disj (set_at (nblocks t P) p (residual_lblock R'))) ->
      Σ ⊳ ‹ residual_lblock R, E › →ₗ Gl ->
      Permutation
        (flat_map
           (fun c => denote (nlseq t (set_at P p (advance (fst c) K T)))
                       (snd c)) Gl)
        (denote (nlseq t P) E).
  Proof.
    intros Hloc t P p T R K E Gl Hsh Ht Hp HdisjR Hstep.
    assert (Hnb : leaf_at (nblocks t P) p = Some (residual_lblock R)).
    { rewrite (nblocks_leaf_at t P p T _ Hsh Ht Hp), dk_block_phase.
      reflexivity. }
    assert (Hsome : leaf_at (nblocks t P) p <> None) by congruence.
    unfold nlseq.
    erewrite flat_map_ext' with
      (g := fun c => denote
              (lseq (set_at (nblocks t P) p (residual_lblock (fst c))))
              (snd c)).
    2:{ intros [R' E']; cbn [fst snd].
        rewrite (nblocks_set t P p T _ Hsh Ht), dk_block_advance.
        reflexivity. }
    eapply Permutation_trans with
      (l' := flat_map
               (fun c => denote (lseq (set_at (nblocks t P) p l_skip))
                           (denote (residual_lblock (fst c)) (snd c))) Gl).
    { apply Permutation_flat_map_in. intros [R' E'] _; cbn [fst snd].
      apply (lseq_pull Hloc _ p _ _ Hsome (HdisjR R')). }
    eapply Permutation_trans; [apply denote_flat_map_gen |].
    erewrite flat_map_ext' with (g := fun c => residual_denote (fst c) (snd c))
      by (intros [R' E']; apply denote_residual).
    eapply Permutation_trans;
      [apply denote_perm, (local_step_denote _ _ _ Hstep) |].
    apply Permutation_sym.
    pose proof (lseq_pull Hloc (nblocks t P) p (residual_lblock R) E Hsome
                  (HdisjR R)) as Hpull.
    rewrite (set_at_same _ p _ Hnb) in Hpull.
    exact Hpull.
  Qed.

  (** ** 11b. The steps that pass THROUGH the normalisation.

      A rendezvous acts on a leaf whose residual is already ↓, so it removes
      no D part and [nblocks] does not move; [ndrop] simply takes the same
      step.  [stage_ok] is what makes this uniform in whether the leaf has
      already fallen through — without it a leaf could fall into a tail that
      happens to be [phase _ _ T] and count as [before T] all over again. *)

  (** A leaf is in a LEGAL stage relative to its original tail T when it is
      either still before T, or has already fallen through — in which case it
      is strictly smaller.  The second disjunct is what rules out a leaf
      falling into a tail that happens to be [phase _ _ T] and thereby
      becoming [before T] all over again. *)
  Definition stage_ok (T S : process) : Prop :=
    before T S \/ (proc_size S <= proc_size T)%nat.

  Lemma small_not_beforeb : forall T S,
      (proc_size S <= proc_size T)%nat -> beforeb T S = false.
  Proof.
    intros T S H; destruct (beforeb T S) eqn:E; [| reflexivity].
    exfalso; apply beforeb_spec, before_size in E.
    rewrite E in H. apply (Nat.nle_succ_diag_l _ H).
  Qed.

  (** A leaf whose residual is ↓ contributes no D part, before or after the
      rendezvous. *)
  Lemma dk_block_rdv : forall T K T',
      stage_ok T (phase r_done K T') ->
      dk_block T (phase r_done K T') = l_skip.
  Proof.
    intros T K T' [Hb | Hs].
    - destruct Hb as (R0 & K1 & Heq); injection Heq as _ _ HT; subst T.
      unfold dk_block; rewrite beforeb_phase; reflexivity.
    - unfold dk_block; rewrite (small_not_beforeb _ _ Hs); reflexivity.
  Qed.

  Lemma dk_block_rdv_after : forall T K K' T',
      stage_ok T (phase r_done K T') ->
      dk_block T (advance r_done K' T') = l_skip.
  Proof.
    intros T K K' T' Hst.
    destruct K' as [| a K0]; cbn [advance].
    - unfold dk_block.
      destruct Hst as [Hb | Hs].
      + destruct Hb as (R0 & K1 & Heq); injection Heq as _ _ HT; subst T.
        rewrite beforeb_self; reflexivity.
      + cbn [proc_size] in Hs.
        rewrite (small_not_beforeb T T') by
            (apply Nat.le_trans with (m := proc_size (phase r_done K T'));
             [cbn; apply Nat.le_succ_diag_r | exact Hs]).
        reflexivity.
    - unfold dk_block.
      destruct Hst as [Hb | Hs].
      + destruct Hb as (R0 & K1 & Heq); injection Heq as _ _ HT; subst T.
        rewrite beforeb_phase; reflexivity.
      + rewrite (small_not_beforeb T (phase r_done (a :: K0) T'))
          by (cbn [proc_size] in *; exact Hs).
        reflexivity.
  Qed.

  (** …and [ndrop] takes the very same step. *)
  Lemma dk_drop_rdv : forall T K T',
      K <> nil -> dk_drop T (phase r_done K T') = phase r_done K T'.
  Proof.
    intros T [| a K0] T' Hne; [contradiction |].
    unfold dk_drop; destruct (beforeb T (phase r_done (a :: K0) T')) eqn:Eb;
      [| reflexivity].
    cbn [advance]. reflexivity.
  Qed.

  Lemma dk_drop_rdv_after : forall T K K' T',
      stage_ok T (phase r_done K T') ->
      dk_drop T (advance r_done K' T') = advance r_done K' T'.
  Proof.
    intros T K K' T' Hst.
    destruct K' as [| a K0]; cbn [advance]; [| apply dk_drop_rdv; discriminate].
    unfold dk_drop.
    destruct Hst as [Hb | Hs].
    - destruct Hb as (R0 & K1 & Heq); injection Heq as _ _ HT; subst T.
      rewrite beforeb_self; reflexivity.
    - cbn [proc_size] in Hs.
      rewrite (small_not_beforeb T T') by
          (apply Nat.le_trans with (m := proc_size (phase r_done K T'));
           [cbn; apply Nat.le_succ_diag_r | exact Hs]).
      reflexivity.
  Qed.

  (** [denote] commutes with a rendezvous, the same three classical checks as
      [local_step_rmap] but stated for the denotation. *)
  Lemma denote_rmap : forall L x e E,
      rdv_indep L x e -> denote L (rmap x e E) = rmap x e (denote L E).
  Proof.
    intro L;
      induction L as [| y e' | q | U qs | y M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intros x e E Hind; cbn [denote].
    - reflexivity.
    - destruct Hind as (Hr & Hc & Hd);
        cbn [lblock_read lblock_change] in Hr, Hc, Hd.
      unfold rmap; rewrite !map_map; apply map_ext; intros [s r]; cbn.
      f_equal. apply rendezvous_store_comm.
      + intro; subst y; apply Hc; left; reflexivity.
      + exact Hr.
      + intro Hy; apply (Hd y); [left; reflexivity | exact Hy].
    - unfold rmap; rewrite !map_map; apply map_ext; intros [s r]; reflexivity.
    - unfold rmap; rewrite !map_map; apply map_ext; intros [s r]; reflexivity.
    - destruct Hind as (Hr & Hc & Hd);
        cbn [lblock_read lblock_change] in Hr, Hc, Hd.
      unfold rmap; rewrite flat_map_map, map_flat_map.
      apply flat_map_ext'; intros [s r]; rewrite map_map.
      apply map_ext; intro m; cbn. f_equal.
      rewrite (eval_expr_update_notin _ _ y m e)
        by (intro Hy; apply (Hd y); [left; reflexivity | exact Hy]).
      apply store_update_comm.
      intro; subst y; apply Hc; left; reflexivity.
    - destruct (rdv_indep_seq _ _ _ _ Hind) as (H1 & H2).
      rewrite (IH1 _ _ _ H1), (IH2 _ _ _ H2). reflexivity.
    - destruct (rdv_indep_if _ _ _ _ _ Hind) as (H1 & H0 & Hb).
      assert (Hf : forall p : bexpr,
                 ~ In x (bexpr_vars p) ->
                 ensemble_filter
                   (fun s => eval_bool (i_fn Σ) (i_rl Σ) s p) (rmap x e E)
                 = rmap x e
                     (ensemble_filter
                        (fun s => eval_bool (i_fn Σ) (i_rl Σ) s p) E)).
      { intros p Hp. unfold ensemble_filter, rmap.
        rewrite filter_map_comm. f_equal.
        apply filter_ext; intros [s r]; cbn.
        apply eval_bool_update_notin, Hp. }
      (* the negated guard is only CONVERTIBLE to [b_not b], and rewrite
         matches syntactically, so it needs its own instance *)
      assert (Hfn : ensemble_filter
                      (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b))
                      (rmap x e E)
                    = rmap x e
                        (ensemble_filter
                           (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E)).
      { unfold ensemble_filter, rmap.
        rewrite filter_map_comm. f_equal.
        apply filter_ext; intros [s r]; cbn.
        rewrite eval_bool_update_notin by exact Hb. reflexivity. }
      rewrite (Hf b Hb), Hfn.
      rewrite (IH1 _ _ _ H1), (IH0 _ _ _ H0).
      unfold rmap; rewrite map_app. reflexivity.
  Qed.

  (** ** 11c. Transporting a step to another ensemble.

      [distri_step] picks its rule without ever looking at the ensemble: a
      local step needs a leaf with a residual, a rendezvous needs two matching
      endpoints, and neither is a property of E.  So a step available over one
      ensemble is available over any other, with the same residual shape --
      and the two together are exactly the step over the union.

      This is what lets the several components a branching d-step produces be
      simulated by the single component holding their union, which is what the
      normalisation needs in order to absorb that step. *)

  Lemma distri_step_transfer : forall P Ea Ga,
      Σ ⊳ ‹ P, Ea › ⇝ Ga ->
      forall Eb, exists Gb,
        Σ ⊳ ‹ P, Eb › ⇝ Gb
        /\ map fst Ga = map fst Gb
        /\ Σ ⊳ ‹ P, Ea ++ Eb › ⇝ cfg_zip Ga Gb.
  Proof.
    intros P Ea Ga H; induction H as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 Gx Hs IH
      | P1 P2 E0 Gy Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ];
      intro Eb.
    - (* local: the same block steps over any ensemble *)
      destruct (local_step_total L Eb) as (Gl2 & Hl2).
      exists (map (fun c => (leaf (advance (fst c) K T), snd c)) Gl2).
      split; [apply ds_local, Hl2 | split].
      + rewrite !(map_fst_map (fun R => leaf (advance R K T))),
                (local_step_shape _ _ _ _ _ Hloc Hl2).
        reflexivity.
      + rewrite cfg_zip_map by (intros [| L'] E; reflexivity).
        apply ds_local, (local_step_app _ _ _ _ _ Hloc Hl2).
    - (* left subtree *)
      destruct (IH Eb) as (Gb & Hb & Hsh & Hab).
      exists (map (fun c => (fst c ∥ P2, snd c)) Gb).
      split; [apply ds_par_l, Hb | split].
      + rewrite !(map_fst_map (fun p => p ∥ P2)), Hsh; reflexivity.
      + rewrite cfg_zip_map by (intros a E; reflexivity).
        apply ds_par_l, Hab.
    - (* right subtree *)
      destruct (IH Eb) as (Gb & Hb & Hsh & Hab).
      exists (map (fun c => (P1 ∥ fst c, snd c)) Gb).
      split; [apply ds_par_r, Hb | split].
      + rewrite !(map_fst_map (fun p => P1 ∥ p)), Hsh; reflexivity.
      + rewrite cfg_zip_map by (intros a E; reflexivity).
        apply ds_par_r, Hab.
    - (* rendezvous: does not look at the ensemble at all *)
      eexists. split; [eapply ds_comm_lr; eassumption | split].
      + reflexivity.
      + cbn [cfg_zip]. rewrite <- map_app.
        eapply ds_comm_lr; eassumption.
    - eexists. split; [eapply ds_comm_rl; eassumption | split].
      + reflexivity.
      + cbn [cfg_zip]. rewrite <- map_app.
        eapply ds_comm_rl; eassumption.
  Qed.


(** ** 12. Par-Comp-MP — the cut, and what a phase does to an ensemble ****

    [nblocks]/[ndrop] read the D part off a leaf; the same [row_zip] reads
    the other two.  [cut] is then not a separate construction at all: it IS
    the triple ([nblocks], [nkrow], [tdrop]) taken at the tail it produces,
    which is what lets the normalisation start from a [cut] hypothesis.

    The second half is [kapply], the ensemble action of a whole communication
    phase: a rendezvous is x := e, so a phase is a list of substitutions, and
    [wf_phase] says they are pairwise independent — hence order-free.  Written
    as a [fold_left] over that list, consuming one matched pair peels exactly
    one [rmap] off the front ([kapply_step]), which is how the normalisation
    absorbs a k-step.
*********************************************************************)

  (** ** The other two components of a leaf *)

  Definition dk_kblock (T S : process) : cblock :=
    if beforeb T S
    then match S with phase _ K _ => K | terminated => nil end
    else nil.

  Definition dk_tail (T S : process) : process :=
    if beforeb T S
    then match S with phase _ _ T' => T' | terminated => S end
    else S.

  Definition nkrow (t P : program) : krow    := row_zip nil dk_kblock t P.
  Definition tdrop (t P : program) : program := row_zip terminated dk_tail t P.

  (** ** The cut IS the triple of maps *)

  Lemma cut_shape : forall P d k t, cut P = (d, k, t) -> same_shape t P.
  Proof.
    induction P as [S | P1 IH1 P2 IH2]; intros d k t Hcut.
    - destruct S as [| R K T]; cbn in Hcut; injection Hcut as _ _ Ht; subst t;
        exact Logic.I.
    - cbn in Hcut.
      destruct (cut P1) as [[d1 k1] t1] eqn:E1.
      destruct (cut P2) as [[d2 k2] t2] eqn:E2.
      injection Hcut as _ _ Ht; subst t; cbn.
      split; [apply (IH1 d1 k1 t1 eq_refl) | apply (IH2 d2 k2 t2 eq_refl)].
  Qed.

  Lemma cut_nblocks : forall P d k t, cut P = (d, k, t) -> nblocks t P = d.
  Proof.
    induction P as [S | P1 IH1 P2 IH2]; intros d k t Hcut.
    - destruct S as [| R K T]; cbn in Hcut; injection Hcut as Hd _ Ht;
        subst d t; unfold nblocks; cbn [row_zip].
      + unfold dk_block; rewrite beforeb_self; reflexivity.
      + rewrite dk_block_phase; reflexivity.
    - cbn in Hcut.
      destruct (cut P1) as [[d1 k1] t1] eqn:E1.
      destruct (cut P2) as [[d2 k2] t2] eqn:E2.
      injection Hcut as Hd _ Ht; subst d t.
      unfold nblocks in *; cbn [row_zip].
      rewrite (IH1 d1 k1 t1 eq_refl), (IH2 d2 k2 t2 eq_refl); reflexivity.
  Qed.

  Lemma cut_nkrow : forall P d k t, cut P = (d, k, t) -> nkrow t P = k.
  Proof.
    induction P as [S | P1 IH1 P2 IH2]; intros d k t Hcut.
    - destruct S as [| R K T]; cbn in Hcut; injection Hcut as _ Hk Ht;
        subst k t; unfold nkrow; cbn [row_zip]; unfold dk_kblock.
      + rewrite beforeb_self; reflexivity.
      + rewrite beforeb_phase; reflexivity.
    - cbn in Hcut.
      destruct (cut P1) as [[d1 k1] t1] eqn:E1.
      destruct (cut P2) as [[d2 k2] t2] eqn:E2.
      injection Hcut as _ Hk Ht; subst k t.
      unfold nkrow in *; cbn [row_zip].
      rewrite (IH1 d1 k1 t1 eq_refl), (IH2 d2 k2 t2 eq_refl); reflexivity.
  Qed.

  Lemma cut_tdrop : forall P d k t, cut P = (d, k, t) -> tdrop t P = t.
  Proof.
    induction P as [S | P1 IH1 P2 IH2]; intros d k t Hcut.
    - destruct S as [| R K T]; cbn in Hcut; injection Hcut as _ _ Ht;
        subst t; unfold tdrop; cbn [row_zip]; unfold dk_tail.
      + rewrite beforeb_self; reflexivity.
      + rewrite beforeb_phase; reflexivity.
    - cbn in Hcut.
      destruct (cut P1) as [[d1 k1] t1] eqn:E1.
      destruct (cut P2) as [[d2 k2] t2] eqn:E2.
      injection Hcut as _ _ Ht; subst t.
      unfold tdrop in *; cbn [row_zip].
      rewrite (IH1 d1 k1 t1 eq_refl), (IH2 d2 k2 t2 eq_refl); reflexivity.
  Qed.

  (** ** The substitution a phase performs, as a list *)

  Definition send_of (k : krow) (c : chan) : expr :=
    match filter is_send (krow_endpoints k c) with
    | c_send _ e :: _ => e
    | _               => e_val O
    end.

  Definition subst_of (k : krow) (a : caction) : list (var * expr) :=
    match a with
    | c_recv c x  => (x, send_of k c) :: nil
    | c_send _ _  => nil
    end.

  Definition ksubst (k : krow) : list (var * expr) :=
    flat_map (subst_of k) (krow_actions k).

  Definition frm (E : ensemble dim) (p : var * expr) : ensemble dim :=
    rmap (fst p) (snd p) E.

  Definition kapply (k : krow) (E : ensemble dim) : ensemble dim :=
    fold_left frm (ksubst k) E.

  (** ** Picking removes an occurrence, in place — [kpick_perm] up to order
         is not enough here: [send_of] reads the FIRST endpoint, so the two
         action lists have to line up on the nose. *)

  Lemma picks_split : forall K a K',
      K ∋ a □ K' -> exists l1 l2, K = l1 ++ a :: l2 /\ K' = l1 ++ l2.
  Proof.
    intros K a K' H; induction H as [a K | a b K K' H IH].
    - exists nil, K. split; reflexivity.
    - destruct IH as (l1 & l2 & H1 & H2).
      exists (b :: l1), l2. split; cbn; congruence.
  Qed.

  Lemma kpick_split : forall k a k',
      k ∋ₖ a □ k' ->
      exists l1 l2,
        krow_actions k = l1 ++ a :: l2 /\ krow_actions k' = l1 ++ l2.
  Proof.
    intros k a k' H;
      induction H as [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH].
    - destruct (picks_split _ _ _ Hp) as (l1 & l2 & H1 & H2).
      exists l1, l2. rewrite !krow_actions_leaf. split; assumption.
    - destruct IH as (l1 & l2 & H1 & H2).
      exists l1, (l2 ++ krow_actions k2).
      rewrite !krow_actions_par, H1, H2, <- !app_assoc. split; reflexivity.
    - destruct IH as (l1 & l2 & H1 & H2).
      exists (krow_actions k1 ++ l1), l2.
      rewrite !krow_actions_par, H1, H2, <- !app_assoc. split; reflexivity.
  Qed.

  (** ** Pulling one substitution to the front of the fold *)

  Definition rpair_indep (p q : var * expr) : Prop :=
    fst p <> fst q
    /\ ~ In (fst p) (expr_vars (snd q))
    /\ ~ In (fst q) (expr_vars (snd p)).

  Lemma frm_swap : forall p q E,
      rpair_indep p q -> frm (frm E p) q = frm (frm E q) p.
  Proof.
    intros [x1 e1] [x2 e2] E (H1 & H2 & H3); cbn in *.
    unfold frm; cbn [fst snd]. apply rmap_comm; assumption.
  Qed.

  Lemma fold_rmap_pull : forall l1 p l2 E,
      (forall q, In q l1 -> rpair_indep p q) ->
      fold_left frm (l1 ++ p :: l2) E = fold_left frm (p :: l1 ++ l2) E.
  Proof.
    intro l1; induction l1 as [| q l1 IH]; intros p l2 E Hind; [reflexivity |].
    cbn [app fold_left].
    rewrite (IH p l2 (frm E q))
      by (intros r Hr; apply Hind; right; exact Hr).
    cbn [fold_left].
    rewrite (frm_swap p q E (Hind q (or_introl eq_refl))).
    reflexivity.
  Qed.

  (** ** An exhausted phase does nothing *)

  Lemma krow_actions_eps : forall k,
      row_all (fun K => K = ε) k -> krow_actions k = nil.
  Proof.
    intro k; induction k as [K | k1 IH1 k2 IH2]; cbn [row_all]; intro H.
    - rewrite krow_actions_leaf; exact H.
    - destruct H as [H1 H2].
      rewrite krow_actions_par, (IH1 H1), (IH2 H2); reflexivity.
  Qed.

  Lemma kapply_done : forall k E,
      row_all (fun K => K = ε) k -> kapply k E = E.
  Proof.
    intros k E H; unfold kapply, ksubst.
    rewrite (krow_actions_eps k H); reflexivity.
  Qed.

  (** ** Footprint of the substitution list *)

  Lemma send_of_read : forall k c,
      incl (expr_vars (send_of k c)) (phase_oread k).
  Proof.
    intros k c. unfold send_of.
    destruct (filter is_send (krow_endpoints k c)) as [| a l] eqn:Ef;
      [apply incl_nil_l |].
    destruct a as [c0 e0 | c0 x0]; [| apply incl_nil_l].
    assert (Hin : In (c_send c0 e0) (krow_actions k)).
    { assert (H1 : In (c_send c0 e0) (filter is_send (krow_endpoints k c)))
        by (rewrite Ef; left; reflexivity).
      apply filter_In in H1 as [H1 _].
      unfold krow_endpoints in H1; apply filter_In in H1 as [H1 _]; exact H1. }
    unfold phase_oread. intros y Hy.
    apply in_flat_map. exists (c_send c0 e0). split; [exact Hin | exact Hy].
  Qed.

  Lemma ksubst_in_recv : forall k p,
      In p (ksubst k) ->
      exists c, In (c_recv c (fst p)) (krow_actions k) /\ snd p = send_of k c.
  Proof.
    intros k p Hin. unfold ksubst in Hin.
    apply in_flat_map in Hin as (a & Ha & Hp).
    destruct a as [c0 e0 | c0 x0]; cbn in Hp; [contradiction |].
    destruct Hp as [Hp | []]; subst p; cbn [fst snd].
    exists c0. split; [exact Ha | reflexivity].
  Qed.

  Lemma ksubst_fst_recv : forall k p,
      In p (ksubst k) -> In (fst p) (phase_recv k).
  Proof.
    intros k p Hin.
    destruct (ksubst_in_recv k p Hin) as (c & Hc & _).
    unfold phase_recv. apply in_flat_map.
    exists (c_recv c (fst p)). split; [exact Hc | left; reflexivity].
  Qed.

  Lemma ksubst_snd_read : forall k p,
      In p (ksubst k) -> incl (expr_vars (snd p)) (phase_oread k).
  Proof.
    intros k p Hin.
    destruct (ksubst_in_recv k p Hin) as (c & _ & Hs).
    rewrite Hs. apply send_of_read.
  Qed.

  (** ** [kapply], one matched pair at a time *)

  Lemma perm_length_1_eq : forall {A} (l1 l2 : list A),
      Permutation l1 l2 -> length l1 = 1%nat -> l1 = l2.
  Proof.
    intros A [| a [| b l]] l2 Hp Hl; cbn in Hl; try discriminate.
    symmetry; apply Permutation_length_1_inv; exact Hp.
  Qed.

  Lemma flat_map_ext_in : forall {A B} (f g : A -> list B) (l : list A),
      (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
  Proof.
    intros A B f g l; induction l as [| a l IH]; cbn [flat_map]; intro H;
      [reflexivity |].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity |].
    intros b Hb; apply H; right; exact Hb.
  Qed.

  (** Off the picked channel the send endpoint is untouched — and, being
      unique, untouched on the nose rather than up to permutation. *)
  Lemma send_of_kpair_other : forall k c e x k' c',
      wf_kchannels k -> kpair k c e x k' -> In c' (krow_chan k) -> c' <> c ->
      send_of k c' = send_of k' c'.
  Proof.
    intros k c e x k' c' Hwf (kmid & Hs & Hr) Hin Hne.
    assert (Hp : Permutation (krow_endpoints k c') (krow_endpoints k' c')).
    { eapply Permutation_trans.
      - apply (kpick_endpoints_other _ _ _ _ Hs); cbn [caction_chan];
          intro H; apply Hne; symmetry; exact H.
      - apply (kpick_endpoints_other _ _ _ _ Hr); cbn [caction_chan];
          intro H; apply Hne; symmetry; exact H. }
    assert (Hf : filter is_send (krow_endpoints k c')
                 = filter is_send (krow_endpoints k' c')).
    { apply perm_length_1_eq; [apply permutation_filter, Hp |].
      destruct (Hwf c' Hin) as (H1 & _ & _); exact H1. }
    unfold send_of; rewrite Hf; reflexivity.
  Qed.

  (** The picked channel is spent: neither endpoint survives. *)
  Lemma kpair_chan_spent : forall k c e x k',
      wf_kchannels k -> In c (krow_chan k) -> kpair k c e x k' ->
      krow_endpoints k' c = nil.
  Proof.
    intros k c e x k' Hwf Hin (kmid & Hs & Hr).
    pose proof (krow_endpoints_perm _ _ _ c Hs eq_refl) as P1.
    pose proof (krow_endpoints_perm _ _ _ c Hr eq_refl) as P2.
    assert (Hp : Permutation (krow_endpoints k c)
                   (c_send c e :: c_recv c x :: krow_endpoints k' c))
      by (eapply Permutation_trans; [exact P1 | apply perm_skip, P2]).
    apply Permutation_length in Hp.
    pose proof (wf_kchannels_chan_pair _ _ Hwf Hin) as [Hlen _].
    rewrite Hlen in Hp; cbn in Hp.
    destruct (krow_endpoints k' c); [reflexivity | cbn in Hp; lia].
  Qed.

  (** The send picked out of a well-formed phase IS the one the pair names. *)
  Lemma send_of_pick : forall k c e kmid,
      wf_kchannels k -> k ∋ₖ c_send c e □ kmid -> send_of k c = e.
  Proof.
    intros k c e kmid Hwf Hs.
    assert (Hin : In c (krow_chan k)).
    { apply (krow_endpoints_in_chan k c (c_send c e)).
      pose proof (krow_endpoints_perm _ _ _ c Hs eq_refl) as Hp.
      eapply Permutation_in; [apply Permutation_sym, Hp | left; reflexivity]. }
    assert (Hf : filter is_send (krow_endpoints k c) = c_send c e :: nil).
    { symmetry; apply perm_length_1_eq; [| reflexivity].
      apply Permutation_sym.
      eapply Permutation_trans.
      - apply permutation_filter, (krow_endpoints_perm _ _ _ c Hs eq_refl).
      - cbn [filter is_send]. apply perm_skip.
        assert (Hlen : length (filter is_send (krow_endpoints k c)) = 1%nat)
          by (destruct (Hwf c Hin) as (H1 & _ & _); exact H1).
        pose proof (Permutation_length
                      (permutation_filter _ is_send _ _
                         (krow_endpoints_perm _ _ _ c Hs eq_refl))) as HL.
        rewrite Hlen in HL; cbn [filter is_send] in HL.
        destruct (filter is_send (krow_endpoints kmid c));
          [apply Permutation_refl | cbn in HL; lia]. }
    unfold send_of; rewrite Hf; reflexivity.
  Qed.

  (** THE step lemma: consuming one matched pair peels one [rmap] off the
      front of the phase's action.  Everything the pair could have been
      scheduled after is independent of it, so it moves to the front. *)
  Lemma kapply_step : forall k c e x k' (E : ensemble dim),
      wf_phase k -> kpair k c e x k' ->
      kapply k E = kapply k' (rmap x e E).
  Proof.
    intros k c e x k' E Hwf Hpair.
    assert (Hpair' := Hpair). destruct Hpair' as (kmid & Hs & Hr).
    destruct Hwf as (Hch & Hnd & Hdj).
    pose proof (send_of_pick k c e kmid Hch Hs) as Hse.
    destruct (kpick_split _ _ _ Hs) as (A1 & A2 & HA & HAmid).
    destruct (kpick_split _ _ _ Hr) as (B1 & B2 & HB & HB').
    pose proof (kpair_actions_perm _ _ _ _ _ Hpair) as Qk.
    assert (Hsub : forall a, In a (krow_actions k') -> In a (krow_actions k)).
    { intros a Ha. eapply Permutation_in; [apply Permutation_sym, Qk |].
      right; right; exact Ha. }
    assert (HinC : In c (krow_chan k)).
    { apply (krow_endpoints_in_chan k c (c_send c e)).
      pose proof (krow_endpoints_perm _ _ _ c Hs eq_refl) as Hp.
      eapply Permutation_in; [apply Permutation_sym, Hp | left; reflexivity]. }
    pose proof (kpair_chan_spent k c e x k' Hch HinC Hpair) as Hspent.
    assert (Hext : forall a,
               In a (krow_actions k') -> subst_of k a = subst_of k' a).
    { intros [c0 e0 | c0 x0] Ha; [reflexivity |].
      cbn [subst_of].
      assert (Hne : c0 <> c).
      { intro; subst c0.
        assert (Hin' : In (c_recv c x0) (krow_endpoints k' c)).
        { unfold krow_endpoints; apply filter_In; split;
            [exact Ha | cbn [caction_chan]; apply Nat.eqb_refl]. }
        rewrite Hspent in Hin'; exact Hin'. }
      assert (Hin0 : In c0 (krow_chan k)).
      { rewrite krow_chan_actions. apply in_map_iff.
        exists (c_recv c0 x0). split; [reflexivity | apply Hsub, Ha]. }
      rewrite (send_of_kpair_other k c e x k' c0 Hch Hpair Hin0 Hne).
      reflexivity. }
    assert (HkS : ksubst k
                  = flat_map (subst_of k') B1 ++ (x, e)
                    :: flat_map (subst_of k') B2).
    { unfold ksubst. rewrite HA, flat_map_app; cbn [flat_map subst_of app].
      rewrite <- flat_map_app, <- HAmid, HB, flat_map_app.
      cbn [flat_map subst_of app]. rewrite Hse.
      rewrite (flat_map_ext_in (subst_of k) (subst_of k') B1)
        by (intros a Ha; apply Hext; rewrite HB';
            apply in_or_app; left; exact Ha).
      rewrite (flat_map_ext_in (subst_of k) (subst_of k') B2)
        by (intros a Ha; apply Hext; rewrite HB';
            apply in_or_app; right; exact Ha).
      reflexivity. }
    assert (HkS' : ksubst k'
                   = flat_map (subst_of k') B1 ++ flat_map (subst_of k') B2)
      by (unfold ksubst; rewrite HB', flat_map_app; reflexivity).
    assert (HR : Permutation (phase_recv k) (x :: phase_recv k')).
    { unfold phase_recv.
      eapply Permutation_trans;
        [exact (permutation_flat_map _ _ caction_change _ _ Qk) |].
      cbn [flat_map caction_change app]. apply Permutation_refl. }
    assert (HO : Permutation (phase_oread k) (expr_vars e ++ phase_oread k')).
    { unfold phase_oread.
      eapply Permutation_trans;
        [exact (permutation_flat_map _ _ caction_read _ _ Qk) |].
      cbn [flat_map caction_read app]. apply Permutation_refl. }
    assert (Hxnot : ~ In x (phase_recv k')).
    { assert (Hnd' : NoDup (x :: phase_recv k'))
        by (eapply Permutation_NoDup; [exact HR | exact Hnd]).
      inversion Hnd'; assumption. }
    assert (Hind : forall q, In q (flat_map (subst_of k') B1) ->
                             rpair_indep (x, e) q).
    { intros q Hq.
      assert (Hq' : In q (ksubst k'))
        by (rewrite HkS'; apply in_or_app; left; exact Hq).
      pose proof (ksubst_fst_recv k' q Hq') as Hfq.
      pose proof (ksubst_snd_read k' q Hq') as Hsq.
      assert (HxR : In x (phase_recv k))
        by (eapply Permutation_in;
            [apply Permutation_sym, HR | left; reflexivity]).
      assert (HfqR : In (fst q) (phase_recv k))
        by (eapply Permutation_in;
            [apply Permutation_sym, HR | right; exact Hfq]).
      split; [| split]; cbn [fst snd].
      - intro Heq; subst; contradiction.
      - intro Hin1. apply (Hdj x HxR).
        eapply Permutation_in; [apply Permutation_sym, HO |].
        apply in_or_app; right; apply Hsq, Hin1.
      - intro Hin1. apply (Hdj (fst q) HfqR).
        eapply Permutation_in; [apply Permutation_sym, HO |].
        apply in_or_app; left; exact Hin1. }
    unfold kapply. rewrite HkS, HkS'.
    rewrite (fold_rmap_pull _ (x, e) _ E Hind).
    reflexivity.
  Qed.

  (** ** …and what passes through a phase untouched *)

  Lemma fold_rmap_out : forall l p (E : ensemble dim),
      (forall q, In q l -> rpair_indep p q) ->
      fold_left frm l (frm E p) = frm (fold_left frm l E) p.
  Proof.
    intro l; induction l as [| q l IH]; intros p E Hind; [reflexivity |].
    cbn [fold_left].
    rewrite (frm_swap p q E (Hind q (or_introl eq_refl))).
    apply IH. intros r Hr; apply Hind; right; exact Hr.
  Qed.

  Lemma kapply_rmap : forall k y f (E : ensemble dim),
      ~ In y (phase_recv k) ->
      ~ In y (phase_oread k) ->
      disjoint (phase_recv k) (expr_vars f) ->
      kapply k (rmap y f E) = rmap y f (kapply k E).
  Proof.
    intros k y f E H1 H2 H3.
    change (rmap y f ?X) with (frm X (y, f)).
    unfold kapply. apply fold_rmap_out.
    intros q Hq. split; [| split]; cbn [fst snd].
    - intro Heq; apply H1; rewrite Heq; apply ksubst_fst_recv, Hq.
    - intro Hin; apply H2; apply (ksubst_snd_read k q Hq), Hin.
    - intro Hin; apply (H3 (fst q)); [apply ksubst_fst_recv, Hq | exact Hin].
  Qed.

  (** A local block independent of the whole phase takes the same step over
      the phase's image, branch by branch. *)
  Lemma local_step_kapply : forall l L (E : ensemble dim) Gl,
      (forall q, In q l -> rdv_indep L (fst q) (snd q)) ->
      Σ ⊳ ‹ L, E › →ₗ Gl ->
      Σ ⊳ ‹ L, fold_left frm l E › →ₗ
        map (fun c => (fst c, fold_left frm l (snd c))) Gl.
  Proof.
    intro l; induction l as [| q l IH]; intros L E Gl Hind Hstep;
      cbn [fold_left].
    - assert (Hm : forall G : local_config dim,
                 map (fun c => (fst c, snd c)) G = G).
      { intro G; induction G as [| [R E'] G IHG]; cbn;
          [reflexivity | rewrite IHG; reflexivity]. }
      rewrite Hm; exact Hstep.
    - pose proof (local_step_rmap L (fst q) (snd q) E Gl
                    (Hind q (or_introl eq_refl)) Hstep) as Hq.
      change (rmap (fst q) (snd q) E) with (frm E q) in Hq.
      pose proof (IH L (frm E q) _
                    (fun r Hr => Hind r (or_intror Hr)) Hq) as Hl.
      rewrite map_map in Hl; cbn [fst snd] in Hl.
      exact Hl.
  Qed.


(** ** 13. Par-Comp-MP — terminating runs of a whole configuration *********

    §8 splits a run along an appended ENSEMBLE; the normalisation needs the
    same along an appended CONFIGURATION, in both directions.  Splitting is
    §8's [splits] applied to the obvious matching; joining is "run one half,
    then the other", which is where the framing lemma comes in.

    [Term_cfg] is stated up to permutation of the collapse, not on the nose:
    the normalisation only ever reproduces a run's result up to permutation
    (paper Lemma 1 is a [Permutation]), and every consumer downstream —
    [total_degree_perm] — is permutation-invariant anyway.
*********************************************************************)

  (** A terminating run of a configuration, up to permutation on both the
      configuration and the collapse — which is what the normalisation
      produces, and all the degree bookkeeping needs. *)
  Definition Term_cfg (Gn : distri_config dim) (Efin : ensemble dim) : Prop :=
    exists G', step_star Σ (norm Gn) G'
            /\ terminal G' /\ Permutation (collapse G') Efin.

  Lemma Term_cfg_norm : forall Gn E, Term_cfg (norm Gn) E <-> Term_cfg Gn E.
  Proof. intros Gn E; unfold Term_cfg; rewrite norm_idem; reflexivity. Qed.

  Lemma Term_cfg_ens : forall Gn E E',
      Permutation E E' -> Term_cfg Gn E -> Term_cfg Gn E'.
  Proof.
    intros Gn E E' Hp (G & Hs & Ht & Hc); exists G.
    split; [exact Hs | split; [exact Ht | eapply Permutation_trans; eauto]].
  Qed.

  (** A run may be restarted from any permutation of its configuration: every
      step selects its component up to permutation anyway.  Only the
      zero-step case has to move, and there the collapse merely permutes. *)
  Lemma step_star_perm : forall G1 G' ,
      step_star Σ G1 G' -> terminal G' ->
      forall G2, Permutation G2 G1 ->
        exists G'', step_star Σ G2 G'' /\ terminal G''
                 /\ Permutation (collapse G'') (collapse G').
  Proof.
    intros G1 G' Hstar; induction Hstar as [G | Ga Gb Gc Hmix Hstar IH];
      intros Hterm G2 Hp.
    - exists G2. split; [apply star_refl | split].
      + unfold terminal in *; rewrite Forall_forall in *.
        intros c Hc; apply Hterm; eapply Permutation_in; eauto.
      + apply collapse_perm, Hp.
    - destruct (IH Hterm Gb (Permutation_refl _)) as (G'' & Hs & Ht & Hc).
      exists G''. split; [| split; assumption].
      eapply star_step; [| exact Hs].
      inversion Hmix as [Gx D E G0 G1x Hperm Hd Heq1 Heq2]; subst.
      apply (mixed_lift Σ G2 D E G0 G1x); [| exact Hd].
      eapply Permutation_trans; [exact Hp | exact Hperm].
  Qed.

  Lemma Term_cfg_perm : forall Gn Gn' E,
      Permutation Gn Gn' -> Term_cfg Gn E -> Term_cfg Gn' E.
  Proof.
    intros Gn Gn' E Hp (G & Hs & Ht & Hc).
    destruct (step_star_perm _ _ Hs Ht (norm Gn')
                (norm_perm _ _ (Permutation_sym Hp)))
      as (G'' & Hs' & Ht' & Hc').
    exists G''. split; [exact Hs' | split; [exact Ht' |]].
    eapply Permutation_trans; eauto.
  Qed.

  (** ** Framing: the components not being stepped just sit there *)

  Lemma step_star_frame_l : forall GA GA',
      step_star Σ GA GA' -> norm GA = GA ->
      forall GB, norm GB = GB -> step_star Σ (GA ++ GB) (GA' ++ GB).
  Proof.
    intros GA GA' Hstar; induction Hstar as [G | Ga Gb Gc Hmix Hstar IH];
      intros HnA GB HnB; [apply star_refl |].
    inversion Hmix as [Gx D E G0 G1 Hperm Hd Heq1 Heq2]; subst.
    eapply star_step.
    - apply (mixed_lift Σ (Ga ++ GB) D E (G0 ++ GB) G1); [| exact Hd].
      eapply Permutation_trans; [apply Permutation_app_tail, Hperm |].
      apply Permutation_refl.
    - rewrite app_assoc, norm_app, HnB.
      apply IH; [apply norm_idem | exact HnB].
  Qed.

  Lemma step_star_trans : forall G1 G2 G3,
      step_star Σ G1 G2 -> step_star Σ G2 G3 -> step_star Σ G1 G3.
  Proof.
    intros G1 G2 G3 H; induction H as [| Ga Gb Gc Hmix Hstar IH];
      [tauto | intro H3; eapply star_step; [exact Hmix | apply IH, H3]].
  Qed.

  (** There is no framing lemma for the RIGHT half: [mixed_step] renormalises
      the whole configuration, and [norm] of an append only splits into the
      same order, so stepping the right half in place lands on a PERMUTATION
      of the framed configuration.  Commuting the two halves and reusing
      [step_star_frame_l] is what [step_star_perm] is for. *)
  Lemma Term_cfg_join : forall GA EA GB EB,
      Term_cfg GA EA -> Term_cfg GB EB -> Term_cfg (GA ++ GB) (EA ++ EB).
  Proof.
    intros GA EA GB EB (A & HsA & HtA & HcA) (B & HsB & HtB & HcB).
    assert (HnA : norm A = A)
      by (eapply step_star_norm_free; [exact HsA | apply norm_idem]).
    pose proof (step_star_frame_l _ _ HsA (norm_idem _) (norm GB)
                  (norm_idem _)) as H1.
    pose proof (step_star_frame_l _ _ HsB (norm_idem _) A HnA) as H2.
    assert (Ht2 : terminal (B ++ A))
      by (unfold terminal; apply Forall_app; split; assumption).
    destruct (step_star_perm _ _ H2 Ht2 (A ++ norm GB)
                (Permutation_app_comm A (norm GB)))
      as (G'' & Hs'' & Ht'' & Hc'').
    exists G''. split; [| split; [exact Ht'' |]].
    - rewrite norm_app. eapply step_star_trans; [exact H1 | exact Hs''].
    - eapply Permutation_trans; [exact Hc'' |].
      unfold collapse; rewrite flat_map_app.
      eapply Permutation_trans; [apply Permutation_app_comm |].
      apply Permutation_app; assumption.
  Qed.

  (** ** …and the converse: a joined run splits *)

  Lemma norm_map_nil : forall (G : distri_config dim),
      norm (map (fun c => (fst c, @nil (cqstate dim))) G) = nil.
  Proof.
    intro G; induction G as [| [P E] G IH]; [reflexivity |].
    cbn [map norm filter fst snd]. exact IH.
  Qed.

  Lemma map_id_cfg : forall (G : distri_config dim),
      map (fun c => (fst c, snd c)) G = G.
  Proof.
    intro G; induction G as [| [P E] G IH]; cbn [map fst snd];
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma cfg_map_app_nil : forall (G : distri_config dim),
      map (fun c => (fst c, snd c ++ nil)) G = G.
  Proof.
    intro G; induction G as [| [P E] G IH]; cbn [map fst snd];
      [reflexivity | rewrite app_nil_r, IH; reflexivity].
  Qed.

  Lemma splits_app : forall (GA GB : distri_config dim),
      splits (GA ++ GB) GA GB.
  Proof.
    intros GA GB.
    exists (map (fun c => (fst c, (snd c, @nil (cqstate dim)))) GA
            ++ map (fun c => (fst c, (@nil (cqstate dim), snd c))) GB).
    split; [| split].
    - unfold mjoin; rewrite map_app, !map_map; cbn [fst snd app].
      rewrite cfg_map_app_nil, map_id_cfg. apply Permutation_refl.
    - unfold mleft; rewrite map_app, !map_map; cbn [fst snd].
      rewrite map_id_cfg, norm_app, norm_map_nil, app_nil_r.
      apply Permutation_refl.
    - unfold mright; rewrite map_app, !map_map; cbn [fst snd].
      rewrite map_id_cfg, norm_app, norm_map_nil; cbn [app].
      apply Permutation_refl.
  Qed.

  Lemma Term_cfg_split : forall (GA GB : distri_config dim) E,
      Term_cfg (GA ++ GB) E ->
      exists EA EB, Term_cfg GA EA /\ Term_cfg GB EB /\ Permutation E (EA ++ EB).
  Proof.
    intros GA GB E (G & Hs & Ht & Hc).
    assert (Hsp : splits (norm (GA ++ GB)) (norm GA) (norm GB)).
    { eapply splits_perm;
        [apply splits_app | | | ]; rewrite ?norm_app;
        apply Permutation_refl. }
    destruct (step_star_splits _ _ _ _ Hs Hsp) as (GA' & GB' & Hsp' & HA & HB).
    exists (collapse GA'), (collapse GB'). split; [| split].
    - exists GA'. split; [exact HA | split].
      + eapply splits_terminal; [exact Hsp' | exact Ht |].
        eapply step_star_norm_free; [exact HA | apply norm_idem].
      + apply Permutation_refl.
    - exists GB'. split; [exact HB | split].
      + eapply splits_terminal_right; [exact Hsp' | exact Ht |].
        eapply step_star_norm_free; [exact HB | apply norm_idem].
      + apply Permutation_refl.
    - eapply Permutation_trans; [apply Permutation_sym, Hc |].
      apply splits_collapse, Hsp'.
  Qed.


(** ** 14. Par-Comp-MP — the run of a communication phase ******************

    The middle stage of the cut, as a relation rather than a function: with
    only [wf_program] in hand there is no [wf_phase] on the displayed phase as
    such, so
    the matched pairs are not determined by their channel and "the ensemble
    the phase produces" is not a function of the phase.  [krun] carries the
    schedule the ORIGINAL run happened to take.

    Each step carries its pair twice: as [kpair] (row-level, for the
    footprints, which is what lets a t-stage step commute past the phase) and
    as the step it induces on [kprog] over an ARBITRARY ensemble (which is
    what [krun_Term] replays).  The second does not follow from the first
    without [chan_pair] — two [kpick]s may land in the same leaf — but the
    normalisation always has it, since the rendezvous it is transcribing came
    with two distinct positions.
*********************************************************************)

  (** A run of the phase: each step is a matched pair, carried BOTH as the
      row-level selection (for the footprints) and as the step it induces on
      [kprog] over an arbitrary ensemble (for the run it builds).  The second
      is what the normalisation has in hand — [ps <> pr] from the original
      program's rendezvous — and it is not derivable from the first without
      [chan_pair], which is not what the normalisation has in hand. *)
  Inductive krun : krow -> ensemble dim -> ensemble dim -> Prop :=
  | krun_nil : forall k E,
      row_all (fun K => K = ε) k -> krun k E E
  | krun_cons : forall k c e x k' E E',
      kpair k c e x k' ->
      (forall E0, Σ ⊳ ‹ kprog k, E0 › ⇝ {|| kprog k', rmap x e E0 ||}) ->
      krun k' (rmap x e E) E' ->
      krun k E E'.

  (** ** Footprints along a run *)

  Lemma kpair_recv : forall k c e x k',
      kpair k c e x k' ->
      In x (phase_recv k) /\ incl (phase_recv k') (phase_recv k).
  Proof.
    intros k c e x k' Hp.
    pose proof (kpair_actions_perm _ _ _ _ _ Hp) as Q.
    assert (HR : Permutation (phase_recv k) (x :: phase_recv k')).
    { unfold phase_recv.
      eapply Permutation_trans;
        [exact (permutation_flat_map _ _ caction_change _ _ Q) |].
      cbn [flat_map caction_change app]. apply Permutation_refl. }
    split.
    - eapply Permutation_in; [apply Permutation_sym, HR | left; reflexivity].
    - intros y Hy. eapply Permutation_in;
        [apply Permutation_sym, HR | right; exact Hy].
  Qed.

  Lemma kpair_oread : forall k c e x k',
      kpair k c e x k' ->
      incl (expr_vars e) (phase_oread k) /\
      incl (phase_oread k') (phase_oread k).
  Proof.
    intros k c e x k' Hp.
    pose proof (kpair_actions_perm _ _ _ _ _ Hp) as Q.
    assert (HO : Permutation (phase_oread k)
                   (expr_vars e ++ phase_oread k')).
    { unfold phase_oread.
      eapply Permutation_trans;
        [exact (permutation_flat_map _ _ caction_read _ _ Q) |].
      cbn [flat_map caction_read app]. apply Permutation_refl. }
    split; intros y Hy; eapply Permutation_in;
      [apply Permutation_sym, HO | | apply Permutation_sym, HO |];
      apply in_or_app; [left | right]; exact Hy.
  Qed.

  (** ** What has to miss a phase in order to pass through it *)

  Definition kindep (L : lblock) (k : krow) : Prop :=
    disjoint (lblock_read L) (phase_recv k)
    /\ disjoint (lblock_change L) (phase_recv k)
    /\ disjoint (lblock_change L) (phase_oread k).

  Lemma kindep_pair : forall L k c e x k',
      kindep L k -> kpair k c e x k' -> rdv_indep L x e /\ kindep L k'.
  Proof.
    intros L k c e x k' (H1 & H2 & H3) Hp.
    destruct (kpair_recv _ _ _ _ _ Hp) as (Hx & HRi).
    destruct (kpair_oread _ _ _ _ _ Hp) as (He & HOi).
    split.
    - split; [| split].
      + intro Hin; exact (H1 x Hin Hx).
      + intro Hin; exact (H2 x Hin Hx).
      + intros y Hy Hz; exact (H3 y Hy (He y Hz)).
    - split; [| split]; intros y Hy Hz.
      + exact (H1 y Hy (HRi y Hz)).
      + exact (H2 y Hy (HRi y Hz)).
      + exact (H3 y Hy (HOi y Hz)).
  Qed.

  Definition krdv_indep (y : var) (f : expr) (k : krow) : Prop :=
    ~ In y (phase_recv k)
    /\ ~ In y (phase_oread k)
    /\ disjoint (phase_recv k) (expr_vars f).

  Lemma krdv_indep_pair : forall y f k c e x k',
      krdv_indep y f k -> kpair k c e x k' ->
      (x <> y /\ ~ In x (expr_vars f) /\ ~ In y (expr_vars e))
      /\ krdv_indep y f k'.
  Proof.
    intros y f k c e x k' (H1 & H2 & H3) Hp.
    destruct (kpair_recv _ _ _ _ _ Hp) as (Hx & HRi).
    destruct (kpair_oread _ _ _ _ _ Hp) as (He & HOi).
    split.
    - split; [| split].
      + intro Heq; subst; contradiction.
      + intro Hin; exact (H3 x Hx Hin).
      + intro Hin; exact (H2 (He y Hin)).
    - split; [| split].
      + intro Hin; exact (H1 (HRi y Hin)).
      + intro Hin; exact (H2 (HOi y Hin)).
      + intros z Hz Hw; exact (H3 z (HRi z Hz) Hw).
  Qed.

  (** ** A run is a run *)

  Lemma kprog_eps_terminated : forall k,
      row_all (fun K => K = ε) k -> prog_terminated (kprog k).
  Proof.
    intro k; unfold prog_terminated, kprog;
      induction k as [K | k1 IH1 k2 IH2]; cbn [row_map row_all]; intro H.
    - rewrite H; reflexivity.
    - destruct H as [H1 H2]; split; [apply IH1, H1 | apply IH2, H2].
  Qed.

  Lemma krun_nil_ens : forall k E', krun k nil E' -> E' = nil.
  Proof.
    intros k E' H. remember (@nil (cqstate dim)) as E eqn:HE.
    induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH]; subst;
      [reflexivity | apply IH; unfold rmap; reflexivity].
  Qed.

  Lemma krun_Term : forall k E E',
      krun k E E' -> Term_cfg ({|| kprog k, E ||}) E'.
  Proof.
    intros k E E' H;
      induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH].
    - destruct E as [| st E0].
      + exists nil. split; [apply star_refl | split; [constructor |]].
        apply Permutation_refl.
      + exists ({|| kprog k, st :: E0 ||}).
        split; [apply star_refl | split].
        * constructor; [apply kprog_eps_terminated, Heps | constructor].
        * unfold collapse; cbn [flat_map snd]; rewrite app_nil_r.
          apply Permutation_refl.
    - destruct E as [| st E0].
      + rewrite (krun_nil_ens _ _ Hrun).
        exists nil. split; [apply star_refl | split;
          [constructor | apply Permutation_refl]].
      + destruct IH as (G & Hs & Ht & Hc). exists G.
        split; [| split; assumption].
        cbn [norm filter snd] in Hs |- *.
        eapply star_step; [| exact Hs].
        apply (mixed_lift Σ _ (kprog k) (st :: E0) nil _
                 (Permutation_refl _) (Hstep (st :: E0))).
  Qed.

  (** ** A run transports a permutation, an append, and a passing step *)

  Lemma krun_perm : forall k E E',
      krun k E E' -> forall E2, Permutation E E2 ->
      exists E2', krun k E2 E2' /\ Permutation E' E2'.
  Proof.
    intros k E E' H;
      induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH];
      intros E2 Hperm.
    - exists E2. split; [apply krun_nil, Heps | exact Hperm].
    - destruct (IH (rmap x e E2)
                  (Permutation_map _ Hperm)) as (E2' & Hr & Hp2).
      exists E2'. split; [| exact Hp2].
      eapply krun_cons; eassumption.
  Qed.

  Lemma krun_app : forall k E E',
      krun k E E' -> forall E1 E2, E = E1 ++ E2 ->
      exists E1' E2', krun k E1 E1' /\ krun k E2 E2' /\ E' = E1' ++ E2'.
  Proof.
    intros k E E' H;
      induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH];
      intros E1 E2 HE.
    - exists E1, E2. split; [apply krun_nil, Heps |
        split; [apply krun_nil, Heps | exact HE]].
    - subst E. unfold rmap in IH; rewrite map_app in IH.
      destruct (IH _ _ eq_refl) as (E1' & E2' & H1 & H2 & HE').
      exists E1', E2'. split; [| split; [| exact HE']];
        eapply krun_cons; eassumption.
  Qed.

  Lemma krun_rmap : forall k E E',
      krun k E E' -> forall y f, krdv_indep y f k ->
      krun k (rmap y f E) (rmap y f E').
  Proof.
    intros k E E' H;
      induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH];
      intros y f Hind.
    - apply krun_nil, Heps.
    - destruct (krdv_indep_pair _ _ _ _ _ _ _ Hind Hp)
        as ((Hxy & Hxf & Hye) & Hind').
      eapply krun_cons; [exact Hp | exact Hstep |].
      rewrite (rmap_comm y f x e E)
        by (try (intro Heq; apply Hxy; symmetry; exact Heq); assumption).
      apply IH, Hind'.
  Qed.

  Lemma Forall2_map_left : forall {A B C} (R : B -> C -> Prop) (f : A -> B) l1 l2,
      Forall2 R (map f l1) l2 -> Forall2 (fun a c => R (f a) c) l1 l2.
  Proof.
    intros A B C R f l1; induction l1 as [| a l1 IH]; intros l2 H;
      cbn [map] in H.
    - inversion H; constructor.
    - inversion H as [| u v l l' Hh Ht]; subst; constructor;
        [exact Hh | apply IH, Ht].
  Qed.

  Lemma krun_local_step : forall k Ed E2,
      krun k Ed E2 -> forall L, kindep L k ->
      forall Gl, Σ ⊳ ‹ L, Ed › →ₗ Gl ->
      exists Gl2, Σ ⊳ ‹ L, E2 › →ₗ Gl2
               /\ map fst Gl2 = map fst Gl
               /\ Forall2 (fun c c2 => krun k (snd c) (snd c2)) Gl Gl2.
  Proof.
    intros k Ed E2 H;
      induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH];
      intros L Hind Gl Hstepl.
    - exists Gl. split; [exact Hstepl | split; [reflexivity |]].
      clear Hstepl; induction Gl as [| c G IHG]; constructor;
        [apply krun_nil, Heps | exact IHG].
    - destruct (kindep_pair _ _ _ _ _ _ Hind Hp) as (Hrdv & Hind').
      pose proof (local_step_rmap L x e E Gl Hrdv Hstepl) as Hstep2.
      destruct (IH L Hind' _ Hstep2) as (Gl2 & Hs2 & Hm2 & Hf2).
      exists Gl2. split; [exact Hs2 | split].
      + rewrite Hm2, map_map; reflexivity.
      + apply Forall2_map_left in Hf2; cbn [fst snd] in Hf2.
        eapply Forall2_impl; [| exact Hf2].
        intros a b Hab. eapply krun_cons; eassumption.
  Qed.


(** ** 15. Par-Comp-MP — the leaf bookkeeping the normalisation runs on *****

    Two halves.  The first is the STAGE discipline: which of the three maps a
    leaf feeds into is decided by [beforeb] against its tail, and every step
    a leaf can take keeps that decision honest — a leaf still before its tail
    keeps the same K and tail whatever it does ([stage_before]), and one that
    has fallen through can never become [before] again, because it is
    strictly smaller ([stage_after]).

    The second is FOOTPRINTS.  Every independence side condition downstream
    has the same shape: the leaf being stepped contributes nothing to the map
    in question, so everything the map touches belongs to a different leaf,
    and [wf_ownership_paths] separates them.  [off_leaf] is that argument,
    once, generic in the leaf map; the four corollaries at the end are the
    instances the run transformation quotes.
*********************************************************************)

  (** ** Rows of the same shape, related leaf by leaf *)

  Fixpoint row_all2 {A B} (R : A -> B -> Prop) (r1 : row A) (r2 : row B) : Prop :=
    match r1, r2 with
    | leaf a,    leaf b    => R a b
    | par x1 y1, par x2 y2 => row_all2 R x1 x2 /\ row_all2 R y1 y2
    | _,         _         => False
    end.

  Lemma row_all2_shape : forall {A B} (R : A -> B -> Prop) r1 r2,
      row_all2 R r1 r2 -> same_shape r1 r2.
  Proof.
    intros A B R r1; induction r1 as [a | x IHx y IHy];
      intros [b | x2 y2] H; cbn in *; try contradiction; try exact Logic.I.
    destruct H; split; auto.
  Qed.

  Lemma row_all2_at : forall {A B} (R : A -> B -> Prop) r1 r2 p a b,
      row_all2 R r1 r2 -> leaf_at r1 p = Some a -> leaf_at r2 p = Some b -> R a b.
  Proof.
    intros A B R r1; induction r1 as [a0 | x IHx y IHy];
      intros [b0 | x2 y2] [| p' | p'] a b H H1 H2; cbn in *;
      try contradiction; try discriminate.
    - injection H1 as ->; injection H2 as ->; exact H.
    - destruct H as [H _]; exact (IHx _ _ _ _ H H1 H2).
    - destruct H as [_ H]; exact (IHy _ _ _ _ H H1 H2).
  Qed.

  Lemma row_all2_set : forall {A B} (R : A -> B -> Prop) r1 r2 p a b,
      row_all2 R r1 r2 -> leaf_at r1 p = Some a -> R a b ->
      row_all2 R r1 (set_at r2 p b).
  Proof.
    intros A B R r1; induction r1 as [a0 | x IHx y IHy];
      intros [b0 | x2 y2] [| p' | p'] a b H H1 H2; cbn in *;
      try contradiction; try discriminate; try exact H.
    - injection H1 as ->; exact H2.
    - destruct H as [Hx Hy]; split; [exact (IHx _ _ _ _ Hx H1 H2) | exact Hy].
    - destruct H as [Hx Hy]; split; [exact Hx | exact (IHy _ _ _ _ Hy H1 H2)].
  Qed.

  (** ** The stage discipline, leaf by leaf *)

  Lemma proc_size_advance : forall R K T,
      (proc_size (advance R K T) <= Datatypes.S (proc_size T))%nat.
  Proof. intros [| L] [| a K0] T; cbn [advance proc_size]; lia. Qed.

  (** A leaf still [before] its tail: whichever step it takes, the tail and the
      K part it exposes are unchanged, and it stays in a legal stage. *)
  Lemma stage_before : forall T K R',
      dk_tail T (advance R' K T) = T
      /\ dk_kblock T (advance R' K T) = K
      /\ stage_ok T (advance R' K T).
  Proof.
    intros T K R''; destruct R'' as [| L]; destruct K as [| a K0];
      cbn [advance]; unfold dk_tail, dk_kblock.
    - rewrite beforeb_self. split; [reflexivity | split; [reflexivity |]].
      right; apply Nat.le_refl.
    - rewrite beforeb_phase. split; [reflexivity | split; [reflexivity |]].
      left; eexists; eexists; reflexivity.
    - rewrite beforeb_phase. split; [reflexivity | split; [reflexivity |]].
      left; eexists; eexists; reflexivity.
    - rewrite beforeb_phase. split; [reflexivity | split; [reflexivity |]].
      left; eexists; eexists; reflexivity.
  Qed.

  Lemma dk_tail_phase : forall T R K, dk_tail T (phase R K T) = T.
  Proof. intros; unfold dk_tail; rewrite beforeb_phase; reflexivity. Qed.

  Lemma dk_kblock_phase : forall T R K, dk_kblock T (phase R K T) = K.
  Proof. intros; unfold dk_kblock; rewrite beforeb_phase; reflexivity. Qed.

  (** A leaf that has already fallen through: it is invisible to all three
      maps, and every step keeps it that way. *)
  Lemma stage_after : forall T R K T' R' K',
      stage_ok T (phase R K T') -> beforeb T (phase R K T') = false ->
      dk_tail T (advance R' K' T') = advance R' K' T'
      /\ dk_kblock T (advance R' K' T') = nil
      /\ dk_block T (advance R' K' T') = l_skip
      /\ stage_ok T (advance R' K' T').
  Proof.
    intros T R K T' R' K' Hst Hb.
    assert (Hle : (proc_size (phase R K T') <= proc_size T)%nat).
    { destruct Hst as [Hbef | Hle]; [| exact Hle].
      exfalso; rewrite (proj2 (beforeb_spec _ _) Hbef) in Hb; discriminate. }
    assert (Hle' : (proc_size (advance R' K' T') <= proc_size T)%nat).
    { eapply Nat.le_trans; [apply proc_size_advance |].
      cbn [proc_size] in Hle; exact Hle. }
    unfold dk_tail, dk_kblock, dk_block;
      rewrite !(small_not_beforeb _ _ Hle').
    split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
    right; exact Hle'.
  Qed.

  (** ** The three maps under a leaf rewrite *)

  Lemma nkrow_set : forall t P p T S',
      same_shape t P -> leaf_at t p = Some T ->
      nkrow t (set_at P p S') = set_at (nkrow t P) p (dk_kblock T S').
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S' Hsh Ht;
      cbn in Hsh, Ht; try contradiction; try discriminate.
    - injection Ht as ->; unfold nkrow; cbn [row_zip set_at]; reflexivity.
    - destruct Hsh as [Hs1 _]. unfold nkrow in *; cbn [row_zip set_at].
      rewrite (IH1 P1 p' T S' Hs1 Ht); reflexivity.
    - destruct Hsh as [_ Hs2]. unfold nkrow in *; cbn [row_zip set_at].
      rewrite (IH2 P2 p' T S' Hs2 Ht); reflexivity.
  Qed.

  Lemma tdrop_set : forall t P p T S',
      same_shape t P -> leaf_at t p = Some T ->
      tdrop t (set_at P p S') = set_at (tdrop t P) p (dk_tail T S').
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S' Hsh Ht;
      cbn in Hsh, Ht; try contradiction; try discriminate.
    - injection Ht as ->; unfold tdrop; cbn [row_zip set_at]; reflexivity.
    - destruct Hsh as [Hs1 _]. unfold tdrop in *; cbn [row_zip set_at].
      rewrite (IH1 P1 p' T S' Hs1 Ht); reflexivity.
    - destruct Hsh as [_ Hs2]. unfold tdrop in *; cbn [row_zip set_at].
      rewrite (IH2 P2 p' T S' Hs2 Ht); reflexivity.
  Qed.

  Lemma nkrow_leaf_at : forall t P p T S,
      same_shape t P -> leaf_at t p = Some T -> leaf_at P p = Some S ->
      leaf_at (nkrow t P) p = Some (dk_kblock T S).
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S Hsh Ht Hp;
      cbn in Hsh, Ht, Hp; try contradiction; try discriminate.
    - injection Ht as ->; injection Hp as ->;
        unfold nkrow; cbn [row_zip leaf_at]; reflexivity.
    - destruct Hsh as [Hs1 _]; unfold nkrow; cbn [row_zip leaf_at].
      apply (IH1 P1 p' T S Hs1 Ht Hp).
    - destruct Hsh as [_ Hs2]; unfold nkrow; cbn [row_zip leaf_at].
      apply (IH2 P2 p' T S Hs2 Ht Hp).
  Qed.

  Lemma tdrop_leaf_at : forall t P p T S,
      same_shape t P -> leaf_at t p = Some T -> leaf_at P p = Some S ->
      leaf_at (tdrop t P) p = Some (dk_tail T S).
  Proof.
    intros t; induction t as [T0 | t1 IH1 t2 IH2];
      intros [S0 | P1 P2] [| p' | p'] T S Hsh Ht Hp;
      cbn in Hsh, Ht, Hp; try contradiction; try discriminate.
    - injection Ht as ->; injection Hp as ->;
        unfold tdrop; cbn [row_zip leaf_at]; reflexivity.
    - destruct Hsh as [Hs1 _]; unfold tdrop; cbn [row_zip leaf_at].
      apply (IH1 P1 p' T S Hs1 Ht Hp).
    - destruct Hsh as [_ Hs2]; unfold tdrop; cbn [row_zip leaf_at].
      apply (IH2 P2 p' T S Hs2 Ht Hp).
  Qed.

  (** ** The terminated case: all three maps are the identity *)

  Lemma tdrop_terminated : forall t P,
      same_shape t P -> prog_terminated P -> tdrop t P = P.
  Proof.
    intro t; induction t as [T | t1 IH1 t2 IH2]; intros [S | P1 P2] Hsh Ht;
      cbn in Hsh; try contradiction.
    - cbn in Ht; subst S. unfold tdrop; cbn [row_zip].
      unfold dk_tail; reflexivity.
    - destruct Hsh as [H1 H2]; destruct Ht as [T1 T2].
      unfold tdrop in *; cbn [row_zip].
      rewrite (IH1 P1 H1 T1), (IH2 P2 H2 T2); reflexivity.
  Qed.

  Lemma nkrow_terminated : forall t P,
      same_shape t P -> prog_terminated P ->
      row_all (fun K => K = ε) (nkrow t P).
  Proof.
    intro t; induction t as [T | t1 IH1 t2 IH2]; intros [S | P1 P2] Hsh Ht;
      cbn in Hsh; try contradiction.
    - cbn in Ht; subst S. unfold nkrow; cbn [row_zip row_all].
      unfold dk_kblock; reflexivity.
    - destruct Hsh as [H1 H2]; destruct Ht as [T1 T2].
      unfold nkrow in *; cbn [row_zip row_all].
      split; [apply (IH1 P1 H1 T1) | apply (IH2 P2 H2 T2)].
  Qed.

  Lemma nblocks_terminated : forall t P,
      same_shape t P -> prog_terminated P ->
      row_all (fun D => D = l_skip) (nblocks t P).
  Proof.
    intro t; induction t as [T | t1 IH1 t2 IH2]; intros [S | P1 P2] Hsh Ht;
      cbn in Hsh; try contradiction.
    - cbn in Ht; subst S. unfold nblocks; cbn [row_zip row_all].
      unfold dk_block; reflexivity.
    - destruct Hsh as [H1 H2]; destruct Ht as [T1 T2].
      unfold nblocks in *; cbn [row_zip row_all].
      split; [apply (IH1 P1 H1 T1) | apply (IH2 P2 H2 T2)].
  Qed.

  Lemma denote_lseq_skip : forall (d : lrow),
      row_all (fun D => D = l_skip) d ->
      forall E : ensemble dim, denote (lseq d) E = E.
  Proof.
    intro d; induction d as [D | d1 IH1 d2 IH2]; cbn [row_all lseq]; intros H E.
    - subst D; reflexivity.
    - destruct H as [H1 H2]; cbn [denote]; rewrite IH1, IH2 by assumption.
      reflexivity.
  Qed.

  Lemma krun_eps : forall k E E',
      row_all (fun K => K = ε) k -> krun k E E' -> E' = E.
  Proof.
    intros k E E' Heps H; destruct H as [| k c e x k' E0 E1 Hp Hstep Hrun];
      [reflexivity |].
    exfalso. destruct Hp as (kmid & Hs & _).
    apply (kpick_not_terminated _ _ _ Hs), kprog_eps_terminated, Heps.
  Qed.

  Lemma path_eq_dec : forall p q : path, {p = q} + {p <> q}.
  Proof. decide equality. Defined.

  (** ** A displayed sequence's footprint is its row's *)

  Lemma lseq_change : forall d, lblock_change (lseq d) = row_flat lblock_change d.
  Proof.
    intro d; induction d as [D | d1 IH1 d2 IH2];
      cbn [lseq lblock_change row_flat]; congruence.
  Qed.

  Lemma lseq_read : forall d, lblock_read (lseq d) = row_flat lblock_read d.
  Proof.
    intro d; induction d as [D | d1 IH1 d2 IH2];
      cbn [lseq lblock_read row_flat]; congruence.
  Qed.

  Lemma lseq_qvar : forall d, lblock_qvar (lseq d) = row_flat lblock_qvar d.
  Proof.
    intro d; induction d as [D | d1 IH1 d2 IH2];
      cbn [lseq lblock_qvar row_flat]; congruence.
  Qed.

  Lemma phase_recv_flat : forall k, phase_recv k = row_flat cblock_change k.
  Proof.
    intro k; unfold phase_recv, krow_actions, cblock_change;
      induction k as [K | k1 IH1 k2 IH2]; cbn [row_flat].
    - reflexivity.
    - rewrite flat_map_app; congruence.
  Qed.

  Lemma phase_oread_flat : forall k, phase_oread k = row_flat cblock_read k.
  Proof.
    intro k; unfold phase_oread, krow_actions, cblock_read;
      induction k as [K | k1 IH1 k2 IH2]; cbn [row_flat].
    - reflexivity.
    - rewrite flat_map_app; congruence.
  Qed.

  Lemma krow_chan_flat : forall k, krow_chan k = row_flat cblock_chan k.
  Proof. reflexivity. Qed.

  (** ** Membership in a row's footprint names a position *)

  Lemma row_flat_in : forall {A B} (f : A -> list B) (r : row A) y,
      In y (row_flat f r) -> exists p a, leaf_at r p = Some a /\ In y (f a).
  Proof.
    intros A B f r; induction r as [a | r1 IH1 r2 IH2]; intros y Hy; cbn in Hy.
    - exists ph_here, a. split; [reflexivity | exact Hy].
    - apply in_app_or in Hy as [Hy | Hy].
      + destruct (IH1 y Hy) as (p & a & H1 & H2).
        exists (ph_l p), a. split; [exact H1 | exact H2].
      + destruct (IH2 y Hy) as (p & a & H1 & H2).
        exists (ph_r p), a. split; [exact H1 | exact H2].
  Qed.

  Lemma same_shape_leaf_at : forall {A B} (r1 : row A) (r2 : row B) p a,
      same_shape r1 r2 -> leaf_at r1 p = Some a -> exists b, leaf_at r2 p = Some b.
  Proof.
    intros A B r1; induction r1 as [x | x IHx y IHy];
      intros [z | z2 y2] [| p' | p'] a Hsh Hp; cbn in *;
      try contradiction; try discriminate.
    - exists z; reflexivity.
    - destruct Hsh as [H _]; exact (IHx _ _ _ H Hp).
    - destruct Hsh as [_ H]; exact (IHy _ _ _ H Hp).
  Qed.

  (** ** What one leaf contributes to each of the three maps *)

  Lemma dk_block_incl : forall T S,
      incl (lblock_change (dk_block T S)) (process_change S)
      /\ incl (lblock_read (dk_block T S)) (process_read S)
      /\ incl (lblock_qvar (dk_block T S)) (process_qvar S).
  Proof.
    intros T S; unfold dk_block; destruct (beforeb T S); destruct S as [| R K T'];
      cbn [lblock_change lblock_read lblock_qvar
           process_change process_read process_qvar];
      try (repeat split; apply incl_nil_l).
    rewrite residual_lblock_change, residual_lblock_read, residual_lblock_qvar.
    repeat split; apply incl_appl, incl_refl.
  Qed.

  Lemma dk_kblock_incl : forall T S,
      incl (cblock_change (dk_kblock T S)) (process_change S)
      /\ incl (cblock_read (dk_kblock T S)) (process_read S)
      /\ incl (cblock_chan (dk_kblock T S)) (process_chan S).
  Proof.
    intros T S; unfold dk_kblock;
      destruct (beforeb T S); destruct S as [| R K T'];
      cbn [cblock_change cblock_read cblock_chan
           process_change process_read process_chan];
      try (repeat split; apply incl_nil_l).
    repeat split; [apply incl_appr, incl_appl, incl_refl
                  | apply incl_appr, incl_appl, incl_refl
                  | apply incl_appl, incl_refl].
  Qed.

  Lemma dk_tail_incl : forall T S,
      incl (process_chan (dk_tail T S)) (process_chan S).
  Proof.
    intros T S; unfold dk_tail; destruct (beforeb T S);
      destruct S as [| R K T']; try apply incl_refl.
    cbn [process_chan]; apply incl_appr, incl_refl.
  Qed.

  (** ** Zipped rows, positionally *)

  Lemma same_shape_sym : forall {A B} (r1 : row A) (r2 : row B),
      same_shape r1 r2 -> same_shape r2 r1.
  Proof.
    intros A B r1; induction r1 as [x | x IHx y IHy];
      intros [z | z1 z2] H; cbn in *; try contradiction; try exact Logic.I.
    destruct H; split; auto.
  Qed.

  Lemma same_shape_zip : forall {A B C} (dflt : C) (g : A -> B -> C) r1 r2,
      same_shape r1 r2 -> same_shape r1 (row_zip dflt g r1 r2).
  Proof.
    intros A B C dflt g r1; induction r1 as [x | x IHx y IHy];
      intros [z | z1 z2] H; cbn in *; try contradiction; try exact Logic.I.
    destruct H; split; auto.
  Qed.

  Lemma row_zip_leaf_at : forall {A B C} (dflt : C) (g : A -> B -> C) r1 r2 q a b,
      same_shape r1 r2 -> leaf_at r1 q = Some a -> leaf_at r2 q = Some b ->
      leaf_at (row_zip dflt g r1 r2) q = Some (g a b).
  Proof.
    intros A B C dflt g r1; induction r1 as [x | x IHx y IHy];
      intros [z | z1 z2] [| q' | q'] a b Hsh H1 H2; cbn in *;
      try contradiction; try discriminate.
    - injection H1 as <-; injection H2 as <-; reflexivity.
    - destruct Hsh as [H _]; exact (IHx _ q' a b H H1 H2).
    - destruct Hsh as [_ H]; exact (IHy _ q' a b H H1 H2).
  Qed.

  (** ** THE off-leaf lemma: everything a zipped row's footprint contains
         comes from some leaf, and the leaf that contributes nothing is not it.
         This is the one shape all of the normalisation's independence side
         conditions have — for the D blocks, the K endpoints and the channels
         alike — so it is proven once, generically in the leaf map. *)

  Lemma off_leaf : forall {A C} (dflt : C) (g : process -> process -> C)
                          (f : C -> list A) (h : process -> list A)
                          (t P : program) (p : path) (y : A),
      same_shape t P ->
      (forall T S', incl (f (g T S')) (h S')) ->
      (forall T S', leaf_at t p = Some T -> leaf_at P p = Some S' ->
                    f (g T S') = nil) ->
      In y (row_flat f (row_zip dflt g t P)) ->
      exists q Sq, q <> p /\ leaf_at P q = Some Sq /\ In y (h Sq).
  Proof.
    intros A C dflt g f h t P p y Hsh Hincl Hnil Hy.
    destruct (row_flat_in _ _ _ Hy) as (q & c & Hq & Hyc).
    destruct (same_shape_leaf_at _ t q c
                (same_shape_sym _ _ (same_shape_zip dflt g t P Hsh)) Hq)
      as (T & HT).
    destruct (same_shape_leaf_at t P q T Hsh HT) as (Sq & HSq).
    rewrite (row_zip_leaf_at dflt g t P q T Sq Hsh HT HSq) in Hq.
    injection Hq as <-.
    destruct (path_eq_dec q p) as [Heq | Hne].
    - subst q. rewrite (Hnil T Sq HT HSq) in Hyc. contradiction.
    - exists q, Sq. split; [exact Hne | split; [exact HSq | exact (Hincl T Sq y Hyc)]].
  Qed.

  (** ** Shrinking one leaf *)

  Lemma row_leaves_set : forall {A} (r : row A) p b x,
      In x (row_leaves (set_at r p b)) -> In x (row_leaves r) \/ x = b.
  Proof.
    intros A r; induction r as [a | r1 IH1 r2 IH2]; intros [| p' | p'] b x H;
      cbn in *.
    - destruct H as [H | []]; right; congruence.
    - destruct H as [H | []]; left; left; congruence.
    - destruct H as [H | []]; left; left; congruence.
    - left; exact H.
    - apply in_app_or in H as [H | H].
      + destruct (IH1 p' b x H) as [H' | H']; [left; apply in_or_app; left | right];
          assumption.
      + left; apply in_or_app; right; exact H.
    - apply in_app_or in H as [H | H].
      + left; apply in_or_app; left; exact H.
      + destruct (IH2 p' b x H) as [H' | H'];
          [left; apply in_or_app; right | right]; assumption.
  Qed.

  Lemma row_flat_set_incl : forall {A B} (f : A -> list B) (r : row A) p a b,
      leaf_at r p = Some a -> incl (f b) (f a) ->
      incl (row_flat f (set_at r p b)) (row_flat f r).
  Proof.
    intros A B f r; induction r as [x | r1 IH1 r2 IH2];
      intros [| p' | p'] a b Hp Hincl; cbn in *; try discriminate;
      try apply incl_refl.
    - injection Hp as <-; exact Hincl.
    - apply incl_app;
        [eapply incl_tran; [apply (IH1 p' a b Hp Hincl) | apply incl_appl, incl_refl]
        | apply incl_appr, incl_refl].
    - apply incl_app;
        [apply incl_appl, incl_refl
        | eapply incl_tran;
          [apply (IH2 p' a b Hp Hincl) | apply incl_appr, incl_refl]].
  Qed.

  Lemma non_interfering_incl_r : forall L M M',
      incl (lblock_change M') (lblock_change M) ->
      incl (lblock_read M') (lblock_read M) ->
      incl (lblock_qvar M') (lblock_qvar M) ->
      non_interfering L M -> non_interfering L M'.
  Proof.
    intros L M M' Hc Hr Hq H.
    apply non_interfering_sym.
    eapply non_interfering_incl; try eassumption.
    apply non_interfering_sym, H.
  Qed.

  Lemma lrow_disj_set : forall d p D D',
      lrow_disj d -> leaf_at d p = Some D ->
      incl (lblock_change D') (lblock_change D) ->
      incl (lblock_read D') (lblock_read D) ->
      incl (lblock_qvar D') (lblock_qvar D) ->
      lrow_disj (set_at d p D').
  Proof.
    intro d; induction d as [D0 | d1 IH1 d2 IH2];
      intros [| p' | p'] D D' Hdisj Hp Hc Hr Hq; cbn in Hp; try discriminate;
      try exact Hdisj.
    - cbn [set_at]; repeat constructor.
    - unfold lrow_disj, DisjMP in *; cbn [set_at row_leaves] in *.
      destruct (ForallOrdPairs_app_inv _ _ _ Hdisj) as (H1 & H2 & Hcross).
      apply ForallOrdPairs_app; [apply (IH1 p' D D'); assumption | exact H2 |].
      intros X Y HX HY.
      destruct (row_leaves_set d1 p' D' X HX) as [HX' | HX'];
        [apply Hcross; assumption | subst X].
      eapply non_interfering_incl; try eassumption.
      apply Hcross; [apply (leaf_at_In _ p' _ Hp) | exact HY].
    - unfold lrow_disj, DisjMP in *; cbn [set_at row_leaves] in *.
      destruct (ForallOrdPairs_app_inv _ _ _ Hdisj) as (H1 & H2 & Hcross).
      apply ForallOrdPairs_app; [exact H1 | apply (IH2 p' D D'); assumption |].
      intros X Y HX HY.
      destruct (row_leaves_set d2 p' D' Y HY) as [HY' | HY'];
        [apply Hcross; assumption | subst Y].
      eapply non_interfering_incl_r; try eassumption.
      apply Hcross; [exact HX | apply (leaf_at_In _ p' _ Hp)].
  Qed.

  (** ** [nblocks] is a legal D-row, so Theorem 2.1 applies to it *)

  Lemma nblocks_local_row : forall t P,
      same_shape t P -> local_row P (nblocks t P).
  Proof.
    intro t; induction t as [T | t1 IH1 t2 IH2]; intros [S | P1 P2] Hsh;
      cbn in Hsh; try contradiction.
    - unfold nblocks; cbn [row_zip]. constructor.
      unfold dk_block; destruct (beforeb T S) eqn:Eb; destruct S as [| R K T'];
        try (left; reflexivity).
      destruct R as [| L]; [left; reflexivity |].
      right; cbn [block_in]; left; reflexivity.
    - destruct Hsh as [H1 H2]; unfold nblocks in *; cbn [row_zip].
      constructor; [apply (IH1 P1 H1) | apply (IH2 P2 H2)].
  Qed.

  Lemma nblocks_disj : forall t P,
      same_shape t P -> wf_ownership P -> lrow_disj (nblocks t P).
  Proof.
    intros t P Hsh Hown.
    apply (wf_ownership_disj_footprints P _ Hown (nblocks_local_row t P Hsh)).
  Qed.

  (** ** [wf_ownership] survives shrinking one leaf *)

  Lemma wf_ownership_set : forall P p S S',
      wf_ownership P -> leaf_at P p = Some S ->
      incl (process_change S') (process_change S) ->
      incl (process_read S') (process_read S) ->
      incl (process_qvar S') (process_qvar S) ->
      wf_ownership (set_at P p S').
  Proof.
    intro P; induction P as [S0 | P1 IH1 P2 IH2];
      intros [| p' | p'] S S' Hown Hp Hc Hr Hq; cbn in Hp; try discriminate;
      try exact Hown; cbn [set_at];
      destruct Hown as (Ho1 & Ho2 & Hc12 & Hc21 & Hq12);
      assert (Hcv : incl (process_cvar S') (process_cvar S))
        by (unfold process_cvar; apply incl_app;
            [eapply incl_tran; [exact Hc | apply incl_appl, incl_refl]
            | eapply incl_tran; [exact Hr | apply incl_appr, incl_refl]]).
    - assert (Hpc : incl (program_change (set_at P1 p' S')) (program_change P1))
        by (unfold program_change;
            apply (row_flat_set_incl process_change P1 p' S S' Hp Hc)).
      assert (Hpv : incl (program_cvar (set_at P1 p' S')) (program_cvar P1))
        by (unfold program_cvar;
            apply (row_flat_set_incl process_cvar P1 p' S S' Hp Hcv)).
      assert (Hpq : incl (program_qvar (set_at P1 p' S')) (program_qvar P1))
        by (unfold program_qvar;
            apply (row_flat_set_incl process_qvar P1 p' S S' Hp Hq)).
      split; [apply (IH1 p' S S'); assumption | split; [exact Ho2 |]].
      repeat split.
      + eapply disjoint_incl; [exact Hc12 | exact Hpc | apply incl_refl].
      + eapply disjoint_incl; [exact Hc21 | apply incl_refl | exact Hpv].
      + eapply disjoint_incl; [exact Hq12 | exact Hpq | apply incl_refl].
    - assert (Hpc : incl (program_change (set_at P2 p' S')) (program_change P2))
        by (unfold program_change;
            apply (row_flat_set_incl process_change P2 p' S S' Hp Hc)).
      assert (Hpv : incl (program_cvar (set_at P2 p' S')) (program_cvar P2))
        by (unfold program_cvar;
            apply (row_flat_set_incl process_cvar P2 p' S S' Hp Hcv)).
      assert (Hpq : incl (program_qvar (set_at P2 p' S')) (program_qvar P2))
        by (unfold program_qvar;
            apply (row_flat_set_incl process_qvar P2 p' S S' Hp Hq)).
      split; [exact Ho1 | split; [apply (IH2 p' S S'); assumption |]].
      repeat split.
      + eapply disjoint_incl; [exact Hc12 | apply incl_refl | exact Hpv].
      + eapply disjoint_incl; [exact Hc21 | exact Hpc | apply incl_refl].
      + eapply disjoint_incl; [exact Hq12 | apply incl_refl | exact Hpq].
  Qed.

  (** ** The two independence facts, one per map.

      In both, the named leaf contributes nothing to the map, so everything the
      map touches belongs to some OTHER leaf, and [wf_ownership_paths] pays. *)

  Lemma process_change_cvar_leaf : forall S, incl (process_change S) (process_cvar S).
  Proof. intro S; unfold process_cvar; apply incl_appl, incl_refl. Qed.

  Lemma process_read_cvar_leaf : forall S, incl (process_read S) (process_cvar S).
  Proof. intro S; unfold process_cvar; apply incl_appr, incl_refl. Qed.

  Lemma nlseq_off : forall t P p S,
      wf_ownership P -> same_shape t P -> leaf_at P p = Some S ->
      (forall T, leaf_at t p = Some T -> dk_block T S = l_skip) ->
      disjoint (lblock_change (nlseq t P)) (process_cvar S)
      /\ disjoint (process_change S) (lblock_read (nlseq t P))
      /\ disjoint (lblock_qvar (nlseq t P)) (process_qvar S).
  Proof.
    intros t P p S Hown Hsh HpS Hskip.
    assert (Hnil : forall (B : Type) (f : lblock -> list B),
               f l_skip = nil ->
               forall T S', leaf_at t p = Some T -> leaf_at P p = Some S' ->
                            f (dk_block T S') = nil).
    { intros B f Hf T S' HT HS'. rewrite HpS in HS'; injection HS' as <-.
      rewrite (Hskip T HT); exact Hf. }
    unfold nlseq; rewrite lseq_change, lseq_read, lseq_qvar.
    split; [| split]; intros y Hy Hz.
    - destruct (off_leaf l_skip dk_block lblock_change process_change t P p y Hsh
                  (fun T S' => proj1 (dk_block_incl T S'))
                  (Hnil _ lblock_change eq_refl) Hy) as (q & Sq & Hne & HSq & HyS).
      destruct (wf_ownership_paths P q p Sq S Hown Hne HSq HpS)
        as (Hd & _ & _). exact (Hd y HyS Hz).
    - destruct (off_leaf l_skip dk_block lblock_read process_read t P p y Hsh
                  (fun T S' => proj1 (proj2 (dk_block_incl T S')))
                  (Hnil _ lblock_read eq_refl) Hz) as (q & Sq & Hne & HSq & HyS).
      destruct (wf_ownership_paths P p q S Sq Hown
                  ltac:(intro Hc; apply Hne; symmetry; exact Hc) HpS HSq)
        as (Hd & _ & _). exact (Hd y Hy (process_read_cvar_leaf Sq y HyS)).
    - destruct (off_leaf l_skip dk_block lblock_qvar process_qvar t P p y Hsh
                  (fun T S' => proj2 (proj2 (dk_block_incl T S')))
                  (Hnil _ lblock_qvar eq_refl) Hy) as (q & Sq & Hne & HSq & HyS).
      destruct (wf_ownership_paths P q p Sq S Hown Hne HSq HpS)
        as (_ & _ & Hd). exact (Hd y HyS Hz).
  Qed.

  Lemma nkrow_off : forall t P p S,
      wf_ownership P -> same_shape t P -> leaf_at P p = Some S ->
      (forall T, leaf_at t p = Some T -> dk_kblock T S = nil) ->
      disjoint (phase_recv (nkrow t P)) (process_cvar S)
      /\ disjoint (process_change S) (phase_oread (nkrow t P)).
  Proof.
    intros t P p S Hown Hsh HpS Hnone.
    assert (Hnil : forall (B : Type) (f : cblock -> list B),
               f nil = nil ->
               forall T S', leaf_at t p = Some T -> leaf_at P p = Some S' ->
                            f (dk_kblock T S') = nil).
    { intros B f Hf T S' HT HS'. rewrite HpS in HS'; injection HS' as <-.
      rewrite (Hnone T HT); exact Hf. }
    rewrite phase_recv_flat, phase_oread_flat.
    split; intros y Hy Hz.
    - destruct (off_leaf nil dk_kblock cblock_change process_change t P p y Hsh
                  (fun T S' => proj1 (dk_kblock_incl T S'))
                  (Hnil _ cblock_change eq_refl) Hy) as (q & Sq & Hne & HSq & HyS).
      destruct (wf_ownership_paths P q p Sq S Hown Hne HSq HpS)
        as (Hd & _ & _). exact (Hd y HyS Hz).
    - destruct (off_leaf nil dk_kblock cblock_read process_read t P p y Hsh
                  (fun T S' => proj1 (proj2 (dk_kblock_incl T S')))
                  (Hnil _ cblock_read eq_refl) Hz) as (q & Sq & Hne & HSq & HyS).
      destruct (wf_ownership_paths P p q S Sq Hown
                  ltac:(intro Hc; apply Hne; symmetry; exact Hc) HpS HSq)
        as (Hd & _ & _). exact (Hd y Hy (process_read_cvar_leaf Sq y HyS)).
  Qed.

  (** ** …and the four side conditions the normalisation actually quotes *)

  Lemma nlseq_rdv_indep : forall t P ps pr Ss Sr x e,
      wf_ownership P -> same_shape t P ->
      leaf_at P ps = Some Ss -> leaf_at P pr = Some Sr ->
      (forall T, leaf_at t ps = Some T -> dk_block T Ss = l_skip) ->
      (forall T, leaf_at t pr = Some T -> dk_block T Sr = l_skip) ->
      In x (process_change Sr) -> incl (expr_vars e) (process_read Ss) ->
      rdv_indep (nlseq t P) x e.
  Proof.
    intros t P ps pr Ss Sr x e Hown Hsh Hs Hr Hbs Hbr Hx He.
    destruct (nlseq_off t P ps Ss Hown Hsh Hs Hbs) as (Hs1 & _ & _).
    destruct (nlseq_off t P pr Sr Hown Hsh Hr Hbr) as (Hr1 & Hr2 & _).
    split; [| split].
    - intro Hin; exact (Hr2 x Hx Hin).
    - intro Hin; exact (Hr1 x Hin (process_change_cvar_leaf Sr x Hx)).
    - intros y Hy Hz; exact (Hs1 y Hy (process_read_cvar_leaf Ss y (He y Hz))).
  Qed.

  Lemma nkrow_krdv_indep : forall t P ps pr Ss Sr x e,
      wf_ownership P -> same_shape t P ->
      leaf_at P ps = Some Ss -> leaf_at P pr = Some Sr ->
      (forall T, leaf_at t ps = Some T -> dk_kblock T Ss = nil) ->
      (forall T, leaf_at t pr = Some T -> dk_kblock T Sr = nil) ->
      In x (process_change Sr) -> incl (expr_vars e) (process_read Ss) ->
      krdv_indep x e (nkrow t P).
  Proof.
    intros t P ps pr Ss Sr x e Hown Hsh Hs Hr Hbs Hbr Hx He.
    destruct (nkrow_off t P ps Ss Hown Hsh Hs Hbs) as (Hs1 & _).
    destruct (nkrow_off t P pr Sr Hown Hsh Hr Hbr) as (Hr1 & Hr2).
    split; [| split].
    - intro Hin; exact (Hr1 x Hin (process_change_cvar_leaf Sr x Hx)).
    - intro Hin; exact (Hr2 x Hx Hin).
    - intros y Hy Hz; exact (Hs1 y Hy (process_read_cvar_leaf Ss y (He y Hz))).
  Qed.

  Lemma nlseq_non_interfering : forall t P p S L,
      wf_ownership P -> same_shape t P -> leaf_at P p = Some S ->
      (forall T, leaf_at t p = Some T -> dk_block T S = l_skip) ->
      incl (lblock_change L) (process_change S) ->
      incl (lblock_read L) (process_read S) ->
      incl (lblock_qvar L) (process_qvar S) ->
      non_interfering L (nlseq t P).
  Proof.
    intros t P p S L Hown Hsh Hp Hb Hc Hr Hq.
    destruct (nlseq_off t P p S Hown Hsh Hp Hb) as (H1 & H2 & H3).
    split; [| split; [| split]]; intros y Hy Hz.
    - exact (H1 y Hz (process_change_cvar_leaf S y (Hc y Hy))).
    - exact (H2 y (Hc y Hy) Hz).
    - exact (H1 y Hy (process_read_cvar_leaf S y (Hr y Hz))).
    - exact (H3 y Hz (Hq y Hy)).
  Qed.

  Lemma nkrow_kindep : forall t P p S L,
      wf_ownership P -> same_shape t P -> leaf_at P p = Some S ->
      (forall T, leaf_at t p = Some T -> dk_kblock T S = nil) ->
      incl (lblock_change L) (process_change S) ->
      incl (lblock_read L) (process_read S) ->
      kindep L (nkrow t P).
  Proof.
    intros t P p S L Hown Hsh Hp Hb Hc Hr.
    destruct (nkrow_off t P p S Hown Hsh Hp Hb) as (H1 & H2).
    split; [| split]; intros y Hy Hz.
    - exact (H1 y Hz (process_read_cvar_leaf S y (Hr y Hy))).
    - exact (H1 y Hz (process_change_cvar_leaf S y (Hc y Hy))).
    - exact (H2 y (Hc y Hy) Hz).
  Qed.


(** ** 16. Par-Comp-MP — the invariant carried along a run *****************

    [cut_inv t P] is what the normalisation needs of a reachable program:
    every leaf is in a legal stage relative to its tail in t, ownership still
    separates the leaves, and the displayed phase shares no channel with the
    tail.

    The last clause is the cut's channel disjointness ([cut_chan_disjoint],
    from [wf_channels] and [wf_phase_aligned]), and [rdv_same_stage]
    is the one place it pays: without it a rendezvous could pair an endpoint
    still in the displayed phase with one that has already fallen through,
    and such a step is neither a k-step (it moves the tail) nor a t-step (it
    moves the phase) — the normalisation would have no case for it.

    Every step of the semantics rewrites ONE leaf into [advance R' K' T0]
    with a smaller footprint and a smaller K, so all three cases maintain the
    invariant through the single lemma [cut_inv_leaf].
*********************************************************************)

  (** ** Picking an endpoint only shrinks a block *)

  Lemma picks_In : forall K a K', K ∋ a □ K' -> In a K.
  Proof.
    intros K a K' H; induction H as [a K | a b K K' H IH];
      [left; reflexivity | right; exact IH].
  Qed.

  Lemma picks_footprint : forall K a K',
      K ∋ a □ K' ->
      incl (cblock_change K') (cblock_change K)
      /\ incl (cblock_read K') (cblock_read K)
      /\ incl (cblock_chan K') (cblock_chan K).
  Proof.
    intros K a K' H.
    pose proof (picks_perm _ _ _ H) as Hp.
    unfold cblock_change, cblock_read, cblock_chan.
    repeat split; intros y Hy.
    - eapply Permutation_in;
        [apply Permutation_sym, (permutation_flat_map _ _ caction_change _ _ Hp) |].
      cbn [flat_map]; apply in_or_app; right; exact Hy.
    - eapply Permutation_in;
        [apply Permutation_sym, (permutation_flat_map _ _ caction_read _ _ Hp) |].
      cbn [flat_map]; apply in_or_app; right; exact Hy.
    - eapply Permutation_in;
        [apply Permutation_sym, (Permutation_map caction_chan Hp) |].
      cbn [map]; right; exact Hy.
  Qed.

  (** ** A step only shrinks a leaf *)

  Lemma advance_incl : forall R K T,
      incl (process_change (advance R K T)) (process_change (phase R K T))
      /\ incl (process_read (advance R K T)) (process_read (phase R K T))
      /\ incl (process_qvar (advance R K T)) (process_qvar (phase R K T))
      /\ incl (process_chan (advance R K T)) (process_chan (phase R K T)).
  Proof.
    intros [| L] [| a K0] T; cbn [advance]; repeat split; apply incl_refl.
  Qed.

  Lemma leaf_shrink_local : forall L K T R',
      incl (residual_change R') (lblock_change L) ->
      incl (residual_read R') (lblock_read L) ->
      incl (residual_qvar R') (lblock_qvar L) ->
      incl (process_change (advance R' K T)) (process_change (phase (r_more L) K T))
      /\ incl (process_read (advance R' K T)) (process_read (phase (r_more L) K T))
      /\ incl (process_qvar (advance R' K T)) (process_qvar (phase (r_more L) K T))
      /\ incl (process_chan (advance R' K T)) (process_chan (phase (r_more L) K T)).
  Proof.
    intros L K T R' Hc Hr Hq.
    destruct (advance_incl R' K T) as (H1 & H2 & H3 & H4).
    repeat split;
      (eapply incl_tran; [eassumption |]);
      cbn [process_change process_read process_qvar process_chan
           residual_change residual_read residual_qvar].
    - apply incl_app; [apply incl_appl, Hc | apply incl_appr, incl_refl].
    - apply incl_app; [apply incl_appl, Hr | apply incl_appr, incl_refl].
    - apply incl_app; [apply incl_appl, Hq | apply incl_appr, incl_refl].
    - apply incl_refl.
  Qed.

  Lemma leaf_shrink_rdv : forall K K' T a,
      K ∋ a □ K' ->
      incl (process_change (advance r_done K' T))
           (process_change (phase r_done K T))
      /\ incl (process_read (advance r_done K' T))
              (process_read (phase r_done K T))
      /\ incl (process_qvar (advance r_done K' T))
              (process_qvar (phase r_done K T))
      /\ incl (process_chan (advance r_done K' T))
              (process_chan (phase r_done K T)).
  Proof.
    intros K K' T a Hp.
    destruct (picks_footprint _ _ _ Hp) as (Hc & Hr & Hch).
    destruct (advance_incl r_done K' T) as (H1 & H2 & H3 & H4).
    repeat split;
      (eapply incl_tran; [eassumption |]);
      cbn [process_change process_read process_qvar process_chan
           residual_change residual_read residual_qvar app].
    - apply incl_app; [apply incl_appl, Hc | apply incl_appr, incl_refl].
    - apply incl_app; [apply incl_appl, Hr | apply incl_appr, incl_refl].
    - apply incl_refl.
    - apply incl_app; [apply incl_appl, Hch | apply incl_appr, incl_refl].
  Qed.

  (** ** The one place the cut's channel disjointness pays: a rendezvous
         cannot straddle the cut.  If one endpoint is still in the displayed
         phase and the other has fallen through into the tail, the shared
         channel sits in both [krow_chan k] and [program_chan t]. *)

  Lemma rdv_same_stage : forall t P ps pr Tps Tpr Ks Kr Ts Tr c e x Ks' Kr',
      same_shape t P ->
      disjoint (krow_chan (nkrow t P)) (program_chan (tdrop t P)) ->
      leaf_at t ps = Some Tps -> leaf_at t pr = Some Tpr ->
      leaf_at P ps = Some (phase r_done Ks Ts) ->
      leaf_at P pr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send c e □ Ks' -> Kr ∋ c_recv c x □ Kr' ->
      beforeb Tps (phase r_done Ks Ts) = beforeb Tpr (phase r_done Kr Tr).
  Proof.
    intros t P ps pr Tps Tpr Ks Kr Ts Tr c e x Ks' Kr'
           Hsh Hdisj Hts Htr Hps Hpr Hsend Hrecv.
    assert (Hcs : In c (cblock_chan Ks)).
    { unfold cblock_chan; apply in_map_iff.
      exists (c_send c e); split; [reflexivity | apply (picks_In _ _ _ Hsend)]. }
    assert (Hcr : In c (cblock_chan Kr)).
    { unfold cblock_chan; apply in_map_iff.
      exists (c_recv c x); split; [reflexivity | apply (picks_In _ _ _ Hrecv)]. }
    (* in the displayed phase: the leaf is still before its tail *)
    assert (Hk : forall p T K T0,
               leaf_at t p = Some T -> leaf_at P p = Some (phase r_done K T0) ->
               beforeb T (phase r_done K T0) = true ->
               In c (cblock_chan K) -> In c (krow_chan (nkrow t P))).
    { intros p T K T0 HT HP Hb Hc.
      rewrite krow_chan_flat.
      apply (leaf_at_flat_incl cblock_chan (nkrow t P) p K); [| exact Hc].
      rewrite (nkrow_leaf_at t P p T _ Hsh HT HP).
      unfold dk_kblock; rewrite Hb; reflexivity. }
    (* in the tail: the leaf has fallen through, and keeps its own channels *)
    assert (Ht : forall p T K T0,
               leaf_at t p = Some T -> leaf_at P p = Some (phase r_done K T0) ->
               beforeb T (phase r_done K T0) = false ->
               In c (cblock_chan K) -> In c (program_chan (tdrop t P))).
    { intros p T K T0 HT HP Hb Hc.
      unfold program_chan.
      apply (leaf_at_flat_incl process_chan (tdrop t P) p (phase r_done K T0)).
      - rewrite (tdrop_leaf_at t P p T _ Hsh HT HP).
        unfold dk_tail; rewrite Hb; reflexivity.
      - cbn [process_chan]; apply in_or_app; left; exact Hc. }
    destruct (beforeb Tps (phase r_done Ks Ts)) eqn:Es;
      destruct (beforeb Tpr (phase r_done Kr Tr)) eqn:Er;
      try reflexivity; exfalso.
    - exact (Hdisj c (Hk ps Tps Ks Ts Hts Hps Es Hcs)
               (Ht pr Tpr Kr Tr Htr Hpr Er Hcr)).
    - exact (Hdisj c (Hk pr Tpr Kr Tr Htr Hpr Er Hcr)
               (Ht ps Tps Ks Ts Hts Hps Es Hcs)).
  Qed.

  (** ** The invariant, and the single lemma that maintains it *)

  Definition cut_inv (t P : program) : Prop :=
    row_all2 stage_ok t P
    /\ wf_ownership P
    /\ disjoint (krow_chan (nkrow t P)) (program_chan (tdrop t P)).

  Lemma cut_inv_shape : forall t P, cut_inv t P -> same_shape t P.
  Proof. intros t P (H & _ & _); exact (row_all2_shape _ _ _ H). Qed.

  (** Every step of the semantics rewrites ONE leaf into [advance R' K' T0]
      with a smaller footprint and a smaller K; that is all the invariant
      needs, so the three cases share one lemma. *)
  Lemma cut_inv_leaf : forall t P p T R K T0 R' K',
      cut_inv t P ->
      leaf_at t p = Some T -> leaf_at P p = Some (phase R K T0) ->
      incl (process_change (advance R' K' T0)) (process_change (phase R K T0)) ->
      incl (process_read (advance R' K' T0)) (process_read (phase R K T0)) ->
      incl (process_qvar (advance R' K' T0)) (process_qvar (phase R K T0)) ->
      incl (process_chan (advance R' K' T0)) (process_chan (phase R K T0)) ->
      incl (cblock_chan K') (cblock_chan K) ->
      cut_inv t (set_at P p (advance R' K' T0)).
  Proof.
    intros t P p T R K T0 R' K' Hinv Ht Hp Hc Hr Hq Hch HK.
    assert (Hsh := cut_inv_shape _ _ Hinv).
    destruct Hinv as (Hst & Hown & Hdj).
    (* the two facts that depend on which stage the leaf is in *)
    assert (Hstage : stage_ok T (advance R' K' T0)
                     /\ incl (cblock_chan (dk_kblock T (advance R' K' T0)))
                             (cblock_chan (dk_kblock T (phase R K T0)))
                     /\ incl (process_chan (dk_tail T (advance R' K' T0)))
                             (process_chan (dk_tail T (phase R K T0)))).
    { destruct (beforeb T (phase R K T0)) eqn:Eb.
      - apply beforeb_spec in Eb as (R1 & K1 & Heq).
        injection Heq as _ _ HT0; subst T0.
        destruct (stage_before T K' R') as (Hta & Hka & Hok).
        rewrite Hta, Hka, dk_tail_phase, dk_kblock_phase.
        split; [exact Hok | split; [exact HK | apply incl_refl]].
      - assert (Hok0 : stage_ok T (phase R K T0))
          by exact (row_all2_at _ _ _ _ _ _ Hst Ht Hp).
        destruct (stage_after T R K T0 R' K' Hok0 Eb) as (Hta & Hka & _ & Hok).
        rewrite Hta, Hka.
        replace (dk_tail T (phase R K T0)) with (phase R K T0)
          by (unfold dk_tail; rewrite Eb; reflexivity).
        split; [exact Hok | split; [apply incl_nil_l | exact Hch]]. }
    destruct Hstage as (Hok & Hkc & Htc).
    split; [| split].
    - apply (row_all2_set _ _ _ _ _ _ Hst Ht Hok).
    - apply (wf_ownership_set P p _ _ Hown Hp Hc Hr Hq).
    - rewrite (nkrow_set t P p T _ Hsh Ht), (tdrop_set t P p T _ Hsh Ht).
      eapply disjoint_incl; [exact Hdj | |].
      + rewrite !krow_chan_flat.
        apply (row_flat_set_incl cblock_chan (nkrow t P) p
                 (dk_kblock T (phase R K T0)) _
                 (nkrow_leaf_at t P p T _ Hsh Ht Hp) Hkc).
      + unfold program_chan.
        apply (row_flat_set_incl process_chan (tdrop t P) p
                 (dk_tail T (phase R K T0)) _
                 (tdrop_leaf_at t P p T _ Hsh Ht Hp) Htc).
  Qed.


(** ** 17. Par-Comp-MP — the normalisation relation ***********************

    One original component's image is a GROUP of normalised components, each
    carrying its own slice of the d-stage ensemble and its own k-stage
    schedule.  Groups are only ever CONCATENATED, never merged into a single
    component: merging would ask for

      Term_cfg [(Q,A)] X -> Term_cfg [(Q,B)] Y -> Term_cfg [(Q,A++B)] (X++Y)

    and [distri_step_transfer] only gives "run A's schedule, dragging B
    along", whose right half is a DIFFERENT terminal ensemble unless the
    semantics is confluent.  [wf_program] does buy that, but only through a
    diamond argument (§20 onwards); keeping the group split costs
    nothing: the degree chain has to take the normalised ensemble apart to
    single states anyway.

    So a d-step, which splits one component into several with the same
    [tdrop], is a pure regrouping — the normalised CONFIGURATION does not
    move at all.
*********************************************************************)

  (** One original component's image: a GROUP of normalised components, each
      carrying its own slice of the d-stage ensemble and its own k-stage
      schedule.  Groups are never merged back into one component — that would
      need the semantics to be confluent — they are only ever concatenated,
      which leaves the configuration alone. *)
  Definition nrm_rel (t : program) (c : program * ensemble dim)
                     (Gm : distri_config dim) : Prop :=
    exists Eds : list (ensemble dim),
      Permutation (concat Eds) (denote (nlseq t (fst c)) (snd c))
      /\ Forall2 (fun Ed cn => fst cn = tdrop t (fst c)
                               /\ krun (nkrow t (fst c)) Ed (snd cn)) Eds Gm.

  (** ** Plumbing on the group *)

  Lemma nrm_rel_progs : forall t c Gm,
      nrm_rel t c Gm -> Forall (fun cn => fst cn = tdrop t (fst c)) Gm.
  Proof.
    intros t c Gm (Eds & _ & HF).
    induction HF as [| Ed cn Eds' Gm' (H1 & _) HF IH]; constructor;
      [exact H1 | exact IH].
  Qed.

  (** ** The terminated case *)

  Lemma nrm_rel_terminated : forall t P E Gm,
      same_shape t P -> prog_terminated P ->
      nrm_rel t (P, E) Gm ->
      Forall (fun cn => fst cn = P) Gm /\ Permutation (collapse Gm) E.
  Proof.
    intros t P E Gm Hsh Ht (Eds & Hperm & HF).
    rewrite (denote_lseq_skip (nblocks t P) (nblocks_terminated t P Hsh Ht))
      in Hperm.
    split.
    - clear Hperm; induction HF as [| Ed cn Eds' Gm' (H1 & _) HF IH];
        constructor;
        [rewrite H1; cbn [fst]; apply (tdrop_terminated t P Hsh Ht)
        | exact IH].
    - (* each group member's krun is the identity, so the collapse is [concat Eds] *)
      assert (Hid : Forall2 (fun Ed cn => Permutation Ed (snd cn)) Eds Gm).
      { eapply Forall2_impl; [| exact HF].
        intros Ed cn (_ & Hk); cbn [fst] in Hk.
        rewrite (krun_eps (nkrow t P) Ed (snd cn)
                   (nkrow_terminated t P Hsh Ht) Hk).
        apply Permutation_refl. }
      eapply Permutation_trans; [| exact Hperm].
      unfold collapse. clear Hperm HF.
      induction Hid as [| Ed cn Eds' Gm' Hp HF IH]; cbn [concat flat_map];
        [apply Permutation_refl |].
      apply Permutation_app; [apply Permutation_sym, Hp | exact IH].
  Qed.

  (** ** A k-step's [rmap] has to be pulled back through the group's split *)

  Lemma map_concat_inv : forall {A B} (f : A -> B) (l : list A) (Ls : list (list B)),
      map f l = concat Ls ->
      exists Ls', l = concat Ls' /\ map (map f) Ls' = Ls.
  Proof.
    intros A B f l Ls; revert l; induction Ls as [| L Ls IH]; intros l H.
    - cbn [concat] in H. exists nil. split; [| reflexivity].
      destruct l; [reflexivity | discriminate].
    - cbn [concat] in H.
      destruct (map_eq_app _ _ _ _ H) as (l1 & l2 & Hl & H1 & H2).
      destruct (IH l2 H2) as (Ls' & HL & HM).
      exists (l1 :: Ls'). split; cbn [concat map]; congruence.
  Qed.

  Lemma rmap_pullback : forall x e (Ed : ensemble dim) (Eds' : list (ensemble dim)),
      Permutation (concat Eds') (rmap x e Ed) ->
      exists Eds, Permutation (concat Eds) Ed
               /\ map (rmap x e) Eds = Eds'.
  Proof.
    intros x e Ed Eds' Hp.
    unfold rmap in Hp |- *.
    destruct (Permutation_map_inv _ _ Hp) as (Ed'' & Heq & Hperm).
    destruct (map_concat_inv _ Ed'' Eds' (eq_sym Heq)) as (Eds & HL & HM).
    exists Eds. split.
    - rewrite HL in Hperm. apply Permutation_sym, Hperm.
    - exact HM.
  Qed.

  (** ** A local step commutes with a non-interfering block, branch by branch *)

  Lemma local_step_denote_branch : local_ops ->
    forall M L (E : ensemble dim) Gl,
      non_interfering L M ->
      Σ ⊳ ‹ L, E › →ₗ Gl ->
      exists Gl', Σ ⊳ ‹ L, denote M E › →ₗ Gl'
               /\ map fst Gl' = map fst Gl
               /\ Forall2 (fun c c' => Permutation (denote M (snd c)) (snd c'))
                          Gl Gl'.
  Proof.
    intros Hloc M L E Gl Hni Hstep.
    destruct (local_step_total L (denote M E)) as (Gl' & Hstep').
    exists Gl'. split; [exact Hstep' | split].
    - exact (local_step_shape L _ _ _ _ Hstep' Hstep).
    - revert Gl' Hstep'; induction Hstep as
        [ Ea | y f Ea | q Ea | U qs Ea | y M0 qs Ea
        | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
        intros Gl' Hstep'; inversion Hstep' as
        [ Eb | y' f' Eb | q' Eb | U' qs' Eb | y' M0' qs' Eb
        | L1' L2' Eb Gb Hs' | b' L1' L0' Eb ]; subst.
      + repeat constructor. apply Permutation_refl.
      + repeat constructor; cbn [snd].
        apply Permutation_sym, (denote_comm Hloc (l_assign y f) M Hni).
      + repeat constructor; cbn [snd].
        apply Permutation_sym, (denote_comm Hloc (l_init q) M Hni).
      + repeat constructor; cbn [snd].
        apply Permutation_sym, (denote_comm Hloc (l_ugate U qs) M Hni).
      + repeat constructor; cbn [snd].
        apply Permutation_sym, (denote_comm Hloc (l_meas y M0 qs) M Hni).
      + destruct (non_interfering_seq _ _ _ Hni) as (H1 & _).
        pose proof (IH H1 _ Hs') as HF.
        clear -HF. revert Gb HF; induction Ga as [| c Ga IHg];
          intros [| c' Gb] HF; cbn [map]; try (inversion HF; fail).
        * constructor.
        * inversion HF as [| u v l l' Hh Ht]; subst.
          constructor;
            [destruct (fst c), (fst c'); cbn [snd]; exact Hh | apply IHg, Ht].
      + destruct (non_interfering_if _ _ _ _ Hni) as (H1 & H0).
        pose proof (non_interfering_guard _ _ _ _ Hni) as Hg.
        cbn [app]. constructor; [| constructor; [| constructor]]; cbn [snd].
        * apply Permutation_sym.
          rewrite (denote_filter_comm _ M Ea (store_indep_guard b _ Hg)).
          apply Permutation_refl.
        * apply Permutation_sym.
          rewrite (denote_filter_comm _ M Ea
                     (store_indep_negb _ _ (store_indep_guard b _ Hg))).
          apply Permutation_refl.
  Qed.


(** ** 18. Par-Comp-MP — every run terminates ******************************

    Weighting a component by 3^(its measure) makes the whole configuration
    strictly decrease at every step.  Two facts about a local step are what
    makes the weight work: it shrinks the block it leaves behind
    ([local_step_size], where [if] and [seq] are the only cases with anything
    to say), and it forks in two at worst ([local_step_len]) — so one weight
    3^n is replaced by at most 2·3^(n-1), which is less than 3^n.

    The measure counts the CHOICES a leaf still has to make: an atomic block
    is 0, because it runs in one step and leaves ↓ behind, while [seq] and
    [if] each cost one.  A rendezvous is paid for by the endpoint count.
    [advance]'s erasure is invisible to it — dropping an exhausted phase
    removes exactly the zero it contributed — which is what lets the
    rendezvous and local cases share one bookkeeping lemma.
*********************************************************************)

  (** The size of a block is the number of CHOICES still inside it: an atomic
      block is 0, since it runs in one step and leaves ↓ behind. *)
  Fixpoint lb_size (L : lblock) : nat :=
    match L with
    | l_seq L1 L2  => Datatypes.S (lb_size L1 + lb_size L2)
    | l_if _ L1 L0 => Datatypes.S (lb_size L1 + lb_size L0)
    | _            => 0
    end.

  Definition res_msr (R : residual) : nat :=
    match R with r_done => 0 | r_more L => Datatypes.S (lb_size L) end.

  Fixpoint proc_msr (T : process) : nat :=
    match T with
    | terminated   => 0
    | phase R K T' => res_msr R + length K + proc_msr T'
    end.

  Fixpoint prog_msr (P : program) : nat :=
    match P with
    | leaf T    => proc_msr T
    | par P1 P2 => prog_msr P1 + prog_msr P2
    end.

  (** [advance]'s erasure is invisible to the measure: dropping an exhausted
      phase removes exactly the zero it contributed. *)
  Lemma proc_msr_advance : forall R K T,
      proc_msr (advance R K T) = (res_msr R + length K + proc_msr T)%nat.
  Proof. intros [| L] [| a K0] T; reflexivity. Qed.

  Lemma prog_msr_set : forall P p S S',
      leaf_at P p = Some S ->
      (prog_msr (set_at P p S') + proc_msr S)%nat = (prog_msr P + proc_msr S')%nat.
  Proof.
    intro P; induction P as [T | P1 IH1 P2 IH2]; intros [| p' | p'] S S' H;
      cbn in H; try discriminate.
    - injection H as <-; cbn [set_at prog_msr]; lia.
    - cbn [set_at prog_msr]. specialize (IH1 p' S S' H); lia.
    - cbn [set_at prog_msr]. specialize (IH2 p' S S' H); lia.
  Qed.

  Lemma replace_leaf_msr : forall a b P P',
      replace_leaf a b P P' ->
      (prog_msr P' + proc_msr a)%nat = (prog_msr P + proc_msr b)%nat.
  Proof.
    intros a b P P' H; induction H as [| P P' Q H IH | P Q Q' H IH];
      cbn [prog_msr]; lia.
  Qed.

  Lemma picks_length : forall K a K', K ∋ a □ K' -> length K = Datatypes.S (length K').
  Proof.
    intros K a K' H; induction H as [a K | a b K K' H IH]; cbn [length];
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  (** A local step shrinks the block it leaves behind… *)
  Lemma local_step_size : forall L E G,
      Σ ⊳ ‹ L, E › →ₗ G ->
      Forall (fun c => (res_msr (fst c) < Datatypes.S (lb_size L))%nat) G.
  Proof.
    intros L E G H; induction H as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      cbn [lb_size].
    1-5: apply Forall_cons; [cbn [fst res_msr]; lia | apply Forall_nil].
    - rewrite Forall_map. eapply Forall_impl; [| exact IH].
      intros [rd Ee] Hr; cbn [fst] in *.
      destruct rd; cbn [fst res_msr lb_size] in *; lia.
    - cbn [app]. apply Forall_cons; [cbn [fst res_msr]; lia |].
      apply Forall_cons; [cbn [fst res_msr]; lia | apply Forall_nil].
  Qed.

  (** …and never forks more than in two. *)
  Lemma local_step_len : forall L E G,
      Σ ⊳ ‹ L, E › →ₗ G -> (length G <= 2)%nat.
  Proof.
    intros L E G H; induction H as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      cbn [length app]; try lia.
    rewrite length_map; exact IH.
  Qed.

  Lemma distri_step_msr : forall P E G,
      Σ ⊳ ‹ P, E › ⇝ G ->
      Forall (fun c => (prog_msr (fst c) < prog_msr P)%nat) G
      /\ (length G <= 2)%nat.
  Proof.
    intros P E G H; induction H as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 Ga Hs IH
      | P1 P2 E0 Gb Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ].
    - split.
      + rewrite Forall_map.
        pose proof (local_step_size _ _ _ Hloc) as Hs.
        eapply Forall_impl; [| exact Hs].
        intros [rd Ee] Hr; cbn [fst prog_msr] in *.
        rewrite proc_msr_advance; cbn [proc_msr res_msr]; lia.
      + rewrite length_map. exact (local_step_len _ _ _ Hloc).
    - destruct IH as (HF & HL). split; [| rewrite length_map; exact HL].
      rewrite Forall_map. eapply Forall_impl; [| exact HF].
      intros [Q Ee] Hq; cbn [fst prog_msr] in *; lia.
    - destruct IH as (HF & HL). split; [| rewrite length_map; exact HL].
      rewrite Forall_map. eapply Forall_impl; [| exact HF].
      intros [Q Ee] Hq; cbn [fst prog_msr] in *; lia.
    - pose proof (replace_leaf_msr _ _ _ _ HrS) as HS.
      pose proof (replace_leaf_msr _ _ _ _ HrR) as HR.
      rewrite !proc_msr_advance in HS, HR; cbn [proc_msr res_msr] in HS, HR.
      rewrite (picks_length _ _ _ HpS) in HS.
      rewrite (picks_length _ _ _ HpR) in HR.
      split; [| cbn; lia].
      repeat constructor; cbn [fst prog_msr]; lia.
    - pose proof (replace_leaf_msr _ _ _ _ HrS) as HS.
      pose proof (replace_leaf_msr _ _ _ _ HrR) as HR.
      rewrite !proc_msr_advance in HS, HR; cbn [proc_msr res_msr] in HS, HR.
      rewrite (picks_length _ _ _ HpS) in HS.
      rewrite (picks_length _ _ _ HpR) in HR.
      split; [| cbn; lia].
      repeat constructor; cbn [fst prog_msr]; lia.
  Qed.

  (** Components fork in two at worst, so weighting each by 3^(its measure)
      makes the whole configuration decrease: one weight 3^n is replaced by
      at most two of weight 3^(n-1), and 2·3^(n-1) < 3^n. *)
  Fixpoint cfg_msr (G : distri_config dim) : nat :=
    match G with
    | nil     => 0
    | c :: G' => (3 ^ (prog_msr (fst c)) + cfg_msr G')%nat
    end.

  Lemma cfg_msr_app : forall G1 G2,
      (cfg_msr (G1 ++ G2) = cfg_msr G1 + cfg_msr G2)%nat.
  Proof.
    intro G1; induction G1 as [| c G1 IH]; intro G2; cbn [app cfg_msr];
      [reflexivity | rewrite IH; lia].
  Qed.

  Lemma cfg_msr_perm : forall G G', Permutation G G' -> cfg_msr G = cfg_msr G'.
  Proof. intros G G' H; induction H; cbn [cfg_msr] in *; lia. Qed.

  Lemma cfg_msr_norm : forall G, (cfg_msr (norm G) <= cfg_msr G)%nat.
  Proof.
    intro G; induction G as [| [P E] G IH]; [cbn; lia |].
    unfold norm in *; cbn [filter snd].
    destruct E; cbn [cfg_msr fst]; lia.
  Qed.

  Lemma cfg_msr_bound : forall G n,
      Forall (fun c => (prog_msr (fst c) < n)%nat) G ->
      (cfg_msr G <= length G * 3 ^ (n - 1))%nat.
  Proof.
    intro G; induction G as [| c G IH]; intros n HF; cbn [cfg_msr length];
      [lia |].
    inversion HF as [| u v Hh Ht]; subst.
    specialize (IH n Ht).
    assert (Hp : (3 ^ (prog_msr (fst c)) <= 3 ^ (n - 1))%nat)
      by (apply Nat.pow_le_mono_r; lia).
    lia.
  Qed.

  Lemma mixed_step_msr : forall G G',
      mixed_step Σ G G' -> (cfg_msr G' < cfg_msr G)%nat.
  Proof.
    intros G G' H; inversion H as [Gx D E G0 G1 Hperm Hd Heq1 Heq2]; subst.
    destruct (distri_step_msr _ _ _ Hd) as (HF & HL).
    rewrite (cfg_msr_perm _ _ Hperm); cbn [cfg_msr fst].
    eapply Nat.le_lt_trans; [apply cfg_msr_norm |].
    rewrite cfg_msr_app.
    pose proof (cfg_msr_bound _ _ HF) as Hb.
    assert (Hnz : forall m, (0 < 3 ^ m)%nat).
    { intro m; assert (3 ^ m <> 0)%nat by (apply Nat.pow_nonzero; lia); lia. }
    assert (Hb2 : (cfg_msr G1 <= 2 * 3 ^ (prog_msr D - 1))%nat)
      by (eapply Nat.le_trans;
          [exact Hb | apply Nat.mul_le_mono_r; exact HL]).
    destruct G1 as [| c G1'].
    - cbn [cfg_msr]. pose proof (Hnz (prog_msr D)). lia.
    - inversion HF as [| u v Hh _]; subst.
      assert (He : (3 ^ prog_msr D = 3 * 3 ^ (prog_msr D - 1))%nat).
      { replace (prog_msr D) with (Datatypes.S (prog_msr D - 1)) at 1 by lia.
        cbn [Nat.pow]. reflexivity. }
      pose proof (Hnz ((prog_msr D - 1)%nat)).
      lia.
  Qed.


(** ** 19. Par-Comp-MP — configurations the semantics cannot tell apart *****

    The confluence argument cannot be stated on the nose.  Two steps at
    different components commute, but the two orders land on configurations
    that differ by the order of their components; two steps at the same
    component on different leaves commute by Lemma 1, whose conclusion is a
    [Permutation] of ensembles.  So the diamond closes up to [cfg_eq]: same
    components in some order, each holding the same states in some order.

    Everything the argument reads off a configuration — [terminal], the
    collapse, and the ability to take a step — is invariant under it.
*********************************************************************)

  (** ** An ensemble permutation propagates through one step *)

  Lemma ensemble_filter_perm : forall p (E E' : ensemble dim),
      Permutation E E' -> Permutation (ensemble_filter p E) (ensemble_filter p E').
  Proof. intros p E E' H; unfold ensemble_filter; apply permutation_filter, H. Qed.

  Lemma local_step_perm : forall L (E E' : ensemble dim) G,
      Permutation E E' ->
      Σ ⊳ ‹ L, E › →ₗ G ->
      exists G', Σ ⊳ ‹ L, E' › →ₗ G'
              /\ Forall2 (fun c c' => fst c = fst c'
                                      /\ Permutation (snd c) (snd c')) G G'.
  Proof.
    intros L E E' G Hp Hstep; revert E' Hp.
    induction Hstep as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      intros E' Hp.
    - eexists; split; [apply local_step_skip |].
      repeat constructor; exact Hp.
    - eexists; split; [apply local_step_assign |].
      repeat constructor; cbn [snd]; apply Permutation_map, Hp.
    - eexists; split; [apply local_step_init |].
      repeat constructor; cbn [snd]; apply Permutation_map, Hp.
    - eexists; split; [apply local_step_ugate |].
      repeat constructor; cbn [snd]; apply Permutation_map, Hp.
    - eexists; split; [apply local_step_meas |].
      repeat constructor; cbn [snd]; apply permutation_flat_map, Hp.
    - destruct (IH E' Hp) as (Gb & Hb & HF).
      exists (map (fun c => match fst c with
                            | r_done     => (r_more L2, snd c)
                            | r_more L1' => (r_more <{ L1' ; L2 }>, snd c)
                            end) Gb).
      split; [apply local_step_seq, Hb |].
      clear -HF. induction HF as [| c c' Ga Gb (H1 & H2) HF IH];
        cbn [map]; constructor; [| exact IH].
      destruct c as [R1 Ea1]; destruct c' as [R2 Ea2];
        cbn [fst snd] in H1, H2 |- *; subst R2;
        destruct R1; cbn [fst snd]; split;
        solve [reflexivity | exact H2].
    - eexists; split; [apply local_step_if |].
      cbn [app]; repeat constructor; cbn [snd];
        apply ensemble_filter_perm, Hp.
  Qed.

  Lemma distri_step_perm : forall P (E E' : ensemble dim) G,
      Permutation E E' ->
      Σ ⊳ ‹ P, E › ⇝ G ->
      exists G', Σ ⊳ ‹ P, E' › ⇝ G'
              /\ Forall2 (fun c c' => fst c = fst c'
                                      /\ Permutation (snd c) (snd c')) G G'.
  Proof.
    intros P E E' G Hp Hstep; revert E' Hp.
    induction Hstep as
      [ L K T E0 Gl Hloc
      | P1 P2 E0 Ga Hs IH
      | P1 P2 E0 Gb Hs IH
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR
      | P1 P1' P2 P2' Ks Ks' Kr Kr' Ts Tr c e x E0 HpS HpR HrS HrR ];
      intros E' Hp.
    - destruct (local_step_perm _ _ _ _ Hp Hloc) as (Gl' & Hl' & HF).
      exists (map (fun c => (⟨ advance (fst c) K T ⟩, snd c)) Gl').
      split; [apply ds_local, Hl' |].
      clear -HF. induction HF as [| c c' Ga Gb (H1 & H2) HF IH];
        cbn [map]; constructor; [| exact IH].
      destruct c as [R1 Ea1]; destruct c' as [R2 Ea2];
        cbn [fst snd] in H1, H2 |- *; subst R2;
        split; [reflexivity | exact H2].
    - destruct (IH E' Hp) as (Ga' & Ha & HF).
      exists (map (fun c => (fst c ∥ P2, snd c)) Ga').
      split; [apply ds_par_l, Ha |].
      clear -HF. induction HF as [| c c' Ga Gb (H1 & H2) HF IH];
        cbn [map]; constructor; [| exact IH].
      destruct c as [R1 Ea1]; destruct c' as [R2 Ea2];
        cbn [fst snd] in H1, H2 |- *; subst R2;
        split; [reflexivity | exact H2].
    - destruct (IH E' Hp) as (Gb' & Hb & HF).
      exists (map (fun c => (P1 ∥ fst c, snd c)) Gb').
      split; [apply ds_par_r, Hb |].
      clear -HF. induction HF as [| c c' Ga Gb (H1 & H2) HF IH];
        cbn [map]; constructor; [| exact IH].
      destruct c as [R1 Ea1]; destruct c' as [R2 Ea2];
        cbn [fst snd] in H1, H2 |- *; subst R2;
        split; [reflexivity | exact H2].
    - eexists; split; [eapply ds_comm_lr; eassumption |].
      repeat constructor; cbn [snd]; apply Permutation_map, Hp.
    - eexists; split; [eapply ds_comm_rl; eassumption |].
      repeat constructor; cbn [snd]; apply Permutation_map, Hp.
  Qed.

  (** Two configurations the semantics cannot tell apart: same components in
      some order, each holding the same states in some order.  The two
      branches of a diamond land on configurations related like this, never
      on the same one, which is why the whole confluence argument has to be
      stated up to it. *)
  Definition cpt_eq (c c' : program * ensemble dim) : Prop :=
    fst c = fst c' /\ Permutation (snd c) (snd c').

  Definition cfg_eq (G G' : distri_config dim) : Prop :=
    exists G0, Forall2 cpt_eq G G0 /\ Permutation G0 G'.

  Lemma cpt_eq_refl : forall c, cpt_eq c c.
  Proof. intro c; split; [reflexivity | apply Permutation_refl]. Qed.

  Lemma cpt_eq_trans : forall c1 c2 c3, cpt_eq c1 c2 -> cpt_eq c2 c3 -> cpt_eq c1 c3.
  Proof.
    intros c1 c2 c3 (H1 & H2) (H3 & H4).
    split; [congruence | eapply Permutation_trans; eassumption].
  Qed.

  Lemma Forall2_cpt_refl : forall G, Forall2 cpt_eq G G.
  Proof.
    intro G; induction G as [| c G IH]; constructor;
      [apply cpt_eq_refl | exact IH].
  Qed.

  Lemma cfg_eq_refl : forall G, cfg_eq G G.
  Proof. intro G; exists G; split; [apply Forall2_cpt_refl | apply Permutation_refl]. Qed.

  Lemma cfg_eq_perm : forall G G', Permutation G G' -> cfg_eq G G'.
  Proof. intros G G' H; exists G; split; [apply Forall2_cpt_refl | exact H]. Qed.

  Lemma cfg_eq_trans : forall G1 G2 G3, cfg_eq G1 G2 -> cfg_eq G2 G3 -> cfg_eq G1 G3.
  Proof.
    intros G1 G2 G3 (A & HA & PA) (B & HB & PB).
    destruct (Permutation_Forall2 (Permutation_sym PA) HB) as (B' & PB' & HB').
    exists B'. split.
    - clear -HA HB'. revert B' HB'; induction HA as [| c c' G1 A H HA IH];
        intros B' HB'; inversion HB' as [| u v l l' Hh Ht]; subst;
        constructor; [eapply cpt_eq_trans; eassumption | apply IH, Ht].
    - eapply Permutation_trans; [apply Permutation_sym, PB' | exact PB].
  Qed.

  (** ** What the relation preserves *)

  Lemma Forall2_cpt_terminal : forall G G',
      Forall2 cpt_eq G G' -> terminal G -> terminal G'.
  Proof.
    intros G G' H; induction H as [| c c' G G' (H1 & _) HF IH]; intro Ht;
      [constructor |].
    inversion Ht as [| u v Hh Htl]; subst.
    constructor; [rewrite <- H1; exact Hh | apply IH, Htl].
  Qed.

  Lemma cfg_eq_terminal : forall G G', cfg_eq G G' -> terminal G -> terminal G'.
  Proof.
    intros G G' (A & HA & PA) Ht.
    eapply Forall_perm; [exact PA | eapply Forall2_cpt_terminal; eassumption].
  Qed.

  Lemma Forall2_cpt_collapse : forall G G',
      Forall2 cpt_eq G G' -> Permutation (collapse G) (collapse G').
  Proof.
    intros G G' H; induction H as [| c c' G G' (_ & H2) HF IH];
      [apply Permutation_refl |].
    unfold collapse in *; cbn [flat_map].
    apply Permutation_app; [exact H2 | exact IH].
  Qed.

  Lemma cfg_eq_collapse : forall G G',
      cfg_eq G G' -> Permutation (collapse G) (collapse G').
  Proof.
    intros G G' (A & HA & PA).
    eapply Permutation_trans;
      [eapply Forall2_cpt_collapse, HA | apply collapse_perm, PA].
  Qed.

  Lemma Forall2_cpt_norm : forall G G',
      Forall2 cpt_eq G G' -> Forall2 cpt_eq (norm G) (norm G').
  Proof.
    intros G G' H; induction H as [| c c' G G' (H1 & H2) HF IH];
      [constructor |].
    destruct c as [Pc Ec]; destruct c' as [Pc' Ec'];
      cbn [fst snd] in H1, H2.
    unfold norm in *; cbn [filter snd].
    destruct Ec as [| st E1]; destruct Ec' as [| st' E2].
    - exact IH.
    - exfalso; exact (Permutation_nil_cons H2).
    - exfalso; exact (Permutation_nil_cons (Permutation_sym H2)).
    - constructor; [split; cbn [fst snd]; assumption | exact IH].
  Qed.

  Lemma mixed_step_cfg_eq : forall G G1 G',
      mixed_step Σ G G1 -> cfg_eq G G' ->
      exists G1', mixed_step Σ G' G1' /\ cfg_eq G1 G1'.
  Proof.
    intros G G1 G' Hstep (A & HA & PA).
    inversion Hstep as [Gx D E H0 K Hperm Hd Heq1 Heq2]; subst.
    destruct (Permutation_Forall2 Hperm HA) as (A' & PA' & HA').
    inversion HA' as [| u c' l l' Hc HF Eq1 Eq2]; subst.
    destruct c' as [D' E']; destruct Hc as (HD & HE);
      cbn [fst snd] in HD, HE; subst D'.
    destruct (distri_step_perm _ _ _ _ HE Hd) as (K' & Hd' & HK).
    exists (norm (K' ++ l')). split.
    - apply (mixed_lift Σ G' D E' l' K'); [| exact Hd'].
      eapply Permutation_trans; [apply Permutation_sym, PA | exact PA'].
    - exists (norm (K' ++ l')). split; [| apply Permutation_refl].
      apply Forall2_cpt_norm, Forall2_app; assumption.
  Qed.

  Lemma step_star_cfg_eq : forall G X,
      step_star Σ G X -> terminal X ->
      forall G', cfg_eq G G' ->
      exists X', step_star Σ G' X' /\ terminal X'
              /\ Permutation (collapse X') (collapse X).
  Proof.
    intros G X H; induction H as [G | G G1 X Hmix Hstar IH]; intros Ht G' Heq.
    - exists G'. split; [apply star_refl | split].
      + eapply cfg_eq_terminal; eassumption.
      + apply Permutation_sym, cfg_eq_collapse, Heq.
    - destruct (mixed_step_cfg_eq _ _ _ Hmix Heq) as (G1' & Hm' & Heq1).
      destruct (IH Ht G1' Heq1) as (X' & Hs' & Ht' & Hc').
      exists X'. split; [eapply star_step; eassumption | split; assumption].
  Qed.


(** ** 20. Par-Comp-MP — two local steps at different leaves commute ********

    The hard case of the diamond.  Lemma 1 ([denote_comm]) says two
    non-interfering blocks agree on the TOTAL ensemble; the diamond needs
    them to agree BRANCH BY BRANCH, since each branch has to go on running
    separately.

    [lstep] is [local_step] as a function — legitimate, since the relation is
    total and deterministic — which is what makes the statement bearable:
    [lstep2 L1 L2 E] is the list of (residual, residual, ensemble) a run of
    L1 then L2 produces, and the claim is that transposing the two labels
    turns it into the list for L2 then L1, up to [lst_eq].

    The induction is on L1 alone.  Its three cases are exactly the three
    facts already available: the atomic case IS §17's
    [local_step_denote_branch]; [seq] only relabels the first component, so
    the induction hypothesis carries it; and [if] contributes a filter, which
    commutes with the other step's branches by [local_step_filter] — on the
    nose, not up to permutation, because filtering does not reorder.
*********************************************************************)

  (** The step as a function.  [local_step] is total and deterministic, so
      nothing is lost, and the swap lemma below is far easier to state about
      a function than about two existentials. *)
  Fixpoint lstep (L : lblock) (E : ensemble dim) : local_config dim :=
    match L with
    | l_skip       => {|| ↓, E ||}
    | l_assign x e =>
        {|| ↓, map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
    | l_init q     => {|| ↓, map (fun '(s,r) => (s, apply_init q r)) E ||}
    | l_ugate U qs =>
        {|| ↓, map (fun '(s,r) => (s, apply_unitary (i_uu Σ U qs) r)) E ||}
    | l_meas x M qs =>
        {|| ↓, flat_map (fun '(s,r) =>
                 map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r))
                     (fst (i_mm Σ M qs))) E ||}
    | l_seq L1 L2  =>
        map (fun c => match fst c with
                      | r_done     => (r_more L2, snd c)
                      | r_more L1' => (r_more <{ L1' ; L2 }>, snd c)
                      end) (lstep L1 E)
    | l_if b L1 L0 =>
        {|| r_more L1,
            ensemble_filter (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E ||}
        ⊎ {|| r_more L0,
              ensemble_filter
                (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E ||}
    end.

  Lemma lstep_step : forall L E, Σ ⊳ ‹ L, E › →ₗ lstep L E.
  Proof.
    induction L as [| x e | q | U qs | x M qs | L1 IH1 L2 IH2 | b L1 IH1 L0 IH0];
      intro E; cbn [lstep].
    - apply local_step_skip.
    - apply local_step_assign.
    - apply local_step_init.
    - apply local_step_ugate.
    - apply local_step_meas.
    - apply local_step_seq, IH1.
    - apply local_step_if.
  Qed.

  Lemma lstep_eq : forall L E G, Σ ⊳ ‹ L, E › →ₗ G -> G = lstep L E.
  Proof.
    intros L E G H; exact (local_step_det _ _ _ _ H (lstep_step L E)).
  Qed.

  Lemma lstep_atomic : forall L E,
      atomic L -> lstep L E = {|| ↓, denote L E ||}.
  Proof.
    intros [| x e | q | U qs | x M qs | L1 L2 | b L1 L0] E Ha;
      try contradiction; reflexivity.
  Qed.

  (** A step's branches commute with a filter its block cannot see. *)
  Lemma local_step_filter : forall p L (E : ensemble dim) G,
      store_indep p (lblock_change L) ->
      Σ ⊳ ‹ L, E › →ₗ G ->
      exists G', Σ ⊳ ‹ L, ensemble_filter p E › →ₗ G'
              /\ Forall2 (fun c c' => fst c = fst c'
                                      /\ snd c' = ensemble_filter p (snd c)) G G'.
  Proof.
    intros p L E G Hind Hstep; revert Hind.
    induction Hstep as
      [ Ea | x e Ea | q Ea | U qs Ea | x M qs Ea
      | L1 L2 Ea Ga Hs IH | b L1 L0 Ea ];
      intro Hind.
    - eexists; split; [apply local_step_skip |].
      repeat constructor.
    - eexists; split; [apply local_step_assign |].
      repeat constructor; cbn [snd].
      symmetry; exact (denote_filter_comm p (l_assign x e) Ea Hind).
    - eexists; split; [apply local_step_init |].
      repeat constructor; cbn [snd].
      symmetry; exact (denote_filter_comm p (l_init q) Ea Hind).
    - eexists; split; [apply local_step_ugate |].
      repeat constructor; cbn [snd].
      symmetry; exact (denote_filter_comm p (l_ugate U qs) Ea Hind).
    - eexists; split; [apply local_step_meas |].
      repeat constructor; cbn [snd].
      symmetry; exact (denote_filter_comm p (l_meas x M qs) Ea Hind).
    - cbn [lblock_change] in Hind.
      destruct (store_indep_app _ _ _ Hind) as (H1 & _).
      destruct (IH H1) as (Gb & Hb & HF).
      exists (map (fun c => match fst c with
                            | r_done     => (r_more L2, snd c)
                            | r_more L1' => (r_more <{ L1' ; L2 }>, snd c)
                            end) Gb).
      split; [apply local_step_seq, Hb |].
      clear -HF. induction HF as [| c c' Ga Gb (H1 & H2) HF IH];
        cbn [map]; constructor; [| exact IH].
      destruct c as [R1 Ea1]; destruct c' as [R2 Ea2];
        cbn [fst snd] in H1, H2 |- *; subst R2 Ea2;
        destruct R1; cbn [fst snd]; split; reflexivity.
    - cbn [lblock_change] in Hind.
      destruct (store_indep_app _ _ _ Hind) as (H1 & H0).
      eexists; split; [apply local_step_if |].
      cbn [app]; repeat constructor; cbn [snd];
        apply ensemble_filter_comm.
  Qed.

  (** §19's [cfg_eq] at an arbitrary label type: the two branches of a
      diamond are lists of (label, ensemble) pairs agreeing up to the order
      of the list and of each ensemble. *)
  Definition pt_eq {A} (c c' : A * ensemble dim) : Prop :=
    fst c = fst c' /\ Permutation (snd c) (snd c').

  Definition lst_eq {A} (l l' : list (A * ensemble dim)) : Prop :=
    exists l0, Forall2 pt_eq l l0 /\ Permutation l0 l'.

  Lemma Forall2_map2 : forall {A B C D} (R : C -> D -> Prop)
                              (f : A -> C) (g : B -> D) l1 l2,
      Forall2 (fun a b => R (f a) (g b)) l1 l2 ->
      Forall2 R (map f l1) (map g l2).
  Proof.
    intros A B C D R f g l1 l2 H; induction H; cbn [map]; constructor;
      assumption.
  Qed.

  Lemma lst_eq_of_forall2 : forall {A} (l l' : list (A * ensemble dim)),
      Forall2 pt_eq l l' -> lst_eq l l'.
  Proof. intros A l l' H; exists l'; split; [exact H | apply Permutation_refl]. Qed.

  Lemma lst_eq_perm_r : forall {A} (l l' l'' : list (A * ensemble dim)),
      lst_eq l l' -> Permutation l' l'' -> lst_eq l l''.
  Proof.
    intros A l l' l'' (l0 & H0 & P0) P.
    exists l0; split; [exact H0 | eapply Permutation_trans; eassumption].
  Qed.

  (** ** The two-step product, and its transpose *)

  Definition lstep2 (L1 L2 : lblock) (E : ensemble dim)
    : list ((residual * residual) * ensemble dim) :=
    flat_map (fun c => map (fun d => ((fst c, fst d), snd d)) (lstep L2 (snd c)))
             (lstep L1 E).

  Definition swap_tri (t : (residual * residual) * ensemble dim)
    : (residual * residual) * ensemble dim :=
    ((snd (fst t), fst (fst t)), snd t).

  Lemma flat_map_singleton : forall {A B} (f : A -> B) (l : list A),
      flat_map (fun a => f a :: nil) l = map f l.
  Proof.
    intros A B f l; induction l as [| a l IH]; cbn [flat_map map];
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  (** The atomic case, which is where [local_step_denote_branch] pays. *)
  Lemma lstep_swap_atomic : local_ops ->
    forall L1 L2 E, atomic L1 -> non_interfering L1 L2 ->
      lst_eq (lstep2 L1 L2 E) (map swap_tri (lstep2 L2 L1 E)).
  Proof.
    intros Hloc L1 L2 E Ha Hni.
    destruct (local_step_denote_branch Hloc L1 L2 E (lstep L2 E) (non_interfering_sym _ _ Hni)
                (lstep_step L2 E)) as (Gl' & Hs' & Hm' & HF').
    rewrite (lstep_eq _ _ _ Hs') in Hm', HF'.
    apply lst_eq_of_forall2.
    unfold lstep2; rewrite (lstep_atomic L1 E Ha).
    cbn [flat_map app].
    rewrite app_nil_r.
    (* the right-hand side collapses to a map as well *)
    replace (map swap_tri
               (flat_map (fun d => map (fun c => ((fst d, fst c), snd c))
                            (lstep L1 (snd d))) (lstep L2 E)))
      with (map (fun d => ((r_done, fst d), denote L1 (snd d))) (lstep L2 E)).
    2:{ erewrite flat_map_ext'
          with (g := fun d => ((fst d, r_done), denote L1 (snd d)) :: nil)
          by (intro d; rewrite (lstep_atomic L1 (snd d) Ha); reflexivity).
        rewrite flat_map_singleton, map_map. reflexivity. }
    apply Forall2_map2; cbn [fst snd].
    (* fst agrees by the shape, snd by the branch-wise commutation *)
    clear -Hm' HF'. revert Hm' HF'.
    generalize (lstep L2 E) as A; generalize (lstep L2 (denote L1 E)) as B.
    intros B A Hm HF.
    induction HF as [| c c' A B H HF IH]; constructor.
    - cbn [map] in Hm; injection Hm as Hf Hm'.
      split; [cbn [fst]; rewrite Hf; reflexivity | cbn [snd]; apply Permutation_sym, H].
    - cbn [map] in Hm; injection Hm as _ Hm'. apply IH, Hm'.
  Qed.

  Lemma lst_eq_map : forall {A B} (g : A -> B) (l l' : list (A * ensemble dim)),
      lst_eq l l' ->
      lst_eq (map (fun c => (g (fst c), snd c)) l)
             (map (fun c => (g (fst c), snd c)) l').
  Proof.
    intros A B g l l' (l0 & H0 & P0).
    exists (map (fun c => (g (fst c), snd c)) l0).
    split; [| apply Permutation_map, P0]. clear P0.
    induction H0 as [| c c' l l0 (H1 & H2) HF2 IH]; cbn [map]; [constructor |].
    constructor; [| exact IH].
    split; cbn [fst snd]; [rewrite H1; reflexivity | exact H2].
  Qed.

  Lemma flat_map_pair_perm : forall {A B} (f g : A -> B) (l : list A),
      Permutation (flat_map (fun a => f a :: g a :: nil) l)
                  (map f l ++ map g l).
  Proof.
    intros A B f g l; induction l as [| a l IH]; cbn [flat_map map app];
      [apply Permutation_refl |].
    apply perm_skip.
    eapply Permutation_trans; [apply perm_skip, IH | apply Permutation_middle].
  Qed.

  Lemma lstep_seq_shape : forall A B E,
      lstep <{ A ; B }> E
      = map (fun c => (match fst c with
                       | r_done   => r_more B
                       | r_more A' => r_more <{ A' ; B }>
                       end, snd c)) (lstep A E).
  Proof.
    intros A B E; cbn [lstep]. apply map_ext; intros [R Ea];
      destruct R; reflexivity.
  Qed.

  Lemma Forall2_eq_map : forall {A B} (f : A -> B) (l : list A) (l' : list B),
      Forall2 (fun a b => b = f a) l l' -> l' = map f l.
  Proof.
    intros A B f l l' H; induction H as [| a b l l' Hh HF IH]; cbn [map];
      [reflexivity | rewrite Hh, IH; reflexivity].
  Qed.

  Lemma Forall2_pt_refl : forall {A} (l : list (A * ensemble dim)),
      Forall2 pt_eq l l.
  Proof.
    intros A l; induction l as [| c l IH]; [constructor |].
    constructor; [split; [reflexivity | apply Permutation_refl] | exact IH].
  Qed.

  Lemma lstep_swap : local_ops ->
    forall L1 L2 E, non_interfering L1 L2 ->
      lst_eq (lstep2 L1 L2 E) (map (swap_tri) (lstep2 L2 L1 E)).
  Proof.
    intros Hloc L1; induction L1 as
      [| x e | q | U qs | x M qs | A IHA B IHB | b A IHA B IHB ];
      intros L2 E Hni.
    1-5: apply lstep_swap_atomic; solve [exact Hloc | exact Hni | exact Logic.I].
    - (* L1 = A ; B : the relabelling touches only the first label *)
      destruct (non_interfering_seq _ _ _ Hni) as (HA & _).
      pose proof (IHA L2 E HA) as IH.
      set (rf := fun R => match R with
                          | r_done    => r_more B
                          | r_more A' => r_more <{ A' ; B }>
                          end).
      set (gf := fun lab : residual * residual => (rf (fst lab), snd lab)).
      set (F := fun t : (residual * residual) * ensemble dim =>
                  (gf (fst t), snd t)).
      assert (HL : lstep2 <{ A ; B }> L2 E = map F (lstep2 A L2 E)).
      { unfold lstep2, F. rewrite lstep_seq_shape, flat_map_map, map_flat_map.
        apply flat_map_ext'; intro c.
        rewrite map_map. apply map_ext; intro d.
        unfold gf, rf; cbn [fst snd]; destruct (fst c); reflexivity. }
      assert (HR : map swap_tri (lstep2 L2 <{ A ; B }> E)
                   = map F (map swap_tri (lstep2 L2 A E))).
      { unfold lstep2, F. rewrite map_flat_map, map_map, map_flat_map.
        apply flat_map_ext'; intro d.
        rewrite lstep_seq_shape, !map_map. apply map_ext; intro c.
        unfold swap_tri, gf, rf; cbn [fst snd]; destruct (fst c); reflexivity. }
      rewrite HL, HR. apply (lst_eq_map gf), IH.
    - (* L1 = if b then A else B : the filter is the whole content *)
      pose proof (non_interfering_guard _ _ _ _ Hni) as Hg.
      set (pb := fun s => eval_bool (i_fn Σ) (i_rl Σ) s b).
      set (pn := fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)).
      destruct (local_step_filter pb L2 E (lstep L2 E)
                  (store_indep_guard b _ Hg) (lstep_step L2 E))
        as (Gb & Hb & HFb).
      destruct (local_step_filter pn L2 E (lstep L2 E)
                  (store_indep_negb _ _ (store_indep_guard b _ Hg))
                  (lstep_step L2 E))
        as (Gn & Hn & HFn).
      rewrite (lstep_eq _ _ _ Hb) in HFb.
      rewrite (lstep_eq _ _ _ Hn) in HFn.
      (* each filtered step IS the filter of the step, on the nose *)
      assert (Eb : lstep L2 (ensemble_filter pb E)
                   = map (fun c => (fst c, ensemble_filter pb (snd c)))
                         (lstep L2 E)).
      { apply Forall2_eq_map. eapply Forall2_impl; [| exact HFb].
        intros c c' (H1 & H2); destruct c as [R Ea]; destruct c' as [R' Ea'];
          cbn [fst snd] in H1, H2 |- *; subst; reflexivity. }
      assert (En : lstep L2 (ensemble_filter pn E)
                   = map (fun c => (fst c, ensemble_filter pn (snd c)))
                         (lstep L2 E)).
      { apply Forall2_eq_map. eapply Forall2_impl; [| exact HFn].
        intros c c' (H1 & H2); destruct c as [R Ea]; destruct c' as [R' Ea'];
          cbn [fst snd] in H1, H2 |- *; subst; reflexivity. }
      eapply lst_eq_perm_r; [apply lst_eq_of_forall2, Forall2_pt_refl |].
      unfold lstep2 at 1; cbn [lstep]; cbn [flat_map app fst snd].
      rewrite app_nil_r. unfold pb, pn in Eb, En.
      rewrite Eb, En, !map_map.
      unfold lstep2; rewrite map_flat_map.
      erewrite flat_map_ext' with
        (g := fun d => ((r_more A, fst d), ensemble_filter pb (snd d))
                       :: ((r_more B, fst d), ensemble_filter pn (snd d)) :: nil).
      2:{ intro d; cbn [lstep]; cbn [map app swap_tri fst snd]; reflexivity. }
      apply Permutation_sym, flat_map_pair_perm.
  Qed.


(** ** 21. Par-Comp-MP — the other two commutations, and a whole-row step ***

    A3 and A4 of the diamond, both of which reduce to something already
    proven: a rendezvous only rewrites the store, so §9's [local_step_rmap]
    is already branch-wise, and two rendezvous commute exactly when their
    substitutions do ([rmap_comm], §7).

    [step_star_cfg] is §19's [cfg_eq] transport without the terminality
    assumption — the diamond's two branches meet in mid-run, not at the end.
    [step_star_each] then steps every component of a configuration in one go,
    which is how a branch of the diamond catches up with the other: the first
    step forked the configuration, so the second has to be taken in each fork.
*********************************************************************)

  (** A3.  A local step and a rendezvous at other leaves commute ON THE
      NOSE — a rendezvous only rewrites the store, so §9 already gives the
      branch-wise statement. *)
  Lemma lstep_rmap : forall L x e (E : ensemble dim),
      rdv_indep L x e ->
      lstep L (rmap x e E)
      = map (fun c => (fst c, rmap x e (snd c))) (lstep L E).
  Proof.
    intros L x e E Hind. symmetry.
    apply (lstep_eq), (local_step_rmap L x e E (lstep L E) Hind
                           (lstep_step L E)).
  Qed.

  (** A4.  Two rendezvous commute when their substitutions do. *)
  Lemma rmap_swap : forall x1 e1 x2 e2 (E : ensemble dim),
      x1 <> x2 -> ~ In x1 (expr_vars e2) -> ~ In x2 (expr_vars e1) ->
      rmap x2 e2 (rmap x1 e1 E) = rmap x1 e1 (rmap x2 e2 E).
  Proof. intros; apply rmap_comm; assumption. Qed.

  (** ** [cfg_eq] travels along a whole run, terminal or not.

      §19's version stops at a terminal configuration, which is what the
      normalisation needed; the diamond needs the general one, since the two
      branches meet in mid-run. *)
  Lemma cfg_eq_sym : forall G G' : distri_config dim,
      cfg_eq G G' -> cfg_eq G' G.
  Proof.
    intros G G' (G0 & HF & HP).
    assert (HFs : Forall2 cpt_eq G0 G).
    { clear -HF. induction HF as [| c c' l l' (H1 & H2) HF IH]; constructor;
        [split; [symmetry; exact H1 | apply Permutation_sym, H2] | exact IH]. }
    destruct (Permutation_Forall2 HP HFs) as (G1 & HP1 & HF1).
    exists G1. split; [exact HF1 | apply Permutation_sym, HP1].
  Qed.

  Lemma step_star_cfg : forall G X,
      step_star Σ G X ->
      forall G' : distri_config dim,
        cfg_eq G G' -> exists X', step_star Σ G' X' /\ cfg_eq X X'.
  Proof.
    intros G X H; induction H as [G | G G1 X Hmix Hstar IH]; intros G' Heq.
    - exists G'. split; [apply star_refl | exact Heq].
    - destruct (mixed_step_cfg_eq _ _ _ Hmix Heq) as (G1' & Hm' & Heq1).
      destruct (IH G1' Heq1) as (X' & Hs' & Heq2).
      exists X'. split; [eapply star_step; eassumption | exact Heq2].
  Qed.

  (** ** Stepping every component of a configuration, in one go *)

  Lemma norm_nonempty : forall G : distri_config dim,
      Forall (fun c => snd c <> nil) G -> norm G = G.
  Proof.
    intro G; induction G as [| c G IH]; intro H; [reflexivity |].
    inversion H as [| u v Hh Ht]; subst.
    destruct c as [P E]; cbn [snd] in Hh.
    destruct E as [| st E0]; [exfalso; apply Hh; reflexivity |].
    unfold norm in *; cbn [filter snd].
    f_equal; exact (IH Ht).
  Qed.

  Lemma step_star_each : forall (f : program * ensemble dim -> distri_config dim)
                                (G : distri_config dim),
      (forall c, In c G -> Σ ⊳ ‹ fst c, snd c › ⇝ f c) ->
      Forall (fun c => snd c <> nil) G ->
      exists X, step_star Σ G X /\ cfg_eq X (norm (flat_map f G)).
  Proof.
    intros f G; induction G as [| c G IH]; intros Hf Hn.
    - exists nil. split; [apply star_refl | apply cfg_eq_refl].
    - assert (Hc : Σ ⊳ ‹ fst c, snd c › ⇝ f c) by (apply Hf; left; reflexivity).
      inversion Hn as [| u v Hhd Htl]; subst.
      assert (HnG : norm G = G) by (apply norm_nonempty, Htl).
      destruct (IH (fun d Hd => Hf d (or_intror Hd)) Htl) as (Y & HY & HeqY).
      pose proof (step_star_frame_l _ _ HY HnG (norm (f c)) (norm_idem _))
        as Hfr.
      destruct (step_star_cfg _ _ Hfr (norm (f c) ++ G)
                  (cfg_eq_perm _ _ (Permutation_app_comm _ _)))
        as (X & HX & HeqX).
      exists X. split.
      + eapply star_step; [| exact HX].
        assert (Hstep := mixed_lift Σ (c :: G) (fst c) (snd c) G (f c)
                           ltac:(destruct c; apply Permutation_refl) Hc).
        rewrite norm_app, HnG in Hstep. exact Hstep.
      + eapply cfg_eq_trans; [apply cfg_eq_sym, HeqX |].
        cbn [flat_map]; rewrite norm_app.
        eapply cfg_eq_trans; [| apply cfg_eq_perm, Permutation_app_comm].
        destruct HeqY as (Y0 & HFY & HPY).
        exists (Y0 ++ norm (f c)). split.
        * clear -HFY. induction HFY as [| a b l l' Hab HF IHf];
            cbn [app]; [apply Forall2_cpt_refl | constructor; assumption].
        * apply Permutation_app_tail, HPY.
  Qed.


(** ** 22. Par-Comp-MP — two steps at different components ******************

    The last shape the diamond needs.  Both [mixed_step]s select their
    component only up to permutation, so "they picked different components"
    is not a case distinction the syntax offers: it has to be recovered from
    the two permutations, and that is what this decomposition does — either
    the two heads are the same element (and the tails agree), or each tail
    contains the other head.
*********************************************************************)

  Lemma Permutation_cons_inv_two : forall {A} (a1 a2 : A) l1 l2,
      Permutation (a1 :: l1) (a2 :: l2) ->
      (a1 = a2 /\ Permutation l1 l2)
      \/ (exists l', Permutation l1 (a2 :: l') /\ Permutation l2 (a1 :: l')).
  Proof.
    intros A a1 a2 l1 l2 Hp.
    assert (Hin : In a2 (a1 :: l1))
      by (eapply Permutation_in; [apply Permutation_sym, Hp | left; reflexivity]).
    destruct Hin as [Heq | Hin].
    - left. split; [exact Heq |].
      subst a2. exact (Permutation_cons_inv Hp).
    - right. apply in_split in Hin as (B1 & B2 & HB); subst l1.
      exists (B1 ++ B2). split; [apply Permutation_sym, Permutation_middle |].
      (* a1 :: B1 ++ a2 :: B2  ~  a2 :: l2, so peel a2 off both sides *)
      assert (H2 : Permutation (a2 :: a1 :: B1 ++ B2) (a2 :: l2)).
      { eapply Permutation_trans; [| exact Hp].
        eapply Permutation_trans; [apply perm_swap |].
        apply perm_skip, Permutation_middle. }
      apply Permutation_sym, (Permutation_cons_inv H2).
  Qed.


(** ** 23. Par-Comp-MP — the diamond, at configuration level ***************

    §20 and §21 commute the ENSEMBLE effects of two steps; this lifts them to
    whole configurations, where the programs also have to line up.  That part
    is [set_at_comm] throughout: two steps at different leaves write at
    different positions, so the two orders build the same tree.

    Two of the three cases close on the nose.  Only the local/local one needs
    [cfg_eq], and only because Lemma 1's conclusion is a permutation — which
    is why [lstep_swap] was stated up to [lst_eq] in the first place.
*********************************************************************)

  (** The configuration a local step at one leaf produces. *)
  Definition dstep_local (P : program) (p : path) (K : cblock) (T : process)
                         (G : local_config dim) : distri_config dim :=
    map (fun c => (set_at P p (advance (fst c) K T), snd c)) G.

  Lemma cfg_eq_lst : forall l l' : distri_config dim,
      lst_eq l l' -> cfg_eq l l'.
  Proof. intros l l' H; exact H. Qed.

  (** A2 at configuration level. *)
  Lemma diamond_local_local : local_ops ->
    forall P p q Lp Kp Tp Lq Kq Tq (E : ensemble dim),
      p <> q -> non_interfering Lp Lq ->
      cfg_eq
        (flat_map (fun c => dstep_local (fst c) q Kq Tq (lstep Lq (snd c)))
                  (dstep_local P p Kp Tp (lstep Lp E)))
        (flat_map (fun c => dstep_local (fst c) p Kp Tp (lstep Lp (snd c)))
                  (dstep_local P q Kq Tq (lstep Lq E))).
  Proof.
    intros Hloc P p q Lp Kp Tp Lq Kq Tq E Hne Hni.
    set (g := fun lab : residual * residual =>
                set_at (set_at P p (advance (fst lab) Kp Tp)) q
                       (advance (snd lab) Kq Tq)).
    assert (HL : flat_map (fun c => dstep_local (fst c) q Kq Tq
                                      (lstep Lq (snd c)))
                   (dstep_local P p Kp Tp (lstep Lp E))
                 = map (fun t => (g (fst t), snd t)) (lstep2 Lp Lq E)).
    { unfold dstep_local, lstep2, g.
      rewrite flat_map_map, map_flat_map.
      apply flat_map_ext'; intro c; rewrite !map_map; cbn [fst snd].
      apply map_ext; intro d; reflexivity. }
    assert (HR : flat_map (fun c => dstep_local (fst c) p Kp Tp
                                      (lstep Lp (snd c)))
                   (dstep_local P q Kq Tq (lstep Lq E))
                 = map (fun t => (g (fst t), snd t))
                       (map (swap_tri) (lstep2 Lq Lp E))).
    { unfold dstep_local, lstep2, g.
      rewrite flat_map_map, map_map, map_flat_map.
      apply flat_map_ext'; intro d; rewrite !map_map; cbn [fst snd].
      apply map_ext; intro c; unfold swap_tri; cbn [fst snd].
      rewrite set_at_comm by (intro Hc; apply Hne; symmetry; exact Hc).
      reflexivity. }
    rewrite HL, HR.
    apply cfg_eq_lst, (lst_eq_map g), (lstep_swap Hloc); exact Hni.
  Qed.

  (** The configuration a rendezvous produces. *)
  Definition dstep_comm (P : program) (ps pr : path)
                        (Ks' Kr' : cblock) (Ts Tr : process)
                        (x : var) (e : expr) (E : ensemble dim)
    : distri_config dim :=
    {|| set_at (set_at P ps (advance r_done Ks' Ts)) pr
               (advance r_done Kr' Tr),
        rmap x e E ||}.

  (** A3 at configuration level: a rendezvous only rewrites the store, so the
      two orders agree on the nose. *)
  Lemma diamond_local_comm : forall P p Lp Kp Tp qs qr Ks' Kr' Ts Tr x e
                                    (E : ensemble dim),
      p <> qs -> p <> qr -> rdv_indep Lp x e ->
      flat_map (fun c => dstep_comm (fst c) qs qr Ks' Kr' Ts Tr x e (snd c))
               (dstep_local P p Kp Tp (lstep Lp E))
      = dstep_local (set_at (set_at P qs (advance r_done Ks' Ts)) qr
                            (advance r_done Kr' Tr))
                    p Kp Tp (lstep Lp (rmap x e E)).
  Proof.
    intros P p Lp Kp Tp qs qr Ks' Kr' Ts Tr x e E Hs Hr Hind.
    unfold dstep_local, dstep_comm.
    rewrite (lstep_rmap Lp x e E Hind), flat_map_map, !map_map.
    rewrite flat_map_singleton.
    apply map_ext; intro c; cbn [fst snd].
    rewrite (set_at_comm _ p qs) by exact Hs.
    rewrite (set_at_comm _ p qr) by exact Hr.
    reflexivity.
  Qed.

  (** A4 at configuration level. *)
  Lemma diamond_comm_comm : forall P ps pr qs qr Ks' Kr' Ts Tr Ls' Lr' Us Ur
                                   x1 e1 x2 e2 (E : ensemble dim),
      ps <> qs -> ps <> qr -> pr <> qs -> pr <> qr ->
      x1 <> x2 -> ~ In x1 (expr_vars e2) -> ~ In x2 (expr_vars e1) ->
      flat_map (fun c => dstep_comm (fst c) qs qr Ls' Lr' Us Ur x2 e2 (snd c))
               (dstep_comm P ps pr Ks' Kr' Ts Tr x1 e1 E)
      = flat_map (fun c => dstep_comm (fst c) ps pr Ks' Kr' Ts Tr x1 e1 (snd c))
                 (dstep_comm P qs qr Ls' Lr' Us Ur x2 e2 E).
  Proof.
    intros P ps pr qs qr Ks' Kr' Ts Tr Ls' Lr' Us Ur x1 e1 x2 e2 E
           H1 H2 H3 H4 Hx He1 He2.
    unfold dstep_comm; cbn [flat_map fst snd app].
    rewrite (rmap_swap x1 e1 x2 e2 E Hx He1 He2).
    rewrite (set_at_comm _ pr qs) by exact H3.
    rewrite (set_at_comm _ ps qs) by exact H1.
    rewrite (set_at_comm _ pr qr) by exact H4.
    rewrite (set_at_comm _ ps qr) by exact H2.
    reflexivity.
  Qed.


(** ** 24. Par-Comp-MP — a rendezvous, and when two of them commute ********

    §23's [diamond_comm_comm] asks for four DISTINCT positions, and that is
    not the general case: one leaf may send on one channel and receive on
    another, so two available rendezvous can share a leaf.  Writing the step
    as [set_at] at a path cannot see that — the two writes land on the same
    position and do not commute.

    So the endpoint selection is recast as [ppick], the program-level twin of
    [kpick], and its confluence is [kpick_confluent] word for word: the leaf
    case is [picks_confluent], which is exactly where two endpoints of ONE
    leaf are handled.  A rendezvous is then two [ppick]s, and the two
    questions the diamond asks — "is it the same step?" and "do the two
    substitutions commute?" — are answered by channel uniqueness and by
    ownership together with a leaf-local independence condition.
*********************************************************************)

  (** ** Taking one endpoint out of a leaf's DISPLAYED block.

      The row-level companion of [picks], as [kpick] is for K-rows — except
      that the leaf here is a whole process, so [advance] may drop the phase
      when its block runs out.  The path is carried, because the semantics
      needs the two endpoints of a rendezvous to sit at DIFFERENT leaves and
      the confluence has to produce the same positions again. *)
  Inductive ppick : program -> path -> caction -> program -> Prop :=
  | pp_here : forall K a K' T,
      K ∋ a □ K' ->
      ppick (leaf (phase r_done K T)) ph_here a (leaf (advance r_done K' T))
  | pp_left : forall P1 P2 p a P1',
      ppick P1 p a P1' -> ppick (par P1 P2) (ph_l p) a (par P1' P2)
  | pp_right : forall P1 P2 p a P2',
      ppick P2 p a P2' -> ppick (par P1 P2) (ph_r p) a (par P1 P2').

  (** ** The bridge to [leaf_at]/[set_at], which is how the semantics states
         the same step *)

  Lemma picks_nonnil : forall K a K', K ∋ a □ K' -> K <> nil.
  Proof. intros K a K' H; destruct H; discriminate. Qed.

  Lemma advance_done_nonnil : forall K T,
      K <> nil -> advance r_done K T = phase r_done K T.
  Proof. intros [| a K] T H; [contradiction | reflexivity]. Qed.

  Lemma ppick_intro : forall P p K T a K',
      leaf_at P p = Some (phase r_done K T) -> K ∋ a □ K' ->
      ppick P p a (set_at P p (advance r_done K' T)).
  Proof.
    intro P; induction P as [S | P1 IH1 P2 IH2]; intros [| p' | p'] K T a K' Hl Hp;
      cbn in Hl; try discriminate.
    - injection Hl as HS; subst S; cbn [set_at]. apply pp_here, Hp.
    - cbn [set_at]. apply pp_left, (IH1 p' K T a K' Hl Hp).
    - cbn [set_at]. apply pp_right, (IH2 p' K T a K' Hl Hp).
  Qed.

  Lemma ppick_elim : forall P p a P',
      ppick P p a P' ->
      exists K T K', leaf_at P p = Some (phase r_done K T)
                  /\ K ∋ a □ K'
                  /\ P' = set_at P p (advance r_done K' T).
  Proof.
    intros P p a P' H;
      induction H as [K a K' T Hp | P1 P2 p a P1' H IH | P1 P2 p a P2' H IH].
    - exists K, T, K'. split; [reflexivity | split; [exact Hp | reflexivity]].
    - destruct IH as (K & T & K' & Hl & Hp & He).
      exists K, T, K'. split; [exact Hl | split; [exact Hp |]].
      cbn [set_at]; rewrite <- He; reflexivity.
    - destruct IH as (K & T & K' & Hl & Hp & He).
      exists K, T, K'. split; [exact Hl | split; [exact Hp |]].
      cbn [set_at]; rewrite <- He; reflexivity.
  Qed.

  (** ** Confluence.  Word for word [kpick_confluent]; the leaf case is where
         two endpoints of the SAME leaf are handled, which is exactly what a
         path-indexed [set_at] argument cannot see. *)

  Lemma ppick_confluent : forall P p a P1,
      ppick P p a P1 ->
      forall q b P2, ppick P q b P2 ->
        caction_chan a <> caction_chan b ->
        exists P12, ppick P1 q b P12 /\ ppick P2 p a P12.
  Proof.
    intros P p a P1 H1;
      induction H1 as [K a K1 T Hpk | PA PB p a PA' H1 IH | PA PB p a PB' H1 IH];
      intros q b P2 H2 Hne.
    - inversion H2 as [Kx bx Kx' Tx Hpk2 Eq1 Eq2 | |]; subst.
      destruct (picks_confluent _ _ _ Hpk _ _ Hpk2 Hne) as (K12 & Hb & Ha).
      exists (leaf (advance r_done K12 T)). split.
      + rewrite (advance_done_nonnil K1 T (picks_nonnil _ _ _ Hb)).
        apply pp_here, Hb.
      + rewrite (advance_done_nonnil Kx' T (picks_nonnil _ _ _ Ha)).
        apply pp_here, Ha.
    - inversion H2 as [| PX PY qx bx PX' H2' Eq1 Eq2
                       | PX PY qx bx PY' H2' Eq1 Eq2]; subst.
      + destruct (IH _ _ _ H2' Hne) as (P12 & Hb & Ha).
        exists (par P12 PB). split; apply pp_left; assumption.
      + exists (par PA' PY'). split; [apply pp_right, H2' | apply pp_left, H1].
    - inversion H2 as [| PX PY qx bx PX' H2' Eq1 Eq2
                       | PX PY qx bx PY' H2' Eq1 Eq2]; subst.
      + exists (par PX' PB'). split; [apply pp_left, H2' | apply pp_right, H1].
      + destruct (IH _ _ _ H2' Hne) as (P12 & Hb & Ha).
        exists (par PA P12). split; apply pp_right; assumption.
  Qed.

  (** ** What a pick does to the action multiset *)

  Lemma process_actions_advance : forall K T,
      process_actions (advance r_done K T) = K ++ process_actions T.
  Proof. intros [| a K] T; reflexivity. Qed.

  Lemma program_actions_leaf : forall T,
      program_actions (leaf T) = process_actions T.
  Proof. intro T; reflexivity. Qed.

  Lemma program_actions_par : forall P1 P2,
      program_actions (par P1 P2) = program_actions P1 ++ program_actions P2.
  Proof. reflexivity. Qed.

  Lemma ppick_perm : forall P p a P',
      ppick P p a P' ->
      Permutation (program_actions P) (a :: program_actions P').
  Proof.
    intros P p a P' H;
      induction H as [K a K' T Hp | PA PB p a PA' H IH | PA PB p a PB' H IH].
    - rewrite !program_actions_leaf; cbn [process_actions].
      rewrite process_actions_advance.
      exact (Permutation_app_tail (process_actions T) (picks_perm _ _ _ Hp)).
    - rewrite !program_actions_par.
      eapply Permutation_trans; [apply Permutation_app_tail, IH |].
      apply Permutation_refl.
    - rewrite !program_actions_par.
      eapply Permutation_trans; [apply Permutation_app_head, IH |].
      apply Permutation_sym, Permutation_middle.
  Qed.

  (** ** Uniqueness: with only one endpoint of its kind in the whole tree, a
         pick is determined by the channel *)

  Lemma ppick_ends_ge1 : forall f P p a P' c,
      ppick P p a P' -> caction_chan a = c -> f a = true ->
      (1 <= length (ends_on f (program_actions P) c))%nat.
  Proof.
    intros f P p a P' c H Hc Hf.
    eapply ends_on_ge1; [| exact Hc | exact Hf].
    eapply Permutation_in; [apply Permutation_sym, (ppick_perm _ _ _ _ H) |].
    left; reflexivity.
  Qed.

  Lemma ppick_unique : forall f P p a1 P1,
      ppick P p a1 P1 ->
      forall q a2 P2,
        length (ends_on f (program_actions P) (caction_chan a1)) = 1%nat ->
        f a1 = true -> f a2 = true ->
        caction_chan a1 = caction_chan a2 ->
        ppick P q a2 P2 -> a1 = a2 /\ P1 = P2 /\ p = q.
  Proof.
    intros f P p a1 P1 H1;
      induction H1 as [K a K1 T Hpk | PA PB p a PA' H1 IH | PA PB p a PB' H1 IH];
      intros q a2 P2 Hlen Hf1 Hf2 Hc H2.
    - inversion H2 as [Kx a2x Kx' Tx Hpk2 Eq1 Eq2 | |]; subst.
      rewrite program_actions_leaf in Hlen; cbn [process_actions] in Hlen.
      rewrite ends_on_app, length_app in Hlen.
      assert (Hl : length (ends_on f K (caction_chan a)) = 1%nat).
      { pose proof (ends_on_ge1 f K (caction_chan a) a
                      (picks_In _ _ _ Hpk) eq_refl Hf1). lia. }
      destruct (picks_unique _ _ _ _ Hpk _ _ Hl Hf1 Hf2 Hc Hpk2) as [Ha HK];
        subst.
      split; [reflexivity | split; reflexivity].
    - rewrite program_actions_par, ends_on_app, length_app in Hlen.
      inversion H2 as [| PX PY qx a2x PX' H2' Eq1 Eq2
                       | PX PY qx a2x PY' H2' Eq1 Eq2]; subst.
      + pose proof (ppick_ends_ge1 f _ _ _ _ _ H1 eq_refl Hf1) as G1.
        assert (Hl : length (ends_on f (program_actions PA) (caction_chan a))
                     = 1%nat) by lia.
        destruct (IH _ _ _ Hl Hf1 Hf2 Hc H2') as (Ha & HP & Hq); subst.
        split; [reflexivity | split; reflexivity].
      + exfalso.
        pose proof (ppick_ends_ge1 f _ _ _ _ _ H1 eq_refl Hf1) as G1.
        pose proof (ppick_ends_ge1 f _ _ _ _ _ H2' (eq_sym Hc) Hf2) as G2.
        lia.
    - rewrite program_actions_par, ends_on_app, length_app in Hlen.
      inversion H2 as [| PX PY qx a2x PX' H2' Eq1 Eq2
                       | PX PY qx a2x PY' H2' Eq1 Eq2]; subst.
      + exfalso.
        pose proof (ppick_ends_ge1 f _ _ _ _ _ H1 eq_refl Hf1) as G1.
        pose proof (ppick_ends_ge1 f _ _ _ _ _ H2' (eq_sym Hc) Hf2) as G2.
        lia.
      + pose proof (ppick_ends_ge1 f _ _ _ _ _ H1 eq_refl Hf1) as G1.
        assert (Hl : length (ends_on f (program_actions PB) (caction_chan a))
                     = 1%nat) by lia.
        destruct (IH _ _ _ Hl Hf1 Hf2 Hc H2') as (Ha & HP & Hq); subst.
        split; [reflexivity | split; reflexivity].
  Qed.



  (** ** A rendezvous, at the level of programs *)

  Definition prdv (P : program) (c : chan) (e : expr) (x : var)
                  (ps pr : path) (P' : program) : Prop :=
    exists Pmid, ps <> pr
              /\ ppick P ps (c_send c e) Pmid
              /\ ppick Pmid pr (c_recv c x) P'.

  Lemma prdv_ends : forall P c e x ps pr P',
      prdv P c e x ps pr P' ->
      exists Ks Ts Kr Tr Ks' Kr',
        leaf_at P ps = Some (phase r_done Ks Ts)
        /\ leaf_at P pr = Some (phase r_done Kr Tr)
        /\ Ks ∋ c_send c e □ Ks'
        /\ Kr ∋ c_recv c x □ Kr'
        /\ P' = set_at (set_at P ps (advance r_done Ks' Ts)) pr
                       (advance r_done Kr' Tr).
  Proof.
    intros P c e x ps pr P' (Pmid & Hne & Hs & Hr).
    destruct (ppick_elim _ _ _ _ Hs) as (Ks & Ts & Ks' & Hls & Hps & HM).
    destruct (ppick_elim _ _ _ _ Hr) as (Kr & Tr & Kr' & Hlr & Hpr & HP').
    exists Ks, Ts, Kr, Tr, Ks', Kr'.
    rewrite HM in Hlr; rewrite (leaf_at_set_other P pr ps _ (not_eq_sym Hne)) in Hlr.
    split; [exact Hls | split; [exact Hlr | split; [exact Hps |
      split; [exact Hpr | rewrite HP', HM; reflexivity]]]].
  Qed.

  Lemma prdv_intro : forall P ps pr c e x Ks Ks' Kr Kr' Ts Tr,
      ps <> pr ->
      leaf_at P ps = Some (phase r_done Ks Ts) ->
      leaf_at P pr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send c e □ Ks' -> Kr ∋ c_recv c x □ Kr' ->
      prdv P c e x ps pr
        (set_at (set_at P ps (advance r_done Ks' Ts)) pr
                (advance r_done Kr' Tr)).
  Proof.
    intros P ps pr c e x Ks Ks' Kr Kr' Ts Tr Hne Hls Hlr Hps Hpr.
    exists (set_at P ps (advance r_done Ks' Ts)).
    split; [exact Hne | split; [apply (ppick_intro _ _ Ks Ts); assumption |]].
    apply (ppick_intro _ _ Kr Tr); [| exact Hpr].
    rewrite (leaf_at_set_other P pr ps _ (not_eq_sym Hne)); exact Hlr.
  Qed.

  (** ** …is a step *)

  Lemma prdv_step_at : forall P c e x ps pr P' (E : ensemble dim),
      prdv P c e x ps pr P' -> step_at P E {|| P', rmap x e E ||}.
  Proof.
    intros P c e x ps pr P' E Hp.
    destruct (prdv_ends _ _ _ _ _ _ _ Hp)
      as (Ks & Ts & Kr & Tr & Ks' & Kr' & Hls & Hlr & Hps & Hpr & HP').
    destruct Hp as (Pmid & Hne & _ & _).
    eapply (sa_comm ps pr P E c e x Ks Ks' Kr Kr' Ts Tr);
      try eassumption; rewrite HP'; reflexivity.
  Qed.

  (** ** Channel uniqueness, as an invariant of the whole tree *)

  Definition chan_unique (P : program) : Prop :=
    forall c, (length (ends_on is_send (program_actions P) c) <= 1)%nat
           /\ (length (ends_on (fun a => negb (is_send a))
                         (program_actions P) c) <= 1)%nat.

  Lemma ends_on_perm : forall f l l' c,
      Permutation l l' -> Permutation (ends_on f l c) (ends_on f l' c).
  Proof.
    intros f l l' c H; unfold ends_on.
    apply permutation_filter, permutation_filter, H.
  Qed.

  Lemma chan_unique_ppick : forall P p a P',
      chan_unique P -> ppick P p a P' -> chan_unique P'.
  Proof.
    intros P p a P' Hcu Hpk c.
    pose proof (ppick_perm _ _ _ _ Hpk) as Hperm.
    destruct (Hcu c) as (H1 & H2); split.
    - rewrite (Permutation_length (ends_on_perm is_send _ _ c Hperm)) in H1.
      rewrite ends_on_cons in H1.
      destruct (Nat.eqb (caction_chan a) c && is_send a)%bool;
        cbn [length] in H1; lia.
    - rewrite (Permutation_length
                 (ends_on_perm (fun b => negb (is_send b)) _ _ c Hperm)) in H2.
      rewrite ends_on_cons in H2.
      destruct (Nat.eqb (caction_chan a) c && negb (is_send a))%bool;
        cbn [length] in H2; lia.
  Qed.

  (** ** Same channel: the same rendezvous *)

  Lemma prdv_unique : forall P c e1 x1 ps1 pr1 P1 e2 x2 ps2 pr2 P2,
      chan_unique P ->
      prdv P c e1 x1 ps1 pr1 P1 -> prdv P c e2 x2 ps2 pr2 P2 ->
      e1 = e2 /\ x1 = x2 /\ P1 = P2.
  Proof.
    intros P c e1 x1 ps1 pr1 P1 e2 x2 ps2 pr2 P2 Hcu
           (M1 & Hne1 & Hs1 & Hr1) (M2 & Hne2 & Hs2 & Hr2).
    (* the send *)
    assert (Hls : length (ends_on is_send (program_actions P)
                            (caction_chan (c_send c e1))) = 1%nat).
    { pose proof (ppick_ends_ge1 is_send _ _ _ _ _ Hs1 eq_refl eq_refl) as Hge.
      destruct (Hcu (caction_chan (c_send c e1))) as (Hle & _). cbn in *. lia. }
    destruct (ppick_unique is_send P ps1 (c_send c e1) M1 Hs1
                ps2 (c_send c e2) M2 Hls eq_refl eq_refl eq_refl Hs2)
      as (Ha & HM & Hp).
    injection Ha as He; subst e2 M2.
    (* the receive, out of the residual *)
    assert (Hcu1 : chan_unique M1) by exact (chan_unique_ppick _ _ _ _ Hcu Hs1).
    assert (Hlr : length (ends_on (fun a => negb (is_send a))
                            (program_actions M1)
                            (caction_chan (c_recv c x1))) = 1%nat).
    { pose proof (ppick_ends_ge1 (fun a => negb (is_send a)) _ _ _ _ _ Hr1
                    eq_refl eq_refl) as Hge.
      destruct (Hcu1 (caction_chan (c_recv c x1))) as (_ & Hle). cbn in *. lia. }
    destruct (ppick_unique (fun a => negb (is_send a)) M1 pr1 (c_recv c x1) P1
                Hr1 pr2 (c_recv c x2) P2 Hlr eq_refl eq_refl eq_refl Hr2)
      as (Hb & HP & _).
    injection Hb as Hx; subst x2.
    split; [reflexivity | split; [reflexivity | exact HP]].
  Qed.

  (** ** Different channels: the two rendezvous join *)

  Lemma prdv_confluent : forall P c1 e1 x1 ps1 pr1 P1 c2 e2 x2 ps2 pr2 P2,
      c1 <> c2 ->
      prdv P c1 e1 x1 ps1 pr1 P1 -> prdv P c2 e2 x2 ps2 pr2 P2 ->
      exists P12, prdv P1 c2 e2 x2 ps2 pr2 P12 /\ prdv P2 c1 e1 x1 ps1 pr1 P12.
  Proof.
    intros P c1 e1 x1 ps1 pr1 P1 c2 e2 x2 ps2 pr2 P2 Hc
           (M1 & Hne1 & Hs1 & Hr1) (M2 & Hne2 & Hs2 & Hr2).
    assert (N12 : caction_chan (c_send c1 e1) <> caction_chan (c_send c2 e2))
      by (cbn; exact Hc).
    assert (N21 : caction_chan (c_send c2 e2) <> caction_chan (c_send c1 e1))
      by (cbn; intro H; apply Hc; symmetry; exact H).
    destruct (ppick_confluent _ _ _ _ Hs1 _ _ _ Hs2 N12) as (n & Hn1 & Hn2).
    destruct (ppick_confluent _ _ _ _ Hr1 _ _ _ Hn1 N12) as (p & Hp1 & Hp2).
    destruct (ppick_confluent _ _ _ _ Hr2 _ _ _ Hn2 N21) as (q & Hq1 & Hq2).
    destruct (ppick_confluent _ _ _ _ Hp2 _ _ _ Hq2 N12) as (P12 & Hk1 & Hk2).
    exists P12. split.
    - exists p. split; [exact Hne2 | split; [exact Hp1 | exact Hk1]].
    - exists q. split; [exact Hne1 | split; [exact Hq1 | exact Hk2]].
  Qed.



  (** ** Same-phase independence, as a property of the tree.

      [wf_phase_independence] is stated per padded phase, and a reachable
      program has lost that alignment — a leaf that finished its block moved
      on while its neighbours did not.  What survives is the LEAF-LOCAL
      half: no block names a receive target twice, and none of its own
      outputs reads one.  Across leaves the same facts come from
      [wf_ownership], so between them every pair of simultaneously available
      rendezvous is independent. *)

  Fixpoint proc_bindep (T : process) : Prop :=
    match T with
    | terminated   => True
    | phase _ K T' => NoDup (cblock_change K)
                      /\ disjoint (cblock_change K) (cblock_read K)
                      /\ proc_bindep T'
    end.

  Definition blocks_indep (P : program) : Prop := row_all proc_bindep P.

  Lemma blocks_indep_at : forall P p S,
      blocks_indep P -> leaf_at P p = Some S -> proc_bindep S.
  Proof.
    intro P; induction P as [S0 | P1 IH1 P2 IH2]; intros [| p' | p'] S Hbi Hl;
      cbn in Hl; try discriminate.
    - injection Hl as HS; subst S0; exact Hbi.
    - exact (IH1 p' S (proj1 Hbi) Hl).
    - exact (IH2 p' S (proj2 Hbi) Hl).
  Qed.

  (** ** Footprints of one endpoint *)

  Lemma cblock_change_recv : forall K c x,
      In (c_recv c x) K -> In x (cblock_change K).
  Proof.
    intros K c x Hin; unfold cblock_change; apply in_flat_map.
    exists (c_recv c x); split; [exact Hin | left; reflexivity].
  Qed.

  Lemma cblock_read_send : forall K c e y,
      In (c_send c e) K -> In y (expr_vars e) -> In y (cblock_read K).
  Proof.
    intros K c e y Hin Hy; unfold cblock_read; apply in_flat_map.
    exists (c_send c e); split; [exact Hin | exact Hy].
  Qed.

  Lemma process_change_disp : forall K T y,
      In y (cblock_change K) -> In y (process_change (phase r_done K T)).
  Proof.
    intros K T y Hy; cbn [process_change residual_change].
    rewrite app_nil_l. apply in_or_app; left; exact Hy.
  Qed.

  Lemma process_read_disp : forall K T y,
      In y (cblock_read K) -> In y (process_read (phase r_done K T)).
  Proof.
    intros K T y Hy; cbn [process_read residual_read].
    rewrite app_nil_l. apply in_or_app; left; exact Hy.
  Qed.

  (** ** A receive target is not read by an output *)

  Lemma rdv_change_read : forall P p q Kp Tp Kq Tq c1 x c2 e,
      wf_ownership P -> blocks_indep P ->
      leaf_at P p = Some (phase r_done Kp Tp) ->
      leaf_at P q = Some (phase r_done Kq Tq) ->
      In (c_recv c1 x) Kp -> In (c_send c2 e) Kq ->
      ~ In x (expr_vars e).
  Proof.
    intros P p q Kp Tp Kq Tq c1 x c2 e Hown Hbi Hp Hq Hrec Hsend Hin.
    destruct (path_eq_dec p q) as [Heq | Hne].
    - subst q. rewrite Hp in Hq; injection Hq as HK _; subst Kq.
      destruct (blocks_indep_at P p _ Hbi Hp) as (_ & Hdj & _).
      exact (Hdj x (cblock_change_recv _ _ _ Hrec)
               (cblock_read_send _ _ _ _ Hsend Hin)).
    - destruct (wf_ownership_paths P p q _ _ Hown Hne Hp Hq) as (Hd & _ & _).
      apply (Hd x (process_change_disp _ _ _ (cblock_change_recv _ _ _ Hrec))).
      unfold process_cvar; apply in_or_app; right.
      exact (process_read_disp _ _ _ (cblock_read_send _ _ _ _ Hsend Hin)).
  Qed.

  (** ** Two receive targets are distinct *)

  Lemma rdv_change_change : forall P p q Kp Tp Kq Tq c1 x1 Kp1 c2 x2 Kq2,
      wf_ownership P -> blocks_indep P -> c1 <> c2 ->
      leaf_at P p = Some (phase r_done Kp Tp) ->
      leaf_at P q = Some (phase r_done Kq Tq) ->
      Kp ∋ c_recv c1 x1 □ Kp1 -> Kq ∋ c_recv c2 x2 □ Kq2 ->
      x1 <> x2.
  Proof.
    intros P p q Kp Tp Kq Tq c1 x1 Kp1 c2 x2 Kq2 Hown Hbi Hc Hp Hq H1 H2 Heq.
    destruct (path_eq_dec p q) as [Hpq | Hne].
    - subst q. rewrite Hp in Hq; injection Hq as HK _; subst Kq.
      destruct (picks_confluent _ _ _ H1 _ _ H2 Hc) as (K12 & Hb & _).
      assert (Hperm : Permutation Kp (c_recv c1 x1 :: c_recv c2 x2 :: K12)).
      { eapply Permutation_trans; [apply (picks_perm _ _ _ H1) |].
        apply perm_skip, (picks_perm _ _ _ Hb). }
      destruct (blocks_indep_at P p _ Hbi Hp) as (Hnd & _ & _).
      unfold cblock_change in Hnd.
      rewrite (permutation_flat_map _ _ caction_change _ _ Hperm) in Hnd.
      cbn [flat_map caction_change app] in Hnd.
      apply NoDup_cons_iff in Hnd as (Hy & _).
      apply Hy; left; symmetry; exact Heq.
    - destruct (wf_ownership_paths P p q _ _ Hown Hne Hp Hq) as (Hd & _ & _).
      apply (Hd x1 (process_change_disp _ _ _ (cblock_change_recv _ _ _
                                                 (picks_In _ _ _ H1)))).
      unfold process_cvar; apply in_or_app; left. rewrite Heq.
      exact (process_change_disp _ _ _ (cblock_change_recv _ _ _
                                          (picks_In _ _ _ H2))).
  Qed.

  (** ** …so two rendezvous on different channels have commuting substitutions *)

  Lemma prdv_subst_indep : forall P c1 e1 x1 ps1 pr1 P1 c2 e2 x2 ps2 pr2 P2,
      wf_ownership P -> blocks_indep P -> c1 <> c2 ->
      prdv P c1 e1 x1 ps1 pr1 P1 -> prdv P c2 e2 x2 ps2 pr2 P2 ->
      x1 <> x2 /\ ~ In x1 (expr_vars e2) /\ ~ In x2 (expr_vars e1).
  Proof.
    intros P c1 e1 x1 ps1 pr1 P1 c2 e2 x2 ps2 pr2 P2 Hown Hbi Hc H1 H2.
    destruct (prdv_ends _ _ _ _ _ _ _ H1)
      as (Ks1 & Ts1 & Kr1 & Tr1 & Ks1' & Kr1' & Hls1 & Hlr1 & Hps1 & Hpr1 & _).
    destruct (prdv_ends _ _ _ _ _ _ _ H2)
      as (Ks2 & Ts2 & Kr2 & Tr2 & Ks2' & Kr2' & Hls2 & Hlr2 & Hps2 & Hpr2 & _).
    split; [| split].
    - exact (rdv_change_change P pr1 pr2 _ _ _ _ _ _ _ _ _ _
               Hown Hbi Hc Hlr1 Hlr2 Hpr1 Hpr2).
    - exact (rdv_change_read P pr1 ps2 _ _ _ _ _ _ _ _
               Hown Hbi Hlr1 Hls2 (picks_In _ _ _ Hpr1) (picks_In _ _ _ Hps2)).
    - exact (rdv_change_read P pr2 ps1 _ _ _ _ _ _ _ _
               Hown Hbi Hlr2 Hls1 (picks_In _ _ _ Hpr2) (picks_In _ _ _ Hps1)).
  Qed.


(** ** 25. Par-Comp-MP — the invariant a run carries ***********************

    Three clauses, and each is preserved because a step only ever SHRINKS one
    leaf: [wf_ownership] because the footprints shrink, [chan_unique] because
    the endpoint multiset shrinks, [blocks_indep] because a block shrinks.
    That last one is why the leaf-local half of Definition 2.1(4) was
    isolated in §24: the padded-phase alignment does NOT survive a run, since
    a leaf that finished its block moved on while its neighbours did not.
*********************************************************************)

  (** ** Rewriting one leaf *)

  Lemma row_all_set : forall {A} (Q : A -> Prop) (r : row A) p a,
      row_all Q r -> Q a -> row_all Q (set_at r p a).
  Proof.
    intros A Q r; induction r as [b | r1 IH1 r2 IH2]; intros [| p' | p'] a H Ha;
      cbn in *; try exact H; try exact Ha.
    - split; [apply IH1; [exact (proj1 H) | exact Ha] | exact (proj2 H)].
    - split; [exact (proj1 H) | apply IH2; [exact (proj2 H) | exact Ha]].
  Qed.

  Lemma row_all_leaves : forall {A} (Q : A -> Prop) (r : row A),
      (forall a, In a (row_leaves r) -> Q a) -> row_all Q r.
  Proof.
    intros A Q r; induction r as [b | r1 IH1 r2 IH2]; intro H; cbn in *.
    - apply H; left; reflexivity.
    - split; [apply IH1 | apply IH2]; intros a Ha; apply H, in_or_app;
        [left | right]; exact Ha.
  Qed.

  Lemma row_flat_set_eq : forall {A B} (f : A -> list B) (r : row A) p a b,
      leaf_at r p = Some a -> f b = f a ->
      row_flat f (set_at r p b) = row_flat f r.
  Proof.
    intros A B f r; induction r as [x | r1 IH1 r2 IH2];
      intros [| p' | p'] a b Hp He; cbn in *; try discriminate; try reflexivity.
    - injection Hp as <-; rewrite He; reflexivity.
    - rewrite (IH1 p' a b Hp He); reflexivity.
    - rewrite (IH2 p' a b Hp He); reflexivity.
  Qed.

  Lemma process_actions_advance_any : forall R K T,
      process_actions (advance R K T) = K ++ process_actions T.
  Proof. intros [| L] [| a K] T; reflexivity. Qed.

  (** ** The three clauses, each preserved by one leaf shrinking *)

  Lemma proc_bindep_advance : forall R K T,
      proc_bindep (phase R K T) -> proc_bindep (advance R K T).
  Proof.
    intros [| L] [| a K] T H; cbn [advance]; try exact H.
    exact (proj2 (proj2 H)).
  Qed.

  Lemma NoDup_app_r : forall {A} (l1 l2 : list A),
      NoDup (l1 ++ l2) -> NoDup l2.
  Proof.
    intros A l1; induction l1 as [| a l1 IH]; intros l2 H; [exact H |].
    apply IH. cbn in H. inversion H; assumption.
  Qed.

  Lemma proc_bindep_picks : forall R K a K' T,
      proc_bindep (phase R K T) -> K ∋ a □ K' -> proc_bindep (phase R K' T).
  Proof.
    intros R K a K' T (Hnd & Hdj & Hrest) Hp.
    destruct (picks_footprint _ _ _ Hp) as (Hc & Hr & _).
    split; [| split; [| exact Hrest]].
    - pose proof (permutation_flat_map _ _ caction_change _ _
                    (picks_perm _ _ _ Hp)) as Q.
      unfold cblock_change in *. rewrite Q in Hnd.
      cbn [flat_map] in Hnd. exact (NoDup_app_r _ _ Hnd).
    - eapply disjoint_incl; [exact Hdj | exact Hc | exact Hr].
  Qed.

  (** ** The invariant *)

  Definition wf_run (P : program) : Prop :=
    wf_ownership P /\ chan_unique P /\ blocks_indep P.

  Lemma wf_run_local : forall P p L K T R',
      wf_run P -> leaf_at P p = Some (phase (r_more L) K T) ->
      incl (residual_change R') (lblock_change L) ->
      incl (residual_read R') (lblock_read L) ->
      incl (residual_qvar R') (lblock_qvar L) ->
      wf_run (set_at P p (advance R' K T)).
  Proof.
    intros P p L K T R' (Hown & Hcu & Hbi) Hl Hc Hr Hq.
    destruct (leaf_shrink_local L K T R' Hc Hr Hq) as (H1 & H2 & H3 & _).
    split; [| split].
    - exact (wf_ownership_set P p _ _ Hown Hl H1 H2 H3).
    - assert (Hact : program_actions (set_at P p (advance R' K T))
                     = program_actions P).
      { unfold program_actions.
        apply (row_flat_set_eq process_actions P p _ _ Hl).
        rewrite process_actions_advance_any; reflexivity. }
      unfold chan_unique; rewrite Hact; exact Hcu.
    - apply (row_all_set _ _ _ _ Hbi), proc_bindep_advance.
      exact (blocks_indep_at P p _ Hbi Hl).
  Qed.

  Lemma wf_run_ppick : forall P p a P',
      wf_run P -> ppick P p a P' -> wf_run P'.
  Proof.
    intros P p a P' (Hown & Hcu & Hbi) Hpk.
    destruct (ppick_elim _ _ _ _ Hpk) as (K & T & K' & Hl & Hp & HP').
    subst P'. split; [| split].
    - destruct (leaf_shrink_rdv K K' T a Hp) as (H1 & H2 & H3 & _).
      exact (wf_ownership_set P p _ _ Hown Hl H1 H2 H3).
    - exact (chan_unique_ppick _ _ _ _ Hcu Hpk).
    - apply (row_all_set _ _ _ _ Hbi), proc_bindep_advance.
      exact (proc_bindep_picks r_done K a K' T (blocks_indep_at P p _ Hbi Hl) Hp).
  Qed.

  (** ** …hence by every step *)

  Lemma wf_run_step_at : forall P E G,
      wf_run P -> step_at P E G -> Forall (fun c => wf_run (fst c)) G.
  Proof.
    intros P E G Hwf Hstep; destruct Hstep as
      [p L K T P0 E0 Gl G0 Hl Hloc HG
      | ps pr P0 E0 c e x Ks Ks' Kr Kr' Ts Tr G0 Hne Hls Hlr Hps Hpr HG];
      subst G0.
    - rewrite Forall_map.
      pose proof (local_step_residual_incl _ _ _ Hloc) as Hcr.
      pose proof (local_step_residual_qvar _ _ _ Hloc) as Hqv.
      eapply Forall_impl with
        (P := fun c => (incl (residual_change (fst c)) (lblock_change L)
                        /\ incl (residual_read (fst c)) (lblock_read L))
                       /\ incl (residual_qvar (fst c)) (lblock_qvar L)).
      2:{ apply Forall_and; assumption. }
      intros cc ((Hc & Hr) & Hq); cbn [fst].
      exact (wf_run_local P0 p L K T _ Hwf Hl Hc Hr Hq).
    - constructor; [| constructor]; cbn [fst].
      destruct (prdv_intro P0 ps pr c e x Ks Ks' Kr Kr' Ts Tr Hne Hls Hlr Hps Hpr)
        as (Pmid & _ & Hs & Hr).
      exact (wf_run_ppick _ _ _ _ (wf_run_ppick _ _ _ _ Hwf Hs) Hr).
  Qed.

  Lemma wf_run_distri : forall P E G,
      wf_run P -> Σ ⊳ ‹ P, E › ⇝ G -> Forall (fun c => wf_run (fst c)) G.
  Proof.
    intros P E G Hwf Hstep.
    exact (wf_run_step_at P E G Hwf (distri_step_at P E G Hstep)).
  Qed.

  Definition cfg_wf (G : distri_config dim) : Prop :=
    Forall (fun c => wf_run (fst c)) G.

  Lemma cfg_wf_mixed : forall G G',
      cfg_wf G -> mixed_step Σ G G' -> cfg_wf G'.
  Proof.
    intros G G' Hwf Hstep.
    inversion Hstep as [Gx D E G0 G1 Hperm Hd Heq1 Heq2]; subst.
    assert (Hhd : wf_run D).
    { assert (Hin : In (D, E) G)
        by (eapply Permutation_in;
            [apply Permutation_sym, Hperm | left; reflexivity]).
      exact (proj1 (Forall_forall _ _) Hwf (D, E) Hin). }
    assert (Htl : cfg_wf G0).
    { apply Forall_forall; intros cc Hcc.
      assert (Hin : In cc G)
        by (eapply Permutation_in;
            [apply Permutation_sym, Hperm | right; exact Hcc]).
      exact (proj1 (Forall_forall _ _) Hwf cc Hin). }
    apply Forall_forall; intros cc Hcc.
    unfold norm in Hcc; apply filter_In in Hcc as (Hin & _).
    apply in_app_or in Hin as [Hin | Hin].
    - exact (proj1 (Forall_forall _ _) (wf_run_distri D E G1 Hhd Hd) cc Hin).
    - exact (proj1 (Forall_forall _ _) Htl cc Hin).
  Qed.

  Lemma cfg_wf_star : forall G G',
      cfg_wf G -> step_star Σ G G' -> cfg_wf G'.
  Proof.
    intros G G' Hwf Hstar; induction Hstar as [G | G1 G2 G3 Hmix Hstar IH];
      [exact Hwf | apply IH, (cfg_wf_mixed _ _ Hwf Hmix)].
  Qed.

  (** ** Definition 2.1 supplies it *)

  Lemma wf_channels_chan_unique : forall P, wf_channels P -> chan_unique P.
  Proof.
    intros P Hwf c.
    destruct (in_dec Nat.eq_dec c (program_chan P)) as [Hin | Hnin].
    - destruct (Hwf c Hin) as (Hs & Hr & _).
      unfold endpoints_of in Hs, Hr; unfold ends_on.
      split; [rewrite Hs | rewrite Hr]; lia.
    - assert (Hnil : filter (fun a => Nat.eqb (caction_chan a) c)
                       (program_actions P) = nil).
      { apply (proj2 (filter_chan_nil_iff c (program_actions P))).
        rewrite <- program_chan_actions; exact Hnin. }
      unfold ends_on; rewrite Hnil; split; cbn; lia.
  Qed.

  Lemma NoDup_app_l : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
  Proof.
    intros A l1; induction l1 as [| a l1 IH]; intros l2 H; [constructor |].
    cbn in H; inversion H as [| y ys Hy Hnd]; subst.
    constructor;
      [intro Hin; apply Hy, in_or_app; left; exact Hin | exact (IH l2 Hnd)].
  Qed.

  Lemma NoDup_flat_map_in : forall {A B} (f : A -> list B) l a,
      NoDup (flat_map f l) -> In a l -> NoDup (f a).
  Proof.
    intros A B f l a Hnd Hin.
    apply in_split in Hin as (l1 & l2 & Hl); subst l.
    rewrite flat_map_app in Hnd; cbn [flat_map] in Hnd.
    apply NoDup_app_r in Hnd. exact (NoDup_app_l _ _ Hnd).
  Qed.

  Lemma disjoint_flat_map_in : forall {A} (f g : A -> names) l a,
      disjoint (flat_map f l) (flat_map g l) -> In a l -> disjoint (f a) (g a).
  Proof.
    intros A f g l a Hdj Hin y Hy Hz.
    apply (Hdj y); apply in_flat_map; exists a; split; assumption.
  Qed.

  Lemma proc_bindep_comm_at : forall T,
      (forall n, NoDup (cblock_change (comm_at T n))
              /\ disjoint (cblock_change (comm_at T n))
                          (cblock_read (comm_at T n))) ->
      proc_bindep T.
  Proof.
    intro T; induction T as [| R K T IH]; intro H; cbn [proc_bindep];
      [exact Logic.I |].
    destruct (H O) as (H1 & H2).
    split; [exact H1 | split; [exact H2 |]].
    apply IH; intro n; exact (H (Datatypes.S n)).
  Qed.

  Lemma wf_phase_independence_blocks : forall P,
      wf_phase_independence P -> blocks_indep P.
  Proof.
    intros P Hwf. apply row_all_leaves; intros T HT.
    apply proc_bindep_comm_at; intro n.
    destruct (Hwf n) as (Hnd & Hdj).
    assert (Hin : In (comm_at T n) (phase_at P n))
      by (rewrite phase_at_leaves;
          exact (in_map (fun T0 => comm_at T0 n) _ T HT)).
    rewrite recv_targets_concat, <- flat_map_concat_flat in Hnd.
    rewrite recv_targets_concat, output_reads_concat,
            <- !flat_map_concat_flat in Hdj.
    split.
    - exact (NoDup_flat_map_in _ _ _ Hnd Hin).
    - exact (disjoint_flat_map_in _ _ _ _ Hdj Hin).
  Qed.

  Lemma wf_program_run : forall P, wf_program P -> wf_run P.
  Proof.
    intros P (Ho & Hc & _ & Hi).
    split; [exact Ho | split;
      [exact (wf_channels_chan_unique P Hc)
      | exact (wf_phase_independence_blocks P Hi)]].
  Qed.


(** ** 26. Par-Comp-MP — the diamond, assembled *****************************

    Two steps from the same configuration, joined.  The whole argument runs
    through ONE tool, [step_star_each] of §21: whichever step is taken first
    forks the configuration, so the other one has to be taken again in every
    fork, and that is several [mixed_step]s rather than one.  Stating both
    branches that way also removes every empty-ensemble case split — a fork
    with no states contributes nothing to either side, which is exactly what
    [norm_flat_map] says.

    The four combinations are then §23's three commutations plus determinism:
    two local steps at ONE leaf agree by [local_step_det], and two rendezvous
    on ONE channel agree by [prdv_unique].  The genuinely new work is in §24,
    which is what lets the two-rendezvous case run without assuming the four
    endpoints sit at four distinct leaves.
*********************************************************************)

  (** ** [norm] plumbing *)

  Lemma norm_forall_nonnil : forall G : distri_config dim,
      Forall (fun c => snd c <> nil) (norm G).
  Proof.
    intro G; induction G as [| [Pc Ec] G IH]; [constructor |].
    unfold norm in *; cbn [filter snd].
    destruct Ec as [| st E0]; [exact IH |].
    constructor; [cbn [snd]; discriminate | exact IH].
  Qed.

  Lemma Forall_norm : forall (Q : program * ensemble dim -> Prop) G,
      Forall Q G -> Forall Q (norm G).
  Proof.
    intros Q G H; apply Forall_forall; intros cc Hcc.
    unfold norm in Hcc; apply filter_In in Hcc as (Hin & _).
    exact (proj1 (Forall_forall _ _) H cc Hin).
  Qed.

  Lemma norm_nil_of_Forall : forall (G : distri_config dim),
      Forall (fun c => snd c = nil) G -> norm G = nil.
  Proof.
    intro G; induction G as [| [Pc Ec] G IH]; intro H; [reflexivity |].
    inversion H as [| u v Hh Ht]; subst; cbn [snd] in Hh; subst Ec.
    unfold norm in *; cbn [filter snd]; exact (IH Ht).
  Qed.

  Lemma cfg_eq_norm : forall G G' : distri_config dim,
      cfg_eq G G' -> cfg_eq (norm G) (norm G').
  Proof.
    intros G G' (G0 & HF & HP).
    exists (norm G0).
    split; [apply Forall2_cpt_norm, HF | apply norm_perm, HP].
  Qed.

  Lemma norm_flat_map : forall (f : program * ensemble dim -> distri_config dim)
                               (G : distri_config dim),
      (forall cc, snd cc = nil -> norm (f cc) = nil) ->
      norm (flat_map f (norm G)) = norm (flat_map f G).
  Proof.
    intros f G Hf; induction G as [| [Pc Ec] G IH]; [reflexivity |].
    cbn [flat_map]; rewrite norm_app.
    destruct Ec as [| st E0].
    - assert (Hz : norm (f (@pair program (ensemble dim) Pc nil)) = nil)
        by (apply Hf; reflexivity).
      rewrite Hz; cbn [app].
      replace (norm (@pair program (ensemble dim) Pc nil :: G)) with (norm G)
        by (unfold norm; reflexivity).
      exact IH.
    - replace (norm (@pair program (ensemble dim) Pc (st :: E0) :: G))
        with (@pair program (ensemble dim) Pc (st :: E0) :: norm G)
        by (unfold norm; reflexivity).
      cbn [flat_map]; rewrite norm_app, IH; reflexivity.
  Qed.

  (** ** Taking THE SAME step at every component *)

  Definition each_local (q : path) (Lq : lblock) (Kq : cblock) (Tq : process)
                        (cc : program * ensemble dim) : distri_config dim :=
    dstep_local (fst cc) q Kq Tq (lstep Lq (snd cc)).

  Definition each_comm (qs qr : path) (Ks' Kr' : cblock) (Ts Tr : process)
                       (xx : var) (ee : expr)
                       (cc : program * ensemble dim) : distri_config dim :=
    dstep_comm (fst cc) qs qr Ks' Kr' Ts Tr xx ee (snd cc).

  Lemma each_local_nil : forall q Lq Kq Tq cc,
      snd cc = nil -> norm (each_local q Lq Kq Tq cc) = nil.
  Proof.
    intros q Lq Kq Tq [Pc Ec] Hc; cbn [snd] in Hc; subst Ec.
    unfold each_local, dstep_local; cbn [fst snd].
    apply norm_nil_of_Forall, Forall_map.
    pose proof (local_step_nil Lq _ (lstep_step Lq nil)) as Hn.
    eapply Forall_impl; [| exact Hn]. intros a Ha; cbn [snd]; exact Ha.
  Qed.

  Lemma each_comm_nil : forall qs qr Ks' Kr' Ts Tr xx ee cc,
      snd cc = nil -> norm (each_comm qs qr Ks' Kr' Ts Tr xx ee cc) = nil.
  Proof.
    intros qs qr Ks' Kr' Ts Tr xx ee [Pc Ec] Hc; cbn [snd] in Hc; subst Ec.
    unfold each_comm, dstep_comm; cbn [fst snd].
    apply norm_nil_of_Forall; constructor; [reflexivity | constructor].
  Qed.

  Lemma each_local_step : forall q Lq Kq Tq cc,
      leaf_at (fst cc) q = Some (phase (r_more Lq) Kq Tq) ->
      Σ ⊳ ‹ fst cc, snd cc › ⇝ each_local q Lq Kq Tq cc.
  Proof.
    intros q Lq Kq Tq cc Hl; unfold each_local.
    exact (sa_local_step q Lq Kq Tq _ _ _ Hl (lstep_step Lq (snd cc))).
  Qed.

  Lemma each_comm_step : forall qs qr Ks Ks' Kr Kr' Ts Tr ch ee xx cc,
      qs <> qr ->
      leaf_at (fst cc) qs = Some (phase r_done Ks Ts) ->
      leaf_at (fst cc) qr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send ch ee □ Ks' -> Kr ∋ c_recv ch xx □ Kr' ->
      Σ ⊳ ‹ fst cc, snd cc › ⇝ each_comm qs qr Ks' Kr' Ts Tr xx ee cc.
  Proof.
    intros qs qr Ks Ks' Kr Kr' Ts Tr ch ee xx cc Hne Hls Hlr Hps Hpr.
    unfold each_comm, dstep_comm.
    exact (sa_comm_step qs qr _ _ ch ee xx Ks Ks' Kr Kr' Ts Tr
             Hne Hls Hlr Hps Hpr).
  Qed.

  (** ** …which needs the leaf to still be there *)

  Lemma dstep_local_leaf_other : forall P p Kp Tp (Gl : local_config dim) q S,
      q <> p -> leaf_at P q = Some S ->
      Forall (fun cc => leaf_at (fst cc) q = Some S)
             (dstep_local P p Kp Tp Gl).
  Proof.
    intros P p Kp Tp Gl q S Hne Hl; unfold dstep_local.
    apply Forall_map, Forall_forall; intros a _; cbn [fst].
    rewrite (leaf_at_set_other P q p _ Hne); exact Hl.
  Qed.

  Lemma dstep_comm_leaf_other :
    forall P ps pr Ks' Kr' Ts Tr xx ee (E : ensemble dim) q S,
      q <> ps -> q <> pr -> leaf_at P q = Some S ->
      Forall (fun cc => leaf_at (fst cc) q = Some S)
             (dstep_comm P ps pr Ks' Kr' Ts Tr xx ee E).
  Proof.
    intros P ps pr Ks' Kr' Ts Tr xx ee E q S Hs Hr Hl.
    unfold dstep_comm; constructor; [| constructor]; cbn [fst].
    rewrite (leaf_at_set_other _ q pr _ Hr), (leaf_at_set_other P q ps _ Hs).
    exact Hl.
  Qed.

  (** ** The side conditions, out of the invariant *)

  Lemma wf_run_non_interfering : forall P p q Lp Kp Tp Lq Kq Tq,
      wf_ownership P -> p <> q ->
      leaf_at P p = Some (phase (r_more Lp) Kp Tp) ->
      leaf_at P q = Some (phase (r_more Lq) Kq Tq) ->
      non_interfering Lp Lq.
  Proof.
    intros P p q Lp Kp Tp Lq Kq Tq Hown Hne Hp Hq.
    destruct (wf_ownership_paths P p q _ _ Hown Hne Hp Hq) as (H1 & H2 & H3).
    assert (Hc : forall L K T y, In y (lblock_change L) ->
                   In y (process_change (phase (r_more L) K T)))
      by (intros L K T y Hy; cbn [process_change residual_change];
          apply in_or_app; left; exact Hy).
    assert (Hr : forall L K T y, In y (lblock_read L) ->
                   In y (process_read (phase (r_more L) K T)))
      by (intros L K T y Hy; cbn [process_read residual_read];
          apply in_or_app; left; exact Hy).
    assert (Hq2 : forall L K T y, In y (lblock_qvar L) ->
                    In y (process_qvar (phase (r_more L) K T)))
      by (intros L K T y Hy; cbn [process_qvar residual_qvar];
          apply in_or_app; left; exact Hy).
    split; [| split; [| split]]; intros y Hy Hz.
    - exact (H1 y (Hc _ _ _ _ Hy)
               (in_or_app _ _ _ (or_introl (Hc _ _ _ _ Hz)))).
    - exact (H1 y (Hc _ _ _ _ Hy)
               (in_or_app _ _ _ (or_intror (Hr _ _ _ _ Hz)))).
    - exact (H2 y (Hc _ _ _ _ Hy)
               (in_or_app _ _ _ (or_intror (Hr _ _ _ _ Hz)))).
    - exact (H3 y (Hq2 _ _ _ _ Hy) (Hq2 _ _ _ _ Hz)).
  Qed.

  Lemma wf_run_rdv_indep :
    forall P p Lp Kp Tp qs qr Ks Ts Kr Tr ch ee xx Ks' Kr',
      wf_ownership P -> p <> qs -> p <> qr ->
      leaf_at P p = Some (phase (r_more Lp) Kp Tp) ->
      leaf_at P qs = Some (phase r_done Ks Ts) ->
      leaf_at P qr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send ch ee □ Ks' -> Kr ∋ c_recv ch xx □ Kr' ->
      rdv_indep Lp xx ee.
  Proof.
    intros P p Lp Kp Tp qs qr Ks Ts Kr Tr ch ee xx Ks' Kr'
           Hown Hs Hr Hlp Hls Hlr Hps Hpr.
    assert (Hx : In xx (process_change (phase r_done Kr Tr)))
      by (apply process_change_disp, cblock_change_recv with (c := ch);
          exact (picks_In _ _ _ Hpr)).
    assert (Hee : forall y, In y (expr_vars ee) ->
                    In y (process_read (phase r_done Ks Ts)))
      by (intros y Hy; apply process_read_disp;
          exact (cblock_read_send _ _ _ _ (picks_In _ _ _ Hps) Hy)).
    destruct (wf_ownership_paths P qr p _ _ Hown
                (fun H => Hr (eq_sym H)) Hlr Hlp) as (Hd1 & _ & _).
    destruct (wf_ownership_paths P p qs _ _ Hown Hs Hlp Hls) as (Hd2 & _ & _).
    split; [| split].
    - intro Hin. apply (Hd1 xx Hx). unfold process_cvar; apply in_or_app; right.
      cbn [process_read residual_read]; apply in_or_app; left; exact Hin.
    - intro Hin. apply (Hd1 xx Hx). unfold process_cvar; apply in_or_app; left.
      cbn [process_change residual_change]; apply in_or_app; left; exact Hin.
    - intros y Hy Hz. apply (Hd2 y).
      + cbn [process_change residual_change]; apply in_or_app; left; exact Hy.
      + unfold process_cvar; apply in_or_app; right; exact (Hee y Hz).
  Qed.



  (** ** A local step and a rendezvous *)

  Lemma step_at_diamond_lc : local_ops ->
    forall P (E : ensemble dim) p Lp Kp Tp qs qr ch ee xx Ks Ks' Kr Kr' Ts Tr,
      wf_run P ->
      leaf_at P p = Some (phase (r_more Lp) Kp Tp) ->
      qs <> qr ->
      leaf_at P qs = Some (phase r_done Ks Ts) ->
      leaf_at P qr = Some (phase r_done Kr Tr) ->
      Ks ∋ c_send ch ee □ Ks' -> Kr ∋ c_recv ch xx □ Kr' ->
      exists X1 X2,
        step_star Σ (norm (dstep_local P p Kp Tp (lstep Lp E))) X1
        /\ step_star Σ (norm (dstep_comm P qs qr Ks' Kr' Ts Tr xx ee E)) X2
        /\ cfg_eq X1 X2.
  Proof.
    intros Hloc P E p Lp Kp Tp qs qr ch ee xx Ks Ks' Kr Kr' Ts Tr
           Hwf Hlp Hne Hls Hlr Hps Hpr.
    assert (Hps' : p <> qs) by (intro He; subst; rewrite Hlp in Hls; discriminate).
    assert (Hpr' : p <> qr) by (intro He; subst; rewrite Hlp in Hlr; discriminate).
    assert (Hind : rdv_indep Lp xx ee)
      by exact (wf_run_rdv_indep P p Lp Kp Tp qs qr Ks Ts Kr Tr ch ee xx Ks' Kr'
                  (proj1 Hwf) Hps' Hpr' Hlp Hls Hlr Hps Hpr).
    (* the local side takes the rendezvous, in every branch *)
    destruct (step_star_each (each_comm qs qr Ks' Kr' Ts Tr xx ee)
                (norm (dstep_local P p Kp Tp (lstep Lp E))))
      as (X1 & HX1 & Heq1).
    { intros cc Hcc.
      apply (each_comm_step qs qr Ks Ks' Kr Kr' Ts Tr ch ee xx cc Hne).
      - exact (proj1 (Forall_forall _ _)
                 (Forall_norm _ _ (dstep_local_leaf_other P p Kp Tp _ qs _
                                       (not_eq_sym Hps') Hls)) cc Hcc).
      - exact (proj1 (Forall_forall _ _)
                 (Forall_norm _ _ (dstep_local_leaf_other P p Kp Tp _ qr _
                                       (not_eq_sym Hpr') Hlr)) cc Hcc).
      - exact Hps.
      - exact Hpr. }
    { apply norm_forall_nonnil. }
    (* the rendezvous side takes the local step *)
    destruct (step_star_each (each_local p Lp Kp Tp)
                (norm (dstep_comm P qs qr Ks' Kr' Ts Tr xx ee E)))
      as (X2 & HX2 & Heq2).
    { intros cc Hcc.
      apply (each_local_step p Lp Kp Tp cc).
      exact (proj1 (Forall_forall _ _)
               (Forall_norm _ _ (dstep_comm_leaf_other P qs qr Ks' Kr' Ts Tr
                                     xx ee E p _ Hps' Hpr' Hlp)) cc Hcc). }
    { apply norm_forall_nonnil. }
    exists X1, X2. split; [exact HX1 | split; [exact HX2 |]].
    eapply cfg_eq_trans; [exact Heq1 |].
    eapply cfg_eq_trans; [| apply cfg_eq_sym, Heq2].
    rewrite (norm_flat_map _ _ (each_comm_nil qs qr Ks' Kr' Ts Tr xx ee)).
    rewrite (norm_flat_map _ _ (each_local_nil p Lp Kp Tp)).
    apply cfg_eq_norm.
    unfold each_comm, each_local.
    rewrite (diamond_local_comm P p Lp Kp Tp qs qr Ks' Kr' Ts Tr xx ee E
               Hps' Hpr' Hind).
    unfold dstep_comm; cbn [flat_map]; rewrite app_nil_r.
    apply cfg_eq_refl.
  Qed.



  (** ** A step, read off as one of two shapes *)

  Lemma step_at_shape : forall P (E : ensemble dim) G,
      step_at P E G ->
      (exists p Lp Kp Tp, leaf_at P p = Some (phase (r_more Lp) Kp Tp)
                          /\ G = dstep_local P p Kp Tp (lstep Lp E))
      \/ (exists ps pr ch ee xx Ks Ks' Kr Kr' Ts Tr,
             ps <> pr
             /\ leaf_at P ps = Some (phase r_done Ks Ts)
             /\ leaf_at P pr = Some (phase r_done Kr Tr)
             /\ Ks ∋ c_send ch ee □ Ks'
             /\ Kr ∋ c_recv ch xx □ Kr'
             /\ G = dstep_comm P ps pr Ks' Kr' Ts Tr xx ee E).
  Proof.
    intros P E G H; destruct H as
      [p L K T P0 E0 Gl G0 Hl Hloc HG
      | ps pr P0 E0 ch ee xx Ks Ks' Kr Kr' Ts Tr G0 Hne Hls Hlr Hps Hpr HG].
    - left. exists p, L, K, T. split; [exact Hl |].
      rewrite HG; unfold dstep_local; rewrite (lstep_eq _ _ _ Hloc);
        reflexivity.
    - right. exists ps, pr, ch, ee, xx, Ks, Ks', Kr, Kr', Ts, Tr.
      split; [exact Hne | split; [exact Hls | split; [exact Hlr |
        split; [exact Hps | split; [exact Hpr | exact HG]]]]].
  Qed.

  Lemma Forall_leaf_of_prog : forall (G : distri_config dim) Q q S,
      Forall (fun cc => fst cc = Q) G -> leaf_at Q q = Some S ->
      Forall (fun cc => leaf_at (fst cc) q = Some S) G.
  Proof.
    intros G Q q S HF Hl; eapply Forall_impl; [| exact HF].
    intros cc Hc; rewrite Hc; exact Hl.
  Qed.

  Lemma dstep_comm_prog : forall P ps pr Ks' Kr' Ts Tr xx ee (E : ensemble dim),
      Forall (fun cc => fst cc
                        = set_at (set_at P ps (advance r_done Ks' Ts)) pr
                                 (advance r_done Kr' Tr))
             (dstep_comm P ps pr Ks' Kr' Ts Tr xx ee E).
  Proof.
    intros; unfold dstep_comm; constructor; [reflexivity | constructor].
  Qed.

  (** ** The diamond *)

  Lemma step_at_diamond : local_ops ->
    forall P (E : ensemble dim) G1 G2,
      wf_run P -> step_at P E G1 -> step_at P E G2 ->
      exists X1 X2, step_star Σ (norm G1) X1 /\ step_star Σ (norm G2) X2
                 /\ cfg_eq X1 X2.
  Proof.
    intros Hloc P E G1 G2 Hwf H1 H2.
    apply step_at_shape in H1; apply step_at_shape in H2.
    destruct H1 as [(p & Lp & Kp & Tp & Hlp & HG1)
                   | (ps1 & pr1 & ch1 & ee1 & xx1 & Ks1 & Ks1' & Kr1 & Kr1'
                      & Ts1 & Tr1 & Hne1 & Hls1 & Hlr1 & Hps1 & Hpr1 & HG1)];
      destruct H2 as [(q & Lq & Kq & Tq & Hlq & HG2)
                     | (ps2 & pr2 & ch2 & ee2 & xx2 & Ks2 & Ks2' & Kr2 & Kr2'
                        & Ts2 & Tr2 & Hne2 & Hls2 & Hlr2 & Hps2 & Hpr2 & HG2)];
      subst G1 G2.
    - (* two local steps *)
      destruct (path_eq_dec p q) as [Heq | Hne].
      + subst q. rewrite Hlp in Hlq.
        inversion Hlq; subst.
        eexists; eexists.
        split; [apply star_refl | split; [apply star_refl | apply cfg_eq_refl]].
      + assert (Hni : non_interfering Lp Lq)
          by exact (wf_run_non_interfering P p q Lp Kp Tp Lq Kq Tq
                      (proj1 Hwf) Hne Hlp Hlq).
        destruct (step_star_each (each_local q Lq Kq Tq)
                    (norm (dstep_local P p Kp Tp (lstep Lp E))))
          as (X1 & HX1 & Heq1).
        { intros cc Hcc; apply each_local_step.
          exact (proj1 (Forall_forall _ _)
                   (Forall_norm _ _ (dstep_local_leaf_other P p Kp Tp _ q _
                                       (not_eq_sym Hne) Hlq)) cc Hcc). }
        { apply norm_forall_nonnil. }
        destruct (step_star_each (each_local p Lp Kp Tp)
                    (norm (dstep_local P q Kq Tq (lstep Lq E))))
          as (X2 & HX2 & Heq2).
        { intros cc Hcc; apply each_local_step.
          exact (proj1 (Forall_forall _ _)
                   (Forall_norm _ _ (dstep_local_leaf_other P q Kq Tq _ p _
                                       Hne Hlp)) cc Hcc). }
        { apply norm_forall_nonnil. }
        exists X1, X2. split; [exact HX1 | split; [exact HX2 |]].
        eapply cfg_eq_trans; [exact Heq1 |].
        eapply cfg_eq_trans; [| apply cfg_eq_sym, Heq2].
        rewrite (norm_flat_map _ _ (each_local_nil q Lq Kq Tq)).
        rewrite (norm_flat_map _ _ (each_local_nil p Lp Kp Tp)).
        apply cfg_eq_norm. unfold each_local.
        exact (diamond_local_local Hloc P p q Lp Kp Tp Lq Kq Tq E Hne Hni).
    - (* local, then rendezvous *)
      exact (step_at_diamond_lc Hloc P E p Lp Kp Tp ps2 pr2 ch2 ee2 xx2
               Ks2 Ks2' Kr2 Kr2' Ts2 Tr2 Hwf Hlp Hne2 Hls2 Hlr2 Hps2 Hpr2).
    - (* rendezvous, then local *)
      destruct (step_at_diamond_lc Hloc P E q Lq Kq Tq ps1 pr1 ch1 ee1 xx1
                  Ks1 Ks1' Kr1 Kr1' Ts1 Tr1 Hwf Hlq Hne1 Hls1 Hlr1 Hps1 Hpr1)
        as (Y1 & Y2 & HY1 & HY2 & Heq).
      exists Y2, Y1.
      split; [exact HY2 | split; [exact HY1 | apply cfg_eq_sym, Heq]].
    - (* two rendezvous *)
      assert (Hr1 : prdv P ch1 ee1 xx1 ps1 pr1
                      (set_at (set_at P ps1 (advance r_done Ks1' Ts1)) pr1
                              (advance r_done Kr1' Tr1)))
        by exact (prdv_intro P ps1 pr1 ch1 ee1 xx1 Ks1 Ks1' Kr1 Kr1' Ts1 Tr1
                    Hne1 Hls1 Hlr1 Hps1 Hpr1).
      assert (Hr2 : prdv P ch2 ee2 xx2 ps2 pr2
                      (set_at (set_at P ps2 (advance r_done Ks2' Ts2)) pr2
                              (advance r_done Kr2' Tr2)))
        by exact (prdv_intro P ps2 pr2 ch2 ee2 xx2 Ks2 Ks2' Kr2 Kr2' Ts2 Tr2
                    Hne2 Hls2 Hlr2 Hps2 Hpr2).
      destruct (Nat.eq_dec ch1 ch2) as [Hc | Hc].
      + subst ch2.
        destruct (prdv_unique P ch1 ee1 xx1 ps1 pr1 _ ee2 xx2 ps2 pr2 _
                    (proj1 (proj2 Hwf)) Hr1 Hr2) as (He & Hx & HP).
        subst ee2 xx2.
        assert (Hgg : dstep_comm P ps1 pr1 Ks1' Kr1' Ts1 Tr1 xx1 ee1 E
                      = dstep_comm P ps2 pr2 Ks2' Kr2' Ts2 Tr2 xx1 ee1 E)
          by (unfold dstep_comm; rewrite HP; reflexivity).
        rewrite Hgg. eexists; eexists.
        split; [apply star_refl | split; [apply star_refl | apply cfg_eq_refl]].
      + destruct (prdv_confluent P ch1 ee1 xx1 ps1 pr1 _ ch2 ee2 xx2 ps2 pr2 _
                    Hc Hr1 Hr2) as (P12 & Hj1 & Hj2).
        destruct (prdv_subst_indep P ch1 ee1 xx1 ps1 pr1 _ ch2 ee2 xx2 ps2 pr2 _
                    (proj1 Hwf) (proj2 (proj2 Hwf)) Hc Hr1 Hr2)
          as (Hxne & Hnx1 & Hnx2).
        destruct (prdv_ends _ _ _ _ _ _ _ Hj1)
          as (As & Us & Ar & Ur & As' & Ar' & Hlj1 & Hlj2 & Hpj1 & Hpj2 & HPa).
        destruct (prdv_ends _ _ _ _ _ _ _ Hj2)
          as (Bs & Vs & Br & Vr & Bs' & Br' & Hlk1 & Hlk2 & Hpk1 & Hpk2 & HPb).
        destruct (step_star_each (each_comm ps2 pr2 As' Ar' Us Ur xx2 ee2)
                    (norm (dstep_comm P ps1 pr1 Ks1' Kr1' Ts1 Tr1 xx1 ee1 E)))
          as (X1 & HX1 & Heq1).
        { intros cc Hcc.
          apply (each_comm_step ps2 pr2 As As' Ar Ar' Us Ur ch2 ee2 xx2 cc
                   Hne2);
            [ exact (proj1 (Forall_forall _ _)
                       (Forall_norm _ _ (Forall_leaf_of_prog _ _ ps2 _
                          (dstep_comm_prog P ps1 pr1 Ks1' Kr1' Ts1 Tr1 xx1 ee1 E)
                          Hlj1)) cc Hcc)
            | exact (proj1 (Forall_forall _ _)
                       (Forall_norm _ _ (Forall_leaf_of_prog _ _ pr2 _
                          (dstep_comm_prog P ps1 pr1 Ks1' Kr1' Ts1 Tr1 xx1 ee1 E)
                          Hlj2)) cc Hcc)
            | exact Hpj1 | exact Hpj2 ]. }
        { apply norm_forall_nonnil. }
        destruct (step_star_each (each_comm ps1 pr1 Bs' Br' Vs Vr xx1 ee1)
                    (norm (dstep_comm P ps2 pr2 Ks2' Kr2' Ts2 Tr2 xx2 ee2 E)))
          as (X2 & HX2 & Heq2).
        { intros cc Hcc.
          apply (each_comm_step ps1 pr1 Bs Bs' Br Br' Vs Vr ch1 ee1 xx1 cc
                   Hne1);
            [ exact (proj1 (Forall_forall _ _)
                       (Forall_norm _ _ (Forall_leaf_of_prog _ _ ps1 _
                          (dstep_comm_prog P ps2 pr2 Ks2' Kr2' Ts2 Tr2 xx2 ee2 E)
                          Hlk1)) cc Hcc)
            | exact (proj1 (Forall_forall _ _)
                       (Forall_norm _ _ (Forall_leaf_of_prog _ _ pr1 _
                          (dstep_comm_prog P ps2 pr2 Ks2' Kr2' Ts2 Tr2 xx2 ee2 E)
                          Hlk2)) cc Hcc)
            | exact Hpk1 | exact Hpk2 ]. }
        { apply norm_forall_nonnil. }
        exists X1, X2. split; [exact HX1 | split; [exact HX2 |]].
        eapply cfg_eq_trans; [exact Heq1 |].
        eapply cfg_eq_trans; [| apply cfg_eq_sym, Heq2].
        rewrite (norm_flat_map _ _ (each_comm_nil ps2 pr2 As' Ar' Us Ur xx2 ee2)).
        rewrite (norm_flat_map _ _ (each_comm_nil ps1 pr1 Bs' Br' Vs Vr xx1 ee1)).
        apply cfg_eq_norm.
        unfold each_comm, dstep_comm; cbn [flat_map fst snd]; rewrite !app_nil_r.
        rewrite <- HPa, <- HPb.
        rewrite (rmap_swap xx1 ee1 xx2 ee2 E Hxne Hnx1 Hnx2).
        apply cfg_eq_refl.
  Qed.




(** ** 27. Par-Comp-MP — Newman, and what it buys ***************************

    Local confluence (§26) plus termination (§18) is Newman's lemma, and the
    induction is on §18's measure.  Two things beyond the textbook argument:
    the joined configurations only agree up to [cfg_eq], so each step of the
    argument has to be transported with [step_star_cfg]; and the "already
    terminal" case is closed by [terminated_stuck] rather than by a
    normal-form assumption — a STUCK configuration is not terminal, and
    nothing here rules one out.  That is deliberate: deadlock-freedom is not
    among Par-Comp-MP's side conditions, and it is not needed, because the
    terminating run is always one that was HANDED to us.

    [Term_cfg_reduct] is the whole point.  A terminating run's collapse can
    be read off ANY reduct of its configuration — so the soundness proof may
    build the run it wants (d-stage first, then the phase, then the tail)
    and still be talking about the run it was given.
*********************************************************************)

  Lemma norm_cons_perm : forall (D : program) (E : ensemble dim) l,
      E <> nil -> Permutation (norm ((D, E) :: l)) ((D, E) :: norm l).
  Proof. intros D [| st E'] l H; [contradiction | apply Permutation_refl]. Qed.

  Lemma cfg_eq_app : forall A A' B B' : distri_config dim,
      cfg_eq A A' -> cfg_eq B B' -> cfg_eq (A ++ B) (A' ++ B').
  Proof.
    intros A A' B B' (A0 & HFA & HPA) (B0 & HFB & HPB).
    exists (A0 ++ B0).
    split; [apply Forall2_app; assumption | apply Permutation_app; assumption].
  Qed.

  Lemma terminal_no_step : forall G G' : distri_config dim,
      terminal G -> mixed_step Σ G G' -> False.
  Proof.
    intros G G' Ht Hstep.
    inversion Hstep as [Gx D E G0 G1 Hperm Hd Heq1 Heq2]; subst.
    assert (Hin : In (D, E) G)
      by (eapply Permutation_in;
          [apply Permutation_sym, Hperm | left; reflexivity]).
    exact (terminated_stuck D (proj1 (Forall_forall _ _) Ht (D, E) Hin) E G1 Hd).
  Qed.

  Lemma norm_in_nonnil : forall (G : distri_config dim) cc,
      norm G = G -> In cc G -> snd cc <> nil.
  Proof.
    intros G cc Hn Hin.
    pose proof (norm_forall_nonnil G) as HF; rewrite Hn in HF.
    exact (proj1 (Forall_forall _ _) HF cc Hin).
  Qed.

  (** ** Local confluence *)

  Lemma mixed_step_diamond : local_ops -> forall G G1 G2,
      cfg_wf G -> norm G = G ->
      mixed_step Σ G G1 -> mixed_step Σ G G2 ->
      exists X1 X2, step_star Σ G1 X1 /\ step_star Σ G2 X2 /\ cfg_eq X1 X2.
  Proof.
    intros Hloc G G1 G2 Hwf Hn Hm1 Hm2.
    inversion Hm1 as [Ga D1 E1 G01 H1 Hp1 Hd1 Ha1 Hb1]; subst.
    inversion Hm2 as [Gb D2 E2 G02 H2 Hp2 Hd2 Ha2 Hb2]; subst.
    assert (Hpp : Permutation ((D1, E1) :: G01) ((D2, E2) :: G02))
      by (eapply Permutation_trans; [apply Permutation_sym, Hp1 | exact Hp2]).
    destruct (Permutation_cons_inv_two _ _ _ _ Hpp)
      as [(Heq & Hperm) | (l' & Hl1 & Hl2)].
    - injection Heq as HD HE; subst D2 E2.
      assert (Hwf1 : wf_run D1).
      { assert (Hin : In (D1, E1) G)
          by (eapply Permutation_in;
              [apply Permutation_sym, Hp1 | left; reflexivity]).
        exact (proj1 (Forall_forall _ _) Hwf (D1, E1) Hin). }
      destruct (step_at_diamond Hloc D1 E1 H1 H2 Hwf1
                  (distri_step_at _ _ _ Hd1) (distri_step_at _ _ _ Hd2))
        as (Y1 & Y2 & HY1 & HY2 & Heq12).
      exists (Y1 ++ norm G01), (Y2 ++ norm G02). split; [| split].
      + rewrite norm_app.
        exact (step_star_frame_l _ _ HY1 (norm_idem _) _ (norm_idem _)).
      + rewrite norm_app.
        exact (step_star_frame_l _ _ HY2 (norm_idem _) _ (norm_idem _)).
      + apply cfg_eq_app; [exact Heq12 | apply cfg_eq_perm, norm_perm, Hperm].
    - assert (HE2 : E2 <> nil).
      { apply (norm_in_nonnil G (D2, E2) Hn).
        eapply Permutation_in; [apply Permutation_sym, Hp2 | left; reflexivity]. }
      assert (HE1 : E1 <> nil).
      { apply (norm_in_nonnil G (D1, E1) Hn).
        eapply Permutation_in; [apply Permutation_sym, Hp1 | left; reflexivity]. }
      assert (HP1 : Permutation (norm (H1 ⊎ G01))
                      ((D2, E2) :: (norm H1 ++ norm l'))).
      { eapply Permutation_trans;
          [apply norm_perm, (Permutation_app_head H1 Hl1) |].
        eapply Permutation_trans;
          [apply norm_perm, Permutation_sym, Permutation_middle |].
        eapply Permutation_trans; [apply (norm_cons_perm D2 E2 (H1 ⊎ l') HE2) |].
        apply perm_skip; rewrite norm_app; apply Permutation_refl. }
      assert (HP2 : Permutation (norm (H2 ⊎ G02))
                      ((D1, E1) :: (norm H2 ++ norm l'))).
      { eapply Permutation_trans;
          [apply norm_perm, (Permutation_app_head H2 Hl2) |].
        eapply Permutation_trans;
          [apply norm_perm, Permutation_sym, Permutation_middle |].
        eapply Permutation_trans; [apply (norm_cons_perm D1 E1 (H2 ⊎ l') HE1) |].
        apply perm_skip; rewrite norm_app; apply Permutation_refl. }
      exists (norm (H2 ⊎ (norm H1 ++ norm l'))),
             (norm (H1 ⊎ (norm H2 ++ norm l'))).
      split; [| split].
      + eapply star_step; [| apply star_refl].
        exact (mixed_lift Σ _ D2 E2 (norm H1 ++ norm l') H2 HP1 Hd2).
      + eapply star_step; [| apply star_refl].
        exact (mixed_lift Σ _ D1 E1 (norm H2 ++ norm l') H1 HP2 Hd1).
      + apply cfg_eq_perm.
        rewrite !norm_app, !norm_idem, !app_assoc.
        apply Permutation_app_tail, Permutation_app_comm.
  Qed.

  (** ** Newman: terminating plus locally confluent *)

  Lemma confluent : local_ops -> forall n (G : distri_config dim),
      (cfg_msr G <= n)%nat -> cfg_wf G -> norm G = G ->
      forall A, step_star Σ G A -> terminal A ->
      forall B, step_star Σ G B ->
      exists A', step_star Σ B A' /\ terminal A'
              /\ Permutation (collapse A') (collapse A).
  Proof.
    intros Hloc n; induction n as [| n IH]; intros G Hm Hwf Hn A HA HtA B HB.
    - destruct HB as [Gx | Gx B1 Bx Hmix HB1].
      + exists A. split; [exact HA | split; [exact HtA | apply Permutation_refl]].
      + exfalso; pose proof (mixed_step_msr _ _ Hmix); lia.
    - destruct HB as [Gx | Gx B1 Bx Hmix1 HB1].
      + exists A. split; [exact HA | split; [exact HtA | apply Permutation_refl]].
      + destruct HA as [Gy | Gy A1 Ay Hmix2 HA1];
          [exfalso; exact (terminal_no_step _ _ HtA Hmix1) |].
        destruct (mixed_step_diamond Hloc Gy A1 B1 Hwf Hn Hmix2 Hmix1)
          as (Y1 & Y2 & HY1 & HY2 & Heq).
        assert (HmA1 : (cfg_msr A1 <= n)%nat)
          by (pose proof (mixed_step_msr _ _ Hmix2); lia).
        assert (HmB1 : (cfg_msr B1 <= n)%nat)
          by (pose proof (mixed_step_msr _ _ Hmix1); lia).
        assert (HnA1 : norm A1 = A1)
          by (inversion Hmix2; subst; apply norm_idem).
        assert (HnB1 : norm B1 = B1)
          by (inversion Hmix1; subst; apply norm_idem).
        destruct (IH A1 HmA1 (cfg_wf_mixed _ _ Hwf Hmix2) HnA1 Ay HA1 HtA
                    Y1 HY1) as (A2 & HA2 & HtA2 & HcA2).
        destruct (step_star_cfg _ _ HA2 Y2 Heq) as (A3 & HA3 & Heq3).
        destruct (IH B1 HmB1 (cfg_wf_mixed _ _ Hwf Hmix1) HnB1 A3
                    (step_star_trans _ _ _ HY2 HA3)
                    (cfg_eq_terminal _ _ Heq3 HtA2) Bx HB1)
          as (A' & HA' & HtA' & HcA').
        exists A'. split; [exact HA' | split; [exact HtA' |]].
        eapply Permutation_trans; [exact HcA' |].
        eapply Permutation_trans;
          [apply Permutation_sym, (cfg_eq_collapse _ _ Heq3) | exact HcA2].
  Qed.

  Lemma Term_cfg_reduct : local_ops -> forall G G' E,
      cfg_wf G -> norm G = G ->
      step_star Σ G G' -> Term_cfg G E -> Term_cfg G' E.
  Proof.
    intros Hloc G G' E Hwf Hn Hstep (G0 & Hs0 & Ht0 & Hc0).
    rewrite Hn in Hs0.
    destruct (confluent Hloc (cfg_msr G) G (Nat.le_refl _) Hwf Hn
                G0 Hs0 Ht0 G' Hstep) as (A' & HA' & HtA' & HcA').
    exists A'. rewrite (step_star_norm_free _ _ Hstep Hn).
    split; [exact HA' | split; [exact HtA' |]].
    eapply Permutation_trans; [exact HcA' | exact Hc0].
  Qed.


(** ** 28. Par-Comp-MP — popping the leaves the semantics cannot pop ********

    A leaf [↓ ⨾ ε ⨾ T] is STUCK: [ds_local] wants a residual and [ds_comm]
    wants an endpoint, so it never becomes T on its own — while [cut] puts T
    in the tail.  Nothing in Definition 2.1 forbids such a leaf, so the
    d-stage's run cannot reach the cut's tail as it stands.

    [pops] pops them, and the simulation says a terminating run cannot tell
    the difference.  It is not the "stuck programs never terminate" argument
    (which is false — every state can die in a measurement with no outcomes,
    and the empty configuration IS terminal): it is a step-for-step
    simulation, available because a stuck leaf is never the leaf a step acts
    on, so every step transfers by [set_at_comm] at another position.  What
    makes the terminal end line up is that [pops] is the identity on a
    terminated program.
*********************************************************************)

  (** A leaf [↓ ⨾ ε ⨾ T] is STUCK: [ds_local] wants a residual and [ds_comm]
      wants an endpoint, so it never becomes T — while [cut] puts T in the
      tail.  [pops] is the relation that pops such leaves; the simulation
      below says popping them changes nothing a terminating run can see,
      which is what lets the d-stage's target be the cut's tail. *)
  Inductive pops : program -> program -> Prop :=
  | pops_keep : forall S, pops (leaf S) (leaf S)
  | pops_pop  : forall T, pops (leaf (phase r_done nil T)) (leaf T)
  | pops_par  : forall A A' B B',
      pops A A' -> pops B B' -> pops (par A B) (par A' B').

  Definition unstuck_proc (S : process) : Prop :=
    forall T, S <> phase r_done nil T.

  Lemma unstuck_more : forall L K T, unstuck_proc (phase (r_more L) K T).
  Proof. intros L K T T'; discriminate. Qed.

  Lemma unstuck_cons : forall a K T, unstuck_proc (phase r_done (a :: K) T).
  Proof. intros a K T T'; discriminate. Qed.

  Lemma pops_leaf_at : forall P Q p S,
      pops P Q -> leaf_at P p = Some S -> unstuck_proc S ->
      leaf_at Q p = Some S.
  Proof.
    intros P Q p S H; revert p; induction H as
      [S0 | T | A A' B B' H1 IH1 H2 IH2]; intros [| p' | p'] Hl Hu;
      cbn in Hl |- *; try discriminate; try exact Hl.
    - injection Hl as <-. exfalso; exact (Hu T eq_refl).
    - exact (IH1 p' Hl Hu).
    - exact (IH2 p' Hl Hu).
  Qed.

  Lemma pops_set_at : forall P Q p S X,
      pops P Q -> leaf_at P p = Some S -> unstuck_proc S ->
      pops (set_at P p X) (set_at Q p X).
  Proof.
    intros P Q p S X H; revert p; induction H as
      [S0 | T | A A' B B' H1 IH1 H2 IH2]; intros [| p' | p'] Hl Hu;
      cbn in Hl |- *; try discriminate.
    - apply pops_keep.
    - apply pops_keep.
    - constructor; [exact (IH1 p' Hl Hu) | exact H2].
    - constructor; [exact H1 | exact (IH2 p' Hl Hu)].
  Qed.

  Lemma pops_terminated : forall P Q,
      pops P Q -> prog_terminated P -> Q = P.
  Proof.
    intros P Q H; induction H as [S0 | T | A A' B B' H1 IH1 H2 IH2]; intro Ht.
    - reflexivity.
    - cbn in Ht; discriminate.
    - destruct Ht as (Ht1 & Ht2); rewrite (IH1 Ht1), (IH2 Ht2); reflexivity.
  Qed.

  (** ** One step, simulated *)

  Lemma pops_step : forall P Q (E : ensemble dim) G,
      pops P Q -> step_at P E G ->
      exists G', step_at Q E G'
              /\ Forall2 (fun c c' => pops (fst c) (fst c') /\ snd c = snd c')
                         G G'.
  Proof.
    intros P Q E G Hp Hstep; destruct Hstep as
      [p L K T P0 E0 Gl G0 Hl Hloc HG
      | ps pr P0 E0 ch ee xx Ks Ks' Kr Kr' Ts Tr G0 Hne Hls Hlr Hps Hpr HG];
      subst.
    - exists (map (fun c => (set_at Q p (advance (fst c) K T), snd c)) Gl).
      split.
      + eapply (sa_local p L K T);
          [exact (pops_leaf_at P0 Q p _ Hp Hl (unstuck_more L K T))
          | exact Hloc | reflexivity].
      + clear Hloc. induction Gl as [| c Gl IH]; cbn [map]; constructor;
          [| exact IH].
        split; [| reflexivity]; cbn [fst].
        exact (pops_set_at P0 Q p _ _ Hp Hl (unstuck_more L K T)).
    - assert (Hus : unstuck_proc (phase r_done Ks Ts))
        by (destruct Ks as [| a Ks0];
            [exfalso; inversion Hps | apply unstuck_cons]).
      assert (Hur : unstuck_proc (phase r_done Kr Tr))
        by (destruct Kr as [| a Kr0];
            [exfalso; inversion Hpr | apply unstuck_cons]).
      exists {|| set_at (set_at Q ps (advance r_done Ks' Ts)) pr
                  (advance r_done Kr' Tr), rmap xx ee E0 ||}.
      split.
      + eapply (sa_comm ps pr Q E0 ch ee xx Ks Ks' Kr Kr' Ts Tr);
          [ exact Hne
          | exact (pops_leaf_at P0 Q ps _ Hp Hls Hus)
          | exact (pops_leaf_at P0 Q pr _ Hp Hlr Hur)
          | exact Hps | exact Hpr | reflexivity].
      + constructor; [| constructor]. split; [| reflexivity]; cbn [fst].
        assert (Hmid : pops (set_at P0 ps (advance r_done Ks' Ts))
                            (set_at Q ps (advance r_done Ks' Ts)))
          by exact (pops_set_at P0 Q ps _ _ Hp Hls Hus).
        apply (pops_set_at _ _ pr (phase r_done Kr Tr) _ Hmid);
          [rewrite (leaf_at_set_other P0 pr ps _ (not_eq_sym Hne)); exact Hlr
          | exact Hur].
  Qed.

  (** ** …lifted to configurations *)

  Definition psim (G G' : distri_config dim) : Prop :=
    Forall2 (fun c c' => pops (fst c) (fst c') /\ snd c = snd c') G G'.

  Lemma psim_app : forall A A' B B',
      psim A A' -> psim B B' -> psim (A ++ B) (A' ++ B').
  Proof. intros; apply Forall2_app; assumption. Qed.

  Lemma psim_norm : forall G G', psim G G' -> psim (norm G) (norm G').
  Proof.
    intros G G' H; induction H as [| c c' G G' (H1 & H2) HF IH]; [constructor |].
    destruct c as [Pc Ec]; destruct c' as [Pc' Ec']; cbn [fst snd] in H1, H2.
    subst Ec'. unfold norm in *; cbn [filter snd].
    destruct Ec as [| st E1]; [exact IH |].
    constructor; [split; cbn [fst snd]; [exact H1 | reflexivity] | exact IH].
  Qed.

  Lemma psim_terminal : forall G G', psim G G' -> terminal G -> terminal G'.
  Proof.
    intros G G' H; induction H as [| c c' G G' (H1 & H2) HF IH]; intro Ht;
      [constructor |].
    inversion Ht as [| u v Hh Htl]; subst.
    constructor; [rewrite (pops_terminated _ _ H1 Hh); exact Hh | exact (IH Htl)].
  Qed.

  Lemma psim_collapse : forall G G', psim G G' -> collapse G = collapse G'.
  Proof.
    intros G G' H; induction H as [| c c' G G' (H1 & H2) HF IH]; [reflexivity |].
    destruct c as [Pc Ec]; destruct c' as [Pc' Ec']; cbn [fst snd] in H1, H2.
    subst Ec'. unfold collapse in *; cbn [flat_map snd].
    rewrite IH; reflexivity.
  Qed.

  Lemma psim_mixed : forall G G1 G',
      mixed_step Σ G G1 -> psim G G' ->
      exists G1', mixed_step Σ G' G1' /\ psim G1 G1'.
  Proof.
    intros G G1 G' Hstep Hsim.
    inversion Hstep as [Gx D E G0 H1 Hperm Hd Ha Hb]; subst.
    destruct (Permutation_Forall2 Hperm Hsim) as (H & HpH & HFH).
    inversion HFH as [| u v l l' (Hh1 & Hh2) Htl Hu Hv]; subst.
    destruct v as [D' E']; cbn [fst snd] in Hh1, Hh2; subst E'.
    destruct (pops_step D D' E H1 Hh1 (distri_step_at _ _ _ Hd))
      as (H1' & Hd' & HF1).
    exists (norm (H1' ⊎ l')). split.
    - exact (mixed_lift Σ G' D' E l' H1' HpH (step_at_distri _ _ _ Hd')).
    - apply psim_norm, psim_app; assumption.
  Qed.

  Lemma psim_star : forall G X,
      step_star Σ G X -> forall G', psim G G' ->
      exists X', step_star Σ G' X' /\ psim X X'.
  Proof.
    intros G X H; induction H as [G | G G1 X Hmix Hstar IH]; intros G' Hsim.
    - exists G'. split; [apply star_refl | exact Hsim].
    - destruct (psim_mixed _ _ _ Hmix Hsim) as (G1' & Hm' & Hs1).
      destruct (IH G1' Hs1) as (X' & HX' & HsX).
      exists X'. split; [eapply star_step; eassumption | exact HsX].
  Qed.

  Lemma Term_cfg_pops : forall P Q (E : ensemble dim) Efin,
      pops P Q -> Term_cfg {|| P, E ||} Efin -> Term_cfg {|| Q, E ||} Efin.
  Proof.
    intros P Q E Efin Hp (G & Hs & Ht & Hc).
    assert (Hsim : psim (norm {|| P, E ||}) (norm {|| Q, E ||})).
    { apply psim_norm; constructor;
        [split; [exact Hp | reflexivity] | constructor]. }
    destruct (psim_star _ _ Hs _ Hsim) as (X' & HX' & HsX).
    exists X'. split; [exact HX' | split].
    - exact (psim_terminal _ _ HsX Ht).
    - rewrite <- (psim_collapse _ _ HsX); exact Hc.
  Qed.


(** ** 29. Par-Comp-MP — running the d-stage to the end ********************

    [runs_to c Q F] is "the component c runs to a set of components ALL
    carrying the program Q, whose states together are F".  The d-stage is
    built out of exactly three closure properties of it: running one leaf's
    block ([leaf_runs], by induction on the block's size), a parallel context
    ([runs_to_par_l]/[runs_to_par_r]), and composition ([runs_to_trans]).

    Because the leaves are run one after another IN THE DISPLAYED ORDER, the
    ensemble that comes out is [denote (lseq d) E] on the nose — no
    interference condition is needed here, unlike Par-Disjoint-MP, which has
    to cope with an arbitrary interleaving.
*********************************************************************)

  (** "the component runs to a set of components ALL carrying the program Q,
      whose states together are F".  The whole d-stage is built out of this:
      it is closed under running one leaf, under a parallel context, and
      under composition. *)
  Definition runs_to (c : program * ensemble dim) (Q : program) (F : ensemble dim)
    : Prop :=
    exists G, step_star Σ (norm (c :: nil)) G
           /\ Forall (fun d => fst d = Q) G
           /\ Permutation (collapse G) F.

  Lemma step_star_nil : forall X : distri_config dim,
      step_star Σ nil X -> X = nil.
  Proof.
    intros X H; inversion H as [| G1 G2 G3 Hmix Hstar]; subst; [reflexivity |].
    exfalso; inversion Hmix as [Gx D E G0 G1x Hperm Hd Ha Hb]; subst.
    exact (Permutation_nil_cons Hperm).
  Qed.

  Lemma runs_to_refl : forall Q (E : ensemble dim), runs_to (Q, E) Q E.
  Proof.
    intros Q E. exists (norm {|| Q, E ||}).
    split; [apply star_refl | split].
    - apply Forall_norm; constructor; [reflexivity | constructor].
    - destruct E as [| st E0]; cbn [norm filter snd].
      + apply Permutation_refl.
      + unfold collapse; cbn [flat_map snd]; rewrite app_nil_r.
        apply Permutation_refl.
  Qed.

  Lemma runs_to_nil : forall (Q : program) P F,
      runs_to (P, nil) Q F -> F = nil.
  Proof.
    intros Q P F (G & Hs & _ & Hc).
    cbn [norm filter snd] in Hs. rewrite (step_star_nil G Hs) in Hc.
    apply Permutation_nil in Hc; exact Hc.
  Qed.

  (** ** Every component of a configuration runs, so the configuration does *)

  Lemma Forall_fst_cfg_eq : forall (Q : program) (G G' : distri_config dim),
      cfg_eq G G' -> Forall (fun d => fst d = Q) G ->
      Forall (fun d => fst d = Q) G'.
  Proof.
    intros Q G G' (G0 & HF & HP) Hall.
    assert (H0 : Forall (fun d => fst d = Q) G0).
    { clear HP. revert Hall.
      induction HF as [| c c' l l' (H1 & _) HFF IH]; intro Hall; [constructor |].
      constructor;
        [rewrite <- H1; exact (Forall_inv Hall)
        | exact (IH (Forall_inv_tail Hall))]. }
    eapply Permutation_Forall; [exact HP | exact H0].
  Qed.

  Lemma runs_to_cfg : forall (G : distri_config dim) Q (Fs : list (ensemble dim)),
      Forall2 (fun c F => runs_to c Q F) G Fs ->
      exists X, step_star Σ (norm G) X
             /\ Forall (fun d => fst d = Q) X
             /\ Permutation (collapse X) (concat Fs).
  Proof.
    intros G Q Fs H;
      induction H as [| c F G Fs Hc HF IH]; [exists nil; cbn [norm concat];
        split; [apply star_refl | split; [constructor | apply Permutation_refl]] |].
    destruct IH as (Y & HY & HYall & HYc).
    destruct c as [Pc Ec]; destruct Ec as [| st E0].
    - rewrite (runs_to_nil Q Pc F Hc); cbn [norm filter snd concat app].
      exists Y. split; [exact HY | split; [exact HYall | exact HYc]].
    - destruct Hc as (X1 & HX1 & HX1all & HX1c).
      cbn [norm filter snd] in HX1 |- *.
      assert (HnX1 : norm X1 = X1)
        by (eapply step_star_norm_free; [exact HX1 | reflexivity]).
      pose proof (step_star_frame_l _ _ HX1 eq_refl (norm G)
                    (norm_idem _)) as Hfr1.
      pose proof (step_star_frame_l _ _ HY (norm_idem _) X1 HnX1) as Hfr2.
      destruct (step_star_cfg _ _ Hfr2 (X1 ++ norm G)
                  (cfg_eq_perm _ _ (Permutation_app_comm _ _)))
        as (Z & HZ & HeqZ).
      exists Z. split; [| split].
      + eapply step_star_trans; [exact Hfr1 | exact HZ].
      + apply (Forall_fst_cfg_eq Q (Y ++ X1) Z HeqZ), Forall_app;
          split; assumption.
      + cbn [concat].
        eapply Permutation_trans;
          [apply Permutation_sym, (cfg_eq_collapse _ _ HeqZ) |].
        unfold collapse; rewrite flat_map_app.
        eapply Permutation_trans; [apply Permutation_app_comm |].
        apply Permutation_app; assumption.
  Qed.

  (** ** …and a run happens inside a parallel context *)

  Lemma distri_step_par_l : forall P1 P2 (E : ensemble dim) G,
      Σ ⊳ ‹ P1, E › ⇝ G ->
      Σ ⊳ ‹ par P1 P2, E › ⇝ map (fun c => (par (fst c) P2, snd c)) G.
  Proof. intros; apply ds_par_l; assumption. Qed.

  Lemma norm_map_par_l : forall P2 (G : distri_config dim),
      norm (map (fun c => (par (fst c) P2, snd c)) G)
      = map (fun c => (par (fst c) P2, snd c)) (norm G).
  Proof.
    intros P2 G; unfold norm; induction G as [| [Pc Ec] G IH]; [reflexivity |].
    destruct Ec as [| st E1]; cbn [map filter snd];
      [exact IH | rewrite IH; reflexivity].
  Qed.

  Lemma norm_map_par_r : forall P1 (G : distri_config dim),
      norm (map (fun c => (par P1 (fst c), snd c)) G)
      = map (fun c => (par P1 (fst c), snd c)) (norm G).
  Proof.
    intros P1 G; unfold norm; induction G as [| [Pc Ec] G IH]; [reflexivity |].
    destruct Ec as [| st E1]; cbn [map filter snd];
      [exact IH | rewrite IH; reflexivity].
  Qed.

  Lemma mixed_step_par_l : forall P2 G G',
      mixed_step Σ G G' ->
      mixed_step Σ (map (fun c => (par (fst c) P2, snd c)) G)
                   (map (fun c => (par (fst c) P2, snd c)) G').
  Proof.
    intros P2 G G' H.
    inversion H as [Gx D E G0 G1 Hperm Hd Ha Hb]; subst.
    assert (Hstep' : mixed_step Σ (map (fun c => (par (fst c) P2, snd c)) G)
                       (norm (map (fun c => (par (fst c) P2, snd c)) (G1 ⊎ G0)))).
    { rewrite map_app.
      apply (mixed_lift Σ _ (par D P2) E
               (map (fun c => (par (fst c) P2, snd c)) G0)
               (map (fun c => (par (fst c) P2, snd c)) G1)).
      - eapply Permutation_trans; [apply (Permutation_map _ Hperm) |].
        cbn [map fst snd]; apply Permutation_refl.
      - apply ds_par_l, Hd. }
    rewrite (norm_map_par_l P2 (G1 ⊎ G0)) in Hstep'. exact Hstep'.
  Qed.

  Lemma mixed_step_par_r : forall P1 G G',
      mixed_step Σ G G' ->
      mixed_step Σ (map (fun c => (par P1 (fst c), snd c)) G)
                   (map (fun c => (par P1 (fst c), snd c)) G').
  Proof.
    intros P1 G G' H.
    inversion H as [Gx D E G0 G1 Hperm Hd Ha Hb]; subst.
    assert (Hstep' : mixed_step Σ (map (fun c => (par P1 (fst c), snd c)) G)
                       (norm (map (fun c => (par P1 (fst c), snd c)) (G1 ⊎ G0)))).
    { rewrite map_app.
      apply (mixed_lift Σ _ (par P1 D) E
               (map (fun c => (par P1 (fst c), snd c)) G0)
               (map (fun c => (par P1 (fst c), snd c)) G1)).
      - eapply Permutation_trans; [apply (Permutation_map _ Hperm) |].
        cbn [map fst snd]; apply Permutation_refl.
      - apply ds_par_r, Hd. }
    rewrite (norm_map_par_r P1 (G1 ⊎ G0)) in Hstep'. exact Hstep'.
  Qed.

  Lemma step_star_par_l : forall P2 G X,
      step_star Σ G X ->
      step_star Σ (map (fun c => (par (fst c) P2, snd c)) G)
                  (map (fun c => (par (fst c) P2, snd c)) X).
  Proof.
    intros P2 G X H; induction H as [G | G G1 X Hmix Hstar IH];
      [apply star_refl |].
    eapply star_step; [apply (mixed_step_par_l P2 _ _ Hmix) | exact IH].
  Qed.

  Lemma step_star_par_r : forall P1 G X,
      step_star Σ G X ->
      step_star Σ (map (fun c => (par P1 (fst c), snd c)) G)
                  (map (fun c => (par P1 (fst c), snd c)) X).
  Proof.
    intros P1 G X H; induction H as [G | G G1 X Hmix Hstar IH];
      [apply star_refl |].
    eapply star_step; [apply (mixed_step_par_r P1 _ _ Hmix) | exact IH].
  Qed.

  Lemma runs_to_par_l : forall P1 P2 (E : ensemble dim) Q F,
      runs_to (P1, E) Q F -> runs_to (par P1 P2, E) (par Q P2) F.
  Proof.
    intros P1 P2 E Q F (G & Hs & Hall & Hc).
    exists (map (fun c => (par (fst c) P2, snd c)) G).
    destruct E as [| st E0].
    - cbn [norm filter snd] in Hs |- *.
      rewrite (step_star_nil G Hs) in Hall, Hc |- *; cbn [map].
      split; [apply star_refl | split; [constructor | exact Hc]].
    - cbn [norm filter snd] in Hs |- *.
      pose proof (step_star_par_l P2 _ _ Hs) as Hs'; cbn [map fst snd] in Hs'.
      split; [exact Hs' | split].
      + rewrite Forall_map; eapply Forall_impl; [| exact Hall].
        intros a Ha; cbn [fst]; rewrite Ha; reflexivity.
      + unfold collapse in *; rewrite flat_map_concat_map, map_map;
          cbn [snd]; rewrite <- flat_map_concat_map; exact Hc.
  Qed.

  Lemma runs_to_par_r : forall P1 P2 (E : ensemble dim) Q F,
      runs_to (P2, E) Q F -> runs_to (par P1 P2, E) (par P1 Q) F.
  Proof.
    intros P1 P2 E Q F (G & Hs & Hall & Hc).
    exists (map (fun c => (par P1 (fst c), snd c)) G).
    destruct E as [| st E0].
    - cbn [norm filter snd] in Hs |- *.
      rewrite (step_star_nil G Hs) in Hall, Hc |- *; cbn [map].
      split; [apply star_refl | split; [constructor | exact Hc]].
    - cbn [norm filter snd] in Hs |- *.
      pose proof (step_star_par_r P1 _ _ Hs) as Hs'; cbn [map fst snd] in Hs'.
      split; [exact Hs' | split].
      + rewrite Forall_map; eapply Forall_impl; [| exact Hall].
        intros a Ha; cbn [fst]; rewrite Ha; reflexivity.
      + unfold collapse in *; rewrite flat_map_concat_map, map_map;
          cbn [snd]; rewrite <- flat_map_concat_map; exact Hc.
  Qed.

  (** ** …and runs compose *)

  Lemma denote_flat_map_snd : forall M (G : distri_config dim),
      Permutation (concat (map (fun d => denote M (snd d)) G))
                  (denote M (collapse G)).
  Proof.
    intros M G; induction G as [| [Pc Ec] G IH]; cbn [concat map snd].
    - rewrite denote_nil; apply Permutation_refl.
    - unfold collapse; cbn [flat_map snd].
      eapply Permutation_trans; [apply Permutation_app_head, IH |].
      apply Permutation_sym, denote_app.
  Qed.

  Lemma runs_to_trans : forall c Q Q' M F,
      runs_to c Q F ->
      (forall E', runs_to (Q, E') Q' (denote M E')) ->
      runs_to c Q' (denote M F).
  Proof.
    intros c Q Q' M F (G & Hs & Hall & Hc) Hstep.
    assert (HF2 : Forall2 (fun d F' => runs_to d Q' F') G
                    (map (fun d => denote M (snd d)) G)).
    { clear Hs Hc. revert Hall.
      induction G as [| d G IH]; intro Hall; [constructor |].
      destruct d as [Pd Ed]; cbn [map]; constructor.
      - pose proof (Forall_inv Hall) as Hh; cbn [fst] in Hh; subst Pd.
        cbn [snd]; apply Hstep.
      - exact (IH (Forall_inv_tail Hall)). }
    destruct (runs_to_cfg G Q' _ HF2) as (X & HX & HXall & HXc).
    assert (HnG : norm G = G)
      by (eapply step_star_norm_free; [exact Hs | apply norm_idem]).
    rewrite HnG in HX.
    exists X. split; [| split; [exact HXall |]].
    - eapply step_star_trans; [exact Hs | exact HX].
    - eapply Permutation_trans; [exact HXc |].
      eapply Permutation_trans; [apply denote_flat_map_snd |].
      apply denote_perm, Hc.
  Qed.



  Lemma set_at_set_at : forall {A} (r : row A) p a b,
      set_at (set_at r p a) p b = set_at r p b.
  Proof.
    intros A r; induction r as [x | r1 IH1 r2 IH2]; intros [| p' | p'] a b;
      cbn; try reflexivity; [rewrite IH1 | rewrite IH2]; reflexivity.
  Qed.

  (** ** One leaf's local block, run to the end *)

  Lemma leaf_runs : forall n L, (Datatypes.S (lb_size L) <= n)%nat ->
    forall P p K T (E : ensemble dim),
      leaf_at P p = Some (phase (r_more L) K T) ->
      runs_to (P, E) (set_at P p (advance r_done K T)) (denote L E).
  Proof.
    induction n as [| n IH]; intros L Hn P p K T E Hl; [lia |].
    destruct E as [| st E0].
    - exists nil. rewrite denote_nil.
      split; [cbn [norm filter snd]; apply star_refl
             | split; [constructor | apply Permutation_refl]].
    - assert (Hstep : step_at P (st :: E0)
                        (dstep_local P p K T (lstep L (st :: E0))))
        by (eapply (sa_local p L K T);
            [exact Hl | apply lstep_step | reflexivity]).
      assert (Hmix : mixed_step Σ ((P, st :: E0) :: nil)
                       (norm (dstep_local P p K T (lstep L (st :: E0)) ⊎ nil)))
        by (apply (mixed_lift Σ _ P (st :: E0) nil _ (Permutation_refl _));
            exact (step_at_distri _ _ _ Hstep)).
      pose proof (local_step_size L (st :: E0) _ (lstep_step L (st :: E0)))
        as Hsz.
      assert (HF2 : Forall2 (fun c F => runs_to c
                               (set_at P p (advance r_done K T)) F)
                      (dstep_local P p K T (lstep L (st :: E0)))
                      (map (fun b => residual_denote (fst b) (snd b))
                           (lstep L (st :: E0)))).
      { unfold dstep_local. revert Hsz.
        generalize (lstep L (st :: E0)); intro Gl.
        induction Gl as [| b Gl IHg]; intro Hsz; [constructor |].
        destruct b as [Rb Eb]; cbn [map fst snd].
        pose proof (Forall_inv Hsz) as Hb; cbn [fst] in Hb.
        constructor; [| exact (IHg (Forall_inv_tail Hsz))].
        destruct Rb as [| L'].
        - cbn [advance residual_denote]. apply runs_to_refl.
        - cbn [residual_denote].
          assert (Hl' : leaf_at (set_at P p (advance (r_more L') K T)) p
                        = Some (phase (r_more L') K T))
            by (rewrite (leaf_at_set_same P p _ _ Hl); reflexivity).
          pose proof (IH L' ltac:(cbn [res_msr] in Hb; lia)
                        (set_at P p (advance (r_more L') K T)) p K T Eb Hl')
            as Hrun.
          rewrite set_at_set_at in Hrun. exact Hrun. }
      destruct (runs_to_cfg _ _ _ HF2) as (X & HX & HXall & HXc).
      exists X. cbn [norm filter snd].
      split; [| split; [exact HXall |]].
      + eapply star_step; [exact Hmix |]. rewrite app_nil_r. exact HX.
      + eapply Permutation_trans; [exact HXc |].
        rewrite <- flat_map_concat_map.
        exact (local_step_denote L (st :: E0) _ (lstep_step L (st :: E0))).
  Qed.

  (** ** …and the whole d-stage, leaf after leaf in the displayed order *)

  Definition dstep_leaf (S : process) : process :=
    match S with
    | terminated            => terminated
    | phase (r_more L) K T  => advance r_done K T
    | phase r_done K T      => phase r_done K T
    end.

  Definition dblock_leaf (S : process) : lblock :=
    match S with
    | terminated  => l_skip
    | phase R _ _ => residual_lblock R
    end.

  Lemma drun_row : forall (P : program) (E : ensemble dim),
      runs_to (P, E) (row_map dstep_leaf P)
              (denote (lseq (row_map dblock_leaf P)) E).
  Proof.
    intro P; induction P as [S | P1 IH1 P2 IH2]; intro E; cbn [row_map lseq].
    - destruct S as [| R K T];
        [cbn [dstep_leaf dblock_leaf denote]; apply runs_to_refl |].
      destruct R as [| L];
        [cbn [dstep_leaf dblock_leaf residual_lblock denote]; apply runs_to_refl |].
      cbn [dstep_leaf dblock_leaf residual_lblock].
      exact (leaf_runs (Datatypes.S (lb_size L)) L (Nat.le_refl _)
               (leaf (phase (r_more L) K T)) ph_here K T E eq_refl).
    - cbn [denote].
      apply (runs_to_trans _ (par (row_map dstep_leaf P1) P2) _
               (lseq (row_map dblock_leaf P2))).
      + apply runs_to_par_l, IH1.
      + intro E'. apply runs_to_par_r, IH2.
  Qed.


(** ** 30. Par-Comp-MP — running the phase, against arbitrary tails *********

    §6 and §7 proved everything about [kprog k], the phase over TERMINATED
    tails, which is all Comm-Select-MP needs.  Par-Comp-MP runs the same
    phase in front of the cut's tail, so the selection has to be redone one
    notch more generally: [kmerge k t].  The proofs are §6's, verbatim
    except for the leaf, where the continuation is T rather than ↓.

    The schedule itself is not read off a given run: [find_kpair] BUILDS one.
    [wf_kchannels] is what makes that possible — naming a channel already
    determines the matched pair — and [chan_pair]'s party count is what puts
    the two endpoints at different leaves, which [ds_comm] needs and two
    [kpick]s alone do not give.
*********************************************************************)

  (** [kprog k] is the phase over TERMINATED tails, which is all
      Comm-Select-MP needs.  Par-Comp-MP runs the same phase in front of the
      cut's tail, so everything §6/§7 proved about [kprog] has to be redone
      one notch more generally — [kmerge k t] is that notch. *)
  Fixpoint kmerge (k : krow) (t : program) : program :=
    match k, t with
    | leaf K,    leaf T    => leaf (advance r_done K T)
    | par k1 k2, par t1 t2 => par (kmerge k1 t1) (kmerge k2 t2)
    | _,         _         => t
    end.

  Lemma kmerge_eps : forall k t,
      same_shape k t -> row_all (fun K => K = ε) k -> kmerge k t = t.
  Proof.
    intro k; induction k as [K | k1 IH1 k2 IH2]; intros [T | t1 t2] Hsh Heps;
      cbn in Hsh |- *; try contradiction.
    - rewrite Heps; reflexivity.
    - destruct Hsh as (H1 & H2); destruct Heps as (E1 & E2).
      rewrite (IH1 t1 H1 E1), (IH2 t2 H2 E2); reflexivity.
  Qed.

  Lemma kpick_shape : forall k a k',
      k ∋ₖ a □ k' -> forall {B} (r : row B), same_shape k r -> same_shape k' r.
  Proof.
    intros k a k' H; induction H as
      [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH];
      intros B [b | r1 r2] Hsh; cbn in Hsh |- *; try contradiction;
      try exact Logic.I.
    - destruct Hsh as (H1 & H2); split; [exact (IH B r1 H1) | exact H2].
    - destruct Hsh as (H1 & H2); split; [exact H1 | exact (IH B r2 H2)].
  Qed.

  Lemma kpick_replace_m : forall k a k',
      k ∋ₖ a □ k' -> forall t, same_shape k t ->
      exists K K' T, K ∋ a □ K' /\
        replace_leaf (phase r_done K T) (advance r_done K' T)
                     (kmerge k t) (kmerge k' t).
  Proof.
    intros k a k' H; induction H as
      [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH];
      intros [T | t1 t2] Hsh; cbn in Hsh |- *; try contradiction.
    - exists K, K', T. split; [exact Hp |].
      destruct K as [| a0 K0]; [inversion Hp |]. cbn [advance]. apply rl_here.
    - destruct Hsh as (H1 & H2).
      destruct (IH t1 H1) as (K & K' & T & Hp & Hr).
      exists K, K', T. split; [exact Hp | apply rl_left, Hr].
    - destruct Hsh as (H1 & H2).
      destruct (IH t2 H2) as (K & K' & T & Hp & Hr).
      exists K, K', T. split; [exact Hp | apply rl_right, Hr].
  Qed.

  (** The selected pair steps, with the tails carried along.  [chan_pair]'s
      party count is again what puts the two endpoints in different leaves. *)
  Lemma comm_pair_step_m : forall k a kmid,
      k ∋ₖ a □ kmid ->
      forall c e x k' t,
        a = c_send c e ->
        chan_pair k c ->
        same_shape k t ->
        kmid ∋ₖ c_recv c x □ k' ->
        forall E, Σ ⊳ ‹ kmerge k t, E › ⇝
          {|| kmerge k' t, rmap x e E ||}.
  Proof.
    intros k a kmid H1.
    induction H1 as [K a K' Hp | k1 k1' k2 a H IH | k1 k2 k2' a H IH];
      intros c e x k' t Ha Hcp Hsh H2 E; subst a.
    - exfalso. destruct Hcp as [_ Hpar]; cbn [row_parties] in Hpar.
      destruct (existsb (Nat.eqb c) (cblock_chan K)); discriminate.
    - destruct t as [T | t1 t2]; cbn in Hsh; [contradiction |].
      destruct Hsh as (Hs1 & Hs2).
      inversion H2 as [| kA kA' kB aa HL EqA EqB | kA kB kB' aa HR EqA EqB]; subst.
      + assert (Hcp1 : chan_pair k1 c).
        { destruct Hcp as [Hlen Hpar].
          rewrite krow_endpoints_par in Hlen.
          pose proof (krow_endpoints_perm _ _ _ c H eq_refl) as P1.
          pose proof (krow_endpoints_perm _ _ _ c HL eq_refl) as P2.
          rewrite length_app in Hlen.
          apply Permutation_length in P1, P2. cbn in P1, P2.
          assert (Hk2 : krow_endpoints k2 c = []).
          { destruct (krow_endpoints k2 c); [reflexivity | cbn in Hlen; lia]. }
          split; [lia |].
          cbn [row_parties] in Hpar.
          rewrite (krow_endpoints_nil_parties _ _ Hk2) in Hpar. lia. }
        pose proof (IH c e x _ t1 eq_refl Hcp1 Hs1 HL E) as Hstep.
        pose proof (ds_par_l Σ (kmerge k1 t1) (kmerge k2 t2) E _ Hstep) as Hd.
        cbn [kmerge] in *; cbn [map fst snd] in Hd. exact Hd.
      + destruct (kpick_replace_m _ _ _ H t1 Hs1) as (Ks & Ks' & Ts & HpS & HrS).
        destruct (kpick_replace_m _ _ _ HR t2 Hs2) as (Kr & Kr' & Tr & HpR & HrR).
        cbn [kmerge].
        exact (ds_comm_lr Σ _ _ _ _ Ks Ks' Kr Kr' Ts Tr c e x E HpS HpR HrS HrR).
    - destruct t as [T | t1 t2]; cbn in Hsh; [contradiction |].
      destruct Hsh as (Hs1 & Hs2).
      inversion H2 as [| kA kA' kB aa HL EqA EqB | kA kB kB' aa HR EqA EqB]; subst.
      + destruct (kpick_replace_m _ _ _ H t2 Hs2) as (Ks & Ks' & Ts & HpS & HrS).
        destruct (kpick_replace_m _ _ _ HL t1 Hs1) as (Kr & Kr' & Tr & HpR & HrR).
        cbn [kmerge].
        exact (ds_comm_rl Σ _ _ _ _ Ks Ks' Kr Kr' Ts Tr c e x E HpS HpR HrS HrR).
      + assert (Hcp2 : chan_pair k2 c).
        { destruct Hcp as [Hlen Hpar].
          rewrite krow_endpoints_par in Hlen.
          pose proof (krow_endpoints_perm _ _ _ c H eq_refl) as P1.
          pose proof (krow_endpoints_perm _ _ _ c HR eq_refl) as P2.
          rewrite length_app in Hlen.
          apply Permutation_length in P1, P2. cbn in P1, P2.
          assert (Hk1 : krow_endpoints k1 c = []).
          { destruct (krow_endpoints k1 c); [reflexivity | cbn in Hlen; lia]. }
          split; [lia |].
          cbn [row_parties] in Hpar.
          rewrite (krow_endpoints_nil_parties _ _ Hk1) in Hpar. lia. }
        pose proof (IH c e x _ t2 eq_refl Hcp2 Hs2 HR E) as Hstep.
        pose proof (ds_par_r Σ (kmerge k1 t1) (kmerge k2 t2) E _ Hstep) as Hd.
        cbn [kmerge] in *; cbn [map fst snd] in Hd. exact Hd.
  Qed.



  (** ** Finding the next matched pair *)

  Lemma picks_of_In : forall K a, In a K -> exists K', K ∋ a □ K'.
  Proof.
    intros K a; induction K as [| b K IH]; intro H; [contradiction |].
    destruct H as [He | H]; [subst; exists K; apply pick_here |].
    destruct (IH H) as (K' & HK). exists (b :: K'); apply pick_there, HK.
  Qed.

  Lemma kpick_of_In : forall k a,
      In a (krow_actions k) -> exists k', k ∋ₖ a □ k'.
  Proof.
    intro k; induction k as [K | k1 IH1 k2 IH2]; intros a Hin.
    - rewrite krow_actions_leaf in Hin.
      destruct (picks_of_In K a Hin) as (K' & HK).
      exists (leaf K'); apply kp_here, HK.
    - rewrite krow_actions_par in Hin; apply in_app_or in Hin as [Hin | Hin].
      + destruct (IH1 a Hin) as (k1' & H). exists (par k1' k2); apply kp_left, H.
      + destruct (IH2 a Hin) as (k2' & H). exists (par k1 k2'); apply kp_right, H.
  Qed.

  Lemma krow_actions_nil_eps : forall k,
      krow_actions k = nil -> row_all (fun K => K = ε) k.
  Proof.
    intro k; induction k as [K | k1 IH1 k2 IH2]; intro H; cbn [row_all].
    - rewrite krow_actions_leaf in H; exact H.
    - rewrite krow_actions_par in H.
      apply app_eq_nil in H as (H1 & H2). split; [apply IH1, H1 | apply IH2, H2].
  Qed.

  Lemma find_kpair : forall k,
      wf_kchannels k -> krow_actions k <> nil ->
      exists c e x k', kpair k c e x k' /\ chan_pair k c.
  Proof.
    intros k Hwf Hne.
    destruct (krow_actions k) as [| a rest] eqn:Ek; [exfalso; apply Hne; reflexivity |].
    assert (Hin : In a (krow_actions k)) by (rewrite Ek; left; reflexivity).
    set (c := caction_chan a).
    assert (Hch : In c (krow_chan k))
      by (rewrite krow_chan_actions; apply in_map, Hin).
    destruct (Hwf c Hch) as (Hs & Hr & Hp).
    (* the unique output on c *)
    destruct (filter is_send (krow_endpoints k c)) as [| b bs] eqn:Eb;
      [cbn in Hs; discriminate |].
    assert (Hbin : In b (filter is_send (krow_endpoints k c)))
      by (rewrite Eb; left; reflexivity).
    apply filter_In in Hbin as (Hbe & Hbs).
    unfold krow_endpoints in Hbe; apply filter_In in Hbe as (HbA & Hbc).
    apply Nat.eqb_eq in Hbc.
    destruct b as [cb eb | cb xb]; cbn in Hbs; [| discriminate].
    cbn in Hbc; subst cb.
    (* the unique input on c *)
    destruct (filter (fun a0 => negb (is_send a0)) (krow_endpoints k c))
      as [| d ds] eqn:Ed; [cbn in Hr; discriminate |].
    assert (Hdin : In d (filter (fun a0 => negb (is_send a0)) (krow_endpoints k c)))
      by (rewrite Ed; left; reflexivity).
    apply filter_In in Hdin as (Hde & Hds).
    unfold krow_endpoints in Hde; apply filter_In in Hde as (HdA & Hdc).
    apply Nat.eqb_eq in Hdc.
    destruct d as [cd ed | cd xd]; cbn in Hds; [discriminate |].
    cbn in Hdc; subst cd.
    destruct (kpick_of_In k _ HbA) as (kmid & Hpk1).
    assert (HdM : In (c_recv c xd) (krow_actions kmid)).
    { pose proof (kpick_perm _ _ _ Hpk1) as Hperm.
      assert (Hin2 : In (c_recv c xd) (c_send c eb :: krow_actions kmid))
        by (eapply Permutation_in; [exact Hperm | exact HdA]).
      destruct Hin2 as [Heq | Hin2]; [discriminate | exact Hin2]. }
    destruct (kpick_of_In kmid _ HdM) as (k' & Hpk2).
    exists c, eb, xd, k'.
    split; [exists kmid; split; assumption
           | exact (wf_kchannels_chan_pair k c Hwf Hch)].
  Qed.

  (** ** A schedule exists, and it is a run of the merged program *)

  Lemma krun_exists : forall n k, (length (krow_actions k) <= n)%nat ->
      wf_phase k -> forall E : ensemble dim, exists Ek, krun k E Ek.
  Proof.
    induction n as [| n IH]; intros k Hn Hwf E.
    - exists E. apply krun_nil, krow_actions_nil_eps.
      destruct (krow_actions k); [reflexivity | cbn in Hn; lia].
    - destruct (krow_actions k) as [| a rest] eqn:Eqk.
      + exists E. apply krun_nil, krow_actions_nil_eps, Eqk.
      + assert (Hne : krow_actions k <> nil) by (rewrite Eqk; discriminate).
        destruct (find_kpair k (proj1 Hwf) Hne) as (c & e & x & k' & Hpair & Hcp).
        destruct Hpair as (kmid & Hs & Hr).
        assert (Hlen : length (krow_actions k)
                       = (2 + length (krow_actions k'))%nat).
        { pose proof (Permutation_length
            (kpair_actions_perm _ _ _ _ _ (ex_intro _ kmid (conj Hs Hr)))) as HL.
          cbn [length] in HL; lia. }
        rewrite Eqk in Hlen; cbn [length] in Hlen; cbn [length] in Hn.
        assert (Hwf' : wf_phase k') by exact (wf_phase_pair k c e x kmid k' Hwf Hs Hr).
        destruct (IH k' ltac:(lia) Hwf' (rmap x e E)) as (Ek & Hrun).
        exists Ek. eapply krun_cons; [exists kmid; split; eassumption | | exact Hrun].
        intro E0. exact (comm_pair_step k _ kmid Hs c e x k' eq_refl Hcp Hr E0).
  Qed.

  Lemma krun_star : forall k (E Ek : ensemble dim),
      krun k E Ek -> forall t, same_shape k t -> wf_phase k ->
      step_star Σ (norm {|| kmerge k t, E ||}) (norm {|| t, Ek ||}).
  Proof.
    intros k E Ek H;
      induction H as [k E Heps | k c e x k' E E' Hp Hstep Hrun IH];
      intros t Hsh Hwf.
    - rewrite (kmerge_eps k t Hsh Heps). apply star_refl.
    - destruct Hp as (kmid & Hs & Hr).
      destruct E as [| st E0].
      + cbn [norm filter snd].
        assert (Hnil : E' = nil)
          by (apply (krun_nil_ens k'); unfold rmap in Hrun; cbn [map] in Hrun;
              exact Hrun).
        rewrite Hnil; cbn [norm filter snd]; apply star_refl.
      + assert (Hcp : chan_pair k c) by exact (wf_phase_chan_pair k kmid c e Hwf Hs).
        assert (Hd : Σ ⊳ ‹ kmerge k t, st :: E0 › ⇝
                       {|| kmerge k' t, rmap x e (st :: E0) ||})
          by exact (comm_pair_step_m k _ kmid Hs c e x k' t eq_refl Hcp Hsh Hr _).
        assert (Hmix : mixed_step Σ {|| kmerge k t, st :: E0 ||}
                         (norm ({|| kmerge k' t, rmap x e (st :: E0) ||} ⊎ nil)))
          by (apply (mixed_lift Σ _ (kmerge k t) (st :: E0) nil _
                       (Permutation_refl _)); exact Hd).
        cbn [norm filter snd].
        eapply star_step; [exact Hmix |].
        rewrite app_nil_r.
        apply IH;
          [ exact (kpick_shape _ _ _ Hr _ (kpick_shape _ _ _ Hs _ Hsh))
          | exact (wf_phase_pair k c e x kmid k' Hwf Hs Hr) ].
  Qed.


(** ** 31. Par-Comp-MP — the three stages, joined **************************

    [par_comp_factor] is the whole construction: every terminating run of P
    is matched by one that does the d-stage first (§29), pops the leaves the
    semantics cannot pop (§28), runs the phase (§30), and leaves the tail —
    and by §27 the two runs have the same collapse, so the premises may be
    read off the constructed one.

    Nothing is ever merged back: the d-stage leaves a SET of components with
    the same program, and the factorisation keeps them apart all the way down
    to single states.  That is why the statement is a pair of [Forall2]s over
    a [concat] rather than an equation about one ensemble.
*********************************************************************)

  (** ** The cut, read off leaf by leaf *)

  Definition kblock_leaf (S : process) : cblock :=
    match S with terminated => ε | phase _ K _ => K end.

  Definition tail_leaf (S : process) : process :=
    match S with terminated => terminated | phase _ _ T => T end.

  Lemma cut_rows : forall P,
      cut P = (row_map dblock_leaf P, row_map kblock_leaf P,
               row_map tail_leaf P).
  Proof.
    intro P; induction P as [S | P1 IH1 P2 IH2]; cbn [cut row_map].
    - destruct S as [| R K T]; reflexivity.
    - rewrite IH1, IH2; reflexivity.
  Qed.

  Lemma cut_shape_kt : forall P,
      same_shape (row_map kblock_leaf P) (row_map tail_leaf P).
  Proof.
    intro P; induction P as [S | P1 IH1 P2 IH2]; cbn [row_map same_shape];
      [exact Logic.I | split; assumption].
  Qed.

  (** ** The d-stage's target pops to the k-stage's source *)

  Lemma pops_dstep_kmerge : forall P,
      pops (row_map dstep_leaf P)
           (kmerge (row_map kblock_leaf P) (row_map tail_leaf P)).
  Proof.
    intro P; induction P as [S | P1 IH1 P2 IH2]; cbn [row_map kmerge].
    - destruct S as [| R K T]; [apply pops_keep |].
      destruct R as [| L]; cbn [dstep_leaf kblock_leaf tail_leaf].
      + destruct K as [| a K0]; cbn [advance]; [apply pops_pop | apply pops_keep].
      + apply pops_keep.
    - constructor; assumption.
  Qed.

  (** ** …and popping keeps the invariant, because it changes no footprint *)

  Lemma pops_prog_fp : forall P Q,
      pops P Q ->
      program_change Q = program_change P
      /\ program_read Q = program_read P
      /\ program_qvar Q = program_qvar P
      /\ program_cvar Q = program_cvar P
      /\ program_actions Q = program_actions P.
  Proof.
    intros P Q H; induction H as [S | T | A A' B B' H1 IH1 H2 IH2].
    - repeat split; reflexivity.
    - unfold program_change, program_read, program_qvar, program_cvar,
        program_actions, process_cvar; cbn [row_flat process_change process_read
        process_qvar process_actions residual_change residual_read
        residual_qvar cblock_change cblock_read flat_map app].
      repeat split; reflexivity.
    - destruct IH1 as (A1 & A2 & A3 & A4 & A5);
        destruct IH2 as (B1 & B2 & B3 & B4 & B5).
      unfold program_change, program_read, program_qvar, program_cvar,
        program_actions in *; cbn [row_flat].
      repeat split; congruence.
  Qed.

  Lemma pops_ownership : forall P Q, pops P Q -> wf_ownership P -> wf_ownership Q.
  Proof.
    intros P Q H; induction H as [S | T | A A' B B' H1 IH1 H2 IH2]; intro Hown;
      cbn [wf_ownership] in *; try exact Logic.I.
    destruct Hown as (Ha & Hb & Hc1 & Hc2 & Hc3).
    destruct (pops_prog_fp _ _ H1) as (E1 & _ & E3 & E4 & _).
    destruct (pops_prog_fp _ _ H2) as (F1 & _ & F3 & F4 & _).
    split; [exact (IH1 Ha) | split; [exact (IH2 Hb) |]].
    unfold cross_disjoint; rewrite E1, E3, E4, F1, F3, F4.
    exact (conj Hc1 (conj Hc2 Hc3)).
  Qed.

  Lemma pops_blocks_indep : forall P Q,
      pops P Q -> blocks_indep P -> blocks_indep Q.
  Proof.
    intros P Q H; induction H as [S | T | A A' B B' H1 IH1 H2 IH2]; intro Hbi;
      cbn [blocks_indep row_all] in *.
    - exact Hbi.
    - exact (proj2 (proj2 Hbi)).
    - destruct Hbi as (Ha & Hb); split; [exact (IH1 Ha) | exact (IH2 Hb)].
  Qed.

  Lemma pops_wf_run : forall P Q, pops P Q -> wf_run P -> wf_run Q.
  Proof.
    intros P Q H (Hown & Hcu & Hbi).
    destruct (pops_prog_fp _ _ H) as (_ & _ & _ & _ & Hact).
    split; [exact (pops_ownership _ _ H Hown) | split].
    - unfold chan_unique in *; rewrite Hact; exact Hcu.
    - exact (pops_blocks_indep _ _ H Hbi).
  Qed.



  (** ** Definition 2.1 makes the displayed phase a legal Comm-Select phase *)

  Lemma process_chan_split : forall T,
      process_chan T = cblock_chan (kblock_leaf T) ++ process_chan (tail_leaf T).
  Proof. intros [| R K T']; reflexivity. Qed.

  Lemma row_parties_ext : forall (P : program) c,
      (forall T, In T (row_leaves P) ->
                 (In c (process_chan T) <-> In c (cblock_chan (kblock_leaf T)))) ->
      row_parties cblock_chan (row_map kblock_leaf P) c
      = row_parties process_chan P c.
  Proof.
    intro P; induction P as [S | P1 IH1 P2 IH2]; intros c Hiff;
      cbn [row_map row_parties].
    - destruct (Hiff S ltac:(left; reflexivity)) as (Hfwd & Hbwd).
      destruct (existsb (Nat.eqb c) (cblock_chan (kblock_leaf S))) eqn:E1;
        destruct (existsb (Nat.eqb c) (process_chan S)) eqn:E2;
        try reflexivity; exfalso.
      + apply (proj1 (existsb_eqb_true_iff _ _)) in E1.
        apply Hbwd in E1.
        rewrite (proj2 (existsb_eqb_true_iff _ _) E1) in E2; discriminate.
      + apply (proj1 (existsb_eqb_true_iff _ _)) in E2.
        apply Hfwd in E2.
        rewrite (proj2 (existsb_eqb_true_iff _ _) E2) in E1; discriminate.
    - rewrite (IH1 c), (IH2 c); [reflexivity | |];
        intros T HT; apply Hiff, in_or_app; [right | left]; exact HT.
  Qed.

  Lemma flat_map_id : forall {A} (l : list (list A)),
      flat_map (fun x => x) l = concat l.
  Proof. intros A l; induction l as [| a l IH]; cbn; [reflexivity | rewrite IH;
    reflexivity]. Qed.

  Lemma wf_program_wf_phase : forall P d k t,
      cut P = (d, k, t) -> wf_program P -> wf_phase k.
  Proof.
    intros P d k t Hcut (Hown & Hch & Hal & Hind).
    pose proof (cut_rows P) as Hrows; rewrite Hcut in Hrows.
    injection Hrows as Hd Hk Ht.
    pose proof (cut_chan_disjoint P d k t Hch Hal Hcut) as Hdisj.
    pose proof (cut_actions P d k t Hcut) as Hsplit.
    (* the tail holds no endpoint of a displayed channel *)
    assert (Htnil : forall c, In c (krow_chan k) ->
               filter (fun a => Nat.eqb (caction_chan a) c) (program_actions t)
               = nil).
    { intros c Hc. apply (proj2 (filter_chan_nil_iff c (program_actions t))).
      rewrite <- program_chan_actions. intro Hin; exact (Hdisj c Hc Hin). }
    assert (Hperm : forall c, In c (krow_chan k) ->
               Permutation (endpoints_of P c) (krow_endpoints k c)).
    { intros c Hc. unfold endpoints_of, krow_endpoints.
      eapply Permutation_trans; [apply (permutation_filter _ _ _ _ Hsplit) |].
      rewrite filter_app, (Htnil c Hc), app_nil_r. apply Permutation_refl. }
    assert (HinP : forall c, In c (krow_chan k) -> In c (program_chan P)).
    { intros c Hc. rewrite krow_chan_actions' in Hc.
      apply in_map_iff in Hc as (a & Ha & HaIn).
      rewrite program_chan_actions; apply in_map_iff; exists a; split;
        [exact Ha |].
      eapply Permutation_in; [apply Permutation_sym, Hsplit |].
      apply in_or_app; left; exact HaIn. }
    split; [| split].
    - intros c Hc.
      destruct (Hch c (HinP c Hc)) as (Hs & Hr & Hp).
      split; [| split].
      + rewrite <- (perm_filter_len is_send _ _ (Hperm c Hc)); exact Hs.
      + rewrite <- (perm_filter_len (fun a => negb (is_send a)) _ _
                      (Hperm c Hc)); exact Hr.
      + rewrite Hk. rewrite row_parties_ext; [exact Hp |].
        intros T HT; split; [| intro Hin; rewrite process_chan_split;
                              apply in_or_app; left; exact Hin].
        intro Hin. rewrite process_chan_split in Hin.
        apply in_app_or in Hin as [Hin | Hin]; [exact Hin | exfalso].
        apply (Hdisj c Hc). rewrite Ht.
        unfold program_chan; rewrite row_flat_leaves, row_leaves_map.
        apply in_flat_map; exists (tail_leaf T); split;
          [apply in_map, HT | exact Hin].
    - destruct (Hind O) as (Hnd & _).
      rewrite recv_targets_concat in Hnd.
      unfold phase_recv. rewrite Hk.
      replace (krow_actions (row_map kblock_leaf P))
        with (concat (phase_at P O)); [exact Hnd |].
      unfold krow_actions.
      rewrite row_flat_leaves, row_leaves_map, flat_map_id, phase_at_leaves.
      f_equal. apply map_ext; intros [| R K T']; reflexivity.
    - destruct (Hind O) as (_ & Hdj).
      rewrite recv_targets_concat, output_reads_concat in Hdj.
      unfold phase_recv, phase_oread. rewrite Hk.
      replace (krow_actions (row_map kblock_leaf P))
        with (concat (phase_at P O)); [exact Hdj |].
      unfold krow_actions.
      rewrite row_flat_leaves, row_leaves_map, flat_map_id, phase_at_leaves.
      f_equal. apply map_ext; intros [| R K T']; reflexivity.
  Qed.



  (** ** Taking a terminating run apart *)

  Lemma Term_cfg_nil : forall E, Term_cfg nil E -> E = nil.
  Proof.
    intros E (G & Hs & _ & Hc); cbn [norm filter] in Hs.
    rewrite (step_star_nil G Hs) in Hc.
    apply Permutation_nil in Hc; exact Hc.
  Qed.

  Lemma Term_cfg_components : forall (G : distri_config dim) E,
      Term_cfg G E ->
      exists Es, Forall2 (fun c Ec => Term_cfg (c :: nil) Ec) G Es
              /\ Permutation E (concat Es).
  Proof.
    intro G; induction G as [| c G IH]; intros E HT.
    - exists nil. split; [constructor |].
      rewrite (Term_cfg_nil E HT); apply Permutation_refl.
    - destruct (Term_cfg_split (c :: nil) G E HT) as (EA & EB & HA & HB & Hp).
      destruct (IH EB HB) as (Es & HF & Hpe).
      exists (EA :: Es). split; [constructor; assumption |].
      cbn [concat]. eapply Permutation_trans; [exact Hp |].
      apply Permutation_app_head, Hpe.
  Qed.

  Lemma Term_cfg_Term : forall P st E,
      Term_cfg ((P, st :: nil) :: nil) E ->
      exists E0, Term Σ P st E0 /\ Permutation E0 E.
  Proof.
    intros P st E (G & Hs & Ht & Hc); cbn [norm filter snd] in Hs.
    exists (collapse G).
    split; [exists G; split; [exact Hs | split; [exact Ht | reflexivity]]
           | exact Hc].
  Qed.

  Lemma Term_cfg_states : forall P (E : ensemble dim) E',
      Term_cfg ((P, E) :: nil) E' ->
      exists Es, Forall2 (fun st Est => Term Σ P st Est) E Es
              /\ Permutation E' (concat Es).
  Proof.
    intros P E; induction E as [| st E0 IH]; intros E' HT.
    - exists nil. split; [constructor |].
      destruct HT as (G & Hs & _ & Hc); cbn [norm filter snd] in Hs.
      rewrite (step_star_nil G Hs) in Hc.
      apply Permutation_nil in Hc; rewrite Hc; apply Permutation_refl.
    - destruct E0 as [| st2 E1].
      + destruct (Term_cfg_Term P st E' HT) as (E0' & HT0 & Hp).
        exists (E0' :: nil). split; [constructor; [exact HT0 | constructor] |].
        cbn [concat]; rewrite app_nil_r. apply Permutation_sym, Hp.
      + destruct HT as (G & Hs & Ht & Hc); cbn [norm filter snd] in Hs.
        assert (Hte : Term_ens P (st :: st2 :: E1) (collapse G))
          by (exists G; split; [exact Hs | split; [exact Ht | reflexivity]]).
        destruct (Term_ens_app P (st :: nil) (st2 :: E1) _
                    ltac:(discriminate) ltac:(discriminate) Hte)
          as (E1' & E2' & HA & HB & Hp).
        assert (HBc : Term_cfg ((P, st2 :: E1) :: nil) E2').
        { destruct HB as (GB & HsB & HtB & HcB). exists GB.
          cbn [norm filter snd].
          split; [exact HsB | split; [exact HtB | rewrite HcB;
            apply Permutation_refl]]. }
        destruct (IH E2' HBc) as (Es & HF & Hpe).
        exists (E1' :: Es). split; [constructor; [exact HA | exact HF] |].
        cbn [concat].
        eapply Permutation_trans; [apply Permutation_sym, Hc |].
        eapply Permutation_trans; [exact Hp |].
        apply Permutation_app_head, Hpe.
  Qed.

  Lemma krun_states : forall k (E Ek : ensemble dim),
      krun k E Ek ->
      exists Eks, Forall2 (fun st Ekst => krun k (st :: nil) Ekst) E Eks
               /\ Ek = concat Eks.
  Proof.
    intros k E; induction E as [| st E0 IH]; intros Ek Hr.
    - exists nil. split; [constructor |].
      cbn [concat]. exact (krun_nil_ens k Ek Hr).
    - destruct (krun_app k _ _ Hr (st :: nil) E0 eq_refl)
        as (E1' & E2' & H1 & H2 & HE).
      destruct (IH E2' H2) as (Eks & HF & Hc).
      exists (E1' :: Eks). split; [constructor; assumption |].
      cbn [concat]; rewrite HE, Hc; reflexivity.
  Qed.

  (** ** The k-stage and the tail, component by component *)

  Lemma factor_group : local_ops -> forall Pd k t (G : distri_config dim) Efin,
      pops Pd (kmerge k t) -> wf_run Pd -> wf_phase k -> same_shape k t ->
      Forall (fun c => fst c = Pd) G ->
      Term_cfg G Efin ->
      exists Eks Efs,
        Forall2 (fun st Ek => krun k (st :: nil) Ek) (collapse G) Eks
        /\ Forall2 (fun st Ef => Term Σ t st Ef) (concat Eks) Efs
        /\ Permutation Efin (concat Efs).
  Proof.
    intros Hloc Pd k t G; induction G as [| c G IH]; intros Efin Hp Hwr Hwf Hsh
      Hall HT.
    - exists nil, nil. cbn [collapse flat_map concat].
      split; [constructor | split; [constructor |]].
      rewrite (Term_cfg_nil Efin HT); apply Permutation_refl.
    - destruct (Term_cfg_split (c :: nil) G Efin HT) as (E1 & E2 & HA & HB & Hpe).
      destruct c as [Pc Ec]; cbn [fst] in Hall.
      pose proof (Forall_inv Hall) as Hpc; cbn [fst] in Hpc; subst Pc.
      (* pop the stuck leaves, then run the phase *)
      assert (HA' : Term_cfg ((kmerge k t, Ec) :: nil) E1)
        by exact (Term_cfg_pops Pd (kmerge k t) Ec E1 Hp HA).
      destruct (krun_exists (length (krow_actions k)) k (Nat.le_refl _) Hwf Ec)
        as (Ek & Hkr).
      assert (Hwrm : wf_run (kmerge k t)) by exact (pops_wf_run Pd _ Hp Hwr).
      assert (HA'' : Term_cfg ((t, Ek) :: nil) E1).
      { apply (proj1 (Term_cfg_norm _ _)).
        apply (Term_cfg_reduct Hloc (norm ((kmerge k t, Ec) :: nil))
                 (norm ((t, Ek) :: nil)) E1).
        - apply Forall_norm; constructor; [exact Hwrm | constructor].
        - apply norm_idem.
        - exact (krun_star k Ec Ek Hkr t Hsh Hwf).
        - apply (proj2 (Term_cfg_norm _ _)), HA'. }
      destruct (krun_states k Ec Ek Hkr) as (Eks1 & HF1 & HE1).
      destruct (Term_cfg_states t Ek E1 HA'') as (Efs1 & HF2 & Hpe1).
      destruct (IH E2 Hp Hwr Hwf Hsh (Forall_inv_tail Hall) HB)
        as (Eks2 & Efs2 & HG1 & HG2 & HG3).
      exists (Eks1 ++ Eks2), (Efs1 ++ Efs2).
      split; [| split].
      + unfold collapse; cbn [flat_map snd]; fold (collapse G).
        apply Forall2_app; assumption.
      + rewrite concat_app, <- HE1. apply Forall2_app; assumption.
      + rewrite concat_app.
        eapply Permutation_trans; [exact Hpe |].
        apply Permutation_app; assumption.
  Qed.



  (** ** Every terminating run of P factors through the three stages *)

  Lemma par_comp_factor : local_ops ->
    forall P d k t st (E : ensemble dim),
      cut P = (d, k, t) -> wf_program P -> Term Σ P st E ->
      exists Ed Eks Efs,
        Permutation Ed (denote (lseq d) (st :: nil))
        /\ Forall2 (fun st1 Ek => krun k (st1 :: nil) Ek) Ed Eks
        /\ Forall2 (fun st2 Ef => Term Σ t st2 Ef) (concat Eks) Efs
        /\ Permutation E (concat Efs).
  Proof.
    intros Hloc P d k t st E Hcut Hwf HT.
    pose proof (cut_rows P) as Hrows; rewrite Hcut in Hrows.
    injection Hrows as Hd Hk Ht.
    assert (HTc : Term_cfg ((P, st :: nil) :: nil) E).
    { destruct HT as (G & Hs & Htm & Hc). exists G.
      cbn [norm filter snd].
      split; [exact Hs | split; [exact Htm | rewrite Hc; apply Permutation_refl]]. }
    destruct (drun_row P (st :: nil)) as (G1 & Hs1 & Hall1 & Hc1).
    assert (Hwrun : wf_run P) by exact (wf_program_run P Hwf).
    assert (HcfgP : cfg_wf ((P, st :: nil) :: nil))
      by (constructor; [exact Hwrun | constructor]).
    assert (HT1 : Term_cfg G1 E)
      by exact (Term_cfg_reduct Hloc ((P, st :: nil) :: nil) G1 E
                  HcfgP eq_refl Hs1 HTc).
    destruct G1 as [| c1 G1'].
    - exists nil, nil, nil. cbn [concat].
      rewrite (Term_cfg_nil E HT1).
      split; [rewrite Hd; exact Hc1 |
        split; [constructor | split; [constructor | apply Permutation_refl]]].
    - assert (Hcfg1 : cfg_wf (c1 :: G1'))
        by exact (cfg_wf_star _ _ HcfgP Hs1).
      pose proof (Forall_inv Hcfg1) as Hwr1.
      pose proof (Forall_inv Hall1) as Hp1.
      cbv beta in Hp1, Hwr1. rewrite Hp1 in Hwr1.
      destruct (factor_group Hloc (row_map dstep_leaf P) k t (c1 :: G1') E
                  ltac:(rewrite Hk, Ht; apply pops_dstep_kmerge)
                  Hwr1
                  (wf_program_wf_phase P d k t Hcut Hwf)
                  ltac:(rewrite Hk, Ht; apply cut_shape_kt)
                  Hall1 HT1)
        as (Eks & Efs & HF1 & HF2 & Hpe).
      exists (collapse (c1 :: G1')), Eks, Efs.
      split; [rewrite Hd; exact Hc1 |
        split; [exact HF1 | split; assumption]].
  Qed.



  Lemma sum_degree_bound : forall (Q R : assertion dim) (E : ensemble dim)
                                  (Es : list (ensemble dim)),
      Forall2 (fun st Est => (degree Σ Q st <= total_degree Σ R Est)%R) E Es ->
      (total_degree Σ Q E <= total_degree Σ R (concat Es))%R.
  Proof.
    intros Q R E Es H; induction H as [| st Est E Es Hh HF IH].
    - cbn [concat]; unfold total_degree; cbn [map fold_right]; lra.
    - cbn [concat]; rewrite total_degree_app.
      unfold total_degree in *; cbn [map fold_right] in *; lra.
  Qed.

  Lemma row_map_map : forall {A B C} (f : B -> C) (g : A -> B) (r : row A),
      row_map f (row_map g r) = row_map (fun a => f (g a)) r.
  Proof.
    intros A B C f g r; induction r as [a | r1 IH1 r2 IH2]; cbn;
      [reflexivity | rewrite IH1, IH2; reflexivity].
  Qed.

  Lemma row_map_id : forall {A} (r : row A), row_map (fun a => a) r = r.
  Proof.
    intros A r; induction r as [a | r1 IH1 r2 IH2]; cbn;
      [reflexivity | rewrite IH1, IH2; reflexivity].
  Qed.

End SoundnessFacts.
