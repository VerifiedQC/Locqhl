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
    (forall M qs m, WF_Matrix (snd (i_mm Σ M qs) m)).

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

  (** ** 3. Par-Disjoint-MP.  Route: [local_sound] is the one-leaf base
         case; then wf ⟹ DisjMP (Thm 2.1) ⟹ interference freedom (Lemma 1)
         normalises every interleaving to the [locals_seq]
         sequentialisation. *)
  Lemma local_sound : forall (Q R : assertion dim) (L : lblock),
      Σ ⊢ₗ {{ Q }} L {{ R }} ->
      Σ ⊨ {{ Q }} (⟨ₗ L ⟩) {{ R }}.
  Admitted.

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
    - (* Conseq *)          eapply conseq_sound.
      + exact interp_ok.
      + (* wf_assertion of the target postcondition — assertion formation is
           a meta-level check in the paper (p.10); how to thread it through
           derivations is an open design item *)
        admit.
      + eassumption.
      + apply IHHd; assumption.
      + assumption.
  Admitted.

End Soundness.
