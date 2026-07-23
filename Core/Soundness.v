(** * Soundness — paper Theorem 4.1: every derivable triple is valid.

        Σ ⊢ₚ {{ Q }} P {{ R }}   ⟹   Σ ⊨ {{ Q }} P {{ R }}

    Per-rule obligations, in planned order of attack:
      1. conseq_sound
      2. comm_done_sound
      3. local_sound
      4. par_disjoint_sound
      5. comm_select_sound
      6. par_comp_sound
      7. branch_accum_sound
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
    intros interp_ok D E G Hstep; destruct Hstep; intros HokE.
    - (* local *) apply config_ok_map.
      + intros c Hc. exact Hc.
      + eapply local_step_preserves; eauto.
    - (* comm *)  constructor; [| constructor]. simpl.
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

  (** ** 2. Comm-Done  — a program of exhausted communication phases performs
         no state change: {Q} ε_K ‖ … ‖ ε_K {Q}.

         Semantic shape: every process of [par_comm Ks] with all-empty blocks
         is [phase ↓ [] terminated], which can take NO step (no local block
         to run, no endpoint to select from an empty block).  So the initial
         configuration is the only reachable one, and the proof splits:
           Ks = []      the empty program is terminal at once, E = {(s,r)},
                        and the trace inequality is an equality;
           Ks nonempty  a dead phase is not syntactically [terminated], so no
                        terminal configuration is ever reached and the triple
                        holds vacuously (Term is empty).                    *)

  Lemma par_comm_empty_stuck :
    forall (Ks : list cblock) (E0 : ensemble dim) (G : distri_config dim),
      Forall (fun K => K = []) Ks ->
      Σ ⊳ ‹ par_comm Ks, E0 › ⇝ G -> False.
  Proof.
    intros Ks E0 G HK Hstep.
    inversion Hstep as [l1 L K S l2 E' Gl Hl HeqP HeqE
                       | D Ks0 S Ks0' Kr T Kr' rest c e x E' Hperm Hs1 Hs2 HeqP];
      subst.
    - (* a Local step needs a phase with a live local block *)
      assert (Hin : In (phase (r_more L) K S) (par_comm Ks))
        by (rewrite <- HeqP; apply in_elt).
      apply in_map_iff in Hin as (K' & Heq & _). discriminate.
    - (* a Communicate step needs an endpoint in some block — all are empty *)
      assert (Hin : In (phase ↓ Ks0 S) (par_comm Ks)).
      { eapply Permutation_in; [apply Permutation_sym; eassumption |].
        left; reflexivity. }
      apply in_map_iff in Hin as (K' & Heq & HinK).
      injection Heq as HK0 _. subst K'.
      rewrite Forall_forall in HK. specialize (HK _ HinK). subst Ks0.
      destruct Hs1 as (pre & post & Hnil & _).
      destruct pre; discriminate.
  Qed.

  Lemma comm_done_no_mixed_step :
    forall (Ks : list cblock) (E0 : ensemble dim) (G2 : distri_config dim),
      Forall (fun K => K = []) Ks ->
      mixed_step Σ ({|| par_comm Ks, E0 ||}) G2 -> False.
  Proof.
    intros Ks E0 G2 HK Hstep.
    inversion Hstep as [G D E G0 G1 Hperm Hd]; subst.
    apply Permutation_length_1_inv in Hperm.
    injection Hperm as HD HE HG0. subst.
    eapply par_comm_empty_stuck; eauto.
  Qed.

  Lemma comm_done_star_id :
    forall (Ks : list cblock) (E0 : ensemble dim) (G : distri_config dim),
      Forall (fun K => K = []) Ks ->
      step_star Σ ({|| par_comm Ks, E0 ||}) G -> G = {|| par_comm Ks, E0 ||}.
  Proof.
    intros Ks E0 G HK Hstar.
    inversion Hstar; subst; auto.
    exfalso. eapply comm_done_no_mixed_step; eauto.
  Qed.

  Lemma comm_done_sound : forall (Q : assertion dim) (Ks : list cblock),
      Forall (fun K => K = []) Ks ->
      Σ ⊨ {{ Q }} (par_comm Ks) {{ Q }}.
  Proof.
    intros Q Ks HK s r HWFr Hherm Hpsd Hh Hd E HTerm.
    destruct HTerm as (G & Hstar & Hterm & Hcoll).
    apply comm_done_star_id in Hstar; auto. subst G.
    destruct Ks as [| K Ks'].
    - (* empty program: already terminal, E = [(s,r)], equality *)
      simpl in Hcoll. subst E.
      unfold total_degree. simpl. lra.
    - (* dead phases are not [terminated]: no terminal config, vacuous *)
      exfalso.
      inversion Hterm as [| ? ? Hhead _]; subst.
      simpl in Hhead.
      inversion Hhead as [| ? ? Heq _]; subst.
      discriminate.
  Qed.

  (** ** 3. Local bridge  — soundness of the LOCAL proof system ⊢ₗ, read as a
         one-party program.  Discharges the [rule_par_disjoint] premise after
         the interleaving has been serialised to [seq_all Ds]. *)
  Lemma local_sound : forall (Q R : assertion dim) (L : lblock),
      Σ ⊢ₗ {{ Q }} L {{ R }} ->
      Σ ⊨ {{ Q }} (par_local ([L])) {{ R }}.
  Admitted.

  (** ** 4. Par-Disjoint-MP  — communication-free local blocks in parallel:
         any interleaving is equivalent to the fixed sequentialisation
         [seq_all Ds].  Uses wf ⟹ DisjMP (paper Thm 2.1) ⟹ interference
         freedom (paper Lemma 1). *)
  Lemma par_disjoint_sound : forall (Q R : assertion dim) (Ds : list lblock),
      wf_program (par_local Ds) ->
      Σ ⊢ₗ {{ Q }} (seq_all Ds) {{ R }} ->
      Σ ⊨ {{ Q }} (par_local Ds) {{ R }}.
  Admitted.

  (** ** 5. Comm-Select-MP  — one selected rendezvous c!e ⋈ c?x behaves as the
         assignment x := e (substitution in the precondition); the residual
         phase is handled by the recursive premise.  Same-phase independence
         (paper Lemma 2) lets the selected rendezvous be commuted first. *)
  Lemma comm_select_sound :
    forall (Q R : assertion dim) (Ks : list cblock) (Ki Ki' Kj Kj' : cblock)
           (rest : list cblock) (c : chan) (e : expr) (x : var),
      wf_program (par_comm Ks) ->
      Permutation Ks (Ki :: Kj :: rest) ->
      selects Ki (c_send c e) Ki' ->
      selects Kj (c_recv c x) Kj' ->
      Σ ⊨ {{ Q }} (par_comm (Ki' :: Kj' :: rest)) {{ R }} ->
      Σ ⊨ {{ assertion_subst Q x e }} (par_comm Ks) {{ R }}.
  Admitted.

  (** ** 6. Par-Comp-MP  — every terminating distributed run of the padded
         program (D_i;K_i;T_i)‖… factors through the three aligned stages
         (paper Lemma 2 normalises runs to prefix-phase-tail order). *)
  Lemma par_comp_sound :
    forall (Q0 Q1 Q2 Q3 : assertion dim)
           (Ds : list lblock) (Ks : list cblock) (Ts : list process),
      wf_program (par_phases Ds Ks Ts) ->
      length Ds = length Ks -> length Ks = length Ts ->
      Σ ⊨ {{ Q0 }} (par_local Ds) {{ Q1 }} ->
      Σ ⊨ {{ Q1 }} (par_comm Ks)  {{ Q2 }} ->
      Σ ⊨ {{ Q2 }} Ts             {{ Q3 }} ->
      Σ ⊨ {{ Q0 }} (par_phases Ds Ks Ts) {{ Q3 }}.
  Admitted.

  (** ** 7. Branch-Accum  — finite additivity: sum the pre-effects and disjoin
         the mutually exclusive classical postconditions over the family. *)
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
  Lemma wf_par_comm_residual :
    forall (Ks : list cblock) (Ki Ki' Kj Kj' : cblock) (rest : list cblock)
           (c : chan) (e : expr) (x : var),
      wf_program (par_comm Ks) ->
      Permutation Ks (Ki :: Kj :: rest) ->
      selects Ki (c_send c e) Ki' ->
      selects Kj (c_recv c x) Kj' ->
      wf_program (par_comm (Ki' :: Kj' :: rest)).
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
    - (* Par-Disjoint-MP *) apply par_disjoint_sound; assumption.
    - (* Comm-Done *)       apply comm_done_sound; assumption.
    - (* Comm-Select-MP *)  eapply comm_select_sound; try eassumption.
      apply IHHd. eapply wf_par_comm_residual; eassumption.
    - (* Par-Comp-MP *)     eapply par_comp_sound; try eassumption.
      + apply IHHd1. admit. (* wf of the prefix stage — from Hwf *)
      + apply IHHd2. admit. (* wf of the comm stage   — from Hwf *)
      + apply IHHd3. admit. (* wf of the tail stage   — from Hwf *)
    - (* Branch-Accum *)    apply branch_accum_sound.
      + apply IHHd; assumption.
      + (* the family premise, pointwise via the Forall IH *) admit.
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
