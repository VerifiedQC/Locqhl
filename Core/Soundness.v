(** * Soundness — paper Theorem 4.1: every derivable triple is valid.

        Σ ⊢ₚ {{ Q }} P {{ R }}   ⟹   Σ ⊨ {{ Q }} P {{ R }}

    One lemma per rule, then the assembly.  The machinery they run on lives
    in SoundnessFacts.
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Reals.Reals Lra.
From Stdlib Require Import Lia.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import
  Syntax QuantumActions SemanticDomain Semantics Assertions WellFormed Rules
  TraceFacts SoundnessFacts.
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
  (** ** 1. Conseq  ** **)
  Lemma conseq_sound :
    wf_interp Σ ->
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
    pose proof (term_preservation Σ interp_ok P s r E HWFr Hherm Hpsd HTerm) as HE.
    pose proof (total_degree_entails Σ R R' E Hpost HwfR' HE) as Hout.
    lra.
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

  Lemma local_sound :
    wf_interp Σ ->
    forall (Q R : assertion dim) (L : lblock),
      Σ ⊢ₗ {{ Q }} L {{ R }} ->
      Σ ⊨ {{ Q }} (⟨ₗ L ⟩) {{ R }}.
  Proof.
    intros interp_ok Q R L Hd s r HWFr Hherm Hpsd Hh Hdef E HTerm.
    apply one_leaf_adequacy in HTerm.
    rewrite (total_degree_perm Σ R _ _ HTerm).
    assert (Hok : ensemble_ok ((s, r) :: nil))
      by (constructor; [repeat split; assumption | constructor]).
    pose proof (denote_sound Σ interp_ok Q R L Hd ((s, r) :: nil) Hok) as Hle.
    unfold total_degree in Hle |- *. cbn [fold_right map] in Hle.
    rewrite Rplus_0_r in Hle. exact Hle.
  Qed.

  Lemma par_disjoint_sound :
    forall (Q R : assertion dim) (PD : program) (Dseq : lblock),
      wf_ownership PD ->
      locals_seq PD Dseq ->
      Σ ⊢ₗ {{ Q }} Dseq {{ R }} ->
      Σ ⊨ {{ Q }} PD {{ R }}.
  Admitted.

  (** ** 4. Comm-Select-MP.  One rendezvous c!e ⋈ c?x behaves as x := e;
         Lemma 2 commutes the selected rendezvous first. *)
  Lemma comm_select_sound :
    forall (Q R : assertion dim) (PK P1 PK' : program)
           (c : chan) (e : expr) (x : var),
      wf_phase PK ->
      PK ∋ₖ c_send c e □ P1 ->
      P1 ∋ₖ c_recv c x □ PK' ->
      Σ ⊨ {{ Q }} PK' {{ R }} ->
      Σ ⊨ {{ assertion_subst Q x e }} PK {{ R }}.
  Admitted.

  (** ** 5. Par-Comp-MP.  Every terminating run factors through the three
         aligned stages (Lemma 2 normalises runs to prefix-phase-tail
         order). *)
  Lemma par_comp_sound :
    forall (Q0 Q1 Q2 Q3 : assertion dim) (PD PK PT P : program),
      zip3 PD PK PT P ->
      wf_cut PK PT P ->
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
  Proof.
    intros phi B P A0 psi0 fam H0 Hfam Hex
           s r HWFr Hherm Hpsd Hh Hdef E HTerm.
    unfold defined_in, mk_assertion in Hdef;
      cbn [quantum_part] in Hdef; destruct Hdef as (M & HM).
    destruct (qsum_denote_parts Σ s A0 (map fst fam) M HM)
      as ((M0 & HM0) & HAs).
    (* the sum of pre-effects splits the precondition's degree *)
    rewrite (degree_qsum Σ phi A0 (map fst fam) s r M HM).
    (* mutually exclusive guards split the postcondition's degree *)
    rewrite (total_degree_fdisj_exclusive Σ psi0 (map snd fam) B E Hex).
    apply fold_right_Rplus_le.
    - apply (H0 s r HWFr Hherm Hpsd Hh); [exists M0; exact HM0 | exact HTerm].
    - (* the family, one member at a time; drop everything fam-dependent so
         the induction hypothesis stays a plain implication *)
      assert (Hphi : formula_holds Σ s phi = true)
        by (unfold mk_assertion in Hh; cbn [classical_part] in Hh; exact Hh).
      clear Hh Hex HM.
      revert Hfam HAs; induction fam as [| Api fam IH];
        intros Hfam HAs; cbn [map] in HAs |- *.
      + constructor.
      + constructor.
        * apply (Forall_inv Hfam s r HWFr Hherm Hpsd Hphi
                   (Forall_inv HAs) E HTerm).
        * apply IH; [apply (Forall_inv_tail Hfam) | apply (Forall_inv_tail HAs)].
  Qed.

  (** ** Well-formedness is inherited by the sub-programs appearing in rule
         premises.  Soundness no longer needs this — each rule carries its
         own side condition — so these are now the DISCHARGE lemmas: they
         are what supplies those conditions, phase after phase, to someone
         building a derivation for a well-formed source program.  Their
         [wf_program] conclusions are stronger than the rules ask for
         ([wf_phase], [wf_cut]); tightening them is left for when the
         discharge theorem is stated. *)
  Lemma wf_comm_select_residual :
    forall (PK P1 PK' : program) (c : chan) (e : expr) (x : var),
      wf_program PK ->
      PK ∋ₖ c_send c e □ P1 ->
      P1 ∋ₖ c_recv c x □ PK' ->
      wf_program PK'.
  Proof.
    intros PK P1 PK' c e x (Hown & Hch & Hal & Hind) Hr1 Hr2.
    (* the phase's actions lose the send, then the recv *)
    assert (HPK : Permutation (program_actions PK)
                    (c_send c e :: c_recv c x :: program_actions PK')).
    { eapply Permutation_trans;
        [ apply (comm_sel_actions _ _ _ _ Hr1 eq_refl)
        | apply perm_skip, (comm_sel_actions _ _ _ _ Hr2 eq_refl) ]. }
    (* a phase's endpoints all live in phase 0, which loses the same two *)
    assert (HPH : Permutation (concat (phase_at PK 0%nat))
                    (c_send c e :: c_recv c x :: concat (phase_at PK' 0%nat))).
    { eapply Permutation_trans;
        [ apply (comm_sel_phase0 _ _ _ _ Hr1 eq_refl)
        | apply perm_skip, (comm_sel_phase0 _ _ _ _ Hr2 eq_refl) ]. }
    assert (HL : forall k, phase_at PK' (S k) = phase_at PK (S k)).
    { intro k. rewrite (comm_sel_phase_later _ _ _ Hr2 k).
      apply (comm_sel_phase_later _ _ _ Hr1 k). }
    (* c had exactly two endpoints in PK and we consumed both, so c is gone *)
    assert (HinPKc : In c (program_chan PK)).
    { rewrite program_chan_actions. apply (in_map caction_chan _ (c_send c e)).
      apply (Permutation_in _ (Permutation_sym HPK)); left; reflexivity. }
    destruct (Hch c HinPKc) as (Hsc & Hrc & _).
    assert (HcA : filter (fun a => Nat.eqb (caction_chan a) c)
                    (program_actions PK') = nil).
    { pose proof (endpoints_two _ _ Hsc Hrc) as H2. unfold endpoints_of in H2.
      pose proof (filter_perm_cons2_keep
                    (fun a => Nat.eqb (caction_chan a) c) _ _ _ _ HPK
                    (Nat.eqb_refl c) (Nat.eqb_refl c)) as Hcnt.
      apply length_zero_iff_nil. rewrite H2 in Hcnt. lia. }
    assert (HcP0 : filter (fun a => Nat.eqb (caction_chan a) c)
                     (concat (phase_at PK' 0%nat)) = nil).
    { assert (HinPK0 : In c (map caction_chan (concat (phase_at PK 0%nat)))).
      { apply (in_map caction_chan _ (c_send c e)).
        apply (Permutation_in _ (Permutation_sym HPH)); left; reflexivity. }
      pose proof (Hal 0%nat c HinPK0) as HAL. unfold phase_actions in HAL.
      pose proof (filter_perm_cons2_keep
                    (fun a => Nat.eqb (caction_chan a) c) _ _ _ _ HPH
                    (Nat.eqb_refl c) (Nat.eqb_refl c)) as Hcnt.
      apply length_zero_iff_nil. rewrite HAL in Hcnt. lia. }
    split; [| split; [| split]].
    - (* ownership: consuming an endpoint only shrinks footprints *)
      eapply comm_sel_ownership; [exact Hr2 |].
      eapply comm_sel_ownership; [exact Hr1 | exact Hown].
    - (* channels *)
      intros d Hd.
      assert (HdPK : In d (program_chan PK)).
      { rewrite program_chan_actions in Hd |- *.
        revert Hd. apply incl_map. intros y Hy.
        apply (Permutation_in _ (Permutation_sym HPK)); right; right; exact Hy. }
      assert (Hdc : d <> c).
      { intro Heq; subst d.
        apply (proj1 (filter_chan_nil_iff c (program_actions PK')) HcA).
        rewrite <- program_chan_actions. exact Hd. }
      assert (Hgf : (fun a => Nat.eqb (caction_chan a) d) (c_send c e) = false)
        by (apply Nat.eqb_neq; intro H; exact (Hdc (eq_sym H))).
      assert (Hgf' : (fun a => Nat.eqb (caction_chan a) d) (c_recv c x) = false)
        by (apply Nat.eqb_neq; intro H; exact (Hdc (eq_sym H))).
      pose proof (filter_perm_cons2_drop _ _ _ _ _ HPK Hgf Hgf') as Hperm.
      destruct (Hch d HdPK) as (Hsd & Hrd & Hpd).
      unfold endpoints_of in *. repeat split.
      + rewrite <- (Permutation_length (permutation_filter _ is_send _ _ Hperm)).
        exact Hsd.
      + rewrite <- (Permutation_length
                      (permutation_filter _ (fun a => negb (is_send a)) _ _ Hperm)).
        exact Hrd.
      + rewrite (comm_sel_parties _ _ _ _ _ Hr2 eq_refl Hdc).
        rewrite (comm_sel_parties _ _ _ _ _ Hr1 eq_refl Hdc).
        exact Hpd.
    - (* alignment *)
      intros k d Hd. destruct k as [| k]; unfold phase_actions in *.
      + assert (Hdc : d <> c).
        { intro Heq; subst d.
          exact (proj1 (filter_chan_nil_iff c _) HcP0 Hd). }
        assert (Hgf : (fun a => Nat.eqb (caction_chan a) d) (c_send c e) = false)
          by (apply Nat.eqb_neq; intro H; exact (Hdc (eq_sym H))).
        assert (Hgf' : (fun a => Nat.eqb (caction_chan a) d) (c_recv c x) = false)
          by (apply Nat.eqb_neq; intro H; exact (Hdc (eq_sym H))).
        pose proof (filter_perm_cons2_drop _ _ _ _ _ HPH Hgf Hgf') as Hp0.
        assert (HdPK0 : In d (map caction_chan (concat (phase_at PK 0%nat)))).
        { apply filter_chan_nonnil_in. intro Hnil.
          rewrite Hnil in Hp0. apply Permutation_nil in Hp0.
          exact (proj1 (filter_chan_nil_iff d _) Hp0 Hd). }
        rewrite <- (Permutation_length Hp0). exact (Hal 0%nat d HdPK0).
      + rewrite (HL k) in Hd |- *. exact (Hal (S k) d Hd).
    - (* same-phase independence *)
      intro k; destruct k as [| k].
      + destruct (Hind 0%nat) as (HND & HDJ).
        rewrite recv_targets_concat in HND, HDJ |- *.
        rewrite output_reads_concat in HDJ |- *.
        assert (HpR : Permutation
                        (flat_map caction_change (concat (phase_at PK 0%nat)))
                        (x :: flat_map caction_change
                                (concat (phase_at PK' 0%nat)))).
        { eapply Permutation_trans;
            [apply (permutation_flat_map _ _ caction_change _ _ HPH) |].
          simpl. apply Permutation_refl. }
        split.
        * exact (proj2 (proj1 (NoDup_cons_iff _ _)
                          (Permutation_NoDup HpR HND))).
        * eapply disjoint_incl; [exact HDJ | | ];
            [ apply (flat_map_perm_incl caction_change _ _ _ _ HPH)
            | apply (flat_map_perm_incl caction_read _ _ _ _ HPH) ].
      + rewrite (HL k). exact (Hind (S k)).
  Qed.

  (** Each row's footprints are bounded by the zipped program's: a leaf
      [phase (r_more D) K T] contains its own D, K and T. *)
  Lemma wf_zip3_prefix : forall PD PK PT P : program,
      zip3 PD PK PT P -> wf_program P -> wf_program PD.
  Proof.
    intros PD PK PT P Hz (Hown & _ & _ & _).
    split; [| split; [| split]].
    - eapply zip3_prefix_ownership; eassumption.
    - intros c Hc. rewrite (zip3_prefix_chan _ _ _ _ Hz) in Hc. destruct Hc.
    - intros k c Hc. unfold phase_actions in Hc.
      rewrite (zip3_prefix_actions _ _ _ _ Hz) in Hc. destruct Hc.
    - intro k. rewrite recv_targets_concat, output_reads_concat,
        (zip3_prefix_actions _ _ _ _ Hz).
      split; [constructor | intros y Hy; destruct Hy].
  Qed.

  Lemma wf_zip3_comm : forall PD PK PT P : program,
      zip3 PD PK PT P -> wf_program P -> wf_program PK.
  Proof.
    intros PD PK PT P Hz (Hown & Hch & Hal & Hind).
    assert (HA : program_actions PK = phase_actions P 0%nat)
      by (unfold phase_actions; apply (zip3_comm_actions _ _ _ _ Hz)).
    split; [| split; [| split]].
    - eapply zip3_comm_ownership; eassumption.
    - (* channels *)
      intros c Hc.
      assert (Hc0 : In c (map caction_chan (phase_actions P 0%nat)))
        by (rewrite <- HA, <- program_chan_actions; exact Hc).
      assert (HcP : In c (program_chan P)).
      { rewrite program_chan_actions.
        apply (Permutation_in _
                 (Permutation_map caction_chan
                    (Permutation_sym (zip3_actions_split _ _ _ _ Hz)))).
        rewrite map_app. apply in_or_app; left.
        rewrite <- program_chan_actions. exact Hc. }
      destruct (Hch c HcP) as (Hs & Hr & Hp).
      pose proof (endpoints_two _ _ Hs Hr) as H2P.
      assert (HK2 : length (endpoints_of PK c) = 2%nat)
        by (unfold endpoints_of; rewrite HA; exact (Hal 0%nat c Hc0)).
      (* both endpoints sit in phase 0, so the tail row has none *)
      assert (HT0 : filter (fun a => Nat.eqb (caction_chan a) c)
                      (program_actions PT) = nil).
      { apply length_zero_iff_nil.
        pose proof (zip3_filter_count _ _ _ _
                      (fun a => Nat.eqb (caction_chan a) c) Hz) as Hcnt.
        unfold endpoints_of in H2P, HK2. rewrite H2P, HK2 in Hcnt. lia. }
      repeat split.
      + pose proof (zip3_filter_count _ _ _ _
                      (fun a => andb (Nat.eqb (caction_chan a) c) (is_send a)) Hz)
          as Hcnt.
        unfold endpoints_of in *. rewrite <- !filter_filter_and in Hcnt.
        rewrite HT0 in Hcnt. cbn [filter length] in Hcnt.
        rewrite Nat.add_0_r in Hcnt. rewrite <- Hcnt. exact Hs.
      + pose proof (zip3_filter_count _ _ _ _
                      (fun a => andb (Nat.eqb (caction_chan a) c)
                                     (negb (is_send a))) Hz) as Hcnt.
        unfold endpoints_of in *. rewrite <- !filter_filter_and in Hcnt.
        rewrite HT0 in Hcnt. cbn [filter length] in Hcnt.
        rewrite Nat.add_0_r in Hcnt. rewrite <- Hcnt. exact Hr.
      + rewrite (zip3_parties_comm _ _ _ _ _ Hz HT0). exact Hp.
    - (* alignment *)
      intros k c Hc. destruct k as [| k].
      + unfold phase_actions in *.
        rewrite (zip3_comm_phase0 _ _ _ _ Hz) in Hc |- *. exact (Hal 0%nat c Hc).
      + unfold phase_actions in Hc.
        rewrite (zip3_comm_later _ _ _ _ Hz) in Hc. destruct Hc.
    - (* same-phase independence *)
      intro k; destruct k as [| k].
      + rewrite (zip3_comm_phase0 _ _ _ _ Hz). exact (Hind 0%nat).
      + rewrite recv_targets_concat, output_reads_concat,
          (zip3_comm_later _ _ _ _ Hz).
        split; [constructor | intros y Hy; destruct Hy].
  Qed.

  Lemma wf_zip3_tail : forall PD PK PT P : program,
      zip3 PD PK PT P -> wf_program P -> wf_program PT.
  Proof.
    intros PD PK PT P Hz (Hown & Hch & Hal & Hind).
    assert (HA : program_actions PK = phase_actions P 0%nat)
      by (unfold phase_actions; apply (zip3_comm_actions _ _ _ _ Hz)).
    split; [| split; [| split]].
    - eapply zip3_tail_ownership; eassumption.
    - (* channels *)
      intros c Hc.
      assert (HcP : In c (program_chan P)).
      { rewrite program_chan_actions.
        apply (Permutation_in _
                 (Permutation_map caction_chan
                    (Permutation_sym (zip3_actions_split _ _ _ _ Hz)))).
        rewrite map_app. apply in_or_app; right.
        rewrite <- program_chan_actions. exact Hc. }
      destruct (Hch c HcP) as (Hs & Hr & Hp).
      pose proof (endpoints_two _ _ Hs Hr) as H2P.
      pose proof (zip3_filter_count _ _ _ _
                    (fun a => Nat.eqb (caction_chan a) c) Hz) as Hcnt0.
      (* c is not exposed in phase 0: alignment would otherwise put both
         endpoints there, leaving the tail none — but c occurs in the tail *)
      assert (HK0 : filter (fun a => Nat.eqb (caction_chan a) c)
                      (program_actions PK) = nil).
      { apply length_zero_iff_nil.
        destruct (Nat.eq_dec
                    (length (filter (fun a => Nat.eqb (caction_chan a) c)
                               (program_actions PK))) 0%nat) as [Heq | Hne];
          [exact Heq | exfalso].
        assert (Hin0 : In c (map caction_chan (phase_actions P 0%nat))).
        { rewrite <- HA. apply filter_chan_nonnil_in.
          intro Hnil; apply Hne; rewrite Hnil; reflexivity. }
        pose proof (Hal 0%nat c Hin0) as HAL. rewrite <- HA in HAL.
        unfold endpoints_of in H2P. rewrite H2P, HAL in Hcnt0.
        assert (Hz0 : filter (fun a => Nat.eqb (caction_chan a) c)
                        (program_actions PT) = nil)
          by (apply length_zero_iff_nil; lia).
        apply (filter_chan_nil_iff c (program_actions PT)) in Hz0.
        apply Hz0. rewrite <- program_chan_actions. exact Hc. }
      repeat split.
      + pose proof (zip3_filter_count _ _ _ _
                      (fun a => andb (Nat.eqb (caction_chan a) c) (is_send a)) Hz)
          as Hcnt.
        unfold endpoints_of in *. rewrite <- !filter_filter_and in Hcnt.
        rewrite HK0 in Hcnt. cbn [filter length] in Hcnt.
        rewrite Nat.add_0_l in Hcnt. rewrite <- Hcnt. exact Hs.
      + pose proof (zip3_filter_count _ _ _ _
                      (fun a => andb (Nat.eqb (caction_chan a) c)
                                     (negb (is_send a))) Hz) as Hcnt.
        unfold endpoints_of in *. rewrite <- !filter_filter_and in Hcnt.
        rewrite HK0 in Hcnt. cbn [filter length] in Hcnt.
        rewrite Nat.add_0_l in Hcnt. rewrite <- Hcnt. exact Hr.
      + rewrite (zip3_parties_tail _ _ _ _ _ Hz HK0). exact Hp.
    - (* alignment: the tail's phase k is P's phase k+1 *)
      intros k c Hc. unfold phase_actions in *.
      rewrite (zip3_tail_phase _ _ _ _ Hz) in Hc |- *. exact (Hal (S k) c Hc).
    - (* same-phase independence, same shift *)
      intro k. rewrite (zip3_tail_phase _ _ _ _ Hz). exact (Hind (S k)).
  Qed.

  (** ** Induction principle for [derivable] with the Branch-Accum family IH.
         The generated principle offers no IH for that rule's premise: the
         sub-derivations sit inside a [Forall], a nested occurrence.  Same
         principle, recursion written out, with an inner fix over the
         family. *)
  Fixpoint derivable_ind'
      (Pr : assertion dim -> program -> assertion dim -> Prop)
      (Hpd : forall Q R PD Dseq,
          wf_ownership PD ->
          locals_seq PD Dseq -> Σ ⊢ₗ {{ Q }} Dseq {{ R }} -> Pr Q PD R)
      (Hcd : forall Q PK, all_comm_done PK -> Pr Q PK Q)
      (Hcs : forall Q R PK P1 PK' c e x,
          wf_phase PK ->
          PK ∋ₖ c_send c e □ P1 ->
          P1 ∋ₖ c_recv c x □ PK' ->
          Σ ⊢ₚ {{ Q }} PK' {{ R }} -> Pr Q PK' R ->
          Pr (assertion_subst Q x e) PK R)
      (Hpc : forall Q0 Q1 Q2 Q3 PD PK PT P,
          zip3 PD PK PT P -> wf_cut PK PT P ->
          Σ ⊢ₚ {{ Q0 }} PD {{ Q1 }} -> Pr Q0 PD Q1 ->
          Σ ⊢ₚ {{ Q1 }} PK {{ Q2 }} -> Pr Q1 PK Q2 ->
          Σ ⊢ₚ {{ Q2 }} PT {{ Q3 }} -> Pr Q2 PT Q3 ->
          Pr Q0 P Q3)
      (Hba : forall phi B P A0 psi0 fam,
          Σ ⊢ₚ {{ mk_assertion phi A0 }} P {{ mk_assertion psi0 B }} ->
          Pr (mk_assertion phi A0) P (mk_assertion psi0 B) ->
          Forall (fun Api => Σ ⊢ₚ {{ mk_assertion phi (fst Api) }} P
                                 {{ mk_assertion (snd Api) B }}) fam ->
          Forall (fun Api => Pr (mk_assertion phi (fst Api)) P
                                (mk_assertion (snd Api) B)) fam ->
          ForallOrdPairs (exclusive Σ) (psi0 :: map snd fam) ->
          Pr (mk_assertion phi (qsum A0 (map fst fam))) P
             (mk_assertion (fdisj psi0 (map snd fam)) B))
      (Hcq : forall Q Q' R R' P,
          Q' ⊨[Σ] Q -> Σ ⊢ₚ {{ Q }} P {{ R }} -> Pr Q P R ->
          R ⊨[Σ] R' -> wf_assertion Σ R' -> Pr Q' P R')
      (Q : assertion dim) (P : program) (R : assertion dim)
      (d : Σ ⊢ₚ {{ Q }} P {{ R }}) {struct d} : Pr Q P R :=
    let rec := derivable_ind' Pr Hpd Hcd Hcs Hpc Hba Hcq in
    match d with
    | rule_par_disjoint _ Q R PD Dseq h0 h1 h2 => Hpd Q R PD Dseq h0 h1 h2
    | rule_comm_done _ Q PK h => Hcd Q PK h
    | rule_comm_select _ Q R PK P1 PK' c e x h0 h1 h2 d' =>
        Hcs Q R PK P1 PK' c e x h0 h1 h2 d' (rec _ _ _ d')
    | rule_par_comp _ Q0 Q1 Q2 Q3 PD PK PT P h1 h2 d1 d2 d3 =>
        Hpc Q0 Q1 Q2 Q3 PD PK PT P h1 h2
            d1 (rec _ _ _ d1) d2 (rec _ _ _ d2) d3 (rec _ _ _ d3)
    | rule_branch_accum _ phi B P A0 psi0 fam d0 df hex =>
        Hba phi B P A0 psi0 fam d0 (rec _ _ _ d0) df
            ((fix go (l : list (qpred dim * formula))
                  (h : Forall (fun Api =>
                         Σ ⊢ₚ {{ mk_assertion phi (fst Api) }} P
                             {{ mk_assertion (snd Api) B }}) l)
               {struct h}
               : Forall (fun Api =>
                   Pr (mk_assertion phi (fst Api)) P
                      (mk_assertion (snd Api) B)) l :=
                match h in Forall _ l0
                      return Forall (fun Api =>
                               Pr (mk_assertion phi (fst Api)) P
                                  (mk_assertion (snd Api) B)) l0 with
                | Forall_nil _ => Forall_nil _
                | Forall_cons x0 hx hl =>
                    Forall_cons x0 (rec _ _ _ hx) (go _ hl)
                end) fam df)
            hex
    | rule_conseq_d _ Q Q' R R' P h1 d' h2 h3 =>
        Hcq Q Q' R R' P h1 d' (rec _ _ _ d') h2 h3
    end.

  (** ** Theorem 4.1 (Soundness of the proof system).
         Assembled from the per-rule lemmas by induction on the derivation —
         the wiring below is machine-checked.  There is no [wf_program]
         premise: every rule instance already carries the side condition its
         own validity argument needs, so the theorem is about the proof
         system rather than about one class of programs. *)
  Theorem soundness :
    wf_interp Σ ->
    forall (Q R : assertion dim) (P : program),
      Σ ⊢ₚ {{ Q }} P {{ R }} ->
      Σ ⊨ {{ Q }} P {{ R }}.
  Proof.
    intros interp_ok.
    assert (main : forall (Q : assertion dim) (P : program) (R : assertion dim),
               Σ ⊢ₚ {{ Q }} P {{ R }} -> Σ ⊨ {{ Q }} P {{ R }}).
    { apply (derivable_ind' (fun Q P R => Σ ⊨ {{ Q }} P {{ R }})).
      - (* Par-Disjoint-MP *)
        intros q r pd dseq Hown Hls Hloc.
        eapply par_disjoint_sound; eassumption.
      - (* Comm-Done *)
        intros q pk Hacd. apply comm_done_sound; assumption.
      - (* Comm-Select-MP *)
        intros q r pk p1 pk' ch ex xv Hwfp Hcs1 Hcs2 Hd0 IH.
        eapply comm_select_sound; eassumption.
      - (* Par-Comp-MP *)
        intros q0 q1 q2 q3 pd pk pt p Hz Hcut Hd1 IH1 Hd2 IH2 Hd3 IH3.
        eapply par_comp_sound; eassumption.
      - (* Branch-Accum *)
        intros phi bb p a0 psi0 fam Hd0 IH0 Hdf IHf Hex.
        apply branch_accum_sound; assumption.
      - (* Conseq — wf_assertion supplied by the rule itself *)
        intros q q' r r' p He1 Hd0 IH0 He2 Hwfa.
        eapply conseq_sound; eassumption. }
    intros Q R P Hd. apply main; assumption.
  Qed.

End Soundness.

(*   

do [] g -> comm; l

**)