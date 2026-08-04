(** * Soundness — paper Theorem 4.1: every derivable triple is valid.

        Σ ⊢ₚ {{ Q }} P {{ R }}   ⟹   Σ ⊨ {{ Q }} P {{ R }}

    One lemma per rule, then the assembly.  There is no [wf_program]
    premise: every rule instance carries the side condition its own validity
    argument needs, so this is a statement about the proof system rather
    than about one class of programs.

    WIP after the row refactor: the per-rule lemmas below are stated against
    the new three-judgment system (dloc on lrow, ⊢ₖ on krow, ⊢ₚ on program)
    and left Admitted.  The assembly — the induction principle and Theorem
    4.1 — is machine-checked.
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

  (** ** 2. Done — a terminated program cannot step, so E = {(s,r)}. ** **)
  Lemma done_sound : forall (Q : assertion dim) (P : program),
      prog_terminated P ->
      Σ ⊨ {{ Q }} P {{ Q }}.
  Proof.
    intros Q P Ht s r HWFr Hherm Hpsd Hh Hd E HTerm.
    destruct HTerm as (G & Hstar & Hterm & Hcoll).
    apply terminated_star_id in Hstar; auto. subst G.
    simpl in Hcoll. subst E.
    unfold total_degree. simpl. lra.
  Qed.

  (** ** 3. The row judgments.
         [dloc] and [⊢ₖ] are about rows, which are not programs, so their
         validity is stated through the embeddings: a D-row leaf runs as
         D;ε_K;↓ and a K-row leaf as ↓;K;↓. *)
  Definition lrow_prog (d : lrow) : program :=
    row_map (fun D => phase (r_more D) nil terminated) d.

  Definition krow_prog (k : krow) : program :=
    row_map (fun K => advance r_done K terminated) k.

  (** Par-Disjoint-MP: interference freedom normalises every interleaving of
      the row to its displayed sequentialisation [lseq d]. *)
  Lemma par_disjoint_sound :
    forall (Q R : assertion dim) (d : lrow),
      lrow_disj d ->
      Σ ⊢ₗ {{ Q }} lseq d {{ R }} ->
      Σ ⊨ {{ Q }} lrow_prog d {{ R }}.
  Admitted.

  Lemma dloc_sound :
    forall (Q R : assertion dim) (d : lrow),
      dloc Σ Q d R -> Σ ⊨ {{ Q }} lrow_prog d {{ R }}.
  Proof.
    intros Q R d Hd; destruct Hd as [Q0 R0 d0 Hdisj Hloc].
    apply par_disjoint_sound; assumption.
  Qed.

  (** Comm-Select-MP: one rendezvous c!e ⋈ c?x behaves as x := e, and
      same-phase independence commutes the selected pair to the front. *)
  Lemma comm_select_sound :
    forall (Q R : assertion dim) (k kmid k' : krow)
           (c : chan) (e : expr) (x : var),
      wf_phase k ->
      k    ∋ₖ c_send c e □ kmid ->
      kmid ∋ₖ c_recv c x □ k'   ->
      Σ ⊨ {{ Q }} krow_prog k' {{ R }} ->
      Σ ⊨ {{ assertion_subst Q x e }} krow_prog k {{ R }}.
  Admitted.

  Lemma comm_done_sound : forall (Q : assertion dim) (k : krow),
      row_all (fun K => K = ε) k ->
      Σ ⊨ {{ Q }} krow_prog k {{ Q }}.
  Proof.
    (* an all-ε K-row embeds as a row of terminated processes, so this is
       exactly [done_sound] *)
    intros Q k Hk. apply done_sound.
    unfold prog_terminated, krow_prog.
    induction k as [K | k1 IH1 k2 IH2]; cbn [row_map row_all] in *.
    - rewrite Hk. reflexivity.
    - destruct Hk as [H1 H2]. split; [apply IH1; exact H1 | apply IH2; exact H2].
  Qed.

  (** The whole ⊢ₖ judgment, by induction on its derivation. *)
  Lemma comm_derivable_sound :
    wf_interp Σ ->
    forall (Q : assertion dim) (k : krow) (R : assertion dim),
      Σ ⊢ₖ {{ Q }} k {{ R }} -> Σ ⊨ {{ Q }} krow_prog k {{ R }}.
  Proof.
    intros interp_ok Q k R Hd; induction Hd.
    - apply comm_done_sound; assumption.
    - eapply comm_select_sound; eassumption.
    - eapply conseq_sound; eassumption.
  Qed.

  (** ** 4. Par-Comp-MP.  Every terminating run factors through the three
         aligned stages read off by [cut]. *)
  Lemma par_comp_sound :
    forall (Q0 Q1 Q2 Q3 : assertion dim) (P : program) (d : lrow) (k : krow)
           (t : program),
      cut P = (d, k, t) ->
      wf_cut k t P ->
      Σ ⊨ {{ Q0 }} lrow_prog d {{ Q1 }} ->
      Σ ⊨ {{ Q1 }} krow_prog k {{ Q2 }} ->
      Σ ⊨ {{ Q2 }} t {{ Q3 }} ->
      Σ ⊨ {{ Q0 }} P {{ Q3 }}.
  Admitted.

  (** ** 5. Aux-Subst — a variable the program neither reads nor writes may
         be replaced by any value throughout the triple. *)
  Lemma aux_subst_sound :
    forall (Q R : assertion dim) (P : program) (y : var) (v : val),
      ~ In y (program_cvar P) ->
      Σ ⊨ {{ Q }} P {{ R }} ->
      Σ ⊨ {{ assertion_subst Q y (e_val v) }} P
          {{ assertion_subst R y (e_val v) }}.
  Admitted.

  (** ** 6. Branch-Accum — finite additivity over the family. *)
  Lemma branch_accum_sound :
    forall (phi : formula) (B : qpred dim) (P : program)
           (fam : list (qpred dim * formula)),
      Forall (fun Api =>
                Σ ⊨ {{ mk_assertion phi (fst Api) }} P
                    {{ mk_assertion (snd Api) B }}) fam ->
      ForallOrdPairs (exclusive Σ) (map snd fam) ->
      Σ ⊨ {{ mk_assertion phi (qsum (map fst fam)) }} P
          {{ mk_assertion (fdisj (map snd fam)) B }}.
  Proof.
    intros phi B P fam Hfam Hex
           s r HWFr Hherm Hpsd Hh Hdef E HTerm.
    unfold defined_in, mk_assertion in Hdef;
      cbn [quantum_part] in Hdef; destruct Hdef as (M & HM).
    pose proof (qsum_denote_parts Σ s (map fst fam) M HM) as HAs.
    (* the sum of pre-effects splits the precondition's degree,
       the mutually exclusive guards split the postcondition's *)
    rewrite (degree_qsum Σ phi (map fst fam) s r M HM).
    rewrite (total_degree_fdisj_exclusive Σ (map snd fam) B E Hex).
    apply fold_right_Rplus_le; [lra |].
    (* the family, one member at a time; drop everything fam-dependent so
       the induction hypothesis stays a plain implication *)
    assert (Hphi : formula_holds Σ s phi = true)
      by (unfold mk_assertion in Hh; cbn [classical_part] in Hh; exact Hh).
    clear Hh Hex HM.
    revert Hfam HAs; induction fam as [| Api fam IH];
      intros Hfam HAs; cbn [map] in HAs |- *.
    - constructor.
    - constructor.
      + apply (Forall_inv Hfam s r HWFr Hherm Hpsd Hphi
                 (Forall_inv HAs) E HTerm).
      + apply IH; [apply (Forall_inv_tail Hfam) | apply (Forall_inv_tail HAs)].
  Qed.

  (** ** Induction principle for [derivable] with the Branch-Accum family IH.
         The generated principle offers no IH for that rule's premise: the
         sub-derivations sit inside a [Forall], a nested occurrence.  Same
         principle, recursion written out, with an inner fix over the
         family. *)
  Fixpoint derivable_ind'
      (Pr : assertion dim -> program -> assertion dim -> Prop)
      (Hpc : forall Q0 Q1 Q2 Q3 P d k t,
          cut P = (d, k, t) -> wf_cut k t P ->
          dloc Σ Q0 d Q1 ->
          Σ ⊢ₖ {{ Q1 }} k {{ Q2 }} ->
          Σ ⊢ₚ {{ Q2 }} t {{ Q3 }} -> Pr Q2 t Q3 ->
          Pr Q0 P Q3)
      (Hdn : forall Q P, prog_terminated P -> Pr Q P Q)
      (Hba : forall phi B P fam,
          Forall (fun Api => Σ ⊢ₚ {{ mk_assertion phi (fst Api) }} P
                                 {{ mk_assertion (snd Api) B }}) fam ->
          Forall (fun Api => Pr (mk_assertion phi (fst Api)) P
                                (mk_assertion (snd Api) B)) fam ->
          ForallOrdPairs (exclusive Σ) (map snd fam) ->
          Pr (mk_assertion phi (qsum (map fst fam))) P
             (mk_assertion (fdisj (map snd fam)) B))
      (Hax : forall Q R P y v,
          ~ In y (program_cvar P) ->
          Σ ⊢ₚ {{ Q }} P {{ R }} -> Pr Q P R ->
          Pr (assertion_subst Q y (e_val v)) P (assertion_subst R y (e_val v)))
      (Hcq : forall Q Q' R R' P,
          Q' ⊨[Σ] Q -> Σ ⊢ₚ {{ Q }} P {{ R }} -> Pr Q P R ->
          R ⊨[Σ] R' -> wf_assertion Σ R' -> Pr Q' P R')
      (Q : assertion dim) (P : program) (R : assertion dim)
      (d : Σ ⊢ₚ {{ Q }} P {{ R }}) {struct d} : Pr Q P R :=
    let rec := derivable_ind' Pr Hpc Hdn Hba Hax Hcq in
    match d with
    | rule_par_comp _ Q0 Q1 Q2 Q3 P0 d0 k0 t0 h1 h2 hd hk dt =>
        Hpc Q0 Q1 Q2 Q3 P0 d0 k0 t0 h1 h2 hd hk dt (rec _ _ _ dt)
    | rule_done _ Q0 P0 h => Hdn Q0 P0 h
    | rule_branch_accum _ phi B P0 fam df hex =>
        Hba phi B P0 fam df
            ((fix go (l : list (qpred dim * formula))
                  (h : Forall (fun Api =>
                         Σ ⊢ₚ {{ mk_assertion phi (fst Api) }} P0
                             {{ mk_assertion (snd Api) B }}) l)
               {struct h}
               : Forall (fun Api =>
                   Pr (mk_assertion phi (fst Api)) P0
                      (mk_assertion (snd Api) B)) l :=
                match h in Forall _ l0
                      return Forall (fun Api =>
                               Pr (mk_assertion phi (fst Api)) P0
                                  (mk_assertion (snd Api) B)) l0 with
                | Forall_nil _ => Forall_nil _
                | Forall_cons x0 hx hl =>
                    Forall_cons x0 (rec _ _ _ hx) (go _ hl)
                end) fam df)
            hex
    | rule_aux_subst _ Q0 R0 P0 y v h d' =>
        Hax Q0 R0 P0 y v h d' (rec _ _ _ d')
    | rule_conseq_d _ Q0 Q' R0 R' P0 h1 d' h2 h3 =>
        Hcq Q0 Q' R0 R' P0 h1 d' (rec _ _ _ d') h2 h3
    end.

  (** ** Theorem 4.1 (Soundness of the proof system). *)
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
      - (* Par-Comp-MP *)
        intros q0 q1 q2 q3 p d k t Hcut Hwf Hd Hk Ht IHt.
        eapply par_comp_sound; try eassumption.
        + exact (dloc_sound _ _ _ Hd).
        + exact (comm_derivable_sound interp_ok _ _ _ Hk).
      - (* Done *)
        intros q p Ht. apply done_sound; assumption.
      - (* Branch-Accum *)
        intros phi bb p fam Hdf IHf Hex.
        apply branch_accum_sound; assumption.
      - (* Aux-Subst *)
        intros q r p y v Hy Hd IH. apply aux_subst_sound; assumption.
      - (* Conseq *)
        intros q q' r r' p He1 Hd0 IH0 He2 Hwfa.
        eapply conseq_sound; eassumption. }
    intros Q R P Hd. apply main; assumption.
  Qed.

End Soundness.
