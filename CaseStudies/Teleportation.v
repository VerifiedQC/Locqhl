From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import Syntax Names QuantumActions Semantics Assertions WellFormed Rules.
Import ListNotations.
Open Scope proc_scope.

Definition A1 : qvar := 0%nat.
Definition A2 : qvar := 1%nat.
Definition B  : qvar := 2%nat.
Definition m1 : var  := 0%nat.
Definition m2 : var  := 2%nat.
Definition i  : var  := 1%nat.
Definition j  : var  := 3%nat.
Definition cz : chan := 0%nat.
Definition cx : chan := 1%nat.

Definition CNOT : usym := 0%nat.
Definition H    : usym := 1%nat.
Definition Z    : usym := 2%nat.
Definition X    : usym := 3%nat.
Definition Meas : msym := 0%nat.

(* corr(P, b, q) = if b = 1 then P[q] else skip *)
Definition corr (U : usym) (b : var) (q : qvar) : lblock :=
  <{ if (b_eq (e_var b) (e_val 1%nat)) then U @ [q] else skip }>.

Definition alice_pre : lblock :=
  <{ CNOT @ [A1; A2] ; H @ [A1] ; m1 <- Meas @ [A1] ; m2 <- Meas @ [A2] }>.

Definition bob_corr : lblock :=
  l_seq (corr Z i B) (corr X j B).

Definition alice : process :=
  alice_pre ⨾ [cz ‼ e_var m1; cx ‼ e_var m2] ⨾ terminated.

Definition bob : process :=
  l_skip ⨾ [cz ⁇ i; cx ⁇ j] ⨾ (bob_corr ⨾ ε ⨾ terminated).

Definition tele : program := ⟨ alice ⟩ ∥ ⟨ bob ⟩.

Definition d1 : lrow    := ⟨ alice_pre ⟩ ∥ ⟨ l_skip ⟩.

Definition k1 : krow    := ⟨ [cz ‼ e_var m1; cx ‼ e_var m2] ⟩ ∥ ⟨ [cz ⁇ i; cx ⁇ j] ⟩.

Definition t1 : program := ⟨ terminated ⟩ ∥ ⟨ bob_corr ⨾ ε ⨾ terminated ⟩.

Definition d2 : lrow    := ⟨ l_skip ⟩ ∥ ⟨ bob_corr ⟩.

Definition k2 : krow    := ⟨ ε ⟩ ∥ ⟨ ε ⟩.

Definition t2 : program := ⟨ terminated ⟩ ∥ ⟨ terminated ⟩.


Local Open Scope matrix_scope.

(* ---- Generic facts used by the Conseq steps ---------------------- *)

Lemma lowner_refl : forall n (M : Square n), M ⊑ M.
Proof.
  intros n M. unfold lowner, positive_semidefinite. intros z Hz.
  replace (M .+ (- C1) .* M) with (@Zero n n) by lma.
  rewrite Mmult_0_r, Mmult_0_l. cbn. lra.
Qed.

Lemma entails_refl : forall dim (S0 : interp dim) (Q : assertion dim), Q ⊨[S0] Q.
Proof.
  intros dim S0 Q. repeat split; auto.
  intros s M N _ H1 H2. rewrite H1 in H2. inversion H2. apply lowner_refl.
Qed.

(* Hermitian + idempotent is exactly what an orthogonal projector is, and
   such a matrix is an effect: PSD because it equals M x M dagger, and
   below I because I - M is again hermitian idempotent. *)
Lemma herm_idem_psd : forall n (M : Square n),
    M† = M -> M × M = M -> positive_semidefinite M.
Proof.
  intros n M Hh Hi.
  assert (E : M = M × M†) by (rewrite Hh, Hi; reflexivity).
  rewrite E at 1. apply positive_semidefinite_AAadjoint.
Qed.

Lemma herm_idem_effect : forall dim (M : Square (2 ^ dim)),
    WF_Matrix M -> M† = M -> M × M = M -> is_effect (dim := dim) M.
Proof.
  intros dim M HW Hh Hi. split; [apply herm_idem_psd; assumption |].
  unfold lowner. apply herm_idem_psd.
  - rewrite Mplus_adjoint, Mscale_adj, id_adjoint_eq, Hh.
    assert (Hc : Cconj (- C1) = - C1) by lca. rewrite Hc. reflexivity.
  - rewrite Mmult_plus_distr_l, !Mmult_plus_distr_r.
    Msimpl. rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Hi, Mscale_assoc. lma.
Qed.

Section Spec.

  Variable psi : Vector 2.
  (* Necessary, not cosmetic: rho_psi is an effect only for a unit vector,
     and the postcondition has to be one. *)
  Hypothesis WF_psi   : WF_Matrix psi.
  Hypothesis norm_psi : psi† × psi = I 1.
  
  Definition rho_psi : Square 2 := psi × psi†.

  Lemma WF_rho : WF_Matrix rho_psi.
  Proof. unfold rho_psi; auto with wf_db. Qed.
  #[local] Hint Resolve WF_rho : wf_db.

  Lemma rho_herm : rho_psi† = rho_psi.
  Proof. unfold rho_psi. rewrite Mmult_adjoint, adjoint_involutive. reflexivity. Qed.

  Lemma rho_idem : rho_psi × rho_psi = rho_psi.
  Proof.
    unfold rho_psi. rewrite Mmult_assoc, <- (Mmult_assoc (psi†)), norm_psi.
    rewrite Mmult_1_l; auto with wf_db.
  Qed.

  Definition base3 : Square (2 ^ 3) := I 2 ⊗ I 2 ⊗ rho_psi.
  Lemma WF_base3 : WF_Matrix base3.  Proof. unfold base3; auto with wf_db. Qed.

  Lemma is_effect_base3 : is_effect (dim := 3) base3.
  Proof.
    apply herm_idem_effect; [apply WF_base3 | | ].
    - unfold base3. restore_dims.
      rewrite !kron_adjoint, !id_adjoint_eq, rho_herm. reflexivity.
    - unfold base3. restore_dims. rewrite !kron_mixed_product.
      rewrite Mmult_1_l, rho_idem by auto with wf_db. reflexivity.
  Qed.

  Definition tele_pre : assertion 3 :=
    {| classical_part := f_bexp b_true;
       quantum_part   := q_op (fun _ => Some (rho_psi ⊗ (∣Φ+⟩ × ∣Φ+⟩†))) nil |}.
  Definition tele_post : assertion 3 :=
    {| classical_part := f_bexp b_true;
       quantum_part   := q_op (fun _ => Some (I 2 ⊗ I 2 ⊗ rho_psi)) nil |}.

  Definition tele_uu (U : usym) (qs : list qvar) : Square (2 ^ 3) :=
    match U, qs with
    | 0%nat, a :: b :: nil => pad_ctrl 3 a b σx      (* CNOT *)
    | 1%nat, a :: nil      => pad_u 3 a hadamard     (* H    *)
    | 2%nat, a :: nil      => pad_u 3 a σz           (* Z    *)
    | 3%nat, a :: nil      => pad_u 3 a σx           (* X    *)
    | _, _                 => I (2 ^ 3)
    end.

  Definition tele_mm (M : msym) (qs : list qvar) : measurement 3 :=
    match qs with
    | a :: nil => (0%nat :: 1%nat :: nil,
                   fun m => pad_u 3 a (if Nat.eqb m 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣))
    | _        => (0%nat :: nil, fun _ => I (2 ^ 3))
    end.

  Definition tele_rl (R : relsym) (args : list val) : bool :=
    match R, args with
    | 0%nat, a :: b :: nil => Nat.eqb a b            (* r_eq *)
    | 1%nat, a :: b :: nil => Nat.ltb a b            (* r_lt *)
    | 2%nat, a :: b :: nil => Nat.ltb b a            (* r_gt *)
    | _, _                 => false
    end.

  Definition Sig : interp 3 :=
    {| i_fn := fun _ _ => 0%nat;
       i_rl := tele_rl;
       i_uu := tele_uu;
       i_mm := tele_mm |}.

 
  Lemma HR    : standard_rels Sig.
  Proof. repeat split; reflexivity. Qed.
  Lemma HCNOT : i_uu Sig CNOT ([A1; A2]) = pad_ctrl 3 A1 A2 σx.
  Proof. reflexivity. Qed.
  Lemma HH    : i_uu Sig H ([A1]) = pad_u 3 A1 hadamard.
  Proof. reflexivity. Qed.
  Lemma HZ    : i_uu Sig Z ([B]) = pad_u 3 B σz.
  Proof. reflexivity. Qed.
  Lemma HX    : i_uu Sig X ([B]) = pad_u 3 B σx.
  Proof. reflexivity. Qed.

  
  Lemma tele_cut : cut tele = (d1, k1, t1).
  Proof. reflexivity. Qed.

  Lemma tele_wf_cut : wf_cut k1 t1 tele.
  Proof.
    split.
    - repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
    - intros c _ [].
  Qed.


  (* ---- Fig. 6 Step I notation ------------------------------------- *)
  Definition UA : Square (2 ^ 3) := pad_u 3 A1 hadamard × pad_ctrl 3 A1 A2 σx.
  Definition Pi (b : nat) : Square 2 :=
    if Nat.eqb b 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣.
  Definition ZX (u v : nat) : Square 2 :=
    (if Nat.eqb u 1%nat then σz else I 2) × (if Nat.eqb v 1%nat then σx else I 2).
  Definition Corr (u v : nat) : Square 2 := (ZX u v)† × rho_psi × (ZX u v).
  Definition Auv (u v : nat) : Square (2 ^ 3) :=
    UA† × (Pi u ⊗ Pi v ⊗ Corr u v) × UA.

  Definition y1 : var := 4%nat.
  Definition y2 : var := 5%nat.

  Definition qCorr (a b : var) : qpred 3 :=
    q_op (fun vs => Some (I 2 ⊗ I 2 ⊗ Corr (nth 0 vs 0%nat) (nth 1 vs 0%nat)))
         [e_var a; e_var b].

  Definition qB : qpred 3 := q_op (fun _ => Some (I 2 ⊗ I 2 ⊗ rho_psi)) nil.


  (* The transcript, shaped so that (Axiom-Meas) applies on the nose: its
     postcondition must be literally (phi /\ x = y), so after the two
     rendezvous substitutions this must read ((true /\ m1 = y1) /\ m2 = y2)
     — one nesting level per measurement. *)
  Definition chi : formula :=
    f_and (f_and (f_bexp b_true) (f_eq (e_var i) (e_var y1)))
          (f_eq (e_var j) (e_var y2)).

  (* ---- Step II: the communication phase --------------------------- *)
  Definition kz_mid : krow := ⟨ [cx ‼ e_var m2] ⟩ ∥ ⟨ [cz ⁇ i; cx ⁇ j] ⟩.
  Definition kz_res : krow := ⟨ [cx ‼ e_var m2] ⟩ ∥ ⟨ [cx ⁇ j] ⟩.
  Definition kx_mid : krow := ⟨ ε ⟩ ∥ ⟨ [cx ⁇ j] ⟩.

  Ltac wfphase :=
    split; [| split];
    [ intros c Hc; vm_compute in Hc;
      repeat (destruct Hc as [Hc | Hc]); try contradiction;
      rewrite <- Hc; vm_compute; repeat split; reflexivity
    | vm_compute; repeat constructor; cbn; intuition congruence
    | intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence ].

  Lemma wf_k1     : wf_phase k1.     Proof. wfphase. Qed.
  Lemma wf_kz_res : wf_phase kz_res. Proof. wfphase. Qed.

  Lemma tele_phase :
      Sig ⊢ₖ {{ assertion_subst (assertion_subst
                   (mk_assertion chi (qCorr i j)) j (e_var m2)) i (e_var m1) }}
            k1
            {{ mk_assertion chi (qCorr i j) }}.
  Proof.
    apply rule_comm_select with (kmid := kz_mid) (k' := kz_res)
                                (c := cz) (e := e_var m1) (x := i).
    { exact wf_k1. }
    { unfold k1, kz_mid; eauto with locc. }
    { unfold kz_mid, kz_res; eauto with locc. }
    apply rule_comm_select with (kmid := kx_mid) (k' := k2)
                                (c := cx) (e := e_var m2) (x := j).
    { exact wf_kz_res. }
    { unfold kz_res, kx_mid; eauto with locc. }
    { unfold kx_mid, k2; eauto with locc. }
    apply rule_comm_done; split; reflexivity.
  Qed.


  Lemma qCorr_subst : qpred_subst (qpred_subst (qCorr i j) j (e_var m2)) i (e_var m1)
                      = qCorr m1 m2.
  Proof. reflexivity. Qed.

  Definition PostA : assertion 3 :=
    assertion_subst (assertion_subst (mk_assertion chi (qCorr i j))
                       j (e_var m2)) i (e_var m1).

  Definition Q_m2 : assertion 3 :=
    mk_assertion (f_and (f_bexp b_true) (f_eq (e_var m1) (e_var y1)))
                 (qCorr m1 m2).

  Definition Q_m1 : assertion 3 :=
    mk_assertion (f_bexp b_true)
      (quantum_part (wp_meas Sig Meas ([A2]) y2
                       (assertion_subst Q_m2 m2 (e_var y2)))).

  Definition alice_wp : assertion 3 :=
    wp_unitary (i_uu Sig CNOT ([A1; A2]))
      (wp_unitary (i_uu Sig H ([A1]))
        (wp_meas Sig Meas ([A1]) y1 (assertion_subst Q_m1 m1 (e_var y1)))).

  Lemma alice_local : Sig ⊢ₗ {{ alice_wp }} (lseq d1) {{ PostA }}.
  Proof.
    unfold alice_wp, PostA. cbn [lseq].
    eapply rule_seq. 2:{ apply rule_skip. }
    eapply rule_seq. 2:{
      eapply rule_seq. 2:{
        eapply rule_seq. 2:{
          apply rule_meas with (Q := Q_m2) (x := m2) (M := Meas)
                               (qs := ([A2])) (y := y2);
            vm_compute; intuition congruence. }
        apply rule_meas with (Q := Q_m1) (x := m1) (M := Meas)
                             (qs := ([A1])) (y := y1);
          vm_compute; intuition congruence. }
      apply rule_unitary. }
    apply rule_unitary.
  Qed.

  Lemma tele_branch :
      Sig ⊢ₚ {{ alice_wp }} tele {{ mk_assertion chi qB }}.
  Proof.
    apply rule_par_comp with (d := d1) (k := k1) (t := t1)
                             (Q1 := assertion_subst (assertion_subst
                                      (mk_assertion chi (qCorr i j))
                                      j (e_var m2)) i (e_var m1))
                             (Q2 := mk_assertion chi (qCorr i j)).
    - exact tele_cut.
    - exact tele_wf_cut.
    - (* Step I: Par-Disjoint-MP *)
      apply rule_par_disjoint.
      + repeat constructor; repeat split;
          intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
      + exact alice_local.
    - (* Step II *)
      apply tele_phase.
    - apply rule_par_comp with (d := d2) (k := k2) (t := t2)
                               (Q1 := mk_assertion chi qB)
                               (Q2 := mk_assertion chi qB).
      + reflexivity.
      + split.
        * repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
        * intros c [].
      + apply rule_par_disjoint.
        * repeat constructor; repeat split;
            intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
        * (* Bob's conditional Pauli corrections.  Backwards through the two
             If's, the common precondition is exactly qCorr i j — a predicate
             that reads i and j, which is why it has to be store-dependent. *)
          admit.
      + apply rule_comm_done; split; reflexivity.
      + apply rule_done; split; reflexivity.
  Admitted.

  (* ---- The four branches, by Aux-Subst ---------------------------- *)
  (* y1 and y2 are auxiliary: tele never reads or writes them, so they may
     be replaced by any value.  That is what turns "m1 = y1" into
     "m1 = 0" — and only literal guards are mutually exclusive, which is
     what Branch-Accum asks of its family. *)
  Definition at_uv (Q : assertion 3) (u v : val) : assertion 3 :=
    assertion_subst (assertion_subst Q y1 (e_val u)) y2 (e_val v).

  Lemma tele_branch_at : forall u v : val,
      Sig ⊢ₚ {{ at_uv alice_wp u v }} tele
            {{ at_uv (mk_assertion chi qB) u v }}.
  Proof.
    intros u v. unfold at_uv.
    apply rule_aux_subst; [ vm_compute; intuition congruence |].
    apply rule_aux_subst; [ vm_compute; intuition congruence |].
    apply tele_branch.
  Qed.

  Definition br (u v : val) : qpred 3 * formula :=
    (quantum_part (at_uv alice_wp u v),
     classical_part (at_uv (mk_assertion chi qB) u v)).

  Definition four : list (qpred 3 * formula) :=
    [br 0%nat 0%nat; br 0%nat 1%nat; br 1%nat 0%nat; br 1%nat 1%nat].

  Ltac excl1 :=
    intros s H1 H2; cbn in H1, H2;
    rewrite !andb_true_iff in H1, H2;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end;
    congruence.

  (* Fig. 6 Step V. *)
  Lemma tele_accum :
    Sig ⊢ₚ {{ mk_assertion (f_bexp b_true) (qsum (map fst four)) }} tele
          {{ mk_assertion (fdisj (map snd four)) qB }}.
  Proof.
    apply rule_branch_accum.
    - repeat (apply Forall_cons; [ apply tele_branch_at |]). apply Forall_nil.
    - cbn [map fst snd four br].
      repeat (apply FOP_cons;
              [ repeat (apply Forall_cons; [ excl1 |]); apply Forall_nil |]).
      apply FOP_nil.
  Qed.

  Lemma tele_derivable : Sig ⊢ₚ {{ tele_pre }} tele {{ tele_post }}.
  Proof.
    eapply rule_conseq_d with
      (Q := mk_assertion (f_bexp b_true) (qsum (map fst four)))
      (R := mk_assertion (fdisj (map snd four)) qB).
    - (* rho_psi (x) EPR  <=  sum of the four branch pre-effects.  This is
         teleportation's actual mathematical content — completeness of the
         Bell basis — and the only matrix fact the derivation needs. *)
      admit.
    - exact tele_accum.
    - (* the four guards disjoined are weaker than true, and both sides have
         the same quantum part *)
      split; [| split].
      + intros s _; cbn; reflexivity.
      + intros s _ _; cbn; eexists; reflexivity.
      + intros s M N _ HM HN; cbn in HM, HN;
          inversion HM; inversion HN; subst; apply lowner_refl.
    - (* the postcondition is an effect *)
      intros s M HM; cbn in HM; inversion HM; apply is_effect_base3.
  Admitted.

  (* Paper Theorem 5.1. *)
  Theorem teleportation : Sig ⊨ {{ tele_pre }} tele {{ tele_post }}.
  Proof.
  Admitted.

End Spec.
