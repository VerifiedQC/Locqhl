(** * Completeness of Charlie's Bell measurement — the one matrix fact
      behind the entanglement-swapping case study.

    The counterpart of [BellComplete.v], and it REUSES that file wherever
    the fact is about a projector rather than about teleportation:
    [outer_le_proj] (the Cauchy-Schwarz step), [EPR_inner], and the
    single-qubit projector algebra [braket*] / [ketbra*].  What is new here
    is everything that mentions the AB pair.

    Qubit order is A(0), B(1), C_A(2), C_B(3): the AB pair is the FIRST
    tensor factor, because it is the one the postcondition speaks about.
    In that order the two pre-shared pairs EPR(A,C_A) ⊗ EPR(B,C_B) are

        Psi0 = ½ Σ_{a,b} ∣a,b⟩_{AB} ⊗ ∣a,b⟩_{C_A C_B}.

    Statement.  With
        A_{uv} := UC† (Corr u v ⊗ ∣u⟩⟨u∣ ⊗ ∣v⟩⟨v∣) UC
    the four branch pre-effects, we prove

        Psi0 Psi0†  ⊑  Σ_{u,v} A_{uv}.

    Proof shape, the same four steps as BellComplete:
      1.  S := Σ Corr u v ⊗ ∣u⟩⟨u∣ ⊗ ∣v⟩⟨v∣ is an orthogonal projector;
      2.  UC is unitary, so P := UC† S UC is an orthogonal projector;
      3.  the swapping identity: S (UC Psi0) = UC Psi0, hence P Psi0 = Psi0;
      4.  a unit vector in the range of a projector satisfies q q† ⊑ P.

    Step 3 is where the two protocols differ.  In teleportation the
    measured branch carries a Pauli-frame copy of an unknown ψ; here it
    carries one of the four Bell vectors (Z^u ⊗ X^v)∣Φ+⟩ on the REMOTE
    pair AB — entanglement between two qubits that never met. *)

From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad VecSet CauchySchwarz.
From Locqhl.CaseStudies Require BellComplete.

Local Open Scope matrix_scope.

(* The Löwner order, written exactly as in Locqhl.Core.Assertions — and as
   in BellComplete.  Same body, so the three notions are definitionally
   equal: this file states its theorem in its OWN terms and the case study
   still closes its obligation by conversion.  That is what keeps the file
   dependent on QuantumLib alone — no notion of the logic, in particular no
   [is_effect], appears anywhere below. *)
Definition lowner {n} (M N : Square n) : Prop :=
  positive_semidefinite (N .+ (- C1) .* M)%M.

Notation "M ⊑ N" := (lowner M N) (at level 70).

(* ---- The entanglement-swapping matrices ---------------------------- *)

Definition UC : Square (2 ^ 4) := pad_u 4 2 hadamard × pad_ctrl 4 2 3 σx.

Definition Pi (b : nat) : Square 2 :=
  if Nat.eqb b 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣.

(* Z[A]^u X[B]^v.  A Pauli on A and a Pauli on B, so a kron — not the
   product of two same-qubit gates teleportation has.  They therefore
   commute, and no sign is picked up anywhere below. *)
Definition ZX (u v : nat) : Square 4 :=
  (if Nat.eqb u 1%nat then σz else I 2) ⊗ (if Nat.eqb v 1%nat then σx else I 2).

Definition EPR : Square 4 := ∣Φ+⟩ × ∣Φ+⟩†.

Definition Corr (u v : nat) : Square 4 := (ZX u v)† × EPR × (ZX u v).

Definition Psi0 : Vector (2 ^ 4) :=
  / 2 .* (∣0,0⟩ ⊗ ∣0,0⟩ .+ ∣0,1⟩ ⊗ ∣0,1⟩
          .+ ∣1,0⟩ ⊗ ∣1,0⟩ .+ ∣1,1⟩ ⊗ ∣1,1⟩).

(* ---- Well-formedness ------------------------------------------------ *)

Lemma WF_ZX : forall u v, WF_Matrix (ZX u v).
Proof.
  intros u v; unfold ZX;
    destruct (Nat.eqb u 1%nat); destruct (Nat.eqb v 1%nat); auto with wf_db.
Qed.
#[export] Hint Resolve WF_ZX : wf_db.

Lemma WF_EPR : WF_Matrix EPR.
Proof. unfold EPR; auto with wf_db. Qed.
#[export] Hint Resolve WF_EPR : wf_db.

Lemma WF_Corr : forall u v, WF_Matrix (Corr u v).
Proof. intros u v; unfold Corr; auto with wf_db. Qed.
#[export] Hint Resolve WF_Corr : wf_db.

Lemma WF_Pi : forall b, WF_Matrix (Pi b).
Proof. intros b; unfold Pi; destruct (Nat.eqb b 0%nat); auto with wf_db. Qed.
#[export] Hint Resolve WF_Pi : wf_db.

Lemma WF_Psi0 : WF_Matrix Psi0.
Proof. unfold Psi0; restore_dims; auto 10 with wf_db. Qed.
#[export] Hint Resolve WF_Psi0 : wf_db.

(* ---- The EPR projector on AB ---------------------------------------- *)

(* ∣Φ+⟩ is a unit vector — proved once, in BellComplete. *)
Lemma EPR_herm : EPR† = EPR.
Proof. unfold EPR. rewrite Mmult_adjoint, adjoint_involutive. reflexivity. Qed.

Lemma EPR_idem : EPR × EPR = EPR.
Proof.
  unfold EPR. rewrite Mmult_assoc, <- (Mmult_assoc (∣Φ+⟩†)), BellComplete.EPR_inner.
  rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma EPR_fix : EPR × ∣Φ+⟩ = ∣Φ+⟩.
Proof.
  unfold EPR. rewrite Mmult_assoc, BellComplete.EPR_inner, Mmult_1_r;
    auto with wf_db.
Qed.

Lemma ZX_unitary : forall u v, ZX u v × (ZX u v)† = I 4.
Proof.
  intros u v; unfold ZX;
    destruct (Nat.eqb u 1%nat); destruct (Nat.eqb v 1%nat); lma'.
Qed.

Lemma Corr_herm : forall u v, (Corr u v)† = Corr u v.
Proof.
  intros u v; unfold Corr.
  rewrite !Mmult_adjoint, adjoint_involutive, EPR_herm, Mmult_assoc.
  reflexivity.
Qed.

Lemma Corr_idem : forall u v, Corr u v × Corr u v = Corr u v.
Proof.
  intros u v; unfold Corr.
  rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (ZX u v)), ZX_unitary.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc EPR), EPR_idem.
  reflexivity.
Qed.

(* ---- The block projector S ------------------------------------------ *)

(* The (C_A, C_B) factors are kept merged: every use below feeds S a vector
   whose second factor is the two-qubit basis vector ∣u,v⟩ that Charlie's
   measurement leaves behind. *)
Definition blk (u v : nat) : Square (2 ^ 4) := Corr u v ⊗ (Pi u ⊗ Pi v).

Definition Sblk : Square (2 ^ 4) :=
  blk 0 0 .+ blk 0 1 .+ blk 1 0 .+ blk 1 1.

Lemma WF_blk : forall u v, WF_Matrix (blk u v).
Proof. intros u v; unfold blk; restore_dims; auto with wf_db. Qed.
#[export] Hint Resolve WF_blk : wf_db.

Lemma WF_Sblk : WF_Matrix Sblk.
Proof. unfold Sblk; auto with wf_db. Qed.
#[export] Hint Resolve WF_Sblk : wf_db.

(* The single-qubit projector algebra is BellComplete's. *)
Lemma Pi_herm : forall b, (Pi b)† = Pi b.
Proof.
  intros b; unfold Pi; destruct (Nat.eqb b 0%nat);
    [apply BellComplete.braket0_herm | apply BellComplete.braket1_herm].
Qed.

Lemma Pi_same : forall b, Pi b × Pi b = Pi b.
Proof.
  intros b; unfold Pi; destruct (Nat.eqb b 0%nat);
    [apply BellComplete.braket00 | apply BellComplete.braket11].
Qed.

Lemma Pi_01 : Pi 0 × Pi 1 = Zero.
Proof. unfold Pi; cbn; apply BellComplete.braket01. Qed.

Lemma Pi_10 : Pi 1 × Pi 0 = Zero.
Proof. unfold Pi; cbn; apply BellComplete.braket10. Qed.

Lemma blk_mult : forall u v u' v',
    blk u v × blk u' v'
    = (Corr u v × Corr u' v') ⊗ ((Pi u × Pi u') ⊗ (Pi v × Pi v')).
Proof.
  intros. unfold blk. restore_dims. rewrite !kron_mixed_product. reflexivity.
Qed.

Lemma Sblk_herm : Sblk† = Sblk.
Proof.
  unfold Sblk, blk.
  rewrite !Mplus_adjoint. restore_dims.
  rewrite !kron_adjoint, !Corr_herm, !Pi_herm.
  reflexivity.
Qed.

Lemma Sblk_idem : Sblk × Sblk = Sblk.
Proof.
  unfold Sblk.
  rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r, !blk_mult.
  cbn [Nat.eqb].
  rewrite !Pi_same, !Pi_01, !Pi_10, !Corr_idem.
  restore_dims.
  rewrite ?kron_0_l, ?kron_0_r.
  restore_dims.
  rewrite ?kron_0_l, ?kron_0_r.
  rewrite ?Mplus_0_l, ?Mplus_0_r.
  unfold blk. reflexivity.
Qed.

(* ---- UC is unitary, and is the identity on the AB block ------------- *)

Lemma UC_unitary : WF_Unitary UC.
Proof.
  apply Mmult_unitary.
  - apply pad_u_unitary; [lia | apply H_unitary].
  - apply pad_ctrl_unitary; [lia | lia | lia | apply σx_unitary].
Qed.

Lemma WF_UC : WF_Matrix UC.
Proof. destruct UC_unitary; assumption. Qed.
#[export] Hint Resolve WF_UC : wf_db.

(* Charlie's two gates touch only C_A and C_B, so UC is I on AB.  This is
   the whole reason the four branch vectors below still live on AB. *)
Definition Mcb : Square 4 := (hadamard ⊗ I 2) × cnot.

(* The two-qubit block [pad_ctrl] builds when the control and the target
   are adjacent. *)
Lemma ctrl_blob : ∣1⟩⟨1∣ ⊗ I 1 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 1 ⊗ I 2 = cnot.
Proof. lma'. Qed.

Lemma UC_kron : UC = I 4 ⊗ Mcb.
Proof.
  unfold UC, Mcb, pad_u, pad_ctrl, pad; cbn.
  restore_dims. rewrite ctrl_blob, kron_1_r.
  rewrite (kron_assoc (I 4) hadamard (I 2)) by auto with wf_db.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite Mmult_1_l by auto with wf_db.
  reflexivity.
Qed.

(* ---- The swapping identity ------------------------------------------ *)

(* The Bell vector branch (u,v) leaves on AB. *)
Definition bvec (u v : nat) : Vector 4 := (ZX u v)† × ∣Φ+⟩.

Definition W : Vector (2 ^ 4) :=
  / 2 .* (bvec 0 0 ⊗ ∣0,0⟩ .+ bvec 0 1 ⊗ ∣0,1⟩
          .+ bvec 1 0 ⊗ ∣1,0⟩ .+ bvec 1 1 ⊗ ∣1,1⟩).

Lemma WF_bvec : forall u v, WF_Matrix (bvec u v).
Proof. intros u v; unfold bvec; auto with wf_db. Qed.
#[export] Hint Resolve WF_bvec : wf_db.

Lemma WF_W : WF_Matrix W.
Proof. unfold W; restore_dims; auto 10 with wf_db. Qed.
#[export] Hint Resolve WF_W : wf_db.

(* What Charlie's two gates do to each basis vector of (C_A, C_B). *)
Lemma Mcb00 : Mcb × ∣0,0⟩ = / √ 2 .* (∣0,0⟩ .+ ∣1,0⟩).
Proof. unfold Mcb. lma'. Qed.
Lemma Mcb01 : Mcb × ∣0,1⟩ = / √ 2 .* (∣0,1⟩ .+ ∣1,1⟩).
Proof. unfold Mcb. lma'. Qed.
Lemma Mcb10 : Mcb × ∣1,0⟩ = / √ 2 .* (∣0,1⟩ .+ (- C1) .* ∣1,1⟩).
Proof. unfold Mcb. lma'. Qed.
Lemma Mcb11 : Mcb × ∣1,1⟩ = / √ 2 .* (∣0,0⟩ .+ (- C1) .* ∣1,0⟩).
Proof. unfold Mcb. lma'. Qed.

(* The four Bell vectors, explicitly. *)
Lemma b00 : bvec 0 0 = ∣Φ+⟩.
Proof. unfold bvec, ZX; cbn [Nat.eqb]; lma'. Qed.
Lemma b01 : bvec 0 1 = / √ 2 .* (∣0,1⟩ .+ ∣1,0⟩).
Proof. unfold bvec, ZX; cbn [Nat.eqb]; lma'. Qed.
Lemma b10 : bvec 1 0 = / √ 2 .* (∣0,0⟩ .+ (- C1) .* ∣1,1⟩).
Proof. unfold bvec, ZX; cbn [Nat.eqb]; lma'. Qed.
Lemma b11 : bvec 1 1 = / √ 2 .* (∣0,1⟩ .+ (- C1) .* ∣1,0⟩).
Proof. unfold bvec, ZX; cbn [Nat.eqb]; lma'. Qed.

(* THE step: the same superposition, read by (C_A,C_B) outcome instead of
   by AB basis vector.  Each of Charlie's four outcomes leaves a DIFFERENT
   Bell vector on A and B — which is the protocol. *)
Lemma regroup :
  ∣0,0⟩ ⊗ (Mcb × ∣0,0⟩) .+ ∣0,1⟩ ⊗ (Mcb × ∣0,1⟩)
  .+ ∣1,0⟩ ⊗ (Mcb × ∣1,0⟩) .+ ∣1,1⟩ ⊗ (Mcb × ∣1,1⟩)
  = bvec 0 0 ⊗ ∣0,0⟩ .+ bvec 0 1 ⊗ ∣0,1⟩
    .+ bvec 1 0 ⊗ ∣1,0⟩ .+ bvec 1 1 ⊗ ∣1,1⟩.
Proof.
  rewrite Mcb00, Mcb01, Mcb10, Mcb11, b00, b01, b10, b11.
  unfold EPRpair.
  apply mat_equiv_eq; [ restore_dims; auto 10 with wf_db .. | ].
  by_cell; lca.
Qed.

Lemma UC_Psi0 : UC × Psi0 = W.
Proof.
  rewrite UC_kron.
  unfold Psi0, W.
  rewrite Mscale_mult_dist_r. f_equal.
  rewrite !Mmult_plus_distr_l.
  restore_dims.
  rewrite !kron_mixed_product.
  rewrite !Mmult_1_l by auto with wf_db.
  exact regroup.
Qed.

(* ---- S fixes the post-measurement state ------------------------------ *)

Lemma blk_apply : forall u v (x : Vector 4) (y z : Vector 2),
    blk u v × (x ⊗ (y ⊗ z))
    = (Corr u v × x) ⊗ ((Pi u × y) ⊗ (Pi v × z)).
Proof.
  intros. unfold blk. restore_dims. rewrite !kron_mixed_product. reflexivity.
Qed.

Lemma corr_fix : forall u v, Corr u v × bvec u v = bvec u v.
Proof.
  intros u v. unfold Corr, bvec.
  rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (ZX u v)), ZX_unitary.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite EPR_fix.
  reflexivity.
Qed.

Lemma Sblk_W : Sblk × W = W.
Proof.
  unfold Sblk, W.
  rewrite Mscale_mult_dist_r. f_equal.
  rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r.
  rewrite !blk_apply.
  unfold Pi; cbn [Nat.eqb].
  rewrite !BellComplete.ketbra00, !BellComplete.ketbra01,
          !BellComplete.ketbra10, !BellComplete.ketbra11.
  restore_dims.
  rewrite ?kron_0_l, ?kron_0_r.
  restore_dims.
  rewrite ?kron_0_l, ?kron_0_r.
  rewrite ?Mplus_0_l, ?Mplus_0_r.
  rewrite !corr_fix.
  reflexivity.
Qed.

Lemma Psi0_norm : ⟨ Psi0 , Psi0 ⟩ = C1.
Proof.
  unfold inner_product, Psi0.
  unfold Mmult, adjoint, kron, scale, Mplus, big_sum, ket, qubit0, qubit1;
    cbn; lca.
Qed.

Lemma UC_flip : UC × UC† = I (2 ^ 4).
Proof.
  destruct UC_unitary as [WFU HU].
  apply Minv_flip; auto with wf_db.
Qed.

(* ---- Assembly -------------------------------------------------------- *)

Theorem swap_completeness :
  Psi0 × Psi0†
  ⊑ UC† × (Corr 0 0 ⊗ Pi 0 ⊗ Pi 0) × UC
    .+ (UC† × (Corr 0 1 ⊗ Pi 0 ⊗ Pi 1) × UC
    .+ (UC† × (Corr 1 0 ⊗ Pi 1 ⊗ Pi 0) × UC
    .+ UC† × (Corr 1 1 ⊗ Pi 1 ⊗ Pi 1) × UC)).
Proof.
  destruct UC_unitary as [WFU HU].
  (* the four displayed blocks are the [blk]s, re-associated *)
  replace (UC† × (Corr 0 0 ⊗ Pi 0 ⊗ Pi 0) × UC
           .+ (UC† × (Corr 0 1 ⊗ Pi 0 ⊗ Pi 1) × UC
           .+ (UC† × (Corr 1 0 ⊗ Pi 1 ⊗ Pi 0) × UC
           .+ UC† × (Corr 1 1 ⊗ Pi 1 ⊗ Pi 1) × UC)))
    with (UC† × Sblk × UC).
  2:{ unfold Sblk, blk.
      rewrite <- !(kron_assoc (Corr _ _) (Pi _) (Pi _)) by auto with wf_db.
      restore_dims.
      rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r.
      rewrite !Mplus_assoc. reflexivity. }
  apply BellComplete.outer_le_proj; auto with wf_db.
  - (* hermitian *)
    rewrite !Mmult_adjoint, adjoint_involutive, Sblk_herm.
    rewrite !Mmult_assoc. reflexivity.
  - (* idempotent *)
    rewrite !Mmult_assoc.
    rewrite <- (Mmult_assoc UC), UC_flip.
    rewrite Mmult_1_l by auto with wf_db.
    rewrite <- (Mmult_assoc Sblk), Sblk_idem.
    reflexivity.
  - (* Psi0 is in the range *)
    rewrite !Mmult_assoc.
    rewrite UC_Psi0, Sblk_W, <- UC_Psi0.
    rewrite <- Mmult_assoc, HU.
    apply Mmult_1_l; auto with wf_db.
  - exact Psi0_norm.
Qed.

(** ** The matrix side of the case study's Conseq steps ****************

    Still pure QuantumLib: the case study's own effect checks are two
    applications of "hermitian and idempotent", and this is where that
    arithmetic is done — [is_effect] itself is a notion of the logic and
    stays in the case study.                                            *)

(* ---- Hermitian idempotents ------------------------------------------ *)

Lemma lowner_refl : forall n (M : Square n), M ⊑ M.
Proof.
  intros n M. unfold lowner, positive_semidefinite. intros z Hz.
  replace (M .+ (- C1) .* M) with (@Zero n n) by lma.
  rewrite Mmult_0_r, Mmult_0_l. cbn. lra.
Qed.

Lemma herm_idem_psd : forall n (M : Square n),
    M† = M -> M × M = M -> positive_semidefinite M.
Proof.
  intros n M Hh Hi.
  assert (E : M = M × M†) by (rewrite Hh, Hi; reflexivity).
  rewrite E at 1. apply positive_semidefinite_AAadjoint.
Qed.

(* I - M is again a hermitian idempotent — the half of "M is an effect"
   that is not immediate. *)
Lemma compl_herm : forall n (M : Square n),
    M† = M -> (I n .+ (- C1) .* M)† = I n .+ (- C1) .* M.
Proof.
  intros n M Hh.
  rewrite Mplus_adjoint, Mscale_adj, id_adjoint_eq, Hh.
  assert (Hc : Cconj (- C1) = - C1) by lca. rewrite Hc. reflexivity.
Qed.

Lemma compl_idem : forall n (M : Square n),
    WF_Matrix M -> M × M = M ->
    (I n .+ (- C1) .* M) × (I n .+ (- C1) .* M) = I n .+ (- C1) .* M.
Proof.
  intros n M HW Hi.
  rewrite Mmult_plus_distr_l, !Mmult_plus_distr_r.
  Msimpl. rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Hi, Mscale_assoc. lma.
Qed.

(* ---- The padded AB operator every assertion here denotes ------------- *)

Lemma WF_ab : forall C : Square 4, WF_Matrix C -> WF_Matrix (C ⊗ I 2 ⊗ I 2).
Proof. intros C WC. restore_dims; auto with wf_db. Qed.

Lemma ab_herm : forall C : Square 4,
    WF_Matrix C -> C† = C -> (C ⊗ I 2 ⊗ I 2)† = C ⊗ I 2 ⊗ I 2.
Proof.
  intros C WC Hh. restore_dims.
  rewrite !kron_adjoint, !id_adjoint_eq, Hh. reflexivity.
Qed.

Lemma ab_idem : forall C : Square 4,
    WF_Matrix C -> C × C = C ->
    (C ⊗ I 2 ⊗ I 2) × (C ⊗ I 2 ⊗ I 2) = C ⊗ I 2 ⊗ I 2.
Proof.
  intros C WC Hi. restore_dims. rewrite !kron_mixed_product.
  rewrite Mmult_1_l, Hi by auto with wf_db. reflexivity.
Qed.

(* ---- Conjugation ---------------------------------------------------- *)

(* Merge a two-layer conjugation into one. *)
Lemma conj_merge : forall n (A B M : Square n),
    A† × (B† × M × B) × A = (B × A)† × M × (B × A).
Proof.
  intros n A B M. rewrite Mmult_adjoint. rewrite !Mmult_assoc. reflexivity.
Qed.

Lemma conj_ab : forall (K C : Square 4),
    WF_Matrix K -> WF_Matrix C ->
    (K ⊗ I 2 ⊗ I 2)† × (C ⊗ I 2 ⊗ I 2) × (K ⊗ I 2 ⊗ I 2)
    = (K† × C × K) ⊗ I 2 ⊗ I 2.
Proof.
  intros K C WK WC. restore_dims.
  rewrite !kron_adjoint, !id_adjoint_eq. restore_dims.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

(* Conjugation by a gate on A, resp. on B, in the raw shape [cbn] produces
   for [pad_u 4 0 _] and [pad_u 4 1 _]: both act inside the AB factor. *)
Lemma padA_conj : forall (M : Square 2) (C : Square 4),
    WF_Matrix M -> WF_Matrix C ->
    adjoint (I 1 ⊗ M ⊗ I 8) × (C ⊗ I 2 ⊗ I 2) × (I 1 ⊗ M ⊗ I 8)
    = ((M ⊗ I 2)† × C × (M ⊗ I 2)) ⊗ I 2 ⊗ I 2.
Proof.
  intros M C WM WC.
  assert (E : I 1 ⊗ M ⊗ I 8 = (M ⊗ I 2) ⊗ I 2 ⊗ I 2).
  { rewrite kron_1_l by auto with wf_db.
    replace (I 8) with (I 2 ⊗ I 2 ⊗ I 2) by (rewrite !id_kron; reflexivity).
    restore_dims. rewrite <- !kron_assoc by auto with wf_db. reflexivity. }
  rewrite E. apply conj_ab; auto with wf_db.
Qed.

Lemma padB_conj : forall (M : Square 2) (C : Square 4),
    WF_Matrix M -> WF_Matrix C ->
    adjoint (I 2 ⊗ M ⊗ I 4) × (C ⊗ I 2 ⊗ I 2) × (I 2 ⊗ M ⊗ I 4)
    = ((I 2 ⊗ M)† × C × (I 2 ⊗ M)) ⊗ I 2 ⊗ I 2.
Proof.
  intros M C WM WC.
  assert (E : I 2 ⊗ M ⊗ I 4 = (I 2 ⊗ M) ⊗ I 2 ⊗ I 2).
  { rewrite (kron_assoc (I 2 ⊗ M) (I 2) (I 2)) by auto with wf_db.
    rewrite id_kron. reflexivity. }
  rewrite E. apply conj_ab; auto with wf_db.
Qed.

(* ---- How the two corrections move the AB frame ---------------------- *)

(* Z[A] and X[B] commute, so the frame factors: ZX(1,v) = ZX(0,v) · Z[A].
   Teleportation has no such lemma: there both Paulis land on the same
   qubit, they anticommute, and a sign has to be chased. *)
Lemma zx_Z : forall v, ZX 1 v = ZX 0 v × (σz ⊗ I 2).
Proof.
  intros v. unfold ZX. cbn [Nat.eqb]. destruct (Nat.eqb v 1%nat); lma'.
Qed.

Lemma corr_Z : forall u v, Nat.eqb u 1%nat = true ->
    Corr u v = (σz ⊗ I 2)† × Corr 0 v × (σz ⊗ I 2).
Proof.
  intros u v Hu. apply Nat.eqb_eq in Hu; subst u.
  unfold Corr. rewrite zx_Z, conj_merge. reflexivity.
Qed.

Lemma corr_noZ : forall u v, Nat.eqb u 1%nat = false -> Corr u v = Corr 0 v.
Proof.
  intros u v Hu. unfold Corr, ZX. rewrite Hu. cbn [Nat.eqb]. reflexivity.
Qed.

Lemma corr_X : forall v, Nat.eqb v 1%nat = true ->
    Corr 0 v = (I 2 ⊗ σx)† × EPR × (I 2 ⊗ σx).
Proof.
  intros v Hv. unfold Corr, ZX. rewrite Hv. cbn [Nat.eqb]. reflexivity.
Qed.

Lemma corr_noX : forall v, Nat.eqb v 1%nat = false -> Corr 0 v = EPR.
Proof.
  intros v Hv. unfold Corr, ZX. rewrite Hv. cbn [Nat.eqb].
  rewrite id_kron. cbn.
  rewrite id_adjoint_eq, Mmult_1_l, Mmult_1_r by auto with wf_db.
  reflexivity.
Qed.

(* ---- The branch pre-effect, in the shape [cbn] produces -------------- *)

(* Charlie's CNOT and H, then his two measurement projectors, conjugated
   onto the AB frame: the projectors collapse onto Charlie's two factors
   and the two unitary layers merge into UC.  This is what turns a branch
   precondition into one of [swap_completeness]'s summands. *)
Lemma chain_eq : forall (P Q : Square 2) (C : Square 4),
    WF_Matrix P -> WF_Matrix Q -> WF_Matrix C ->
    P† = P -> P × P = P -> Q† = Q -> Q × Q = Q ->
    adjoint (I 4 ⊗ (∣1⟩⟨1∣ ⊗ I 1 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 1 ⊗ I 2) ⊗ I 1)
    × (adjoint (I 4 ⊗ hadamard ⊗ I 2)
       × (adjoint (I 4 ⊗ P ⊗ I 2)
          × (adjoint (I 8 ⊗ Q ⊗ I 1) × (C ⊗ I 2 ⊗ I 2) × (I 8 ⊗ Q ⊗ I 1))
          × (I 4 ⊗ P ⊗ I 2))
       × (I 4 ⊗ hadamard ⊗ I 2))
    × (I 4 ⊗ (∣1⟩⟨1∣ ⊗ I 1 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 1 ⊗ I 2) ⊗ I 1)
    = UC† × (C ⊗ P ⊗ Q) × UC.
Proof.
  intros P Q C WFP WFQ WFC HPh HPi HQh HQi.
  assert (EQ : I 8 ⊗ Q ⊗ I 1 = I 4 ⊗ I 2 ⊗ Q).
  { rewrite kron_1_r.
    replace (I 8) with (I 4 ⊗ I 2) by (rewrite id_kron; reflexivity).
    reflexivity. }
  assert (Hmid :
    adjoint (I 4 ⊗ P ⊗ I 2)
    × (adjoint (I 8 ⊗ Q ⊗ I 1) × (C ⊗ I 2 ⊗ I 2) × (I 8 ⊗ Q ⊗ I 1))
    × (I 4 ⊗ P ⊗ I 2) = C ⊗ P ⊗ Q).
  { rewrite EQ. restore_dims.
    rewrite !kron_adjoint, !id_adjoint_eq, HPh, HQh.
    restore_dims.
    rewrite !kron_mixed_product.
    Msimpl.
    rewrite HQi, HPi.
    reflexivity. }
  rewrite Hmid.
  unfold UC, pad_u, pad_ctrl, pad; cbn.
  rewrite Mmult_adjoint.
  rewrite !Mmult_assoc.
  reflexivity.
Qed.
