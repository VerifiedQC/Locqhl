(** * SharedKernel — linear-algebra / projector facts shared across case studies

    Pure-move refactor (proof-review delta, 2026-08-17): declarations that were
    byte-for-byte duplicated between [SwapComplete.v] and [NonlocalCNOTComplete.v]
    (the Löwner order and its notation, the [Pi]/[EPR] projectors and their
    Hermitian/idempotent/WF facts, and the generic effect lemma [herm_idem_psd]
    and its complement).  No new abstraction; statements and proofs are verbatim.
    Depends only on QuantumLib plus the braket lemmas already proved in
    [BellComplete.v]. *)

From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad VecSet CauchySchwarz.
From Locqhl.CaseStudies Require BellComplete.

(* The Löwner order, written exactly as in Locqhl.Core.Assertions — and as
   in BellComplete.  Same body, so the three notions are definitionally
   equal: this file states its theorem in its OWN terms and the case study
   still closes its obligation by conversion.  That is what keeps the file
   dependent on QuantumLib alone — no notion of the logic, in particular no
   [is_effect], appears anywhere below. *)
Definition lowner {n} (M N : Square n) : Prop :=
  positive_semidefinite (N .+ (- C1) .* M)%M.

Notation "M ⊑ N" := (lowner M N) (at level 70).

Definition Pi (b : nat) : Square 2 :=
  if Nat.eqb b 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣.

Definition EPR : Square 4 := ∣Φ+⟩ × ∣Φ+⟩†.

Lemma WF_EPR : WF_Matrix EPR.
Proof. unfold EPR; auto with wf_db. Qed.

Lemma WF_Pi : forall b, WF_Matrix (Pi b).
Proof. intros b; unfold Pi; destruct (Nat.eqb b 0%nat); auto with wf_db. Qed.

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
