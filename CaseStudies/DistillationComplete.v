(** * Distillation — the matrix side.

    Depends on QuantumLib alone, as [BellComplete] and [SwapComplete] do:
    nothing here may mention the logic.  The definitions are repeated
    verbatim from [Distillation.v], so the obligations stated there close
    by conversion.

    What lives here is the one thing the derivation cannot do for itself:
    the round-[j] operators act on four qubits at offset [4j] inside a
    [4(n+1)]-qubit register, and every fact about them is a statement about
    [pad] at a SYMBOLIC offset.  The block-level algebra underneath is
    easy and is proved; the lifting is not, and is left open. **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From QuantumLib Require Import Matrix Quantum Pad.
Import ListNotations.

Local Open Scope matrix_scope.

(** ** Registers, repeated from Distillation.v *********************** *)

Definition Ak (i : nat) : nat := 4 * i.
Definition Bk (i : nat) : nat := 4 * i + 1.
Definition At (i : nat) : nat := 4 * i + 2.
Definition Bt (i : nat) : nat := 4 * i + 3.

(** ** The block algebra — one round's four qubits ******************** *)

Definition Pi (b : nat) : Square 2 :=
  if Nat.eqb b 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣.

Definition Ev : Square 4 := ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣.
Definition Od : Square 4 := ∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣ .+ ∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣.

(** Summing a one-qubit measurement over its outcomes is the identity —
    the fact the per-outcome [Meas] rule makes you recover by hand. *)
Lemma Pi_sum : Pi 0%nat .+ Pi 1%nat = I 2.
Proof. unfold Pi; cbn [Nat.eqb]; lma'. Qed.

(** Over a PAIR of measured qubits, the four outcomes likewise sum to the
    identity — this is the whole content of "an idle round changes
    nothing", before any lifting. *)
Lemma Pi_pair_sum :
  (Pi 0%nat ⊗ Pi 0%nat .+ Pi 0%nat ⊗ Pi 1%nat)
  .+ (Pi 1%nat ⊗ Pi 0%nat .+ Pi 1%nat ⊗ Pi 1%nat) = I 4.
Proof.
  rewrite <- !kron_plus_distr_l.
  rewrite Pi_sum, <- kron_plus_distr_r, Pi_sum, id_kron.
  reflexivity.
Qed.

(** Split by the parity of the two outcomes instead: the two that agree
    make [Ev], the two that differ make [Od].  This is what the accepting
    and rejecting rounds need in place of [Pi_pair_sum]. *)
Lemma Pi_pair_eq : Pi 0%nat ⊗ Pi 0%nat .+ Pi 1%nat ⊗ Pi 1%nat = Ev.
Proof. unfold Pi, Ev; cbn [Nat.eqb]; reflexivity. Qed.

Lemma Pi_pair_neq : Pi 0%nat ⊗ Pi 1%nat .+ Pi 1%nat ⊗ Pi 0%nat = Od.
Proof. unfold Pi, Od; cbn [Nat.eqb]; reflexivity. Qed.

(** ** The predicates, repeated from Distillation.v ****************** *)

Definition Pass   : Square 16 := Ev ⊗ Ev .+ Od ⊗ Od.
Definition Rej    : Square 16 := Ev ⊗ Od .+ Od ⊗ Ev.
Definition EqSub  : Square 16 := I 4 ⊗ Ev.
Definition NeqSub : Square 16 := I 4 ⊗ Od.

Definition pre_q (k n : nat) : Square (2 ^ (4 * S n)) :=
  kron_n k Rej ⊗ Pass ⊗ kron_n (n - k) (I 16).
Definition post_q (k n : nat) : Square (2 ^ (4 * S n)) :=
  kron_n k NeqSub ⊗ EqSub ⊗ kron_n (n - k) (I 16).

(** The loop invariant: [j] rounds measured and rejected, rounds [j..k-1]
    still to reject, round [k] still to pass. *)
Definition inv_q (j k n : nat) : Square (2 ^ (4 * S n)) :=
  kron_n j NeqSub ⊗ kron_n (k - j) Rej ⊗ Pass ⊗ kron_n (n - k) (I 16).

(** ** The lifting — OPEN ********************************************

    Round [j] occupies qubits [4j .. 4j+3] of a [4(n+1)]-qubit register.
    Its gates and measurements reach those qubits through [pad_ctrl] and
    [pad_u] at the SYMBOLIC offset [4j], and that is the whole difficulty:
    the block algebra underneath is [Pi_pair_sum] / [Pi_pair_eq] /
    [Pi_pair_neq] above, all three of them two lines.

    These three are the matrix content of the case study, the counterpart
    of [NonlocalCNOTComplete.rcnot_completeness].  None is proved. *)

Definition cA (n j : nat) : Square (2 ^ (4 * S n)) :=
  pad_ctrl (4 * S n) (Ak j) (At j) σx.
Definition cB (n j : nat) : Square (2 ^ (4 * S n)) :=
  pad_ctrl (4 * S n) (Bk j) (Bt j) σx.
Definition mA (n j v : nat) : Square (2 ^ (4 * S n)) :=
  pad_u (4 * S n) (At j) (Pi v).
Definition mB (n j v : nat) : Square (2 ^ (4 * S n)) :=
  pad_u (4 * S n) (Bt j) (Pi v).

(** One round's backward transformer at outcome pair (va, vb): the weakest
    precondition of [CNOT_A ; Meas_A ; CNOT_B ; Meas_B], read outside-in. *)
Definition round_wp (n j va vb : nat) (X : Square (2 ^ (4 * S n)))
  : Square (2 ^ (4 * S n)) :=
  (cA n j) † × ((mA n j va) † ×
    ((cB n j) † × ((mB n j vb) † × X × (mB n j vb)) × (cB n j))
    × (mA n j va)) × (cA n j).

Definition round_sum (n j : nat) (X : Square (2 ^ (4 * S n)))
  : Square (2 ^ (4 * S n)) :=
  (round_wp n j 0 0 X .+ round_wp n j 0 1 X)
  .+ (round_wp n j 1 0 X .+ round_wp n j 1 1 X).

(** OPEN 1 — an idle round, [j > k].  The postcondition leaves round [j]
    free, the four outcome operators sum to the identity there
    ([Pi_pair_sum]), and the two CNOTs then cancel. *)
Lemma round_sum_idle : forall n k j,
    (k < j)%nat -> (j <= n)%nat ->
    round_sum n j (post_q k n) = post_q k n.
Admitted.

(** OPEN 2 — the accepting round, [j = k].  Only the two agreeing outcomes
    survive ([Pi_pair_eq] gives [Ev] on the target pair), and pulling
    [EqSub] back through the bilateral CNOTs gives [Pass].  The rounds
    before [k] have already been measured, so the left factor is [NeqSub]
    and the target is [inv_q k k n], not [pre_q k n]. *)
Lemma round_sum_accept : forall n k,
    (k <= n)%nat ->
    (round_wp n k 0 0 (post_q k n) .+ round_wp n k 1 1 (post_q k n))
    = inv_q k k n.
Admitted.

(** OPEN 3 — a rejecting round, [j < k].  The two disagreeing outcomes
    survive ([Pi_pair_neq] gives [Od]), and pulling [NeqSub] back through
    the bilateral CNOTs gives [Rej] — Distillation.md's

        A(1,0) + A(0,1) = CNOT_A* CNOT_B* NeqSub_j CNOT_B CNOT_A = Rej_j.

    Round [j] carries [NeqSub] in [inv_q (S j) k n] and [Rej] in
    [inv_q j k n]; the two agreeing outcomes contribute Zero, which is why
    only two summands appear. *)
Lemma round_sum_reject : forall n k j,
    (j < k)%nat -> (k <= n)%nat ->
    (round_wp n j 0 1 (inv_q (S j) k n) .+ round_wp n j 1 0 (inv_q (S j) k n))
    = inv_q j k n.
Admitted.

(** And [inv_q 0 k n] is the specification's precondition, up to the unit
    factor [kron_n 0 _ = I 1]. *)
Lemma inv_q_0 : forall k n, inv_q 0 k n = pre_q k n.
Proof.
  intros k n. unfold inv_q, pre_q. cbn [kron_n].
  rewrite Nat.sub_0_r.
  rewrite kron_1_l by (apply WF_kron_n; unfold Rej, Ev, Od; auto with wf_db).
  reflexivity.
Qed.
