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

(** ** Splitting a 16-dimensional operator by its leading qubit *********

    Every product below lives in 16 dimensions, and [lma'] cannot evaluate
    a 16-dimensional product — its cost is driven by the number of NESTED
    [Mmult]s (each one costs roughly a factor of five), so anything with
    more than two of them is out of reach at any dimension.

    [s2] is the way round: it splits an operator by the value of its
    leading qubit, and turns ONE product of size 2m into TWO of size m.
    Two applications take a round's operators from 16 down to 4, where the
    remaining products can be pushed onto the two qubits separately by
    [kron_mixed_product] and finished entrywise. *)

Definition s2 {m : nat} (A B : Square m) : Square (2 * m) :=
  Pi 0 ⊗ A .+ Pi 1 ⊗ B.

Lemma WF_Pi : forall v, WF_Matrix (Pi v).
Proof. intro v; unfold Pi; destruct (Nat.eqb v 0%nat); auto with wf_db. Qed.
#[local] Hint Resolve WF_Pi : wf_db.

Lemma Pi_herm : forall v, (Pi v) † = Pi v.
Proof. intro v; unfold Pi; destruct (Nat.eqb v 0%nat); lma'. Qed.
Lemma Pi_00 : Pi 0 × Pi 0 = Pi 0.  Proof. unfold Pi; cbn; lma'. Qed.
Lemma Pi_11 : Pi 1 × Pi 1 = Pi 1.  Proof. unfold Pi; cbn; lma'. Qed.
Lemma Pi_01 : Pi 0 × Pi 1 = Zero.  Proof. unfold Pi; cbn; lma'. Qed.
Lemma Pi_10 : Pi 1 × Pi 0 = Zero.  Proof. unfold Pi; cbn; lma'. Qed.

Lemma s2_mult : forall m (A B C D : Square m),
    @s2 m A B × @s2 m C D = @s2 m (A × C) (B × D).
Proof.
  intros m A B C D. unfold s2.
  rewrite Mmult_plus_distr_l, !Mmult_plus_distr_r, !kron_mixed_product.
  rewrite Pi_00, Pi_11, Pi_01, Pi_10, !kron_0_l, Mplus_0_r, Mplus_0_l.
  reflexivity.
Qed.

Lemma s2_adj : forall m (A B : Square m), (@s2 m A B) † = @s2 m (A †) (B †).
Proof.
  intros m A B. unfold s2.
  rewrite Mplus_adjoint, !kron_adjoint, !Pi_herm. reflexivity.
Qed.

Lemma s2_plus : forall m (A B C D : Square m),
    @s2 m A B .+ @s2 m C D = @s2 m (A .+ C) (B .+ D).
Proof. intros m A B C D. unfold s2. lma. Qed.

Lemma s2_I : forall m, @s2 m (I m) (I m) = I (2 * m).
Proof.
  intro m. unfold s2. rewrite <- kron_plus_distr_r, Pi_sum, id_kron. reflexivity.
Qed.

Lemma s2_diag : forall m (A : Square m), @s2 m A A = I 2 ⊗ A.
Proof.
  intros m A. unfold s2. rewrite <- kron_plus_distr_r, Pi_sum. reflexivity.
Qed.

Lemma s2_inj : forall m (A B C D : Square m),
    A = C -> B = D -> @s2 m A B = @s2 m C D.
Proof. intros; subst; reflexivity. Qed.

Lemma I4_s2 : forall m (A : Square m), WF_Matrix A ->
    I 4 ⊗ A = @s2 (2 * m) (@s2 m A A) (@s2 m A A).
Proof.
  intros m A HA. rewrite !s2_diag, <- kron_assoc by auto with wf_db.
  rewrite id_kron. reflexivity.
Qed.

(** ** One round's four qubits: Ak, Bk, At, Bt *************************

    Everything below is stated at dimension 16 — the round's own block —
    and lifted to the [4(n+1)]-qubit register afterwards. *)

Lemma WF_Ev : WF_Matrix Ev. Proof. unfold Ev; auto with wf_db. Qed.
Lemma WF_Od : WF_Matrix Od. Proof. unfold Od; auto with wf_db. Qed.
#[local] Hint Resolve WF_Ev WF_Od : wf_db.

Definition CA4 : Square 16 := pad_ctrl 4 0 2 σx.
Definition CB4 : Square 16 := pad_ctrl 4 1 3 σx.
Definition MA4 (v : nat) : Square 16 := pad_u 4 2 (Pi v).
Definition MB4 (v : nat) : Square 16 := pad_u 4 3 (Pi v).

Ltac padcbn := cbn [Nat.ltb Nat.leb Nat.sub Nat.add Nat.pow];
  rewrite ?Nat.mul_1_r, ?Nat.mul_1_l.

Lemma CA4_s2 : CA4 = @s2 8 (@s2 4 (I 4) (I 4)) (@s2 4 (σx ⊗ I 2) (σx ⊗ I 2)).
Proof.
  unfold CA4, pad_ctrl, pad; padcbn.
  rewrite kron_1_l by auto with wf_db.
  rewrite kron_plus_distr_r, !kron_assoc by auto with wf_db.
  rewrite !id_kron, s2_I, s2_diag. unfold s2.
  apply Mplus_comm.
Qed.

Lemma CB4_s2 : CB4 = @s2 8 (@s2 4 (I 4) (I 2 ⊗ σx)) (@s2 4 (I 4) (I 2 ⊗ σx)).
Proof.
  unfold CB4, pad_ctrl, pad; padcbn.
  rewrite kron_1_r by auto with wf_db.
  rewrite s2_diag. f_equal.
  rewrite !kron_assoc by auto with wf_db.
  rewrite !id_kron. unfold s2. apply Mplus_comm.
Qed.

Lemma pad_u_2 : forall (u : Square 2), WF_Matrix u -> pad_u 4 2 u = I 4 ⊗ (u ⊗ I 2).
Proof.
  intros u Hu. rewrite <- kron_assoc by auto with wf_db.
  unfold pad_u, pad; padcbn. reflexivity.
Qed.

Lemma pad_u_3 : forall (u : Square 2), WF_Matrix u -> pad_u 4 3 u = I 4 ⊗ (I 2 ⊗ u).
Proof.
  intros u Hu. rewrite <- kron_assoc by auto with wf_db. rewrite id_kron.
  unfold pad_u, pad; padcbn. rewrite kron_1_r by auto with wf_db. reflexivity.
Qed.

Lemma MA4_s2 : forall v, MA4 v
    = @s2 8 (@s2 4 (Pi v ⊗ I 2) (Pi v ⊗ I 2)) (@s2 4 (Pi v ⊗ I 2) (Pi v ⊗ I 2)).
Proof.
  intro v. unfold MA4. rewrite pad_u_2 by auto with wf_db.
  rewrite I4_s2 by auto with wf_db. reflexivity.
Qed.

Lemma MB4_s2 : forall v, MB4 v
    = @s2 8 (@s2 4 (I 2 ⊗ Pi v) (I 2 ⊗ Pi v)) (@s2 4 (I 2 ⊗ Pi v) (I 2 ⊗ Pi v)).
Proof.
  intro v. unfold MB4. rewrite pad_u_3 by auto with wf_db.
  rewrite I4_s2 by auto with wf_db. reflexivity.
Qed.

Lemma Ev_kron : forall m (C : Square m), WF_Matrix C ->
    Ev ⊗ C = @s2 (2 * m) (Pi 0 ⊗ C) (Pi 1 ⊗ C).
Proof.
  intros m C HC. unfold Ev, s2.
  rewrite kron_plus_distr_r, !kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma Od_kron : forall m (C : Square m), WF_Matrix C ->
    Od ⊗ C = @s2 (2 * m) (Pi 1 ⊗ C) (Pi 0 ⊗ C).
Proof.
  intros m C HC. unfold Od, s2.
  rewrite kron_plus_distr_r, !kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma Pass_s2 : Pass = @s2 8 (@s2 4 Ev Od) (@s2 4 Od Ev).
Proof.
  unfold Pass.
  rewrite Ev_kron by auto with wf_db. rewrite Od_kron by auto with wf_db.
  restore_dims. rewrite s2_plus.
  apply s2_inj; [reflexivity | apply Mplus_comm].
Qed.

Lemma Rej_s2 : Rej = @s2 8 (@s2 4 Od Ev) (@s2 4 Ev Od).
Proof.
  unfold Rej.
  rewrite Ev_kron by auto with wf_db. rewrite Od_kron by auto with wf_db.
  restore_dims. rewrite s2_plus.
  apply s2_inj; [reflexivity | apply Mplus_comm].
Qed.

Lemma EqSub_s2 : EqSub = @s2 8 (@s2 4 Ev Ev) (@s2 4 Ev Ev).
Proof. unfold EqSub. rewrite I4_s2 by auto with wf_db. reflexivity. Qed.

Lemma NeqSub_s2 : NeqSub = @s2 8 (@s2 4 Od Od) (@s2 4 Od Od).
Proof. unfold NeqSub. rewrite I4_s2 by auto with wf_db. reflexivity. Qed.

(** ** The block-level transformers and the four core identities ******* *)

Definition wpA4 (v : nat) (X : Square 16) : Square 16 :=
  CA4 † × ((MA4 v) † × X × MA4 v) × CA4.
Definition wpB4 (v : nat) (X : Square 16) : Square 16 :=
  CB4 † × ((MB4 v) † × X × MB4 v) × CB4.
Definition r4 (va vb : nat) (X : Square 16) : Square 16 := wpA4 va (wpB4 vb X).

Ltac s2_step :=
  restore_dims; rewrite ?s2_adj;
  restore_dims; rewrite ?s2_mult;
  restore_dims; rewrite ?s2_plus.

Ltac leafcycle :=
  restore_dims; rewrite ?Mmult_plus_distr_l, ?Mmult_plus_distr_r;
  restore_dims; rewrite ?kron_mixed_product; Msimpl.

Ltac leaf :=
  restore_dims; rewrite ?kron_adjoint; Msimpl;
  unfold Ev, Od, Pi; cbn [Nat.eqb];
  leafcycle; leafcycle; leafcycle; leafcycle;
  lma'; auto 20 with wf_db.

Ltac to_s2 :=
  unfold r4, wpA4, wpB4;
  rewrite ?CA4_s2, ?CB4_s2, ?MA4_s2, ?MB4_s2,
          ?EqSub_s2, ?NeqSub_s2, ?Pass_s2, ?Rej_s2.

Ltac core := to_s2; s2_step; apply s2_inj; s2_step; apply s2_inj; leaf.

(** The accepting round: only the two AGREEING outcome pairs survive, and
    the bilateral CNOT pulls [EqSub] back to [Pass]. *)
Lemma core_accept : r4 0 0 EqSub .+ r4 1 1 EqSub = Pass.
Proof. core. Qed.

(** A rejecting round: only the two DISAGREEING pairs survive, and the
    bilateral CNOT pulls [NeqSub] back to [Rej]. *)
Lemma core_reject : r4 0 1 NeqSub .+ r4 1 0 NeqSub = Rej.
Proof. core. Qed.

(** An idle round, one party at a time: the two outcomes sum to the
    identity on that party's test qubit, and its CNOT then cancels. *)
Lemma core_idleA : wpA4 0 (I 16) .+ wpA4 1 (I 16) = I 16.
Proof.
  unfold wpA4. rewrite ?CA4_s2, ?MA4_s2.
  replace (I 16) with (@s2 8 (@s2 4 (I 4) (I 4)) (@s2 4 (I 4) (I 4)))
    by (rewrite !s2_I; reflexivity).
  s2_step. apply s2_inj; s2_step; apply s2_inj; leaf.
Qed.

Lemma core_idleB : wpB4 0 (I 16) .+ wpB4 1 (I 16) = I 16.
Proof.
  unfold wpB4. rewrite ?CB4_s2, ?MB4_s2.
  replace (I 16) with (@s2 8 (@s2 4 (I 4) (I 4)) (@s2 4 (I 4) (I 4)))
    by (rewrite !s2_I; reflexivity).
  s2_step. apply s2_inj; s2_step; apply s2_inj; leaf.
Qed.
Lemma pow16 : forall j, (16 ^ j)%nat = (2 ^ (4 * j))%nat.
Proof. intro j. rewrite Nat.pow_mul_r. reflexivity. Qed.

(** The one lemma the whole matrix side stands on: an operator padded at a
    SYMBOLIC offset [4j] touches only block [j].  The right-hand side is
    written out rather than as [pad w s 4 A], so that the middle factor's
    kron index is the natural [2^s * 2^w * 2^(4-s-w)] and not the ascribed
    [16] — for symbolic [s] and [w] the two are equal but NOT convertible,
    and [kron_assoc] would not unify. *)
Lemma pad_block : forall n j s w (A : Square (2 ^ w)),
    WF_Matrix A -> (j <= n)%nat -> (s + w <= 4)%nat ->
    @pad w (4 * j + s) (4 * S n) A
    = I (16 ^ j) ⊗ (I (2 ^ s) ⊗ A ⊗ I (2 ^ (4 - (s + w)))) ⊗ I (16 ^ (n - j)).
Proof.
  intros n j s w A HA Hj Hsw. unfold pad.
  bdestruct (4 * j + s + w <=? 4 * S n); [| exfalso; lia].
  rewrite !pow16.
  replace (2 ^ (4 * j + s))%nat with (2 ^ (4 * j) * 2 ^ s)%nat
    by (rewrite <- Nat.pow_add_r; reflexivity).
  replace (2 ^ (4 * S n - (4 * j + s + w)))%nat
     with (2 ^ (4 - (s + w)) * 2 ^ (4 * (n - j)))%nat
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite <- !id_kron.
  rewrite <- !kron_assoc by auto with wf_db.
  reflexivity.
Qed.

Lemma pad_block0 : forall n j w (A : Square (2 ^ w)),
    WF_Matrix A -> (j <= n)%nat -> (w <= 4)%nat ->
    @pad w (4 * j) (4 * S n) A
    = I (16 ^ j) ⊗ (A ⊗ I (2 ^ (4 - w))) ⊗ I (16 ^ (n - j)).
Proof.
  intros n j w A HA Hj Hw.
  replace (4 * j)%nat with (4 * j + 0)%nat by lia.
  rewrite (pad_block n j 0 w A HA Hj ltac:(lia)).
  cbn [Nat.pow]. rewrite kron_1_l by assumption. rewrite ?Nat.mul_1_l.
  replace (4 - (0 + w))%nat with (4 - w)%nat by lia.
  reflexivity.
Qed.

Lemma pad_ctrl_blockA : forall n j (u : Square 2), WF_Matrix u -> (j <= n)%nat ->
    pad_ctrl (4 * S n) (4 * j) (4 * j + 2) u
    = I (16 ^ j) ⊗ pad_ctrl 4 0 2 u ⊗ I (16 ^ (n - j)).
Proof.
  intros n j u Hu Hj. unfold pad_ctrl at 1.
  bdestruct (4 * j <? 4 * j + 2); [| exfalso; lia].
  replace (4 * j + 2 - 4 * j - 1)%nat with 1%nat by lia.
  rewrite (pad_block0 n j (1 + 1 + 1)
             (∣1⟩⟨1∣ ⊗ I (2 ^ 1) ⊗ u .+ ∣0⟩⟨0∣ ⊗ I (2 ^ 1) ⊗ I 2)
             ltac:(auto with wf_db) Hj ltac:(lia)).
  unfold pad_ctrl, pad; cbn; Msimpl; reflexivity.
Qed.

Lemma pad_ctrl_blockB : forall n j (u : Square 2), WF_Matrix u -> (j <= n)%nat ->
    pad_ctrl (4 * S n) (4 * j + 1) (4 * j + 3) u
    = I (16 ^ j) ⊗ pad_ctrl 4 1 3 u ⊗ I (16 ^ (n - j)).
Proof.
  intros n j u Hu Hj. unfold pad_ctrl at 1.
  bdestruct (4 * j + 1 <? 4 * j + 3); [| exfalso; lia].
  replace (4 * j + 3 - (4 * j + 1) - 1)%nat with 1%nat by lia.
  rewrite (pad_block n j 1 (1 + 1 + 1)
             (∣1⟩⟨1∣ ⊗ I (2 ^ 1) ⊗ u .+ ∣0⟩⟨0∣ ⊗ I (2 ^ 1) ⊗ I 2)
             ltac:(auto with wf_db) Hj ltac:(lia)).
  unfold pad_ctrl, pad; cbn; Msimpl; reflexivity.
Qed.

Lemma pad_u_blockA : forall n j (u : Square 2), WF_Matrix u -> (j <= n)%nat ->
    pad_u (4 * S n) (4 * j + 2) u = I (16 ^ j) ⊗ pad_u 4 2 u ⊗ I (16 ^ (n - j)).
Proof.
  intros n j u Hu Hj. unfold pad_u at 1.
  rewrite (pad_block n j 2 1 u Hu Hj) by lia.
  unfold pad_u, pad; cbn; Msimpl; reflexivity.
Qed.

Lemma pad_u_blockB : forall n j (u : Square 2), WF_Matrix u -> (j <= n)%nat ->
    pad_u (4 * S n) (4 * j + 3) u = I (16 ^ j) ⊗ pad_u 4 3 u ⊗ I (16 ^ (n - j)).
Proof.
  intros n j u Hu Hj. unfold pad_u at 1.
  rewrite (pad_block n j 3 1 u Hu Hj) by lia.
  unfold pad_u, pad; cbn; Msimpl; reflexivity.
Qed.
(** ** A round's operators, and their block form *********************** *)

Lemma WF_CA4 : WF_Matrix CA4.
Proof. unfold CA4. apply (WF_pad_ctrl 4); auto with wf_db. Qed.
Lemma WF_CB4 : WF_Matrix CB4.
Proof. unfold CB4. apply (WF_pad_ctrl 4); auto with wf_db. Qed.
Lemma WF_MA4 : forall v, WF_Matrix (MA4 v).
Proof. intro v. unfold MA4. apply (WF_pad_u 4); auto with wf_db. Qed.
Lemma WF_MB4 : forall v, WF_Matrix (MB4 v).
Proof. intro v. unfold MB4. apply (WF_pad_u 4); auto with wf_db. Qed.
#[local] Hint Resolve WF_CA4 WF_CB4 WF_MA4 WF_MB4 : wf_db.

Definition cA (n j : nat) : Square (2 ^ (4 * S n)) :=
  pad_ctrl (4 * S n) (Ak j) (At j) σx.
Definition cB (n j : nat) : Square (2 ^ (4 * S n)) :=
  pad_ctrl (4 * S n) (Bk j) (Bt j) σx.
Definition mA (n j v : nat) : Square (2 ^ (4 * S n)) :=
  pad_u (4 * S n) (At j) (Pi v).
Definition mB (n j v : nat) : Square (2 ^ (4 * S n)) :=
  pad_u (4 * S n) (Bt j) (Pi v).

Lemma cA_block : forall n j, (j <= n)%nat ->
    cA n j = I (16 ^ j) ⊗ CA4 ⊗ I (16 ^ (n - j)).
Proof.
  intros n j Hj. unfold cA, Ak, At, CA4.
  apply pad_ctrl_blockA; [auto with wf_db | exact Hj].
Qed.

Lemma cB_block : forall n j, (j <= n)%nat ->
    cB n j = I (16 ^ j) ⊗ CB4 ⊗ I (16 ^ (n - j)).
Proof.
  intros n j Hj. unfold cB, Bk, Bt, CB4.
  apply pad_ctrl_blockB; [auto with wf_db | exact Hj].
Qed.

Lemma mA_block : forall n j v, (j <= n)%nat ->
    mA n j v = I (16 ^ j) ⊗ MA4 v ⊗ I (16 ^ (n - j)).
Proof.
  intros n j v Hj. unfold mA, At, MA4.
  apply pad_u_blockA; [auto with wf_db | exact Hj].
Qed.

Lemma mB_block : forall n j v, (j <= n)%nat ->
    mB n j v = I (16 ^ j) ⊗ MB4 v ⊗ I (16 ^ (n - j)).
Proof.
  intros n j v Hj. unfold mB, Bt, MB4.
  apply pad_u_blockB; [auto with wf_db | exact Hj].
Qed.

(** ONE PARTY's half of a round, read backwards. *)
Definition wpA (n j v : nat) (X : Square (2 ^ (4 * S n)))
  : Square (2 ^ (4 * S n)) :=
  (cA n j) † × ((mA n j v) † × X × (mA n j v)) × (cA n j).

Definition wpB (n j v : nat) (X : Square (2 ^ (4 * S n)))
  : Square (2 ^ (4 * S n)) :=
  (cB n j) † × ((mB n j v) † × X × (mB n j v)) × (cB n j).

Definition round_wp (n j va vb : nat) (X : Square (2 ^ (4 * S n)))
  : Square (2 ^ (4 * S n)) :=
  wpA n j va (wpB n j vb X).

Definition round_sum (n j : nat) (X : Square (2 ^ (4 * S n)))
  : Square (2 ^ (4 * S n)) :=
  (round_wp n j 0 0 X .+ round_wp n j 0 1 X)
  .+ (round_wp n j 1 0 X .+ round_wp n j 1 1 X).

Lemma wpA_plus : forall n j v X Y,
    wpA n j v (X .+ Y) = wpA n j v X .+ wpA n j v Y.
Proof.
  intros n j v X Y. unfold wpA.
  rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
  rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
  reflexivity.
Qed.

(** ** Localisation ***************************************************

    Conjugating a three-factor tensor by an operator supported on the
    middle factor leaves the outer two alone. *)

Lemma conj_local : forall a b (L : Square a) (R : Square b) (X K : Square 16),
    WF_Matrix L -> WF_Matrix R -> WF_Matrix X -> WF_Matrix K ->
    (I a ⊗ K ⊗ I b) † × (L ⊗ X ⊗ R) × (I a ⊗ K ⊗ I b)
    = L ⊗ (K † × X × K) ⊗ R.
Proof.
  intros a b L R X K HL HR HX HK.
  rewrite !kron_adjoint, !id_adjoint_eq.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

Lemma dim16 : forall j n, (j <= n)%nat ->
    (16 ^ j * 16 * 16 ^ (n - j))%nat = (2 ^ (4 * S n))%nat.
Proof.
  intros j n H.
  replace (16 ^ j * 16 * 16 ^ (n - j))%nat with (16 ^ (j + 1 + (n - j)))%nat
    by (rewrite !Nat.pow_add_r; cbn [Nat.pow]; ring).
  replace (j + 1 + (n - j))%nat with (S n) by lia.
  rewrite Nat.pow_mul_r. reflexivity.
Qed.

Lemma wpA_local : forall n j v (L : Square (16 ^ j)) (R : Square (16 ^ (n - j)))
                         (X : Square 16),
    (j <= n)%nat -> WF_Matrix L -> WF_Matrix R -> WF_Matrix X ->
    wpA n j v (L ⊗ X ⊗ R) = L ⊗ wpA4 v X ⊗ R.
Proof.
  intros n j v L R X Hj HL HR HX.
  unfold wpA, wpA4.
  rewrite (cA_block n j Hj), (mA_block n j v Hj).
  rewrite <- (dim16 j n Hj).
  rewrite !conj_local by auto with wf_db.
  reflexivity.
Qed.

Lemma wpB_local : forall n j v (L : Square (16 ^ j)) (R : Square (16 ^ (n - j)))
                         (X : Square 16),
    (j <= n)%nat -> WF_Matrix L -> WF_Matrix R -> WF_Matrix X ->
    wpB n j v (L ⊗ X ⊗ R) = L ⊗ wpB4 v X ⊗ R.
Proof.
  intros n j v L R X Hj HL HR HX.
  unfold wpB, wpB4.
  rewrite (cB_block n j Hj), (mB_block n j v Hj).
  rewrite <- (dim16 j n Hj).
  rewrite !conj_local by auto with wf_db.
  reflexivity.
Qed.

(** ** Splitting a predicate at one block ****************************** *)

Lemma WF_Pass : WF_Matrix Pass.     Proof. unfold Pass; auto with wf_db. Qed.
Lemma WF_Rej : WF_Matrix Rej.       Proof. unfold Rej; auto with wf_db. Qed.
Lemma WF_EqSub : WF_Matrix EqSub.   Proof. unfold EqSub; auto with wf_db. Qed.
Lemma WF_NeqSub : WF_Matrix NeqSub. Proof. unfold NeqSub; auto with wf_db. Qed.
#[local] Hint Resolve WF_Pass WF_Rej WF_EqSub WF_NeqSub : wf_db.
Lemma WF_kn_NeqSub : forall j, WF_Matrix (kron_n j NeqSub).
Proof. intro j. apply WF_kron_n; auto with wf_db. Qed.
Lemma WF_kn_Rej : forall j, WF_Matrix (kron_n j Rej).
Proof. intro j. apply WF_kron_n; auto with wf_db. Qed.
#[local] Hint Resolve WF_kron_n WF_kn_NeqSub WF_kn_Rej : wf_db.

Lemma WF_wpA4 : forall v X, WF_Matrix X -> WF_Matrix (wpA4 v X).
Proof. intros v X HX. unfold wpA4; repeat apply WF_mult; auto with wf_db. Qed.
Lemma WF_wpB4 : forall v X, WF_Matrix X -> WF_Matrix (wpB4 v X).
Proof. intros v X HX. unfold wpB4; repeat apply WF_mult; auto with wf_db. Qed.
#[local] Hint Resolve WF_wpA4 WF_wpB4 : wf_db.

Lemma pow16_split : forall a b, (16 ^ a * 16 * 16 ^ b)%nat = (16 ^ (a + 1 + b))%nat.
Proof. intros a b. rewrite !Nat.pow_add_r; cbn [Nat.pow]; ring. Qed.

(** An idle round [j > k]: the postcondition leaves block [j] free. *)
Lemma post_q_idle : forall k n j, (k < j)%nat -> (j <= n)%nat ->
    exists L : Square (16 ^ j),
      WF_Matrix L /\ post_q k n = L ⊗ I 16 ⊗ I (16 ^ (n - j)).
Proof.
  intros k n j Hkj Hjn.
  exists (kron_n k NeqSub ⊗ EqSub ⊗ I (16 ^ (j - k - 1))).
  replace (16 ^ j)%nat with (16 ^ k * 16 * 16 ^ (j - k - 1))%nat
    by (rewrite pow16_split; f_equal; lia).
  split; [solve [auto 30 with wf_db] |].
  unfold post_q. rewrite kron_n_I_gen.
  replace (16 ^ (n - k))%nat with (16 ^ (j - k - 1) * 16 * 16 ^ (n - j))%nat
    by (rewrite pow16_split; f_equal; lia).
  rewrite <- !id_kron.
  rewrite <- !kron_assoc by auto with wf_db.
  reflexivity.
Qed.

(** The accepting round [j = k]: block [k] carries [EqSub] afterwards and
    [Pass] before. *)
Lemma acc_split : forall k n, (k <= n)%nat ->
    post_q k n = kron_n k NeqSub ⊗ EqSub ⊗ I (16 ^ (n - k))
    /\ inv_q k k n = kron_n k NeqSub ⊗ Pass ⊗ I (16 ^ (n - k)).
Proof.
  intros k n Hk. split.
  - unfold post_q. rewrite kron_n_I_gen. reflexivity.
  - unfold inv_q. rewrite kron_n_I_gen.
    replace (k - k)%nat with 0%nat by lia. cbn [kron_n].
    rewrite kron_1_r by auto with wf_db. reflexivity.
Qed.

(** A rejecting round [j < k]: block [j] carries [NeqSub] afterwards and
    [Rej] before, with everything to its right unchanged. *)
(* All five dimensions are variables, so nothing can mismatch: this is the
   one shape the regrouping ever needs. *)
Lemma kron5_regroup : forall a b c d e (A : Square a) (B : Square b)
                             (C : Square c) (D : Square d) (E : Square e),
    WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> WF_Matrix D -> WF_Matrix E ->
    A ⊗ B ⊗ C ⊗ D ⊗ E = A ⊗ B ⊗ (C ⊗ D ⊗ E).
Proof.
  intros. rewrite !kron_assoc by auto with wf_db.
  rewrite !Nat.mul_assoc. reflexivity.
Qed.

Lemma kron5_regroup' : forall a b c d e (A : Square a) (B : Square b)
                              (C : Square c) (D : Square d) (E : Square e),
    WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> WF_Matrix D -> WF_Matrix E ->
    A ⊗ (B ⊗ C) ⊗ D ⊗ E = A ⊗ B ⊗ (C ⊗ D ⊗ E).
Proof.
  intros. rewrite !kron_assoc by auto with wf_db.
  rewrite !Nat.mul_assoc. reflexivity.
Qed.

Lemma rej_split : forall j k n, (j < k)%nat -> (k <= n)%nat ->
    exists R : Square (16 ^ (n - j)),
      WF_Matrix R
      /\ inv_q (S j) k n = kron_n j NeqSub ⊗ NeqSub ⊗ R
      /\ inv_q j k n     = kron_n j NeqSub ⊗ Rej ⊗ R.
Proof.
  intros j k n Hjk Hkn.
  exists (kron_n (k - S j) Rej ⊗ Pass ⊗ I (16 ^ (n - k))).
  assert (Hl : (16 ^ (n - j))%nat = (16 ^ (k - S j) * 16 * 16 ^ (n - k))%nat)
    by (rewrite pow16_split; f_equal; lia).
  rewrite Hl.
  split; [ solve [auto 30 with wf_db] |]. split.
  - unfold inv_q. rewrite kron_n_I_gen.
    replace (16 ^ S j)%nat with (16 ^ j * 16)%nat by (cbn [Nat.pow]; ring).
    rewrite kron_n_S.
    apply kron5_regroup; auto 30 with wf_db.
  - unfold inv_q. rewrite kron_n_I_gen.
    replace (k - j)%nat with (S (k - S j)) by lia.
    rewrite kron_n_assoc by auto 30 with wf_db.
    apply kron5_regroup'; auto 30 with wf_db.
Qed.

(* Again all dimensions are variables, so the pattern cannot fail to
   match on an index. *)
Lemma kron3_plus : forall a b c (L : Square a) (X Y : Square b) (R : Square c),
    L ⊗ X ⊗ R .+ L ⊗ Y ⊗ R = L ⊗ (X .+ Y) ⊗ R.
Proof.
  intros a b c L X Y R.
  rewrite <- kron_plus_distr_r, <- kron_plus_distr_l. reflexivity.
Qed.

(** ** The four obligations ******************************************* *)

Lemma core_accept' : wpA4 0 (wpB4 0 EqSub) .+ wpA4 1 (wpB4 1 EqSub) = Pass.
Proof. exact core_accept. Qed.

Lemma core_reject' : wpA4 0 (wpB4 1 NeqSub) .+ wpA4 1 (wpB4 0 NeqSub) = Rej.
Proof. exact core_reject. Qed.

Lemma wpA_sum_idle : forall n k j,
    (k < j)%nat -> (j <= n)%nat ->
    wpA n j 0 (post_q k n) .+ wpA n j 1 (post_q k n) = post_q k n.
Proof.
  intros n k j Hkj Hjn.
  destruct (post_q_idle k n j Hkj Hjn) as [L [HL HP]].
  rewrite HP. rewrite <- (dim16 j n Hjn).
  rewrite !wpA_local by (try lia; auto with wf_db).
  rewrite kron3_plus, core_idleA. reflexivity.
Qed.

Lemma wpB_sum_idle : forall n k j,
    (k < j)%nat -> (j <= n)%nat ->
    wpB n j 0 (post_q k n) .+ wpB n j 1 (post_q k n) = post_q k n.
Proof.
  intros n k j Hkj Hjn.
  destruct (post_q_idle k n j Hkj Hjn) as [L [HL HP]].
  rewrite HP. rewrite <- (dim16 j n Hjn).
  rewrite !wpB_local by (try lia; auto with wf_db).
  rewrite kron3_plus, core_idleB. reflexivity.
Qed.

Lemma round_sum_accept : forall n k,
    (k <= n)%nat ->
    (round_wp n k 0 0 (post_q k n) .+ round_wp n k 1 1 (post_q k n))
    = inv_q k k n.
Proof.
  intros n k Hk. destruct (acc_split k n Hk) as [HP HI].
  rewrite HP, HI. rewrite <- (dim16 k n Hk). unfold round_wp.
  rewrite !wpB_local by (try lia; auto with wf_db).
  rewrite !wpA_local by (try lia; auto with wf_db).
  rewrite kron3_plus, core_accept'. reflexivity.
Qed.

Lemma round_sum_reject : forall n k j,
    (j < k)%nat -> (k <= n)%nat ->
    (round_wp n j 0 1 (inv_q (S j) k n) .+ round_wp n j 1 0 (inv_q (S j) k n))
    = inv_q j k n.
Proof.
  intros n k j Hjk Hkn. destruct (rej_split j k n Hjk Hkn) as [R [HR [H1 H2]]].
  rewrite H1, H2. rewrite <- (dim16 j n ltac:(lia)). unfold round_wp.
  rewrite !wpB_local by (try lia; auto with wf_db).
  rewrite !wpA_local by (try lia; auto with wf_db).
  rewrite kron3_plus, core_reject'. reflexivity.
Qed.

(** An idle round as a whole, from the two halves. *)
Lemma round_sum_idle : forall n k j,
    (k < j)%nat -> (j <= n)%nat ->
    round_sum n j (post_q k n) = post_q k n.
Proof.
  intros n k j H1 H2. unfold round_sum, round_wp.
  rewrite <- !wpA_plus.
  rewrite (wpB_sum_idle n k j H1 H2).
  apply (wpA_sum_idle n k j H1 H2).
Qed.

(** And [inv_q 0 k n] is the specification's precondition, up to the unit
    factor [kron_n 0 _ = I 1]. *)
Lemma inv_q_0 : forall k n, inv_q 0 k n = pre_q k n.
Proof.
  intros k n. unfold inv_q, pre_q. cbn [kron_n].
  rewrite Nat.sub_0_r.
  rewrite kron_1_l by (apply WF_kron_n; unfold Rej, Ev, Od; auto with wf_db).
  reflexivity.
Qed.
