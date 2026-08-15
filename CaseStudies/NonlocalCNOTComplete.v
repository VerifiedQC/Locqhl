(** * Completeness of the non-local CNOT protocol — the matrix facts
      behind the [NonlocalCNOT.v] case study.

    The counterpart of [BellComplete.v] and [SwapComplete.v], and like them
    it depends on QuantumLib ALONE (plus BellComplete, which is itself
    QuantumLib-only).  No notion of the logic appears here: no [is_effect],
    no [assertion], no [interp].  The case study states its obligations in
    the logic's terms and closes them against this file by conversion,
    because the two [lowner]s have the same body.

    Qubit order, six of them:  A(0) B(1) C(2) C'(3) T(4) T'(5).

    The protocol, as a single operator string.  Reading right to left is
    reading the protocol forwards:

        K(u,v) = Z_C^v · Π^B_v · H_B · CNOT[B,T] · X_B^u · Π^A_u · CNOT[C,A]

    and the branch pre-effect is the sandwich K(u,v)† · Post · K(u,v).

    Why this file cannot copy SwapComplete's shape.  There, every unitary
    came BEFORE every measurement, so the whole string factored as U† S U
    with one unitary U and one block projector S.  Here Bob's X correction
    sits BETWEEN the two measurements and DEPENDS on the first outcome, so
    no such factorisation exists.  What replaces it:

      * Π^A_u touches qubit 0 and everything between the two measurements
        touches qubits 1..5, so Π^A_u COMMUTES with all of it.  That is
        what makes each branch a projector.
      * Branches with different u are killed by Π^A_u Π^A_{u'} = 0, and
        branches with the same u but different v by Π^B_v Π^B_{v'} = 0
        carried through the conjugation.  So the four branches are
        pairwise orthogonal projectors and their sum is a projector.
      * The Cauchy-Schwarz step ([BellComplete.outer_le_proj]) is then the
        same as in the other two files. *)

From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad VecSet CauchySchwarz.
From Locqhl.CaseStudies Require BellComplete.

Local Open Scope matrix_scope.

(* The Löwner order, written exactly as in Locqhl.Core.Assertions, in
   BellComplete and in SwapComplete.  Same body, so the case study's
   obligation is closed by conversion. *)
Definition lowner {n} (M N : Square n) : Prop :=
  positive_semidefinite (N .+ (- C1) .* M)%M.

Notation "M ⊑ N" := (lowner M N) (at level 70).

(* ---- The matrices --------------------------------------------------- *)

Definition EPR : Square 4 := ∣Φ+⟩ × ∣Φ+⟩†.

(** The input: EPR(A,B) ⊗ EPR(C,C') ⊗ EPR(T,T'), three adjacent pairs. *)
Definition Psi0 : Vector (2 ^ 6) := ∣Φ+⟩ ⊗ ∣Φ+⟩ ⊗ ∣Φ+⟩.

Definition Pi (b : nat) : Square 2 :=
  if Nat.eqb b 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣.

(** The reference block (C,C',T,T'), block-local indices: C is 0, T is 2. *)
Definition CNOT_CT : Square (2 ^ 4) := pad_ctrl 4 0 2 σx.

Definition CNOTChoi : Square (2 ^ 4) := CNOT_CT × (EPR ⊗ EPR) × CNOT_CT †.

(** Alice's Z correction, inside the block. *)
Definition Zblk : Square (2 ^ 4) := pad_u 4 0 σz.

Definition Frame (v : nat) : Square (2 ^ 4) :=
  if Nat.eqb v 1%nat then Zblk † × CNOTChoi × Zblk else CNOTChoi.

(* ---- The six-qubit operators of the protocol ------------------------ *)

Definition gCNOT_CA : Square (2 ^ 6) := pad_ctrl 6 2 0 σx.
Definition gCNOT_BT : Square (2 ^ 6) := pad_ctrl 6 1 4 σx.
Definition gH_B     : Square (2 ^ 6) := pad_u 6 1 hadamard.

Definition gX_B (u : nat) : Square (2 ^ 6) :=
  if Nat.eqb u 1%nat then pad_u 6 1 σx else I (2 ^ 6).

Definition gZ_C (v : nat) : Square (2 ^ 6) :=
  if Nat.eqb v 1%nat then pad_u 6 2 σz else I (2 ^ 6).

Definition PiA (u : nat) : Square (2 ^ 6) := pad_u 6 0 (Pi u).
Definition PiB (v : nat) : Square (2 ^ 6) := pad_u 6 1 (Pi v).

Definition Post : Square (2 ^ 6) := I 2 ⊗ I 2 ⊗ CNOTChoi.

(** The protocol as one operator string; right to left is forwards. *)
(** Right-associated on purpose: this is the association that six
    [conj_merge] steps produce when the case study folds its nested
    sandwich, so the two sides meet by conversion rather than by another
    round of [Mmult_assoc]. *)
Definition Kuv (u v : nat) : Square (2 ^ 6) :=
  gZ_C v × (PiB v × (gH_B × (gCNOT_BT × (gX_B u × (PiA u × gCNOT_CA))))).

Definition Auv (u v : nat) : Square (2 ^ 6) := (Kuv u v) † × Post × (Kuv u v).

(* ---- Well-formedness ------------------------------------------------- *)

Lemma WF_EPR : WF_Matrix EPR.
Proof. unfold EPR; auto with wf_db. Qed.
#[export] Hint Resolve WF_EPR : wf_db.

Lemma WF_Pi : forall b, WF_Matrix (Pi b).
Proof. intros b; unfold Pi; destruct (Nat.eqb b 0%nat); auto with wf_db. Qed.
#[export] Hint Resolve WF_Pi : wf_db.

Lemma WF_Psi0 : WF_Matrix Psi0.
Proof. unfold Psi0; restore_dims; auto 10 with wf_db. Qed.
#[export] Hint Resolve WF_Psi0 : wf_db.

Lemma CNOT_CT_unitary : WF_Unitary CNOT_CT.
Proof. apply pad_ctrl_unitary; [lia | lia | lia | apply σx_unitary]. Qed.

Lemma WF_CNOT_CT : WF_Matrix CNOT_CT.
Proof. destruct CNOT_CT_unitary; assumption. Qed.
#[export] Hint Resolve WF_CNOT_CT : wf_db.

Lemma WF_CNOTChoi : WF_Matrix CNOTChoi.
Proof. unfold CNOTChoi; auto with wf_db. Qed.
#[export] Hint Resolve WF_CNOTChoi : wf_db.

Lemma Zblk_unitary : WF_Unitary Zblk.
Proof. apply pad_u_unitary; [lia | apply σz_unitary]. Qed.

Lemma WF_Zblk : WF_Matrix Zblk.
Proof. destruct Zblk_unitary; assumption. Qed.
#[export] Hint Resolve WF_Zblk : wf_db.

Lemma WF_Frame : forall v, WF_Matrix (Frame v).
Proof.
  intros v; unfold Frame; destruct (Nat.eqb v 1%nat); auto with wf_db.
Qed.
#[export] Hint Resolve WF_Frame : wf_db.

Lemma gCNOT_CA_unitary : WF_Unitary gCNOT_CA.
Proof. apply pad_ctrl_unitary; [lia | lia | lia | apply σx_unitary]. Qed.

Lemma gCNOT_BT_unitary : WF_Unitary gCNOT_BT.
Proof. apply pad_ctrl_unitary; [lia | lia | lia | apply σx_unitary]. Qed.

Lemma gH_B_unitary : WF_Unitary gH_B.
Proof. apply pad_u_unitary; [lia | apply H_unitary]. Qed.

Lemma gX_B_unitary : forall u, WF_Unitary (gX_B u).
Proof.
  intros u; unfold gX_B; destruct (Nat.eqb u 1%nat);
    [apply pad_u_unitary; [lia | apply σx_unitary] | apply id_unitary].
Qed.

Lemma gZ_C_unitary : forall v, WF_Unitary (gZ_C v).
Proof.
  intros v; unfold gZ_C; destruct (Nat.eqb v 1%nat);
    [apply pad_u_unitary; [lia | apply σz_unitary] | apply id_unitary].
Qed.

Lemma WF_gCNOT_CA : WF_Matrix gCNOT_CA.
Proof. destruct gCNOT_CA_unitary; assumption. Qed.
Lemma WF_gCNOT_BT : WF_Matrix gCNOT_BT.
Proof. destruct gCNOT_BT_unitary; assumption. Qed.
Lemma WF_gH_B : WF_Matrix gH_B.
Proof. destruct gH_B_unitary; assumption. Qed.
Lemma WF_gX_B : forall u, WF_Matrix (gX_B u).
Proof. intros u; destruct (gX_B_unitary u); assumption. Qed.
Lemma WF_gZ_C : forall v, WF_Matrix (gZ_C v).
Proof. intros v; destruct (gZ_C_unitary v); assumption. Qed.
#[export] Hint Resolve WF_gCNOT_CA WF_gCNOT_BT WF_gH_B WF_gX_B WF_gZ_C : wf_db.

Lemma WF_PiA : forall u, WF_Matrix (PiA u).
Proof. intros u; unfold PiA; apply WF_pad_u; auto with wf_db. Qed.
Lemma WF_PiB : forall v, WF_Matrix (PiB v).
Proof. intros v; unfold PiB; apply WF_pad_u; auto with wf_db. Qed.
#[export] Hint Resolve WF_PiA WF_PiB : wf_db.

Lemma WF_Post : WF_Matrix Post.
Proof. unfold Post; restore_dims; auto with wf_db. Qed.
#[export] Hint Resolve WF_Post : wf_db.

Lemma WF_Kuv : forall u v, WF_Matrix (Kuv u v).
Proof. intros u v; unfold Kuv; auto 10 with wf_db. Qed.
#[export] Hint Resolve WF_Kuv : wf_db.

Lemma WF_Auv : forall u v, WF_Matrix (Auv u v).
Proof. intros u v; unfold Auv; auto with wf_db. Qed.
#[export] Hint Resolve WF_Auv : wf_db.

(* ---- Generic projector algebra --------------------------------------- *)

Lemma sandwich_herm : forall n (V M : Square n),
    M † = M -> (V × M × V †) † = V × M × V †.
Proof.
  intros n V M Hh.
  rewrite !Mmult_adjoint, adjoint_involutive, Hh, Mmult_assoc. reflexivity.
Qed.

Lemma sandwich_idem : forall n (V M : Square n),
    WF_Matrix V -> WF_Matrix M -> V † × V = I n -> M × M = M ->
    (V × M × V †) × (V × M × V †) = V × M × V †.
Proof.
  intros n V M WV WM Hu Hi.
  rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (V †) V (M × V †)), Hu.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc M M (V †)), Hi. reflexivity.
Qed.

(* ---- The Bell projector ---------------------------------------------- *)

Lemma EPR_herm : EPR † = EPR.
Proof. unfold EPR. rewrite Mmult_adjoint, adjoint_involutive. reflexivity. Qed.

Lemma EPR_idem : EPR × EPR = EPR.
Proof.
  unfold EPR. rewrite Mmult_assoc, <- (Mmult_assoc (∣Φ+⟩ †)), BellComplete.EPR_inner.
  rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma EPR_fix : EPR × ∣Φ+⟩ = ∣Φ+⟩.
Proof.
  unfold EPR. rewrite Mmult_assoc, BellComplete.EPR_inner, Mmult_1_r;
    auto with wf_db.
Qed.

(** The two Bell pairs of the reference block, as one projector. *)
Definition EE : Square (2 ^ 4) := EPR ⊗ EPR.

Lemma WF_EE : WF_Matrix EE.
Proof. unfold EE; restore_dims; auto with wf_db. Qed.
#[export] Hint Resolve WF_EE : wf_db.

Lemma EE_herm : EE † = EE.
Proof. unfold EE. restore_dims. rewrite kron_adjoint, !EPR_herm. reflexivity. Qed.

Lemma EE_idem : EE × EE = EE.
Proof.
  unfold EE. restore_dims. rewrite kron_mixed_product, !EPR_idem. reflexivity.
Qed.

(* ---- The Choi projector ---------------------------------------------- *)

Lemma CNOT_CT_flip : CNOT_CT † × CNOT_CT = I (2 ^ 4).
Proof. destruct CNOT_CT_unitary as [_ H]; exact H. Qed.

Lemma CNOT_CT_flip' : CNOT_CT × CNOT_CT † = I (2 ^ 4).
Proof.
  destruct CNOT_CT_unitary as [W H]. apply Minv_flip; auto with wf_db.
Qed.

Lemma CNOTChoi_herm : CNOTChoi † = CNOTChoi.
Proof. unfold CNOTChoi. apply sandwich_herm, EE_herm. Qed.

Lemma CNOTChoi_idem : CNOTChoi × CNOTChoi = CNOTChoi.
Proof.
  unfold CNOTChoi.
  apply sandwich_idem; auto with wf_db; [ exact CNOT_CT_flip | exact EE_idem ].
Qed.

(* ---- Alice's Z frame ------------------------------------------------- *)

(* [pad_u 4 0] is [I 1 ⊗ _ ⊗ I 8]; peel the unit factor once, here, so that
   no proof below has to reason under a [pad]. *)
Lemma Zblk_eq : Zblk = σz ⊗ I 8.
Proof.
  unfold Zblk, pad_u, pad. cbn [Nat.add Nat.sub Nat.leb Nat.pow].
  rewrite kron_1_l by auto with wf_db. reflexivity.
Qed.

Lemma Zblk_herm : Zblk † = Zblk.
Proof.
  rewrite Zblk_eq. restore_dims.
  rewrite kron_adjoint, id_adjoint_eq.
  replace (σz †) with σz by lma'. reflexivity.
Qed.

Lemma Zblk_flip : Zblk † × Zblk = I (2 ^ 4).
Proof. destruct Zblk_unitary as [_ H]; exact H. Qed.

Lemma Zblk_flip' : Zblk × Zblk † = I (2 ^ 4).
Proof.
  destruct Zblk_unitary as [W H]. apply Minv_flip; auto with wf_db.
Qed.

Lemma Frame_herm : forall v, (Frame v) † = Frame v.
Proof.
  intros v; unfold Frame; destruct (Nat.eqb v 1%nat); [| apply CNOTChoi_herm].
  rewrite !Mmult_adjoint, adjoint_involutive, CNOTChoi_herm, Mmult_assoc.
  reflexivity.
Qed.

Lemma Frame_idem : forall v, Frame v × Frame v = Frame v.
Proof.
  intros v; unfold Frame; destruct (Nat.eqb v 1%nat); [| apply CNOTChoi_idem].
  rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc Zblk (Zblk †) (CNOTChoi × Zblk)), Zblk_flip'.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc CNOTChoi CNOTChoi Zblk), CNOTChoi_idem.
  reflexivity.
Qed.

(* ---- The single-qubit projector algebra, from BellComplete ----------- *)

Lemma Pi_herm : forall b, (Pi b) † = Pi b.
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

(* ---- G: "Bob measures v, and the block is in Frame v" ---------------- *)

(** The projector Bob's measurement leaves behind, on (B,C,C',T,T').
    Blocks orthogonal on B, each block a Frame — so a projector. *)
Definition G : Square (2 ^ 5) := Pi 0 ⊗ Frame 0 .+ Pi 1 ⊗ Frame 1.

Lemma WF_G : WF_Matrix G.
Proof. unfold G; restore_dims; auto with wf_db. Qed.
#[export] Hint Resolve WF_G : wf_db.

Lemma G_herm : G † = G.
Proof.
  unfold G. rewrite Mplus_adjoint. restore_dims.
  rewrite !kron_adjoint, !Pi_herm, !Frame_herm. reflexivity.
Qed.

Lemma G_idem : G × G = G.
Proof.
  unfold G.
  rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r.
  restore_dims. rewrite !kron_mixed_product.
  rewrite !Pi_same, Pi_01, Pi_10, !Frame_idem.
  rewrite !kron_0_l, Mplus_0_l, Mplus_0_r. reflexivity.
Qed.

(* ---- Padded operators: adjoint, product, and commutation ------------- *)

(** No operator below is ever taken apart into [I 2 ⊗ _].  QuantumLib's
    [pad_A_B_commutes] and [pad_A_ctrl_commutes] already say what this file
    needs — that operators at distinct qubits commute — and saying it that
    way keeps every dimension index in the product form the rewrites want.
    An earlier attempt that split qubit A off by hand fought [restore_dims]
    at every step; this does not. *)

Lemma pad_u_adjoint : forall dim n (M : Square 2),
    (pad_u dim n M) † = pad_u dim n (M †).
Proof.
  (* [gridify] is what puts the dimension indices back in product form, so
     that [kron_adjoint] can see the krons at all. *)
  intros dim n M. unfold pad_u, pad. gridify.
  rewrite !kron_adjoint, !id_adjoint_eq. reflexivity.
Qed.

Lemma pad_u_zero : forall dim n, pad_u dim n Zero = Zero.
Proof.
  intros dim n. unfold pad_u, pad.
  destruct (n + 1 <=? dim)%nat; [| reflexivity].
  rewrite kron_0_r, kron_0_l. reflexivity.
Qed.

(* -- Alice's measurement projector -- *)

Lemma PiA_herm : forall u, (PiA u) † = PiA u.
Proof. intros u; unfold PiA; rewrite pad_u_adjoint, Pi_herm; reflexivity. Qed.

Lemma PiA_idem : forall u, PiA u × PiA u = PiA u.
Proof.
  intros u; unfold PiA.
  rewrite <- pad_u_mmult by auto with wf_db. rewrite Pi_same. reflexivity.
Qed.

Lemma PiA_01 : PiA 0 × PiA 1 = Zero.
Proof.
  unfold PiA. rewrite <- pad_u_mmult by auto with wf_db.
  rewrite Pi_01. apply pad_u_zero.
Qed.

Lemma PiA_10 : PiA 1 × PiA 0 = Zero.
Proof.
  unfold PiA. rewrite <- pad_u_mmult by auto with wf_db.
  rewrite Pi_10. apply pad_u_zero.
Qed.

(* -- Bob's measurement projector -- *)

Lemma PiB_herm : forall v, (PiB v) † = PiB v.
Proof. intros v; unfold PiB; rewrite pad_u_adjoint, Pi_herm; reflexivity. Qed.

Lemma PiB_idem : forall v, PiB v × PiB v = PiB v.
Proof.
  intros v; unfold PiB.
  rewrite <- pad_u_mmult by auto with wf_db. rewrite Pi_same. reflexivity.
Qed.

Lemma PiB_01 : PiB 0 × PiB 1 = Zero.
Proof.
  unfold PiB. rewrite <- pad_u_mmult by auto with wf_db.
  rewrite Pi_01. apply pad_u_zero.
Qed.

Lemma PiB_10 : PiB 1 × PiB 0 = Zero.
Proof.
  unfold PiB. rewrite <- pad_u_mmult by auto with wf_db.
  rewrite Pi_10. apply pad_u_zero.
Qed.

(* -- Π^A_u commutes with everything between the two measurements --

   This is the fact the whole file turns on: Alice's projector sits at
   qubit 0, and Bob's correction, his CNOT, his H, his projector and
   Alice's Z all sit at qubits 1, 2 and 4.  So the branch operator can be
   reordered until the two Π^A_u meet, and [PiA_idem] collapses them. *)

Lemma PiA_gX_B : forall u w, PiA u × gX_B w = gX_B w × PiA u.
Proof.
  intros u w; unfold PiA, gX_B; destruct (Nat.eqb w 1%nat).
  - apply pad_A_B_commutes; auto with wf_db.
  - rewrite Mmult_1_l, Mmult_1_r by auto with wf_db; reflexivity.
Qed.

Lemma PiA_gH_B : forall u, PiA u × gH_B = gH_B × PiA u.
Proof. intros u; unfold PiA, gH_B; apply pad_A_B_commutes; auto with wf_db. Qed.

Lemma PiA_PiB : forall u v, PiA u × PiB v = PiB v × PiA u.
Proof. intros u v; unfold PiA, PiB; apply pad_A_B_commutes; auto with wf_db. Qed.

Lemma PiA_gZ_C : forall u v, PiA u × gZ_C v = gZ_C v × PiA u.
Proof.
  intros u v; unfold PiA, gZ_C; destruct (Nat.eqb v 1%nat).
  - apply pad_A_B_commutes; auto with wf_db.
  - rewrite Mmult_1_l, Mmult_1_r by auto with wf_db; reflexivity.
Qed.

Lemma PiA_gCNOT_BT : forall u, PiA u × gCNOT_BT = gCNOT_BT × PiA u.
Proof.
  intros u; unfold PiA, gCNOT_BT; apply pad_A_ctrl_commutes; auto with wf_db.
Qed.

(* ---- What the case study's effect checks need ------------------------ *)

(** [is_effect] is a notion of the logic and stays in [NonlocalCNOT.v];
    the arithmetic under it is here.  "Hermitian and idempotent" is exactly
    "orthogonal projector", and such a matrix is an effect: PSD because it
    equals M M†, and below I because I - M is again hermitian idempotent. *)

Lemma lowner_refl : forall n (M : Square n), M ⊑ M.
Proof.
  intros n M. unfold lowner, positive_semidefinite. intros z Hz.
  replace (M .+ (- C1) .* M) with (@Zero n n) by lma.
  rewrite Mmult_0_r, Mmult_0_l. cbn. lra.
Qed.

Lemma herm_idem_psd : forall n (M : Square n),
    M † = M -> M × M = M -> positive_semidefinite M.
Proof.
  intros n M Hh Hi.
  assert (E : M = M × M †) by (rewrite Hh, Hi; reflexivity).
  rewrite E at 1. apply positive_semidefinite_AAadjoint.
Qed.

Lemma compl_herm : forall n (M : Square n),
    M † = M -> (I n .+ (- C1) .* M) † = I n .+ (- C1) .* M.
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

(** The padded block operator every constant assertion of the case study
    denotes.  The I's are on the LEFT here, because A and B are qubits 0
    and 1 — the mirror of [SwapComplete.ab_*]. *)

Lemma WF_blk : forall M : Square (2 ^ 4),
    WF_Matrix M -> WF_Matrix (I 2 ⊗ I 2 ⊗ M).
Proof. intros M WM. restore_dims; auto with wf_db. Qed.

Lemma blk_herm : forall M : Square (2 ^ 4),
    WF_Matrix M -> M † = M -> (I 2 ⊗ I 2 ⊗ M) † = I 2 ⊗ I 2 ⊗ M.
Proof.
  intros M WM Hh. restore_dims.
  rewrite !kron_adjoint, !id_adjoint_eq, Hh. reflexivity.
Qed.

Lemma blk_idem : forall M : Square (2 ^ 4),
    WF_Matrix M -> M × M = M ->
    (I 2 ⊗ I 2 ⊗ M) × (I 2 ⊗ I 2 ⊗ M) = I 2 ⊗ I 2 ⊗ M.
Proof.
  intros M WM Hi. restore_dims. rewrite !kron_mixed_product.
  rewrite !Mmult_1_l, Hi by auto with wf_db. reflexivity.
Qed.

(** The identity branch of a conditional correction: when the guard fails
    the correction is I, and the conjugation is the identity map. *)
Lemma conj_id : forall n (M : Square n),
    WF_Matrix M -> (I n) † × M × I n = M.
Proof.
  intros n M WM. rewrite id_adjoint_eq, Mmult_1_l, Mmult_1_r by assumption.
  reflexivity.
Qed.

(* ---- WF in the shape [cbn] produces ---------------------------------- *)

(** The case study's entailments see the protocol's operators AFTER [cbn]
    has unfolded [pad_u] and [pad_ctrl] into raw krons, and at dimension 64
    [auto with wf_db] cannot rebuild the dimension arithmetic.  Going back
    through the pad lemma does.  These are the counterpart of
    [SwapComplete.padA_conj]/[padB_conj], which are stated in the same
    post-[cbn] shape for the same reason. *)

Lemma WF_cnotBT_raw :
  @WF_Matrix 64 64 (I 2 ⊗ (∣1⟩⟨1∣ ⊗ I 4 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 4 ⊗ I 2) ⊗ I 2).
Proof. apply (WF_pad_ctrl 6 1 4 σx). auto with wf_db. Qed.

Lemma WF_hB_raw : @WF_Matrix 64 64 (I 2 ⊗ hadamard ⊗ I 16).
Proof. apply (WF_pad_u 6 1 hadamard). auto with wf_db. Qed.

Lemma WF_piB0_raw : @WF_Matrix 64 64 (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 16).
Proof. apply (WF_pad_u 6 1 ∣0⟩⟨0∣). auto with wf_db. Qed.

Lemma WF_piB1_raw : @WF_Matrix 64 64 (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 16).
Proof. apply (WF_pad_u 6 1 ∣1⟩⟨1∣). auto with wf_db. Qed.

Lemma WF_choi_raw : @WF_Matrix 64 64 (I 2 ⊗ I 2 ⊗ CNOTChoi).
Proof. restore_dims; auto with wf_db. Qed.

Lemma WF_zC_raw : @WF_Matrix 64 64 (pad_u 6 2 σz).
Proof. apply (WF_pad_u 6 2 σz); auto with wf_db. Qed.

Lemma WF_xB_raw : @WF_Matrix 64 64 (pad_u 6 1 σx).
Proof. apply (WF_pad_u 6 1 σx); auto with wf_db. Qed.

#[export] Hint Resolve WF_cnotBT_raw WF_hB_raw WF_piB0_raw WF_piB1_raw
                       WF_choi_raw WF_zC_raw WF_xB_raw : wf_db.

(* ---- Conjugation by a contraction ------------------------------------ *)

(** The case study's [bob_wp] denotes the goal projector conjugated by the
    whole of Bob's backward chain, and that chain is NOT unitary: it
    contains his measurement operator.  So its effect check is not "this is
    a projector" — it is "conjugating an effect by a contraction leaves an
    effect", which is what the three lemmas below say.

        0 ⊑ K†AK      whenever 0 ⊑ A
        K†AK ⊑ I      whenever A ⊑ I and K†K ⊑ I

    the second because  I − K†AK  =  K†(I − A)K  +  (I − K†K),  a sum of
    two positive operators. *)

Lemma psd_plus : forall n (A B : Square n),
    positive_semidefinite A -> positive_semidefinite B ->
    positive_semidefinite (A .+ B).
Proof.
  intros n A B HA HB z Hz.
  specialize (HA z Hz); specialize (HB z Hz).
  rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
  unfold Mplus. cbn. lra.
Qed.

Lemma conj_psd : forall n (K A : Square n),
    WF_Matrix K -> positive_semidefinite A ->
    positive_semidefinite (K † × A × K).
Proof.
  intros n K A WK HA z Hz.
  specialize (HA (K × z) (WF_mult _ _ WK Hz)).
  replace ((z) † × (K † × A × K) × z) with (((K × z) †) × A × (K × z));
    [ exact HA |].
  rewrite Mmult_adjoint, !Mmult_assoc. reflexivity.
Qed.

Lemma conj_le_I : forall n (K A : Square n),
    WF_Matrix K -> WF_Matrix A ->
    A ⊑ I n -> (K † × K) ⊑ I n -> (K † × A × K) ⊑ I n.
Proof.
  intros n K A WK WA HA HK. unfold lowner in *.
  replace (I n .+ (- C1) .* (K † × A × K))
    with ((K † × (I n .+ (- C1) .* A) × K) .+ (I n .+ (- C1) .* (K † × K))).
  - apply psd_plus; [ apply conj_psd; assumption | assumption ].
  - rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
    rewrite Mmult_1_r by auto with wf_db.
    rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
    lma.
Qed.

(* ---- Bob's backward chain is a contraction --------------------------- *)

(** The chain as [cbn] hands it to the case study.  [reflexivity] against
    the [pad] forms, so the unitarity facts above transfer unchanged. *)

Definition cnotBT_raw : Square 64 :=
  I 2 ⊗ (∣1⟩⟨1∣ ⊗ I 4 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 4 ⊗ I 2) ⊗ I 2.

Definition hB_raw : Square 64 := I 2 ⊗ hadamard ⊗ I 16.

Definition piB_raw (v : nat) : Square 64 :=
  if Nat.eqb v 0%nat then I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 16
  else if Nat.eqb v 1%nat then I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 16 else Zero.

Lemma cnotBT_raw_eq : cnotBT_raw = gCNOT_BT.  Proof. reflexivity. Qed.
Lemma hB_raw_eq     : hB_raw     = gH_B.      Proof. reflexivity. Qed.

Lemma WF_piB_raw : forall v, WF_Matrix (piB_raw v).
Proof.
  intros v; unfold piB_raw;
    destruct (Nat.eqb v 0%nat); [| destruct (Nat.eqb v 1%nat)];
    auto using WF_piB0_raw, WF_piB1_raw with wf_db.
Qed.
#[export] Hint Resolve WF_piB_raw : wf_db.

Lemma piB_raw_herm : forall v, (piB_raw v) † = piB_raw v.
Proof.
  intros v; unfold piB_raw;
    destruct (Nat.eqb v 0%nat); [| destruct (Nat.eqb v 1%nat)];
    try (now rewrite zero_adjoint_eq);
    restore_dims; rewrite !kron_adjoint, !id_adjoint_eq;
    [ rewrite BellComplete.braket0_herm | rewrite BellComplete.braket1_herm ];
    reflexivity.
Qed.

Lemma piB_raw_idem : forall v, piB_raw v × piB_raw v = piB_raw v.
Proof.
  intros v; unfold piB_raw;
    destruct (Nat.eqb v 0%nat); [| destruct (Nat.eqb v 1%nat)];
    try (now rewrite Mmult_0_l);
    restore_dims; rewrite !kron_mixed_product, !Mmult_1_l by auto with wf_db;
    [ rewrite BellComplete.braket00 | rewrite BellComplete.braket11 ];
    reflexivity.
Qed.


(** Bob's two unitary layers as ONE matrix.  Naming the product is what
    makes the chain literally a [W† M W] sandwich, so the projector algebra
    above applies verbatim; leaving it as a two-factor product forces the
    association surgery that Rocq's dimension indices do not survive. *)
Definition bobU : Square 64 := hB_raw × cnotBT_raw.

Lemma bobU_unitary : WF_Unitary bobU.
Proof.
  unfold bobU. rewrite hB_raw_eq, cnotBT_raw_eq.
  apply Mmult_unitary; [ exact gH_B_unitary | exact gCNOT_BT_unitary ].
Qed.

Lemma WF_bobU : WF_Matrix bobU.
Proof. destruct bobU_unitary; assumption. Qed.
#[export] Hint Resolve WF_bobU : wf_db.

Lemma bobU_flip : bobU × bobU † = I 64.
Proof. destruct bobU_unitary as [W H0]. apply Minv_flip; auto with wf_db. Qed.

(** K†K for Bob's chain K = Z0 · Π^B_v · H_B · CNOT[B,T].  The Z0 layer
    cancels against its adjoint, [piB_raw_idem] collapses the projector,
    and what is left is a unitary conjugate of a projector — a projector,
    hence below I.  [Z0] is Alice's pending Z correction, whichever way its
    guard went; all the proof needs of it is unitarity. *)
Lemma bobK_le_I : forall (Z0 : Square 64) (v : nat),
    WF_Matrix Z0 -> Z0 † × Z0 = I 64 ->
    ((Z0 × piB_raw v × hB_raw × cnotBT_raw) †
     × (Z0 × piB_raw v × hB_raw × cnotBT_raw)) ⊑ I 64.
Proof.
  intros Z0 v WZ HZ. unfold lowner.
  replace ((Z0 × piB_raw v × hB_raw × cnotBT_raw) †
           × (Z0 × piB_raw v × hB_raw × cnotBT_raw))
    with (bobU † × piB_raw v × bobU).
  2:{ unfold bobU. rewrite !Mmult_adjoint, !Mmult_assoc.
      rewrite <- (Mmult_assoc (Z0 †) Z0), HZ, Mmult_1_l by auto with wf_db.
      rewrite piB_raw_herm.
      rewrite <- (Mmult_assoc (piB_raw v) (piB_raw v)), piB_raw_idem.
      reflexivity. }
  apply herm_idem_psd.
  - apply compl_herm.
    rewrite !Mmult_adjoint, adjoint_involutive, piB_raw_herm, !Mmult_assoc.
    reflexivity.
  - apply compl_idem; [ auto with wf_db |].
    rewrite !Mmult_assoc.
    rewrite <- (Mmult_assoc bobU (bobU †) (piB_raw v × bobU)), bobU_flip.
    rewrite Mmult_1_l by auto with wf_db.
    rewrite <- (Mmult_assoc (piB_raw v) (piB_raw v) bobU), piB_raw_idem.
    reflexivity.
Qed.

(** A projector is below I — the [K†K ⊑ I] side condition of [conj_le_I]
    whenever K is a measurement operator rather than a gate. *)
Lemma proj_le_I : forall n (M : Square n),
    WF_Matrix M -> M † = M -> M × M = M -> M ⊑ I n.
Proof.
  intros n M WM Hh Hi. unfold lowner.
  apply herm_idem_psd; [ apply compl_herm | apply compl_idem ]; assumption.
Qed.

Lemma cnotBT_flip : cnotBT_raw † × cnotBT_raw = I 64.
Proof. rewrite cnotBT_raw_eq. exact (proj2 gCNOT_BT_unitary). Qed.

Lemma hB_flip : hB_raw † × hB_raw = I 64.
Proof. rewrite hB_raw_eq. exact (proj2 gH_B_unitary). Qed.

Lemma piB_raw_le_I : forall v, (piB_raw v) † × piB_raw v ⊑ I 64.
Proof.
  intros v. rewrite piB_raw_herm, piB_raw_idem.
  apply proj_le_I; [ auto with wf_db | apply piB_raw_herm | apply piB_raw_idem ].
Qed.

(** Folding one conjugation layer into the next.  Applied repeatedly this
    turns the nested sandwich the case study's [cbn] produces into the
    single sandwich [Auv] — confirmed layer by layer against the printed
    goal: [pad_ctrl 6 2 0 σx] is [gCNOT_CA], [pad_u 6 0 (Pi u)] is [PiA u],
    [pad_u 6 2 σz] is [gZ_C 1], and so on. *)
Lemma conj_merge : forall n (A B M : Square n),
    A † × (B † × M × B) × A = (B × A) † × M × (B × A).
Proof. intros n A B M. rewrite Mmult_adjoint, !Mmult_assoc. reflexivity. Qed.

(* ---- Splitting the branch operator at qubit A ------------------------ *)

(** Everything of the protocol that touches qubits 1..5, as one matrix.
    [K(u,v)] is then [L(u,v)] applied after Alice's projector and her CNOT,
    and since L lives on 1..5 and Π^A_u on 0, the two commute. *)
Definition Luv (u v : nat) : Square (2 ^ 6) :=
  gZ_C v × (PiB v × (gH_B × (gCNOT_BT × gX_B u))).

Lemma WF_Luv : forall u v, WF_Matrix (Luv u v).
Proof. intros u v; unfold Luv; auto 10 with wf_db. Qed.
#[export] Hint Resolve WF_Luv : wf_db.

Lemma Kuv_split : forall u v, Kuv u v = Luv u v × (PiA u × gCNOT_CA).
Proof. intros u v. unfold Kuv, Luv. rewrite !Mmult_assoc. reflexivity. Qed.

Lemma PiA_Luv : forall u a b, PiA u × Luv a b = Luv a b × PiA u.
Proof.
  intros u a b. unfold Luv.
  rewrite <- (Mmult_assoc (PiA u) (gZ_C b)), PiA_gZ_C.
  rewrite (Mmult_assoc (gZ_C b) (PiA u)).
  rewrite <- (Mmult_assoc (PiA u) (PiB b)), PiA_PiB.
  rewrite (Mmult_assoc (PiB b) (PiA u)).
  rewrite <- (Mmult_assoc (PiA u) gH_B), PiA_gH_B.
  rewrite (Mmult_assoc gH_B (PiA u)).
  rewrite <- (Mmult_assoc (PiA u) gCNOT_BT), PiA_gCNOT_BT.
  rewrite (Mmult_assoc gCNOT_BT (PiA u)).
  rewrite PiA_gX_B.
  rewrite !Mmult_assoc. reflexivity.
Qed.

(* ---- N(u,v) is a projector, even though L(u,v) is not unitary -------- *)

Lemma gX_B_flip : forall u, gX_B u × (gX_B u) † = I (2 ^ 6).
Proof. intros u; destruct (gX_B_unitary u) as [W H0]; apply Minv_flip; auto with wf_db. Qed.
Lemma gCNOT_BT_flip : gCNOT_BT × gCNOT_BT † = I (2 ^ 6).
Proof. destruct gCNOT_BT_unitary as [W H0]; apply Minv_flip; auto with wf_db. Qed.
Lemma gH_B_flip : gH_B × gH_B † = I (2 ^ 6).
Proof. destruct gH_B_unitary as [W H0]; apply Minv_flip; auto with wf_db. Qed.

Lemma gZ_C_herm : forall v, (gZ_C v) † = gZ_C v.
Proof.
  intros v; unfold gZ_C; destruct (Nat.eqb v 1%nat); [| apply id_adjoint_eq].
  rewrite pad_u_adjoint. replace (σz †) with σz by lma'. reflexivity.
Qed.

Lemma gZ_C_sq : forall v, gZ_C v × gZ_C v = I (2 ^ 6).
Proof.
  intros v. rewrite <- (gZ_C_herm v) at 2.
  destruct (gZ_C_unitary v) as [W H0]. apply Minv_flip; auto with wf_db.
Qed.

(** σz sits at qubit 2 and Bob's projector at qubit 1. *)
Lemma gZ_C_PiB : forall v w, gZ_C v × PiB w = PiB w × gZ_C v.
Proof.
  intros v w; unfold gZ_C, PiB; destruct (Nat.eqb v 1%nat).
  - apply pad_A_B_commutes; [lia | auto with wf_db | auto with wf_db].
  - rewrite Mmult_1_l, Mmult_1_r by auto with wf_db; reflexivity.
Qed.

(** L L† = Π^B: the unitary layers cancel and Z commutes past the
    projector.  This is what makes N idempotent below. *)
Lemma Luv_flip : forall u v, Luv u v × (Luv u v) † = PiB v.
Proof.
  intros u v. unfold Luv.
  rewrite !Mmult_adjoint, !Mmult_assoc.
  rewrite <- (Mmult_assoc (gX_B u) ((gX_B u) †)), gX_B_flip.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc gCNOT_BT (gCNOT_BT †)), gCNOT_BT_flip.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc gH_B (gH_B †)), gH_B_flip.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite PiB_herm.
  rewrite <- (Mmult_assoc (PiB v) (PiB v)), PiB_idem.
  rewrite gZ_C_herm.
  rewrite <- (Mmult_assoc (gZ_C v) (PiB v) (gZ_C v)), gZ_C_PiB.
  rewrite Mmult_assoc, gZ_C_sq, Mmult_1_r by auto with wf_db.
  reflexivity.
Qed.

(** L† Π^B = L†: the projector is already leftmost inside L. *)
Lemma Luv_absorb : forall u v, (Luv u v) † × PiB v = (Luv u v) †.
Proof.
  intros u v. unfold Luv.
  rewrite !Mmult_adjoint, !Mmult_assoc.
  rewrite gZ_C_herm, PiB_herm.
  rewrite gZ_C_PiB.
  rewrite <- (Mmult_assoc (PiB v) (PiB v) (gZ_C v)), PiB_idem.
  reflexivity.
Qed.

Lemma PiB_Luv : forall u v, PiB v × Luv u v = Luv u v.
Proof.
  intros u v. assert (H := Luv_absorb u v).
  apply (f_equal (fun M : Square (2 ^ 6) => M †)) in H.
  rewrite Mmult_adjoint, PiB_herm, !adjoint_involutive in H. exact H.
Qed.

Lemma PiB_eq : forall v, PiB v = I 2 ⊗ Pi v ⊗ I 16.
Proof.
  intros v; unfold PiB, pad_u, pad.
  cbn [Nat.add Nat.sub Nat.leb Nat.pow]. reflexivity.
Qed.

Lemma Post_herm : Post † = Post.
Proof. unfold Post. apply blk_herm; [auto with wf_db | apply CNOTChoi_herm]. Qed.

Lemma Post_idem : Post × Post = Post.
Proof. unfold Post. apply blk_idem; [auto with wf_db | apply CNOTChoi_idem]. Qed.

(** The goal projector lives on qubits 2..5 and Bob's projector on qubit 1. *)
Lemma Post_PiB : forall v, Post × PiB v = PiB v × Post.
Proof.
  intros v. unfold Post. rewrite PiB_eq. restore_dims.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

Definition Nuv (u v : nat) : Square (2 ^ 6) := (Luv u v) † × Post × Luv u v.

Lemma WF_Nuv : forall u v, WF_Matrix (Nuv u v).
Proof. intros u v; unfold Nuv; auto with wf_db. Qed.
#[export] Hint Resolve WF_Nuv : wf_db.

Lemma Nuv_herm : forall u v, (Nuv u v) † = Nuv u v.
Proof.
  intros u v; unfold Nuv.
  rewrite !Mmult_adjoint, adjoint_involutive, Post_herm, Mmult_assoc.
  reflexivity.
Qed.

(** THE step.  L is not unitary, so this is not "unitary conjugate of a
    projector"; it is [Luv_flip] and [PiB_Luv] doing the work. *)
Lemma Nuv_idem : forall u v, Nuv u v × Nuv u v = Nuv u v.
Proof.
  intros u v; unfold Nuv.
  rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (Luv u v) ((Luv u v) †) (Post × Luv u v)), Luv_flip.
  rewrite <- (Mmult_assoc (PiB v) Post (Luv u v)), <- Post_PiB.
  rewrite (Mmult_assoc Post (PiB v) (Luv u v)), PiB_Luv.
  rewrite <- (Mmult_assoc Post Post (Luv u v)), Post_idem.
  reflexivity.
Qed.

(* ---- A(u,v) = CNOT[C,A]† · (Π^A_u · N(u,v)) · CNOT[C,A] -------------- *)

Lemma PiA_eq : forall u, PiA u = Pi u ⊗ I 32.
Proof.
  intros u; unfold PiA, pad_u, pad.
  cbn [Nat.add Nat.sub Nat.leb Nat.pow].
  rewrite kron_1_l by auto with wf_db. reflexivity.
Qed.

Lemma Post_split : Post = I 2 ⊗ (I 2 ⊗ CNOTChoi).
Proof. unfold Post. apply kron_assoc; auto with wf_db. Qed.

Lemma PiA_Post : forall u, PiA u × Post = Post × PiA u.
Proof.
  intros u. rewrite PiA_eq, Post_split. restore_dims.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

Lemma PiA_Luv_adj : forall u a b, PiA u × (Luv a b) † = (Luv a b) † × PiA u.
Proof.
  intros u a b. assert (H := PiA_Luv u a b).
  apply (f_equal (fun M : Square (2 ^ 6) => M †)) in H.
  rewrite !Mmult_adjoint, PiA_herm in H. symmetry; exact H.
Qed.

Lemma PiA_Nuv : forall u a b, PiA u × Nuv a b = Nuv a b × PiA u.
Proof.
  intros u a b. unfold Nuv. rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (PiA u) ((Luv a b) †)), PiA_Luv_adj.
  rewrite (Mmult_assoc ((Luv a b) †) (PiA u)).
  rewrite <- (Mmult_assoc (PiA u) Post), PiA_Post.
  rewrite (Mmult_assoc Post (PiA u)), PiA_Luv.
  rewrite <- !Mmult_assoc. reflexivity.
Qed.

(** The branch, split so that Alice's projector is out in front of
    everything Bob does.  This is where [PiA_Nuv] pays: the inner Π^A_u
    from [Kuv] walks out through L and Post and merges with the outer one. *)
Definition Suv (u v : nat) : Square (2 ^ 6) := PiA u × Nuv u v.

Lemma WF_Suv : forall u v, WF_Matrix (Suv u v).
Proof. intros u v; unfold Suv; auto with wf_db. Qed.
#[export] Hint Resolve WF_Suv : wf_db.

Lemma Auv_eq : forall u v, Auv u v = gCNOT_CA † × Suv u v × gCNOT_CA.
Proof.
  intros u v. unfold Auv, Suv, Nuv. rewrite Kuv_split.
  rewrite !Mmult_adjoint, !Mmult_assoc, ?adjoint_involutive, PiA_herm.
  rewrite <- (Mmult_assoc (Luv u v) (PiA u) gCNOT_CA), <- PiA_Luv.
  rewrite (Mmult_assoc (PiA u) (Luv u v) gCNOT_CA).
  rewrite <- (Mmult_assoc Post (PiA u)), <- PiA_Post.
  rewrite (Mmult_assoc (PiA u) Post).
  rewrite <- (Mmult_assoc ((Luv u v) †) (PiA u)), <- PiA_Luv_adj.
  rewrite (Mmult_assoc (PiA u) ((Luv u v) †)).
  rewrite <- (Mmult_assoc (PiA u) (PiA u)), PiA_idem.
  rewrite ?Mmult_assoc. reflexivity.
Qed.

Lemma Suv_herm : forall u v, (Suv u v) † = Suv u v.
Proof.
  intros u v; unfold Suv.
  rewrite Mmult_adjoint, PiA_herm, Nuv_herm, PiA_Nuv. reflexivity.
Qed.

Lemma Suv_idem : forall u v, Suv u v × Suv u v = Suv u v.
Proof.
  intros u v; unfold Suv. rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (Nuv u v) (PiA u) (Nuv u v)), <- PiA_Nuv.
  rewrite (Mmult_assoc (PiA u) (Nuv u v) (Nuv u v)), Nuv_idem.
  rewrite <- (Mmult_assoc (PiA u) (PiA u)), PiA_idem. reflexivity.
Qed.

(* ---- The four branches are pairwise orthogonal ----------------------- *)

(** [Luv_flip] with the two v's allowed to differ: the unitary layers still
    cancel, and what is left in the middle is [Π^B_v Π^B_v'] — which is
    [Π^B_v] when v = v' and Zero otherwise. *)
Lemma Luv_gen : forall u v v',
    Luv u v × (Luv u v') † = gZ_C v × ((PiB v × PiB v') × gZ_C v').
Proof.
  intros u v v'. unfold Luv.
  rewrite !Mmult_adjoint, !Mmult_assoc.
  rewrite <- (Mmult_assoc (gX_B u) ((gX_B u) †)), gX_B_flip.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc gCNOT_BT (gCNOT_BT †)), gCNOT_BT_flip.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite <- (Mmult_assoc gH_B (gH_B †)), gH_B_flip.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite PiB_herm, gZ_C_herm.
  rewrite <- (Mmult_assoc (PiB v) (PiB v') (gZ_C v')).
  reflexivity.
Qed.

Lemma Nuv_cross : forall u v v',
    PiB v × PiB v' = Zero -> Nuv u v × Nuv u v' = Zero.
Proof.
  intros u v v' Hz. unfold Nuv. rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (Luv u v) ((Luv u v') †) (Post × Luv u v')).
  rewrite Luv_gen, Hz.
  Msimpl. reflexivity.
Qed.

Lemma Suv_cross_u : forall u u' v v',
    PiA u × PiA u' = Zero -> Suv u v × Suv u' v' = Zero.
Proof.
  intros u u' v v' Hz. unfold Suv. rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (Nuv u v) (PiA u') (Nuv u' v')), <- PiA_Nuv.
  rewrite (Mmult_assoc (PiA u') (Nuv u v) (Nuv u' v')).
  rewrite <- (Mmult_assoc (PiA u) (PiA u')), Hz.
  rewrite Mmult_0_l. reflexivity.
Qed.

Lemma Suv_cross_v : forall u v v',
    PiB v × PiB v' = Zero -> Suv u v × Suv u v' = Zero.
Proof.
  intros u v v' Hz. unfold Suv. rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (Nuv u v) (PiA u) (Nuv u v')), <- PiA_Nuv.
  rewrite (Mmult_assoc (PiA u) (Nuv u v) (Nuv u v')).
  rewrite (Nuv_cross u v v' Hz).
  Msimpl. reflexivity.
Qed.

(* ---- The sum of the four branches is a projector --------------------- *)

Definition Ssum : Square (2 ^ 6) :=
  Suv 0 0 .+ (Suv 0 1 .+ (Suv 1 0 .+ Suv 1 1)).

Lemma WF_Ssum : WF_Matrix Ssum.
Proof. unfold Ssum; auto with wf_db. Qed.
#[export] Hint Resolve WF_Ssum : wf_db.

Lemma Ssum_herm : Ssum † = Ssum.
Proof. unfold Ssum. rewrite !Mplus_adjoint, !Suv_herm. reflexivity. Qed.

Lemma Ssum_idem : Ssum × Ssum = Ssum.
Proof.
  unfold Ssum.
  rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r.
  rewrite !Suv_idem.
  rewrite (Suv_cross_v 0 0 1 PiB_01), (Suv_cross_v 0 1 0 PiB_10),
          (Suv_cross_v 1 0 1 PiB_01), (Suv_cross_v 1 1 0 PiB_10).
  rewrite (Suv_cross_u 0 1 0 0 PiA_01), (Suv_cross_u 0 1 0 1 PiA_01),
          (Suv_cross_u 0 1 1 0 PiA_01), (Suv_cross_u 0 1 1 1 PiA_01),
          (Suv_cross_u 1 0 0 0 PiA_10), (Suv_cross_u 1 0 0 1 PiA_10),
          (Suv_cross_u 1 0 1 0 PiA_10), (Suv_cross_u 1 0 1 1 PiA_10).
  rewrite ?Mplus_0_l, ?Mplus_0_r.
  reflexivity.
Qed.

Lemma Asum_eq :
  Auv 0 0 .+ (Auv 0 1 .+ (Auv 1 0 .+ Auv 1 1))
  = gCNOT_CA † × Ssum × gCNOT_CA.
Proof.
  rewrite !Auv_eq. unfold Ssum.
  rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r. reflexivity.
Qed.

(* ---- Completeness ---------------------------------------------------- *)

(** The one fact of this case study that is about the PROTOCOL rather than
    about operator algebra: the three pre-shared Bell pairs lie below the
    sum of the four branch pre-effects.  The counterpart of
    [BellComplete.bell_completeness] and [SwapComplete.swap_completeness].

    Proof plan, and why it cannot copy either of those.  There the whole
    branch operator factored as U† S U for ONE unitary U, so the argument
    was: S is a projector, U† S U is a projector, it fixes the input, done.
    Here Bob's X correction sits between the two measurements and depends
    on the first outcome, so there is no such U.  What replaces it:

      Write  L(u,v) := Z_C^v · Π^B_v · H_B · CNOT[B,T] · X_B^u  — everything
      that touches qubits 1..5 — so that  K(u,v) = L(u,v) · Π^A_u · CNOT[C,A].

      1. Π^A_u sits on qubit 0 and L(u,v) on qubits 1..5, so they commute
         ([PiA_gX_B], [PiA_gH_B], [PiA_PiB], [PiA_gZ_C], [PiA_gCNOT_BT], all
         proved above).  Hence
             A(u,v) = CNOT[C,A]† · (Π^A_u · N(u,v)) · CNOT[C,A],
         with N(u,v) := L(u,v)† · Post · L(u,v).
      2. N(u,v) is a projector.  This is the step that is NOT obvious, since
         L(u,v) is not unitary — it contains Π^B_v.  Two cancellations do it:
             L L† = Z Π^B H C X X† C† H† Π^B Z† = Z Π^B Z† = Π^B
         (the unitary layers cancel, then Z commutes past Π^B), and
             L† Π^B = L†
         (Π^B is already leftmost inside L, and is idempotent).  Therefore
             N² = L† Post (L L†) Post L = L† Π^B Post Post L = L† Post L = N,
         using that Post touches qubits 2..5 and Π^B qubit 1, so they commute.
      3. So each A(u,v) is a projector, and the four are pairwise orthogonal:
         different u by [PiA_01]/[PiA_10]; same u, different v by
         [Pi_01]/[Pi_10] carried through the conjugation.  The sum is a
         projector.
      4. The sum fixes Psi0.  Writing φ := CNOT[C,A] Psi0 and splitting on A
         as φ = ∣0⟩⊗φ₀ + ∣1⟩⊗φ₁, the step that makes this cheap is that
         X_B^u φ_u does NOT depend on u — u flips ∣u⊕c⟩_B back to ∣c⟩_B — so
         both branches reduce to the same vector and the identity is checked
         once, not four times.
      4. [BellComplete.outer_le_proj], as in the other two files. *)
Lemma Psi0_inner : Psi0 † × Psi0 = I 1.
Proof.
  unfold Psi0. restore_dims.
  rewrite !kron_adjoint, !kron_mixed_product, !BellComplete.EPR_inner.
  rewrite !id_kron. reflexivity.
Qed.

Lemma Psi0_norm : ⟨ Psi0 , Psi0 ⟩ = C1.
Proof. unfold inner_product. rewrite Psi0_inner. lca. Qed.

Lemma gCNOT_CA_flip : gCNOT_CA × gCNOT_CA † = I (2 ^ 6).
Proof. destruct gCNOT_CA_unitary as [W H0]; apply Minv_flip; auto with wf_db. Qed.

(** The last step: the sum of the four branch pre-effects FIXES the input.

    The route.  Each [S(u,v)] is [Π^A_u · L(u,v)† · Post · L(u,v)], and Alice's
    projector is the only thing touching qubit A.  Summing over Bob's outcome v
    turns the Z frame into the single projector [G] on qubits 1..5, so

        Σ_v N(u,v) = Wop(u)† · (I₂ ⊗ G) · Wop(u),

    with [Wop u] everything Bob applies.  Since [Π^A_0 .+ Π^A_1 = I] and
    [Π^A_u] commutes with all of Bob's operators, the goal drops to, for
    u = 0 and u = 1,

        (I₂ ⊗ G) · (Wop u · Π^A_u · φ) = Wop u · Π^A_u · φ,   φ := CNOT[C,A]·Psi0,

    a five-qubit statement.  And there Alice's projector makes φ a product:
    [Π^A_u φ = ½ · ∣u⟩ ⊗ (∣u⟩_B ⊗ Blk₀ .+ ∣ū⟩_B ⊗ Blk₁)], so Bob's [X^u]
    returns qubit B to ∣c⟩ either way and the two branches become the same
    vector.  After CNOT[B,T] and H_B the block sits in the range of [G]:
    the two halves are the Choi vector and its Z frame ([L0], [L1]). *)
(* ---- Reduction 1: the four branches, regrouped along Bob ------------- *)

(** Everything Bob applies between the two measurements, as one unitary.
    [Luv u v] is then [gZ_C v · Π^B_v · Wop u].  Summing the branch
    projector over v collapses the Z frame into [G], which lives on
    qubits 1..5 only — and that is what lets qubit A be split off. *)
Definition Wop (u : nat) : Square (2 ^ 6) := gH_B × (gCNOT_BT × gX_B u).

Lemma WF_Wop : forall u, WF_Matrix (Wop u).
Proof. intros u; unfold Wop; auto with wf_db. Qed.
#[local] Hint Resolve WF_Wop : wf_db.

Definition Zpw (v : nat) : Square (2 ^ 4) :=
  if Nat.eqb v 1%nat then Zblk else I (2 ^ 4).

Lemma WF_Zpw : forall v, WF_Matrix (Zpw v).
Proof. intros v; unfold Zpw; destruct (Nat.eqb v 1%nat); auto with wf_db. Qed.
#[local] Hint Resolve WF_Zpw : wf_db.

Lemma Frame_conj : forall v, Zpw v × CNOTChoi × Zpw v = Frame v.
Proof.
  intros v; unfold Zpw, Frame; destruct (Nat.eqb v 1%nat).
  - rewrite Zblk_herm. reflexivity.
  - rewrite Mmult_1_l, Mmult_1_r by auto with wf_db. reflexivity.
Qed.

Lemma gZ_C_eq : forall v, gZ_C v = I 2 ⊗ (I 2 ⊗ Zpw v).
Proof.
  intros v; unfold gZ_C, Zpw; destruct (Nat.eqb v 1%nat).
  - unfold pad_u, pad; cbn [Nat.add Nat.sub Nat.leb Nat.pow].
    rewrite Zblk_eq.
    rewrite <- kron_assoc by auto with wf_db.
    rewrite id_kron.
    rewrite <- kron_assoc by auto with wf_db.
    reflexivity.
  - rewrite !id_kron. reflexivity.
Qed.

Lemma gZPostZ : forall v, gZ_C v × Post × gZ_C v = I 2 ⊗ (I 2 ⊗ Frame v).
Proof.
  intros v. rewrite gZ_C_eq, Post_split.
  restore_dims. rewrite !kron_mixed_product.
  Msimpl.
  rewrite Frame_conj. reflexivity.
Qed.

Lemma PiB_eq' : forall v, PiB v = I 2 ⊗ (Pi v ⊗ I (2 ^ 4)).
Proof.
  intros v. rewrite PiB_eq. rewrite kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma mid_eq : forall v,
    PiB v × (gZ_C v × Post × gZ_C v) × PiB v = I 2 ⊗ (Pi v ⊗ Frame v).
Proof.
  intros v. rewrite gZPostZ, PiB_eq'.
  restore_dims. rewrite !kron_mixed_product.
  Msimpl.
  rewrite Pi_same. reflexivity.
Qed.

Lemma Nuv_alt : forall u v,
    Nuv u v = (Wop u) † × (PiB v × (gZ_C v × Post × gZ_C v) × PiB v) × Wop u.
Proof.
  intros u v; unfold Nuv, Luv, Wop.
  rewrite !Mmult_adjoint, PiB_herm, gZ_C_herm.
  rewrite !Mmult_assoc. reflexivity.
Qed.

Lemma Nsum : forall u,
    Nuv u 0 .+ Nuv u 1 = (Wop u) † × (I 2 ⊗ G) × Wop u.
Proof.
  intros u. rewrite !Nuv_alt, !mid_eq.
  rewrite <- Mmult_plus_distr_r, <- Mmult_plus_distr_l.
  unfold G. restore_dims. rewrite <- kron_plus_distr_l. reflexivity.
Qed.

Lemma PiA_Wop : forall u a, PiA u × Wop a = Wop a × PiA u.
Proof.
  intros u a. unfold Wop.
  rewrite <- (Mmult_assoc (PiA u) gH_B), PiA_gH_B, (Mmult_assoc gH_B (PiA u)).
  rewrite <- (Mmult_assoc (PiA u) gCNOT_BT), PiA_gCNOT_BT,
          (Mmult_assoc gCNOT_BT (PiA u)).
  rewrite PiA_gX_B, !Mmult_assoc. reflexivity.
Qed.

Lemma PiA_Wop_adj : forall u a, PiA u × (Wop a) † = (Wop a) † × PiA u.
Proof.
  intros u a. assert (H := PiA_Wop u a).
  apply (f_equal (fun M : Square (2 ^ 6) => M †)) in H.
  rewrite !Mmult_adjoint, PiA_herm in H. symmetry; exact H.
Qed.

Lemma PiA_IG : forall u, PiA u × (I 2 ⊗ G) = (I 2 ⊗ G) × PiA u.
Proof.
  intros u. rewrite PiA_eq. restore_dims.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

Lemma PiA_sum : PiA 0 .+ PiA 1 = I (2 ^ 6).
Proof.
  rewrite !PiA_eq. restore_dims. rewrite <- kron_plus_distr_r.
  replace (Pi 0 .+ Pi 1) with (I 2) by (unfold Pi; cbn; lma').
  rewrite id_kron. reflexivity.
Qed.

Lemma Ssum_regroup :
  Ssum = PiA 0 × ((Wop 0) † × (I 2 ⊗ G) × Wop 0)
      .+ PiA 1 × ((Wop 1) † × (I 2 ⊗ G) × Wop 1).
Proof.
  unfold Ssum, Suv.
  rewrite <- !Nsum, !Mmult_plus_distr_l, !Mplus_assoc. reflexivity.
Qed.

(* ================================================================== *)
(* Step C: the input vector.                                          *)
(* ================================================================== *)

(** Everything below qubit A, in the grouping B ⊗ (C ⊗ (C' ⊗ (T,T'))). *)
Definition TX : Square 16 := I 4 ⊗ (σx ⊗ I 2).
Definition cB : Square 32 := ∣1⟩⟨1∣ ⊗ TX .+ ∣0⟩⟨0∣ ⊗ I 16.
Definition hB : Square 32 := hadamard ⊗ I 16.
Definition xB (x : Square 2) : Square 32 := x ⊗ I 16.

Lemma WF_TX : WF_Matrix TX.
Proof. unfold TX; auto with wf_db. Qed.
#[local] Hint Resolve WF_TX : wf_db.

Lemma WF_cB : WF_Matrix cB.
Proof. unfold cB; auto with wf_db. Qed.
#[local] Hint Resolve WF_cB : wf_db.

Lemma WF_hB : WF_Matrix hB.
Proof. unfold hB; auto with wf_db. Qed.
#[local] Hint Resolve WF_hB : wf_db.

Lemma gH_B_split : gH_B = I 2 ⊗ hB.
Proof.
  unfold gH_B, hB, pad_u, pad; cbn [Nat.add Nat.sub Nat.leb Nat.pow].
  rewrite kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma gX_B_split : gX_B 1 = I 2 ⊗ xB σx.
Proof.
  unfold gX_B, xB, pad_u, pad; cbn [Nat.add Nat.sub Nat.leb Nat.pow Nat.eqb].
  rewrite kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma gX_B_split0 : gX_B 0 = I 2 ⊗ xB (I 2).
Proof.
  unfold gX_B, xB; cbn [Nat.eqb].
  rewrite !id_kron. reflexivity.
Qed.

Lemma gCNOT_BT_split : gCNOT_BT = I 2 ⊗ cB.
Proof.
  unfold gCNOT_BT, cB, TX, pad_ctrl, pad;
    cbn [Nat.add Nat.sub Nat.leb Nat.ltb Nat.pow].
  rewrite kron_assoc by auto with wf_db.
  f_equal.
  rewrite kron_plus_distr_r. f_equal.
  - rewrite !kron_assoc by auto with wf_db. reflexivity.
  - rewrite !kron_assoc by auto with wf_db. rewrite !id_kron. reflexivity.
Qed.

(* ---- Small facts on one qubit ---------------------------------------- *)

Lemma H0v : hadamard × ∣0⟩ = / √ 2 .* ∣0⟩ .+ / √ 2 .* ∣1⟩.
Proof. lma'. Qed.

Lemma H1v : hadamard × ∣1⟩ = / √ 2 .* ∣0⟩ .+ (- / √ 2) .* ∣1⟩.
Proof. lma'. Qed.

Lemma Pi0_0 : Pi 0 × ∣0⟩ = ∣0⟩.       Proof. unfold Pi; cbn; lma'. Qed.
Lemma Pi0_1 : Pi 0 × ∣1⟩ = @Zero 2 1. Proof. unfold Pi; cbn; lma'. Qed.
Lemma Pi1_0 : Pi 1 × ∣0⟩ = @Zero 2 1. Proof. unfold Pi; cbn; lma'. Qed.
Lemma Pi1_1 : Pi 1 × ∣1⟩ = ∣1⟩.       Proof. unfold Pi; cbn; lma'. Qed.

Lemma Mplus4_swap : forall {m n} (a b c d : Matrix m n),
    a .+ b .+ (c .+ d) = a .+ c .+ (b .+ d).
Proof.
  intros m n a b c d. rewrite <- !Mplus_assoc.
  rewrite (Mplus_assoc _ _ a b c), (Mplus_comm _ _ b c),
          <- (Mplus_assoc _ _ a c b).
  reflexivity.
Qed.

Lemma kron_pm : forall (k : Vector 2) (c d : C) (z0 z1 : Vector 16),
    WF_Matrix k -> WF_Matrix z0 -> WF_Matrix z1 ->
    (c .* k) ⊗ z0 .+ (d .* k) ⊗ z1 = k ⊗ (c .* z0 .+ d .* z1).
Proof.
  intros k c d z0 z1 Hk H0 H1.
  rewrite !Mscale_kron_dist_l, <- !Mscale_kron_dist_r.
  rewrite <- kron_plus_distr_l. reflexivity.
Qed.

(* ---- Bob's Hadamard, and G, on a state split along B ----------------- *)

Lemma hB_apply : forall (z0 z1 : Vector 16),
    WF_Matrix z0 -> WF_Matrix z1 ->
    hB × (∣0⟩ ⊗ z0 .+ ∣1⟩ ⊗ z1)
    = ∣0⟩ ⊗ (/ √ 2 .* z0 .+ / √ 2 .* z1)
   .+ ∣1⟩ ⊗ (/ √ 2 .* z0 .+ (- / √ 2) .* z1).
Proof.
  intros z0 z1 H0 H1. unfold hB.
  rewrite Mmult_plus_distr_l. restore_dims. rewrite !kron_mixed_product.
  rewrite H0v, H1v. Msimpl.
  rewrite !kron_plus_distr_r.
  rewrite Mplus4_swap.
  rewrite !kron_pm by auto with wf_db.
  reflexivity.
Qed.

Lemma G_apply : forall (y0 y1 : Vector 16),
    WF_Matrix y0 -> WF_Matrix y1 ->
    G × (∣0⟩ ⊗ y0 .+ ∣1⟩ ⊗ y1)
    = ∣0⟩ ⊗ (Frame 0 × y0) .+ ∣1⟩ ⊗ (Frame 1 × y1).
Proof.
  intros y0 y1 Hy0 Hy1. unfold G.
  rewrite Mmult_plus_distr_r, !Mmult_plus_distr_l, !kron_mixed_product.
  rewrite Pi0_0, Pi0_1, Pi1_0, Pi1_1.
  rewrite !kron_0_l, Mplus_0_r, Mplus_0_l.
  reflexivity.
Qed.

(* ---- The reference block (C,C',T,T') --------------------------------- *)

Definition Blk0  : Vector 16 := (∣0⟩ ⊗ ∣0⟩) ⊗ ∣Φ+⟩.
Definition Blk1  : Vector 16 := (∣1⟩ ⊗ ∣1⟩) ⊗ ∣Φ+⟩.
Definition Blk1x : Vector 16 := (∣1⟩ ⊗ ∣1⟩) ⊗ ((σx ⊗ I 2) × ∣Φ+⟩).
Definition choiv : Vector 16 := CNOT_CT × (∣Φ+⟩ ⊗ ∣Φ+⟩).

Lemma WF_Blk0 : WF_Matrix Blk0.   Proof. unfold Blk0; auto with wf_db. Qed.
Lemma WF_Blk1 : WF_Matrix Blk1.   Proof. unfold Blk1; auto with wf_db. Qed.
Lemma WF_Blk1x : WF_Matrix Blk1x. Proof. unfold Blk1x; auto with wf_db. Qed.
Lemma WF_choiv : WF_Matrix choiv. Proof. unfold choiv; auto with wf_db. Qed.
#[local] Hint Resolve WF_Blk0 WF_Blk1 WF_Blk1x WF_choiv : wf_db.

(** CNOT[C,T] in the grouping (C,C') ⊗ (T,T'). *)
Lemma CNOT_CT_split :
  CNOT_CT = (∣1⟩⟨1∣ ⊗ I 2) ⊗ (σx ⊗ I 2) .+ (∣0⟩⟨0∣ ⊗ I 2) ⊗ (I 2 ⊗ I 2).
Proof.
  unfold CNOT_CT, pad_ctrl, pad;
    cbn [Nat.add Nat.sub Nat.leb Nat.ltb Nat.pow].
  rewrite kron_1_l by auto with wf_db.
  rewrite kron_plus_distr_r. f_equal.
  - rewrite !kron_assoc by auto with wf_db. reflexivity.
  - rewrite !kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma b1_EPR : (∣1⟩⟨1∣ ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (∣1⟩ ⊗ ∣1⟩).
Proof. lma'. Qed.

Lemma b0_EPR : (∣0⟩⟨0∣ ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (∣0⟩ ⊗ ∣0⟩).
Proof. lma'. Qed.

(** The two halves of Bob's Hadamard branch are the Choi vector, up to the
    Z frame Alice undoes. *)
Lemma L0 : / √ 2 .* Blk0 .+ / √ 2 .* Blk1x = choiv.
Proof.
  unfold choiv. rewrite CNOT_CT_split.
  rewrite Mmult_plus_distr_r. restore_dims.
  rewrite !kron_mixed_product, b1_EPR, b0_EPR.
  rewrite id_kron, Mmult_1_l by auto with wf_db.
  rewrite !Mscale_kron_dist_l.
  unfold Blk0, Blk1x. apply Mplus_comm.
Qed.

Lemma sz0 : σz × ∣0⟩ = ∣0⟩.            Proof. lma'. Qed.
Lemma sz1 : σz × ∣1⟩ = (- C1) .* ∣1⟩.  Proof. lma'. Qed.

Lemma Zblk_split : Zblk = (σz ⊗ I 2) ⊗ I 4.
Proof.
  rewrite Zblk_eq, kron_assoc by auto with wf_db.
  rewrite id_kron. reflexivity.
Qed.

Lemma Zblk_Blk0 : Zblk × Blk0 = Blk0.
Proof.
  unfold Blk0. rewrite Zblk_split. restore_dims.
  rewrite !kron_mixed_product, sz0. Msimpl. reflexivity.
Qed.

Lemma Zblk_Blk1x : Zblk × Blk1x = (- C1) .* Blk1x.
Proof.
  unfold Blk1x. rewrite Zblk_split. restore_dims.
  rewrite !kron_mixed_product, sz1. Msimpl.
  rewrite Mscale_kron_dist_l, Mscale_kron_dist_l. reflexivity.
Qed.

Lemma L1 : Zblk × choiv = / √ 2 .* Blk0 .+ (- / √ 2) .* Blk1x.
Proof.
  rewrite <- L0, Mmult_plus_distr_l, !Mscale_mult_dist_r.
  restore_dims. rewrite Zblk_Blk0, Zblk_Blk1x, Mscale_assoc.
  replace (/ √ 2 * (- C1))%C with (- / √ 2)%C by lca.
  reflexivity.
Qed.

Lemma EE_fix : (EPR ⊗ EPR) × (∣Φ+⟩ ⊗ ∣Φ+⟩) = ∣Φ+⟩ ⊗ ∣Φ+⟩.
Proof. restore_dims. rewrite kron_mixed_product, !EPR_fix. reflexivity. Qed.

Lemma CNOT_CT_undo : CNOT_CT † × choiv = ∣Φ+⟩ ⊗ ∣Φ+⟩.
Proof.
  unfold choiv. rewrite <- Mmult_assoc, CNOT_CT_flip.
  apply Mmult_1_l; auto with wf_db.
Qed.

Lemma choi_fix : CNOTChoi × choiv = choiv.
Proof.
  unfold CNOTChoi. rewrite !Mmult_assoc. restore_dims.
  rewrite CNOT_CT_undo. restore_dims. rewrite EE_fix. reflexivity.
Qed.

Lemma Zblk_sq : Zblk × Zblk = I (2 ^ 4).
Proof. rewrite <- Zblk_herm at 1. exact Zblk_flip. Qed.

Lemma Frame0_choi : Frame 0 × choiv = choiv.
Proof. unfold Frame; cbn [Nat.eqb]. exact choi_fix. Qed.

Lemma Frame1_choi : Frame 1 × (Zblk × choiv) = Zblk × choiv.
Proof.
  unfold Frame; cbn [Nat.eqb]. rewrite Zblk_herm, !Mmult_assoc.
  rewrite <- (Mmult_assoc Zblk Zblk choiv), Zblk_sq.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite choi_fix. reflexivity.
Qed.

Lemma G_fix_blk :
  G × (hB × (∣0⟩ ⊗ Blk0 .+ ∣1⟩ ⊗ Blk1x))
  = hB × (∣0⟩ ⊗ Blk0 .+ ∣1⟩ ⊗ Blk1x).
Proof.
  rewrite !hB_apply by auto with wf_db.
  rewrite L0, <- L1.
  rewrite G_apply by auto with wf_db.
  rewrite Frame0_choi, Frame1_choi. reflexivity.
Qed.

(* ---- Bob's CNOT and X, on the state split along B -------------------- *)

Lemma b1_0 : ∣1⟩⟨1∣ × ∣0⟩ = @Zero 2 1. Proof. lma'. Qed.
Lemma b1_1 : ∣1⟩⟨1∣ × ∣1⟩ = ∣1⟩.       Proof. lma'. Qed.
Lemma b0_0 : ∣0⟩⟨0∣ × ∣0⟩ = ∣0⟩.       Proof. lma'. Qed.
Lemma b0_1 : ∣0⟩⟨0∣ × ∣1⟩ = @Zero 2 1. Proof. lma'. Qed.

Lemma TX_Blk1 : TX × Blk1 = Blk1x.
Proof.
  unfold TX, Blk1, Blk1x. restore_dims.
  rewrite kron_mixed_product. Msimpl. reflexivity.
Qed.

Lemma cB_apply : cB × (∣0⟩ ⊗ Blk0 .+ ∣1⟩ ⊗ Blk1) = ∣0⟩ ⊗ Blk0 .+ ∣1⟩ ⊗ Blk1x.
Proof.
  unfold cB.
  rewrite Mmult_plus_distr_r, !Mmult_plus_distr_l. restore_dims.
  rewrite !kron_mixed_product, b1_0, b1_1, b0_0, b0_1.
  rewrite !kron_0_l, Mplus_0_l, Mplus_0_r.
  rewrite TX_Blk1. Msimpl. apply Mplus_comm.
Qed.

Definition wB (x : Square 2) : Square 32 := hB × (cB × xB x).

Lemma WF_wB : forall x, WF_Matrix x -> WF_Matrix (wB x).
Proof. intros x Hx; unfold wB, xB; auto with wf_db. Qed.

Lemma xB_apply : forall (x : Square 2) (a b : Vector 2),
    WF_Matrix x -> WF_Matrix a -> WF_Matrix b ->
    x × a = ∣0⟩ -> x × b = ∣1⟩ ->
    xB x × (a ⊗ Blk0 .+ b ⊗ Blk1) = ∣0⟩ ⊗ Blk0 .+ ∣1⟩ ⊗ Blk1.
Proof.
  intros x a b Hx Ha Hb Ha0 Hb1. unfold xB.
  rewrite Mmult_plus_distr_l. restore_dims.
  rewrite !kron_mixed_product. Msimpl.
  rewrite Ha0, Hb1. reflexivity.
Qed.

Lemma wB_fix : forall (x : Square 2) (a b : Vector 2),
    WF_Matrix x -> WF_Matrix a -> WF_Matrix b ->
    x × a = ∣0⟩ -> x × b = ∣1⟩ ->
    G × (wB x × (a ⊗ Blk0 .+ b ⊗ Blk1)) = wB x × (a ⊗ Blk0 .+ b ⊗ Blk1).
Proof.
  intros x a b Hx Ha Hb Ha0 Hb1. unfold wB.
  rewrite !Mmult_assoc, (xB_apply x a b) by assumption.
  rewrite cB_apply. apply G_fix_blk.
Qed.

(* ---- Alice's CNOT and measurement ------------------------------------ *)

Lemma Wop_split : forall (u : nat) (x : Square 2),
    gX_B u = I 2 ⊗ xB x -> Wop u = I 2 ⊗ wB x.
Proof.
  intros u x Hx. unfold Wop, wB.
  rewrite gH_B_split, gCNOT_BT_split, Hx. restore_dims.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

Lemma Psi0_split :
  Psi0 = / √ 2 .* (∣Φ+⟩ ⊗ (∣0⟩ ⊗ (∣0⟩ ⊗ ∣Φ+⟩))
               .+ ∣Φ+⟩ ⊗ (∣1⟩ ⊗ (∣1⟩ ⊗ ∣Φ+⟩))).
Proof. unfold Psi0. lma'. all: auto 20 with wf_db. Qed.

Lemma gCNOT_CA_split :
  gCNOT_CA = (σx ⊗ I 2) ⊗ (∣1⟩⟨1∣ ⊗ I 8) .+ (I 2 ⊗ I 2) ⊗ (∣0⟩⟨0∣ ⊗ I 8).
Proof.
  unfold gCNOT_CA, pad_ctrl, pad;
    cbn [Nat.add Nat.sub Nat.leb Nat.ltb Nat.pow].
  rewrite kron_1_l by auto with wf_db.
  rewrite kron_plus_distr_r. f_equal.
  - rewrite !kron_assoc by auto with wf_db. reflexivity.
  - rewrite !kron_assoc by auto with wf_db. reflexivity.
Qed.

Lemma PiA_eq2 : forall u, PiA u = (Pi u ⊗ I 2) ⊗ (I 2 ⊗ I 8).
Proof.
  intros u. rewrite PiA_eq, kron_assoc by auto with wf_db.
  rewrite !id_kron. reflexivity.
Qed.

Lemma PiA_CNOT : forall u,
    PiA u × gCNOT_CA
    = ((Pi u × σx) ⊗ I 2) ⊗ (∣1⟩⟨1∣ ⊗ I 8)
   .+ (Pi u ⊗ I 2) ⊗ (∣0⟩⟨0∣ ⊗ I 8).
Proof.
  intros u. rewrite PiA_eq2, gCNOT_CA_split.
  rewrite Mmult_plus_distr_l. restore_dims.
  rewrite !kron_mixed_product. Msimpl. reflexivity.
Qed.

Lemma W0_Blk0 : ∣0⟩ ⊗ (∣0⟩ ⊗ ∣Φ+⟩) = Blk0.
Proof. unfold Blk0. symmetry. apply kron_assoc; auto with wf_db. Qed.

Lemma W1_Blk1 : ∣1⟩ ⊗ (∣1⟩ ⊗ ∣Φ+⟩) = Blk1.
Proof. unfold Blk1. symmetry. apply kron_assoc; auto with wf_db. Qed.

Lemma chi1 : forall (u : nat) (a b : Vector 2),
    WF_Matrix a -> WF_Matrix b ->
    (Pi u ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (a ⊗ a) ->
    ((Pi u × σx) ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (a ⊗ b) ->
    PiA u × (gCNOT_CA × Psi0)
    = (/ √ 2 * / √ 2) .* (a ⊗ (a ⊗ Blk0 .+ b ⊗ Blk1)).
Proof.
  intros u a b Ha Hb H1 H2.
  rewrite <- Mmult_assoc, PiA_CNOT, Psi0_split.
  rewrite Mscale_mult_dist_r.
  rewrite Mmult_plus_distr_r, !Mmult_plus_distr_l.
  restore_dims. rewrite !kron_mixed_product.
  rewrite H1, H2, b1_0, b1_1, b0_0, b0_1.
  Msimpl.
  rewrite W0_Blk0, W1_Blk1.
  rewrite !Mscale_kron_dist_l.
  rewrite !kron_assoc by auto with wf_db.
  rewrite <- Mscale_plus_distr_r, Mscale_assoc.
  restore_dims.
  rewrite (Mplus_comm _ _ (a ⊗ (b ⊗ Blk1)) (a ⊗ (a ⊗ Blk0))).
  rewrite <- kron_plus_distr_l. reflexivity.
Qed.

(* ---- The input is fixed, branch by branch ---------------------------- *)

Lemma key : forall (u : nat) (a b : Vector 2) (x : Square 2),
    WF_Matrix a -> WF_Matrix b -> WF_Matrix x ->
    (Pi u ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (a ⊗ a) ->
    ((Pi u × σx) ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (a ⊗ b) ->
    gX_B u = I 2 ⊗ xB x ->
    x × a = ∣0⟩ -> x × b = ∣1⟩ ->
    (I 2 ⊗ G) × (Wop u × (PiA u × (gCNOT_CA × Psi0)))
    = Wop u × (PiA u × (gCNOT_CA × Psi0)).
Proof.
  intros u a b x Ha Hb Hx H1 H2 Hg Ha0 Hb1.
  rewrite (chi1 u a b) by assumption.
  rewrite (Wop_split u x) by assumption.
  rewrite !Mscale_mult_dist_r. restore_dims.
  rewrite kron_mixed_product. Msimpl. restore_dims.
  rewrite (wB_fix x a b) by assumption.
  reflexivity.
Qed.

Lemma b0x_EPR : ((∣0⟩⟨0∣ × σx) ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (∣0⟩ ⊗ ∣1⟩).
Proof. lma'. Qed.

Lemma b1x_EPR : ((∣1⟩⟨1∣ × σx) ⊗ I 2) × ∣Φ+⟩ = / √ 2 .* (∣1⟩ ⊗ ∣0⟩).
Proof. lma'. Qed.

Lemma sx0 : σx × ∣0⟩ = ∣1⟩. Proof. lma'. Qed.
Lemma sx1 : σx × ∣1⟩ = ∣0⟩. Proof. lma'. Qed.

Lemma key0 : (I 2 ⊗ G) × (Wop 0 × (PiA 0 × (gCNOT_CA × Psi0)))
           = Wop 0 × (PiA 0 × (gCNOT_CA × Psi0)).
Proof.
  apply (key 0 ∣0⟩ ∣1⟩ (I 2)); auto with wf_db.
  - unfold Pi; cbn [Nat.eqb]; exact b0_EPR.
  - unfold Pi; cbn [Nat.eqb]; exact b0x_EPR.
  - exact gX_B_split0.
  - apply Mmult_1_l; auto with wf_db.
  - apply Mmult_1_l; auto with wf_db.
Qed.

Lemma key1 : (I 2 ⊗ G) × (Wop 1 × (PiA 1 × (gCNOT_CA × Psi0)))
           = Wop 1 × (PiA 1 × (gCNOT_CA × Psi0)).
Proof.
  apply (key 1 ∣1⟩ ∣0⟩ σx); auto with wf_db.
  - unfold Pi; cbn [Nat.eqb]; exact b1_EPR.
  - unfold Pi; cbn [Nat.eqb]; exact b1x_EPR.
  - exact gX_B_split.
  - exact sx1.
  - exact sx0.
Qed.

(* ---- Reduction 2: the sum of the four branches fixes the input ------- *)

Lemma Wop_unitary : forall u, WF_Unitary (Wop u).
Proof.
  intros u; unfold Wop.
  apply Mmult_unitary; [ apply gH_B_unitary |].
  apply Mmult_unitary; [ apply gCNOT_BT_unitary | apply gX_B_unitary ].
Qed.

Lemma PiA_conj_comm : forall u,
    PiA u × ((Wop u) † × (I 2 ⊗ G) × Wop u)
  = (Wop u) † × (I 2 ⊗ G) × Wop u × PiA u.
Proof.
  intros u. rewrite !Mmult_assoc.
  rewrite <- (Mmult_assoc (PiA u) ((Wop u) †)), PiA_Wop_adj,
          (Mmult_assoc ((Wop u) †) (PiA u)).
  rewrite <- (Mmult_assoc (PiA u) (I 2 ⊗ G)), PiA_IG,
          (Mmult_assoc (I 2 ⊗ G) (PiA u)).
  rewrite PiA_Wop. reflexivity.
Qed.

(** One branch of [Ssum] acts on the input as [Π^A_u] does, given that the
    goal projector fixes what Bob's unitary makes of that branch. *)
Lemma branch_fix : forall (u : nat) (phi : Vector (2 ^ 6)),
    WF_Matrix phi ->
    (I 2 ⊗ G) × (Wop u × (PiA u × phi)) = Wop u × (PiA u × phi) ->
    PiA u × ((Wop u) † × (I 2 ⊗ G) × Wop u) × phi = PiA u × phi.
Proof.
  intros u phi Hwf Hkey.
  rewrite PiA_conj_comm, !Mmult_assoc. restore_dims. rewrite Hkey.
  rewrite <- (Mmult_assoc ((Wop u) †) (Wop u)), (proj2 (Wop_unitary u)).
  rewrite Mmult_1_l by auto with wf_db. reflexivity.
Qed.

Lemma Ssum_fix : Ssum × (gCNOT_CA × Psi0) = gCNOT_CA × Psi0.
Proof.
  assert (Hwf : WF_Matrix (gCNOT_CA × Psi0)) by auto with wf_db.
  rewrite Ssum_regroup, Mmult_plus_distr_r.
  rewrite (branch_fix 0 _ Hwf key0), (branch_fix 1 _ Hwf key1).
  rewrite <- Mmult_plus_distr_r, PiA_sum.
  apply Mmult_1_l; auto with wf_db.
Qed.

Theorem rcnot_completeness :
  Psi0 × Psi0 †
  ⊑ Auv 0 0 .+ (Auv 0 1 .+ (Auv 1 0 .+ Auv 1 1)).
Proof.
  rewrite Asum_eq.
  apply BellComplete.outer_le_proj; auto with wf_db.
  - rewrite !Mmult_adjoint, adjoint_involutive, Ssum_herm, !Mmult_assoc.
    reflexivity.
  - rewrite !Mmult_assoc.
    rewrite <- (Mmult_assoc gCNOT_CA (gCNOT_CA †)), gCNOT_CA_flip.
    rewrite Mmult_1_l by auto with wf_db.
    rewrite <- (Mmult_assoc Ssum Ssum), Ssum_idem. reflexivity.
  - rewrite !Mmult_assoc, Ssum_fix.
    rewrite <- Mmult_assoc, (proj2 gCNOT_CA_unitary).
    apply Mmult_1_l; auto with wf_db.
  - exact Psi0_norm.
Qed.
