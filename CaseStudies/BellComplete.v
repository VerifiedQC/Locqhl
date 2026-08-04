(** * Completeness of the Bell measurement — the one matrix fact behind the
      teleportation case study.

    This file is self-contained on purpose: it repeats (verbatim) the small
    matrix definitions of Teleportation.v — rho_psi, Pi, ZX, Corr, UA — so
    that the whole argument can be read, and checked, on its own.  Because
    the definitions are syntactically identical, [Teleportation.v] can close
    its [bell_completeness] fact with a one-line [exact].

    Statement.  With q := ψ ⊗ Φ+ the input state and
        A_{uv} := UA† (∣u⟩⟨u∣ ⊗ ∣v⟩⟨v∣ ⊗ Corr u v) UA
    the four branch pre-effects, we prove

        ρψ ⊗ Φ+Φ+†  ⊑  Σ_{u,v} A_{uv}.

    Proof shape (rank-1 ⊑ rank-4):
      1.  S := Σ ∣u⟩⟨u∣⊗∣v⟩⟨v∣⊗Corr u v is an orthogonal projector
          (blocks are orthogonal, Corr u v is a projector);
      2.  UA is unitary, so P := UA† S UA is an orthogonal projector;
      3.  teleportation identity: S (UA q) = UA q, hence P q = q;
      4.  a unit vector in the range of a projector satisfies q q† ⊑ P
          (Cauchy-Schwarz), and q q† = ρψ ⊗ Φ+Φ+†.  *)

From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad VecSet CauchySchwarz.

Local Open Scope matrix_scope.

(* The Löwner order, written exactly as in Locqhl.Core.Assertions, so that
   this file depends on QuantumLib ONLY.  Same body, so the two notions are
   definitionally equal and Teleportation.v's Fact closes by conversion. *)
Definition lowner {n} (M N : Square n) : Prop :=
  positive_semidefinite (N .+ (- C1) .* M)%M.

Notation "M ⊑ N" := (lowner M N) (at level 70).

(* ---- Generic: a unit vector in a projector's range ------------------ *)

Lemma outer_le_proj : forall n (P : Square n) (q : Vector n),
    WF_Matrix P -> WF_Matrix q ->
    P† = P -> P × P = P -> P × q = q -> ⟨ q, q ⟩ = C1 ->
    q × q† ⊑ P.
Proof.
  intros n P q WFP WFq Hh Hi Hr Hq.
  unfold lowner, positive_semidefinite.
  intros z WFz.
  rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
  rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
  set (a := (z† × P × z) 0%nat 0%nat).
  set (b := (z† × (q × q†) × z) 0%nat 0%nat).
  replace ((z† × P × z .+ - C1 .* (z† × (q × q†) × z)) 0%nat 0%nat)
    with (a + (- C1) * b)%C by reflexivity.
  replace (a + (- C1) * b)%C with (a - b)%C by lca.
  (* a is the squared norm of P z *)
  assert (HPz : z† × P × z = (P × z)† × (P × z)).
  { rewrite Mmult_adjoint, Hh. rewrite <- Hi at 1. rewrite !Mmult_assoc.
    reflexivity. }
  (* b is |⟨q,z⟩|², and ⟨q,z⟩ = ⟨q,Pz⟩ since q is in the range of P *)
  assert (Hbz : z† × (q × q†) × z = (q† × z)† × (q† × z)).
  { rewrite Mmult_adjoint, adjoint_involutive. rewrite !Mmult_assoc.
    reflexivity. }
  assert (HqP : q† × P = q†).
  { assert (E : (P × q)† = q†) by (rewrite Hr; reflexivity).
    rewrite Mmult_adjoint, Hh in E. exact E. }
  assert (Hc : (q† × z) 0%nat 0%nat = ⟨ q, P × z ⟩).
  { unfold inner_product. rewrite <- Mmult_assoc, HqP. reflexivity. }
  assert (Hb : b = (((q† × z) 0%nat 0%nat) ^* * ((q† × z) 0%nat 0%nat))%C).
  { unfold b. rewrite Hbz. unfold Mmult, adjoint. cbn. lca. }
  pose proof (Cauchy_Schwartz_ver1 q (P × z)) as CS.
  rewrite Hq in CS. cbn [fst] in CS. rewrite Rmult_1_l in CS.
  rewrite Hc in Hb.
  rewrite <- Cmod_sqr in Hb.
  assert (Ha : a = ⟨ P × z, P × z ⟩).
  { unfold a. rewrite HPz. reflexivity. }
  cbn. rewrite Hb, Ha. cbn.
  nra.
Qed.

(* ---- The teleportation matrices (verbatim from Teleportation.v) ----- *)

Definition UA : Square (2 ^ 3) := pad_u 3 0 hadamard × pad_ctrl 3 0 1 σx.
Definition Pi (b : nat) : Square 2 :=
  if Nat.eqb b 0%nat then ∣0⟩⟨0∣ else ∣1⟩⟨1∣.

Section Bell.

  Variable psi : Vector 2.
  Hypothesis WF_psi   : WF_Matrix psi.
  Hypothesis norm_psi : psi† × psi = I 1.

  Definition rho_psi : Square 2 := psi × psi†.
  Definition ZX (u v : nat) : Square 2 :=
    (if Nat.eqb u 1%nat then σz else I 2) × (if Nat.eqb v 1%nat then σx else I 2).
  Definition Corr (u v : nat) : Square 2 := (ZX u v)† × rho_psi × (ZX u v).

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

  Lemma WF_ZX : forall u v, WF_Matrix (ZX u v).
  Proof.
    intros u v; unfold ZX;
      destruct (Nat.eqb u 1%nat); destruct (Nat.eqb v 1%nat); auto with wf_db.
  Qed.
  #[local] Hint Resolve WF_ZX : wf_db.

  Lemma WF_Corr : forall u v, WF_Matrix (Corr u v).
  Proof. intros u v; unfold Corr; auto with wf_db. Qed.
  #[local] Hint Resolve WF_Corr : wf_db.

  Lemma ZX_unitary : forall u v, ZX u v × (ZX u v)† = I 2.
  Proof.
    intros u v; unfold ZX;
      destruct (Nat.eqb u 1%nat); destruct (Nat.eqb v 1%nat); lma'.
  Qed.

  Lemma Corr_herm : forall u v, (Corr u v)† = Corr u v.
  Proof.
    intros u v; unfold Corr.
    rewrite !Mmult_adjoint, adjoint_involutive, rho_herm, Mmult_assoc.
    reflexivity.
  Qed.

  Lemma Corr_idem : forall u v, Corr u v × Corr u v = Corr u v.
  Proof.
    intros u v; unfold Corr.
    rewrite !Mmult_assoc.
    rewrite <- (Mmult_assoc (ZX u v)).
    rewrite ZX_unitary.
    rewrite Mmult_1_l by auto with wf_db.
    rewrite <- (Mmult_assoc rho_psi), rho_idem.
    reflexivity.
  Qed.

  (* ---- The block projector S ------------------------------------- *)

  Definition Sblk : Square (2 ^ 3) :=
    ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 0 0
    .+ ∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 0 1
    .+ ∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 1 0
    .+ ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 1 1.

  Lemma WF_Sblk : WF_Matrix Sblk.
  Proof. unfold Sblk; restore_dims; auto 10 with wf_db. Qed.
  #[local] Hint Resolve WF_Sblk : wf_db.

  Lemma braket00 : ∣0⟩⟨0∣ × ∣0⟩⟨0∣ = ∣0⟩⟨0∣.  Proof. lma'. Qed.
  Lemma braket11 : ∣1⟩⟨1∣ × ∣1⟩⟨1∣ = ∣1⟩⟨1∣.  Proof. lma'. Qed.
  Lemma braket01 : ∣0⟩⟨0∣ × ∣1⟩⟨1∣ = Zero.    Proof. lma'. Qed.
  Lemma braket10 : ∣1⟩⟨1∣ × ∣0⟩⟨0∣ = Zero.    Proof. lma'. Qed.
  Lemma braket0_herm : ∣0⟩⟨0∣† = ∣0⟩⟨0∣.       Proof. lma'. Qed.
  Lemma braket1_herm : ∣1⟩⟨1∣† = ∣1⟩⟨1∣.       Proof. lma'. Qed.

  Lemma blk_mult : forall P Q C2 P' Q' C2' : Square 2,
      (P ⊗ Q ⊗ C2) × (P' ⊗ Q' ⊗ C2')
      = (P × P') ⊗ (Q × Q') ⊗ (C2 × C2').
  Proof. intros. restore_dims. rewrite !kron_mixed_product. reflexivity. Qed.

  Lemma Sblk_herm : Sblk† = Sblk.
  Proof.
    unfold Sblk.
    rewrite !Mplus_adjoint, !kron_adjoint, !braket0_herm, !braket1_herm,
            !Corr_herm.
    reflexivity.
  Qed.

  Lemma Sblk_idem : Sblk × Sblk = Sblk.
  Proof.
    unfold Sblk.
    rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r, !blk_mult.
    rewrite !braket00, !braket11, !braket01, !braket10, !Corr_idem.
    restore_dims.
    rewrite ?kron_0_l, ?kron_0_r.
    restore_dims.
    rewrite ?kron_0_l, ?kron_0_r.
    rewrite ?Mplus_0_l, ?Mplus_0_r.
    reflexivity.
  Qed.

  Lemma UA_unitary : WF_Unitary UA.
  Proof.
    apply Mmult_unitary.
    - apply pad_u_unitary; [lia | apply H_unitary].
    - apply pad_ctrl_unitary; [lia | lia | lia | apply σx_unitary].
  Qed.

  (* ---- The teleportation identity --------------------------------- *)

  Definition q3 : Vector (2 ^ 3) := psi ⊗ ∣Φ+⟩.

  Definition w3 : Vector (2 ^ 3) :=
    / 2 .* (∣0,0⟩ ⊗ ((ZX 0 0)† × psi)
        .+ ∣0,1⟩ ⊗ ((ZX 0 1)† × psi)
        .+ ∣1,0⟩ ⊗ ((ZX 1 0)† × psi)
        .+ ∣1,1⟩ ⊗ ((ZX 1 1)† × psi)).

  Lemma WF_UA : WF_Matrix UA.
  Proof. destruct UA_unitary; assumption. Qed.
  #[local] Hint Resolve WF_UA : wf_db.

  Lemma WF_q3 : WF_Matrix q3.
  Proof. unfold q3; auto with wf_db. Qed.
  #[local] Hint Resolve WF_q3 : wf_db.

  Lemma WF_w3 : WF_Matrix w3.
  Proof. unfold w3; restore_dims; auto 10 with wf_db. Qed.
  #[local] Hint Resolve WF_w3 : wf_db.

  (* The computation at the heart of teleportation: after CNOT and H, the
     input decomposes over the four measurement branches, the B register
     holding (ZX u v)† ψ in branch (u,v). *)
  Lemma UA_q3 : UA × q3 = w3.
  Proof.
    unfold UA, q3, w3, ZX, EPRpair.
    unfold pad_u, pad_ctrl, pad; cbn.
    apply mat_equiv_eq;
      [ restore_dims; auto 10 with wf_db .. | ].
    by_cell;
      unfold Mmult, kron, adjoint, scale, Mplus, big_sum,
             qubit0, qubit1, hadamard, σx, σz; cbn;
      C_field_simplify; try nonzero; try lca.
  Qed.

  Lemma ketbra00 : ∣0⟩⟨0∣ × ∣ 0 ⟩ = ∣ 0 ⟩.  Proof. lma'. Qed.
  Lemma ketbra01 : ∣0⟩⟨0∣ × ∣ 1 ⟩ = Zero.  Proof. lma'. Qed.
  Lemma ketbra10 : ∣1⟩⟨1∣ × ∣ 0 ⟩ = Zero.  Proof. lma'. Qed.
  Lemma ketbra11 : ∣1⟩⟨1∣ × ∣ 1 ⟩ = ∣ 1 ⟩.  Proof. lma'. Qed.

  Lemma blk_apply : forall (P Q C2 : Square 2) (x y v : Vector 2),
      (P ⊗ Q ⊗ C2) × (x ⊗ y ⊗ v) = (P × x) ⊗ (Q × y) ⊗ (C2 × v).
  Proof. intros. restore_dims. rewrite !kron_mixed_product. reflexivity. Qed.

  Lemma corr_fix : forall u v,
      Corr u v × ((ZX u v)† × psi) = (ZX u v)† × psi.
  Proof.
    intros u v. unfold Corr, rho_psi.
    rewrite !Mmult_assoc.
    rewrite <- (Mmult_assoc (ZX u v)).
    rewrite ZX_unitary.
    rewrite Mmult_1_l by auto with wf_db.
    rewrite norm_psi.
    rewrite Mmult_1_r by auto with wf_db.
    reflexivity.
  Qed.

  Lemma Sblk_w3 : Sblk × w3 = w3.
  Proof.
    unfold Sblk, w3.
    rewrite Mscale_mult_dist_r. f_equal.
    rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r.
    rewrite !blk_apply.
    rewrite !ketbra00, !ketbra01, !ketbra10, !ketbra11, !corr_fix.
    restore_dims.
    rewrite ?kron_0_l, ?kron_0_r.
    restore_dims.
    rewrite ?kron_0_l, ?kron_0_r.
    rewrite ?Mplus_0_l, ?Mplus_0_r.
    reflexivity.
  Qed.

  (* ---- Assembly ---------------------------------------------------- *)

  Lemma EPR_inner : ∣Φ+⟩† × ∣Φ+⟩ = I 1.
  Proof.
    unfold EPRpair.
    rewrite Mscale_adj, Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
    assert (Hc : ((/ √ 2) ^* = / √ 2)%C) by lca.
    rewrite Hc, Cinv_sqrt2_sqrt.
    apply mat_equiv_eq; [ restore_dims; auto 10 with wf_db .. | ].
    by_cell;
      unfold Mmult, kron, adjoint, scale, Mplus, big_sum, ket, qubit0, qubit1;
      cbn; lca.
  Qed.

  Lemma q3_norm : ⟨ q3 , q3 ⟩ = C1.
  Proof.
    unfold inner_product, q3.
    restore_dims. rewrite kron_adjoint. restore_dims.
    rewrite kron_mixed_product.
    rewrite norm_psi, EPR_inner.
    rewrite id_kron. reflexivity.
  Qed.

  Lemma UA_flip : UA × UA† = I (2 ^ 3).
  Proof.
    destruct UA_unitary as [WFU HU].
    apply Minv_flip; auto with wf_db.
  Qed.

  Theorem bell_completeness :
    rho_psi ⊗ (∣Φ+⟩ × ∣Φ+⟩†)
    ⊑ UA† × (∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 0 0) × UA
      .+ (UA† × (∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 0 1) × UA
      .+ (UA† × (∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 1 0) × UA
      .+ UA† × (∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 1 1) × UA)).
  Proof.
    destruct UA_unitary as [WFU HU].
    (* left side is the outer product of the input state *)
    assert (Hq3 : q3 × q3† = rho_psi ⊗ (∣Φ+⟩ × ∣Φ+⟩†)).
    { unfold q3, rho_psi. restore_dims. rewrite kron_adjoint. restore_dims.
      rewrite kron_mixed_product. reflexivity. }
    rewrite <- Hq3.
    (* right side is the projector UA† Sblk UA *)
    replace (UA† × (∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 0 0) × UA
             .+ (UA† × (∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 0 1) × UA
             .+ (UA† × (∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 1 0) × UA
             .+ UA† × (∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 1 1) × UA)))
      with (UA† × Sblk × UA).
    2:{ unfold Sblk.
        rewrite !Mmult_plus_distr_l, !Mmult_plus_distr_r.
        rewrite !Mplus_assoc. reflexivity. }
    apply outer_le_proj; auto with wf_db.
    - (* hermitian *)
      rewrite !Mmult_adjoint, adjoint_involutive, Sblk_herm.
      rewrite !Mmult_assoc. reflexivity.
    - (* idempotent *)
      rewrite !Mmult_assoc.
      rewrite <- (Mmult_assoc UA).
      rewrite UA_flip.
      rewrite Mmult_1_l by auto with wf_db.
      rewrite <- (Mmult_assoc Sblk), Sblk_idem.
      reflexivity.
    - (* q3 is in the range *)
      rewrite !Mmult_assoc.
      rewrite UA_q3, Sblk_w3, <- UA_q3.
      rewrite <- Mmult_assoc, HU.
      apply Mmult_1_l; auto with wf_db.
    - exact q3_norm.
  Qed.

End Bell.
