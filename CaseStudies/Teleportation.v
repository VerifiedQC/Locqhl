From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import Syntax Names QuantumActions Semantics Assertions WellFormed Rules SoundnessFacts Soundness.
From Locqhl.CaseStudies Require BellComplete.
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

(** The protocol, in one block.  A1 holds the input state ψ; (A2, B) hold
    the shared EPR pair; cz, cx are the two classical channels.

           Alice                          Bob
      ─────────────────────────    ─────────────────────────
      CNOT[A1,A2]; H[A1];          (idle)
      m1 <- Meas[A1];
      m2 <- Meas[A2]
      cz!m1 ; cx!m2                cz?i ; cx?j
      (done)                       if i = 1 then Z[B];
                                   if j = 1 then X[B]
*)
Definition tele : program :=
  ⟨ (* Alice *)
    <{ CNOT @ [A1; A2] ; H @ [A1] ;
       m1 <- Meas @ [A1] ; m2 <- Meas @ [A2] }>
    ⨾ [ cz ‼ e_var m1 ; cx ‼ e_var m2 ]
    ⨾ terminated ⟩
  ∥
  ⟨ (* Bob *)
    <{ skip }>
    ⨾ [ cz ⁇ i ; cx ⁇ j ]
    ⨾ ( <{ (if (b_eq (e_var i) (e_val 1%nat)) then Z @ [B] else skip) ;
           (if (b_eq (e_var j) (e_val 1%nat)) then X @ [B] else skip) }>
        ⨾ ε ⨾ terminated ) ⟩.

(** Named pieces of [tele], for stating the cut rows below.  [corr] is the
    conditional Pauli correction; everything is definitionally equal to the
    corresponding subterm of [tele]. *)
Definition corr (U : usym) (b : var) (q : qvar) : lblock :=
  <{ if (b_eq (e_var b) (e_val 1%nat)) then U @ [q] else skip }>.

Definition alice_pre : lblock :=
  <{ CNOT @ [A1; A2] ; H @ [A1] ; m1 <- Meas @ [A1] ; m2 <- Meas @ [A2] }>.

Definition bob_corr : lblock :=
  l_seq (corr Z i B) (corr X j B).

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

  (* Outside the outcome set T_M = {0,1} the operator is Zero — that is what
     [wf_interp] (the paper's finite family {M_m}, p.4) demands. *)
  Definition tele_mm (M : msym) (qs : list qvar) : measurement 3 :=
    match qs with
    | a :: nil => (0%nat :: 1%nat :: nil,
                   fun m => if Nat.eqb m 0%nat then pad_u 3 a ∣0⟩⟨0∣
                            else if Nat.eqb m 1%nat then pad_u 3 a ∣1⟩⟨1∣
                            else Zero)
    | _        => (0%nat :: nil,
                   fun m => if Nat.eqb m 0%nat then I (2 ^ 3) else Zero)
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

  (** Sig interprets every symbol by a well-formed operator and every
      measurement by a finite family — the side condition [soundness] needs. *)
  Lemma tele_wf_interp : wf_interp Sig.
  Proof.
    split; [| split; [| split]].
    - (* unitaries are WF *)
      intros U qs. unfold Sig, tele_uu; cbn [i_uu].
      destruct U as [|[|[|[|U]]]]; destruct qs as [|a [|b [|c qs]]]; cbn;
        auto with wf_db;
        try (apply (WF_pad_ctrl 3); auto with wf_db);
        try (apply (WF_pad_u 3); auto with wf_db).
    - (* measurement operators are WF *)
      intros M qs m. unfold Sig, tele_mm; cbn [i_mm].
      destruct qs as [|a [|b qs]]; cbn;
        repeat match goal with |- WF_Matrix (if ?x then _ else _) => destruct x end;
        auto with wf_db; try (apply (WF_pad_u 3); auto with wf_db).
    - (* Zero outside the outcome set *)
      intros M qs m Hm. unfold Sig, tele_mm in *; cbn [i_mm] in *.
      destruct qs as [|a [|b qs]]; cbn in *;
        repeat match goal with
               | |- (if ?x then _ else _) = _ => destruct x eqn:?
               end;
        try reflexivity;
        repeat match goal with
               | E : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in E; subst
               end;
        exfalso; apply Hm; cbn; auto.
    - (* the outcome set is a set *)
      intros M qs. unfold Sig, tele_mm; cbn [i_mm].
      destruct qs as [|a [|b qs]]; cbn;
        repeat constructor; cbn; intuition congruence.
  Qed.

  
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

  (* ---- Projector / kron toolbox ----------------------------------- *)
  Lemma braket0_herm : ∣0⟩⟨0∣† = ∣0⟩⟨0∣.  Proof. lma. Qed.
  Lemma braket1_herm : ∣1⟩⟨1∣† = ∣1⟩⟨1∣.  Proof. lma. Qed.
  Lemma braket0_idem : ∣0⟩⟨0∣ × ∣0⟩⟨0∣ = ∣0⟩⟨0∣.  Proof. lma. Qed.
  Lemma braket1_idem : ∣1⟩⟨1∣ × ∣1⟩⟨1∣ = ∣1⟩⟨1∣.  Proof. lma. Qed.

  Lemma WF_Corr : forall u v, WF_Matrix (Corr u v).
  Proof.
    intros u v. unfold Corr, ZX.
    destruct (Nat.eqb u 1%nat); destruct (Nat.eqb v 1%nat); auto with wf_db.
  Qed.
  #[local] Hint Resolve WF_Corr : wf_db.

  (* The raw shape that [cbn] gives the measured-branch pre-effect: the two
     measurement projectors, conjugated in, collapse onto the middle factor.
     P and Q are hermitian idempotents (the outcome projectors). *)
  Lemma chain_eq : forall P Q C2 : Square 2,
      WF_Matrix P -> WF_Matrix Q -> WF_Matrix C2 ->
      P† = P -> P × P = P -> Q† = Q -> Q × Q = Q ->
      adjoint (I 1 ⊗ (∣1⟩⟨1∣ ⊗ I 1 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 1 ⊗ I 2) ⊗ I 2)
      × (adjoint (I 1 ⊗ hadamard ⊗ I 4)
         × (adjoint (I 1 ⊗ P ⊗ I 4)
            × (adjoint (I 2 ⊗ Q ⊗ I 2) × (I 2 ⊗ I 2 ⊗ C2) × (I 2 ⊗ Q ⊗ I 2))
            × (I 1 ⊗ P ⊗ I 4))
         × (I 1 ⊗ hadamard ⊗ I 4))
      × (I 1 ⊗ (∣1⟩⟨1∣ ⊗ I 1 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 1 ⊗ I 2) ⊗ I 2)
      = UA† × (P ⊗ Q ⊗ C2) × UA.
  Proof.
    intros P Q C2 WFP WFQ WFC HPh HPi HQh HQi.
    (* normalize the two measurement pads to canonical 2x2x2 kron triples *)
    assert (EP : I 1 ⊗ P ⊗ I 4 = P ⊗ I 2 ⊗ I 2).
    { rewrite kron_1_l by auto with wf_db.
      replace (I 4) with (I 2 ⊗ I 2) by (rewrite id_kron; reflexivity).
      restore_dims. rewrite <- kron_assoc; auto with wf_db. }
    assert (Hmid :
      adjoint (I 1 ⊗ P ⊗ I 4)
      × (adjoint (I 2 ⊗ Q ⊗ I 2) × (I 2 ⊗ I 2 ⊗ C2) × (I 2 ⊗ Q ⊗ I 2))
      × (I 1 ⊗ P ⊗ I 4) = P ⊗ Q ⊗ C2).
    { rewrite EP. restore_dims.
      rewrite !kron_adjoint.
      rewrite !id_adjoint_eq, HPh, HQh.
      restore_dims.
      rewrite !kron_mixed_product.
      Msimpl.
      rewrite HQi, HPi.
      reflexivity. }
    rewrite Hmid.
    unfold UA, pad_u, pad_ctrl, pad; cbn.
    rewrite Mmult_adjoint.
    rewrite !Mmult_assoc.
    reflexivity.
  Qed.

  Lemma WF_ZX : forall u v, WF_Matrix (ZX u v).
  Proof.
    intros u v; unfold ZX;
      destruct (Nat.eqb u 1%nat); destruct (Nat.eqb v 1%nat); auto with wf_db.
  Qed.
  #[local] Hint Resolve WF_ZX : wf_db.

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

  Lemma is_effect_corr3 : forall u v, is_effect (dim := 3) (I 2 ⊗ I 2 ⊗ Corr u v).
  Proof.
    intros u v. apply herm_idem_effect.
    - auto with wf_db.
    - restore_dims. rewrite !kron_adjoint, !id_adjoint_eq, Corr_herm.
      reflexivity.
    - restore_dims. rewrite !kron_mixed_product.
      rewrite Mmult_1_l, Corr_idem by auto with wf_db. reflexivity.
  Qed.


  (* Merge a two-layer conjugation into one. *)
  Lemma conj_merge : forall n (A B M : Square n),
      A† × (B† × M × B) × A = (B × A)† × M × (B × A).
  Proof.
    intros n A B M. rewrite Mmult_adjoint. rewrite !Mmult_assoc. reflexivity.
  Qed.

  (* A global phase of -1 cancels in a sandwich. *)
  Lemma sandwich_neg : forall n (A M : Square n),
      ((- C1) .* A)† × M × ((- C1) .* A) = A† × M × A.
  Proof.
    intros n A M. rewrite Mscale_adj.
    rewrite !Mscale_mult_dist_l, Mscale_mult_dist_r.
    rewrite !Mscale_assoc.
    replace ((- C1) ^* * - C1)%C with C1 by lca.
    apply Mscale_1_l.
  Qed.

  (* How the residual correction transforms under the two Pauli fixes.
     The -1 from anticommuting σz past σx is absorbed by [sandwich_neg]. *)
  Lemma corr_Z : forall u w, Nat.eqb u 1%nat = true ->
      Corr u w = σz† × Corr 0 w × σz.
  Proof.
    intros u w Hu. unfold Corr, ZX. rewrite Hu. cbn [Nat.eqb].
    rewrite conj_merge.
    destruct (Nat.eqb w 1%nat).
    - replace ((I 2 × σx) × σz) with ((- C1) .* (σz × σx)) by lma'.
      rewrite sandwich_neg. reflexivity.
    - replace ((I 2 × I 2) × σz) with (σz × I 2) by lma'. reflexivity.
  Qed.

  Lemma corr_noZ : forall u w, Nat.eqb u 1%nat = false -> Corr u w = Corr 0 w.
  Proof.
    intros u w Hu. unfold Corr, ZX. rewrite Hu. cbn [Nat.eqb]. reflexivity.
  Qed.

  Lemma corr_X : forall w, Nat.eqb w 1%nat = true ->
      Corr 0 w = σx† × rho_psi × σx.
  Proof.
    intros w Hw. unfold Corr, ZX. rewrite Hw. cbn [Nat.eqb].
    replace (I 2 × σx) with σx by lma'. reflexivity.
  Qed.

  Lemma corr_noX : forall w, Nat.eqb w 1%nat = false -> Corr 0 w = rho_psi.
  Proof.
    intros w Hw. unfold Corr, ZX. rewrite Hw. cbn [Nat.eqb].
    replace (I 2 × I 2) with (I 2) by lma'.
    rewrite id_adjoint_eq.
    rewrite Mmult_1_l, Mmult_1_r by auto with wf_db. reflexivity.
  Qed.

  (* Conjugation by a single-qubit unitary at B, in the raw shape [cbn]
     produces for pad_u 3 B. *)
  Lemma padB_conj : forall M N : Square 2,
      WF_Matrix M -> WF_Matrix N ->
      adjoint (I 4 ⊗ M ⊗ I 1) × (I 2 ⊗ I 2 ⊗ N) × (I 4 ⊗ M ⊗ I 1)
      = I 2 ⊗ I 2 ⊗ (M† × N × M).
  Proof.
    intros M N WM WN.
    assert (E : I 4 ⊗ M ⊗ I 1 = I 2 ⊗ I 2 ⊗ M).
    { rewrite kron_1_r.
      replace (I 4) with (I 2 ⊗ I 2) by (rewrite id_kron; reflexivity).
      reflexivity. }
    rewrite E. restore_dims.
    rewrite !kron_adjoint, !id_adjoint_eq.
    restore_dims. rewrite !kron_mixed_product. Msimpl. reflexivity.
  Qed.

  (* ---- THE mathematical content of teleportation -------------------
     Completeness of the Bell measurement: the input effect ψ ⊗ Φ+ is
     bounded by the sum of the four branch pre-effects
        A_{uv} = UA† (|u⟩⟨u| ⊗ |v⟩⟨v| ⊗ Corr u v) UA.
     This is a statement about QuantumLib matrices only (UA, Corr, rho_psi
     are fixed matrix definitions above); everything else in this file is
     proved.  *)
  Fact bell_completeness :
    rho_psi ⊗ (∣Φ+⟩ × ∣Φ+⟩†)
    ⊑ UA† × (∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 0 0) × UA
      .+ (UA† × (∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 0 1) × UA
      .+ (UA† × (∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣ ⊗ Corr 1 0) × UA
      .+ UA† × (∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ ⊗ Corr 1 1) × UA)).
  Proof.
    (* proved, from first principles, in CaseStudies/BellComplete.v; the
       definitions there are verbatim copies, so this is pure conversion *)
    exact (BellComplete.bell_completeness psi WF_psi norm_psi).
  Qed.

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

  (* ---- Bob's conditional Pauli corrections ------------------------ *)
  (* After the Z-correction fires (or is skipped), the remaining correction
     depends only on j: the quantum part is Corr 0 (s j). *)
  Definition qCorrX (a : var) : qpred 3 :=
    q_op (fun vs => Some (I 2 ⊗ I 2 ⊗ Corr 0 (nth 0 vs 0%nat))) [e_var a].
  Definition Qmid : assertion 3 := mk_assertion chi (qCorrX j).

  Lemma bob_local :
    Sig ⊢ₗ {{ mk_assertion chi (qCorr i j) }} lseq d2 {{ mk_assertion chi qB }}.
  Proof.
    cbn [lseq d2].
    eapply rule_seq; [ apply rule_skip |].
    unfold bob_corr.
    eapply rule_seq with (Q2 := Qmid).
    - (* if i = 1 then Z[B] *)
      unfold corr. apply rule_if.
      + eapply rule_conseq with
          (Q := wp_unitary (i_uu Sig Z ([B])) Qmid) (R := Qmid).
        * split; [| split].
          { intros s Hs. cbn in Hs |- *.
            apply andb_true_iff in Hs as [Hchi _]; exact Hchi. }
          { intros s _ _. eexists. cbn. reflexivity. }
          { intros s M N Hs HM HN. cbn in Hs, HM, HN.
            inversion HM; inversion HN; subst.
            apply andb_true_iff in Hs as [_ Hg].
            rewrite (corr_Z _ _ Hg).
            rewrite padB_conj by auto with wf_db.
            apply lowner_refl. }
        * apply rule_unitary.
        * apply entails_refl.
        * intros s M HM; cbn in HM; inversion HM; subst; apply is_effect_corr3.
      + eapply rule_conseq with
          (Q := and_guard (mk_assertion chi (qCorr i j))
                          (b_eq (e_var i) (e_val 1%nat)) false)
          (R := and_guard (mk_assertion chi (qCorr i j))
                          (b_eq (e_var i) (e_val 1%nat)) false).
        * apply entails_refl.
        * apply rule_skip.
        * split; [| split].
          { intros s Hs. cbn in Hs |- *.
            apply andb_true_iff in Hs as [Hchi _]; exact Hchi. }
          { intros s _ _. eexists. cbn. reflexivity. }
          { intros s M N Hs HM HN. cbn in Hs, HM, HN.
            inversion HM; inversion HN; subst.
            apply andb_true_iff in Hs as [_ Hg].
            apply negb_true_iff in Hg.
            rewrite (corr_noZ _ _ Hg).
            apply lowner_refl. }
        * intros s M HM; cbn in HM; inversion HM; subst; apply is_effect_corr3.
    - (* if j = 1 then X[B] *)
      unfold corr. apply rule_if.
      + eapply rule_conseq with
          (Q := wp_unitary (i_uu Sig X ([B])) (mk_assertion chi qB))
          (R := mk_assertion chi qB).
        * split; [| split].
          { intros s Hs. cbn in Hs |- *.
            apply andb_true_iff in Hs as [Hchi _]; exact Hchi. }
          { intros s _ _. eexists. cbn. reflexivity. }
          { intros s M N Hs HM HN. cbn in Hs, HM, HN.
            inversion HM; inversion HN; subst.
            apply andb_true_iff in Hs as [_ Hg].
            rewrite (corr_X _ Hg).
            rewrite padB_conj by auto with wf_db.
            apply lowner_refl. }
        * apply rule_unitary.
        * apply entails_refl.
        * intros s M HM; cbn in HM; inversion HM; apply is_effect_base3.
      + eapply rule_conseq with
          (Q := and_guard Qmid (b_eq (e_var j) (e_val 1%nat)) false)
          (R := and_guard Qmid (b_eq (e_var j) (e_val 1%nat)) false).
        * apply entails_refl.
        * apply rule_skip.
        * split; [| split].
          { intros s Hs. cbn in Hs |- *.
            apply andb_true_iff in Hs as [Hchi _]; exact Hchi. }
          { intros s _ _. eexists. cbn. reflexivity. }
          { intros s M N Hs HM HN. cbn in Hs, HM, HN.
            inversion HM; inversion HN; subst.
            apply andb_true_iff in Hs as [_ Hg].
            apply negb_true_iff in Hg.
            rewrite (corr_noX _ Hg).
            apply lowner_refl. }
        * intros s M HM; cbn in HM; inversion HM; apply is_effect_base3.
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
          exact bob_local.
      + apply rule_comm_done; split; reflexivity.
      + apply rule_done; split; reflexivity.
  Qed.

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
      split; [| split].
      + intros s _; cbn; reflexivity.
      + intros s _ _; cbn; eexists; reflexivity.
      + intros s M N _ HM HN; cbn in HM, HN;
          inversion HM; inversion HN; subst.
        rewrite !chain_eq
          by (auto using braket0_herm, braket1_herm,
                         braket0_idem, braket1_idem with wf_db).
        rewrite Mplus_0_r.
        exact bell_completeness.
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
  Qed.

  (* Paper Theorem 5.1 — SEMANTIC correctness, via the soundness theorem
     applied to the derivation [tele_derivable]. *)
  Theorem teleportation : Sig ⊨ {{ tele_pre }} tele {{ tele_post }}.
  Proof. exact (soundness Sig tele_wf_interp _ _ _ tele_derivable). Qed.

End Spec.
