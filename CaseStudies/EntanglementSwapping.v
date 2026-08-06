From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import Syntax Names QuantumActions Semantics Assertions WellFormed Rules SoundnessFacts Soundness.
From Locqhl.CaseStudies Require Import SwapComplete.
Import ListNotations.
Open Scope proc_scope.

Definition A  : qvar := 0%nat.
Definition B  : qvar := 1%nat.
Definition CA : qvar := 2%nat.
Definition CB : qvar := 3%nat.
Definition m1 : var  := 0%nat.
Definition m2 : var  := 2%nat.
Definition i  : var  := 1%nat.
Definition j  : var  := 3%nat.
Definition cA : chan := 0%nat.
Definition cB : chan := 1%nat.

Definition CNOT : usym := 0%nat.
Definition H    : usym := 1%nat.
Definition Z    : usym := 2%nat.
Definition X    : usym := 3%nat.
Definition Meas : msym := 0%nat.

(** The protocol, in one block.  (A, C_A) and (B, C_B) hold the two
    pre-shared EPR pairs — no Bell preparation code, the pairs are given —
    and Charlie holds C_A and C_B; c_A, c_B are the two classical channels.
    Charlie's Bell measurement rewires the entanglement onto the remote
    pair (A, B), which is the one thing this protocol does that
    teleportation does not.

          Charlie                   Alice                Bob
      ─────────────────────    ─────────────────    ─────────────────
      CNOT[CA,CB]; H[CA];      (idle)               (idle)
      m1 <- Meas[CA];
      m2 <- Meas[CB]
      cA!m1 ; cB!m2            cA?i                 cB?j
      (done)                   if i = 1 then Z[A]   if j = 1 then X[B]
*)
Definition eswap : program :=
  ⟨ (* Charlie *)
    <{ CNOT @ [CA; CB] ; H @ [CA] ;
       m1 <- Meas @ [CA] ; m2 <- Meas @ [CB] }>
    ⨾ [ cA ‼ e_var m1 ; cB ‼ e_var m2 ]
    ⨾ terminated ⟩
  ∥
  ⟨ (* Alice *)
    <{ skip }>
    ⨾ [ cA ⁇ i ]
    ⨾ ( <{ if (b_eq (e_var i) (e_val 1%nat)) then Z @ [A] else skip }>
        ⨾ ε ⨾ terminated ) ⟩
  ∥
  ⟨ (* Bob *)
    <{ skip }>
    ⨾ [ cB ⁇ j ]
    ⨾ ( <{ if (b_eq (e_var j) (e_val 1%nat)) then X @ [B] else skip }>
        ⨾ ε ⨾ terminated ) ⟩.

(** Named pieces of [eswap], for stating the cut rows below.  [corr] is the
    conditional Pauli correction; everything is definitionally equal to the
    corresponding subterm of [eswap].  Unlike teleportation the two
    corrections sit at two DIFFERENT leaves — one bit each — so a leaf's
    tail carries a single [corr] rather than a sequence of two. *)
Definition corr (U : usym) (b : var) (q : qvar) : lblock :=
  <{ if (b_eq (e_var b) (e_val 1%nat)) then U @ [q] else skip }>.

Definition charlie_pre : lblock :=
  <{ CNOT @ [CA; CB] ; H @ [CA] ; m1 <- Meas @ [CA] ; m2 <- Meas @ [CB] }>.

Definition alice_corr : lblock := corr Z i A.

Definition bob_corr : lblock := corr X j B.

Definition d1 : lrow    := ⟨ charlie_pre ⟩ ∥ ⟨ l_skip ⟩ ∥ ⟨ l_skip ⟩.

Definition k1 : krow    := ⟨ [cA ‼ e_var m1; cB ‼ e_var m2] ⟩ ∥ ⟨ [cA ⁇ i] ⟩ ∥ ⟨ [cB ⁇ j] ⟩.

Definition t1 : program := ⟨ terminated ⟩
                           ∥ ⟨ alice_corr ⨾ ε ⨾ terminated ⟩
                           ∥ ⟨ bob_corr ⨾ ε ⨾ terminated ⟩.

Definition d2 : lrow    := ⟨ l_skip ⟩ ∥ ⟨ alice_corr ⟩ ∥ ⟨ bob_corr ⟩.

Definition k2 : krow    := ⟨ ε ⟩ ∥ ⟨ ε ⟩ ∥ ⟨ ε ⟩.

Definition t2 : program := ⟨ terminated ⟩ ∥ ⟨ terminated ⟩ ∥ ⟨ terminated ⟩.

(** The rows above are the ones [cut] actually produces, in both rounds:
    Charlie's leaf is already ↓ in the second round, and [cut] pads it. *)
Lemma eswap_cut : cut eswap = (d1, k1, t1).
Proof. reflexivity. Qed.

Lemma eswap_cut_tail : cut t1 = (d2, k2, t2).
Proof. reflexivity. Qed.


Local Open Scope matrix_scope.

(** ** The specification (paper Theorem 5.2) **************************

    The matrices are [SwapComplete]'s — [Psi0], the two pre-shared pairs
    EPR(A,C_A) ⊗ EPR(B,C_B) read in the qubit order A(0), B(1), C_A(2),
    C_B(3), and [EPR], the pair on AB the protocol creates.  The point of
    the postcondition is that it names two qubits that never met: no local
    block of [eswap] touches both A and B.  Charlie's two qubits are left
    free, hence the two I's. *)
Definition eswap_pre : assertion 4 :=
  {| classical_part := f_bexp b_true;
     quantum_part   := q_op (fun _ => Some (Psi0 × Psi0†)) nil |}.
Definition eswap_post : assertion 4 :=
  {| classical_part := f_bexp b_true;
     quantum_part   := q_op (fun _ => Some (EPR ⊗ I 2 ⊗ I 2)) nil |}.

Definition es_uu (U : usym) (qs : list qvar) : Square (2 ^ 4) :=
  match U, qs with
  | 0%nat, a :: b :: nil => pad_ctrl 4 a b σx      (* CNOT *)
  | 1%nat, a :: nil      => pad_u 4 a hadamard     (* H    *)
  | 2%nat, a :: nil      => pad_u 4 a σz           (* Z    *)
  | 3%nat, a :: nil      => pad_u 4 a σx           (* X    *)
  | _, _                 => I (2 ^ 4)
  end.

(* Outside the outcome set T_M = {0,1} the operator is Zero — that is what
   [wf_interp] (the paper's finite family {M_m}, p.4) demands. *)
Definition es_mm (M : msym) (qs : list qvar) : measurement 4 :=
  match qs with
  | a :: nil => (0%nat :: 1%nat :: nil,
                 fun m => if Nat.eqb m 0%nat then pad_u 4 a ∣0⟩⟨0∣
                          else if Nat.eqb m 1%nat then pad_u 4 a ∣1⟩⟨1∣
                          else Zero)
  | _        => (0%nat :: nil,
                 fun m => if Nat.eqb m 0%nat then I (2 ^ 4) else Zero)
  end.

Definition es_rl (R : relsym) (args : list val) : bool :=
  match R, args with
  | 0%nat, a :: b :: nil => Nat.eqb a b            (* r_eq *)
  | 1%nat, a :: b :: nil => Nat.ltb a b            (* r_lt *)
  | 2%nat, a :: b :: nil => Nat.ltb b a            (* r_gt *)
  | _, _                 => false
  end.

Definition Sig : interp 4 :=
  {| i_fn := fun _ _ => 0%nat;
     i_rl := es_rl;
     i_uu := es_uu;
     i_mm := es_mm |}.

Lemma HR    : standard_rels Sig.
Proof. repeat split; reflexivity. Qed.
Lemma HCNOT : i_uu Sig CNOT ([CA; CB]) = pad_ctrl 4 CA CB σx.
Proof. reflexivity. Qed.
Lemma HH    : i_uu Sig H ([CA]) = pad_u 4 CA hadamard.
Proof. reflexivity. Qed.
Lemma HZ    : i_uu Sig Z ([A]) = pad_u 4 A σz.
Proof. reflexivity. Qed.
Lemma HX    : i_uu Sig X ([B]) = pad_u 4 B σx.
Proof. reflexivity. Qed.

(** Every operator Sig hands out is a padding of a one- or two-qubit gate
    at the very qubits the primitive names (off-pattern it is I or Zero),
    which is what makes it LOCAL — the premise Par-Disjoint-MP needs. *)
Lemma es_padded : forall K qs, acts_on Sig K qs -> padded K qs.
Proof.
  intros K qs H; destruct H as [U qs | M qs m | q | q].
  - unfold Sig, es_uu; cbn [i_uu].
    destruct U as [|[|[|[|U]]]]; destruct qs as [|a [|b [|c qs]]]; cbn;
      constructor; auto with wf_db.
  - unfold Sig, es_mm; cbn [i_mm snd].
    destruct qs as [|a [|b qs]]; cbn;
      repeat match goal with
             | |- padded (if ?x then _ else _) _ => destruct x
             end;
      constructor; auto with wf_db.
  - constructor; auto with wf_db.
  - constructor; auto with wf_db.
Qed.

Lemma es_local_ops : local_ops Sig.
Proof.
  intros K1 qs1 K2 qs2 H1 H2 Hd.
  eapply padded_commute; eauto using es_padded.
Qed.

(** Sig interprets every symbol by a well-formed operator, every
    measurement by a finite family, and every primitive locally — the side
    condition [soundness] needs. *)
Lemma es_wf_interp : wf_interp Sig.
Proof.
  split; [| split; [| split; [| split]]].
  - (* unitaries are WF *)
    intros U qs. unfold Sig, es_uu; cbn [i_uu].
    destruct U as [|[|[|[|U]]]]; destruct qs as [|a [|b [|c qs]]]; cbn;
      auto with wf_db;
      try (apply (WF_pad_ctrl 4); auto with wf_db);
      try (apply (WF_pad_u 4); auto with wf_db).
  - (* measurement operators are WF *)
    intros M qs m. unfold Sig, es_mm; cbn [i_mm].
    destruct qs as [|a [|b qs]]; cbn;
      repeat match goal with |- WF_Matrix (if ?x then _ else _) => destruct x end;
      auto with wf_db; try (apply (WF_pad_u 4); auto with wf_db).
  - (* Zero outside the outcome set *)
    intros M qs m Hm. unfold Sig, es_mm in *; cbn [i_mm] in *.
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
    intros M qs. unfold Sig, es_mm; cbn [i_mm].
    destruct qs as [|a [|b qs]]; cbn;
      repeat constructor; cbn; intuition congruence.
  - (* the primitives are local *)
    exact es_local_ops.
Qed.

(** Definition 2.1 for [eswap]: the three parties share no variable or
    qubit; c_A and c_B each carry one send and one receive in two distinct
    leaves; both endpoints of each channel sit in the same phase; and that
    phase receives into i and j while reading only m1 and m2. *)
Lemma eswap_wf_program : wf_program eswap.
Proof.
  split; [| split; [| split]].
  - repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
  - intros c Hc; vm_compute in Hc.
    destruct Hc as [Hc | [Hc | [Hc | [Hc | []]]]]; subst c;
      repeat split; reflexivity.
  - intros n c Hc; destruct n as [| [| n]]; vm_compute in Hc |- *;
      try contradiction;
      destruct Hc as [Hc | [Hc | [Hc | [Hc | []]]]]; subst c; reflexivity.
  - intro n; destruct n as [| [| n]]; vm_compute; split;
      solve [ repeat constructor; cbn; intuition congruence
            | intros x Hx Hy; cbn in Hx, Hy; intuition congruence
            | constructor
            | intros x Hx Hy; contradiction ].
Qed.

(** ** The assertions ************************************************

    Three quantum predicates, in the order the derivation meets them
    backwards: the Pauli frame on AB carried by the two classical
    variables, the frame after Alice's Z has fired, and the goal. *)

Definition y1 : var := 4%nat.
Definition y2 : var := 5%nat.

Definition qCorr (a b : var) : qpred 4 :=
  q_op (fun vs => Some (Corr (nth 0 vs 0%nat) (nth 1 vs 0%nat) ⊗ I 2 ⊗ I 2))
       [e_var a; e_var b].

Definition qCorrX (a : var) : qpred 4 :=
  q_op (fun vs => Some (Corr 0 (nth 0 vs 0%nat) ⊗ I 2 ⊗ I 2)) [e_var a].

Definition qAB : qpred 4 := q_op (fun _ => Some (EPR ⊗ I 2 ⊗ I 2)) nil.

(* Shaped so that (Axiom-Meas) applies on the nose: its postcondition must
   be literally (phi /\ x = y), so after the two rendezvous substitutions
   this must read ((true /\ m1 = y1) /\ m2 = y2). *)
Definition chi : formula :=
  f_and (f_and (f_bexp b_true) (f_eq (e_var i) (e_var y1)))
        (f_eq (e_var j) (e_var y2)).

(* The one abbreviation Teleportation.v also uses: the assertion between
   the two corrections, after Alice's Z has fired. *)
Definition Qmid : assertion 4 := mk_assertion chi (qCorrX j).

Definition PostA : assertion 4 :=
  assertion_subst (assertion_subst (mk_assertion chi (qCorr i j))
                     j (e_var m2)) i (e_var m1).

Definition Q_m2 : assertion 4 :=
  mk_assertion (f_and (f_bexp b_true) (f_eq (e_var m1) (e_var y1)))
               (qCorr m1 m2).

Definition Q_m1 : assertion 4 :=
  mk_assertion (f_bexp b_true)
    (quantum_part (wp_meas Sig Meas ([CB]) y2
                     (assertion_subst Q_m2 m2 (e_var y2)))).

Definition charlie_wp : assertion 4 :=
  wp_unitary (i_uu Sig CNOT ([CA; CB]))
    (wp_unitary (i_uu Sig H ([CA]))
      (wp_meas Sig Meas ([CA]) y1 (assertion_subst Q_m1 m1 (e_var y1)))).

Definition at_uv (Q : assertion 4) (u v : val) : assertion 4 :=
  assertion_subst (assertion_subst Q y1 (e_val u)) y2 (e_val v).

Definition br (u v : val) : qpred 4 * formula :=
  (quantum_part (at_uv charlie_wp u v),
   classical_part (at_uv (mk_assertion chi qAB) u v)).

Definition four : list (qpred 4 * formula) :=
  [br 0%nat 0%nat; br 0%nat 1%nat; br 1%nat 0%nat; br 1%nat 1%nat].

(** ** Side conditions of the rules **********************************

    Every premise the derivation below cannot close by another rule is
    proved here, once, under a name — so that the derivation itself is
    nothing but rule applications.  The matrix content they appeal to
    ([corr_Z], [padA_conj], [chain_eq], [swap_completeness], …) is in
    SwapComplete.v. *)

(* -- the phases are matched (Comm-Select-MP) -- *)

Definition kA_mid : krow := ⟨ [cB ‼ e_var m2] ⟩ ∥ ⟨ [cA ⁇ i] ⟩ ∥ ⟨ [cB ⁇ j] ⟩.
Definition kA_res : krow := ⟨ [cB ‼ e_var m2] ⟩ ∥ ⟨ ε ⟩ ∥ ⟨ [cB ⁇ j] ⟩.
Definition kB_mid : krow := ⟨ ε ⟩ ∥ ⟨ ε ⟩ ∥ ⟨ [cB ⁇ j] ⟩.

Ltac wfphase :=
  split; [| split];
  [ intros c Hc; vm_compute in Hc;
    repeat (destruct Hc as [Hc | Hc]); try contradiction;
    rewrite <- Hc; vm_compute; repeat split; reflexivity
  | vm_compute; repeat constructor; cbn; intuition congruence
  | intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence ].

Lemma wf_k1     : wf_phase k1.     Proof. wfphase. Qed.
Lemma wf_kA_res : wf_phase kA_res. Proof. wfphase. Qed.

(* -- the rows are disjoint (Par-Disjoint-MP) -- *)

Ltac disjrow :=
  repeat constructor; repeat split;
  intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.

Lemma disj_d1 : lrow_disj d1.  Proof. disjrow. Qed.
Lemma disj_d2 : lrow_disj d2.  Proof. disjrow. Qed.

(* -- the tail is well formed too (Par-Comp-MP, second round): it owns no
      channel at all -- *)

Lemma t1_wf_program : wf_program t1.
Proof.
  split; [| split; [| split]].
  - repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
  - intros c Hc; vm_compute in Hc; contradiction.
  - intros n c Hc; destruct n as [| n]; vm_compute in Hc; contradiction.
  - intro n; destruct n as [| n]; vm_compute; split;
      [constructor | intros x Hx Hy; contradiction
       | constructor | intros x Hx Hy; contradiction].
Qed.

(* -- the assertions are formed: each denotes an effect at every store -- *)

Lemma wf_qCorr : wf_assertion Sig (mk_assertion chi (qCorr i j)).
Proof. intros s M HM; cbn in HM; inversion HM; subst; apply is_effect_corr. Qed.

Lemma wf_Qmid : wf_assertion Sig Qmid.
Proof. intros s M HM; cbn in HM; inversion HM; subst; apply is_effect_corr. Qed.

Lemma wf_qAB : wf_assertion Sig (mk_assertion chi qAB).
Proof. intros s M HM; cbn in HM; inversion HM; apply is_effect_epr. Qed.

Lemma wf_eswap_post : wf_assertion Sig eswap_post.
Proof. intros s M HM; cbn in HM; inversion HM; apply is_effect_epr. Qed.

(* -- the entailments the Conseq steps discharge --

   Each says how one classical guard moves the AB frame: with the guard
   true the correction fires and conjugates the frame, with it false the
   frame is already the one the postcondition wants. *)

Lemma entails_refl : forall dim (S0 : interp dim) (Q : assertion dim), Q ⊨[S0] Q.
Proof.
  intros dim S0 Q. repeat split; auto.
  intros s M N _ H1 H2. rewrite H1 in H2. inversion H2. apply lowner_refl.
Qed.

Ltac ent_guard :=
  split; [| split];
  [ intros s Hs; cbn in Hs |- *;
    apply andb_true_iff in Hs as [Hchi _]; exact Hchi
  | intros s _ _; eexists; cbn; reflexivity
  | intros s M N Hs HM HN; cbn in Hs, HM, HN;
    inversion HM; inversion HN; subst;
    apply andb_true_iff in Hs as [_ Hg] ].

Lemma ent_Z_fires :
  and_guard (mk_assertion chi (qCorr i j)) (b_eq (e_var i) (e_val 1%nat)) true
  ⊨[Sig] wp_unitary (i_uu Sig Z ([A])) Qmid.
Proof.
  ent_guard.
  rewrite (corr_Z _ _ Hg).
  rewrite padA_conj by auto with wf_db.
  apply lowner_refl.
Qed.

Lemma ent_Z_skipped :
  and_guard (mk_assertion chi (qCorr i j)) (b_eq (e_var i) (e_val 1%nat)) false ⊨[Sig] Qmid.
Proof.
  ent_guard.
  apply negb_true_iff in Hg.
  rewrite (corr_noZ _ _ Hg).
  apply lowner_refl.
Qed.

Lemma ent_X_fires :
  and_guard Qmid (b_eq (e_var j) (e_val 1%nat)) true
  ⊨[Sig] wp_unitary (i_uu Sig X ([B])) (mk_assertion chi qAB).
Proof.
  ent_guard.
  rewrite (corr_X _ Hg).
  rewrite padB_conj by auto with wf_db.
  apply lowner_refl.
Qed.

Lemma ent_X_skipped :
  and_guard Qmid (b_eq (e_var j) (e_val 1%nat)) false ⊨[Sig] mk_assertion chi qAB.
Proof.
  ent_guard.
  apply negb_true_iff in Hg.
  rewrite (corr_noX _ Hg).
  apply lowner_refl.
Qed.

(* -- the two entailments of the outermost Conseq --

   The first is the case study's mathematical content: the two pre-shared
   pairs are below the sum of the four branch pre-effects.  [chain_eq]
   puts each branch into the shape [swap_completeness] states. *)

Lemma ent_pre :
  eswap_pre ⊨[Sig] mk_assertion (f_bexp b_true) (qsum (map fst four)).
Proof.
  split; [| split].
  - intros s _; cbn; reflexivity.
  - intros s _ _; cbn; eexists; reflexivity.
  - intros s M N _ HM HN; cbn in HM, HN;
      inversion HM; inversion HN; subst.
    rewrite !chain_eq
      by (auto using BellComplete.braket0_herm, BellComplete.braket1_herm,
                     BellComplete.braket00, BellComplete.braket11 with wf_db).
    rewrite Mplus_0_r.
    exact swap_completeness.
Qed.

Lemma ent_post :
  mk_assertion (fdisj (map snd four)) qAB ⊨[Sig] eswap_post.
Proof.
  split; [| split].
  - intros s _; cbn; reflexivity.
  - intros s _ _; cbn; eexists; reflexivity.
  - intros s M N _ HM HN; cbn in HM, HN;
      inversion HM; inversion HN; subst; apply lowner_refl.
Qed.

(* -- the four branch guards are mutually exclusive (Branch-Accum) -- *)

Ltac excl1 :=
  intros s H1 H2; cbn in H1, H2;
  rewrite !andb_true_iff in H1, H2;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end;
  congruence.

Lemma four_exclusive : ForallOrdPairs (exclusive Sig) (map snd four).
Proof.
  cbn [map snd four br].
  repeat (apply FOP_cons;
          [ repeat (apply Forall_cons; [ excl1 |]); apply Forall_nil |]).
  apply FOP_nil.
Qed.

(** ** The derivation ************************************************

    From here on every step is a rule of the proof system, applied to the
    side conditions above.  Figure 10's five steps, in order. *)

(* Step I — Charlie's local block: two gates and two measurements, by
   Seq / Unitary / Meas backwards; Alice and Bob idle. *)
Lemma charlie_local : Sig ⊢ₗ {{ charlie_wp }} lseq d1 {{ PostA }}.
Proof.
  unfold charlie_wp, PostA. cbn [lseq].
  eapply rule_seq. 2:{ eapply rule_seq; apply rule_skip. }
  eapply rule_seq. 2:{
    eapply rule_seq. 2:{
      eapply rule_seq. 2:{
        apply rule_meas with (Q := Q_m2) (x := m2) (M := Meas)
                             (qs := ([CB])) (y := y2);
          vm_compute; intuition congruence. }
      apply rule_meas with (Q := Q_m1) (x := m1) (M := Meas)
                           (qs := ([CA])) (y := y1);
        vm_compute; intuition congruence. }
    apply rule_unitary. }
  apply rule_unitary.
Qed.

(* Step II — the communication phase: two rendezvous, each selected by
   naming its channel, then the phase is exhausted. *)
Lemma eswap_phase : Sig ⊢ₖ {{ PostA }} k1 {{ mk_assertion chi (qCorr i j) }}.
Proof.
  unfold PostA.
  apply rule_comm_select with (kmid := kA_mid) (k' := kA_res)
                              (c := cA) (e := e_var m1) (x := i).
  { exact wf_k1. }
  { unfold k1, kA_mid; eauto with locc. }
  { unfold kA_mid, kA_res; eauto with locc. }
  apply rule_comm_select with (kmid := kB_mid) (k' := k2)
                              (c := cB) (e := e_var m2) (x := j).
  { exact wf_kA_res. }
  { unfold kA_res, kB_mid; eauto with locc. }
  { unfold kB_mid, k2; eauto with locc. }
  apply rule_comm_done; repeat split; reflexivity.
Qed.

(* Step III — the two conditional corrections, by If / Unitary / Skip,
   each branch closed by Conseq against one of the four entailments. *)
Lemma corrections_local : Sig ⊢ₗ {{ mk_assertion chi (qCorr i j) }} lseq d2 {{ mk_assertion chi qAB }}.
Proof.
  cbn [lseq d2].
  eapply rule_seq; [ apply rule_skip |].
  unfold alice_corr, bob_corr, corr.
  eapply rule_seq with (Q2 := Qmid).
  - apply rule_if.
    + eapply rule_conseq;
        [ exact ent_Z_fires | apply rule_unitary
        | apply entails_refl | exact wf_Qmid ].
    + eapply rule_conseq;
        [ apply entails_refl | apply rule_skip
        | exact ent_Z_skipped | exact wf_Qmid ].
  - apply rule_if.
    + eapply rule_conseq;
        [ exact ent_X_fires | apply rule_unitary
        | apply entails_refl | exact wf_qAB ].
    + eapply rule_conseq;
        [ apply entails_refl | apply rule_skip
        | exact ent_X_skipped | exact wf_qAB ].
Qed.

(* Step IV — one branch of the whole program: Par-Comp-MP twice, the
   inner one for the tail, with Par-Disjoint-MP at each round. *)
Lemma eswap_branch : Sig ⊢ₚ {{ charlie_wp }} eswap {{ mk_assertion chi qAB }}.
Proof.
  apply rule_par_comp with (d := d1) (k := k1) (t := t1)
                           (Q1 := PostA) (Q2 := mk_assertion chi (qCorr i j)).
  - exact eswap_cut.
  - exact eswap_wf_program.
  - exact wf_qCorr.
  - exact wf_qAB.
  - apply rule_par_disjoint; [ exact disj_d1 | exact charlie_local ].
  - exact eswap_phase.
  - apply rule_par_comp with (d := d2) (k := k2) (t := t2)
                             (Q1 := mk_assertion chi qAB) (Q2 := mk_assertion chi qAB).
    + exact eswap_cut_tail.
    + exact t1_wf_program.
    + exact wf_qAB.
    + exact wf_qAB.
    + apply rule_par_disjoint; [ exact disj_d2 | exact corrections_local ].
    + apply rule_comm_done; repeat split; reflexivity.
    + apply rule_done; repeat split; reflexivity.
Qed.

(* Step V — the four branches, by Aux-Subst (y1, y2 are auxiliary: the
   program neither reads nor writes them) and Branch-Accum. *)
Lemma eswap_branch_at : forall u v : val,
    Sig ⊢ₚ {{ at_uv charlie_wp u v }} eswap {{ at_uv (mk_assertion chi qAB) u v }}.
Proof.
  intros u v. unfold at_uv.
  apply rule_aux_subst; [ vm_compute; intuition congruence |].
  apply rule_aux_subst; [ vm_compute; intuition congruence |].
  exact eswap_branch.
Qed.

Lemma eswap_accum :
  Sig ⊢ₚ {{ mk_assertion (f_bexp b_true) (qsum (map fst four)) }} eswap
        {{ mk_assertion (fdisj (map snd four)) qAB }}.
Proof.
  apply rule_branch_accum.
  - repeat (apply Forall_cons; [ apply eswap_branch_at |]). apply Forall_nil.
  - exact four_exclusive.
Qed.

(* Step VI — Conseq, against completeness of Charlie's Bell measurement. *)
Lemma eswap_derivable : Sig ⊢ₚ {{ eswap_pre }} eswap {{ eswap_post }}.
Proof.
  eapply rule_conseq_d;
    [ exact ent_pre | exact eswap_accum | exact ent_post | exact wf_eswap_post ].
Qed.

(** Paper Theorem 5.2 (correctness of entanglement swapping) — the
    counterpart of [Teleportation.teleportation]: SEMANTIC correctness, via
    the soundness theorem applied to the derivation [eswap_derivable]. *)
Theorem entanglement_swapping : Sig ⊨ {{ eswap_pre }} eswap {{ eswap_post }}.
Proof. exact (soundness Sig es_wf_interp _ _ _ eswap_derivable). Qed.
