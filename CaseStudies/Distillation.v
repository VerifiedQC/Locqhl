(** * Bounded entanglement distillation — the program (paper §5.4 / B.4).

    Round [i] owns two pre-shared pairs: a KEEP pair (Alice's [Ak i], Bob's
    [Bk i]) and a TEST pair ([At i], [Bt i]).  Each party CNOTs keep into
    test, measures its own test half, exchanges the outcome, and accepts
    iff the two bits agree — but only the FIRST agreement counts, which is
    what the latches [da]/[db] are for.

    Unlike the three case studies already in the tree this one is parametric
    in the number of rounds, so its tail is a [Fixpoint] and the derivation
    will be an induction over rounds rather than a fixed number of
    [Par-Comp-MP] applications. **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From Locqhl.Core Require Import Syntax Names QuantumActions Semantics
                                Assertions WellFormed Rules SoundnessFacts Soundness.
Import ListNotations.

Local Open Scope com_scope.
Local Open Scope proc_scope.

(** Round [i] occupies the four ADJACENT qubits [4i .. 4i+3], laid out as
    (keep pair) ⊗ (test pair).  Adjacency is forced by the specification:
    Distillation.md's predicates read
    [NeqSub_(1..i-1) ⊗ Rej_(i..k-1) ⊗ Pass_k ⊗ I_(k+1..n)], so a round has
    to be one tensor factor of the global predicate.  Keep before test
    inside the block makes [I_control_i ⊗ Π_10(EPR_i'a, EPR_i'b)] literally
    [I 4 ⊗ Π₁₀], and the round's slice of the input [EPR ⊗ EPR]. *)
Definition Ak (i : nat) : qvar := 4 * i.       (* Alice, keep *)
Definition Bk (i : nat) : qvar := 4 * i + 1.   (* Bob,   keep *)
Definition At (i : nat) : qvar := 4 * i + 2.   (* Alice, test *)
Definition Bt (i : nat) : qvar := 4 * i + 3.   (* Bob,   test *)

Definition chA (i : nat) : chan := 2 * i.      (* Alice → Bob *)
Definition chB (i : nat) : chan := 2 * i + 1.  (* Bob → Alice *)

(** [ia]/[ib] are 1-based — round [i], counted from 0, records [i+1] — so
    that the initial 0 is the sentinel "no round has accepted yet", exactly
    as Distillation.md writes it. *)
Definition ia : var := 0.   Definition ib : var := 5.
Definition da : var := 1.   Definition db : var := 6.
Definition oa : var := 2.   Definition ob : var := 7.
Definition ma : var := 3.   Definition mb : var := 8.
Definition x  : var := 4.   Definition y  : var := 9.

Definition CNOT : usym := 0.
Definition Meas : msym := 0.

(** The protocol.  Round 0 is the head of [distill]; [alice]/[bob] are the
    tail, round [i] having just communicated and [r] rounds still to come.

           Alice                              Bob
      ─────────────────────────────   ─────────────────────────────
      ia, da, oa := 0;                ib, db, ob := 0;
      CNOT[Ak 0, At 0];               CNOT[Bk 0, Bt 0];
      ma <- Meas[At 0]                mb <- Meas[Bt 0]
      chA 0!ma □ chB 0?x              chB 0!mb □ chA 0?y
      accept(0);                      accept(0);
      CNOT[Ak 1, At 1];               CNOT[Bk 1, Bt 1];
      ma <- Meas[At 1]                mb <- Meas[Bt 1]
      chA 1!ma □ chB 1?x              chB 1!mb □ chA 1?y
              ⋮                                ⋮
      accept(n)                       accept(n)

    A process is [L₀ ; K₀ ; L₁ ; K₁ ; … ; L_r ; K_r ; L_{r+1}], so round
    [i]'s accept test does NOT sit in round [i]'s own phase — it opens the
    local block of round [i+1].  That is Distillation.md's

        program equal to  (IF_A(i-1)) ; CNOT_A ; Meas_A ; …

    Round 0 sits outside the recursion.  Not only for readability: a
    top-level [match n with 0 => …] would leave [cut (distill n)] stuck on
    a symbolic [n], and the induction over rounds needs it to reduce.  So
    [distill n] runs rounds [0 .. n], that is [n+1] attempts; there is no
    zero-round instance of the protocol to lose. *)

Fixpoint alice (i r : nat) : process :=
  match r with
  | 0 =>
      <{ if (b_and (b_eq (e_var ma) (e_var x)) (b_eq (e_var da) (e_val 0)))
         then (oa := (e_val 1) ; da := (e_val 1) ; ia := (e_val (S i)))
         else skip }>
      ⨾ ε ⨾ terminated
  | S r' =>
      <{ (if (b_and (b_eq (e_var ma) (e_var x)) (b_eq (e_var da) (e_val 0)))
          then (oa := (e_val 1) ; da := (e_val 1) ; ia := (e_val (S i)))
          else skip) ;
         CNOT @ [Ak (S i); At (S i)] ; ma <- Meas @ [At (S i)] }>
      ⨾ [ chA (S i) ‼ e_var ma ; chB (S i) ⁇ x ]
      ⨾ alice (S i) r'
  end.

Fixpoint bob (i r : nat) : process :=
  match r with
  | 0 =>
      <{ if (b_and (b_eq (e_var mb) (e_var y)) (b_eq (e_var db) (e_val 0)))
         then (ob := (e_val 1) ; db := (e_val 1) ; ib := (e_val (S i)))
         else skip }>
      ⨾ ε ⨾ terminated
  | S r' =>
      <{ (if (b_and (b_eq (e_var mb) (e_var y)) (b_eq (e_var db) (e_val 0)))
          then (ob := (e_val 1) ; db := (e_val 1) ; ib := (e_val (S i)))
          else skip) ;
         CNOT @ [Bk (S i); Bt (S i)] ; mb <- Meas @ [Bt (S i)] }>
      ⨾ [ chB (S i) ‼ e_var mb ; chA (S i) ⁇ y ]
      ⨾ bob (S i) r'
  end.

Definition distill (n : nat) : program :=
  ⟨ (* Alice *)
    <{ ia := (e_val 0) ; da := (e_val 0) ; oa := (e_val 0) ;
       CNOT @ [Ak 0; At 0] ; ma <- Meas @ [At 0] }>
    ⨾ [ chA 0 ‼ e_var ma ; chB 0 ⁇ x ]
    ⨾ alice 0 n ⟩
  ∥
  ⟨ (* Bob *)
    <{ ib := (e_val 0) ; db := (e_val 0) ; ob := (e_val 0) ;
       CNOT @ [Bk 0; Bt 0] ; mb <- Meas @ [Bt 0] }>
    ⨾ [ chB 0 ‼ e_var mb ; chA 0 ⁇ y ]
    ⨾ bob 0 n ⟩.

(** Named pieces of [distill], for stating the cut rows below.  [accept]
    is the guarded first-agreement test; everything is definitionally equal
    to the corresponding subterm of [distill]. *)
Definition accept_a (i : nat) : lblock :=
  <{ if (b_and (b_eq (e_var ma) (e_var x)) (b_eq (e_var da) (e_val 0)))
     then (oa := (e_val 1) ; da := (e_val 1) ; ia := (e_val (S i)))
     else skip }>.
Definition accept_b (i : nat) : lblock :=
  <{ if (b_and (b_eq (e_var mb) (e_var y)) (b_eq (e_var db) (e_val 0)))
     then (ob := (e_val 1) ; db := (e_val 1) ; ib := (e_val (S i)))
     else skip }>.

Definition head_a : lblock :=
  <{ ia := (e_val 0) ; da := (e_val 0) ; oa := (e_val 0) ;
     CNOT @ [Ak 0; At 0] ; ma <- Meas @ [At 0] }>.
Definition head_b : lblock :=
  <{ ib := (e_val 0) ; db := (e_val 0) ; ob := (e_val 0) ;
     CNOT @ [Bk 0; Bt 0] ; mb <- Meas @ [Bt 0] }>.

(** Round [j]'s probe: entangle keep into test, then measure the test half.
    The derivation treats the probe as a unit — it is the block the
    outcome variable is fresh for. *)
Definition probe_a (j : nat) : lblock :=
  <{ CNOT @ [Ak j; At j] ; ma <- Meas @ [At j] }>.
Definition probe_b (j : nat) : lblock :=
  <{ CNOT @ [Bk j; Bt j] ; mb <- Meas @ [Bt j] }>.

(* [l_seq] rather than [<{ _ ; _ }>]: inside the custom entry only an
   atomic constr parses, and [accept_a i] is an application.  Teleportation
   builds [bob_corr] the same way. *)
Definition mid_a (i : nat) : lblock := l_seq (accept_a i) (probe_a (S i)).
Definition mid_b (i : nat) : lblock := l_seq (accept_b i) (probe_b (S i)).

Definition dhead : lrow := ⟨ head_a ⟩ ∥ ⟨ head_b ⟩.
Definition khead : krow := ⟨ [ chA 0 ‼ e_var ma ; chB 0 ⁇ x ] ⟩
                         ∥ ⟨ [ chB 0 ‼ e_var mb ; chA 0 ⁇ y ] ⟩.

Definition dmid (i : nat) : lrow := ⟨ mid_a i ⟩ ∥ ⟨ mid_b i ⟩.
Definition kmid (i : nat) : krow :=
  ⟨ [ chA (S i) ‼ e_var ma ; chB (S i) ⁇ x ] ⟩
  ∥ ⟨ [ chB (S i) ‼ e_var mb ; chA (S i) ⁇ y ] ⟩.

Definition dlast (i : nat) : lrow := ⟨ accept_a i ⟩ ∥ ⟨ accept_b i ⟩.
Definition kempty : krow := ⟨ ε ⟩ ∥ ⟨ ε ⟩.
Definition tdone : program := ⟨ terminated ⟩ ∥ ⟨ terminated ⟩.

Definition tround (i r : nat) : program := ⟨ alice i r ⟩ ∥ ⟨ bob i r ⟩.

(** The three cuts, mirroring the induction: start, one step, base.  All
    three reduce with [n] and [r] symbolic — which is what the induction
    over rounds stands on.  These are Distillation.md's "phase local",
    "phase communication" and "phase tail". *)
Lemma cut_head : forall n, cut (distill n) = (dhead, khead, tround 0 n).
Proof. reflexivity. Qed.

Lemma cut_step : forall i r,
    cut (tround i (S r)) = (dmid i, kmid i, tround (S i) r).
Proof. reflexivity. Qed.

Lemma cut_base : forall i, cut (tround i 0) = (dlast i, kempty, tdone).
Proof. reflexivity. Qed.

Lemma tdone_terminated : prog_terminated tdone.
Proof. split; reflexivity. Qed.

(** ** The Bell-label predicates (paper §5.4.1) ************************ *)

From QuantumLib Require Import Matrix Quantum Pad.
(* Qualified, as Teleportation takes BellComplete: the matrix side repeats
   the predicates verbatim, so the two copies are convertible, and keeping
   it unimported keeps the names from colliding. *)
From Locqhl.CaseStudies Require DistillationComplete.

Local Open Scope matrix_scope.

Definition EPR : Square 4 := ∣Φ+⟩ × ∣Φ+⟩ †.

(** The paper states the one-round effects over the four Bell projectors

        Φ_xz(q,q') ≜ (I ⊗ X^x Z^z) EPR(q,q') (I ⊗ Z^z X^x),

    but summing a Bell label's PHASE index collapses the pair to a parity
    projector in the computational basis:

        Φ_x0 + Φ_x1  =  Ev  when x = 0,   Od  when x = 1.                (†)

    The parity form is what every rule in the derivation meets, because it
    is what a computational-basis measurement of the two test halves
    produces, so the predicates below are stated with [Ev]/[Od].

    (†) is the one place where the correspondence with §5.4.1 is not
    syntactic.  It is a two-qubit matrix identity, so it belongs in
    DistillationComplete.v with the rest of the matrix side; it is NOT
    proved yet, and until it is, the link between these predicates and the
    paper's Φ-sums rests on a hand check.  ([lma'] does not close it on its
    own: the entries carry [/√2 * /√2] and [lca] has no access to
    [√2 * √2 = 2].) *)
Definition Ev : Square 4 := ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣.
Definition Od : Square 4 := ∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣ .+ ∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣.

Lemma Ev_Od_I : Ev .+ Od = I 4.
Proof. unfold Ev, Od; lma'. Qed.

(** The four one-round effects, on a round's block (keep pair) ⊗ (test
    pair).  [Pass] is the bilateral test: the two pairs carry the SAME
    bit-flip label, i.e. the same parity.  The paper writes it
    [Σ_{x,z,z'} Φ_xz ⊗ Φ_xz'], which is [Σ_x (Σ_z Φ_xz) ⊗ (Σ_z' Φ_xz')] —
    the two parity blocks below.  [EqSub]/[NeqSub] split the round by the
    TEST pair's parity alone, so their keep factor is free. *)
Definition Pass   : Square 16 := Ev ⊗ Ev .+ Od ⊗ Od.
Definition Rej    : Square 16 := Ev ⊗ Od .+ Od ⊗ Ev.
Definition EqSub  : Square 16 := I 4 ⊗ Ev.
Definition NeqSub : Square 16 := I 4 ⊗ Od.

Lemma Pass_Rej_I : Pass .+ Rej = I 16.
Proof. unfold Pass, Rej, Ev, Od. lma'; auto 20 with wf_db. Qed.

Lemma EqSub_NeqSub_I : EqSub .+ NeqSub = I 16.
Proof. unfold EqSub, NeqSub, Ev, Od. lma'; auto 20 with wf_db. Qed.

(** ** The specification, for the run whose first accepting round is k ***

    [seg k n before mid] is the paper's three-segment predicate

        (⊗_{ℓ<k} before) ⊗ mid ⊗ (⊗_{ℓ>k} I_ℓ)

    on the [4(n+1)] qubits of [distill n].  Rounds before [k] carry
    [before], round [k] carries [mid], and the [n-k] rounds after it are
    free.  Matrix dimensions are phantom in QuantumLib, so [kron_n] over
    [Square 16] blocks needs no cast to land in [Square (2 ^ (4 * S n))];
    only the well-formedness obligations see the arithmetic. *)
(** Rounds [0 .. k-1] rejected, round [k] is the first to pass, and the
    [n-k] rounds after it are free.  [kron_n j A] is [A] tensored with
    itself [j] times, and [kron_n 0 A = I 1] — the paper's "empty tensor
    products read as the identity".  Matrix dimensions are phantom in
    QuantumLib, so no cast is needed to land in [Square (2 ^ (4 * S n))];
    only the well-formedness obligations see the arithmetic. *)
Definition pre_q (k n : nat) : Square (2 ^ (4 * S n)) :=
  kron_n k Rej ⊗ Pass ⊗ kron_n (n - k) (I 16).

Definition post_q (k n : nat) : Square (2 ^ (4 * S n)) :=
  kron_n k NeqSub ⊗ EqSub ⊗ kron_n (n - k) (I 16).

(** [Acc_k]: both parties have latched, both succeeded, and both recorded
    the same index.  The index is 1-based, so round [k] records [k+1]. *)
Definition Acc (k : nat) : formula :=
  f_and (f_and (f_and (f_eq (e_var da) (e_val 1%nat)) (f_eq (e_var db) (e_val 1%nat)))
               (f_and (f_eq (e_var oa) (e_val 1%nat)) (f_eq (e_var ob) (e_val 1%nat))))
        (f_and (f_eq (e_var ia) (e_val (S k))) (f_eq (e_var ib) (e_val (S k)))).

Definition distill_pre (k n : nat) : assertion (4 * S n) :=
  {| classical_part := f_bexp b_true;
     quantum_part   := q_op (fun _ => Some (pre_q k n)) nil |}.

Definition distill_post (k n : nat) : assertion (4 * S n) :=
  {| classical_part := Acc k;
     quantum_part   := q_op (fun _ => Some (post_q k n)) nil |}.

(** ** The interpretation ********************************************* *)

(** The protocol uses one gate and one measurement, at every round.  Off
    pattern the operator is the identity; [pad_ctrl]/[pad_u] already return
    [Zero] when an index is out of range, so nothing here needs a bound. *)
Definition d_uu (n : nat) (U : usym) (qs : list qvar)
  : Square (2 ^ (4 * S n)) :=
  match U, qs with
  | 0%nat, a :: b :: nil => pad_ctrl (4 * S n) a b σx     (* CNOT *)
  | _, _                 => I (2 ^ (4 * S n))
  end.

(* Outside the outcome set T_M = {0,1} the operator is Zero — what
   [wf_interp] (the paper's finite family {M_m}) demands. *)
Definition d_mm (n : nat) (M : msym) (qs : list qvar) : measurement (4 * S n) :=
  match qs with
  | a :: nil => (0%nat :: 1%nat :: nil,
                 fun m => if Nat.eqb m 0%nat then pad_u (4 * S n) a ∣0⟩⟨0∣
                          else if Nat.eqb m 1%nat then pad_u (4 * S n) a ∣1⟩⟨1∣
                          else Zero)
  | _        => (0%nat :: nil,
                 fun m => if Nat.eqb m 0%nat then I (2 ^ (4 * S n)) else Zero)
  end.

Definition d_rl (R : relsym) (args : list val) : bool :=
  match R, args with
  | 0%nat, a :: b :: nil => Nat.eqb a b            (* r_eq *)
  | 1%nat, a :: b :: nil => Nat.ltb a b            (* r_lt *)
  | 2%nat, a :: b :: nil => Nat.ltb b a            (* r_gt *)
  | _, _                 => false
  end.

Definition Sig (n : nat) : interp (4 * S n) :=
  {| i_fn := fun _ _ => 0%nat;
     i_rl := d_rl;
     i_uu := d_uu n;
     i_mm := d_mm n |}.

Lemma HR : forall n, standard_rels (Sig n).
Proof. intro n; repeat split; reflexivity. Qed.

Lemma HCNOT : forall n a b, i_uu (Sig n) CNOT ([a; b]) = pad_ctrl (4 * S n) a b σx.
Proof. reflexivity. Qed.

(** Every operator [Sig n] hands out is a padding of a one- or two-qubit
    gate at the very qubits the primitive names, which is what makes it
    LOCAL — the premise Par-Disjoint-MP needs.  The proofs are the same
    case splits as in the fixed-dimension case studies: the dimension is
    symbolic but never inspected. *)
Lemma d_padded : forall n K qs, acts_on (Sig n) K qs -> padded K qs.
Proof.
  intros n K qs H; destruct H as [U qs' | M qs' m | q | q].
  - unfold Sig, d_uu; cbn [i_uu].
    destruct U as [|U]; destruct qs' as [|a [|b [|c qs']]]; cbn;
      constructor; auto with wf_db.
  - unfold Sig, d_mm; cbn [i_mm snd].
    destruct qs' as [|a [|b qs']]; cbn;
      repeat match goal with
             | |- padded (if ?x then _ else _) _ => destruct x
             end;
      constructor; auto with wf_db.
  - constructor; auto with wf_db.
  - constructor; auto with wf_db.
Qed.

Lemma d_local_ops : forall n, local_ops (Sig n).
Proof.
  intros n K1 qs1 K2 qs2 H1 H2 Hd.
  eapply padded_commute; eauto using d_padded.
Qed.

Lemma d_wf_interp : forall n, wf_interp (Sig n).
Proof.
  intro n. split; [| split; [| split; [| split]]].
  - intros U qs. unfold Sig, d_uu; cbn [i_uu].
    destruct U as [|U]; destruct qs as [|a [|b [|c qs]]]; cbn;
      auto with wf_db;
      try (apply (WF_pad_ctrl (4 * S n)); auto with wf_db).
  - intros M qs m. unfold Sig, d_mm; cbn [i_mm].
    destruct qs as [|a [|b qs]]; cbn;
      repeat match goal with |- WF_Matrix (if ?x then _ else _) => destruct x end;
      auto with wf_db; try (apply (WF_pad_u (4 * S n)); auto with wf_db).
  - intros M qs m Hm. unfold Sig, d_mm in *; cbn [i_mm] in *.
    destruct qs as [|a [|b qs]]; cbn in *;
      repeat match goal with
             | |- (if ?x then _ else _) = _ => destruct x eqn:?
             end;
      try reflexivity;
      repeat match goal with
             | E : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in E; subst
             end;
      exfalso; apply Hm; cbn; auto.
  - intros M qs. unfold Sig, d_mm; cbn [i_mm].
    destruct qs as [|a [|b qs]]; cbn;
      repeat constructor; cbn; intuition congruence.
  - exact (d_local_ops n).
Qed.

(** ** Paper Theorem 5.4, the acceptance triple ***********************

    For a run whose FIRST accepting round is [k]: if the input sits where
    rounds [0..k-1] fail the bilateral test and round [k] passes it, then
    the protocol terminates with both parties latched on index [k+1], the
    already-rejected rounds in the NeqSub frame and round [k] in EqSub.

    This is the [acc] half of Theorem 5.4.  The [good] half replaces
    [Pass]/[EqSub] by [Good_k]/[Φ00] and is not stated yet.

    Nothing merges the [k]'s: the quantum postcondition depends on [k], so
    Branch-Accum — which needs one postcondition shared across the family —
    does not apply.  The paper does not merge them either; the k's meet
    only in the Werner-input evaluation, which is arithmetic, not a rule. *)
Theorem distillation_acc : forall (k n : nat), (k <= n)%nat ->
  Sig n ⊨ {{ distill_pre k n }} distill n {{ distill_post k n }}.
Admitted.

(** ** The three phases of the derivation ******************************

    [tround i r] begins with round [i]'s ACCEPT TEST — the test sits in the
    local block of phase [i+1], not phase [i].  So an invariant handed to
    [tround i _] has to say enough for the guard [ma = x /\ da = 0] to be
    decided, and the three regimes of Distillation.md differ exactly there:

      i < k   the guard is false (the outcomes disagreed), nothing latches
      i = k   the guard is true, both parties latch on index k+1
      i > k   [da] is already 1, so the guard is false whatever the bits

    Round [i]'s probe has already run when [tround i _] is entered, so
    round [i] has collapsed: rounds [0..i] carry the post-measurement
    frame, rounds [i+1..k-1] still carry the pre-effect [Rej], round [k]
    carries [Pass], and the rest are free. *)

Definition Zeros : formula :=
  f_and (f_and (f_and (f_eq (e_var da) (e_val 0%nat)) (f_eq (e_var db) (e_val 0%nat)))
               (f_and (f_eq (e_var oa) (e_val 0%nat)) (f_eq (e_var ob) (e_val 0%nat))))
        (f_and (f_eq (e_var ia) (e_val 0%nat)) (f_eq (e_var ib) (e_val 0%nat))).

Definition Disagree : formula :=
  f_and (f_not (f_eq (e_var ma) (e_var x))) (f_not (f_eq (e_var mb) (e_var y))).
Definition Agree : formula :=
  f_and (f_eq (e_var ma) (e_var x)) (f_eq (e_var mb) (e_var y)).

(** [j] rounds have been measured and rejected; rounds [j..k-1] are still
    to come and will reject; round [k] will pass.  [inv_q 0 k n] is
    [pre_q k n] up to the unit factor [kron_n 0 _ = I 1]. *)
Definition inv_q (j k n : nat) : Square (2 ^ (4 * S n)) :=
  kron_n j NeqSub ⊗ kron_n (k - j) Rej ⊗ Pass ⊗ kron_n (n - k) (I 16).

Definition inv_at (j k n : nat) : assertion (4 * S n) :=
  {| classical_part := f_and Zeros Disagree;
     quantum_part   := q_op (fun _ => Some (inv_q j k n)) nil |}.

Definition acc_at (k n : nat) : assertion (4 * S n) :=
  {| classical_part := f_and Zeros Agree;
     quantum_part   := q_op (fun _ => Some (post_q k n)) nil |}.

(** The three triples themselves — [phase_after], [phase_accept],
    [phase_reject] — stand at the END of the file: each needs the
    well-formedness, effect and guard machinery below, and Rocq wants a
    definition before its use. *)

(** ** Well-formedness of the program (Definition 2.1) *****************

    Four obligations, each an induction over the rounds.  The recurring
    shape: a leaf's k-th communication block is round [k]'s rendezvous pair
    when [k] is in range and empty otherwise, and every other footprint is
    a [flat_map] over the rounds. *)

Lemma comm_at_alice : forall r i k,
    comm_at (alice i r) k
    = if Nat.ltb k r then [ chA (S i + k) ‼ e_var ma ; chB (S i + k) ⁇ x ]
      else [].
Proof.
  induction r as [| r' IH]; intros i k.
  - destruct k; cbn [alice comm_at Nat.ltb Nat.leb]; reflexivity.
  - destruct k as [| k'].
    + cbn [alice comm_at Nat.ltb Nat.leb]. rewrite Nat.add_0_r. reflexivity.
    + cbn [alice comm_at Nat.ltb Nat.leb]. rewrite IH.
      replace (S i + S k')%nat with (S (S i) + k')%nat by lia.
      reflexivity.
Qed.

Lemma comm_at_bob : forall r i k,
    comm_at (bob i r) k
    = if Nat.ltb k r then [ chB (S i + k) ‼ e_var mb ; chA (S i + k) ⁇ y ]
      else [].
Proof.
  induction r as [| r' IH]; intros i k.
  - destruct k; cbn [bob comm_at Nat.ltb Nat.leb]; reflexivity.
  - destruct k as [| k'].
    + cbn [bob comm_at Nat.ltb Nat.leb]. rewrite Nat.add_0_r. reflexivity.
    + cbn [bob comm_at Nat.ltb Nat.leb]. rewrite IH.
      replace (S i + S k')%nat with (S (S i) + k')%nat by lia.
      reflexivity.
Qed.

(** The two leaves, named so the phase lemmas can talk about them. *)
Definition proc_a (n : nat) : process :=
  head_a ⨾ ([ chA 0 ‼ e_var ma ; chB 0 ⁇ x ]) ⨾ alice 0 n.
Definition proc_b (n : nat) : process :=
  head_b ⨾ ([ chB 0 ‼ e_var mb ; chA 0 ⁇ y ]) ⨾ bob 0 n.

Lemma distill_leaves : forall n, distill n = ⟨ proc_a n ⟩ ∥ ⟨ proc_b n ⟩.
Proof. reflexivity. Qed.

(** Folding round 0 back in: a leaf's k-th block is round [k]'s rendezvous
    pair exactly when [k <= n].  [Nat.ltb k' n] and [Nat.leb (S k') n] are
    the same term, which is why the successor case closes by [reflexivity]. *)
Lemma comm_at_a : forall n k,
    comm_at (proc_a n) k
    = if Nat.leb k n then [ chA k ‼ e_var ma ; chB k ⁇ x ] else [].
Proof.
  intros n k. destruct k as [| k'].
  - reflexivity.
  - cbn [proc_a comm_at]. rewrite comm_at_alice.
    replace (S 0 + k')%nat with (S k') by lia. reflexivity.
Qed.

Lemma comm_at_b : forall n k,
    comm_at (proc_b n) k
    = if Nat.leb k n then [ chB k ‼ e_var mb ; chA k ⁇ y ] else [].
Proof.
  intros n k. destruct k as [| k'].
  - reflexivity.
  - cbn [proc_b comm_at]. rewrite comm_at_bob.
    replace (S 0 + k')%nat with (S k') by lia. reflexivity.
Qed.

Lemma phase_actions_distill : forall n k,
    phase_actions (distill n) k
    = if Nat.leb k n
      then [ chA k ‼ e_var ma ; chB k ⁇ x ; chB k ‼ e_var mb ; chA k ⁇ y ]
      else [].
Proof.
  intros n k. unfold phase_actions, phase_at, phase_row.
  rewrite distill_leaves. cbn [row_map row_leaves concat].
  rewrite comm_at_a, comm_at_b.
  destruct (Nat.leb k n); reflexivity.
Qed.

(** The two channels of a round are distinct: [chA k = 2k] is even and
    [chB k = 2k+1] is odd. *)
Lemma chAB_neq : forall k, chA k <> chB k.
Proof. intros k; unfold chA, chB; lia. Qed.

Lemma wf_phase_aligned_distill : forall n, wf_phase_aligned (distill n).
Proof.
  intros n k c Hin. rewrite phase_actions_distill in *.
  destruct (Nat.leb k n) eqn:Hk; [| cbn in Hin; contradiction].
  cbn [map caction_chan] in Hin.
  assert (HA : (chB k =? chA k) = false)
    by (apply Nat.eqb_neq; intro H; apply (chAB_neq k); symmetry; exact H).
  assert (HB : (chA k =? chB k) = false)
    by (apply Nat.eqb_neq; apply chAB_neq).
  destruct Hin as [Hc|[Hc|[Hc|[Hc|[]]]]]; rewrite <- Hc;
    cbn [filter caction_chan]; rewrite ?Nat.eqb_refl, ?HA, ?HB; reflexivity.
Qed.

Lemma wf_phase_independence_distill : forall n, wf_phase_independence (distill n).
Proof.
  intros n k. unfold recv_targets, output_reads, phase_at, phase_row.
  rewrite distill_leaves. cbn [row_map row_leaves].
  rewrite comm_at_a, comm_at_b.
  destruct (Nat.leb k n); split;
    solve [ vm_compute; repeat constructor; cbn; intuition congruence
          | intros v Hv Hw; vm_compute in Hv, Hw; intuition congruence
          | vm_compute; constructor
          | intros v Hv; vm_compute in Hv; contradiction ].
Qed.

(** Ownership.  Alice's classical variables are 0..4 and Bob's 5..9, so
    the two classical footprints are separated by a numeric bound; her
    qubits are [Ak j = 4j] and [At j = 4j+2] and his are [Bk j = 4j+1] and
    [Bt j = 4j+3], so the two quantum footprints are separated by parity.
    Both are read off the round structure by induction. *)

Ltac vbound :=
  repeat (match goal with
          | H : _ \/ _ |- _ =>
              destruct H as [H | H];
              [ subst; cbv [ia da oa ma x ib db ob mb y]; lia |]
          end).

Lemma alice_change : forall r i v, In v (process_change (alice i r)) -> (v < 5)%nat.
Proof.
  induction r as [| r' IH]; intros i v Hv; cbn in Hv; vbound.
  - contradiction.
  - exact (IH _ _ Hv).
Qed.

Lemma alice_read : forall r i v, In v (process_read (alice i r)) -> (v < 5)%nat.
Proof.
  induction r as [| r' IH]; intros i v Hv; cbn in Hv; vbound.
  - contradiction.
  - exact (IH _ _ Hv).
Qed.

Lemma bob_change : forall r i v, In v (process_change (bob i r)) -> (5 <= v < 10)%nat.
Proof.
  induction r as [| r' IH]; intros i v Hv; cbn in Hv; vbound.
  - contradiction.
  - exact (IH _ _ Hv).
Qed.

Lemma bob_read : forall r i v, In v (process_read (bob i r)) -> (5 <= v < 10)%nat.
Proof.
  induction r as [| r' IH]; intros i v Hv; cbn in Hv; vbound.
  - contradiction.
  - exact (IH _ _ Hv).
Qed.

Lemma ab_qvar_neq : forall qa qb,
    (exists j, qa = Ak j \/ qa = At j) ->
    (exists j, qb = Bk j \/ qb = Bt j) -> qa <> qb.
Proof.
  intros qa qb [ja Ha] [jb Hb]. unfold Ak, At, Bk, Bt in *.
  destruct Ha; destruct Hb; subst; lia.
Qed.

Lemma alice_qvar : forall r i q, In q (process_qvar (alice i r)) ->
    exists j, q = Ak j \/ q = At j.
Proof.
  induction r as [| r' IH]; intros i q Hq;
    cbn [alice process_qvar residual_qvar lblock_qvar accept_a mid_a app] in Hq.
  - contradiction.
  - destruct Hq as [Hq | [Hq | [Hq | Hq]]];
      [ exists (S i); left  | exists (S i); right | exists (S i); right
      | exact (IH _ _ Hq) ]; symmetry; exact Hq.
Qed.

Lemma bob_qvar : forall r i q, In q (process_qvar (bob i r)) ->
    exists j, q = Bk j \/ q = Bt j.
Proof.
  induction r as [| r' IH]; intros i q Hq;
    cbn [bob process_qvar residual_qvar lblock_qvar accept_b mid_b app] in Hq.
  - contradiction.
  - destruct Hq as [Hq | [Hq | [Hq | Hq]]];
      [ exists (S i); left  | exists (S i); right | exists (S i); right
      | exact (IH _ _ Hq) ]; symmetry; exact Hq.
Qed.

Lemma proc_a_qvar : forall n q, In q (process_qvar (proc_a n)) ->
    exists j, q = Ak j \/ q = At j.
Proof.
  intros n q Hq;
    cbn [proc_a process_qvar residual_qvar lblock_qvar head_a app] in Hq.
  destruct Hq as [Hq | [Hq | [Hq | Hq]]];
    [ exists 0%nat; left | exists 0%nat; right | exists 0%nat; right
    | exact (alice_qvar _ _ _ Hq) ]; symmetry; exact Hq.
Qed.

Lemma proc_b_qvar : forall n q, In q (process_qvar (proc_b n)) ->
    exists j, q = Bk j \/ q = Bt j.
Proof.
  intros n q Hq;
    cbn [proc_b process_qvar residual_qvar lblock_qvar head_b app] in Hq.
  destruct Hq as [Hq | [Hq | [Hq | Hq]]];
    [ exists 0%nat; left | exists 0%nat; right | exists 0%nat; right
    | exact (bob_qvar _ _ _ Hq) ]; symmetry; exact Hq.
Qed.

Lemma proc_a_cvar : forall n v, In v (process_cvar (proc_a n)) -> (v < 5)%nat.
Proof.
  intros n v Hv. unfold process_cvar in Hv. apply in_app_or in Hv.
  destruct Hv as [Hv | Hv]; cbn in Hv; vbound;
    [ exact (alice_change _ _ _ Hv) | exact (alice_read _ _ _ Hv) ].
Qed.

Lemma proc_b_cvar : forall n v, In v (process_cvar (proc_b n)) -> (5 <= v < 10)%nat.
Proof.
  intros n v Hv. unfold process_cvar in Hv. apply in_app_or in Hv.
  destruct Hv as [Hv | Hv]; cbn in Hv; vbound;
    [ exact (bob_change _ _ _ Hv) | exact (bob_read _ _ _ Hv) ].
Qed.

Lemma proc_a_change : forall n v, In v (process_change (proc_a n)) -> (v < 5)%nat.
Proof.
  intros n v Hv; cbn in Hv; vbound; exact (alice_change _ _ _ Hv).
Qed.

Lemma proc_b_change : forall n v, In v (process_change (proc_b n)) -> (5 <= v < 10)%nat.
Proof.
  intros n v Hv; cbn in Hv; vbound; exact (bob_change _ _ _ Hv).
Qed.

Lemma wf_ownership_distill : forall n, wf_ownership (distill n).
Proof.
  intro n. rewrite distill_leaves. cbn [wf_ownership].
  split; [exact Logic.I | split; [exact Logic.I |]].
  unfold cross_disjoint, program_change, program_cvar, program_qvar.
  cbn [row_flat].
  split; [| split].
  - intros v Hv Hw.
    pose proof (proc_a_change n v Hv); pose proof (proc_b_cvar n v Hw). lia.
  - intros v Hv Hw.
    pose proof (proc_b_change n v Hv); pose proof (proc_a_cvar n v Hw). lia.
  - intros q Hq Hw.
    exact (ab_qvar_neq q q (proc_a_qvar n q Hq) (proc_b_qvar n q Hw) eq_refl).
Qed.

(** Channels.  A leaf's action list is a [flat_map] over its rounds, so a
    channel's endpoints are counted by one induction over [seq].  [chA j]
    is even and [chB j] odd, which is what makes the count exactly one on
    each side. *)

Lemma actions_alice : forall r i,
    process_actions (alice i r)
    = flat_map (fun j => [ chA j ‼ e_var ma ; chB j ⁇ x ]) (seq (S i) r).
Proof.
  induction r as [| r' IH]; intros i; [ reflexivity |].
  cbn [alice process_actions seq flat_map]. rewrite IH. reflexivity.
Qed.

Lemma actions_bob : forall r i,
    process_actions (bob i r)
    = flat_map (fun j => [ chB j ‼ e_var mb ; chA j ⁇ y ]) (seq (S i) r).
Proof.
  induction r as [| r' IH]; intros i; [ reflexivity |].
  cbn [bob process_actions seq flat_map]. rewrite IH. reflexivity.
Qed.

Lemma actions_proc_a : forall n,
    process_actions (proc_a n)
    = flat_map (fun j => [ chA j ‼ e_var ma ; chB j ⁇ x ]) (seq 0 (S n)).
Proof.
  intro n. cbn [proc_a process_actions]. rewrite actions_alice.
  cbn [seq flat_map]. reflexivity.
Qed.

Lemma actions_proc_b : forall n,
    process_actions (proc_b n)
    = flat_map (fun j => [ chB j ‼ e_var mb ; chA j ⁇ y ]) (seq 0 (S n)).
Proof.
  intro n. cbn [proc_b process_actions]. rewrite actions_bob.
  cbn [seq flat_map]. reflexivity.
Qed.

(** Counting a channel's endpoints, in two steps that are both blind to the
    order inside a round's block — a [cblock] is unordered, and an earlier
    version of this lemma wrongly baked "the chA endpoint comes first" into
    its statement, which then did not fit Bob's leaf.

    Step one: filtering distributes over the rounds.  Step two: a round
    contributes to channel [c] only if it is the round that owns [c]. *)
Lemma filter_flat_map : forall {A B} (p : B -> bool) (g : A -> list B) (l : list A),
    filter p (flat_map g l) = flat_map (fun a => filter p (g a)) l.
Proof.
  intros A B p g l; induction l as [| a l IH]; cbn; [reflexivity |].
  rewrite filter_app, IH. reflexivity.
Qed.

Lemma flat_map_pick : forall {B} (j0 : nat) (u : nat -> list B) m s,
    flat_map (fun j => if Nat.eqb j j0 then u j else []) (seq s m)
    = if andb (Nat.leb s j0) (Nat.ltb j0 (s + m)) then u j0 else [].
Proof.
  intros B j0 u m; induction m as [| m' IH]; intros s.
  - replace (Nat.leb s j0 && Nat.ltb j0 (s + 0))%bool with false;
      [ reflexivity |].
    destruct (Nat.leb s j0) eqn:E1; destruct (Nat.ltb j0 (s + 0)) eqn:E2;
      cbn; try reflexivity.
    apply Nat.leb_le in E1; apply Nat.ltb_lt in E2; lia.
  - cbn [seq flat_map]. rewrite IH.
    destruct (Nat.eqb s j0) eqn:E.
    + apply Nat.eqb_eq in E; subst s.
      replace (Nat.leb j0 j0) with true by (symmetry; apply Nat.leb_le; lia).
      replace (Nat.ltb j0 (j0 + S m')) with true
        by (symmetry; apply Nat.ltb_lt; lia).
      replace (Nat.leb (S j0) j0) with false
        by (symmetry; apply Nat.leb_gt; lia).
      cbn. apply app_nil_r.
    + apply Nat.eqb_neq in E. cbn [app].
      destruct (Nat.leb s j0) eqn:E1; destruct (Nat.leb (S s) j0) eqn:E2;
        destruct (Nat.ltb j0 (s + S m')) eqn:E3;
        destruct (Nat.ltb j0 (S s + m')) eqn:E4; cbn; try reflexivity;
        repeat match goal with
               | H : Nat.leb _ _ = true  |- _ => apply Nat.leb_le in H
               | H : Nat.leb _ _ = false |- _ => apply Nat.leb_gt in H
               | H : Nat.ltb _ _ = true  |- _ => apply Nat.ltb_lt in H
               | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
               end; lia.
Qed.


Lemma flat_map_ext : forall {A B} (f g : A -> list B) (l : list A),
    (forall a, f a = g a) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l H; induction l as [| a l IH]; cbn; [reflexivity |].
  rewrite H, IH; reflexivity.
Qed.

Lemma eqb_chA : forall j j0, (chA j =? chA j0) = (j =? j0).
Proof.
  intros j j0; unfold chA; destruct (Nat.eqb j j0) eqn:E.
  - apply Nat.eqb_eq in E; subst; apply Nat.eqb_refl.
  - apply Nat.eqb_neq in E; apply Nat.eqb_neq; lia.
Qed.

Lemma eqb_chB : forall j j0, (chB j =? chB j0) = (j =? j0).
Proof.
  intros j j0; unfold chB; destruct (Nat.eqb j j0) eqn:E.
  - apply Nat.eqb_eq in E; subst; apply Nat.eqb_refl.
  - apply Nat.eqb_neq in E; apply Nat.eqb_neq; lia.
Qed.

Lemma eqb_chBA : forall j j0, (chB j =? chA j0) = false.
Proof. intros; apply Nat.eqb_neq; unfold chA, chB; lia. Qed.

Lemma eqb_chAB : forall j j0, (chA j =? chB j0) = false.
Proof. intros; apply Nat.eqb_neq; unfold chA, chB; lia. Qed.

Ltac in_range j0 n :=
  replace (Nat.leb 0 j0) with true by (symmetry; apply Nat.leb_le; lia);
  replace (Nat.ltb j0 (0 + S n)) with true
    by (symmetry; apply Nat.ltb_lt; lia).

(** Both endpoints of [chA j0] — Alice's output and Bob's input — and
    nothing else.  The two leaves are handled by the same two lemmas even
    though Bob writes his block the other way round. *)
Lemma endpoints_chA : forall n j0, (j0 <= n)%nat ->
    filter (fun a => Nat.eqb (caction_chan a) (chA j0)) (program_actions (distill n))
    = [ chA j0 ‼ e_var ma ; chA j0 ⁇ y ].
Proof.
  intros n j0 Hj. unfold program_actions. rewrite distill_leaves.
  cbn [row_flat]. rewrite filter_app, actions_proc_a, actions_proc_b.
  rewrite !filter_flat_map.
  rewrite (flat_map_ext _ (fun j => if Nat.eqb j j0 then [chA j ‼ e_var ma] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chA, eqb_chBA;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite (flat_map_ext (fun a => filter _ _)
                        (fun j => if Nat.eqb j j0 then [chA j ⁇ y] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chA, eqb_chBA;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite !flat_map_pick. in_range j0 n. reflexivity.
Qed.

Lemma endpoints_chB : forall n j0, (j0 <= n)%nat ->
    filter (fun a => Nat.eqb (caction_chan a) (chB j0)) (program_actions (distill n))
    = [ chB j0 ⁇ x ; chB j0 ‼ e_var mb ].
Proof.
  intros n j0 Hj. unfold program_actions. rewrite distill_leaves.
  cbn [row_flat]. rewrite filter_app, actions_proc_a, actions_proc_b.
  rewrite !filter_flat_map.
  rewrite (flat_map_ext _ (fun j => if Nat.eqb j j0 then [chB j ⁇ x] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chB, eqb_chAB;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite (flat_map_ext (fun a => filter _ _)
                        (fun j => if Nat.eqb j j0 then [chB j ‼ e_var mb] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chB, eqb_chAB;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite !flat_map_pick. in_range j0 n. reflexivity.
Qed.

Lemma chan_range : forall n c, In c (program_chan (distill n)) ->
    exists j0, (j0 <= n)%nat /\ (c = chA j0 \/ c = chB j0).
Proof.
  intros n c Hc. rewrite program_chan_actions in Hc.
  apply in_map_iff in Hc. destruct Hc as [a [Hca Ha]].
  unfold program_actions in Ha. rewrite distill_leaves in Ha.
  cbn [row_flat] in Ha. rewrite actions_proc_a, actions_proc_b in Ha.
  apply in_app_or in Ha; destruct Ha as [Ha | Ha];
    apply in_flat_map in Ha; destruct Ha as [j [Hj Ha]];
    apply in_seq in Hj;
    exists j; split; try lia;
    destruct Ha as [Ha | [Ha | []]]; subst a;
    cbn [caction_chan] in Hca; subst c;
    [ left | right | right | left ]; reflexivity.
Qed.

Lemma in_chan_a : forall n j0, (j0 <= n)%nat ->
    In (chA j0) (process_chan (proc_a n)) /\ In (chB j0) (process_chan (proc_a n)).
Proof.
  intros n j0 Hj. rewrite process_chan_actions, actions_proc_a.
  split; [ apply in_map_iff; exists (chA j0 ‼ e_var ma)
         | apply in_map_iff; exists (chB j0 ⁇ x) ];
    (split; [ reflexivity |]);
    apply in_flat_map; exists j0; (split; [ apply in_seq; lia |]);
    cbn; tauto.
Qed.

Lemma in_chan_b : forall n j0, (j0 <= n)%nat ->
    In (chA j0) (process_chan (proc_b n)) /\ In (chB j0) (process_chan (proc_b n)).
Proof.
  intros n j0 Hj. rewrite process_chan_actions, actions_proc_b.
  split; [ apply in_map_iff; exists (chA j0 ⁇ y)
         | apply in_map_iff; exists (chB j0 ‼ e_var mb) ];
    (split; [ reflexivity |]);
    apply in_flat_map; exists j0; (split; [ apply in_seq; lia |]);
    cbn; tauto.
Qed.

Lemma wf_channels_distill : forall n, wf_channels (distill n).
Proof.
  intros n c Hc.
  destruct (chan_range n c Hc) as [j0 [Hj [-> | ->]]];
    unfold endpoints_of;
    [ rewrite endpoints_chA by exact Hj | rewrite endpoints_chB by exact Hj ];
    (split; [ reflexivity | split; [ reflexivity |]]);
    unfold parties; rewrite distill_leaves; cbn [row_parties];
    destruct (in_chan_a n j0 Hj) as [Ha1 Ha2];
    destruct (in_chan_b n j0 Hj) as [Hb1 Hb2];
    repeat match goal with
           | |- context[existsb (Nat.eqb ?c) ?l] =>
               replace (existsb (Nat.eqb c) l) with true
                 by (symmetry; apply existsb_exists; exists c;
                     split; [ assumption | apply Nat.eqb_refl ])
           end; reflexivity.
Qed.

Lemma wf_program_distill : forall n, wf_program (distill n).
Proof.
  intro n. split; [| split; [| split]].
  - exact (wf_ownership_distill n).
  - exact (wf_channels_distill n).
  - exact (wf_phase_aligned_distill n).
  - exact (wf_phase_independence_distill n).
Qed.

(** ** Well-formedness of a tail ***************************************

    [rule_par_comp] asks for [wf_program] of the program it cuts, so the
    induction over rounds needs it of [tround i r] and not only of
    [distill n].  Same four obligations, same four closed forms — they were
    stated over a symbolic round window [seq (S i) r] precisely so that
    both callers fit. *)

Lemma phase_actions_tround : forall i r k,
    phase_actions (tround i r) k
    = if Nat.ltb k r
      then [ chA (S i + k) ‼ e_var ma ; chB (S i + k) ⁇ x ;
             chB (S i + k) ‼ e_var mb ; chA (S i + k) ⁇ y ]
      else [].
Proof.
  intros i r k. unfold phase_actions, phase_at, phase_row, tround.
  cbn [row_map row_leaves concat].
  rewrite comm_at_alice, comm_at_bob.
  destruct (Nat.ltb k r); reflexivity.
Qed.

Lemma wf_phase_aligned_tround : forall i r, wf_phase_aligned (tround i r).
Proof.
  intros i r k c Hin. rewrite phase_actions_tround in *.
  destruct (Nat.ltb k r) eqn:Hk; [| cbn in Hin; contradiction].
  cbn [map caction_chan] in Hin.
  assert (HA : (chB (S i + k) =? chA (S i + k)) = false)
    by (apply Nat.eqb_neq; intro H; apply (chAB_neq (S i + k)); symmetry; exact H).
  assert (HB : (chA (S i + k) =? chB (S i + k)) = false)
    by (apply Nat.eqb_neq; apply chAB_neq).
  destruct Hin as [Hc|[Hc|[Hc|[Hc|[]]]]]; rewrite <- Hc;
    cbn [filter caction_chan]; rewrite ?Nat.eqb_refl, ?HA, ?HB; reflexivity.
Qed.

Lemma wf_phase_independence_tround : forall i r, wf_phase_independence (tround i r).
Proof.
  intros i r k. unfold recv_targets, output_reads, phase_at, phase_row, tround.
  cbn [row_map row_leaves].
  rewrite comm_at_alice, comm_at_bob.
  destruct (Nat.ltb k r); split;
    solve [ vm_compute; repeat constructor; cbn; intuition congruence
          | intros v Hv Hw; vm_compute in Hv, Hw; intuition congruence
          | vm_compute; constructor
          | intros v Hv; vm_compute in Hv; contradiction ].
Qed.

Lemma wf_ownership_tround : forall i r, wf_ownership (tround i r).
Proof.
  intros i r. unfold tround. cbn [wf_ownership].
  split; [exact Logic.I | split; [exact Logic.I |]].
  unfold cross_disjoint, program_change, program_cvar, program_qvar.
  cbn [row_flat].
  split; [| split].
  - intros v Hv Hw. pose proof (alice_change _ _ _ Hv).
    unfold process_cvar in Hw; apply in_app_or in Hw.
    destruct Hw as [Hw | Hw];
      [ pose proof (bob_change _ _ _ Hw) | pose proof (bob_read _ _ _ Hw) ]; lia.
  - intros v Hv Hw. pose proof (bob_change _ _ _ Hv).
    unfold process_cvar in Hw; apply in_app_or in Hw.
    destruct Hw as [Hw | Hw];
      [ pose proof (alice_change _ _ _ Hw) | pose proof (alice_read _ _ _ Hw) ]; lia.
  - intros q Hq Hw.
    exact (ab_qvar_neq q q (alice_qvar _ _ _ Hq) (bob_qvar _ _ _ Hw) eq_refl).
Qed.

Ltac in_window i r j0 :=
  replace (Nat.leb (S i) j0) with true by (symmetry; apply Nat.leb_le; lia);
  replace (Nat.ltb j0 (S i + r)) with true by (symmetry; apply Nat.ltb_lt; lia).

Lemma endpoints_chA_tround : forall i r j0, (S i <= j0 < S i + r)%nat ->
    filter (fun a => Nat.eqb (caction_chan a) (chA j0)) (program_actions (tround i r))
    = [ chA j0 ‼ e_var ma ; chA j0 ⁇ y ].
Proof.
  intros i r j0 Hj. unfold program_actions, tround. cbn [row_flat].
  rewrite filter_app, actions_alice, actions_bob, !filter_flat_map.
  rewrite (flat_map_ext _ (fun j => if Nat.eqb j j0 then [chA j ‼ e_var ma] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chA, eqb_chBA;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite (flat_map_ext (fun a => filter _ _)
                        (fun j => if Nat.eqb j j0 then [chA j ⁇ y] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chA, eqb_chBA;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite !flat_map_pick. in_window i r j0. reflexivity.
Qed.

Lemma endpoints_chB_tround : forall i r j0, (S i <= j0 < S i + r)%nat ->
    filter (fun a => Nat.eqb (caction_chan a) (chB j0)) (program_actions (tround i r))
    = [ chB j0 ⁇ x ; chB j0 ‼ e_var mb ].
Proof.
  intros i r j0 Hj. unfold program_actions, tround. cbn [row_flat].
  rewrite filter_app, actions_alice, actions_bob, !filter_flat_map.
  rewrite (flat_map_ext _ (fun j => if Nat.eqb j j0 then [chB j ⁇ x] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chB, eqb_chAB;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite (flat_map_ext (fun a => filter _ _)
                        (fun j => if Nat.eqb j j0 then [chB j ‼ e_var mb] else []))
    by (intro j; cbn [filter caction_chan]; rewrite eqb_chB, eqb_chAB;
        destruct (Nat.eqb j j0); reflexivity).
  rewrite !flat_map_pick. in_window i r j0. reflexivity.
Qed.

Lemma chan_range_tround : forall i r c, In c (program_chan (tround i r)) ->
    exists j0, (S i <= j0 < S i + r)%nat /\ (c = chA j0 \/ c = chB j0).
Proof.
  intros i r c Hc. rewrite program_chan_actions in Hc.
  apply in_map_iff in Hc. destruct Hc as [a [Hca Ha]].
  unfold program_actions, tround in Ha. cbn [row_flat] in Ha.
  rewrite actions_alice, actions_bob in Ha.
  apply in_app_or in Ha; destruct Ha as [Ha | Ha];
    apply in_flat_map in Ha; destruct Ha as [j [Hj Ha]];
    apply in_seq in Hj;
    exists j; split; try lia;
    destruct Ha as [Ha | [Ha | []]]; subst a;
    cbn [caction_chan] in Hca; subst c;
    [ left | right | right | left ]; reflexivity.
Qed.

Lemma in_chan_alice : forall i r j0, (S i <= j0 < S i + r)%nat ->
    In (chA j0) (process_chan (alice i r)) /\ In (chB j0) (process_chan (alice i r)).
Proof.
  intros i r j0 Hj. rewrite process_chan_actions, actions_alice.
  split; [ apply in_map_iff; exists (chA j0 ‼ e_var ma)
         | apply in_map_iff; exists (chB j0 ⁇ x) ];
    (split; [ reflexivity |]);
    apply in_flat_map; exists j0; (split; [ apply in_seq; lia |]); cbn; tauto.
Qed.

Lemma in_chan_bob : forall i r j0, (S i <= j0 < S i + r)%nat ->
    In (chA j0) (process_chan (bob i r)) /\ In (chB j0) (process_chan (bob i r)).
Proof.
  intros i r j0 Hj. rewrite process_chan_actions, actions_bob.
  split; [ apply in_map_iff; exists (chA j0 ⁇ y)
         | apply in_map_iff; exists (chB j0 ‼ e_var mb) ];
    (split; [ reflexivity |]);
    apply in_flat_map; exists j0; (split; [ apply in_seq; lia |]); cbn; tauto.
Qed.

Lemma wf_channels_tround : forall i r, wf_channels (tround i r).
Proof.
  intros i r c Hc.
  destruct (chan_range_tround i r c Hc) as [j0 [Hj [-> | ->]]];
    unfold endpoints_of;
    [ rewrite endpoints_chA_tround by exact Hj
    | rewrite endpoints_chB_tround by exact Hj ];
    (split; [ reflexivity | split; [ reflexivity |]]);
    unfold parties, tround; cbn [row_parties];
    destruct (in_chan_alice i r j0 Hj) as [Ha1 Ha2];
    destruct (in_chan_bob i r j0 Hj) as [Hb1 Hb2];
    repeat match goal with
           | |- context[existsb (Nat.eqb ?c) ?l] =>
               replace (existsb (Nat.eqb c) l) with true
                 by (symmetry; apply existsb_exists; exists c;
                     split; [ assumption | apply Nat.eqb_refl ])
           end; reflexivity.
Qed.

Lemma wf_program_tround : forall i r, wf_program (tround i r).
Proof.
  intros i r. split; [| split; [| split]].
  - exact (wf_ownership_tround i r).
  - exact (wf_channels_tround i r).
  - exact (wf_phase_aligned_tround i r).
  - exact (wf_phase_independence_tround i r).
Qed.

(** ** The idle rounds *************************************************

    Under [Acc k] the latch [da] is already 1, so both accept tests take
    their else branch: the guard [ma = x /\ da = 0] is contradictory. *)

Definition guard_a : bexpr :=
  b_and (b_eq (e_var ma) (e_var x)) (b_eq (e_var da) (e_val 0%nat)).
Definition guard_b : bexpr :=
  b_and (b_eq (e_var mb) (e_var y)) (b_eq (e_var db) (e_val 0%nat)).

Lemma guard_a_unfold : forall i, accept_a i =
  <{ if guard_a then (oa := (e_val 1%nat) ; da := (e_val 1%nat) ; ia := (e_val (S i)))
     else skip }>.
Proof. reflexivity. Qed.

Lemma guard_b_unfold : forall i, accept_b i =
  <{ if guard_b then (ob := (e_val 1%nat) ; db := (e_val 1%nat) ; ib := (e_val (S i)))
     else skip }>.
Proof. reflexivity. Qed.

(* [Acc k] pins da = 1 while the guard demands da = 0, so the conjunction
   is false in every store and all three entailment obligations are
   vacuous — whatever the target assertion is. *)
Lemma acc_guard_a_true : forall n k (R : assertion (4 * S n)),
    and_guard (distill_post k n) guard_a true ⊨[Sig n] R.
Proof.
  intros n k R.
  assert (Hf : forall s, formula_holds (Sig n) s
                 (classical_part (and_guard (distill_post k n) guard_a true))
               = false).
  { intro s. cbn. destruct (s da) as [| [| d]]; cbn;
      rewrite ?andb_false_r, ?andb_false_l; reflexivity. }
  split; [| split];
    [ intros s Hs | intros s Hs | intros s M N Hs ];
    rewrite Hf in Hs; discriminate.
Qed.

(** ** Effects *********************************************************

    [is_effect M] is 0 ⊑ M ⊑ I, the assertion-formation check that Conseq
    and Par-Comp-MP both carry.  Every assertion of this case study is a
    tensor of projectors, so one generic argument covers all of them. *)

Lemma lowner_refl : forall m (M : Square m), M ⊑ M.
Proof.
  intros m M. unfold lowner, positive_semidefinite. intros z Hz.
  replace (M .+ (- C1) .* M) with (@Zero m m) by lma.
  rewrite Mmult_0_r, Mmult_0_l. cbn. lra.
Qed.

Lemma entails_refl : forall d (S0 : interp d) (Q : assertion d), Q ⊨[S0] Q.
Proof.
  intros d S0 Q. repeat split; auto.
  intros s M N _ H1 H2. rewrite H1 in H2. inversion H2. apply lowner_refl.
Qed.

Lemma herm_idem_psd : forall m (M : Square m),
    M † = M -> M × M = M -> positive_semidefinite M.
Proof.
  intros m M Hh Hi.
  assert (E : M = M × M †) by (rewrite Hh, Hi; reflexivity).
  rewrite E at 1. apply positive_semidefinite_AAadjoint.
Qed.

Lemma herm_idem_effect : forall d (M : Square (2 ^ d)),
    WF_Matrix M -> M † = M -> M × M = M -> is_effect (dim := d) M.
Proof.
  intros d M HW Hh Hi. split; [apply herm_idem_psd; assumption |].
  unfold lowner. apply herm_idem_psd.
  - rewrite Mplus_adjoint, Mscale_adj, id_adjoint_eq, Hh.
    replace ((- C1) ^* )%C with (- C1)%C by lca. reflexivity.
  - rewrite Mmult_plus_distr_l, !Mmult_plus_distr_r. Msimpl.
    rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc, Hi.
    lma.
Qed.

(** A projector, packaged so the three closure properties can be chained. *)
Definition projlike {m} (P : Square m) : Prop :=
  WF_Matrix P /\ P † = P /\ P × P = P.

Lemma projlike_I : forall m, projlike (I m).
Proof.
  intro m; repeat split; [ auto with wf_db | apply id_adjoint_eq
                         | apply Mmult_1_l; auto with wf_db ].
Qed.

Lemma projlike_kron : forall m m' (P : Square m) (Q : Square m'),
    projlike P -> projlike Q -> projlike (P ⊗ Q).
Proof.
  intros m m' P Q [WP [HP IP]] [WQ [HQ IQ]]; repeat split.
  - auto with wf_db.
  - rewrite kron_adjoint, HP, HQ; reflexivity.
  - rewrite kron_mixed_product, IP, IQ; reflexivity.
Qed.

Lemma projlike_kron_n : forall m (P : Square m) j,
    projlike P -> projlike (kron_n j P).
Proof.
  intros m P j HP; induction j as [| j' IH]; cbn [kron_n].
  - apply projlike_I.
  - assert (E : (m ^ S j')%nat = (m ^ j' * m)%nat)
      by (cbn [Nat.pow]; apply Nat.mul_comm).
    rewrite E. apply projlike_kron; assumption.
Qed.

Lemma projlike_Ev : projlike Ev.
Proof.
  unfold Ev; repeat split; [ auto with wf_db | lma' | lma' ].
Qed.

Lemma projlike_Od : projlike Od.
Proof.
  unfold Od; repeat split; [ auto with wf_db | lma' | lma' ].
Qed.

Lemma projlike_EqSub : projlike EqSub.
Proof.
  unfold EqSub. change (@projlike (4 * 4) (I 4 ⊗ Ev)).
  apply projlike_kron; [apply projlike_I | apply projlike_Ev].
Qed.

Lemma projlike_NeqSub : projlike NeqSub.
Proof.
  unfold NeqSub. change (@projlike (4 * 4) (I 4 ⊗ Od)).
  apply projlike_kron; [apply projlike_I | apply projlike_Od].
Qed.

(** [16^k · 16 · 16^(n-k) = 2^(4(n+1))] — the arithmetic the phantom index
    hides.  Needed because [is_effect] at dimension [d] mentions
    [I (2 ^ d)] and so must see the right number. *)
Lemma dim_post : forall k n, (k <= n)%nat ->
    (16 ^ k * 16 * 16 ^ (n - k))%nat = (2 ^ (4 * S n))%nat.
Proof.
  intros k n Hk.
  replace (16 ^ k * 16)%nat with (16 ^ S k)%nat
    by (cbn [Nat.pow]; apply Nat.mul_comm).
  rewrite <- Nat.pow_add_r.
  replace (S k + (n - k))%nat with (S n) by lia.
  rewrite Nat.pow_mul_r. reflexivity.
Qed.

(* At the natural index: the three tensor factors, not the 2^(4(n+1)) the
   definition is ascribed.  [is_effect_post_q] moves across by [dim_post]. *)
Lemma projlike_post_q : forall k n,
    @projlike (16 ^ k * 16 * 16 ^ (n - k)) (post_q k n).
Proof.
  intros k n. unfold post_q.
  apply projlike_kron; [apply projlike_kron |].
  - apply projlike_kron_n, projlike_NeqSub.
  - apply projlike_EqSub.
  - apply projlike_kron_n, projlike_I.
Qed.

Lemma is_effect_post_q : forall k n, (k <= n)%nat ->
    is_effect (dim := 4 * S n) (post_q k n).
Proof.
  intros k n Hk. destruct (projlike_post_q k n) as [HW [Hh Hi]].
  rewrite (dim_post k n Hk) in HW, Hh, Hi.
  apply herm_idem_effect; assumption.
Qed.

Lemma wf_distill_post : forall k n, (k <= n)%nat ->
    wf_assertion (Sig n) (distill_post k n).
Proof.
  intros k n Hk s M HM. cbn in HM. inversion HM; subst.
  apply is_effect_post_q; exact Hk.
Qed.

(** ** The idle-round local row **************************************** *)

Lemma acc_guard_a_false : forall n k,
    and_guard (distill_post k n) guard_a false ⊨[Sig n] distill_post k n.
Proof.
  intros n k. split; [| split].
  - intros s Hs; cbn in Hs; apply andb_true_iff in Hs as [H _]; exact H.
  - intros s _ Hd; exact Hd.
  - intros s M N _ HM HN; cbn in HM, HN;
      rewrite HM in HN; inversion HN; apply lowner_refl.
Qed.

Lemma acc_guard_b_false : forall n k,
    and_guard (distill_post k n) guard_b false ⊨[Sig n] distill_post k n.
Proof.
  intros n k. split; [| split].
  - intros s Hs; cbn in Hs; apply andb_true_iff in Hs as [H _]; exact H.
  - intros s _ Hd; exact Hd.
  - intros s M N _ HM HN; cbn in HM, HN;
      rewrite HM in HN; inversion HN; apply lowner_refl.
Qed.

Lemma acc_guard_b_true : forall n k (R : assertion (4 * S n)),
    and_guard (distill_post k n) guard_b true ⊨[Sig n] R.
Proof.
  intros n k R.
  assert (Hf : forall s, formula_holds (Sig n) s
                 (classical_part (and_guard (distill_post k n) guard_b true))
               = false).
  { intro s. cbn. destruct (s db) as [| [| d]]; cbn;
      rewrite ?andb_false_r, ?andb_false_l; reflexivity. }
  split; [| split];
    [ intros s Hs | intros s Hs | intros s M N Hs ];
    rewrite Hf in Hs; discriminate.
Qed.

Lemma accept_a_noop : forall n k i, (k <= n)%nat ->
    Sig n ⊢ₗ {{ distill_post k n }} accept_a i {{ distill_post k n }}.
Proof.
  intros n k i Hk. apply rule_if.
  - eapply rule_conseq.
    + apply acc_guard_a_true.
    + eapply rule_seq; [apply rule_assign |].
      eapply rule_seq; [apply rule_assign | apply rule_assign].
    + apply entails_refl.
    + apply wf_distill_post; exact Hk.
  - eapply rule_conseq.
    + apply acc_guard_a_false.
    + apply rule_skip.
    + apply entails_refl.
    + apply wf_distill_post; exact Hk.
Qed.

Lemma accept_b_noop : forall n k i, (k <= n)%nat ->
    Sig n ⊢ₗ {{ distill_post k n }} accept_b i {{ distill_post k n }}.
Proof.
  intros n k i Hk. apply rule_if.
  - eapply rule_conseq.
    + apply acc_guard_b_true.
    + eapply rule_seq; [apply rule_assign |].
      eapply rule_seq; [apply rule_assign | apply rule_assign].
    + apply entails_refl.
    + apply wf_distill_post; exact Hk.
  - eapply rule_conseq.
    + apply acc_guard_b_false.
    + apply rule_skip.
    + apply entails_refl.
    + apply wf_distill_post; exact Hk.
Qed.

Ltac disjrow :=
  repeat constructor; repeat split;
  intros v Hv Hw; vm_compute in Hv, Hw; intuition congruence.

Lemma disj_dlast : forall i, lrow_disj (dlast i).
Proof. intro i; unfold dlast; disjrow. Qed.

Lemma dlast_local : forall n k i, (k <= n)%nat ->
    Sig n ⊢ₗ {{ distill_post k n }} lseq (dlast i) {{ distill_post k n }}.
Proof.
  intros n k i Hk. cbn [lseq dlast].
  eapply rule_seq with (Q2 := distill_post k n);
    [ apply accept_a_noop | apply accept_b_noop ]; exact Hk.
Qed.

(** The base of the idle-round induction: nothing is left but round [i]'s
    accept test, which does not fire, an empty communication row, and two
    terminated leaves.  The first complete Par-Comp-MP of this case study. *)
Lemma phase_after_base : forall n k i, (k <= n)%nat ->
    Sig n ⊢ₚ {{ distill_post k n }} tround i 0 {{ distill_post k n }}.
Proof.
  intros n k i Hk.
  eapply rule_par_comp with (d := dlast i) (k := kempty) (t := tdone)
                            (Q1 := distill_post k n) (Q2 := distill_post k n).
  - exact (cut_base i).
  - exact (wf_program_tround i 0).
  - apply wf_distill_post; exact Hk.
  - apply wf_distill_post; exact Hk.
  - apply rule_par_disjoint; [ apply disj_dlast | apply dlast_local; exact Hk ].
  - apply rule_comm_done. cbn. split; reflexivity.
  - apply rule_done. exact tdone_terminated.
Qed.

(** ** The communication row *******************************************

    Two matched pairs, one per direction, then the emptied block.  The
    assertion mentions neither receive target, so both substitutions are
    the identity and the row carries [distill_post] straight through. *)

Definition kmid1 (i : nat) : krow :=
  ⟨ [ chB (S i) ⁇ x ] ⟩ ∥ ⟨ [ chB (S i) ‼ e_var mb ; chA (S i) ⁇ y ] ⟩.
Definition kmid2 (i : nat) : krow :=
  ⟨ [ chB (S i) ⁇ x ] ⟩ ∥ ⟨ [ chB (S i) ‼ e_var mb ] ⟩.
Definition kmid3 (i : nat) : krow :=
  ⟨ [ chB (S i) ⁇ x ] ⟩ ∥ ⟨ ε ⟩.

(* The blunt [vm_compute] tactic the fixed-round case studies use does not
   work here: it unfolds [chA (S i)] into symbolic arithmetic.  Keep the
   channel names folded and settle the comparisons with [eqb_chAB]. *)
Ltac kchan i :=
  assert (HAB : (chA (S i) =? chB (S i)) = false) by apply eqb_chAB;
  assert (HBA : (chB (S i) =? chA (S i)) = false) by apply eqb_chBA;
  unfold krow_endpoints, krow_actions, krow_chan;
  cbn [row_flat cblock_chan map app filter caction_chan is_send negb
       length row_parties existsb];
  rewrite ?Nat.eqb_refl, ?HAB, ?HBA; cbn; repeat split; reflexivity.

Lemma wf_kmid : forall i, wf_phase (kmid i).
Proof.
  intro i. split; [| split].
  - intros c Hc. unfold kmid, krow_chan in Hc;
      cbn [row_flat cblock_chan map app caction_chan] in Hc.
    unfold kmid; destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; kchan i.
  - vm_compute; repeat constructor; cbn; intuition congruence.
  - intros v Hv Hw; vm_compute in Hv, Hw; intuition congruence.
Qed.

Lemma wf_kmid2 : forall i, wf_phase (kmid2 i).
Proof.
  intro i. split; [| split].
  - intros c Hc. unfold kmid2, krow_chan in Hc;
      cbn [row_flat cblock_chan map app caction_chan] in Hc.
    unfold kmid2; destruct Hc as [<-|[<-|[]]]; kchan i.
  - vm_compute; repeat constructor; cbn; intuition congruence.
  - intros v Hv Hw; vm_compute in Hv, Hw; intuition congruence.
Qed.

Lemma kmid_comm : forall n k i,
    Sig n ⊢ₖ {{ distill_post k n }} kmid i {{ distill_post k n }}.
Proof.
  intros n k i.
  replace (distill_post k n)
    with (assertion_subst (distill_post k n) y (e_var ma)) at 1
    by reflexivity.
  apply rule_comm_select with (kmid := kmid1 i) (k' := kmid2 i)
                              (c := chA (S i)) (e := e_var ma) (x := y).
  { apply wf_kmid. }
  { unfold kmid, kmid1; eauto with locc. }
  { unfold kmid1, kmid2; eauto with locc. }
  replace (distill_post k n)
    with (assertion_subst (distill_post k n) x (e_var mb)) at 1
    by reflexivity.
  apply rule_comm_select with (kmid := kmid3 i) (k' := kempty)
                              (c := chB (S i)) (e := e_var mb) (x := x).
  { apply wf_kmid2. }
  { unfold kmid2, kmid3; eauto with locc. }
  { unfold kmid3, kempty; eauto with locc. }
  apply rule_comm_done. cbn. split; reflexivity.
Qed.

(** ** The local row of a round ****************************************

    Backward through [accept ; CNOT ; Meas] on each side.  The assertion is
    no longer [distill_post] at the intermediate points — the measurement
    rule appends [ma = ya] and [mb = yb] — so the guard argument has to be
    stated for any assertion that pins the latch rather than for
    [distill_post] alone. *)

Definition ya : var := 10%nat.
Definition yb : var := 11%nat.

Lemma guard_a_contra : forall n (Q R : assertion (4 * S n)),
    (forall s, formula_holds (Sig n) s (classical_part Q) = true ->
               (s da = 1)%nat) ->
    and_guard Q guard_a true ⊨[Sig n] R.
Proof.
  intros n Q R HQ.
  assert (Hf : forall s, formula_holds (Sig n) s
                 (classical_part (and_guard Q guard_a true)) = false).
  { intro s. cbn [and_guard classical_part].
    destruct (formula_holds (Sig n) s (classical_part Q)) eqn:E.
    - pose proof (HQ s E) as Hlatch.
      cbn [and_guard classical_part formula_holds]. rewrite E. cbn [andb].
      cbn. destruct (s da) as [| [| d]]; cbn in Hlatch |- *; try lia;
        rewrite ?andb_false_r; reflexivity.
    - cbn [and_guard classical_part formula_holds]. rewrite E. reflexivity. }
  split; [| split];
    [ intros s Hs | intros s Hs | intros s M N Hs ];
    rewrite Hf in Hs; discriminate.
Qed.

Lemma guard_b_contra : forall n (Q R : assertion (4 * S n)),
    (forall s, formula_holds (Sig n) s (classical_part Q) = true ->
               (s db = 1)%nat) ->
    and_guard Q guard_b true ⊨[Sig n] R.
Proof.
  intros n Q R HQ.
  assert (Hf : forall s, formula_holds (Sig n) s
                 (classical_part (and_guard Q guard_b true)) = false).
  { intro s. cbn [and_guard classical_part].
    destruct (formula_holds (Sig n) s (classical_part Q)) eqn:E.
    - pose proof (HQ s E) as Hlatch.
      cbn [and_guard classical_part formula_holds]. rewrite E. cbn [andb].
      cbn. destruct (s db) as [| [| d]]; cbn in Hlatch |- *; try lia;
        rewrite ?andb_false_r; reflexivity.
    - cbn [and_guard classical_part formula_holds]. rewrite E. reflexivity. }
  split; [| split];
    [ intros s Hs | intros s Hs | intros s M N Hs ];
    rewrite Hf in Hs; discriminate.
Qed.

(** ** The probe of an idle round *************************************

    Round [j = S i] comes after the accepting round, so [post_q k n] leaves
    its four qubits free.  That is what lets the two parties be handled
    SEPARATELY: neither outcome constrains the other, each party's two
    outcomes already sum to the identity on its own qubit, and the
    assertion between the two halves is [distill_post k n] again.  (In the
    accepting and rejecting rounds the outcomes are correlated and the
    merge has to span both halves.)

    Each half is [accept ; CNOT ; Meas].  The accept test is a no-op
    ([accept_a_noop]), and the probe takes four steps, read backwards:

      Meas          fresh [ya]                    appends [ma = ya]
      Unitary       backwards                     conjugates by CNOT
      Aux-Subst     pins [ya := v]                closes the branch
      Branch-Accum  sums [v = 0, 1]               yields [ma=0 ∨ ma=1]

    Both of the last two are used at the LOCAL judgment.  At [⊢ₚ] neither
    applies: [ma = ya] is what separates the branches, and the next round's
    measurement overwrites it long before the program terminates. *)

(** *** Substituting a variable a formula does not mention **************

    The probe lemma below is stated for an ARBITRARY classical part — the
    accepting round hands it a half-latched state, not [Acc k] — and both
    Meas and Aux-Subst substitute into that part. *)

Fixpoint expr_subst_notin (x : var) (t : expr) (e : expr) {struct e} :
    ~ In x (expr_vars e) -> expr_subst e x t = e.
Proof.
  destruct e as [v | w | f es]; cbn; intro Hx.
  - reflexivity.
  - destruct (Nat.eqb x w) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E; subst; exfalso; apply Hx; left; reflexivity.
  - f_equal. induction es as [| e0 es' IHes]; cbn in *; [reflexivity |].
    f_equal.
    + apply expr_subst_notin. intro Hin; apply Hx, in_or_app; left; exact Hin.
    + apply IHes. intro Hin; apply Hx, in_or_app; right; exact Hin.
Qed.

Lemma map_expr_subst_notin : forall es x t,
    ~ In x (flat_map expr_vars es) ->
    map (fun e => expr_subst e x t) es = es.
Proof.
  induction es as [| e0 es' IH]; intros x t Hx; cbn in *; [reflexivity |].
  f_equal.
  - apply expr_subst_notin. intro Hin; apply Hx, in_or_app; left; exact Hin.
  - apply IH. intro Hin; apply Hx, in_or_app; right; exact Hin.
Qed.

Lemma bexpr_subst_notin : forall b x t,
    ~ In x (bexpr_vars b) -> bexpr_subst b x t = b.
Proof.
  intros b x t.
  induction b as [ | | R es | b1 IH1 | b1 IH1 b2 IH2 | b1 IH1 b2 IH2 ];
    cbn; intro Hx.
  - reflexivity.
  - reflexivity.
  - f_equal. apply map_expr_subst_notin; exact Hx.
  - rewrite IH1; [reflexivity | exact Hx].
  - rewrite IH1, IH2; [reflexivity | |];
      intro Hin; apply Hx, in_or_app; auto.
  - rewrite IH1, IH2; [reflexivity | |];
      intro Hin; apply Hx, in_or_app; auto.
Qed.

Lemma formula_subst_notin : forall p x t,
    ~ In x (formula_vars p) -> formula_subst p x t = p.
Proof.
  intros p x t.
  induction p as [ b | e1 e2 | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 ];
    cbn; intro Hx.
  - f_equal. apply bexpr_subst_notin; exact Hx.
  - f_equal; apply expr_subst_notin;
      intro Hin; apply Hx, in_or_app; auto.
  - rewrite IH1; [reflexivity | exact Hx].
  - rewrite IH1, IH2; [reflexivity | |];
      intro Hin; apply Hx, in_or_app; auto.
  - rewrite IH1, IH2; [reflexivity | |];
      intro Hin; apply Hx, in_or_app; auto.
Qed.

(** *** The pieces of one branch *************************************** *)

(** Every assertion the round's derivation meets has the SAME quantum part
    — [post_q k n], a constant family — and differs only classically.  The
    accept tests move the classical part around; the probes leave it
    alone. *)
Definition qpost (k n : nat) : qpred (4 * S n) :=
  q_op (fun _ => Some (post_q k n)) nil.

Definition at_q (phi : formula) (k n : nat) : assertion (4 * S n) :=
  mk_assertion phi (qpost k n).

Definition psi_a (phi : formula) (v : nat) : formula :=
  f_and phi (f_eq (e_var ma) (e_val v)).
Definition psi_b (phi : formula) (v : nat) : formula :=
  f_and phi (f_eq (e_var mb) (e_val v)).

(** The branch precondition, exactly as Unitary/Meas/Aux-Subst hand it out.
    After the substitution the outcome is a literal, so the qpred no longer
    reads the store — which is what makes the sum below a matrix fact.
    Note the quantum part does not depend on [phi]. *)
Definition Apre (n k j v : nat) (phi : formula) : assertion (4 * S n) :=
  assertion_subst
    (wp_unitary (i_uu (Sig n) CNOT (Ak j :: At j :: nil))
       (wp_meas (Sig n) Meas (At j :: nil) ya
          (assertion_subst (at_q phi k n) ma (e_var ya))))
    ya (e_val v).

Definition Bpre (n k j v : nat) (phi : formula) : assertion (4 * S n) :=
  assertion_subst
    (wp_unitary (i_uu (Sig n) CNOT (Bk j :: Bt j :: nil))
       (wp_meas (Sig n) Meas (Bt j :: nil) yb
          (assertion_subst (at_q phi k n) mb (e_var yb))))
    yb (e_val v).

Definition fam_a (n k j : nat) (phi : formula)
  : list (qpred (4 * S n) * formula) :=
  (quantum_part (Apre n k j 0%nat phi), psi_a phi 0%nat)
  :: (quantum_part (Apre n k j 1%nat phi), psi_a phi 1%nat) :: nil.

Definition fam_b (n k j : nat) (phi : formula)
  : list (qpred (4 * S n) * formula) :=
  (quantum_part (Bpre n k j 0%nat phi), psi_b phi 0%nat)
  :: (quantum_part (Bpre n k j 1%nat phi), psi_b phi 1%nat) :: nil.

(** *** The classical side of the merge ******************************* *)

Lemma psi_a_ma : forall n phi v s,
    formula_holds (Sig n) s (psi_a phi v) = true -> s ma = v.
Proof.
  intros n phi v s H. unfold psi_a in H.
  change (formula_holds (Sig n) s (f_and phi (f_eq (e_var ma) (e_val v))))
    with (andb (formula_holds (Sig n) s phi) (Nat.eqb (s ma) v)) in H.
  apply andb_true_iff in H as [_ H]. apply Nat.eqb_eq in H. exact H.
Qed.

Lemma psi_b_mb : forall n phi v s,
    formula_holds (Sig n) s (psi_b phi v) = true -> s mb = v.
Proof.
  intros n phi v s H. unfold psi_b in H.
  change (formula_holds (Sig n) s (f_and phi (f_eq (e_var mb) (e_val v))))
    with (andb (formula_holds (Sig n) s phi) (Nat.eqb (s mb) v)) in H.
  apply andb_true_iff in H as [_ H]. apply Nat.eqb_eq in H. exact H.
Qed.

Lemma psi_a_drop : forall n phi v s,
    formula_holds (Sig n) s (psi_a phi v) = true ->
    formula_holds (Sig n) s phi = true.
Proof.
  intros n phi v s H. unfold psi_a in H.
  change (formula_holds (Sig n) s (f_and phi (f_eq (e_var ma) (e_val v))))
    with (andb (formula_holds (Sig n) s phi) (Nat.eqb (s ma) v)) in H.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma psi_b_drop : forall n phi v s,
    formula_holds (Sig n) s (psi_b phi v) = true ->
    formula_holds (Sig n) s phi = true.
Proof.
  intros n phi v s H. unfold psi_b in H.
  change (formula_holds (Sig n) s (f_and phi (f_eq (e_var mb) (e_val v))))
    with (andb (formula_holds (Sig n) s phi) (Nat.eqb (s mb) v)) in H.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

(** [⋁ψ ⊨ φ] whenever every disjunct entails φ — the classical half of the
    Conseq step that follows Branch-Accum. *)
Lemma fdisj_elim : forall d (S0 : interp d) s ps (q : formula),
    Forall (fun p => formula_holds S0 s p = true ->
                     formula_holds S0 s q = true) ps ->
    formula_holds S0 s (fdisj ps) = true ->
    formula_holds S0 s q = true.
Proof.
  intros d S0 s ps q HF. induction HF as [| p ps' Hp HF' IH].
  - intro H. cbn in H. discriminate.
  - intro H.
    change (formula_holds S0 s (fdisj (p :: ps')))
      with (orb (formula_holds S0 s p) (formula_holds S0 s (fdisj ps'))) in H.
    apply orb_true_iff in H as [H | H]; [ apply Hp | apply IH ]; exact H.
Qed.

(** *** The quantum side of the merge ********************************* *)

(** [DistillationComplete] repeats the predicates verbatim so that its
    obligations close by conversion here.  Nothing enforces that but this
    check: if the two copies ever drift apart, [reflexivity] stops working
    and the [change] steps below break with it. *)
Lemma post_q_C : forall k n, post_q k n = DistillationComplete.post_q k n.
Proof. reflexivity. Qed.

Lemma qsum_a_idle : forall n k j phi,
    (k < j)%nat -> (j <= n)%nat -> forall s,
    qpred_denote (Sig n) s (qsum (map fst (fam_a n k j phi)))
    = Some (post_q k n).
Proof.
  intros n k j phi Hkj Hjn s.
  change (qpred_denote (Sig n) s (qsum (map fst (fam_a n k j phi))))
    with (Some (DistillationComplete.wpA n j 0 (DistillationComplete.post_q k n)
                .+ (DistillationComplete.wpA n j 1 (DistillationComplete.post_q k n)
                    .+ @Zero (2 ^ (4 * S n)) (2 ^ (4 * S n))))).
  rewrite Mplus_0_r, (DistillationComplete.wpA_sum_idle n k j Hkj Hjn).
  reflexivity.
Qed.

Lemma qsum_b_idle : forall n k j phi,
    (k < j)%nat -> (j <= n)%nat -> forall s,
    qpred_denote (Sig n) s (qsum (map fst (fam_b n k j phi)))
    = Some (post_q k n).
Proof.
  intros n k j phi Hkj Hjn s.
  change (qpred_denote (Sig n) s (qsum (map fst (fam_b n k j phi))))
    with (Some (DistillationComplete.wpB n j 0 (DistillationComplete.post_q k n)
                .+ (DistillationComplete.wpB n j 1 (DistillationComplete.post_q k n)
                    .+ @Zero (2 ^ (4 * S n)) (2 ^ (4 * S n))))).
  rewrite Mplus_0_r, (DistillationComplete.wpB_sum_idle n k j Hkj Hjn).
  reflexivity.
Qed.

(** *** The two conseq steps ****************************************** *)

Lemma entails_q_eq : forall d (S0 : interp d) (phi psi : formula) (A B : qpred d),
    (forall s, formula_holds S0 s phi = true -> formula_holds S0 s psi = true) ->
    (forall s, formula_holds S0 s phi = true ->
               qpred_denote S0 s A = qpred_denote S0 s B) ->
    mk_assertion phi A ⊨[S0] mk_assertion psi B.
Proof.
  intros d S0 phi psi A B Hc Hq. split; [| split].
  - exact Hc.
  - intros s Hs [M HM]. exists M. cbn in HM |- *.
    rewrite <- (Hq s Hs). exact HM.
  - intros s M N Hs HM HN. cbn in HM, HN.
    rewrite (Hq s Hs) in HM. rewrite HM in HN. inversion HN. apply lowner_refl.
Qed.

Lemma wf_at_q : forall n k phi, (k <= n)%nat ->
    wf_assertion (Sig n) (at_q phi k n).
Proof.
  intros n k phi Hk s M HM. cbn in HM. inversion HM; subst.
  apply is_effect_post_q; exact Hk.
Qed.

(** *** One branch, and the merge ************************************* *)

Lemma probe_a_branch : forall n k j v phi,
    ~ In ma (formula_vars phi) -> ~ In ya (formula_vars phi) ->
    Sig n ⊢ₗ {{ mk_assertion phi (quantum_part (Apre n k j v phi)) }}
             probe_a j
             {{ mk_assertion (psi_a phi v) (qpost k n) }}.
Proof.
  intros n k j v phi Hma Hya.
  assert (Hs1 : formula_subst phi ma (e_var ya) = phi)
    by (apply formula_subst_notin; exact Hma).
  assert (Hs2 : forall (w : val), formula_subst phi ya (e_val w) = phi)
    by (intro w; apply formula_subst_notin; exact Hya).
  replace (mk_assertion phi (quantum_part (Apre n k j v phi)))
     with (Apre n k j v phi).
  2:{ unfold Apre, at_q, assertion_subst, wp_unitary, wp_meas, mk_assertion;
      cbn [classical_part quantum_part].
      rewrite Hs1, Hs2. reflexivity. }
  replace (mk_assertion (psi_a phi v) (qpost k n))
     with (assertion_subst (and_eq (at_q phi k n) ma ya) ya (e_val v)).
  2:{ unfold and_eq, at_q, assertion_subst, mk_assertion, psi_a, qpost;
      unfold ya, ma;
      cbn [classical_part quantum_part formula_subst expr_subst qpred_subst
           map Nat.eqb].
      rewrite Hs2. reflexivity. }
  unfold Apre, probe_a.
  apply rule_aux_subst_l.
  - cbn [lblock_change app In]. unfold ya, ma. intuition lia.
  - cbn [lblock_read app In]. intuition.
  - eapply rule_seq; [ apply rule_unitary | apply rule_meas ].
    + unfold ya, ma. lia.
    + unfold at_q, assertion_vars, mk_assertion, qpost;
        cbn [classical_part quantum_part qpred_vars flat_map].
      rewrite app_nil_r. exact Hya.
Qed.

Lemma probe_b_branch : forall n k j v phi,
    ~ In mb (formula_vars phi) -> ~ In yb (formula_vars phi) ->
    Sig n ⊢ₗ {{ mk_assertion phi (quantum_part (Bpre n k j v phi)) }}
             probe_b j
             {{ mk_assertion (psi_b phi v) (qpost k n) }}.
Proof.
  intros n k j v phi Hmb Hyb.
  assert (Hs1 : formula_subst phi mb (e_var yb) = phi)
    by (apply formula_subst_notin; exact Hmb).
  assert (Hs2 : forall (w : val), formula_subst phi yb (e_val w) = phi)
    by (intro w; apply formula_subst_notin; exact Hyb).
  replace (mk_assertion phi (quantum_part (Bpre n k j v phi)))
     with (Bpre n k j v phi).
  2:{ unfold Bpre, at_q, assertion_subst, wp_unitary, wp_meas, mk_assertion;
      cbn [classical_part quantum_part].
      rewrite Hs1, Hs2. reflexivity. }
  replace (mk_assertion (psi_b phi v) (qpost k n))
     with (assertion_subst (and_eq (at_q phi k n) mb yb) yb (e_val v)).
  2:{ unfold and_eq, at_q, assertion_subst, mk_assertion, psi_b, qpost;
      unfold yb, mb;
      cbn [classical_part quantum_part formula_subst expr_subst qpred_subst
           map Nat.eqb].
      rewrite Hs2. reflexivity. }
  unfold Bpre, probe_b.
  apply rule_aux_subst_l.
  - cbn [lblock_change app In]. unfold yb, mb. intuition lia.
  - cbn [lblock_read app In]. intuition.
  - eapply rule_seq; [ apply rule_unitary | apply rule_meas ].
    + unfold yb, mb. lia.
    + unfold at_q, assertion_vars, mk_assertion, qpost;
        cbn [classical_part quantum_part qpred_vars flat_map].
      rewrite app_nil_r. exact Hyb.
Qed.

(** The probe of a round the assertion leaves free, for any classical part
    the probe cannot touch. *)
Lemma probe_a_step : forall n k j phi,
    (k <= n)%nat -> (k < j)%nat -> (j <= n)%nat ->
    ~ In ma (formula_vars phi) -> ~ In ya (formula_vars phi) ->
    Sig n ⊢ₗ {{ at_q phi k n }} probe_a j {{ at_q phi k n }}.
Proof.
  intros n k j phi Hkn Hkj Hjn Hma Hya.
  eapply rule_conseq with
    (Q := mk_assertion phi (qsum (map fst (fam_a n k j phi))))
    (R := mk_assertion (fdisj (map snd (fam_a n k j phi))) (qpost k n)).
  - apply entails_q_eq.
    + intros s H; exact H.
    + intros s _. rewrite (qsum_a_idle n k j phi Hkj Hjn s). reflexivity.
  - apply rule_branch_accum_l.
    + repeat constructor; apply probe_a_branch; assumption.
    + repeat constructor. intros s H0 H1.
      apply psi_a_ma in H0. apply psi_a_ma in H1. lia.
    + intros s. exists (post_q k n). apply qsum_a_idle; assumption.
  - apply entails_q_eq.
    + intros s H.
      apply (fdisj_elim _ (Sig n) s (map snd (fam_a n k j phi)) phi); [| exact H].
      repeat constructor; intro H'; eapply psi_a_drop; exact H'.
    + intros s _. reflexivity.
  - apply wf_at_q; exact Hkn.
Qed.

Lemma probe_b_step : forall n k j phi,
    (k <= n)%nat -> (k < j)%nat -> (j <= n)%nat ->
    ~ In mb (formula_vars phi) -> ~ In yb (formula_vars phi) ->
    Sig n ⊢ₗ {{ at_q phi k n }} probe_b j {{ at_q phi k n }}.
Proof.
  intros n k j phi Hkn Hkj Hjn Hmb Hyb.
  eapply rule_conseq with
    (Q := mk_assertion phi (qsum (map fst (fam_b n k j phi))))
    (R := mk_assertion (fdisj (map snd (fam_b n k j phi))) (qpost k n)).
  - apply entails_q_eq.
    + intros s H; exact H.
    + intros s _. rewrite (qsum_b_idle n k j phi Hkj Hjn s). reflexivity.
  - apply rule_branch_accum_l.
    + repeat constructor; apply probe_b_branch; assumption.
    + repeat constructor. intros s H0 H1.
      apply psi_b_mb in H0. apply psi_b_mb in H1. lia.
    + intros s. exists (post_q k n). apply qsum_b_idle; assumption.
  - apply entails_q_eq.
    + intros s H.
      apply (fdisj_elim _ (Sig n) s (map snd (fam_b n k j phi)) phi); [| exact H].
      repeat constructor; intro H'; eapply psi_b_drop; exact H'.
    + intros s _. reflexivity.
  - apply wf_at_q; exact Hkn.
Qed.

(* [Acc k] mentions only the six latch variables, none of them an outcome
   or an auxiliary. *)
Ltac fresh_in := cbn [formula_vars Acc expr_vars app];
  unfold ma, mb, ya, yb, ia, da, oa, ib, db, ob, x, y;
  cbn [In]; intuition lia.

Lemma probe_a_idle : forall n k j,
    (k <= n)%nat -> (k < j)%nat -> (j <= n)%nat ->
    Sig n ⊢ₗ {{ distill_post k n }} probe_a j {{ distill_post k n }}.
Proof.
  intros n k j Hkn Hkj Hjn.
  apply (probe_a_step n k j (Acc k)); try assumption; fresh_in.
Qed.

Lemma probe_b_idle : forall n k j,
    (k <= n)%nat -> (k < j)%nat -> (j <= n)%nat ->
    Sig n ⊢ₗ {{ distill_post k n }} probe_b j {{ distill_post k n }}.
Proof.
  intros n k j Hkn Hkj Hjn.
  apply (probe_b_step n k j (Acc k)); try assumption; fresh_in.
Qed.

(** The local row of an idle round: accept (a no-op), probe (the merge),
    on each side in turn. *)
Lemma disj_dmid : forall i, lrow_disj (dmid i).
Proof.
  intro i; unfold dmid, lrow_disj, DisjMP.
  cbn [row_leaves app].
  constructor; [ constructor; [| constructor] | constructor; [constructor | constructor] ].
  unfold non_interfering, mid_a, mid_b, accept_a, accept_b, probe_a, probe_b.
  cbn [lblock_change lblock_read lblock_qvar bexpr_vars expr_vars app flat_map].
  unfold ia, da, oa, ma, x, ib, db, ob, mb, y, Ak, At, Bk, Bt.
  repeat split; intros v Hv Hw; cbn in Hv, Hw; intuition lia.
Qed.

Lemma dmid_local_idle : forall n k i,
    (k <= n)%nat -> (k < S i)%nat -> (S i <= n)%nat ->
    Sig n ⊢ₗ {{ distill_post k n }} lseq (dmid i) {{ distill_post k n }}.
Proof.
  intros n k i Hkn Hki Hin. cbn [lseq dmid].
  unfold mid_a, mid_b.
  eapply rule_seq with (Q2 := distill_post k n).
  - eapply rule_seq with (Q2 := distill_post k n).
    + apply accept_a_noop; exact Hkn.
    + apply probe_a_idle; assumption.
  - eapply rule_seq with (Q2 := distill_post k n).
    + apply accept_b_noop; exact Hkn.
    + apply probe_b_idle; assumption.
Qed.

(** ** The three phases of the derivation ******************************

    Stated in the specification section above; proved here, where the
    machinery they stand on is in scope. *)

(** i > k.  [da = 1], so every remaining accept test takes its else branch,
    and every remaining probe acts on a round the postcondition leaves
    free — the weakest precondition of [I] under a unitary is [I], and
    under a measurement it is [Σ_m M_m† M_m = I].  Induction on [r], with
    [i] generalised so the step can instantiate the hypothesis at [S i].

    [i + r <= n] says round [i + r], the last one this tail probes, is a
    round of the program; the case study never needs the triple outside
    that range, and [wpA_sum_idle] is a statement about a round that
    exists. *)
Lemma phase_after : forall n k r i,
    (k <= n)%nat -> (k <= i)%nat -> (i + r <= n)%nat ->
    Sig n ⊢ₚ {{ distill_post k n }} tround i r {{ distill_post k n }}.
Proof.
  intros n k r. induction r as [| r' IH]; intros i Hkn Hki Hir.
  - apply phase_after_base; exact Hkn.
  - eapply rule_par_comp with (d := dmid i) (k := kmid i) (t := tround (S i) r')
                              (Q1 := distill_post k n) (Q2 := distill_post k n).
    + exact (cut_step i r').
    + exact (wf_program_tround i (S r')).
    + apply wf_distill_post; exact Hkn.
    + apply wf_distill_post; exact Hkn.
    + apply rule_par_disjoint;
        [ apply disj_dmid | apply dmid_local_idle; lia ].
    + apply kmid_comm.
    + apply IH; lia.
Qed.

(** ** The accepting round ********************************************

    [tround k _] opens with round [k]'s accept test, and under [acc_at k n]
    the guard is LIVE: [da = 0] (nothing has latched) and [ma = x] (the two
    outcomes agreed).  So both tests fire, one after the other, and between
    them the state is half-latched — Alice has recorded [k+1], Bob has not.
    That intermediate assertion still has to decide Bob's guard, which is
    why [mb = y] survives into it. *)

Definition AccA (k : nat) : formula :=
  f_and (f_and (f_and (f_eq (e_var da) (e_val 1%nat)) (f_eq (e_var oa) (e_val 1%nat)))
               (f_eq (e_var ia) (e_val (S k))))
        (f_and (f_and (f_eq (e_var db) (e_val 0%nat)) (f_eq (e_var ob) (e_val 0%nat)))
               (f_and (f_eq (e_var ib) (e_val 0%nat)) (f_eq (e_var mb) (e_var y)))).

Ltac accA_fresh :=
  cbn [formula_vars AccA expr_vars app];
  unfold ma, mb, ya, yb, ia, da, oa, ib, db, ob, x, y;
  cbn [In]; intuition lia.

(** The counterpart of [guard_a_contra]: an assertion that pins [da = 0]
    and [ma = x] makes the ELSE branch unreachable. *)
Lemma guard_a_live : forall n (Q R : assertion (4 * S n)),
    (forall s, formula_holds (Sig n) s (classical_part Q) = true ->
               s da = 0%nat /\ s ma = s x) ->
    and_guard Q guard_a false ⊨[Sig n] R.
Proof.
  intros n Q R HQ.
  assert (Hf : forall s, formula_holds (Sig n) s
                 (classical_part (and_guard Q guard_a false)) = false).
  { intro s. cbn [and_guard classical_part formula_holds].
    destruct (formula_holds (Sig n) s (classical_part Q)) eqn:E; [| reflexivity].
    destruct (HQ s E) as [Hd Hm]. cbn [andb].
    cbn. rewrite Hd, Hm, !Nat.eqb_refl. reflexivity. }
  split; [| split];
    [ intros s Hs | intros s Hs | intros s M N Hs ];
    rewrite Hf in Hs; discriminate.
Qed.

Lemma guard_b_live : forall n (Q R : assertion (4 * S n)),
    (forall s, formula_holds (Sig n) s (classical_part Q) = true ->
               s db = 0%nat /\ s mb = s y) ->
    and_guard Q guard_b false ⊨[Sig n] R.
Proof.
  intros n Q R HQ.
  assert (Hf : forall s, formula_holds (Sig n) s
                 (classical_part (and_guard Q guard_b false)) = false).
  { intro s. cbn [and_guard classical_part formula_holds].
    destruct (formula_holds (Sig n) s (classical_part Q)) eqn:E; [| reflexivity].
    destruct (HQ s E) as [Hd Hm]. cbn [andb].
    cbn. rewrite Hd, Hm, !Nat.eqb_refl. reflexivity. }
  split; [| split];
    [ intros s Hs | intros s Hs | intros s M N Hs ];
    rewrite Hf in Hs; discriminate.
Qed.

(** Reading the two classical parts back as store facts. *)
Lemma acc_at_vals : forall n k s,
    formula_holds (Sig n) s (classical_part (acc_at k n)) = true ->
    s da = 0%nat /\ s db = 0%nat /\ s oa = 0%nat /\ s ob = 0%nat
    /\ s ia = 0%nat /\ s ib = 0%nat /\ s ma = s x /\ s mb = s y.
Proof.
  intros n k s H. cbn in H. rewrite !andb_true_iff in H.
  destruct H as [[[[Hda Hdb] [Hoa Hob]] [Hia Hib]] [Hma Hmb]].
  repeat split; apply Nat.eqb_eq; assumption.
Qed.

Lemma AccA_vals : forall n k s,
    formula_holds (Sig n) s (AccA k) = true ->
    s da = 1%nat /\ s oa = 1%nat /\ s ia = S k
    /\ s db = 0%nat /\ s ob = 0%nat /\ s ib = 0%nat /\ s mb = s y.
Proof.
  intros n k s H. cbn in H. rewrite !andb_true_iff in H.
  destruct H as [[[Hda Hoa] Hia] [[Hdb Hob] [Hib Hmb]]].
  repeat split; apply Nat.eqb_eq; assumption.
Qed.

Lemma accept_a_fire : forall n k, (k <= n)%nat ->
    Sig n ⊢ₗ {{ acc_at k n }} accept_a k {{ at_q (AccA k) k n }}.
Proof.
  intros n k Hk. apply rule_if.
  - eapply rule_conseq with (R := at_q (AccA k) k n);
      [ | eapply rule_seq; [apply rule_assign |];
          eapply rule_seq; [apply rule_assign | apply rule_assign]
      | apply entails_refl
      | apply wf_at_q; exact Hk ].
    apply entails_q_eq; [| intros s _; reflexivity ].
    intros s Hs.
    change (formula_holds (Sig n) s
              (f_and (classical_part (acc_at k n)) (f_bexp guard_a)))
      with (andb (formula_holds (Sig n) s (classical_part (acc_at k n)))
                 (formula_holds (Sig n) s (f_bexp guard_a))) in Hs.
    apply andb_true_iff in Hs as [Hs _].
    destruct (acc_at_vals n k s Hs)
      as (Hda & Hdb & Hoa & Hob & Hia & Hib & Hma & Hmb).
    cbn. rewrite Hdb, Hob, Hib, Hmb, !Nat.eqb_refl. reflexivity.
  - eapply rule_conseq with (R := at_q (AccA k) k n);
      [ | apply rule_skip | apply entails_refl | apply wf_at_q; exact Hk ].
    apply guard_a_live. intros s Hs.
    destruct (acc_at_vals n k s Hs)
      as (Hda & Hdb & Hoa & Hob & Hia & Hib & Hma & Hmb).
    split; assumption.
Qed.

Lemma accept_b_fire : forall n k, (k <= n)%nat ->
    Sig n ⊢ₗ {{ at_q (AccA k) k n }} accept_b k {{ distill_post k n }}.
Proof.
  intros n k Hk. apply rule_if.
  - eapply rule_conseq with (R := distill_post k n);
      [ | eapply rule_seq; [apply rule_assign |];
          eapply rule_seq; [apply rule_assign | apply rule_assign]
      | apply entails_refl
      | apply wf_distill_post; exact Hk ].
    apply entails_q_eq; [| intros s _; reflexivity ].
    intros s Hs.
    change (formula_holds (Sig n) s
              (f_and (classical_part (at_q (AccA k) k n)) (f_bexp guard_b)))
      with (andb (formula_holds (Sig n) s (classical_part (at_q (AccA k) k n)))
                 (formula_holds (Sig n) s (f_bexp guard_b))) in Hs.
    apply andb_true_iff in Hs as [Hs _].
    destruct (AccA_vals n k s Hs) as (Hda & Hoa & Hia & Hdb & Hob & Hib & Hmb).
    cbn. rewrite Hda, Hoa, Hia, !Nat.eqb_refl. reflexivity.
  - eapply rule_conseq with (R := distill_post k n);
      [ | apply rule_skip | apply entails_refl | apply wf_distill_post; exact Hk ].
    apply guard_b_live. intros s Hs.
    destruct (AccA_vals n k s Hs) as (Hda & Hoa & Hia & Hdb & Hob & Hib & Hmb).
    split; assumption.
Qed.

Lemma dlast_accept : forall n k, (k <= n)%nat ->
    Sig n ⊢ₗ {{ acc_at k n }} lseq (dlast k) {{ distill_post k n }}.
Proof.
  intros n k Hk. cbn [lseq dlast].
  eapply rule_seq with (Q2 := at_q (AccA k) k n);
    [ apply accept_a_fire | apply accept_b_fire ]; exact Hk.
Qed.

Lemma dmid_accept : forall n k, (k <= n)%nat -> (S k <= n)%nat ->
    Sig n ⊢ₗ {{ acc_at k n }} lseq (dmid k) {{ distill_post k n }}.
Proof.
  intros n k Hk Hk1. cbn [lseq dmid]. unfold mid_a, mid_b.
  eapply rule_seq with (Q2 := at_q (AccA k) k n).
  - eapply rule_seq with (Q2 := at_q (AccA k) k n).
    + apply accept_a_fire; exact Hk.
    + apply probe_a_step; try lia; accA_fresh.
  - eapply rule_seq with (Q2 := distill_post k n).
    + apply accept_b_fire; exact Hk.
    + apply probe_b_idle; lia.
Qed.

(** i = k.  One [Par-Comp-MP] step: both accept tests fire, turning
    [Zeros /\ Agree] into [Acc k] and leaving the quantum part alone; round
    [k+1]'s probe is already idle, and the rest is [phase_after]. *)
Lemma phase_accept : forall n k, (k <= n)%nat ->
    Sig n ⊢ₚ {{ acc_at k n }} tround k (n - k) {{ distill_post k n }}.
Proof.
  intros n k Hk. destruct (n - k)%nat as [| r'] eqn:Er.
  - eapply rule_par_comp with (d := dlast k) (k := kempty) (t := tdone)
                              (Q1 := distill_post k n) (Q2 := distill_post k n).
    + exact (cut_base k).
    + exact (wf_program_tround k 0).
    + apply wf_distill_post; exact Hk.
    + apply wf_distill_post; exact Hk.
    + apply rule_par_disjoint; [ apply disj_dlast | apply dlast_accept; exact Hk ].
    + apply rule_comm_done. cbn. split; reflexivity.
    + apply rule_done. exact tdone_terminated.
  - eapply rule_par_comp with (d := dmid k) (k := kmid k) (t := tround (S k) r')
                              (Q1 := distill_post k n) (Q2 := distill_post k n).
    + exact (cut_step k r').
    + exact (wf_program_tround k (S r')).
    + apply wf_distill_post; exact Hk.
    + apply wf_distill_post; exact Hk.
    + apply rule_par_disjoint; [ apply disj_dmid | apply dmid_accept; lia ].
    + apply kmid_comm.
    + apply phase_after; lia.
Qed.

(** i < k.  Induction on [d], the number of rejecting rounds still to come;
    [i + S d = k] ties it to the round index, because [k - i] is not
    structurally decreasing and [induction] will not take it. *)
Lemma phase_reject : forall n k d i,
    (k <= n)%nat -> (S i + d = k)%nat ->
    Sig n ⊢ₚ {{ inv_at (S i) k n }} tround i (n - i) {{ distill_post k n }}.
Admitted.
