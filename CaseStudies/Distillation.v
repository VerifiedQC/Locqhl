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
From Locqhl.Core Require Import Syntax Rules.
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

(* [l_seq] rather than [<{ _ ; _ }>]: inside the custom entry only an
   atomic constr parses, and [accept_a i] is an application.  Teleportation
   builds [bob_corr] the same way. *)
Definition mid_a (i : nat) : lblock :=
  l_seq (accept_a i)
        <{ CNOT @ [Ak (S i); At (S i)] ; ma <- Meas @ [At (S i)] }>.
Definition mid_b (i : nat) : lblock :=
  l_seq (accept_b i)
        <{ CNOT @ [Bk (S i); Bt (S i)] ; mb <- Meas @ [Bt (S i)] }>.

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
