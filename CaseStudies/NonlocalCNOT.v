From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import Syntax Names QuantumActions Semantics Assertions WellFormed Rules SoundnessFacts Soundness.
From Locqhl.CaseStudies Require NonlocalCNOTComplete.
Import ListNotations.
Open Scope proc_scope.

(** * Non-local CNOT — the program (paper §5.3, Figure 8b).

    Alice owns the control qubit C and her half A of a shared EPR pair;
    Bob owns the target qubit T and his half B.  The protocol implements a
    logical CNOT[C,T] using only local operations, the one EPR pair, and
    two classical bits — one in each direction.

    What makes this example different from teleportation and entanglement
    swapping, and the reason it is worth doing next:

      * TWO communication phases, in a CAUSAL handshake.  Alice's c1 is
        what ENABLES Bob's middle block, and Bob's c2 is what enables
        Alice's final Z correction.  Neither message can be commuted past
        the other — unlike the two same-phase messages of teleportation.
      * The second measurement (Bob's m2) sits in the SECOND phase's local
        prefix, not the first.  So the branch on m1 has to survive a
        rendezvous before the branch on m2 is even created, and the four
        (m1,m2) combinations are only recombined at the very top.
      * The specification is Choi-style: the reference qubits C' and T'
        appear in NO local block of the program.  They exist only in the
        assertion, which is what lets a Hoare triple pin down the action of
        the implemented channel on an ARBITRARY input.

    Qubit order.  A(0), B(1), C(2), C'(3), T(4), T'(5).  Two things at
    once: each of the three EPR pairs of the precondition occupies an
    ADJACENT pair of qubits, AND they come out in the order the paper
    writes them in Theorem 5.3, so the Coq precondition is that formula
    read left to right:

        pre  = EPR(A,B) ⊗ EPR(C,C') ⊗ EPR(T,T')     (pairs 0-1, 2-3, 4-5)

    Adjacency is the shape SwapComplete.v had to work to obtain, and it is
    what matters for the proof: the state is what the Cauchy-Schwarz step
    has to see through.  The logical gate is then the one that straddles —
    CNOT[C,T] is a pad_ctrl across the reference block — which is the cheap
    side of the trade, and the same trade SwapComplete made.

    The measured-out qubits A and B are the FIRST tensor factor, so the
    postcondition reads I ⊗ I ⊗ CNOTChoi rather than the CNOTChoi ⊗ I ⊗ I
    that Teleportation.v and EntanglementSwapping.v use.  That is the one
    house convention given up for the paper match; the paper writes no
    tensor order for its postcondition (the lifting convention supplies the
    I's), so nothing is lost against the paper by it.

           Alice                          Bob
      ─────────────────────────    ─────────────────────────
      CNOT[C,A];                   (idle)
      m1 <- Meas[A]
      c1!m1                        c1?i
      (idle)                       if i = 1 then X[B];
                                   CNOT[B,T]; H[B];
                                   m2 <- Meas[B]
      c2?j                         c2!m2
      if j = 1 then Z[C]           (done)
*)

Definition A  : qvar := 0%nat.   (* Alice's half of the shared pair *)
Definition B  : qvar := 1%nat.   (* Bob's half of the shared pair *)
Definition C  : qvar := 2%nat.   (* Alice: control *)
Definition C' : qvar := 3%nat.   (* reference for C — assertion only *)
Definition T  : qvar := 4%nat.   (* Bob: target *)
Definition T' : qvar := 5%nat.   (* reference for T — assertion only *)

Definition m1 : var := 0%nat.    (* Alice measures A *)
Definition i  : var := 1%nat.    (* Bob receives m1 *)
Definition m2 : var := 2%nat.    (* Bob measures B *)
Definition j  : var := 3%nat.    (* Alice receives m2 *)

Definition c1 : chan := 0%nat.   (* Alice → Bob *)
Definition c2 : chan := 1%nat.   (* Bob → Alice *)

Definition CNOT : usym := 0%nat.
Definition H    : usym := 1%nat.
Definition Z    : usym := 2%nat.
Definition X    : usym := 3%nat.
Definition Meas : msym := 0%nat.

(** The protocol.  Alice is L₀;K₀;L₁;K₁;L₂ with L₁ = skip; Bob is the
    mirror image, L₀ = skip and L₂ absent.  The padding is not cosmetic:
    it is what puts c1's two endpoints in phase 0 and c2's two in phase 1,
    which is Definition 2.1(3). *)
Definition rcnot : program :=
  ⟨ (* Alice *)
    <{ CNOT @ [C; A] ; m1 <- Meas @ [A] }>
    ⨾ [ c1 ‼ e_var m1 ]
    ⨾ ( <{ skip }>
        ⨾ [ c2 ⁇ j ]
        ⨾ ( <{ if (b_eq (e_var j) (e_val 1%nat)) then Z @ [C] else skip }>
            ⨾ ε ⨾ terminated ) ) ⟩
  ∥
  ⟨ (* Bob *)
    <{ skip }>
    ⨾ [ c1 ⁇ i ]
    ⨾ ( <{ (if (b_eq (e_var i) (e_val 1%nat)) then X @ [B] else skip) ;
           CNOT @ [B; T] ; H @ [B] ; m2 <- Meas @ [B] }>
        ⨾ [ c2 ‼ e_var m2 ]
        ⨾ terminated ) ⟩.

(** Named pieces of [rcnot], for stating the cut rows.  Everything below
    is definitionally equal to the corresponding subterm of [rcnot]. *)
Definition corr (U : usym) (b : var) (q : qvar) : lblock :=
  <{ if (b_eq (e_var b) (e_val 1%nat)) then U @ [q] else skip }>.

(** Alice's prefix: entangle the control into her EPR half, measure it.
    The measured bit says which X Bob must apply to line his half up. *)
Definition alice_pre : lblock :=
  <{ CNOT @ [C; A] ; m1 <- Meas @ [A] }>.

(** Bob's middle block — the one that only becomes available after c1.
    Correct, apply the real CNOT against his (now aligned) half, then
    disentangle it back out with H and a measurement. *)
Definition bob_mid : lblock :=
  l_seq (corr X i B)
        <{ CNOT @ [B; T] ; H @ [B] ; m2 <- Meas @ [B] }>.

(** Alice's final correction, enabled by c2. *)
Definition alice_corr : lblock := corr Z j C.

(** The tails, named so the three [cut] rounds can be read off. *)
Definition alice_tail : process :=
  <{ skip }> ⨾ [ c2 ⁇ j ] ⨾ ( alice_corr ⨾ ε ⨾ terminated ).

Definition bob_tail : process :=
  bob_mid ⨾ [ c2 ‼ e_var m2 ] ⨾ terminated.

(** ** The three Par-Comp-MP rounds ************************************

    Teleportation and entanglement swapping cut twice: one real phase,
    then an all-ε phase to run out the corrections.  This program cuts
    THREE times, and the middle round is the new one — a non-empty D-row
    (Bob's middle block, containing a measurement) sitting on top of a
    non-empty K-row (c2).  That combination never occurs in the other two
    case studies. *)

(* Round 1: Alice's Bell-style prefix, then the c1 rendezvous. *)
Definition d1 : lrow    := ⟨ alice_pre ⟩ ∥ ⟨ l_skip ⟩.
Definition k1 : krow    := ⟨ [c1 ‼ e_var m1] ⟩ ∥ ⟨ [c1 ⁇ i] ⟩.
Definition t1 : program := ⟨ alice_tail ⟩ ∥ ⟨ bob_tail ⟩.

(* Round 2: Bob's middle block — the measurement that creates the SECOND
   branch — then the c2 rendezvous back to Alice. *)
Definition d2 : lrow    := ⟨ l_skip ⟩ ∥ ⟨ bob_mid ⟩.
Definition k2 : krow    := ⟨ [c2 ⁇ j] ⟩ ∥ ⟨ [c2 ‼ e_var m2] ⟩.
Definition t2 : program := ⟨ alice_corr ⨾ ε ⨾ terminated ⟩ ∥ ⟨ terminated ⟩.

(* Round 3: Alice's Z correction, no communication left. *)
Definition d3 : lrow    := ⟨ alice_corr ⟩ ∥ ⟨ l_skip ⟩.
Definition k3 : krow    := ⟨ ε ⟩ ∥ ⟨ ε ⟩.
Definition t3 : program := ⟨ terminated ⟩ ∥ ⟨ terminated ⟩.

(** These are the rows [cut] actually produces — Bob's leaf is already ↓
    in round 3 and [cut] pads it, as does Alice's in round 2. *)
Lemma rcnot_cut : cut rcnot = (d1, k1, t1).
Proof. reflexivity. Qed.

Lemma rcnot_cut_tail : cut t1 = (d2, k2, t2).
Proof. reflexivity. Qed.

Lemma rcnot_cut_tail2 : cut t2 = (d3, k3, t3).
Proof. reflexivity. Qed.

Lemma t3_terminated : prog_terminated t3.
Proof. split; reflexivity. Qed.

(** ** Definition 2.1 for [rcnot] **************************************

    Ownership: Alice writes {m1, j} and touches {C, A}; Bob writes {i, m2}
    and touches {T, B}.  The reference qubits C' and T' are touched by
    neither, which is exactly what makes the Choi specification legitimate
    — they are pure assertion-level bookkeeping.

    Channels: c1 carries one send (Alice) and one receive (Bob), c2 the
    other way, each pair in its own phase.  Phase independence is then
    trivial — one message per phase, so there is nothing to commute.

    Note what does NOT force the two-phase split.  Def 2.1(4) would be
    satisfied by a single phase containing all four endpoints (recv =
    {i,j}, oread = {m1,m2}, disjoint).  What forbids it is the process
    SHAPE, p.7: m2 does not exist until Bob's middle block has run, and a
    local block cannot sit inside a communication block.  "A send that
    depends on a value received in the same communication phase must be
    placed after a local block in a later communication phase" — that
    sentence is this protocol.  The causality is carried by the
    alternation, and phase independence is what stays cheap because of
    it. *)
Lemma rcnot_wf_program : wf_program rcnot.
Proof.
  split; [| split; [| split]].
  - repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
  - intros c Hc; vm_compute in Hc.
    destruct Hc as [Hc | [Hc | [Hc | [Hc | []]]]]; subst c;
      repeat split; reflexivity.
  (* Three phases, not two: [destruct n] has to reach 2 before the tail
     case, because Alice's Z correction lives in a third (ε) phase. *)
  - intros n c Hc; destruct n as [| [| [| n]]]; vm_compute in Hc |- *;
      try contradiction;
      destruct Hc as [Hc | [Hc | []]]; subst c; reflexivity.
  - intro n; destruct n as [| [| [| n]]]; vm_compute; split;
      solve [ repeat constructor; cbn; intuition congruence
            | intros x Hx Hy; cbn in Hx, Hy; intuition congruence
            | constructor
            | intros x Hx Hy; contradiction ].
Qed.


Local Open Scope matrix_scope.

(** ** The specification (paper Theorem 5.3) ***************************

    Choi-style, and that is the whole point.  Teleportation's postcondition
    names a CONCRETE unknown state ρψ that the precondition also names;
    here the precondition hands the implemented channel one half of each of
    two maximally entangled pairs, and the postcondition says the joint
    state of (C,T,C',T') is the Choi state of CNOT.  Because ∣Φ+⟩ is
    maximally entangled, pinning down that one output pins down the action
    of the channel on EVERY input — no quantification over ψ is needed, and
    none appears.

    C' and T' are touched by no local block of [rcnot] (see
    [rcnot_wf_program]): they are the reference registers, and they are
    exactly the registers the entanglement of the postcondition is
    measured against. *)

(** One Bell pair as a density matrix — ∣Φ+⟩⟨Φ+∣ on two adjacent qubits. *)
Definition EPR : Square 4 := ∣Φ+⟩ × ∣Φ+⟩†.

(** The input state, in the qubit order A(0) B(1) C(2) C'(3) T(4) T'(5):

        EPR(A,B) ⊗ EPR(C,C') ⊗ EPR(T,T')

    three ADJACENT pairs, read left to right exactly as Theorem 5.3 writes
    them.  The factors are equal as matrices, so this term IS the paper's
    precondition, not a rearrangement of it. *)
Definition Psi0 : Vector (2 ^ 6) := ∣Φ+⟩ ⊗ ∣Φ+⟩ ⊗ ∣Φ+⟩.

(** The logical gate, on the reference block alone.  The indices here are
    BLOCK-LOCAL, not the global ones above: inside (C,C',T,T') the control
    C is qubit 0 and the target T is qubit 2.  Globally that block sits at
    offset 2, which the postcondition supplies by tensoring on the left.

    This is the straddle the state ordering costs, and it is the cheap side
    of the trade: an operator that straddles is a [pad_ctrl], while a state
    that straddles is a sum nobody can see through. *)
Definition CNOT_CT : Square (2 ^ 4) := pad_ctrl 4 0 2 σx.

(** CNOTChoi(C,T,C',T') of §5.3.1:

        (CNOT[C,T] ⊗ I_{C'T'}) (EPR(C,C') ⊗ EPR(T,T')) (CNOT[C,T] ⊗ I_{C'T'})†

    [CNOT_CT] already is the lift to the four-qubit block, so the ⊗ I is
    not written again. *)
Definition CNOTChoi : Square (2 ^ 4) :=
  CNOT_CT × (EPR ⊗ EPR) × CNOT_CT †.

(** The two conditional Pauli corrections, as store-indexed operators:
    [gZc v] is what Alice applies when her received bit is v, [gXb u] what
    Bob applies when his is u.  Both are the identity off 1.

    Teleportation and entanglement swapping fold their corrections into a
    CONSTANT frame matrix ([Corr u v]) because both corrections come last,
    after every gate and measurement.  Here Bob's X comes FIRST, before his
    own CNOT, H and measurement, so there is no constant frame to fold it
    into.  Indexing the correction itself is what replaces that, and it
    costs nothing: each guard branch then reduces the index to a literal
    and the two sides of the entailment become the same matrix.

    These, and everything above them, are repeated verbatim in
    [NonlocalCNOTComplete.v]; being syntactically identical, the matrix
    lemmas proved over there close obligations stated here by conversion.
    Same arrangement as [Teleportation.v] and [BellComplete.v]. *)
Definition gZc (v : val) : Square (2 ^ 6) :=
  if Nat.eqb v 1%nat then pad_u 6 C σz else I (2 ^ 6).

Definition gXb (u : val) : Square (2 ^ 6) :=
  if Nat.eqb u 1%nat then pad_u 6 B σx else I (2 ^ 6).

(** Both assertions are classically [true] and quantum-constant: no
    measurement outcome survives into the specification, which is what it
    means for the protocol to implement a DETERMINISTIC gate.  The four
    (m1,m2) branches are internal, and Branch-Accum is where they go. *)
Definition rcnot_pre : assertion 6 :=
  {| classical_part := f_bexp b_true;
     quantum_part   := q_op (fun _ => Some (Psi0 × Psi0 †)) nil |}.

(** A and B have been measured out, so the postcondition leaves them free —
    the two I's are the paper's lifting convention ⟦A⟧σ = σ(A) ⊗ I_R.  They
    are on the LEFT because A and B are qubits 0 and 1; the Choi predicate
    occupies the reference block at offset 2. *)
Definition rcnot_post : assertion 6 :=
  {| classical_part := f_bexp b_true;
     quantum_part   := q_op (fun _ => Some (I 2 ⊗ I 2 ⊗ CNOTChoi)) nil |}.

(** ** The interpretation ********************************************* *)

Definition rc_uu (U : usym) (qs : list qvar) : Square (2 ^ 6) :=
  match U, qs with
  | 0%nat, a :: b :: nil => pad_ctrl 6 a b σx      (* CNOT *)
  | 1%nat, a :: nil      => pad_u 6 a hadamard     (* H    *)
  | 2%nat, a :: nil      => pad_u 6 a σz           (* Z    *)
  | 3%nat, a :: nil      => pad_u 6 a σx           (* X    *)
  | _, _                 => I (2 ^ 6)
  end.

(* Outside the outcome set T_M = {0,1} the operator is Zero — the paper's
   finite family {M_m} (p.4), as [wf_interp] demands. *)
Definition rc_mm (M : msym) (qs : list qvar) : measurement 6 :=
  match qs with
  | a :: nil => (0%nat :: 1%nat :: nil,
                 fun m => if Nat.eqb m 0%nat then pad_u 6 a ∣0⟩⟨0∣
                          else if Nat.eqb m 1%nat then pad_u 6 a ∣1⟩⟨1∣
                          else Zero)
  | _        => (0%nat :: nil,
                 fun m => if Nat.eqb m 0%nat then I (2 ^ 6) else Zero)
  end.

Definition rc_rl (R : relsym) (args : list val) : bool :=
  match R, args with
  | 0%nat, a :: b :: nil => Nat.eqb a b            (* r_eq *)
  | 1%nat, a :: b :: nil => Nat.ltb a b            (* r_lt *)
  | 2%nat, a :: b :: nil => Nat.ltb b a            (* r_gt *)
  | _, _                 => false
  end.

Definition Sig : interp 6 :=
  {| i_fn := fun _ _ => 0%nat;
     i_rl := rc_rl;
     i_uu := rc_uu;
     i_mm := rc_mm |}.


(** The five gates the protocol names, at their global indices. *)
Lemma HR : standard_rels Sig.
Proof. repeat split; reflexivity. Qed.
Lemma HCNOT_CA : i_uu Sig CNOT ([C; A]) = pad_ctrl 6 C A σx.
Proof. reflexivity. Qed.
Lemma HCNOT_BT : i_uu Sig CNOT ([B; T]) = pad_ctrl 6 B T σx.
Proof. reflexivity. Qed.
Lemma HH : i_uu Sig H ([B]) = pad_u 6 B hadamard.
Proof. reflexivity. Qed.
Lemma HZ : i_uu Sig Z ([C]) = pad_u 6 C σz.
Proof. reflexivity. Qed.
Lemma HX : i_uu Sig X ([B]) = pad_u 6 B σx.
Proof. reflexivity. Qed.

(** Every operator Sig hands out is a padding of a one- or two-qubit gate
    at the very qubits the primitive names — which is what makes it LOCAL,
    the premise Par-Disjoint-MP needs. *)
Lemma rc_padded : forall K qs, acts_on Sig K qs -> padded K qs.
Proof.
  intros K qs Hk; destruct Hk as [U qs' | M qs' m | q | q].
  - unfold Sig, rc_uu; cbn [i_uu].
    destruct U as [|[|[|[|U]]]]; destruct qs' as [|a [|b [|c qs']]]; cbn;
      constructor; auto with wf_db.
  - unfold Sig, rc_mm; cbn [i_mm snd].
    destruct qs' as [|a [|b qs']]; cbn;
      repeat match goal with
             | |- padded (if ?x then _ else _) _ => destruct x
             end;
      constructor; auto with wf_db.
  - constructor; auto with wf_db.
  - constructor; auto with wf_db.
Qed.

Lemma rc_local_ops : local_ops Sig.
Proof.
  intros K1 qs1 K2 qs2 H1 H2 Hd.
  eapply padded_commute; eauto using rc_padded.
Qed.

(** Sig interprets every symbol by a well-formed operator, every
    measurement by a finite family, and every primitive locally — the side
    condition [soundness] needs. *)
Lemma rc_wf_interp : wf_interp Sig.
Proof.
  split; [| split; [| split; [| split]]].
  - intros U qs. unfold Sig, rc_uu; cbn [i_uu].
    destruct U as [|[|[|[|U]]]]; destruct qs as [|a [|b [|c qs]]]; cbn;
      auto with wf_db;
      try (apply (WF_pad_ctrl 6); auto with wf_db);
      try (apply (WF_pad_u 6); auto with wf_db).
  - intros M qs m. unfold Sig, rc_mm; cbn [i_mm].
    destruct qs as [|a [|b qs]]; cbn;
      repeat match goal with |- WF_Matrix (if ?x then _ else _) => destruct x end;
      auto with wf_db; try (apply (WF_pad_u 6); auto with wf_db).
  - intros M qs m Hm. unfold Sig, rc_mm in *; cbn [i_mm] in *.
    destruct qs as [|a [|b qs]]; cbn in *;
      repeat match goal with
             | |- (if ?x then _ else _) = _ => destruct x eqn:?
             end;
      try reflexivity;
      repeat match goal with
             | E : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in E; subst
             end;
      exfalso; apply Hm; cbn; auto.
  - intros M qs. unfold Sig, rc_mm; cbn [i_mm].
    destruct qs as [|a [|b qs]]; cbn;
      repeat constructor; cbn; intuition congruence.
  - exact rc_local_ops.
Qed.

(** ** The assertions **************************************************

    One constant predicate — the goal — plus two [q_conj] wrappers, one per
    conditional correction.  Every other assertion in the derivation is a
    weakest precondition computed from these by the local rules, so the
    branch pre-effect the completeness step finally sees is literally the
    protocol's operator string sandwiching the goal. *)

Definition y1 : var := 4%nat.
Definition y2 : var := 5%nat.

Definition qChoi : qpred 6 :=
  q_op (fun _ => Some (I 2 ⊗ I 2 ⊗ CNOTChoi)) nil.

(** The goal with Alice's pending Z conjugated onto it, indexed by j. *)
Definition qAfterZ : qpred 6 :=
  q_conj (fun vs => gZc (nth 0 vs 0%nat)) [e_var j] qChoi.

(** Wrapping Bob's pending X around an arbitrary predicate, indexed by i. *)
Definition withX (A : qpred 6) : qpred 6 :=
  q_conj (fun vs => gXb (nth 0 vs 0%nat)) [e_var i] A.

(* Shaped so that (Axiom-Meas) applies on the nose in BOTH rounds: its
   postcondition must be literally (φ ∧ x = y).  Reading outwards, the last
   conjunct is peeled by Bob's m2 in round 2 and the inner one by Alice's
   m1 in round 1 — which is exactly the order the backward derivation meets
   them, even though a rendezvous sits between the two. *)
Definition chi : formula :=
  f_and (f_and (f_bexp b_true) (f_eq (e_var i) (e_var y1)))
        (f_eq (e_var j) (e_var y2)).

(** ** Side conditions of the rules ***********************************

    Everything the derivation cannot close by another rule, proved once
    under a name.  This section is pure logic: not one matrix appears. *)

(* -- the two phases are matched (Comm-Select-MP) -- *)

Definition k1_mid : krow := ⟨ ε ⟩ ∥ ⟨ [c1 ⁇ i] ⟩.
Definition k2_mid : krow := ⟨ [c2 ⁇ j] ⟩ ∥ ⟨ ε ⟩.

Ltac wfphase :=
  split; [| split];
  [ intros c Hc; vm_compute in Hc;
    repeat (destruct Hc as [Hc | Hc]); try contradiction;
    rewrite <- Hc; vm_compute; repeat split; reflexivity
  | vm_compute; repeat constructor; cbn; intuition congruence
  | intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence ].

Lemma wf_k1 : wf_phase k1.  Proof. wfphase. Qed.
Lemma wf_k2 : wf_phase k2.  Proof. wfphase. Qed.

(* -- the rows are disjoint (Par-Disjoint-MP) --

   [d2] is the one that is new: a real local block on Bob's leaf sitting
   opposite Alice's padded skip, in a round that still has a live
   communication phase above it. *)

Ltac disjrow :=
  repeat constructor; repeat split;
  intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.

Lemma disj_d1 : lrow_disj d1.  Proof. disjrow. Qed.
Lemma disj_d2 : lrow_disj d2.  Proof. disjrow. Qed.
Lemma disj_d3 : lrow_disj d3.  Proof. disjrow. Qed.

(* -- the tails are well formed too (Par-Comp-MP, rounds 2 and 3) --

   [t1] still owns c2, so it needs Definition 2.1 in full; [t2] owns no
   channel at all.  This is the premise teleportation and entanglement
   swapping only ever discharge once. *)

Lemma t1_wf_program : wf_program t1.
Proof.
  split; [| split; [| split]].
  - repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
  - intros c Hc; vm_compute in Hc.
    destruct Hc as [Hc | [Hc | []]]; subst c; repeat split; reflexivity.
  - intros n c Hc; destruct n as [| [| n]]; vm_compute in Hc |- *;
      try contradiction;
      destruct Hc as [Hc | [Hc | []]]; subst c; reflexivity.
  - intro n; destruct n as [| [| n]]; vm_compute; split;
      solve [ repeat constructor; cbn; intuition congruence
            | intros x Hx Hy; cbn in Hx, Hy; intuition congruence
            | constructor
            | intros x Hx Hy; contradiction ].
Qed.

Lemma t2_wf_program : wf_program t2.
Proof.
  split; [| split; [| split]].
  - repeat split; intros x Hx Hy; vm_compute in Hx, Hy; intuition congruence.
  - intros c Hc; vm_compute in Hc; contradiction.
  - intros n c Hc; destruct n as [| n]; vm_compute in Hc; contradiction.
  - intro n; destruct n as [| n]; vm_compute; split;
      [constructor | intros x Hx Hy; contradiction
       | constructor | intros x Hx Hy; contradiction].
Qed.

(** ** Effects ********************************************************

    [is_effect M] is 0 ⊑ M ⊑ I, the paper's assertion-formation check
    (p.10).  It is a notion of the LOGIC, so it may not appear in
    [NonlocalCNOTComplete.v]; every matrix step it appeals to is a lemma
    over there. *)

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

Lemma herm_idem_effect : forall dim (M : Square (2 ^ dim)),
    WF_Matrix M -> M † = M -> M × M = M -> is_effect (dim := dim) M.
Proof.
  intros dim M HW Hh Hi.
  split; [ apply NonlocalCNOTComplete.herm_idem_psd; assumption |].
  unfold lowner. apply NonlocalCNOTComplete.herm_idem_psd;
    [ apply NonlocalCNOTComplete.compl_herm
    | apply NonlocalCNOTComplete.compl_idem ]; assumption.
Qed.

(* Every constant assertion of this case study is a block operator padded
   with I on A and B, so this is the only effect check needed. *)
Lemma is_effect_blk : forall M : Square (2 ^ 4),
    WF_Matrix M -> M † = M -> M × M = M ->
    is_effect (dim := 6) (I 2 ⊗ I 2 ⊗ M).
Proof.
  intros M WM Hh Hi.
  apply herm_idem_effect;
    [ apply NonlocalCNOTComplete.WF_blk
    | apply NonlocalCNOTComplete.blk_herm
    | apply NonlocalCNOTComplete.blk_idem ]; assumption.
Qed.

Lemma is_effect_choi : is_effect (dim := 6) (I 2 ⊗ I 2 ⊗ CNOTChoi).
Proof.
  apply is_effect_blk;
    [ exact NonlocalCNOTComplete.WF_CNOTChoi
    | exact NonlocalCNOTComplete.CNOTChoi_herm
    | exact NonlocalCNOTComplete.CNOTChoi_idem ].
Qed.

(** ** The weakest preconditions, round by round *********************

    Read bottom-up, these are the backward pass: [Q_r3] is what Alice's Z
    correction needs, [Q_m2] what c2 delivers it, [bob_wp] what Bob's three
    gates need, [Q_r2] what his X correction needs, [Q_m1] what c1 delivers
    THAT, and [alice_wp] what her CNOT and measurement need.

    Two rendezvous sit inside this chain — which is the whole point of the
    example.  In teleportation and entanglement swapping the entire
    backward pass happens inside one local block. *)

Definition Q_r3 : assertion 6 := mk_assertion chi qAfterZ.

Definition Q_m2 : assertion 6 :=
  mk_assertion (f_and (f_bexp b_true) (f_eq (e_var i) (e_var y1)))
               (qpred_subst qAfterZ j (e_var m2)).

Definition bob_wp : assertion 6 :=
  wp_unitary (i_uu Sig CNOT ([B; T]))
    (wp_unitary (i_uu Sig H ([B]))
      (wp_meas Sig Meas ([B]) y2 (assertion_subst Q_m2 m2 (e_var y2)))).

Definition Q_r2 : assertion 6 :=
  mk_assertion (classical_part bob_wp) (withX (quantum_part bob_wp)).

Definition Q_m1 : assertion 6 :=
  mk_assertion (f_bexp b_true)
               (quantum_part (assertion_subst Q_r2 i (e_var m1))).

Definition alice_wp : assertion 6 :=
  wp_unitary (i_uu Sig CNOT ([C; A]))
    (wp_meas Sig Meas ([A]) y1 (assertion_subst Q_m1 m1 (e_var y1))).

Definition at_uv (Q : assertion 6) (u v : val) : assertion 6 :=
  assertion_subst (assertion_subst Q y1 (e_val u)) y2 (e_val v).

Definition br (u v : val) : qpred 6 * formula :=
  (quantum_part (at_uv alice_wp u v),
   classical_part (at_uv (mk_assertion chi qChoi) u v)).

Definition four : list (qpred 6 * formula) :=
  [br 0%nat 0%nat; br 0%nat 1%nat; br 1%nat 0%nat; br 1%nat 1%nat].

(* Complete's WF hints are not in scope without [Import] — the same thing
   EntanglementSwapping.v has to do for SwapComplete. *)
#[local] Hint Resolve NonlocalCNOTComplete.WF_CNOTChoi
                      NonlocalCNOTComplete.WF_EPR
                      NonlocalCNOTComplete.WF_Psi0
                      NonlocalCNOTComplete.WF_cnotBT_raw
                      NonlocalCNOTComplete.WF_hB_raw
                      NonlocalCNOTComplete.WF_piB0_raw
                      NonlocalCNOTComplete.WF_piB1_raw
                      NonlocalCNOTComplete.WF_choi_raw
                      NonlocalCNOTComplete.WF_zC_raw
                      NonlocalCNOTComplete.WF_xB_raw : wf_db.

(** ** The entailments the Conseq steps discharge *********************

    Each guard branch reduces the correction's index to a literal: with the
    guard true the indexed operator IS the gate the Unitary rule names, so
    the two sides are the same matrix; with it false it is the identity and
    the conjugation collapses.  None of the four touches the Choi matrix. *)

Ltac ent_guard :=
  split; [| split];
  [ intros s Hs; cbn in Hs |- *;
    apply andb_true_iff in Hs as [Hchi _]; exact Hchi
  | intros s _ _; eexists; cbn; reflexivity
  | intros s M N Hs HM HN; cbn in Hs, HM, HN;
    inversion HM; inversion HN; subst;
    apply andb_true_iff in Hs as [_ Hg] ].

Lemma ent_Z_fires :
  and_guard Q_r3 (b_eq (e_var j) (e_val 1%nat)) true
  ⊨[Sig] wp_unitary (i_uu Sig Z ([C])) (mk_assertion chi qChoi).
Proof. ent_guard. unfold gZc. rewrite Hg. apply lowner_refl. Qed.

Lemma ent_Z_skipped :
  and_guard Q_r3 (b_eq (e_var j) (e_val 1%nat)) false ⊨[Sig] mk_assertion chi qChoi.
Proof.
  ent_guard. apply negb_true_iff in Hg. unfold gZc. rewrite Hg.
  rewrite NonlocalCNOTComplete.conj_id by auto with wf_db.
  apply lowner_refl.
Qed.

Lemma wf_qChoi : wf_assertion Sig (mk_assertion chi qChoi).
Proof. intros s M HM; cbn in HM; inversion HM; apply is_effect_choi. Qed.

Lemma wf_rcnot_post : wf_assertion Sig rcnot_post.
Proof. intros s M HM; cbn in HM; inversion HM; apply is_effect_choi. Qed.

Lemma ent_post : mk_assertion (fdisj (map snd four)) qChoi ⊨[Sig] rcnot_post.
Proof.
  split; [| split].
  - intros s _; cbn; reflexivity.
  - intros s _ _; cbn; eexists; reflexivity.
  - intros s M N _ HM HN; cbn in HM, HN; inversion HM; inversion HN; subst;
      apply lowner_refl.
Qed.

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

(** ** The derivation *************************************************

    Every [rule_seq] below names its intermediate assertion explicitly.
    Leaving it to unification does NOT work here: the evar has to be
    resolved against a weakest precondition that a rendezvous substitution
    has already reshaped, and [eapply] picks the wrong instantiation. *)

(* Round 1 — Alice's CNOT and measurement; Bob idle. *)
Lemma alice_local :
  Sig ⊢ₗ {{ alice_wp }} lseq d1 {{ assertion_subst Q_r2 i (e_var m1) }}.
Proof.
  unfold alice_wp. cbn [lseq d1].
  eapply rule_seq. 2:{ apply rule_skip. }
  unfold alice_pre.
  eapply rule_seq with
    (Q2 := wp_meas Sig Meas ([A]) y1 (assertion_subst Q_m1 m1 (e_var y1))).
  - apply rule_unitary.
  - apply rule_meas with (Q := Q_m1) (x := m1) (M := Meas)
                         (qs := ([A])) (y := y1).
    + vm_compute; intuition congruence.
    + vm_compute; intuition congruence.
Qed.

(* The two rendezvous.  One matched pair each, then the phase is empty. *)
Lemma rcnot_phase1 :
  Sig ⊢ₖ {{ assertion_subst Q_r2 i (e_var m1) }} k1 {{ Q_r2 }}.
Proof.
  apply rule_comm_select with (kmid := k1_mid) (k' := k3)
                              (c := c1) (e := e_var m1) (x := i).
  { exact wf_k1. }
  { unfold k1, k1_mid; eauto with locc. }
  { unfold k1_mid, k3; eauto with locc. }
  apply rule_comm_done; repeat split; reflexivity.
Qed.

Lemma rcnot_phase2 :
  Sig ⊢ₖ {{ assertion_subst Q_r3 j (e_var m2) }} k2 {{ Q_r3 }}.
Proof.
  apply rule_comm_select with (kmid := k2_mid) (k' := k3)
                              (c := c2) (e := e_var m2) (x := j).
  { exact wf_k2. }
  { unfold k2, k2_mid; eauto with locc. }
  { unfold k2_mid, k3; eauto with locc. }
  apply rule_comm_done; repeat split; reflexivity.
Qed.

(* Bob's X correction, the two guard branches.  [ent_X_fires] is the same
   two-line argument as [ent_Z_fires]: the guard pins the index to 1, and
   the indexed operator becomes the gate the Unitary rule names. *)
Lemma ent_X_fires :
  and_guard Q_r2 (b_eq (e_var i) (e_val 1%nat)) true
  ⊨[Sig] wp_unitary (i_uu Sig X ([B])) bob_wp.
Proof. ent_guard. unfold gXb. rewrite Hg. apply lowner_refl. Qed.

(* The skipped branch needs [(I 64)† M (I 64) = M] for M the denotation of
   the whole backward chain, so it needs [WF_Matrix M].  Unlike the Z case,
   where M is the constant [I 2 ⊗ I 2 ⊗ CNOTChoi], M here runs through the
   measurement operator, which is [Zero] off the outcome set — hence the
   case split, and hence the post-[cbn] WF lemmas in Complete: at dimension
   64 [auto with wf_db] cannot rebuild the dimension arithmetic on its own,
   but going back through [WF_pad_u]/[WF_pad_ctrl] can. *)
Ltac wf_chain :=
  unfold gZc, gXb;
  repeat match goal with |- context[if ?b then _ else _] => destruct b end;
  auto 20 with wf_db.

Lemma ent_X_skipped :
  and_guard Q_r2 (b_eq (e_var i) (e_val 1%nat)) false ⊨[Sig] bob_wp.
Proof.
  split; [| split].
  - intros s Hs; cbn in Hs |- *.
    apply andb_true_iff in Hs as [Hchi _]; exact Hchi.
  - intros s _ _; eexists; cbn; reflexivity.
  - intros s M N Hs HM HN; cbn in Hs, HM, HN.
    inversion HM; inversion HN; subst.
    apply andb_true_iff in Hs as [_ Hg].
    apply negb_true_iff in Hg. unfold gXb. rewrite Hg.
    rewrite NonlocalCNOTComplete.conj_id by wf_chain.
    apply lowner_refl.
Qed.

(* Round 3 — Alice's Z correction; Bob already terminated. *)
Lemma alice_corr_local :
  Sig ⊢ₗ {{ Q_r3 }} lseq d3 {{ mk_assertion chi qChoi }}.
Proof.
  cbn [lseq d3]. unfold alice_corr, corr.
  eapply rule_seq with (Q2 := mk_assertion chi qChoi).
  - apply rule_if.
    + eapply rule_conseq;
        [ exact ent_Z_fires | apply rule_unitary
        | apply entails_refl | exact wf_qChoi ].
    + eapply rule_conseq;
        [ apply entails_refl | apply rule_skip
        | exact ent_Z_skipped | exact wf_qChoi ].
  - apply rule_skip.
Qed.

(** ** Effects of the wp chain ****************************************

    [bob_wp] is the goal projector conjugated by Bob's whole backward
    chain, and that chain is NOT unitary — it runs through his measurement
    operator.  So its effect check is the contraction argument, whose
    matrix half ([conj_psd], [conj_le_I], [bobK_le_I]) is proved in
    Complete; what is left here is the bookkeeping. *)

Lemma is_effect_conj : forall (K A : Square (2 ^ 6)),
    WF_Matrix K -> WF_Matrix A -> is_effect (dim := 6) A ->
    (K † × K) ⊑ I (2 ^ 6) -> is_effect (dim := 6) (K † × A × K).
Proof.
  intros K A WK WA [HP HI] HK. split.
  - apply NonlocalCNOTComplete.conj_psd; assumption.
  - apply NonlocalCNOTComplete.conj_le_I; assumption.
Qed.

Lemma gZc_unitary : forall v, WF_Unitary (gZc v).
Proof.
  intros v; unfold gZc; destruct (Nat.eqb v 1%nat);
    [apply pad_u_unitary; [unfold C; lia | apply σz_unitary] | apply id_unitary].
Qed.

Lemma gXb_unitary : forall u, WF_Unitary (gXb u).
Proof.
  intros u; unfold gXb; destruct (Nat.eqb u 1%nat);
    [apply pad_u_unitary; [unfold B; lia | apply σx_unitary] | apply id_unitary].
Qed.

Lemma WF_gZc : forall v, WF_Matrix (gZc v).
Proof. intros v; destruct (gZc_unitary v); assumption. Qed.
Lemma WF_gXb : forall u, WF_Matrix (gXb u).
Proof. intros u; destruct (gXb_unitary u); assumption. Qed.
#[local] Hint Resolve WF_gZc WF_gXb : wf_db.

Lemma unitary_le_I : forall (K : Square (2 ^ 6)),
    K † × K = I (2 ^ 6) -> (K † × K) ⊑ I (2 ^ 6).
Proof. intros K H0. rewrite H0. apply lowner_refl. Qed.

(** Round 3's precondition: the goal with a UNITARY conjugated onto it, so
    it is still a projector and the contraction argument is not needed. *)
Lemma wf_Q_r3 : wf_assertion Sig Q_r3.
Proof.
  intros s M HM; cbn in HM; inversion HM; subst; clear HM.
  apply is_effect_conj;
    [ auto with wf_db | auto with wf_db
    | apply is_effect_choi
    | apply unitary_le_I; exact (proj2 (gZc_unitary (s j))) ].
Qed.

(** The WF side conditions below need one care: the measurement operator
    reaches the goal UNFOLDED — an [if] on the outcome that is [Zero] off
    the outcome set — so [auto] has to case-split before Complete's WF
    lemmas apply.  And [solve], not bare [auto]: [auto] does not FAIL when
    it cannot close a goal, it silently leaves it, which desynchronises
    every bracket after it. *)
Ltac wfc :=
  repeat match goal with |- context[if ?b then _ else _] => destruct b end;
  try (change (2 ^ 6)%nat with 64%nat);
  auto 25 with wf_db.

(** [bob_wp] denotes  K† (I⊗I⊗CNOTChoi) K  with K = gZc · Π^B · H_B ·
    CNOT[B,T], peeled one conjugation at a time.  The two unitary layers
    give [K†K = I]; the measurement layer gives a projector, which is where
    [bobK_le_I]'s contraction argument is really needed. *)
Lemma wf_bob_wp : wf_assertion Sig bob_wp.
Proof.
  intros s M HM. cbn in HM. inversion HM; subst; clear HM.
  apply is_effect_conj;
    [ solve [wfc] | solve [wfc]
    | | solve [apply unitary_le_I; exact NonlocalCNOTComplete.cnotBT_flip] ].
  apply is_effect_conj;
    [ solve [wfc] | solve [wfc]
    | | solve [apply unitary_le_I; exact NonlocalCNOTComplete.hB_flip] ].
  apply is_effect_conj;
    [ solve [wfc] | solve [wfc]
    | | solve [exact (NonlocalCNOTComplete.piB_raw_le_I (s y2))] ].
  apply is_effect_conj;
    [ solve [wfc] | solve [wfc]
    | | solve [apply unitary_le_I; exact (proj2 (gZc_unitary (s y2)))] ].
  apply is_effect_choi.
Qed.

(** One layer further out: [Q_r2] is [bob_wp] with Bob's pending X on top,
    and X is unitary, so this is a single peel onto [wf_bob_wp]. *)
Lemma wf_Q_r2 : wf_assertion Sig Q_r2.
Proof.
  intros s M HM. cbn in HM. inversion HM; subst; clear HM.
  apply is_effect_conj;
    [ solve [wfc] | solve [wfc]
    | | solve [apply unitary_le_I; exact (proj2 (gXb_unitary (s i)))] ].
  apply (wf_bob_wp s). cbn. reflexivity.
Qed.

(** ** The derivation, rounds 2 and 3 ********************************** *)

(* Round 2 — Bob's middle block: the X correction, his CNOT and H, and the
   measurement that creates the SECOND branch. *)
Lemma bob_local :
  Sig ⊢ₗ {{ Q_r2 }} lseq d2 {{ assertion_subst Q_r3 j (e_var m2) }}.
Proof.
  cbn [lseq d2].
  eapply rule_seq with (Q2 := Q_r2); [ apply rule_skip |].
  unfold bob_mid, corr.
  eapply rule_seq with (Q2 := bob_wp).
  - apply rule_if.
    + eapply rule_conseq;
        [ exact ent_X_fires | apply rule_unitary
        | apply entails_refl | exact wf_bob_wp ].
    + eapply rule_conseq;
        [ apply entails_refl | apply rule_skip
        | exact ent_X_skipped | exact wf_bob_wp ].
  - eapply rule_seq with
      (Q2 := wp_unitary (i_uu Sig H ([B]))
               (wp_meas Sig Meas ([B]) y2 (assertion_subst Q_m2 m2 (e_var y2)))).
    + apply rule_unitary.
    + eapply rule_seq with
        (Q2 := wp_meas Sig Meas ([B]) y2 (assertion_subst Q_m2 m2 (e_var y2))).
      * apply rule_unitary.
      * apply rule_meas with (Q := Q_m2) (x := m2) (M := Meas)
                             (qs := ([B])) (y := y2).
        -- vm_compute; intuition congruence.
        -- vm_compute; intuition congruence.
Qed.

(** ** Par-Comp-MP, three rounds ***************************************

    THE structural point of this case study.  Teleportation and
    entanglement swapping recurse twice; here the middle round has a real
    local block on Bob's leaf sitting under a live communication phase, and
    the branch created by his measurement has to survive the second
    rendezvous before Branch-Accum ever sees it. *)
Lemma rcnot_branch : Sig ⊢ₚ {{ alice_wp }} rcnot {{ mk_assertion chi qChoi }}.
Proof.
  apply rule_par_comp with (d := d1) (k := k1) (t := t1)
                           (Q1 := assertion_subst Q_r2 i (e_var m1)) (Q2 := Q_r2).
  - exact rcnot_cut.
  - exact rcnot_wf_program.
  - exact wf_Q_r2.
  - exact wf_qChoi.
  - apply rule_par_disjoint; [ exact disj_d1 | exact alice_local ].
  - exact rcnot_phase1.
  - apply rule_par_comp with (d := d2) (k := k2) (t := t2)
                             (Q1 := assertion_subst Q_r3 j (e_var m2)) (Q2 := Q_r3).
    + exact rcnot_cut_tail.
    + exact t1_wf_program.
    + exact wf_Q_r3.
    + exact wf_qChoi.
    + apply rule_par_disjoint; [ exact disj_d2 | exact bob_local ].
    + exact rcnot_phase2.
    + apply rule_par_comp with (d := d3) (k := k3) (t := t3)
                               (Q1 := mk_assertion chi qChoi)
                               (Q2 := mk_assertion chi qChoi).
      * exact rcnot_cut_tail2.
      * exact t2_wf_program.
      * exact wf_qChoi.
      * exact wf_qChoi.
      * apply rule_par_disjoint; [ exact disj_d3 | exact alice_corr_local ].
      * apply rule_comm_done; repeat split; reflexivity.
      * apply rule_done; exact t3_terminated.
Qed.

(* The four branches, by Aux-Subst (y1 and y2 are auxiliary: the program
   neither reads nor writes them), then Branch-Accum. *)
Lemma rcnot_branch_at : forall u v : val,
    Sig ⊢ₚ {{ at_uv alice_wp u v }} rcnot {{ at_uv (mk_assertion chi qChoi) u v }}.
Proof.
  intros u v. unfold at_uv.
  apply rule_aux_subst; [ vm_compute; intuition congruence |].
  apply rule_aux_subst; [ vm_compute; intuition congruence |].
  exact rcnot_branch.
Qed.

Lemma rcnot_accum :
  Sig ⊢ₚ {{ mk_assertion (f_bexp b_true) (qsum (map fst four)) }} rcnot
        {{ mk_assertion (fdisj (map snd four)) qChoi }}.
Proof.
  apply rule_branch_accum.
  - repeat (apply Forall_cons; [ apply rcnot_branch_at |]). apply Forall_nil.
  - exact four_exclusive.
Qed.

(** The case study's mathematical content, and the only thing left open in
    the whole development: the three pre-shared Bell pairs are below the
    sum of the four branch pre-effects.  Six [conj_merge] steps fold the
    nested sandwich [cbn] produces into Complete's [Auv] — the two agree on
    the nose, operator by operator — and what remains is
    [rcnot_completeness], a statement about matrices only. *)
Lemma ent_pre :
  rcnot_pre ⊨[Sig] mk_assertion (f_bexp b_true) (qsum (map fst four)).
Proof.
  split; [| split].
  - intros s _; cbn; reflexivity.
  - intros s _ _; cbn; eexists; reflexivity.
  - intros s M N _ HM HN; cbn in HM, HN;
      inversion HM; inversion HN; subst.
    rewrite !NonlocalCNOTComplete.conj_merge.
    rewrite Mplus_0_r.
    exact NonlocalCNOTComplete.rcnot_completeness.
Qed.

Lemma rcnot_derivable : Sig ⊢ₚ {{ rcnot_pre }} rcnot {{ rcnot_post }}.
Proof.
  eapply rule_conseq_d;
    [ exact ent_pre | exact rcnot_accum | exact ent_post | exact wf_rcnot_post ].
Qed.

(** Paper Theorem 5.3 (correctness of non-local CNOT) — SEMANTIC
    correctness, via the soundness theorem applied to [rcnot_derivable].
    The same shape as [Teleportation.teleportation] and
    [EntanglementSwapping.entanglement_swapping]. *)
Theorem nonlocal_cnot : Sig ⊨ {{ rcnot_pre }} rcnot {{ rcnot_post }}.
Proof. exact (soundness Sig rc_wf_interp _ _ _ rcnot_derivable). Qed.
