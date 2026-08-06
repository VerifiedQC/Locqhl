(** * Rules — the local proof rules of the LOCC proof system.
      φ[e/x], A[e/x]      substitution   = precompose with a store update
      F_U(t)[q̄](A)        unitary  wp    = U† A U
      F_M(y)[q̄](A)        measure  wp    = M_y† A M_y   (outcome read from y)
      y ∉ free(φ) ∪ cv(A) freshness      = "the assertion does not depend on y"
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.
From QuantumLib Require Import Matrix Quantum.
From Locqhl.Core Require Import Syntax Names QuantumActions SemanticDomain Semantics Assertions WellFormed.
Import ListNotations.

(** ** Assertion transformers (all syntactic) ************************* *)

(** (φ ∧ b, A) and (φ ∧ ¬b, A), for the If rule. **)
Definition and_guard {dim} (Q : assertion dim) (b : bexpr) (positive : bool)
  : assertion dim :=
  {| classical_part :=
       f_and (classical_part Q)
             (if positive then f_bexp b else f_not (f_bexp b));
     quantum_part := quantum_part Q |}.

(** (φ ∧ x = y, A), the postcondition of the Meas rule. **)
Definition and_eq {dim} (Q : assertion dim) (x y : var) : assertion dim :=
  {| classical_part := f_and (classical_part Q) (f_eq (e_var x) (e_var y));
     quantum_part   := quantum_part Q |}.

(** F_U[q̄](A) = U† A U — a [q_conj] node with no classical parameters. **)
Definition wp_unitary {dim} (U : Square (2 ^ dim)) (Q : assertion dim)
  : assertion dim :=
  {| classical_part := classical_part Q;
     quantum_part   := q_conj (fun _ => U) ([]) (quantum_part Q) |}.

(** F_M(y)[q̄](A) = M_y† A M_y, the pre-effect of ONE outcome, the outcome
    being the value of the logical variable y. 
i_mm Σ  : msym -> list qvar -> measurement dim
i_mm Σ M qs  : measurement dim  =  (list nat) * (nat -> Square (2^dim))
                                    └─ T_M ─┘   └── m ↦ M_m ──┘
snd (i_mm Σ M qs)           : nat -> Square (2^dim)        ← m ↦ M_m
nth 0%nat vs 0%nat          : val                          ← vs #0
**)
Definition wp_meas {dim} (Σ : interp dim) (M : msym) (qs : list qvar) (y : var)
           (Q : assertion dim) : assertion dim :=
  {| classical_part := classical_part Q;
     quantum_part   :=
       q_conj (fun vs => snd (i_mm Σ M qs) (nth 0%nat vs 0%nat)) ([e_var y])
              (quantum_part Q) |}.

(** ** The local proof system ***************************************** *)
Reserved Notation "Σ '⊢ₗ' '{{' Pre '}}' L '{{' Post '}}'"
  (at level 70, Pre at level 99, L at level 99, Post at level 99).

Inductive local_derivable {dim} (Σ : interp dim)
    : assertion dim -> lblock -> assertion dim -> Prop :=

(* Skip:  ⊢ₗ {(φ,A)} skip {(φ,A)} *)
| rule_skip : forall Q,
    Σ ⊢ₗ {{ Q }} <{ skip }> {{ Q }}

(* Assign:  ⊢ₗ {(φ[e/x], A[e/x])} x:=e {(φ,A)} *)
| rule_assign : forall Q x e,
    Σ ⊢ₗ {{ assertion_subst Q x e }} <{ x := e }> {{ Q }}

(* Unitary:  ⊢ₗ {(φ, F_U[q̄](A))} U[q̄] {(φ,A)} *)
| rule_unitary : forall Q U qs,
    Σ ⊢ₗ {{ wp_unitary (i_uu Σ U qs) Q }} <{ U @ qs }> {{ Q }}

(* Meas:  y ∉ free(φ) ∪ cv(A) ∪ {x}  ⟹
     ⊢ₗ {(φ[y/x], F_M(y)[q̄](A[y/x]))} x:=M[q̄] {(φ ∧ x=y, A)} *)
| rule_meas : forall Q x M qs y,
    y <> x ->
    ~ In y (assertion_vars Q) ->
    Σ ⊢ₗ {{ wp_meas Σ M qs y (assertion_subst Q x (e_var y)) }}
        <{ x <- M @ qs }>
        {{ and_eq Q x y }}

(* Seq *)
| rule_seq : forall Q1 Q2 Q3 L1 L2,
    Σ ⊢ₗ {{ Q1 }} L1 {{ Q2 }} ->
    Σ ⊢ₗ {{ Q2 }} L2 {{ Q3 }} ->
    Σ ⊢ₗ {{ Q1 }} <{ L1 ; L2 }> {{ Q3 }}

(* If *)
| rule_if : forall Q R b L1 L0,
    Σ ⊢ₗ {{ and_guard Q b true  }} L1 {{ R }} ->
    Σ ⊢ₗ {{ and_guard Q b false }} L0 {{ R }} ->
    Σ ⊢ₗ {{ Q }} <{ if b then L1 else L0 }> {{ R }}

(* Conseq.  The target postcondition must denote an effect: the paper's
   assertion-formation check (p.10), surfacing as a side condition exactly
   where a new assertion enters a derivation — the same treatment the
   distributed rules get below. *)
| rule_conseq : forall Q Q' R R' L,
    Q' ⊨[Σ] Q ->
    Σ ⊢ₗ {{ Q }} L {{ R }} ->
    R ⊨[Σ] R' ->
    wf_assertion Σ R' ->
    Σ ⊢ₗ {{ Q' }} L {{ R' }}

where "Σ '⊢ₗ' '{{' Pre '}}' L '{{' Post '}}'" := (local_derivable Σ Pre L Post).


(** ** The rows of the distributed rules ******************************

      D₁‖…‖D_N      lrow      sequentialised by [lseq]
      K₁‖…‖K_N      krow      one endpoint taken by [kpick]
      S₁‖…‖S_N      program   split into the three rows by [cut]

      The split is by whether a CHOICE is being made.  [lseq] and [cut]
      are determinate constructions, so they are functions and reduce on a
      concrete row — their premises close by [reflexivity].  Picking an
      endpoint out of a phase is a genuine choice, and the operational
      semantics picks the same way, so [kpick] is a structural relation and
      the soundness bridge to [picks]/[replace_leaf] costs nothing.
*********************************************************************)

(** D₁; …; D_N, the displayed order of Par-Disjoint-MP's premise. **)
Fixpoint lseq (d : lrow) : lblock :=
  match d with
  | leaf D    => D
  | par d1 d2 => l_seq (lseq d1) (lseq d2)
  end.

(** Cut every process at its current communication phase: Sᵢ = Dᵢ; Kᵢ; Tᵢ.
    A total function, so the padding of p.15 — "processes without a current
    local prefix or communication block use skip and ε_K" — happens here
    instead of being supplied by whoever applies the rule.  A terminated
    leaf pads to (skip, ε_K, ↓). **)
Fixpoint cut (P : program) : lrow * krow * program :=
  match P with
  | leaf terminated    => (leaf l_skip, leaf ε, leaf terminated)
  | leaf (phase R K T) => (leaf (residual_lblock R), leaf K, leaf T)
  | par P1 P2 =>
      let '(d1, k1, t1) := cut P1 in
      let '(d2, k2, t2) := cut P2 in
      (par d1 d2, par k1 k2, par t1 t2)
  end.

(** The phase K₁‖…‖K_N exposes endpoint a at one of its leaves, leaving the
    residual phase.  Row-level companion of [picks]; the other leaves are
    carried through unchanged by reusing the very same subtree. **)
Inductive kpick : krow -> caction -> krow -> Prop :=
| kp_here  : forall K a K',
    K ∋ a □ K' -> kpick (leaf K) a (leaf K')
| kp_left  : forall k1 k1' k2 a,
    kpick k1 a k1' -> kpick (par k1 k2) a (par k1' k2)
| kp_right : forall k1 k2 k2' a,
    kpick k2 a k2' -> kpick (par k1 k2) a (par k1 k2').

Notation "k '∋ₖ' a '□' k'" := (kpick k a k')
  (at level 70, a at level 60).

(** A selection is found by search, not written out: [eauto with locc]
    picks the leaf and the position within it.  [repeat econstructor] does
    NOT do — it commits to the first applicable constructor and cannot undo
    a wrong leaf, which is exactly what the second endpoint of a pair
    needs. **)
#[export] Hint Constructors picks kpick : locc.

(** ** Side conditions of the distributed rules ***********************

      Each distributed rule carries exactly the syntactic check its own
      soundness argument consumes.  Two of them need less than Definition
      2.1; Par-Comp-MP needs all of it:

        Par-Disjoint-MP    wf_ownership PD    DisjMP on the D-row
        Comm-Select-MP     wf_phase PK        the phase matches, and commutes
        Par-Comp-MP        wf_program P       Definition 2.1 in full — the
                                              only rule that needs it

      Definition 2.1 then discharges all three at once for a well-formed
      source program — that is what Theorem 2.1 and its companions are for —
      so nothing is lost for the case studies, while [derivable] itself no
      longer mentions [wf_program].  All three checks stay syntactic.
*********************************************************************)

(** A phase's endpoints, and its channels. **)
Definition krow_actions (k : krow) : list caction := row_flat (fun K => K) k.
Definition krow_chan    (k : krow) : list chan     := row_flat cblock_chan k.

(** recv(K₁,…,K_N) and oread(K₁,…,K_N) of Definition 2.1(4). **)
Definition phase_recv (k : krow) : list var :=
  flat_map caction_change (krow_actions k).
Definition phase_oread (k : krow) : list var :=
  flat_map caction_read (krow_actions k).

Definition krow_endpoints (k : krow) (c : chan) : list caction :=
  filter (fun a => Nat.eqb (caction_chan a) c) (krow_actions k).

(** Each channel of the phase carries one output and one input, in two
    distinct leaves — [row_parties] counting the leaves is the paper's
    i ≠ j.  So naming a channel already determines the matched pair. **)
Definition wf_kchannels (k : krow) : Prop :=
  forall c, In c (krow_chan k) ->
    length (filter is_send (krow_endpoints k c)) = 1%nat
    /\ length (filter (fun a => negb (is_send a)) (krow_endpoints k c)) = 1%nat
    /\ row_parties cblock_chan k c = 2%nat.

(** Comm-Select-MP's side condition: the phase is matched, and Definition
    2.1(4) holds — which is what commutes the selected rendezvous to the
    front of a terminal run.  Ownership is NOT among these: a rendezvous
    acts as the identity on the quantum store. **)
Definition wf_phase (k : krow) : Prop :=
  wf_kchannels k
  /\ NoDup (phase_recv k)
  /\ disjoint (phase_recv k) (phase_oread k).

(** Par-Comp-MP's side condition is Definition 2.1 itself.  Alone among the
    eight rules it consumes all four clauses:

      wf_ownership          commutes a local step of one leaf past a
                            rendezvous between two others
      wf_channels           a receive has exactly one send it can pair with
      wf_phase_independence two rendezvous in ONE leaf commute — [wf_ownership]
                            separates different leaves and cannot see this
      wf_phase_aligned      together with [wf_channels], keeps the displayed
                            phase from reaching into the tail: see
                            [cut_chan_disjoint] just below

    The last two are what make the TAIL run determinately, which is what the
    rule's normalisation consumes — a d-stage [if] splits the configuration
    in two whose d-steps are then both absorbed, leaving the same program
    holding half an ensemble each, and those have to be recombined.

    A run of this semantics makes exactly two kinds of choice: which send a
    receive pairs with (removed by [wf_channels]) and which of two available
    rendezvous goes first (removed by [wf_phase_independence]). *)

Lemma perm_filter_len : forall {A} (f : A -> bool) l l',
    Permutation l l' -> length (filter f l) = length (filter f l').
Proof.
  intros A f l l' H;
    induction H as [| x l l' H IH | x y l | l1 l2 l3 H1 IH1 H2 IH2]; cbn.
  - reflexivity.
  - destruct (f x); cbn; lia.
  - destruct (f x), (f y); cbn; reflexivity.
  - lia.
Qed.

(** The actions of a program are those of its current phase plus those of
    its tail — the cut splits the endpoint multiset in two. *)
Lemma cut_actions : forall P d k t,
    cut P = (d, k, t) ->
    Permutation (program_actions P) (krow_actions k ++ program_actions t).
Proof.
  induction P as [S0 | P1 IH1 P2 IH2]; intros d k t Hcut.
  - destruct S0 as [| R K T]; cbn in Hcut; injection Hcut as _ Hk Ht;
      subst k t; cbn; apply Permutation_refl.
  - cbn in Hcut.
    destruct (cut P1) as [[d1 k1] t1] eqn:E1.
    destruct (cut P2) as [[d2 k2] t2] eqn:E2.
    injection Hcut as _ Hk Ht; subst k t.
    unfold program_actions, krow_actions in *; cbn [row_flat].
    eapply Permutation_trans;
      [apply Permutation_app;
        [apply (IH1 d1 k1 t1 eq_refl) | apply (IH2 d2 k2 t2 eq_refl)] |].
    rewrite <- !app_assoc. apply Permutation_app_head.
    rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
Qed.

Lemma program_chan_actions : forall P,
    program_chan P = map caction_chan (program_actions P).
Proof.
  unfold program_chan, program_actions;
    induction P as [S0 | P1 IH1 P2 IH2]; cbn [row_flat].
  - induction S0 as [| R K T IH]; cbn [process_chan process_actions];
      [reflexivity |].
    unfold cblock_chan; rewrite map_app, IH; reflexivity.
  - rewrite map_app, IH1, IH2; reflexivity.
Qed.

Lemma krow_chan_actions' : forall k,
    krow_chan k = map caction_chan (krow_actions k).
Proof.
  unfold krow_chan, krow_actions;
    induction k as [K | k1 IH1 k2 IH2]; cbn [row_flat];
    [reflexivity | rewrite map_app, IH1, IH2; reflexivity].
Qed.

(** The cut's phase and its tail share no channel.  A channel occurring in
    the phase already has both its endpoints there ([wf_phase_aligned]), and
    it has only two in the whole tree ([wf_channels]), so none is left for
    the tail. *)
Lemma cut_chan_disjoint : forall P d k t,
    wf_channels P -> wf_phase_aligned P -> cut P = (d, k, t) ->
    disjoint (krow_chan k) (program_chan t).
Proof.
  intros P d k t Hch Hal Hcut c Hk Ht.
  pose proof (cut_actions P d k t Hcut) as Hsplit.
  (* c has an endpoint in the phase, and one in the tail *)
  rewrite krow_chan_actions' in Hk; apply in_map_iff in Hk as (a & Ha & HaIn).
  rewrite program_chan_actions in Ht; apply in_map_iff in Ht as (b & Hb & HbIn).
  (* the phase already holds two of them *)
  assert (Hphase : krow_actions k = phase_actions P 0).
  { clear -Hcut. unfold phase_actions, phase_at, phase_row, krow_actions.
    revert d k t Hcut; induction P as [S0 | P1 IH1 P2 IH2]; intros d k t Hcut.
    - destruct S0 as [| R K T]; cbn in Hcut; injection Hcut as _ Hk _;
        subst k; cbn; rewrite ?app_nil_r; reflexivity.
    - cbn in Hcut.
      destruct (cut P1) as [[d1 k1] t1] eqn:E1.
      destruct (cut P2) as [[d2 k2] t2] eqn:E2.
      injection Hcut as _ Hk _; subst k.
      cbn [row_flat row_map row_leaves]; rewrite concat_app.
      rewrite (IH1 d1 k1 t1 eq_refl), (IH2 d2 k2 t2 eq_refl); reflexivity. }
  assert (Hin0 : In c (map caction_chan (phase_actions P 0)))
    by (rewrite <- Hphase; apply in_map_iff; exists a; split; assumption).
  specialize (Hal 0%nat c Hin0).
  (* but the whole tree holds only two *)
  assert (HinP : In c (program_chan P)).
  { rewrite program_chan_actions; apply in_map_iff; exists a; split;
      [exact Ha |].
    eapply Permutation_in; [apply Permutation_sym, Hsplit |].
    apply in_or_app; left; exact HaIn. }
  destruct (Hch c HinP) as (Hs & Hr & _).
  unfold endpoints_of in Hs, Hr.
  pose proof (filter_length_split is_send
                (filter (fun x => Nat.eqb (caction_chan x) c)
                        (program_actions P))) as Hsplit2.
  rewrite Hs, Hr in Hsplit2.
  (* the split of the action list splits the endpoint list too *)
  assert (Hlen : length (filter (fun x => Nat.eqb (caction_chan x) c)
                                (program_actions P))
                 = (length (filter (fun x => Nat.eqb (caction_chan x) c)
                                   (krow_actions k))
                    + length (filter (fun x => Nat.eqb (caction_chan x) c)
                                     (program_actions t)))%nat).
  { rewrite <- length_app, <- filter_app.
    apply perm_filter_len, Hsplit. }
  rewrite Hphase, Hal in Hlen.
  assert (Hne : filter (fun x => Nat.eqb (caction_chan x) c)
                       (program_actions t) <> nil).
  { intro Hnil. assert (Hbf : In b (filter (fun x => Nat.eqb (caction_chan x) c)
                                           (program_actions t)))
      by (apply filter_In; split; [exact HbIn | rewrite Hb; apply Nat.eqb_refl]).
    rewrite Hnil in Hbf; exact Hbf. }
  destruct (filter (fun x => Nat.eqb (caction_chan x) c) (program_actions t));
    [contradiction | cbn in Hlen; lia].
Qed.

(** ** Helpers for Branch-Accum *************************************** *)

(** Σ_{i∈J} A_i and ⋁_{i∈J} ψ_i.  Both fold over the whole family: [q_zero]
    and false are the units, so there is no distinguished first member and
    the empty family is allowed (it gives the vacuous triple {(φ,0)} P
    {(false,B)}, whose two degrees are both 0). **)
Definition qsum {dim} (As : list (qpred dim)) : qpred dim :=
  fold_right q_add q_zero As.

Definition fdisj (ps : list formula) : formula :=
  fold_right f_or (f_bexp b_false) ps.

(** ⊨ ¬(ψ_i ∧ ψ_j): the two guards never hold at the same store. **)
Definition exclusive {dim} (Σ : interp dim) (p q : formula) : Prop :=
  forall s, formula_holds Σ s p = true -> formula_holds Σ s q = true -> False.

(** Build a cq-assertion (φ, A) from a classical formula and a quantum predicate. **)
Definition mk_assertion {dim} (p : formula) (A : qpred dim) : assertion dim :=
  {| classical_part := p; quantum_part := A |}.

(** ** The distributed proof system ***********************************

      Three subjects, three judgments, in dependency order — none of them
      recursive in another, so the soundness induction still runs over
      [derivable] alone:

        ⊢_D  on an lrow      Par-Disjoint-MP.  One rule, so a Definition
        ⊢_K  on a krow       Comm-Done, Comm-Select-MP, Conseq
        ⊢ₚ   on a program    Par-Comp-MP, Done, Branch-Accum, Conseq

      Conseq is the only rule that has to be repeated: ⊢_D needs none (its
      single rule hands the obligation to ⊢ₗ, which already has one) and
      Branch-Accum is only ever used at whole-program level (Fig. 6, Step V).
*********************************************************************)

(** Par-Disjoint-MP.  [lrow_disj] is the paper's DisjMP({Dᵢ}) read straight
    off the row's leaves; Theorem 2.1 ([wf_disj_footprints]) is what
    discharges it for a cut of a well-formed program.

    One rule, so this could have been a conjunction — but then applying
    Par-Disjoint-MP would read as [split] and the rule would be invisible in
    a derivation.  An inductive with a named constructor keeps
    [apply rule_par_disjoint] in the proof script. **)
Inductive dloc {dim} (Σ : interp dim)
    : assertion dim -> lrow -> assertion dim -> Prop :=
| rule_par_disjoint : forall Q R d,
    lrow_disj d ->
    Σ ⊢ₗ {{ Q }} lseq d {{ R }} ->
    dloc Σ Q d R.

Reserved Notation "Σ '⊢ₖ' '{{' Pre '}}' k '{{' Post '}}'"
  (at level 70, Pre at level 99, k at level 99, Post at level 99).

Inductive comm_derivable {dim} (Σ : interp dim)
    : assertion dim -> krow -> assertion dim -> Prop :=
(* Comm-Done: the phase is exhausted, every leaf being ε_K. *)
| rule_comm_done : forall Q k,
    row_all (fun K => K = ε) k ->
    Σ ⊢ₖ {{ Q }} k {{ Q }}
(* Comm-Select-MP: consume one matched pair (p.15).  Under [wf_phase] the
   channel name already determines the pair, so there is nothing arbitrary
   left in the selection. *)
| rule_comm_select : forall Q R k kmid k' c e x,
    wf_phase k ->
    k    ∋ₖ c_send c e □ kmid ->
    kmid ∋ₖ c_recv c x □ k'   ->
    Σ ⊢ₖ {{ Q }} k' {{ R }} ->
    Σ ⊢ₖ {{ assertion_subst Q x e }} k {{ R }}
(* Conseq, as on the other two judgments. *)
| rule_conseq_k : forall Q Q' R R' k,
    Q' ⊨[Σ] Q ->
    Σ ⊢ₖ {{ Q }} k {{ R }} ->
    R ⊨[Σ] R' ->
    wf_assertion Σ R' ->
    Σ ⊢ₖ {{ Q' }} k {{ R' }}

where "Σ '⊢ₖ' '{{' Pre '}}' k '{{' Post '}}'" := (comm_derivable Σ Pre k Post).

Reserved Notation "Σ '⊢ₚ' '{{' Pre '}}' P '{{' Post '}}'"
  (at level 70, Pre at level 99, P at level 99, Post at level 99).

Inductive derivable {dim} (Σ : interp dim)
    : assertion dim -> program -> assertion dim -> Prop :=
(* Par-Comp-MP.  [cut P] reduces on a concrete program, so the first
   premise is closed by reflexivity and the three rows are read off rather
   than supplied.

   [wf_assertion] on Q2 and Q3 is the paper's assertion-formation check
   (p.10) — "if A is formed and defined in σ it is interpreted as an effect,
   0 ⊑ σ(A) ⊑ I" — surfacing here for the same reason it surfaces on Conseq:
   [qpred] is only semi-deep, so nothing in the TYPE of an assertion forces
   its operator to be an effect.

   This is the one rule that composes three stages, so it is the one rule
   whose validity has to SUM over an intermediate ensemble.  A state whose
   guard fails contributes 0 on the left while still contributing on the
   right, so without the check a non-effect postcondition can drag the sum
   below the precondition's degree and the rule is unsound.  Q1 needs no
   check: the first stage still starts from a single state.

   The side condition is [wf_program P] — Definition 2.1 in full, and this
   is the only rule that needs it.  See the note above [cut_actions] for
   which clause pays for what. *)
| rule_par_comp : forall Q0 Q1 Q2 Q3 P d k t,
    cut P = (d, k, t) ->
    wf_program P ->
    wf_assertion Σ Q2 ->
    wf_assertion Σ Q3 ->
    dloc Σ Q0 d Q1 ->
    Σ ⊢ₖ {{ Q1 }} k {{ Q2 }} ->
    Σ ⊢ₚ {{ Q2 }} t {{ Q3 }} ->
    Σ ⊢ₚ {{ Q0 }} P {{ Q3 }}
(* Done: a terminated program does nothing.  The base case of Par-Comp's
   recursion down the tails — [cut] pads a terminated leaf to itself, so
   without this the rule would recurse forever. *)
| rule_done : forall Q P,
    prog_terminated P ->
    Σ ⊢ₚ {{ Q }} P {{ Q }}
(* Branch-Accum. *)
| rule_branch_accum : forall phi B P fam,
    Forall (fun Api => Σ ⊢ₚ {{ mk_assertion phi (fst Api) }} P
                           {{ mk_assertion (snd Api) B }}) fam ->
    ForallOrdPairs (exclusive Σ) (map snd fam) ->
    Σ ⊢ₚ {{ mk_assertion phi (qsum (map fst fam)) }} P
        {{ mk_assertion (fdisj (map snd fam)) B }}
(* Aux-Subst.  A classical variable the program never reads and never writes
   is an AUXILIARY variable: the triple holds whatever its value, so it may
   be replaced by any value throughout.

   This is what turns QHL+'s (Axiom-Meas) into a branch.  That axiom names
   the outcome with a fresh y and its freshness condition forbids the
   precondition from saying what y is, so on its own it can only ever
   conclude "m = y".  Substituting a value for y afterwards gives "m = 0",
   and only literal guards like that are mutually exclusive — which is
   exactly what Branch-Accum asks of its family. *)
| rule_aux_subst : forall Q R P y (v : val),
    ~ In y (program_cvar P) ->
    Σ ⊢ₚ {{ Q }} P {{ R }} ->
    Σ ⊢ₚ {{ assertion_subst Q y (e_val v) }} P {{ assertion_subst R y (e_val v) }}
(* Conseq (same wf_assertion side condition as the local rule). *)
| rule_conseq_d : forall Q Q' R R' P,
    Q' ⊨[Σ] Q ->
    Σ ⊢ₚ {{ Q }} P {{ R }} ->
    R ⊨[Σ] R' ->
    wf_assertion Σ R' ->
    Σ ⊢ₚ {{ Q' }} P {{ R' }}

where "Σ '⊢ₚ' '{{' Pre '}}' P '{{' Post '}}'" := (derivable Σ Pre P Post).
