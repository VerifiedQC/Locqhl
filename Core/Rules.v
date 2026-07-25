(** * Rules — the local proof rules of the LOCC proof system.
      φ[e/x], A[e/x]      substitution   = precompose with a store update
      F_U(t)[q̄](A)        unitary  wp    = U† A U
      F_M(y)[q̄](A)        measure  wp    = M_y† A M_y   (outcome read from y)
      y ∉ free(φ) ∪ cv(A) freshness      = "the assertion does not depend on y"
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From QuantumLib Require Import Matrix Quantum.
From Locqhl.Core Require Import Syntax QuantumActions SemanticDomain Semantics Assertions WellFormed.
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

(* Conseq *)
| rule_conseq : forall Q Q' R R' L,
    Q' ⊨[Σ] Q ->
    Σ ⊢ₗ {{ Q }} L {{ R }} ->
    R ⊨[Σ] R' ->
    Σ ⊢ₗ {{ Q' }} L {{ R' }}

where "Σ '⊢ₗ' '{{' Pre '}}' L '{{' Post '}}'" := (local_derivable Σ Pre L Post).


(** ** Row shapes of the distributed rules ****************************

      D₁‖…‖D_N      locals_seq   (with its left-to-right sequentialisation)
      ε_K‖…‖ε_K     all_comm_done
      (Dᵢ;Kᵢ;Tᵢ)‖…  zip3 of the D-, K- and T-rows
*********************************************************************)

Inductive locals_seq : program -> lblock -> Prop :=
| lsq_leaf : forall D, locals_seq (⟨ₗ D ⟩) D
| lsq_par  : forall P1 P2 D1 D2,
    locals_seq P1 D1 ->
    locals_seq P2 D2 ->
    locals_seq (pg_par P1 P2) (l_seq D1 D2).

Inductive all_comm_done : program -> Prop :=
| acd_leaf : all_comm_done (⟨ₖ [] ⟩)
| acd_par  : forall P1 P2,
    all_comm_done P1 ->
    all_comm_done P2 ->
    all_comm_done (pg_par P1 P2).

(** The D-, K- and T-rows have the same tree shape and zip leafwise into
    the program of phases. **)
Inductive zip3 : program -> program -> program -> program -> Prop :=
| zip3_leaf : forall D K T,
    zip3 (⟨ₗ D ⟩) (⟨ₖ K ⟩) (⟨ₛ T ⟩)
         (pg_comp (comp_proc (phase (r_more D) K T)))
| zip3_par : forall d1 d2 k1 k2 t1 t2 z1 z2,
    zip3 d1 k1 t1 z1 ->
    zip3 d2 k2 t2 z2 ->
    zip3 (pg_par d1 d2) (pg_par k1 k2) (pg_par t1 t2) (pg_par z1 z2).

(** ** Helpers for Branch-Accum *************************************** *)

(** Σ_{i∈J} A_i over a NON-EMPTY family (there is no zero predicate). **)
Definition qsum {dim} (A0 : qpred dim) (As : list (qpred dim)) : qpred dim :=
  fold_right q_add A0 As.

(** ⋁_{i∈J} ψ_i over a non-empty family. **)
Definition fdisj (p0 : formula) (ps : list formula) : formula :=
  fold_right f_or p0 ps.

(** ⊨ ¬(ψ_i ∧ ψ_j): the two guards never hold at the same store. **)
Definition exclusive {dim} (Σ : interp dim) (p q : formula) : Prop :=
  forall s, formula_holds Σ s p = true -> formula_holds Σ s q = true -> False.

(** Build a cq-assertion (φ, A) from a classical formula and a quantum predicate. **)
Definition mk_assertion {dim} (p : formula) (A : qpred dim) : assertion dim :=
  {| classical_part := p; quantum_part := A |}.

(** ** The distributed proof system *********************************** *)

Reserved Notation "Σ '⊢ₚ' '{{' Pre '}}' P '{{' Post '}}'"
  (at level 70, Pre at level 99, P at level 99, Post at level 99).

Inductive derivable {dim} (Σ : interp dim)
    : assertion dim -> program -> assertion dim -> Prop :=
(* Par-Disjoint-MP.  DisjMP is not a premise: well-formedness supplies it
   (Theorem 2.1). *)
| rule_par_disjoint : forall Q R PD Dseq,
    locals_seq PD Dseq ->
    Σ ⊢ₗ {{ Q }} Dseq {{ R }} ->
    Σ ⊢ₚ {{ Q }} PD {{ R }}
(* Comm-Done. *)
| rule_comm_done : forall Q PK,
    all_comm_done PK ->
    Σ ⊢ₚ {{ Q }} PK {{ Q }}
(* Comm-Select-MP: consume one matched endpoint from the sender leaf and
   the receiver leaf, in place. *)
| rule_comm_select : forall Q R PK P1 PK' Ki Ki' Kj Kj' c e x,
    replace_leaf (comp_comm Ki) (comp_comm Ki') PK P1 ->
    replace_leaf (comp_comm Kj) (comp_comm Kj') P1 PK' ->
    selects Ki (c_send c e) Ki' ->
    selects Kj (c_recv c x) Kj' ->
    Σ ⊢ₚ {{ Q }} PK' {{ R }} ->
    Σ ⊢ₚ {{ assertion_subst Q x e }} PK {{ R }}
(* Par-Comp-MP.  [wf_program] is the paper's "rule instances range over
   well-formed core programs" (p.13). *)
| rule_par_comp : forall Q0 Q1 Q2 Q3 PD PK PT P,
    zip3 PD PK PT P ->
    wf_program P ->
    Σ ⊢ₚ {{ Q0 }} PD {{ Q1 }} ->
    Σ ⊢ₚ {{ Q1 }} PK {{ Q2 }} ->
    Σ ⊢ₚ {{ Q2 }} PT {{ Q3 }} ->
    Σ ⊢ₚ {{ Q0 }} P {{ Q3 }}
(* Branch-Accum. *)
| rule_branch_accum : forall phi B P A0 psi0 fam,
    Σ ⊢ₚ {{ mk_assertion phi A0 }} P {{ mk_assertion psi0 B }} ->
    Forall (fun Api => Σ ⊢ₚ {{ mk_assertion phi (fst Api) }} P {{ mk_assertion (snd Api) B }}) fam ->
    ForallOrdPairs (exclusive Σ) (psi0 :: map snd fam) ->
    Σ ⊢ₚ {{ mk_assertion phi (qsum A0 (map fst fam)) }} P
        {{ mk_assertion (fdisj psi0 (map snd fam)) B }}
(* Conseq *)
| rule_conseq_d : forall Q Q' R R' P,
    Q' ⊨[Σ] Q ->
    Σ ⊢ₚ {{ Q }} P {{ R }} ->
    R ⊨[Σ] R' ->
    Σ ⊢ₚ {{ Q' }} P {{ R' }}

where "Σ '⊢ₚ' '{{' Pre '}}' P '{{' Post '}}'" := (derivable Σ Pre P Post).
