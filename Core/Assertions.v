(** * Assertions — cq-assertions (deep), their degree, entailment, validity.

    A cq-assertion is a pair (φ, A): a classical first-order formula and a
    quantum predicate formula parameterised by classical variables.

    Both are SYNTAX, so the paper's syntactic operations are syntactic here
    too — which is what lets the proof rules stay syntax-directed:

      free(φ), cv(A)   computed by [formula_vars] / [qpred_vars]
      φ[e/x], A[e/x]   computed by [formula_subst] / [qpred_subst]

    Quantum predicates are "semi-deep": the OPERATOR is built by a semantic
    function, but its CLASSICAL PARAMETERS are syntactic expressions.  That
    is exactly the level the paper's side conditions need — they only ever
    ask which classical variables A mentions — and it avoids inventing a
    whole matrix-expression language.

    [None] models the paper's "A is not defined in σ".
** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Reals.Reals.
From QuantumLib Require Import Matrix Quantum.
From Locqhl.Core Require Import Syntax QuantumActions SemanticDomain Semantics.
Import ListNotations.

Local Open Scope R_scope.

(** ** Classical assertion formulas ********************************** *)
Inductive formula : Type :=
| f_bexp : bexpr -> formula          (* a program condition, e.g. an if-guard *)
| f_eq   : expr -> expr -> formula   (* e1 = e2, as needed by Meas *)
| f_not  : formula -> formula
| f_and  : formula -> formula -> formula
| f_or   : formula -> formula -> formula.

Fixpoint formula_vars (p : formula) : list var :=
  match p with
  | f_bexp b    => bexpr_vars b
  | f_eq e1 e2  => expr_vars e1 ++ expr_vars e2
  | f_not p1    => formula_vars p1
  | f_and p1 p2 => formula_vars p1 ++ formula_vars p2
  | f_or  p1 p2 => formula_vars p1 ++ formula_vars p2
  end.

Fixpoint formula_subst (p : formula) (x : var) (t : expr) : formula :=
  match p with
  | f_bexp b    => f_bexp (bexpr_subst b x t)
  | f_eq e1 e2  => f_eq (expr_subst e1 x t) (expr_subst e2 x t)
  | f_not p1    => f_not (formula_subst p1 x t)
  | f_and p1 p2 => f_and (formula_subst p1 x t) (formula_subst p2 x t)
  | f_or  p1 p2 => f_or  (formula_subst p1 x t) (formula_subst p2 x t)
  end.

(** σ ⊨ φ, decided by computation **)
Fixpoint formula_holds {dim} (Σ : interp dim) (s : store) (p : formula) : bool :=
  match p with
  | f_bexp b    => eval_bool (i_fn Σ) (i_rl Σ) s b
  | f_eq e1 e2  => Nat.eqb (eval_expr (i_fn Σ) s e1) (eval_expr (i_fn Σ) s e2)
  | f_not p1    => negb (formula_holds Σ s p1)
  | f_and p1 p2 => andb (formula_holds Σ s p1) (formula_holds Σ s p2)
  | f_or  p1 p2 => orb  (formula_holds Σ s p1) (formula_holds Σ s p2)
  end.

(** ** Quantum predicate formulas ************************************

        ⟦A⟧ : States ⇀ { M | 0 ⊑ M ⊑ I }            σ ↦ σ(A)

    [q_op f ē] says this family FACTORS THROUGH the values of finitely many
    classical expressions ē = e₁,…,e_k:

        σ( q_op f ē )  =  f( ⟦e₁⟧σ , … , ⟦e_k⟧σ )      f : Val^k ⇀ Effects
        
    [q_conj g ē A] denotes  K† · σ(A) · K  with  K = g(⟦ē⟧σ).  It is a
    separate constructor because [q_op] is a leaf and cannot carry a
    sub-predicate, while the two backward rules must WRAP an existing A:

        Unitary :  F_U(A)    = U†   A U       = q_conj (fun _ => U) ε A
        Meas    :  F_M(y)(A) = M_y† A M_y     = q_conj (…) [e_var y] A

    Writing the Meas outcome as the syntactic argument [e_var y] is what puts
    y into [qpred_vars], which is what makes the freshness check real.
*********************************************************************)
Inductive qpred (dim : nat) : Type :=
| q_op   : (list val -> option (Square (2 ^ dim))) -> list expr -> qpred dim
| q_conj : (list val -> Square (2 ^ dim)) -> list expr -> qpred dim -> qpred dim
| q_add  : qpred dim -> qpred dim -> qpred dim.   (* A + B, for Branch-Accum *)

Arguments q_op {dim}. Arguments q_conj {dim}. Arguments q_add {dim}.

Fixpoint qpred_vars {dim} (A : qpred dim) : list var :=
  match A with
  | q_op _ args      => flat_map expr_vars args
  | q_conj _ args A' => flat_map expr_vars args ++ qpred_vars A'
  | q_add A1 A2      => qpred_vars A1 ++ qpred_vars A2
  end.

Fixpoint qpred_subst {dim} (A : qpred dim) (x : var) (t : expr) : qpred dim :=
  match A with
  | q_op f args      => q_op f (map (fun e => expr_subst e x t) args)
  | q_conj g args A' => q_conj g (map (fun e => expr_subst e x t) args)
                                (qpred_subst A' x t)
  | q_add A1 A2      => q_add (qpred_subst A1 x t) (qpred_subst A2 x t)
  end.

(** ⟦A⟧_σ **)
Fixpoint qpred_denote {dim} (Σ : interp dim) (s : store) (A : qpred dim)
  : option (Square (2 ^ dim)) :=
  match A with
  | q_op f args => f (map (eval_expr (i_fn Σ) s) args)
  | q_conj g args A' =>
      match qpred_denote Σ s A' with
      | Some M => let K := g (map (eval_expr (i_fn Σ) s) args) in
                  Some (K† × M × K)%M
      | None   => None
      end
  | q_add A1 A2 =>
      match qpred_denote Σ s A1, qpred_denote Σ s A2 with
      | Some M1, Some M2 => Some (M1 .+ M2)%M
      | _, _             => None        (* a sum is undefined if a summand is *)
      end
  end.

(** ** cq-assertions ************************************************** *)

Record assertion (dim : nat) := {
  classical_part : formula;
  quantum_part   : qpred dim
}.
Arguments classical_part {dim}. Arguments quantum_part {dim}.

(** free(φ) ∪ cv(A) — a genuine syntactic computation. **)
Definition assertion_vars {dim} (Q : assertion dim) : list var :=
  formula_vars (classical_part Q) ++ qpred_vars (quantum_part Q).

(** (φ[e/x], A[e/x]) — genuine syntactic substitution. **)
Definition assertion_subst {dim} (Q : assertion dim) (x : var) (t : expr)
  : assertion dim :=
  {| classical_part := formula_subst (classical_part Q) x t;
     quantum_part   := qpred_subst   (quantum_part Q)   x t |}.

(** "A is defined in σ". **)
Definition defined_in {dim} (Σ : interp dim) (Q : assertion dim) (s : store) : Prop :=
  exists M, qpred_denote Σ s (quantum_part Q) = Some M.

(** ** Löwner order and effects ************************************** *)

Definition lowner {n} (M N : Square n) : Prop :=
  positive_semidefinite (N .+ (- C1) .* M)%M.

Notation "M ⊑ N" := (lowner M N) (at level 70).

Definition is_effect {dim} (M : Square (2 ^ dim)) : Prop :=
  positive_semidefinite M /\ M ⊑ I (2 ^ dim).

Definition wf_assertion {dim} (Σ : interp dim) (Q : assertion dim) : Prop :=
  forall s M, qpred_denote Σ s (quantum_part Q) = Some M -> is_effect M.

(** ** Satisfaction degree ******************************************* *)

(** tr(⟦A⟧_σ ρ) when σ ⊨ φ and A is defined in σ, else 0. **)
Definition degree {dim} (Σ : interp dim) (Q : assertion dim) (st : cqstate dim) : R :=
  let (s, r) := st in
  if formula_holds Σ s (classical_part Q) then
    match qpred_denote Σ s (quantum_part Q) with
    | Some M => fst (trace (M × r)%M)
    | None   => 0
    end
  else 0.

Definition total_degree {dim} (Σ : interp dim) (Q : assertion dim)
                        (E : ensemble dim) : R :=
  fold_right Rplus 0 (map (degree Σ Q) E).

(** ** Entailment  (φ,A) ⊨ (ψ,B) ************************************* *)

Definition entails {dim} (Σ : interp dim) (Q1 Q2 : assertion dim) : Prop :=
  (forall s, formula_holds Σ s (classical_part Q1) = true ->
             formula_holds Σ s (classical_part Q2) = true)
  /\ (forall s, formula_holds Σ s (classical_part Q1) = true ->
                defined_in Σ Q1 s -> defined_in Σ Q2 s)
  /\ (forall s M N, formula_holds Σ s (classical_part Q1) = true ->
        qpred_denote Σ s (quantum_part Q1) = Some M ->
        qpred_denote Σ s (quantum_part Q2) = Some N -> M ⊑ N).

(** ** Validity of a correctness formula ***************************** *)

Definition valid {dim} (Σ : interp dim)
                 (Pre : assertion dim) (P : program) (Post : assertion dim) : Prop :=
  forall (s : store) (r : qstate dim),
    formula_holds Σ s (classical_part Pre) = true ->
    defined_in Σ Pre s ->
    forall E, Term Σ P (s, r) E ->
      degree Σ Pre (s, r) <= total_degree Σ Post E.

Notation "Σ '⊨' '{{' Pre '}}' P '{{' Post '}}'" := (valid Σ Pre P Post)
  (at level 70, Pre at level 99, P at level 99, Post at level 99).
