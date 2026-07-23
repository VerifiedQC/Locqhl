(** * Syntax — the LOCC language (Section: Programs, Syntax and Semantics).

      e ::= v | x | f(e_1..e_k)
      b ::= true | false | R(e_1..e_k) | not b | b /\ b | b \/ b
      L ::= skip | x := e | q := |0> | U[q_1..q_n] | x := M[q_1..q_n]
          | L ; L | if b then L else L
      alpha ::= c!e | c?x
      K ::= eps | alpha | K [] K
      S ::= L_0 ; K_0 ; L_1 ; K_1 ; ... ; L_r ; K_r ; L_{r+1}   (r >= 0)
      P ::= S_1 || ... || S_n
* **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

(** ** Alphabets (the grammar's terminals) * **)

(* Identifiers. *)
Definition var   : Type := nat.   (* classical variables   x in Var   *)
Definition qvar  : Type := nat.   (* quantum variables      q in qVar  *)
Definition chan  : Type := nat.   (* communication channels c in Chan  *)
Definition party : Type := nat.   (* component index in S_1 || .. || S_n *)

(* Operator / value symbols, interpreted later. *)
Definition val    : Type := nat.  (* values          v in Val *)
Definition funsym : Type := nat.  (* function symbols f in F   *)
Definition relsym : Type := nat.  (* relation symbols R in R   *)
Definition usym   : Type := nat.  (* unitary symbols  U in U   *)
Definition msym   : Type := nat.  (* measurement syms M in M   *)

(** ** Expressions and Boolean conditions *)
Inductive expr : Type :=
| e_val : val -> expr                    (* v *)
| e_var : var -> expr                    (* x *)
| e_app : funsym -> list expr -> expr.   (* f(e_1..e_k) *)

Inductive bexpr : Type :=
| b_true  : bexpr                        (* true  *)
| b_false : bexpr                        (* false *)
| b_rel   : relsym -> list expr -> bexpr (* R(e_1..e_k) *)
| b_not   : bexpr -> bexpr               (* not b *)
| b_and   : bexpr -> bexpr -> bexpr      (* b /\ b *)
| b_or    : bexpr -> bexpr -> bexpr.     (* b \/ b *)

(** ** Local blocks ** **)
Inductive lblock : Type :=
| l_skip   : lblock                             (* skip *)
| l_assign : var -> expr -> lblock              (* x := e *)
| l_init   : qvar -> lblock                     (* q := |0> *)
| l_ugate  : usym -> list qvar -> lblock        (* U[q_1..q_n] *)
| l_meas   : var -> msym -> list qvar -> lblock (* x := M[q_1..q_n] *)
| l_seq    : lblock -> lblock -> lblock         (* L ; L *)
| l_if     : bexpr -> lblock -> lblock -> lblock. (* if b then L else L *)

(** ** Communication actions and blocks *)
Inductive caction : Type :=
| c_send : chan -> expr -> caction   (* c!e *)
| c_recv : chan -> var -> caction.   (* c?x *)

(* A communication block is a finite unordered collection of one-shot
   endpoints.
   We represent it directly as a list of endpoints: 
   [] is ε_K, and □ is list append. *)
Definition cblock : Type := list caction.

(** ** Local residuals — what is left of a local block.
       This is syntax (↓, or a command that still remains), so it lives
       here with the language rather than in the semantic domain. ** **)
Inductive residual : Type :=
| r_done : residual              (* ↓ *)
| r_more : lblock -> residual.   (* a command remains *)

Notation "'↓'" := r_done (at level 0).

(** ** Processes. ** **)
Inductive process : Type :=
| terminated : process                                (* ↓ *)
| phase      : residual -> cblock -> process -> process. (* (L;K) ; S *)

Definition program : Type := list process.   (* P ::= S_1 ‖ … ‖ S_n *)

(** ** Variables of, and substitution into, program expressions ******** *)

Fixpoint expr_vars (e : expr) : list var :=
  match e with
  | e_val _    => []
  | e_var x    => [x]
  | e_app _ es => (fix go (l : list expr) : list var :=
                     match l with
                     | []       => []
                     | e' :: l' => expr_vars e' ++ go l'
                     end) es
  end.

Fixpoint expr_subst (e : expr) (x : var) (t : expr) : expr :=
  match e with
  | e_val v    => e_val v
  | e_var y    => if Nat.eqb x y then t else e_var y
  | e_app f es => e_app f ((fix go (l : list expr) : list expr :=
                              match l with
                              | []       => []
                              | e' :: l' => expr_subst e' x t :: go l'
                              end) es)
  end.

Fixpoint bexpr_vars (b : bexpr) : list var :=
  match b with
  | b_true       => []
  | b_false      => []
  | b_rel _ es   => flat_map expr_vars es
  | b_not b1     => bexpr_vars b1
  | b_and b1 b2  => bexpr_vars b1 ++ bexpr_vars b2
  | b_or  b1 b2  => bexpr_vars b1 ++ bexpr_vars b2
  end.

Fixpoint bexpr_subst (b : bexpr) (x : var) (t : expr) : bexpr :=
  match b with
  | b_true       => b_true
  | b_false      => b_false
  | b_rel R es   => b_rel R (map (fun e => expr_subst e x t) es)
  | b_not b1     => b_not (bexpr_subst b1 x t)
  | b_and b1 b2  => b_and (bexpr_subst b1 x t) (bexpr_subst b2 x t)
  | b_or  b1 b2  => b_or  (bexpr_subst b1 x t) (bexpr_subst b2 x t)
  end.


(** ** Notation approximating the paper's syntax table. ** **)
Declare Custom Entry com.
Declare Scope com_scope.
Delimit Scope com_scope with com.
Open Scope com_scope.

Notation "<{ L }>" := L (L custom com at level 99) : com_scope.
Notation "( L )" := L (in custom com, L at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.

Notation "'skip'" := l_skip
  (in custom com at level 0) : com_scope.
Notation "x := e" := (l_assign x e)
  (in custom com at level 0, x constr at level 0, e constr at level 0) : com_scope.
Notation "'init' q" := (l_init q)
  (in custom com at level 0, q constr at level 0) : com_scope.
Notation "U @ qs" := (l_ugate U qs)
  (in custom com at level 0, U constr at level 0, qs constr at level 0) : com_scope.
Notation "x <- M @ qs" := (l_meas x M qs)
  (in custom com at level 0, x constr at level 0, M constr at level 0, qs constr at level 0) : com_scope.
Notation "c1 ; c2" := (l_seq c1 c2)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'if' b 'then' c1 'else' c0" := (l_if b c1 c0)
  (in custom com at level 89, b constr at level 0,
      c1 custom com at level 99, c0 custom com at level 99) : com_scope.


(** ** Notation for the distributed-program layer (α, K, S, P).

    Mirrors the paper's surface syntax:
      c ! e      communication output  (c_send)
      c ? x      communication input   (c_recv)
      ε              empty communication block  ε_K
      [ α ; β ]      communication block  α □ β    (a [cblock] is a list)
      L ⨾ K ⨾ S      one phase: local block L, comm block K, then S
      [ S ; T ]      distributed program  S ‖ T    (a [program] is a list)
    A phase whose local block has already finished is written out directly
    as [phase ↓ K S].
** **)
Declare Scope proc_scope.
Delimit Scope proc_scope with proc.

Notation "c '!' e" := (c_send c e)
  (at level 60, no associativity) : proc_scope.
Notation "c '?' x" := (c_recv c x)
  (at level 60, no associativity) : proc_scope.
Notation "'ε'" := (@nil caction) : proc_scope.
Notation "L '⨾' K '⨾' S" := (phase (r_more L) K S)
  (at level 100, K at level 99, right associativity) : proc_scope.

Open Scope proc_scope.
