(** * Syntax — the LOCC language (Section: Programs, Syntax and Semantics).

      e ::= v | x | f(e_1..e_k)
      b ::= true | false | R(e_1..e_k) | not b | b /\ b | b \/ b
      L ::= skip | x := e | q := |0> | U[q_1..q_n] | x := M[q_1..q_n]
          | L ; L | if b then L else L
      alpha ::= c!e | c?x
      K ::= eps | alpha | K [] K
      S ::= L_0 ; K_0 ; L_1 ; K_1 ; ... ; L_r ; K_r ; L_{r+1}   (r >= 0)
      P ::= S_1 || ... || S_n

    The parallel layer is ONE tree functor [row A], instantiated three times.
    The proof system's three subjects — the paper's

      D_1 || ... || D_N     the current communication-free prefixes
      K_1 || ... || K_N     the current communication phase
      S_1 || ... || S_N     the program itself

    — differ only in what sits at a leaf, so they are [row lblock],
    [row cblock] and [row process].  A row is what a rule is ABOUT; it is
    not carved out of the program type by a side predicate.
* **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

(** ** Alphabets (the grammar's terminals) * **)

(* Identifiers. *)
Definition var   : Type := nat.   (* classical variables   x in Var   *)
Definition qvar  : Type := nat.   (* quantum variables      q in qVar  *)
Definition chan  : Type := nat.   (* communication channels c in Chan  *)

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

(** The relation alphabet R is arbitrary, but the guards an LOCC protocol
    actually writes are comparisons of classical values, and three of them
    suffice for every protocol in the paper.  Fix canonical symbols, and
    write the guards through them rather than through raw [b_rel] and a
    numeral nobody can read.  What they MEAN is a property of the structure
    Σ, not of the syntax — see [Semantics.standard_rels]. **)
Definition r_eq : relsym := 0.   (* e₁ = e₂  *)
Definition r_lt : relsym := 1.   (* e₁ < e₂  *)
Definition r_gt : relsym := 2.   (* e₁ > e₂  *)

Definition b_eq (e1 e2 : expr) : bexpr := b_rel r_eq [e1; e2].
Definition b_lt (e1 e2 : expr) : bexpr := b_rel r_lt [e1; e2].
Definition b_gt (e1 e2 : expr) : bexpr := b_rel r_gt [e1; e2].

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

(** Selecting one endpoint out of an unordered block:  K = a □ K'.
    Structural rather than an existential over append decompositions, so a
    selection is BUILT by constructors and TAKEN APART by induction.  This
    is the one-step generator of "the block is unordered": □ is read modulo
    associativity and commutativity, and picking any occurrence is all the
    proof system ever needs of that. **)
Inductive picks : cblock -> caction -> cblock -> Prop :=
| pick_here  : forall a K,
    picks (a :: K) a K
| pick_there : forall a b K K',
    picks K a K' -> picks (b :: K) a (b :: K').

Notation "K '∋' a '□' K'" := (picks K a K')
  (at level 70, a at level 60).

(** ** Local residuals — what is left of a local block.
       This is syntax (↓, or a command that still remains), so it lives
       here with the language rather than in the semantic domain. ** **)
Inductive residual : Type :=
| r_done : residual              (* ↓ *)
| r_more : lblock -> residual.   (* a command remains *)

Notation "'↓'" := r_done (at level 0).

(** Reading a residual as the local block it still owes — the ↓ ≡ skip half
    of the erasure conventions of p.7. **)
Definition residual_lblock (R : residual) : lblock :=
  match R with r_done => l_skip | r_more L => L end.

(** ** Processes (sequential process S). ** **)
Inductive process : Type :=
| terminated : process                                (* ↓ *)
| phase      : residual -> cblock -> process -> process. (* (L;K) ; S *)

(** Rebuild a process from its head phase, applying BOTH structural
    erasures of p.7 at once:  ↓;T ≡ T  and  ε_K;T ≡ T.  When both hold the
    phase is over, so it is dropped and the process continues with its next
    one.  Every place that builds a phase — the operational semantics after
    a step, and the proof system when it cuts a program into rows — goes
    through this, so the erasure convention is honoured by construction. **)
Definition advance (R : residual) (K : cblock) (T : process) : process :=
  match R, K with
  | r_done, []  => T                 (* phase complete → on to the next *)
  | _     , _   => phase R K T
  end.

(** ** The parallel layer: one tree, three instances ****************** *)

(** A free binary tree of leaves of type A.  Well-formedness (Def 2.1) is a
    side condition on rows, not a restriction on the type: ragged async
    intermediates such as ↓ ∥ mid-phase must stay typeable. **)
Inductive row (A : Type) : Type :=
| leaf : A -> row A
| par  : row A -> row A -> row A.

Arguments leaf {A} _.
Arguments par  {A} _ _.

Notation lrow    := (row lblock).    (* D₁ ∥ … ∥ D_N *)
Notation krow    := (row cblock).    (* K₁ ∥ … ∥ K_N *)
Notation program := (row process).   (* S₁ ∥ … ∥ S_N *)

(** The generic traversals.  Every row-level notion downstream — footprints,
    disjointness, termination, the two soundness-level embeddings — is one
    of these three applied to the right leaf function, so none of it is
    written out per instance. **)
Fixpoint row_map {A B} (f : A -> B) (r : row A) : row B :=
  match r with
  | leaf a      => leaf (f a)
  | par r1 r2   => par (row_map f r1) (row_map f r2)
  end.

(** The leaves, left to right — the paper's S₁, …, S_N as a list. **)
Fixpoint row_leaves {A} (r : row A) : list A :=
  match r with
  | leaf a      => [a]
  | par r1 r2   => row_leaves r1 ++ row_leaves r2
  end.

Fixpoint row_all {A} (P : A -> Prop) (r : row A) : Prop :=
  match r with
  | leaf a      => P a
  | par r1 r2   => row_all P r1 /\ row_all P r2
  end.

(** Collect a per-leaf list, left to right.  Every footprint of a row is
    this applied to the leaf's own footprint; it is a fixpoint rather than
    [flat_map ∘ row_leaves] so that the ∥ case splits definitionally. **)
Fixpoint row_flat {A B} (f : A -> list B) (r : row A) : list B :=
  match r with
  | leaf a      => f a
  | par r1 r2   => row_flat f r1 ++ row_flat f r2
  end.

Lemma row_flat_leaves : forall {A B} (f : A -> list B) (r : row A),
    row_flat f r = flat_map f (row_leaves r).
Proof.
  intros A B f r; induction r as [a | r1 IH1 r2 IH2]; simpl.
  - rewrite app_nil_r; reflexivity.
  - rewrite flat_map_app, IH1, IH2; reflexivity.
Qed.

Lemma row_leaves_map : forall {A B} (f : A -> B) (r : row A),
    row_leaves (row_map f r) = map f (row_leaves r).
Proof.
  intros A B f r; induction r as [a | r1 IH1 r2 IH2]; simpl;
    [reflexivity | rewrite map_app, IH1, IH2; reflexivity].
Qed.

(** Termination of a program: every leaf is ↓. **)
Definition prog_terminated (P : program) : Prop :=
  row_all (fun T => T = terminated) P.

(** [replace_leaf a b r r']: r' is r with ONE leaf occurrence of a replaced
    by b, in place.  The Communicate step selects its two endpoints this
    way. **)
Inductive replace_leaf {A} (a b : A) : row A -> row A -> Prop :=
| rl_here  : replace_leaf a b (leaf a) (leaf b)
| rl_left  : forall r r' q,
    replace_leaf a b r r' -> replace_leaf a b (par r q) (par r' q)
| rl_right : forall r q q',
    replace_leaf a b q q' -> replace_leaf a b (par r q) (par r q').

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


(** ** Notation for the distributed layer (α, K, S, and rows).

    Mirrors the paper's surface syntax:
      c ! e      communication output  (c_send)
      c ? x      communication input   (c_recv)
      ε              empty communication block  ε_K
      [ α ; β ]      communication block  α □ β    (a [cblock] is a list)
      L ⨾ K ⨾ S      one phase: local block L, comm block K, then S
      p ∥ q          parallel composition of two rows  (par)
      ⟨ a ⟩          a one-leaf row  (leaf a)
    A phase whose local block has already finished is written out directly
    as [phase ↓ K S].

    There is one leaf bracket, not three: a D-row leaf holds an [lblock], a
    K-row leaf a [cblock] and a program leaf a [process], but all three are
    the same constructor, so the leaf's type is what tells them apart.  Thus
    a D-row displays as ⟨ D₁ ⟩ ∥ ⟨ D₂ ⟩ and a program as ⟨ S₁ ⟩ ∥ ⟨ S₂ ⟩.
** **)
Declare Scope proc_scope.
Delimit Scope proc_scope with proc.

(* The paper writes c!e and c?x.  A bare "!" is unusable: Corelib.Program.Utils
   declares a nullary "!" and notation GRAMMAR is global — once anything in
   the file's dependencies pulls in Program (QuantumLib does), the parser
   reads "c !" as an application, and no amount of Close Scope helps.  The
   doubled forms U+203C / U+2047 are free and keep the output/input pair
   symmetric. *)
Notation "c '‼' e" := (c_send c e)
  (at level 60, no associativity) : proc_scope.
Notation "c '⁇' x" := (c_recv c x)
  (at level 60, no associativity) : proc_scope.
Notation "'ε'" := (@nil caction) : proc_scope.
Notation "L '⨾' K '⨾' S" := (phase (r_more L) K S)
  (at level 100, K at level 99, right associativity) : proc_scope.

Notation "p '∥' q" := (par p q)
  (at level 41, right associativity) : proc_scope.
Notation "'⟨' a '⟩'" := (leaf a) (at level 0) : proc_scope.

Open Scope proc_scope.
