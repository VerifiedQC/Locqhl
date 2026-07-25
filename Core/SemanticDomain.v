(** * SemanticDomain — classical stores, cq-states, and cq-ensembles. ** **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.
From Locqhl.Core Require Import Syntax QuantumActions.

(** ** Classical stores ** **)
Definition store : Type := var -> val.

Definition store_update (s : store) (x : var) (v : val) : store :=
  fun y => if Nat.eqb x y then v else s y.

Notation "s [ x |-> v ]" := (store_update s x v)
  (at level 9, x at level 0).

(** ** cq-states ** **)
Definition cqstate (dim : nat) : Type := store * qstate dim.

(** ** cq-ensembles ** **)
Definition ensemble (dim : nat) : Type := list (cqstate dim).

(** filtering 𝔼↾p on the *store* component. ** **)
Definition ensemble_filter {dim} (p : store -> bool) (E : ensemble dim) : ensemble dim :=
  filter (fun st => p (fst st)) E.


(** ** Mixed configurations -
    a finite multiset of (residual, ensemble) components
    G = ⊎_r (D_r, E_r) *)
Definition local_config (dim : nat) : Type := list (residual * ensemble dim).

(** ** Display notations:
      {|| R , E ||}    a single component of a result     ({| (R, E) |})
      G1 ⊎ G2      multiset union of results          (list append)
    These are polymorphic in R, so they serve both the local result type
    [local_config] (R = residual) and the distributed one (R = program).
    (↓ itself is a Syntax.v notation, next to [residual].) ** **)
Notation "'{||' R ',' E '||}'" := (cons (R, E) nil)
  (at level 0, R at level 99, E at level 99).
Notation "G1 '⊎' G2" := (app G1 G2)
  (at level 65, right associativity).


(** Distributed mixed configuration  G = ⊎_r (D_r, E_r). **)
Definition distri_config (dim : nat) : Type := list (program * ensemble dim).


(** ** Evaluation ** **)
(** ⟦e⟧σ. **)
Definition eval_expr (fn : funsym -> list val -> val) (s : store) : expr -> val :=
  fix ev (e : expr) : val :=
    match e with
    | e_val v => v
    | e_var x => s x
    | e_app f args =>
        fn f ((fix ev_args (es : list expr) : list val :=
                 match es with
                 | []        => []
                 | e' :: es' => ev e' :: ev_args es'
                 end) args)
    end.

(** ⟦b⟧σ. **)
Definition eval_bool (fn : funsym -> list val -> val)
                     (rl : relsym -> list val -> bool) (s : store) : bexpr -> bool :=
  fix ev (b : bexpr) : bool :=
    match b with
    | b_true       => true
    | b_false      => false
    | b_rel R args => rl R (map (eval_expr fn s) args)
    | b_not b1     => negb (ev b1)
    | b_and b1 b2  => andb (ev b1) (ev b2)
    | b_or  b1 b2  => orb  (ev b1) (ev b2)
    end.



(** ** Operations on mixed configurations ******************************

    Everything here is a plain operation on a [distri_config]; none of it
    mentions the step relation, which is why it lives in the domain rather
    than in Semantics.v.
*********************************************************************)

(** A mixed configuration is terminal when every program has terminated. **)
Definition terminal {dim} (G : distri_config dim) : Prop :=
  Forall (fun c => prog_terminated (fst c)) G.

(** Terminal collapse:  coll(⊎_r (↓, E_r)) ≜ ⊎_r E_r. **)
Definition collapse {dim} (G : distri_config dim) : ensemble dim :=
  flat_map snd G.

(** Normalisation.  **)
Definition norm {dim} (G : distri_config dim) : distri_config dim :=
  filter (fun c => match snd c with [] => false | _ :: _ => true end) G.
