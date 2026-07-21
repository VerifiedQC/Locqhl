(** * Names — finite sets of names * **)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

(** ** Finite name sets ** **)
Definition names : Type := list nat.

Definition empty : names := [].

Definition mem (x : nat) (xs : names) : bool := 
  existsb (Nat.eqb x) xs.

Definition add (x : nat) (xs : names) : names :=
  if mem x xs then xs else x :: xs.

Fixpoint union (xs ys : names) : names :=
  match xs with
  | []        => ys
  | x :: xs'  => add x (union xs' ys)
  end.

Definition unions (xss : list names) : names := 
  fold_right union empty xss.

Definition disjoint (xs ys : names) : Prop :=
  forall x, In x xs -> ~ In x ys.

Definition subset (xs ys : names) : Prop :=
  forall x, In x xs -> In x ys.
