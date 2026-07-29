(** * Names — finite sets of names * **)

From Stdlib Require Import Lists.List.
Import ListNotations.

Definition names : Type := list nat.

Definition disjoint (xs ys : names) : Prop :=
  forall x, In x xs -> ~ In x ys.
