(** * Semantics — the operational semantics of LOCC (Figure 2). * **)

From QuantumLib Require Import Matrix.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Locqhl.Core Require Import Syntax QuantumActions SemanticDomain.
Import ListNotations.

(** ** The fixed structure Σ ******************************************

    The paper interprets the symbol alphabets by a fixed classical structure
    (function/relation symbols) and a fixed quantum structure (unitary and
    measurement symbols).  We bundle all four into one record [interp], so a
    step judgment reads  [Σ ⊳ (L, E) →ₗ G]  — a relation "against Σ".
*********************************************************************)
Record interp (dim : nat) := {
  i_fn : funsym -> list val -> val;
  i_rl : relsym -> list val -> bool;
  i_uu : usym  -> list qvar -> Square (2 ^ dim);
  i_mm : msym  -> list qvar -> measurement dim
}.
Arguments i_fn {dim}. Arguments i_rl {dim}. Arguments i_uu {dim}. Arguments i_mm {dim}.

(** Σ is standard on the three comparison symbols of Syntax when it reads
    them the way their names promise.  Protocol guards are written with
    [b_eq]/[b_lt]/[b_gt], so a case study that needs to evaluate a guard
    assumes this of its Σ and nothing else about the relation alphabet.

    Note the explicit [cons]: a bare [ .. ; .. ] right after a term is read
    as SemanticDomain's store update s[x |-> v]. **)
Definition standard_rels {dim} (Σ : interp dim) : Prop :=
  (forall a b, i_rl Σ r_eq (cons a (cons b nil)) = Nat.eqb a b)
  /\ (forall a b, i_rl Σ r_lt (cons a (cons b nil)) = Nat.ltb a b)
  /\ (forall a b, i_rl Σ r_gt (cons a (cons b nil)) = Nat.ltb b a).

Reserved Notation "Σ '⊳' '‹' L ',' E '›' '→ₗ' G"
  (at level 70, L at level 99, E at level 99).
Reserved Notation "Σ '⊳' '‹' D ',' E '›' '⇝' G"
  (at level 70, D at level 99, E at level 99).

(** ** Local step  ** **)
Inductive local_step {dim} (Σ : interp dim)
    : lblock -> ensemble dim -> local_config dim -> Prop :=
| local_step_skip : forall E,
    Σ ⊳ ‹ <{ skip }>, E › →ₗ {|| ↓, E ||}
| local_step_assign : forall x e E,
    Σ ⊳ ‹ <{ x := e }>, E › →ₗ
      {|| ↓, map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
| local_step_init : forall q E,
    Σ ⊳ ‹ <{ init q }>, E › →ₗ
      {|| ↓, map (fun '(s,r) => (s, apply_init q r)) E ||}
| local_step_ugate : forall U qs E,
    Σ ⊳ ‹ <{ U @ qs }>, E › →ₗ
      {|| ↓, map (fun '(s,r) => (s, apply_unitary (i_uu Σ U qs) r)) E ||}
| local_step_meas : forall x M qs E,
    Σ ⊳ ‹ <{ x <- M @ qs }>, E › →ₗ
      {|| ↓, flat_map (fun '(s,r) =>
              map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r))
                  (fst (i_mm Σ M qs))) E ||}
| local_step_seq : forall L1 L2 E G,
    Σ ⊳ ‹ L1, E › →ₗ G ->
    Σ ⊳ ‹ <{ L1 ; L2 }>, E › →ₗ
      map (fun c => match fst c with
                    | r_done     => (r_more L2, snd c)
                    | r_more L1' => (r_more <{ L1' ; L2 }>, snd c)
                    end) G
| local_step_if : forall b L1 L0 E,
    Σ ⊳ ‹ <{ if b then L1 else L0 }>, E › →ₗ
        {|| r_more L1, ensemble_filter (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E ||}
      ⊎ {|| r_more L0, ensemble_filter (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E ||}
where "Σ '⊳' '‹' L ',' E '›' '→ₗ' G" := (local_step Σ L E G).

(** ** Distributed step (Fig. 2(b)).
      ds_local       one local ensemble step at a leaf
      ds_par_l/r     the step happens inside one subtree
      ds_comm_lr/rl  one atomic rendezvous; the sender and receiver leaves
                     are located by [replace_leaf] in the two subtrees of
                     their least common ∥ node

    A leaf now IS a process, so each rule matches the leaf's head phase
    directly instead of asking what a component reads as.  Every residual
    leaf is rebuilt with [advance], which is what keeps the ε_K erasure of
    p.7 true of reachable programs: a leaf never carries an exhausted
    phase ↓;ε_K, since [advance] drops it. **)
Inductive distri_step {dim} (Σ : interp dim)
    : program -> ensemble dim -> distri_config dim -> Prop :=
(* (Local) at a leaf *)
| ds_local : forall (L : lblock) (K : cblock) (T : process)
                    (E : ensemble dim) (Gl : local_config dim),
    Σ ⊳ ‹ L, E › →ₗ Gl ->
    Σ ⊳ ‹ ⟨ phase (r_more L) K T ⟩, E › ⇝
      map (fun c => (⟨ advance (fst c) K T ⟩, snd c)) Gl
(* the step happens in the left / right subtree *)
| ds_par_l : forall (P1 P2 : program) (E : ensemble dim) (G1 : distri_config dim),
    Σ ⊳ ‹ P1, E › ⇝ G1 ->
    Σ ⊳ ‹ P1 ∥ P2, E › ⇝
      map (fun c => (fst c ∥ P2, snd c)) G1
| ds_par_r : forall (P1 P2 : program) (E : ensemble dim) (G2 : distri_config dim),
    Σ ⊳ ‹ P2, E › ⇝ G2 ->
    Σ ⊳ ‹ P1 ∥ P2, E › ⇝
      map (fun c => (P1 ∥ fst c, snd c)) G2
(* (Communicate): sender leaf in the left subtree, receiver in the right *)
| ds_comm_lr : forall (P1 P1' P2 P2' : program)
                      (Ks Ks' Kr Kr' : cblock) (Ts Tr : process)
                      (c : chan) (e : expr) (x : var) (E : ensemble dim),
    Ks ∋ c_send c e □ Ks' ->
    Kr ∋ c_recv c x □ Kr' ->
    replace_leaf (phase ↓ Ks Ts) (advance ↓ Ks' Ts) P1 P1' ->
    replace_leaf (phase ↓ Kr Tr) (advance ↓ Kr' Tr) P2 P2' ->
    Σ ⊳ ‹ P1 ∥ P2, E › ⇝
      {|| P1' ∥ P2',
        map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
(* (Communicate): sender leaf in the right subtree, receiver in the left *)
| ds_comm_rl : forall (P1 P1' P2 P2' : program)
                      (Ks Ks' Kr Kr' : cblock) (Ts Tr : process)
                      (c : chan) (e : expr) (x : var) (E : ensemble dim),
    Ks ∋ c_send c e □ Ks' ->
    Kr ∋ c_recv c x □ Kr' ->
    replace_leaf (phase ↓ Ks Ts) (advance ↓ Ks' Ts) P2 P2' ->
    replace_leaf (phase ↓ Kr Tr) (advance ↓ Kr' Tr) P1 P1' ->
    Σ ⊳ ‹ P1 ∥ P2, E › ⇝
      {|| P1' ∥ P2',
        map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
where "Σ '⊳' '‹' D ',' E '›' '⇝' G" := (distri_step Σ D E G).


(** One step of a whole mixed configuration: pick ANY branch component — ⊎
    is an unordered multiset union, hence the [Permutation] premise — step
    it with [distri_step], renormalise:  (D,E) ⊎ G₀ ⇝ norm(G₁ ⊎ G₀). **)
Inductive mixed_step {dim} (Σ : interp dim)
    : distri_config dim -> distri_config dim -> Prop :=
| mixed_lift : forall (G : distri_config dim) (D : program) (E : ensemble dim)
                      (G0 : distri_config dim) (G1 : distri_config dim),
    Permutation G ((D, E) :: G0) ->
    Σ ⊳ ‹ D, E › ⇝ G1 ->
    mixed_step Σ G (norm (G1 ⊎ G0)).

(** Reflexive–transitive closure:  ⇝*  **)
Inductive step_star {dim} (Σ : interp dim)
    : distri_config dim -> distri_config dim -> Prop :=
| star_refl : forall G, step_star Σ G G
| star_step : forall G1 G2 G3,
    mixed_step Σ G1 G2 -> step_star Σ G2 G3 -> step_star Σ G1 G3.

(** Term(P, σ, ρ)  ≜  { coll(G) | (P, {|(σ,ρ)|}) ⇝* G, G terminal }. **)
Definition Term {dim} (Σ : interp dim) (P : program) (st : cqstate dim)
                (E : ensemble dim) : Prop :=
  exists G, step_star Σ ({|| P, [st] ||}) G /\ terminal G /\ collapse G = E.
