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
    step judgment reads  [Σ ⊢ (L, E) →ₗ G]  — a relation "against Σ".
*********************************************************************)
Record interp (dim : nat) := {
  i_fn : funsym -> list val -> val;
  i_rl : relsym -> list val -> bool;
  i_uu : usym  -> list qvar -> Square (2 ^ dim);
  i_mm : msym  -> list qvar -> measurement dim
}.
Arguments i_fn {dim}. Arguments i_rl {dim}. Arguments i_uu {dim}. Arguments i_mm {dim}.

(** Selecting one endpoint out of an unordered comm block:  K = a □ K'. **)
Definition selects (K : cblock) (a : caction) (K' : cblock) : Prop :=
  exists pre post, K = pre ++ a :: post /\ K' = pre ++ post.

Notation "K '∋' a '□' K'" := (selects K a K')
  (at level 70, a at level 60).

(** Parallel context:  l1 ‖ p ‖ l2   **)
Notation "l1 '‖' p '‖' l2" := (l1 ++ p :: l2)
  (at level 62, p at level 61, right associativity).

(** Rebuild a process from its head phase after a step, applying BOTH
    structural erasures of the paper at once:
      ↓ ; T   ≡ T   (the local block has finished)
      ε_K ; T ≡ T   (the communication block is exhausted)
    When both hold the phase itself is over, so it is dropped and the process
    continues with its next phase. **)
Definition advance (R : residual) (K : cblock) (S : process) : process :=
  match R, K with
  | r_done, []     => S             (* phase complete → on to the next one *)
  | _     , _      => phase R K S
  end.

Reserved Notation "Σ '⊢' '‹' L ',' E '›' '→ₗ' G"
  (at level 70, L at level 99, E at level 99).
Reserved Notation "Σ '⊢' '‹' D ',' E '›' '⇝' G"
  (at level 70, D at level 99, E at level 99).

(** ** Local step  ** **)
Inductive local_step {dim} (Σ : interp dim)
    : lblock -> ensemble dim -> local_config dim -> Prop :=
| local_step_skip : forall E,
    Σ ⊢ ‹ <{ skip }>, E › →ₗ {|| ↓, E ||}
| local_step_assign : forall x e E,
    Σ ⊢ ‹ <{ x := e }>, E › →ₗ
      {|| ↓, map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
| local_step_init : forall q E,
    Σ ⊢ ‹ <{ init q }>, E › →ₗ
      {|| ↓, map (fun '(s,r) => (s, apply_init q r)) E ||}
| local_step_ugate : forall U qs E,
    Σ ⊢ ‹ <{ U @ qs }>, E › →ₗ
      {|| ↓, map (fun '(s,r) => (s, apply_unitary (i_uu Σ U qs) r)) E ||}
| local_step_meas : forall x M qs E,
    Σ ⊢ ‹ <{ x <- M @ qs }>, E › →ₗ
      {|| ↓, flat_map (fun '(s,r) =>
              map (fun m => (s [ x |-> m ], apply_meas (i_mm Σ M qs) m r))
                  (fst (i_mm Σ M qs))) E ||}
| local_step_seq : forall L1 L2 E G,
    Σ ⊢ ‹ L1, E › →ₗ G ->
    Σ ⊢ ‹ <{ L1 ; L2 }>, E › →ₗ
      map (fun c => match fst c with
                    | r_done     => (r_more L2, snd c)
                    | r_more L1' => (r_more <{ L1' ; L2 }>, snd c)
                    end) G
| local_step_if : forall b L1 L0 E,
    Σ ⊢ ‹ <{ if b then L1 else L0 }>, E › →ₗ
        {|| r_more L1, ensemble_filter (fun s => eval_bool (i_fn Σ) (i_rl Σ) s b) E ||}
      ⊎ {|| r_more L0, ensemble_filter (fun s => negb (eval_bool (i_fn Σ) (i_rl Σ) s b)) E ||}
where "Σ '⊢' '‹' L ',' E '›' '→ₗ' G" := (local_step Σ L E G).

(** ** Distributed step  ** **)
Inductive distri_step {dim} (Σ : interp dim)
    : program -> ensemble dim -> distri_config dim -> Prop :=
(* (Local) *)
| distri_local : forall (l1 : program) (L : lblock) (K : cblock) (S : process)
                        (l2 : program) (E : ensemble dim) (Gl : local_config dim),
    Σ ⊢ ‹ L, E › →ₗ Gl ->
    Σ ⊢ ‹ l1 ‖ (L ⨾ K ⨾ S) ‖ l2, E › ⇝
      map (fun c => (l1 ‖ advance (fst c) K S ‖ l2, snd c)) Gl
(* (Communicate) *)
| distri_comm : forall (D : program) (Ks : cblock) (S : process) (Ks' : cblock)
                       (Kr : cblock) (T : process) (Kr' : cblock) (rest : program)
                       (c : chan) (e : expr) (x : var) (E : ensemble dim),
    Permutation D (phase ↓ Ks S :: phase ↓ Kr T :: rest) ->
    Ks ∋ c_send c e □ Ks' ->
    Kr ∋ c_recv c x □ Kr' ->
    Σ ⊢ ‹ D, E › ⇝
      {|| advance ↓ Ks' S :: advance ↓ Kr' T :: rest,
        map (fun '(s,r) => (s [ x |-> eval_expr (i_fn Σ) s e ], r)) E ||}
where "Σ '⊢' '‹' D ',' E '›' '⇝' G" := (distri_step Σ D E G).


(** One step of a whole mixed configuration: pick ANY component, step it with
    [distri_step], splice the resulting components back in, renormalise. **)
Inductive mixed_step {dim} (Σ : interp dim)
    : distri_config dim -> distri_config dim -> Prop :=
| mixed_lift : forall (Ga : distri_config dim) (D : program) (E : ensemble dim)
                      (Gb : distri_config dim) (G1 : distri_config dim),
    Σ ⊢ ‹ D, E › ⇝ G1 ->
    mixed_step Σ (Ga ‖ (D, E) ‖ Gb) (norm (G1 ⊎ Ga ⊎ Gb)).

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
