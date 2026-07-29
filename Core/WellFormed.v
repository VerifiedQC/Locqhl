(** * WellFormed — footprints of program phrases, and the well-formedness
      conditions of a LOCC distributed program.

      cvar(P)     classical variables occurring in P
      qvar(P)     quantum variables occurring in P
      change(P)   classical variables assigned (by :=, by measurement, or by
                  a communication input)
      read(P)     classical variables read by expressions or control guards
      channel(P)  channels occurring in P
** **)
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Locqhl.Core Require Import Syntax Names.
Import ListNotations.

(** ** Footprints of a local block ** **)
Fixpoint lblock_change (L : lblock) : list var :=
  match L with
  | l_skip           => []
  | l_assign x _     => [x]
  | l_init _         => []
  | l_ugate _ _      => []
  | l_meas x _ _     => [x]
  | l_seq L1 L2      => lblock_change L1 ++ lblock_change L2
  | l_if _ L1 L0     => lblock_change L1 ++ lblock_change L0
  end.

Fixpoint lblock_read (L : lblock) : list var :=
  match L with
  | l_skip           => []
  | l_assign _ e     => expr_vars e
  | l_init _         => []
  | l_ugate _ _      => []
  | l_meas _ _ _     => []
  | l_seq L1 L2      => lblock_read L1 ++ lblock_read L2
  | l_if b L1 L0     => bexpr_vars b ++ lblock_read L1 ++ lblock_read L0
  end.

Fixpoint lblock_qvar (L : lblock) : list qvar :=
  match L with
  | l_skip           => []
  | l_assign _ _     => []
  | l_init q         => [q]
  | l_ugate _ qs     => qs
  | l_meas _ _ qs    => qs
  | l_seq L1 L2      => lblock_qvar L1 ++ lblock_qvar L2
  | l_if _ L1 L0     => lblock_qvar L1 ++ lblock_qvar L0
  end.

(** ** Footprints of communication actions and blocks ** **)
Definition caction_change (a : caction) : list var :=
  match a with c_send _ _ => []      | c_recv _ x => [x] end.
Definition caction_read (a : caction) : list var :=
  match a with c_send _ e => expr_vars e | c_recv _ _ => [] end.
Definition caction_chan (a : caction) : chan :=
  match a with c_send c _ => c       | c_recv c _ => c end.

Definition is_send (a : caction) : bool :=
  match a with c_send _ _ => true | c_recv _ _ => false end.

Definition cblock_change (K : cblock) : list var := flat_map caction_change K.
Definition cblock_read   (K : cblock) : list var := flat_map caction_read K.
Definition cblock_chan   (K : cblock) : list chan := map caction_chan K.

(** ** Footprints of a process and of a program ** **)
Definition residual_change (R : residual) : list var :=
  match R with r_done => [] | r_more L => lblock_change L end.
Definition residual_read (R : residual) : list var :=
  match R with r_done => [] | r_more L => lblock_read L end.
Definition residual_qvar (R : residual) : list qvar :=
  match R with r_done => [] | r_more L => lblock_qvar L end.

Fixpoint process_change (p : process) : list var :=
  match p with
  | terminated     => []
  | phase R K p'   => residual_change R ++ cblock_change K ++ process_change p'
  end.

Fixpoint process_read (p : process) : list var :=
  match p with
  | terminated     => []
  | phase R K p'   => residual_read R ++ cblock_read K ++ process_read p'
  end.

Fixpoint process_qvar (p : process) : list qvar :=
  match p with
  | terminated     => []
  | phase R _ p'   => residual_qvar R ++ process_qvar p'
  end.

Fixpoint process_chan (p : process) : list chan :=
  match p with
  | terminated     => []
  | phase _ K p'   => cblock_chan K ++ process_chan p'
  end.

(** cvar = every classical variable occurring, read or written. **)
Definition process_cvar (p : process) : list var :=
  process_change p ++ process_read p.

(** ** Footprints of a component, through its reading. ** **)
Definition comp_change (C : component) : list var  := process_change (read_component C).
Definition comp_cvar   (C : component) : list var  := process_cvar   (read_component C).
Definition comp_qvar   (C : component) : list qvar := process_qvar   (read_component C).
Definition comp_chan   (C : component) : list chan := process_chan   (read_component C).

(** ** Footprints of a program ** **)
Fixpoint program_change (P : program) : list var :=
  match P with
  | pg_comp C    => comp_change C
  | pg_par P1 P2 => program_change P1 ++ program_change P2
  end.
Fixpoint program_cvar (P : program) : list var :=
  match P with
  | pg_comp C    => comp_cvar C
  | pg_par P1 P2 => program_cvar P1 ++ program_cvar P2
  end.
Fixpoint program_qvar (P : program) : list qvar :=
  match P with
  | pg_comp C    => comp_qvar C
  | pg_par P1 P2 => program_qvar P1 ++ program_qvar P2
  end.
Fixpoint program_chan (P : program) : list chan :=
  match P with
  | pg_comp C    => comp_chan C
  | pg_par P1 P2 => program_chan P1 ++ program_chan P2
  end.

(** |parties_P(c)| — how many leaves mention channel c. **)
Fixpoint parties (P : program) (c : chan) : nat :=
  match P with
  | pg_comp C    => if existsb (Nat.eqb c) (comp_chan C) then 1 else 0
  | pg_par P1 P2 => parties P1 c + parties P2 c
  end.

(** ** DisjMP — disjoint footprints of communication-free local blocks **)
(** The pairwise non-interference condition on two local blocks. It is
    stated symmetrically, so quantifying over ORDERED pairs already covers
    every unordered pair. **)
Definition non_interfering (Di Dj : lblock) : Prop :=
  disjoint (lblock_change Di) (lblock_change Dj)
  /\ disjoint (lblock_change Di) (lblock_read Dj)
  /\ disjoint (lblock_change Dj) (lblock_read Di)
  /\ disjoint (lblock_qvar Di) (lblock_qvar Dj).

Definition DisjMP (Ds : list lblock) : Prop :=
  ForallOrdPairs non_interfering Ds.

(** ** Well-formedness of a distributed program ********************** *)

(** Ownership: at every ∥ node the two subtrees own disjoint state. **)
Definition cross_disjoint (P1 P2 : program) : Prop :=
  disjoint (program_change P1) (program_cvar P2)
  /\ disjoint (program_change P2) (program_cvar P1)
  /\ disjoint (program_qvar P1) (program_qvar P2).

Fixpoint wf_ownership (P : program) : Prop :=
  match P with
  | pg_comp _    => True
  | pg_par P1 P2 => wf_ownership P1 /\ wf_ownership P2 /\ cross_disjoint P1 P2
  end.

(** The k-th communication block of a process; processes with fewer phases
    are padded with ε_K, which is exactly the paper's padding convention. **)
Fixpoint comm_at (p : process) (k : nat) : cblock :=
  match p, k with
  | terminated,    _    => []
  | phase _ K _,   O    => K
  | phase _ _ p',  S k' => comm_at p' k'
  end.

(** The k-th communication PHASE of a program: the k-th block of every
    leaf, padded. **)
Fixpoint phase_at (P : program) (k : nat) : list cblock :=
  match P with
  | pg_comp C    => [comm_at (read_component C) k]
  | pg_par P1 P2 => phase_at P1 k ++ phase_at P2 k
  end.

(** All communication actions of a process / of a program. **)
Fixpoint process_actions (p : process) : list caction :=
  match p with
  | terminated   => []
  | phase _ K p' => K ++ process_actions p'
  end.

Fixpoint program_actions (P : program) : list caction :=
  match P with
  | pg_comp C    => process_actions (read_component C)
  | pg_par P1 P2 => program_actions P1 ++ program_actions P2
  end.

(** Logical channels: every channel carries exactly one output and one
    input endpoint, in two distinct leaves. **)
Definition endpoints_of (P : program) (c : chan) : list caction :=
  filter (fun a => Nat.eqb (caction_chan a) c) (program_actions P).

Definition wf_channels (P : program) : Prop :=
  forall c, In c (program_chan P) ->
    length (filter is_send (endpoints_of P c)) = 1
    /\ length (filter (fun a => negb (is_send a)) (endpoints_of P c)) = 1
    /\ parties P c = 2.

(** Same-phase communication independence: within one padded phase the
    receive targets are pairwise distinct and none of them is read by an
    output in the same phase.  **)
Definition recv_targets (Ks : list cblock) : list var := flat_map cblock_change Ks.
Definition output_reads (Ks : list cblock) : list var := flat_map cblock_read Ks.

Definition wf_phase_independence (P : program) : Prop :=
  forall k,
    NoDup (recv_targets (phase_at P k))
    /\ disjoint (recv_targets (phase_at P k)) (output_reads (phase_at P k)).

(** A well-formed LOCC distributed program. **)
Definition wf_program (P : program) : Prop :=
  wf_ownership P /\ wf_channels P /\ wf_phase_independence P.

(** ** Theorem 2.1 — well-formedness implies disjoint local footprints ***

    The paper cuts one communication-free local block Dᵢ out of each process
    Sᵢ — the padded case being skip — and claims DisjMP({Dᵢ}).  An [lblock]
    holds no endpoints by construction, so only "occurring in Sᵢ" is left to
    state. **)

(** D is the local block of one of p's phases. **)
Fixpoint block_in (D : lblock) (p : process) : Prop :=
  match p with
  | terminated   => False
  | phase R _ p' => R = r_more D \/ block_in D p'
  end.

(** What one leaf may contribute to the row: a block of its own, or skip. **)
Definition leaf_block (C : component) (D : lblock) : Prop :=
  D = l_skip \/ block_in D (read_component C).

(** [local_row P Ds]: Ds is one such block per leaf, left to right — the
    D-row of Par-Comp-MP.  A leaf [⟨ₗ D ⟩] reads as [phase (r_more D) ε ↓],
    so a whole D-row program is an instance. **)
Inductive local_row : program -> list lblock -> Prop :=
| lrow_leaf : forall C D,
    leaf_block C D ->
    local_row (pg_comp C) [D]
| lrow_par : forall P1 P2 Ds1 Ds2,
    local_row P1 Ds1 ->
    local_row P2 Ds2 ->
    local_row (pg_par P1 P2) (Ds1 ++ Ds2).

(** Footprint monotonicity: a phase's block touches only what its process
    touches. **)
Lemma block_in_change : forall D p,
    block_in D p -> incl (lblock_change D) (process_change p).
Proof.
  intros D p; induction p as [| R K p' IH]; simpl.
  - intros [].
  - intros [Heq | Hin].
    + subst R; simpl; apply incl_appl, incl_refl.
    + eapply incl_tran; [ apply IH, Hin | apply incl_appr, incl_appr, incl_refl ].
Qed.

Lemma block_in_read : forall D p,
    block_in D p -> incl (lblock_read D) (process_read p).
Proof.
  intros D p; induction p as [| R K p' IH]; simpl.
  - intros [].
  - intros [Heq | Hin].
    + subst R; simpl; apply incl_appl, incl_refl.
    + eapply incl_tran; [ apply IH, Hin | apply incl_appr, incl_appr, incl_refl ].
Qed.

Lemma block_in_qvar : forall D p,
    block_in D p -> incl (lblock_qvar D) (process_qvar p).
Proof.
  intros D p; induction p as [| R K p' IH]; simpl.
  - intros [].
  - intros [Heq | Hin].
    + subst R; simpl; apply incl_appl, incl_refl.
    + eapply incl_tran; [ apply IH, Hin | apply incl_appr, incl_refl ].
Qed.

Lemma program_change_cvar : forall P, incl (program_change P) (program_cvar P).
Proof.
  induction P as [C | P1 IH1 P2 IH2]; simpl.
  - unfold comp_change, comp_cvar, process_cvar. apply incl_appl, incl_refl.
  - apply incl_app; [ apply incl_appl, IH1 | apply incl_appr, IH2 ].
Qed.

(** …and hence a whole row: every block in it is bounded by its program. **)
Lemma local_row_change : forall P Ds,
    local_row P Ds -> forall D, In D Ds -> incl (lblock_change D) (program_change P).
Proof.
  induction 1 as [C D0 Hleaf | P1 P2 Ds1 Ds2 H1 IH1 H2 IH2]; intros D HIn.
  - destruct HIn as [Heq | []]; subst D0.
    destruct Hleaf as [Hskip | Hb].
    + subst D; apply incl_nil_l.
    + unfold program_change, comp_change; apply block_in_change, Hb.
  - simpl; apply in_app_or in HIn as [HIn | HIn].
    + apply incl_appl, IH1, HIn.
    + apply incl_appr, IH2, HIn.
Qed.

Lemma local_row_read : forall P Ds,
    local_row P Ds -> forall D, In D Ds -> incl (lblock_read D) (program_cvar P).
Proof.
  induction 1 as [C D0 Hleaf | P1 P2 Ds1 Ds2 H1 IH1 H2 IH2]; intros D HIn.
  - destruct HIn as [Heq | []]; subst D0.
    destruct Hleaf as [Hskip | Hb].
    + subst D; apply incl_nil_l.
    + unfold program_cvar, comp_cvar, process_cvar.
      apply incl_appr, block_in_read, Hb.
  - simpl; apply in_app_or in HIn as [HIn | HIn].
    + apply incl_appl, IH1, HIn.
    + apply incl_appr, IH2, HIn.
Qed.

Lemma local_row_qvar : forall P Ds,
    local_row P Ds -> forall D, In D Ds -> incl (lblock_qvar D) (program_qvar P).
Proof.
  induction 1 as [C D0 Hleaf | P1 P2 Ds1 Ds2 H1 IH1 H2 IH2]; intros D HIn.
  - destruct HIn as [Heq | []]; subst D0.
    destruct Hleaf as [Hskip | Hb].
    + subst D; apply incl_nil_l.
    + unfold program_qvar, comp_qvar; apply block_in_qvar, Hb.
  - simpl; apply in_app_or in HIn as [HIn | HIn].
    + apply incl_appl, IH1, HIn.
    + apply incl_appr, IH2, HIn.
Qed.

(** Two list-level steps: [disjoint] is inherited by sublists, and pairing up
    an append needs the within-halves and across-halves facts. **)
Lemma disjoint_incl : forall a b A B,
    disjoint A B -> incl a A -> incl b B -> disjoint a b.
Proof. intros a b A B H Ha Hb x Hx Hy. exact (H x (Ha x Hx) (Hb x Hy)). Qed.

Lemma ForallOrdPairs_app : forall {A} (R : A -> A -> Prop) l1 l2,
    ForallOrdPairs R l1 -> ForallOrdPairs R l2 ->
    (forall x y, In x l1 -> In y l2 -> R x y) ->
    ForallOrdPairs R (l1 ++ l2).
Proof.
  intros A R l1; induction l1 as [| a l1 IH]; intros l2 H1 H2 Hcross; simpl.
  - assumption.
  - inversion H1 as [| ? ? Hhd Htl]; subst; constructor.
    + apply Forall_app; split; [ assumption |].
      apply Forall_forall; intros y Hy; apply Hcross; [ left; reflexivity | assumption ].
    + apply IH; [ assumption | assumption |].
      intros x y Hx Hy; apply Hcross; [ right; assumption | assumption ].
Qed.

(** Theorem 2.1.  The induction runs on ownership alone: [wf_channels] is
    NOT inherited by a subtree (a channel's two endpoints straddle the ∥),
    so it cannot appear in the induction hypothesis. **)
Lemma wf_ownership_disj_footprints : forall (P : program) (Ds : list lblock),
    wf_ownership P -> local_row P Ds -> DisjMP Ds.
Proof.
  intros P Ds Hown Hrow; revert Hown.
  induction Hrow as [C D0 Hleaf | P1 P2 Ds1 Ds2 H1 IH1 H2 IH2]; intros Hown.
  - repeat constructor.
  - destruct Hown as (Ho1 & Ho2 & Hc12 & Hc21 & Hq).
    apply ForallOrdPairs_app; [ apply IH1, Ho1 | apply IH2, Ho2 |].
    intros Di Dj HDi HDj; repeat split.
    + eapply disjoint_incl;
        [ exact Hc12
        | eapply local_row_change; eassumption
        | eapply incl_tran;
            [ eapply local_row_change; eassumption | apply program_change_cvar ] ].
    + eapply disjoint_incl;
        [ exact Hc12
        | eapply local_row_change; eassumption
        | eapply local_row_read; eassumption ].
    + eapply disjoint_incl;
        [ exact Hc21
        | eapply local_row_change; eassumption
        | eapply local_row_read; eassumption ].
    + eapply disjoint_incl;
        [ exact Hq
        | eapply local_row_qvar; eassumption
        | eapply local_row_qvar; eassumption ].
Qed.

Theorem wf_disj_footprints : forall (P : program) (Ds : list lblock),
    wf_program P -> local_row P Ds -> DisjMP Ds.
Proof.
  intros P Ds (Hown & _ & _). apply wf_ownership_disj_footprints, Hown.
Qed.
