(** * WellFormed — footprints of program phrases, and the well-formedness
      conditions of a LOCC distributed program.

      cvar(P)     classical variables occurring in P
      qvar(P)     quantum variables occurring in P
      change(P)   classical variables assigned (by :=, by measurement, or by
                  a communication input)
      read(P)     classical variables read by expressions or control guards
      channel(P)  channels occurring in P

      A row's footprint is its leaves' footprints collected left to right,
      i.e. [row_flat] of the leaf-level notion — so nothing below is written
      out twice for the D-, K- and program rows.
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

(** ** Footprints of a process ** **)
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

(** All communication actions of a process. **)
Fixpoint process_actions (p : process) : list caction :=
  match p with
  | terminated   => []
  | phase _ K p' => K ++ process_actions p'
  end.

(** ** Footprints of a program ** **)
Definition program_change  (P : program) : list var     := row_flat process_change  P.
Definition program_read    (P : program) : list var     := row_flat process_read    P.
Definition program_cvar    (P : program) : list var     := row_flat process_cvar    P.
Definition program_qvar    (P : program) : list qvar    := row_flat process_qvar    P.
Definition program_chan    (P : program) : list chan    := row_flat process_chan    P.
Definition program_actions (P : program) : list caction := row_flat process_actions P.

(** |parties_P(c)| — how many leaves mention channel c.  Stated for any row
    with a notion of "the channels of a leaf", since the proof system asks
    the same question of a communication phase (a K-row). **)
Fixpoint row_parties {A} (chans : A -> list chan) (r : row A) (c : chan) : nat :=
  match r with
  | leaf a    => if existsb (Nat.eqb c) (chans a) then 1 else 0
  | par r1 r2 => row_parties chans r1 c + row_parties chans r2 c
  end.

Definition parties (P : program) (c : chan) : nat :=
  row_parties process_chan P c.

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

(** Par-Disjoint-MP's side condition, on the D-row itself: the paper's
    DisjMP({Dᵢ}) with the Dᵢ read straight off the row's leaves. **)
Definition lrow_disj (d : lrow) : Prop := DisjMP (row_leaves d).

(** ** Well-formedness of a distributed program ********************** *)

(** Ownership: at every ∥ node the two subtrees own disjoint state. **)
Definition cross_disjoint (P1 P2 : program) : Prop :=
  disjoint (program_change P1) (program_cvar P2)
  /\ disjoint (program_change P2) (program_cvar P1)
  /\ disjoint (program_qvar P1) (program_qvar P2).

Fixpoint wf_ownership (P : program) : Prop :=
  match P with
  | leaf _    => True
  | par P1 P2 => wf_ownership P1 /\ wf_ownership P2 /\ cross_disjoint P1 P2
  end.

(** The k-th communication block of a process; processes with fewer phases
    are padded with ε_K, which is exactly the paper's padding convention. **)
Fixpoint comm_at (p : process) (k : nat) : cblock :=
  match p, k with
  | terminated,    _    => []
  | phase _ K _,   O    => K
  | phase _ _ p',  S k' => comm_at p' k'
  end.

(** The k-th communication PHASE of a program is a K-ROW: the k-th block of
    every leaf, padded.  Reading a program's phase is [row_map], not a
    predicate that has to be discharged. **)
Definition phase_row (P : program) (k : nat) : krow :=
  row_map (fun T => comm_at T k) P.

Definition phase_at (P : program) (k : nat) : list cblock :=
  row_leaves (phase_row P k).

(** Logical channels: every channel carries exactly one output and one
    input endpoint, in two distinct leaves. **)
Definition endpoints_of (P : program) (c : chan) : list caction :=
  filter (fun a => Nat.eqb (caction_chan a) c) (program_actions P).

Definition wf_channels (P : program) : Prop :=
  forall c, In c (program_chan P) ->
    length (filter is_send (endpoints_of P c)) = 1
    /\ length (filter (fun a => negb (is_send a)) (endpoints_of P c)) = 1
    /\ parties P c = 2.

(** Phase alignment: a channel's two endpoints occur in the SAME padded
    communication phase.  With [wf_channels] pinning the whole tree to two
    endpoint occurrences per channel, "this phase holds two of them" says
    exactly that both live here.  **)
Definition phase_actions (P : program) (k : nat) : list caction :=
  concat (phase_at P k).

Definition wf_phase_aligned (P : program) : Prop :=
  forall k c, In c (map caction_chan (phase_actions P k)) ->
    length (filter (fun a => Nat.eqb (caction_chan a) c) (phase_actions P k)) = 2.

(** Same-phase communication independence: within one padded phase the
    receive targets are pairwise distinct and none of them is read by an
    output in the same phase.  **)
Definition recv_targets (Ks : list cblock) : list var := flat_map cblock_change Ks.
Definition output_reads (Ks : list cblock) : list var := flat_map cblock_read Ks.

Definition wf_phase_independence (P : program) : Prop :=
  forall k,
    NoDup (recv_targets (phase_at P k))
    /\ disjoint (recv_targets (phase_at P k)) (output_reads (phase_at P k)).

(** Both phase footprints factor through [phase_actions]: flattening the
    blocks first and then reading each action is the same traversal. **)
Lemma flat_map_concat_flat : forall {A B} (f : A -> list B) (l : list (list A)),
    flat_map (fun x => flat_map f x) l = flat_map f (concat l).
Proof.
  induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite flat_map_app, IH; reflexivity.
Qed.

Lemma recv_targets_concat : forall Ks,
    recv_targets Ks = flat_map caction_change (concat Ks).
Proof. intro Ks. apply (flat_map_concat_flat caction_change Ks). Qed.

Lemma output_reads_concat : forall Ks,
    output_reads Ks = flat_map caction_read (concat Ks).
Proof. intro Ks. apply (flat_map_concat_flat caction_read Ks). Qed.

(** Channels are the channel names of the actions — [process_chan] and
    [program_chan] are [caction_chan] read off the actions. **)
Lemma process_chan_actions : forall p,
    process_chan p = map caction_chan (process_actions p).
Proof.
  induction p as [| R K p' IH]; simpl; [reflexivity |].
  rewrite map_app, IH; reflexivity.
Qed.

Lemma program_chan_actions : forall P,
    program_chan P = map caction_chan (program_actions P).
Proof.
  unfold program_chan, program_actions.
  induction P as [T | P1 IH1 P2 IH2]; simpl.
  - apply process_chan_actions.
  - rewrite map_app, IH1, IH2; reflexivity.
Qed.

(** A phase's blocks are its leaves' k-th blocks. **)
Lemma phase_at_leaves : forall P k,
    phase_at P k = map (fun T => comm_at T k) (row_leaves P).
Proof.
  intros P k. unfold phase_at, phase_row. apply row_leaves_map.
Qed.

(** "No endpoint on c" as a filter and as a membership. **)
Lemma filter_chan_nil_iff : forall c l,
    filter (fun a => Nat.eqb (caction_chan a) c) l = nil <-> ~ In c (map caction_chan l).
Proof.
  intros c l; induction l as [| a l IH]; simpl.
  - split; [intros _ [] | reflexivity].
  - destruct (Nat.eqb (caction_chan a) c) eqn:Hc.
    + apply Nat.eqb_eq in Hc. split; [discriminate |].
      intro H; exfalso; apply H; left; exact Hc.
    + apply Nat.eqb_neq in Hc. rewrite IH.
      split; intros H Hin; [| apply H].
      * destruct Hin as [Heq | Hin]; [exact (Hc Heq) | exact (H Hin)].
      * right; exact Hin.
Qed.

Lemma filter_chan_nonnil_in : forall (c : chan) (l : list caction),
    filter (fun a => Nat.eqb (caction_chan a) c) l <> [] ->
    In c (map caction_chan l).
Proof.
  intros c l H.
  destruct (filter (fun a => Nat.eqb (caction_chan a) c) l) as [| a rest] eqn:Ef;
    [exfalso; exact (H eq_refl) |].
  assert (Hain : In a (filter (fun a0 => Nat.eqb (caction_chan a0) c) l))
    by (rewrite Ef; left; reflexivity).
  apply filter_In in Hain as [HinL Hchan].
  apply Nat.eqb_eq in Hchan. rewrite <- Hchan. apply in_map, HinL.
Qed.

Lemma filter_length_split : forall {A} (f : A -> bool) (l : list A),
    length l = length (filter f l) + length (filter (fun x => negb (f x)) l).
Proof.
  induction l as [| a l IH]; simpl; [reflexivity |].
  destruct (f a); simpl; rewrite IH;
    [reflexivity | symmetry; apply Nat.add_succ_r].
Qed.

Lemma filter_filter_and : forall {A} (f g : A -> bool) (l : list A),
    filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [| a l IH]; simpl; [reflexivity |].
  destruct (g a); simpl; [destruct (f a) | ]; rewrite IH; reflexivity.
Qed.

Lemma existsb_eqb_true_iff : forall (c : chan) (l : list chan),
    existsb (Nat.eqb c) l = true <-> In c l.
Proof.
  intros c l; induction l as [| a l IH]; simpl.
  - split; [discriminate | intros []].
  - rewrite Bool.orb_true_iff, IH, Nat.eqb_eq.
    split; (intros [H | H]; [left | right]); auto.
Qed.

(** A leaf's party count only depends on whether it mentions c at all. **)
Lemma parties_leaf_eq : forall (T1 T2 : process) (c : chan),
    (In c (process_chan T1) <-> In c (process_chan T2)) ->
    parties (leaf T1) c = parties (leaf T2) c.
Proof.
  intros T1 T2 c Hiff. unfold parties; cbn [row_parties].
  match goal with
  | |- (if ?b1 then _ else _) = (if ?b2 then _ else _) =>
      destruct b1 eqn:E1; destruct b2 eqn:E2
  end; try reflexivity; exfalso.
  - apply (proj1 (existsb_eqb_true_iff c (process_chan T1))) in E1.
    apply Hiff in E1.
    apply (proj2 (existsb_eqb_true_iff c (process_chan T2))) in E1.
    rewrite E1 in E2; discriminate.
  - apply (proj1 (existsb_eqb_true_iff c (process_chan T2))) in E2.
    apply Hiff in E2.
    apply (proj2 (existsb_eqb_true_iff c (process_chan T1))) in E2.
    rewrite E2 in E1; discriminate.
Qed.

(** A well-formed LOCC distributed program (Definition 2.1). **)
Definition wf_program (P : program) : Prop :=
  wf_ownership P /\ wf_channels P /\ wf_phase_aligned P /\ wf_phase_independence P.

(** ** Theorem 2.1 — well-formedness implies disjoint local footprints ***

    The paper cuts one communication-free local block Dᵢ out of each process
    Sᵢ — the padded case being skip — and claims DisjMP({Dᵢ}).  An [lblock]
    holds no endpoints by construction, so only "occurring in Sᵢ" is left to
    state.  The chosen blocks form an lrow of the SAME SHAPE as the program,
    which is what [local_row] records. **)

(** D is the local block of one of p's phases. **)
Fixpoint block_in (D : lblock) (p : process) : Prop :=
  match p with
  | terminated   => False
  | phase R _ p' => R = r_more D \/ block_in D p'
  end.

(** What one leaf may contribute to the row: a block of its own, or skip. **)
Definition leaf_block (T : process) (D : lblock) : Prop :=
  D = l_skip \/ block_in D T.

(** [local_row P d]: d is one such block per leaf — the D-row of
    Par-Comp-MP, shaped like P. **)
Inductive local_row : program -> lrow -> Prop :=
| lrow_leaf : forall T D,
    leaf_block T D ->
    local_row (leaf T) (leaf D)
| lrow_par : forall P1 P2 d1 d2,
    local_row P1 d1 ->
    local_row P2 d2 ->
    local_row (par P1 P2) (par d1 d2).

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
  unfold program_change, program_cvar.
  induction P as [T | P1 IH1 P2 IH2]; simpl.
  - unfold process_cvar. apply incl_appl, incl_refl.
  - apply incl_app; [ apply incl_appl, IH1 | apply incl_appr, IH2 ].
Qed.

(** …and hence a whole row: every block in it is bounded by its program. **)
Lemma local_row_change : forall P d,
    local_row P d ->
    forall D, In D (row_leaves d) -> incl (lblock_change D) (program_change P).
Proof.
  induction 1 as [T D0 Hleaf | P1 P2 d1 d2 H1 IH1 H2 IH2]; intros D HIn.
  - destruct HIn as [Heq | []]; subst D0.
    destruct Hleaf as [Hskip | Hb].
    + subst D; apply incl_nil_l.
    + unfold program_change; simpl; apply block_in_change, Hb.
  - unfold program_change in *; simpl; apply in_app_or in HIn as [HIn | HIn].
    + apply incl_appl, IH1, HIn.
    + apply incl_appr, IH2, HIn.
Qed.

Lemma local_row_read : forall P d,
    local_row P d ->
    forall D, In D (row_leaves d) -> incl (lblock_read D) (program_cvar P).
Proof.
  induction 1 as [T D0 Hleaf | P1 P2 d1 d2 H1 IH1 H2 IH2]; intros D HIn.
  - destruct HIn as [Heq | []]; subst D0.
    destruct Hleaf as [Hskip | Hb].
    + subst D; apply incl_nil_l.
    + unfold program_cvar; simpl; unfold process_cvar.
      apply incl_appr, block_in_read, Hb.
  - unfold program_cvar in *; simpl; apply in_app_or in HIn as [HIn | HIn].
    + apply incl_appl, IH1, HIn.
    + apply incl_appr, IH2, HIn.
Qed.

Lemma local_row_qvar : forall P d,
    local_row P d ->
    forall D, In D (row_leaves d) -> incl (lblock_qvar D) (program_qvar P).
Proof.
  induction 1 as [T D0 Hleaf | P1 P2 d1 d2 H1 IH1 H2 IH2]; intros D HIn.
  - destruct HIn as [Heq | []]; subst D0.
    destruct Hleaf as [Hskip | Hb].
    + subst D; apply incl_nil_l.
    + unfold program_qvar; simpl; apply block_in_qvar, Hb.
  - unfold program_qvar in *; simpl; apply in_app_or in HIn as [HIn | HIn].
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
Lemma wf_ownership_disj_footprints : forall (P : program) (d : lrow),
    wf_ownership P -> local_row P d -> lrow_disj d.
Proof.
  intros P d Hown Hrow; revert Hown.
  induction Hrow as [T D0 Hleaf | P1 P2 d1 d2 H1 IH1 H2 IH2]; intros Hown.
  - repeat constructor.
  - destruct Hown as (Ho1 & Ho2 & Hc12 & Hc21 & Hq).
    unfold lrow_disj, DisjMP in *; simpl.
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

Theorem wf_disj_footprints : forall (P : program) (d : lrow),
    wf_program P -> local_row P d -> lrow_disj d.
Proof.
  intros P d (Hown & _ & _). apply wf_ownership_disj_footprints, Hown.
Qed.
