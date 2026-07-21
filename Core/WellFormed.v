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

Definition program_change (P : program) : list var := flat_map process_change P.
Definition program_read   (P : program) : list var := flat_map process_read P.
Definition program_cvar   (P : program) : list var := flat_map process_cvar P.
Definition program_qvar   (P : program) : list qvar := flat_map process_qvar P.
Definition program_chan   (P : program) : list chan := flat_map process_chan P.

(** parties_P(c) — the indices of the processes mentioning channel c. **)
Definition parties (P : program) (c : chan) : list nat :=
  filter (fun i => existsb (Nat.eqb c)
                     (process_chan (nth i P terminated)))
         (seq 0 (length P)).

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

(** Ownership: no process writes another's classical state, and quantum
    registers are privately owned. **)
(** Two processes own disjoint state: neither writes anything the other
    touches, and their quantum registers are disjoint.  Symmetric, so
    ordered pairs suffice. **)
Definition owns_disjointly (p q : process) : Prop :=
  disjoint (process_change p) (process_cvar q)
  /\ disjoint (process_change q) (process_cvar p)
  /\ disjoint (process_qvar p) (process_qvar q).

Definition wf_ownership (P : program) : Prop :=
  ForallOrdPairs owns_disjointly P.

(** The k-th communication block of a process; processes with fewer phases
    are padded with ε_K, which is exactly the paper's padding convention. **)
Fixpoint comm_at (p : process) (k : nat) : cblock :=
  match p, k with
  | terminated,    _    => []
  | phase _ K _,   O    => K
  | phase _ _ p',  S k' => comm_at p' k'
  end.

(** The k-th communication PHASE of a program: K_1 ‖ … ‖ K_N, padded. **)
Definition phase_at (P : program) (k : nat) : list cblock :=
  map (fun p => comm_at p k) P.

(** Logical channels: every channel carries exactly one output and one
    input endpoint, and they sit in two distinct processes. **)
Definition endpoints_of (P : program) (c : chan) : list caction :=
  filter (fun a => Nat.eqb (caction_chan a) c)
         (flat_map (fun p =>
            (fix all (q : process) : list caction :=
               match q with
               | terminated    => []
               | phase _ K q'  => K ++ all q'
               end) p) P).

Definition wf_channels (P : program) : Prop :=
  forall c, In c (program_chan P) ->
    length (filter is_send (endpoints_of P c)) = 1
    /\ length (filter (fun a => negb (is_send a)) (endpoints_of P c)) = 1
    /\ length (parties P c) = 2.

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
