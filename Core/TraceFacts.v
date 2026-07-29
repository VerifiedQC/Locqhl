(** * TraceFacts — the bridge from the Löwner order to trace inequalities.

    [lowner] (Assertions.v) is an ORDER on operators: M ⊑ N iff N − M is
    positive semidefinite.  [degree] measures satisfaction by TRACES,
    tr(⟦A⟧ρ).  Soundness needs the standard bridge between the two:

        0 ⊑ A,  ρ a state   ⟹   0 ≤ tr(A ρ)          (psd_trace_nonneg)
        A ⊑ B,  ρ a state   ⟹   tr(A ρ) ≤ tr(B ρ)    (lowner_trace_mono)
** **)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lra Lia.
From QuantumLib Require Import Matrix Quantum RowColOps VecSet Eigenvectors.
From Locqhl.Core Require Import Syntax QuantumActions SemanticDomain Semantics Assertions.

Local Open Scope R_scope.

(** Real parts of complex sums/negations — bookkeeping for the derivation. **)
Lemma fst_Cplus : forall a b : C, fst (a + b)%C = (fst a + fst b)%R.
Proof. intros [x1 y1] [x2 y2]. reflexivity. Qed.

Lemma fst_Cn1_mult : forall z : C, fst ((- C1)%C * z)%C = (- fst z)%R.
Proof. intros [x y]. simpl. lra. Qed.

(** B1 — a PSD matrix has nonnegative real part on its diagonal:
    A i i IS the quadratic form on the i-th basis vector e_i. **)
Lemma psd_diag_entry : forall {n} (A : Square n) (i : nat),
    positive_semidefinite A -> (i < n)%nat -> 0 <= fst (A i i).
Proof.
  intros n A i HA Hi.
  rewrite (get_entry_with_e_i A i i Hi Hi).
  apply Rge_le, HA, WF_e_i.
Qed.

(** B2 — trace against a diagonal matrix collapses to the diagonal sum:
    tr(M·D) = Σᵢ Mᵢᵢ·Dᵢᵢ  (all cross terms vanish). **)
Lemma trace_mult_diag : forall {n} (M D : Square n),
    (forall i j, i <> j -> D i j = C0) ->
    trace (M × D)%M = big_sum (fun i => (M i i * D i i)%C) n.
Proof.
  intros n M D HD. unfold trace, Mmult.
  apply big_sum_eq_bounded; intros i Hi.
  apply big_sum_unique.
  exists i. split; [exact Hi | split; [reflexivity |]].
  intros j _ Hne. rewrite HD; [lca | auto].
Qed.

(** B3 — The state side must be a genuine
    density operator (WF + hermitian + PSD); the effect side needs only PSD
    (its anti-hermitian junk, if any, lands in the imaginary part, which the
    real-part pairing never sees).
    Proof: diagonalise the state, ρ = U·D·U† (Spectral_Theorem); D's diagonal
    is nonnegative-real; push A through the conjugation and collapse
    the trace with B2; every summand is (B1-nonneg)·(nonneg) ≥ 0. **)
Lemma psd_trace_nonneg : forall {n} (A ρ : Square n),
    positive_semidefinite A ->
    WF_Matrix ρ -> hermitian ρ -> positive_semidefinite ρ ->
    0 <= fst (trace (A × ρ)%M).
Proof.
  intros n A ρ HA HWF Hherm Hρ.
  assert (Hnorm : (ρ† × ρ)%M = (ρ × ρ†)%M) by (rewrite Hherm; reflexivity).
  destruct (@Spectral_Theorem n ρ HWF Hnorm) as [U [HU HD]].
  set (D := (U† × ρ × U)%M) in *.
  pose proof (proj1 HU) as HUwf.
  assert (HDherm : hermitian D).
  { unfold D.
    replace (U† × ρ × U)%M with (U† × ρ × (U†)†)%M
      by (rewrite adjoint_involutive; reflexivity).
    apply unit_conj_hermitian; auto using adjoint_unitary. }
  assert (HDpsd : positive_semidefinite D).
  { unfold D. apply positive_semidefinite_unitary_conj; auto. }
  destruct (pos_semi_def_diag_implies_nonneg D HD HDherm HDpsd) as [HDwf HDnn].
  assert (HUflip : (U × U†)%M = I n)
    by (apply Minv_flip; auto with wf_db; apply (proj2 HU)).
  assert (Hρeq : ρ = (U × D × U†)%M).
  { unfold D. rewrite <- !Mmult_assoc. rewrite HUflip.
    rewrite Mmult_1_l; auto. rewrite Mmult_assoc, HUflip.
    rewrite Mmult_1_r; auto. }
  rewrite Hρeq.
  replace (A × (U × D × U†))%M with ((A × U × D) × U†)%M
    by (rewrite !Mmult_assoc; reflexivity).
  rewrite trace_mmult_comm.
  replace (U† × (A × U × D))%M with ((U† × A × U) × D)%M
    by (rewrite !Mmult_assoc; reflexivity).
  rewrite (trace_mult_diag _ D (proj2 HD)).
  apply big_sum_ge_0. intro i.
  destruct (HDnn i i) as [HRe HIm]. unfold Re, Im in HRe, HIm.
  bdestruct (i <? n)%nat.
  - assert (HAii : 0 <= fst ((U† × A × U)%M i i)).
    { apply psd_diag_entry; auto.
      apply positive_semidefinite_unitary_conj; auto. }
    unfold Cmult; simpl.
    rewrite HIm, Rmult_0_r, Rminus_0_r.
    apply Rmult_le_pos; [exact HAii | lra].
  - rewrite (HDwf i i); [| left; lia].
    rewrite Cmult_0_r. simpl. lra.
Qed.

(** B4 — the bridge soundness actually uses, hypotheses matching B3:
    tr((B − A) ρ) ≥ 0  and  tr((B − A) ρ) = tr(Bρ) − tr(Aρ). **)
Lemma lowner_trace_mono : forall {n} (A B ρ : Square n),
    A ⊑ B ->
    WF_Matrix ρ -> hermitian ρ -> positive_semidefinite ρ ->
    fst (trace (A × ρ)%M) <= fst (trace (B × ρ)%M).
Proof.
  intros n A B ρ Hle HWF Hherm Hρ. unfold lowner in Hle.
  pose proof (psd_trace_nonneg _ _ Hle HWF Hherm Hρ) as H0.
  rewrite Mmult_plus_distr_r, Mscale_mult_dist_l in H0.
  rewrite trace_plus_dist, trace_mult_dist in H0.
  rewrite fst_Cplus, fst_Cn1_mult in H0. lra.
Qed.

(** ** Degree facts *****************************************************

    Lifting B3/B4 through [degree]'s two guards (classical formula holds?
    quantum predicate defined?).  When both guards pass, the trace facts
    apply directly; when a guard fails, degree is 0 and comparing against
    the other side needs its nonnegativity — which is where [wf_assertion]
    (denotations are effects) comes in, on the POST side only.
*********************************************************************)

(** Both guards pass or degree is 0; in the live branch tr(effect·state) ≥ 0. **)
Lemma degree_nonneg : forall {dim} (Σ : interp dim) (Q : assertion dim) s (r : qstate dim),
    wf_assertion Σ Q ->
    @WF_Matrix (2 ^ dim) (2 ^ dim) r ->
    @hermitian (2 ^ dim) r ->
    @positive_semidefinite (2 ^ dim) r ->
    0 <= degree Σ Q (s, r).
Proof.
  intros dim Σ Q s r Hwf HWFr Hherm Hpsd. unfold degree.
  destruct (formula_holds Σ s (classical_part Q)); [| lra].
  destruct (qpred_denote Σ s (quantum_part Q)) as [M|] eqn:HM; [| lra].
  apply psd_trace_nonneg; auto.
  apply (proj1 (Hwf s M HM)).
Qed.

(** PRE side of Conseq: Q1 holds and is defined at s, so both live branches
    are taken and entailment's Löwner clause feeds B4 directly. **)
Lemma degree_entails_defined :
  forall {dim} (Σ : interp dim) (Q1 Q2 : assertion dim) s (r : qstate dim),
    Q1 ⊨[Σ] Q2 ->
    formula_holds Σ s (classical_part Q1) = true ->
    defined_in Σ Q1 s ->
    @WF_Matrix (2 ^ dim) (2 ^ dim) r ->
    @hermitian (2 ^ dim) r ->
    @positive_semidefinite (2 ^ dim) r ->
    degree Σ Q1 (s, r) <= degree Σ Q2 (s, r).
Proof.
  intros dim Σ Q1 Q2 s r (Hcl & Hdef & Hlow) Hh1 Hd1 HWFr Hherm Hpsd.
  destruct (Hdef s Hh1 Hd1) as [N HN].
  destruct Hd1 as [M HM].
  unfold degree. rewrite Hh1, (Hcl s Hh1), HM, HN.
  apply lowner_trace_mono; auto. eapply Hlow; eauto.
Qed.

(** POST side of Conseq: the state is an arbitrary ensemble member, so Q1's
    guards may fail (degree 0) — then Q2's degree must be ≥ 0, forcing
    [wf_assertion Σ Q2]. **)
Lemma degree_entails_wf :
  forall {dim} (Σ : interp dim) (Q1 Q2 : assertion dim) s (r : qstate dim),
    Q1 ⊨[Σ] Q2 -> wf_assertion Σ Q2 ->
    @WF_Matrix (2 ^ dim) (2 ^ dim) r ->
    @hermitian (2 ^ dim) r ->
    @positive_semidefinite (2 ^ dim) r ->
    degree Σ Q1 (s, r) <= degree Σ Q2 (s, r).
Proof.
  intros dim Σ Q1 Q2 s r Hent Hwf HWFr Hherm Hpsd.
  destruct (formula_holds Σ s (classical_part Q1)) eqn:Hh1.
  - destruct (qpred_denote Σ s (quantum_part Q1)) as [M|] eqn:HM.
    + apply degree_entails_defined; auto. exists M; auto.
    + replace (degree Σ Q1 (s, r)) with 0;
        [ apply degree_nonneg; auto
        | unfold degree; rewrite Hh1, HM; reflexivity ].
  - replace (degree Σ Q1 (s, r)) with 0;
      [ apply degree_nonneg; auto
      | unfold degree; rewrite Hh1; reflexivity ].
Qed.

(** ** Closure of state legitimacy under the language's quantum actions ***

    Every quantum action of the semantics is (a sum of) conjugation maps
    ρ ↦ K·ρ·K†  ([super] K).  All three components of "genuine state" are
    closed under them — for ANY K (unitarity is not needed for closure;
    only well-formedness of K, for the WF component).
*********************************************************************)

Lemma super_WF : forall {n} (K ρ : Square n),
    WF_Matrix K -> WF_Matrix ρ -> WF_Matrix (super K ρ).
Proof. intros. unfold super. auto with wf_db. Qed.

Lemma super_hermitian : forall {n} (K ρ : Square n),
    hermitian ρ -> hermitian (super K ρ).
Proof.
  intros n K ρ Hρ. unfold super, hermitian.
  rewrite !Mmult_adjoint, adjoint_involutive, Hρ, Mmult_assoc.
  reflexivity.
Qed.

Lemma super_psd : forall {n} (K ρ : Square n),
    WF_Matrix K -> positive_semidefinite ρ -> positive_semidefinite (super K ρ).
Proof.
  intros n K ρ HK Hρ. unfold positive_semidefinite, super in *.
  intros z Hz.
  replace ((z† × (K × ρ × K†) × z))%M with (((K† × z)† × ρ × (K† × z)))%M
    by (rewrite Mmult_adjoint, adjoint_involutive, !Mmult_assoc; reflexivity).
  apply Hρ. auto with wf_db.
Qed.

Lemma hermitian_plus : forall {n} (A B : Square n),
    hermitian A -> hermitian B -> hermitian (A .+ B)%M.
Proof.
  intros n A B HA HB. unfold hermitian.
  rewrite Mplus_adjoint, HA, HB. reflexivity.
Qed.

Lemma psd_plus : forall {n} (A B : Square n),
    positive_semidefinite A -> positive_semidefinite B ->
    positive_semidefinite (A .+ B)%M.
Proof.
  intros n A B HA HB. unfold positive_semidefinite in *.
  intros z Hz.
  replace ((z† × (A .+ B) × z))%M with ((z† × A × z .+ z† × B × z))%M
    by (rewrite Mmult_plus_distr_l, Mmult_plus_distr_r; reflexivity).
  specialize (HA z Hz). specialize (HB z Hz).
  unfold Mplus. rewrite fst_Cplus. lra.
Qed.

(** Sum the POST-side pointwise bound over an ensemble of genuine states. **)
Lemma total_degree_entails :
  forall {dim} (Σ : interp dim) (Q1 Q2 : assertion dim) (E : ensemble dim),
    Q1 ⊨[Σ] Q2 -> wf_assertion Σ Q2 ->
    Forall (fun st : cqstate dim =>
              @WF_Matrix (2 ^ dim) (2 ^ dim) (snd st) /\
              @hermitian (2 ^ dim) (snd st) /\
              @positive_semidefinite (2 ^ dim) (snd st)) E ->
    total_degree Σ Q1 E <= total_degree Σ Q2 E.
Proof.
  intros dim Σ Q1 Q2 E Hent Hwf HF.
  induction HF as [| st E Hst HF IH]; unfold total_degree in *; simpl.
  - lra.
  - apply Rplus_le_compat; [| exact IH].
    destruct st as [s r]. destruct Hst as (H1 & H2 & H3).
    apply degree_entails_wf; auto.
Qed.

(** ** Substitution lemmas (paper Appendix A.2) *************************

    Substituting t for x and then evaluating at σ equals evaluating at
    σ[x ↦ ⟦t⟧σ] — for expressions, boolean conditions, formulas, quantum
    predicates, and finally [degree].
*********************************************************************)

Fixpoint eval_expr_subst (fn : funsym -> list val -> val)
    (s : store) (x : var) (t : expr) (e : expr) {struct e} :
    eval_expr fn s (expr_subst e x t)
    = eval_expr fn (s [ x |-> eval_expr fn s t ]) e.
Proof.
  destruct e as [v | y | f es]; simpl.
  - reflexivity.
  - unfold store_update. destruct (Nat.eqb x y); reflexivity.
  - f_equal. induction es as [| e0 es' IHes]; simpl; [reflexivity |].
    f_equal; [apply eval_expr_subst | exact IHes].
Qed.

Lemma eval_bool_subst : forall (fn : funsym -> list val -> val)
    (rl : relsym -> list val -> bool) (s : store) (x : var) (t : expr)
    (b : bexpr),
    eval_bool fn rl s (bexpr_subst b x t)
    = eval_bool fn rl (s [ x |-> eval_expr fn s t ]) b.
Proof.
  intros fn rl s x t b; induction b; simpl;
    try reflexivity;
    try (now rewrite IHb);
    try (now rewrite IHb1, IHb2).
  f_equal. rewrite map_map. apply map_ext. intro e0. apply eval_expr_subst.
Qed.

Lemma formula_holds_subst :
  forall {dim} (Σ : interp dim) (s : store) (x : var) (t : expr) (p : formula),
    formula_holds Σ s (formula_subst p x t)
    = formula_holds Σ (s [ x |-> eval_expr (i_fn Σ) s t ]) p.
Proof.
  intros dim Σ s x t p; induction p; simpl;
    try (now rewrite IHp);
    try (now rewrite IHp1, IHp2).
  - apply eval_bool_subst.
  - now rewrite !eval_expr_subst.
Qed.

Lemma qpred_denote_subst :
  forall {dim} (Σ : interp dim) (s : store) (x : var) (t : expr) (A : qpred dim),
    qpred_denote Σ s (qpred_subst A x t)
    = qpred_denote Σ (s [ x |-> eval_expr (i_fn Σ) s t ]) A.
Proof.
  intros dim Σ s x t A;
    induction A as [f args | g args A' IH | A1 IH1 A2 IH2]; simpl.
  - f_equal. rewrite map_map. apply map_ext. intro e0. apply eval_expr_subst.
  - rewrite IH.
    assert (HK : map (eval_expr (i_fn Σ) s) (map (fun e => expr_subst e x t) args)
               = map (eval_expr (i_fn Σ) (s [ x |-> eval_expr (i_fn Σ) s t ])) args).
    { rewrite map_map. apply map_ext. intro e0. apply eval_expr_subst. }
    rewrite HK. reflexivity.
  - now rewrite IH1, IH2.
Qed.

Lemma degree_subst :
  forall {dim} (Σ : interp dim) (Q : assertion dim) (x : var) (t : expr)
         (s : store) (r : qstate dim),
    degree Σ (assertion_subst Q x t) (s, r)
    = degree Σ Q (s [ x |-> eval_expr (i_fn Σ) s t ], r).
Proof.
  intros. unfold degree, assertion_subst; simpl.
  rewrite formula_holds_subst, qpred_denote_subst. reflexivity.
Qed.
