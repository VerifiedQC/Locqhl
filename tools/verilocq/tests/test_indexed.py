"""Independent small dense semantics and adversarial indexed-proof checks."""

from dataclasses import replace
import unittest

import sympy as sp

from verilocq import Unsupported
from verilocq.indexed import (Equality, IndexedEvidence, IndexedFamily, Kernel,
                               Positive, add, effect_induction, finite_sum,
                               first_acceptance, framed_attempt, identity, local,
                               pullback, recurrence, substitute, tensor,
                               tensor_product, zero)
from verilocq.quantum import clean


def dense(term, kernel, values):
    """A separate finite interpretation; never used by the proof checker."""
    a = term.args
    number = lambda expression: int(expression.subs(values, simultaneous=True))
    lo,hi = map(number,term.space)
    dimension = kernel.dimension**(hi-lo)
    if term.kind == "I":
        return sp.eye(dimension)
    if term.kind == "0":
        return sp.zeros(dimension)
    if term.kind == "local":
        return kernel.matrices[a[0]]
    if term.kind == "call":
        return dense(a[0].unfold(a[1],a[2]),kernel,values)
    if term.kind in ("add","sub"):
        return dense(a[0],kernel,values) + (1 if term.kind == "add" else -1)*dense(a[1],kernel,values)
    if term.kind == "tensor":
        result = sp.ones(1)
        for part in a:
            result = sp.kronecker_product(result,dense(part,kernel,values))
        return result
    if term.kind == "product":
        result = sp.ones(1)
        for _ in range(number(a[1]),number(a[2])):
            result = sp.kronecker_product(result,kernel.matrices[a[0]])
        return result
    if term.kind == "sum":
        binder,start,end,body = a
        result = sp.zeros(dimension)
        for i in range(number(start),number(end)):
            result += dense(body,kernel,{**values,binder:i})
        return result
    if term.kind == "pullback":
        operator = sp.kronecker_product(kernel.maps[a[0]],sp.eye(kernel.dimension**(hi-lo-1)))
        return operator.H*dense(a[2],kernel,values)*operator
    raise AssertionError(f"Missing dense interpretation for {term}")


class IndexedProofTests(unittest.TestCase):
    def setUp(self):
        self.hit = sp.ImmutableMatrix([[1,0],[0,0]])
        self.retry = sp.eye(2)-self.hit
        self.kernel = Kernel({"Hit":self.hit,"Retry":self.retry,"One":sp.eye(2)})
        self.family = first_acceptance("Success","Hit","Retry")
        self.k,self.n = self.family.start,self.family.end
        self.context = (self.k >= 0,self.k < self.n)

    def test_induction_is_protocol_independent_and_matches_dense_semantics(self):
        proof = effect_induction(self.family,self.kernel)
        self.assertTrue(self.kernel.induction(proof))
        for n in range(4):
            for k in range(n+1):
                values = {self.k:k,self.n:n}
                actual = dense(self.family(self.k,self.n),self.kernel,values)
                expected = sp.eye(2**(n-k))
                rejected = sp.ones(1)
                for _ in range(n-k):
                    rejected = sp.kronecker_product(rejected,self.retry)
                self.assertIs(clean(actual-(expected-rejected)).is_zero_matrix,True)
                if k < n:
                    self.assertIs(clean(dense(proof.step.left,self.kernel,values)-dense(proof.step.right,self.kernel,values)).is_zero_matrix,True)

    def test_nonprojective_heads_and_different_names_are_supported(self):
        kernel = Kernel({"A":sp.diag(sp.Rational(1,3),sp.Rational(1,4)),
                         "R":sp.diag(sp.Rational(1,2),sp.Rational(1,5))})
        family = first_acceptance("Weighted","A","R")
        self.assertTrue(kernel.induction(effect_induction(family,kernel)))

    def test_frame_and_accumulation_equal_the_global_operator_on_entangled_inputs(self):
        self.kernel.maps = {"K0":self.hit,"K1":self.retry}
        proof = framed_attempt(self.family,self.kernel,(("K0",True),("K1",False)),"One")
        self.assertTrue(self.kernel.check(proof,self.context))
        values = {self.k:0,self.n:3}
        left,right = dense(proof.left,self.kernel,values),dense(proof.right,self.kernel,values)
        self.assertIs(clean(left-right).is_zero_matrix,True)
        ghz = sp.zeros(8,1)
        ghz[0]=ghz[7]=1/sp.sqrt(2)
        rho=ghz*ghz.H
        self.assertEqual(sp.trace(left*rho),sp.Rational(1,2))
        self.assertEqual(sp.trace(left*rho),sp.trace(right*rho))

    def test_wrong_recurrence_is_rejected(self):
        proof = recurrence(self.family)
        wrong = add(tensor(local("Retry",self.k),identity(self.k+1,self.n)),proof.right.args[1])
        with self.assertRaises(Unsupported):
            self.kernel.check(replace(proof,right=wrong),self.context)

    def test_wrong_base_and_wrong_induction_family_are_rejected(self):
        proof = effect_induction(self.family,self.kernel)
        for changed in (replace(proof,base=Equality("Tensor-Linearity",self.family(self.n,self.n),identity(self.n,self.n))),
                        replace(proof,family=first_acceptance("Other","Retry","Hit"))):
            with self.assertRaises(Unsupported):
                self.kernel.induction(changed)

    def test_bad_local_bound_cannot_prove_an_effect(self):
        kernel=Kernel({"TooLarge":sp.eye(2),"Again":sp.eye(2)})
        family=first_acceptance("Bad","TooLarge","Again")
        with self.assertRaises(Unsupported):
            kernel.induction(effect_induction(family,kernel))

    def test_overlap_and_reversed_tensor_factors_are_rejected(self):
        for expression in (tensor(local("Hit",self.k),local("Retry",self.k)),
                           tensor(identity(self.k+1,self.n),local("Hit",self.k))):
            with self.assertRaises(Unsupported):
                self.kernel.check(Equality("Tensor-Linearity",expression,expression),self.context)

    def test_unjustified_product_split_and_sum_split_are_rejected(self):
        i=sp.Dummy("i",integer=True)
        for proof in (
            Equality("Product-Head",tensor_product("Retry",self.k,self.k),
                     tensor(local("Retry",self.k),tensor_product("Retry",self.k+1,self.k))),
            Equality("Sum-Head",finite_sum(i,self.n,self.n,identity(0,0)),
                     add(identity(0,0),finite_sum(i,self.n+1,self.n,identity(0,0))))):
            with self.assertRaises(Unsupported):
                self.kernel.check(proof,self.context)

    def test_sum_cannot_factor_an_operator_that_depends_on_its_binder(self):
        i=sp.Dummy("i",integer=True)
        expression=finite_sum(i,self.k,self.n,tensor(local("Hit",i),identity(i+1,self.n)))
        with self.assertRaises(Unsupported):
            self.kernel.check(Equality("Sum-Factor",expression,expression),self.context)

    def test_capture_avoiding_index_substitution(self):
        i=sp.Symbol("i",integer=True)
        expression=finite_sum(i,0,2,tensor(local("Hit",self.k),identity(self.k+1,self.n)))
        substituted=substitute(expression,{self.k:i})
        self.assertNotEqual(substituted.args[0],i)
        self.assertEqual(substituted.space,(i,self.n))

    def test_scope_cannot_leak_a_sum_assumption_to_an_outer_proof(self):
        proof=Equality("Product-Head",tensor_product("Retry",self.k,self.n),
                       tensor(local("Retry",self.k),tensor_product("Retry",self.k+1,self.n)))
        with self.assertRaises(Unsupported):
            self.kernel.check(proof,(self.k >= 0,self.k <= self.n))

    def test_sum_binder_cannot_capture_an_outer_context_variable(self):
        i=sp.Symbol("i",integer=True)
        left=finite_sum(i,0,2,tensor(tensor_product("Hit",0,i),identity(i,2)))
        right=finite_sum(i,0,2,tensor(identity(0,i),identity(i,2)))
        child=Equality("Product-Empty",tensor_product("Hit",0,i),identity(0,i))
        forged=Equality("Congruence",left,right,(child,),(3,0))
        with self.assertRaises(Unsupported):
            self.kernel.check(forged,(sp.Eq(i,100),))
        self.assertIs(clean(dense(left,self.kernel,{})-dense(right,self.kernel,{})).is_zero_matrix,False)

    def test_missing_rejection_branch_cannot_establish_the_family(self):
        self.kernel.maps={"K0":self.hit}
        proof=framed_attempt(self.family,self.kernel,(("K0",True),),"One")
        with self.assertRaises(Unsupported):
            self.kernel.check(proof,self.context)

    def test_wrong_frame_matrix_and_changed_suffix_are_rejected(self):
        self.kernel.maps={"K0":self.hit}
        target=tensor(local("One",self.k),self.family(self.k+1,self.n))
        left=pullback("K0",self.k,target)
        for right in (tensor(local("Retry",self.k),self.family(self.k+1,self.n)),
                      tensor(local("Hit",self.k),identity(self.k+1,self.n))):
            with self.assertRaises(Unsupported):
                self.kernel.check(Equality("Frame",left,right),self.context)

    def test_forged_rule_and_unscoped_induction_hypothesis_are_rejected(self):
        for proof in (Equality("Trust me",self.family(self.k,self.n),zero(self.k,self.n)),
                      Equality("Tensor-Linearity",identity(self.k,self.n),zero(self.k,self.n))):
            with self.assertRaises(Unsupported):
                self.kernel.check(proof,self.context)
        with self.assertRaises(Unsupported):
            self.kernel.positive(Positive("Induction-Hypothesis",self.family(self.k,self.n)),self.context)

    def test_exact_matrix_unit_normalization_preserves_multiplicity(self):
        a=local("Hit",self.k)
        b=local("Retry",self.k)
        expression=tensor(add(a,b),add(local("Hit",self.k+1),local("Retry",self.k+1)))
        expected=add(add(tensor(a,local("Hit",self.k+1)),tensor(a,local("Retry",self.k+1))),
                     add(tensor(b,local("Hit",self.k+1)),tensor(b,local("Retry",self.k+1))))
        self.assertTrue(self.kernel.check(Equality("Tensor-Linearity",expression,expected),(self.k >= 0,)))

    def test_local_definitions_cannot_be_overwritten_or_contain_floats(self):
        for name,value in (("Hit",self.retry),("Float",sp.Matrix([[0.5,0],[0,0.5]]))):
            with self.assertRaises(Unsupported):
                self.kernel.define(name,value)

    def test_excessive_proof_terms_have_an_explicit_budget(self):
        expression=identity(0,0)
        for _ in range(150):
            expression=add(expression,identity(0,0))
        with self.assertRaisesRegex(Unsupported,"budget"):
            self.kernel.check(Equality("Tensor-Linearity",expression,expression),())

    def test_family_definitions_cannot_have_free_indices(self):
        other=sp.Symbol("other",integer=True)
        with self.assertRaises(Unsupported):
            IndexedFamily("Bad",self.k,self.n,local("Hit",other))

    def test_explanation_contains_replayed_rules(self):
        proof=effect_induction(self.family,self.kernel)
        evidence=IndexedEvidence(self.kernel,proof)
        for rule in ("Sum-Head","Product-Head","Sum-Factor","Interval-Induction","Complement-Hypothesis"):
            self.assertIn(f"[{rule}]",evidence.explain())


if __name__ == "__main__":
    unittest.main()
