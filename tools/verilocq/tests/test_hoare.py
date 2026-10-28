"""Paper-rule replay and adversarial proof-object regressions."""

from dataclasses import replace
import unittest

import sympy as sp
import z3

from verilocq import (Assign, Branch, Gate, Measure, Process, Program, Receive,
                      Send, Skip, Unsupported, Variable)
from verilocq import hoare as h
from verilocq import indexed as ix
from verilocq.distillation import distillation
from verilocq.quantum import embed


class HoareRulesTests(unittest.TestCase):
    def setUp(self):
        self.model=distillation()
        self.schema=self.model.controller
        self.layout=h.Layout(self.schema,{"ac":"kA","at":"kA","bc":"kB","bt":"kB"})
        self.kernel=ix.Kernel({"One":sp.eye(16)})
        self.quantum=h.QuantumChecker(self.schema,self.kernel,())
        self.checker=h.RuleChecker(self.schema,self.layout,self.quantum)
        self.a=h.Assertion(True,h.I)

    def test_actual_meas_aux_subst_accumulation_and_sequence_rules(self):
        block=(Gate("CNOT",("ac","at")),Measure("mA","at"),Assign("sentA",False))
        proof=h.prove_local(self.schema,self.layout,self.a,block,self.a)
        self.assertTrue(self.checker.check(proof))
        rules={node.rule for node in self.checker.steps}
        self.assertTrue({"Unitary","Meas","Aux-Subst","Branch-Accum","Seq","Conseq","Assert-Eq"} <= rules)

    def test_meas_requires_a_fresh_variable_not_an_expression(self):
        command=Measure("mA","at")
        x=self.schema.varmap["mA"].symbol
        for y in (x+1,z3.IntVal(0),x):
            pre=h.Assertion(True,h.backward(self.layout.operation(command,y),h.I))
            post=h.Assertion(z3.And(True,x==y),h.I)
            proof=h.Proof("Meas",pre,(command,),post,data=(self.a,y))
            with self.assertRaises(Unsupported):
                self.checker.check(proof)

    def test_aux_subst_cannot_substitute_an_expression_containing_an_assigned_variable(self):
        x=self.schema.varmap["mA"].symbol
        command=Assign("mA",0)
        post=h.Assertion(x+1==1,h.I)
        pre=post.substitute(((x,z3.IntVal(0)),))
        child=h.Proof("Assign",pre,(command,),post)
        mapping=((x+1,z3.IntVal(0)),)
        forged=h.Proof("Aux-Subst",pre.substitute(mapping),(command,),post.substitute(mapping),(child,),(x+1,0))
        with self.assertRaises(Unsupported):
            self.checker.check(forged)

    def test_aux_subst_checks_program_reads_and_writes(self):
        x=self.schema.varmap["mA"].symbol
        child=h.Proof("Assign",self.a,(Assign("mA",0),),self.a)
        forged=h.Proof("Aux-Subst",self.a,child.block,self.a,(child,),(x,0))
        with self.assertRaises(Unsupported):
            self.checker.check(forged)

    def test_dummy_indices_cannot_alias_declared_program_indices(self):
        p0=embed(sp.ImmutableMatrix(sp.diag(1,0)),(0,),4)
        p1=sp.eye(16)-p0
        kernel=ix.Kernel({"P0":p0,"P1":p1})
        quantum=h.QuantumChecker(self.schema,kernel,())
        checker=h.RuleChecker(self.schema,self.layout,quantum)
        at=sp.Symbol("kA",integer=True)
        other=sp.Dummy("kA",integer=True)
        pre=h.Assertion(True,h.leaf(ix.local("P1",at)))
        post=h.Assertion(True,h.leaf(ix.local("P0",other)))
        proof=h.prove_local(self.schema,self.layout,pre,(Gate("X",("ac",)),),post)
        with self.assertRaises(Unsupported):
            checker.check(proof)

    def test_index_substitution_uses_symbol_identity(self):
        at=sp.Dummy("kA",integer=True)
        formula=h.leaf(ix.local("One",at))
        replaced=formula.substitute(((self.schema.varmap["kA"].symbol,z3.IntVal(0)),))
        self.assertEqual(replaced.args[0],formula.args[0])

    def test_identity_factors_cannot_hide_tensor_overlap(self):
        k=sp.Symbol("kA",integer=True)
        n=sp.Symbol("n",integer=True)
        q=h.leaf(ix.tensor(ix.local("One",k),ix.identity(k,n)))
        assertion=h.Assertion(self.schema.varmap["kA"].symbol<self.schema.varmap["n"].symbol,q)
        with self.assertRaises(Unsupported):
            self.checker.check(h.Proof("Skip",assertion,(),assertion))

    def test_predicates_outside_effect_bounds_are_rejected(self):
        kernel=ix.Kernel({"TooLarge":2*sp.eye(16)})
        checker=h.RuleChecker(self.schema,self.layout,h.QuantumChecker(self.schema,kernel,()))
        assertion=h.Assertion(True,h.leaf(ix.local("TooLarge",sp.Symbol("kA",integer=True))))
        with self.assertRaises(Unsupported):
            checker.check(h.Proof("Skip",assertion,(),assertion))

    def test_malformed_predicate_syntax_is_rejected_even_for_false_preconditions(self):
        with self.assertRaises(Unsupported):
            assertion=h.Assertion(False,h.Formula("not-a-quantum-formula"))
            self.checker.check(h.Proof("Skip",assertion,(),assertion))
        with self.assertRaises(Unsupported):
            ix.Term("not-an-operator",())

    def test_changed_quantum_environment_invalidates_replay(self):
        proof=h.Proof("Skip",self.a,(),self.a)
        self.kernel.matrices["One"]=2*sp.eye(16)
        with self.assertRaisesRegex(Unsupported,"changed"):
            self.checker.check(proof)

    def test_cache_keys_distinguish_sorts_and_reject_shadowed_declarations(self):
        a,b,c=z3.Bools("kA kB n")
        boolean_claim=z3.Or(a==b,a==c,b==c)
        child=h.Proof("Skip",self.a,(),self.a)
        with self.assertRaisesRegex(Unsupported,"different type"):
            self.checker.check(h.Proof("Conseq",self.a,(),h.Assertion(boolean_claim,h.I),(child,)))
        x,y,n=(self.schema.varmap[name].symbol for name in ("kA","kB","n"))
        integer_claim=z3.Or(x==y,x==n,y==n)
        self.assertNotEqual(h.expression_key(boolean_claim),h.expression_key(integer_claim))
        with self.assertRaises(Unsupported):
            self.checker.check(h.Proof("Conseq",self.a,(),h.Assertion(integer_claim,h.I),(child,)))

    def test_unsupported_function_cannot_poison_a_builtin_operator_cache(self):
        fake_add=z3.Function("+",z3.IntSort(),z3.IntSort(),z3.BoolSort())
        a=[fake_add(z3.IntVal(0),z3.IntVal(k)) for k in range(3)]
        b=[z3.IntVal(0)+z3.IntVal(k) for k in range(3)]
        pigeonhole=lambda values:z3.Or(values[0]==values[1],values[0]==values[2],values[1]==values[2])
        self.assertNotEqual(h.expression_key(pigeonhole(a)),h.expression_key(pigeonhole(b)))
        child=h.Proof("Skip",self.a,(),self.a)
        for post in (pigeonhole(a),pigeonhole(b)):
            with self.assertRaises(Unsupported):
                self.checker.check(h.Proof("Conseq",self.a,(),h.Assertion(post,h.I),(child,)))

    def test_assignment_cannot_escape_its_declared_domain(self):
        proof=h.Proof("Assign",self.a,(Assign("mA",2),),self.a)
        with self.assertRaisesRegex(Unsupported,"domain"):
            self.checker.check(proof)

    def test_an_inconsistent_invalid_program_cannot_prove_false_by_vacuity(self):
        variables=(Variable("x","P",(0,)),Variable("x","P",(1,)))
        schema=Program("Invalid",variables,("q",),(Process("P",("q",),(),()),))
        layout=h.Layout(schema,{})
        quantum=h.QuantumChecker(schema,ix.Kernel({"I":sp.eye(2)}),())
        checker=h.RuleChecker(schema,layout,quantum)
        false=h.Assertion(False,h.I)
        with self.assertRaisesRegex(Unsupported,"Duplicate"):
            checker.check(h.prove_local(schema,layout,self.a,(),false))

    def test_wrong_assignment_and_sequence_assertions_are_rejected(self):
        x=self.schema.varmap["mA"].symbol
        post=h.Assertion(x==1,h.I)
        proof=h.Proof("Assign",self.a,(Assign("mA",0),),post)
        with self.assertRaises(Unsupported):
            self.checker.check(proof)
        left=h.Proof("Skip",self.a,(),self.a)
        right=h.Proof("Skip",post,(),post)
        with self.assertRaises(Unsupported):
            self.checker.check(h.Proof("Seq",self.a,(),post,(left,right)))

    def test_branch_accumulation_requires_exclusive_posts(self):
        command=Measure("mA","at")
        generated=h.local_proof(self.schema,self.layout,(command,),self.a)
        accumulated=generated.premises[0]
        child=accumulated.premises[0]
        pre=h.Assertion(True,h.plus(child.pre.quantum,child.pre.quantum))
        post=h.Assertion(z3.Or(child.post.classical,child.post.classical),h.I)
        with self.assertRaises(Unsupported):
            self.checker.check(h.Proof("Branch-Accum",pre,(command,),post,(child,child)))

    def test_false_total_correctness_using_constant_old_rank_is_rejected(self):
        r=Variable("r","Bob",(0,1))
        alice=Process("Alice",("a",),(),(Branch("send",True,Send("c",0),(Skip(),)),))
        bob=Process("Bob",("b",),(),(Branch("recv",True,Receive("c","r"),(Skip(),)),))
        schema=Program("Infinite",(r,),("a","b"),(alice,bob))
        layout=h.Layout(schema,{})
        checker=h.RuleChecker(schema,layout,h.QuantumChecker(schema,ix.Kernel({"I":sp.eye(4)}),()))
        inv=h.Assertion(True,h.I)
        pairs=tuple(schema.matching_pairs())
        initial=h.prove_local(schema,layout,inv,schema.initialization,inv)
        preserved=tuple(h.prove_local(schema,layout,h.Assertion(z3.And(True,g),h.I),body,inv) for _,g,body in pairs)
        rank=z3.IntVal(1)
        old=z3.IntVal(0)
        ranked=tuple(h.prove_local(schema,layout,h.Assertion(z3.And(True,g,rank==old),h.I),body,h.Assertion(rank<old,h.I)) for _,g,body in pairs)
        post=h.Assertion(z3.And(True,schema.termination),h.I)
        forged=h.Proof("Distributed-tot",inv,schema,post,(initial,*preserved,*ranked),(h.DistributedData(inv,rank,old),))
        with self.assertRaisesRegex(Unsupported,"ranking variable"):
            checker.check(forged)

    def test_distributed_rule_rejects_missing_or_duplicate_premises(self):
        proof=h.prove_distributed(self.schema,self.layout,self.a,self.a,self.a,z3.IntVal(1))
        distributed=proof.premises[0]
        with self.assertRaisesRegex(Unsupported,"omits or duplicates"):
            self.checker.check(replace(distributed,premises=distributed.premises[:-1]))


if __name__=="__main__":
    unittest.main()
