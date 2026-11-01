"""Universal normalized-state specifications and their soundness boundaries."""

import unittest

import sympy as sp
import z3

from verilocq import assertion, program, verify, Unsupported
from verilocq.examples import teleportation, remote_cnot, audit_pair_orders, audit_teleportation_orders
from verilocq.quantum import (Effect, clean, projector, psd, state_counterexample,
                             state_projector, state_symbols)


class GeneralStateTests(unittest.TestCase):
    def local(self, body="skip;", declaration="state psi;"):
        return program(f"program P {{ {declaration} process A {{ qubit q; {body} }} }}")

    def test_identity_is_proved_with_both_state_parameters_still_symbolic(self):
        p = self.local("H[q]; H[q];")
        report = verify("{ true ; rho(psi)[q] }", p, "{ true ; rho(psi)[q] }")
        self.assertTrue(report.verified, report.details())
        self.assertIn("For every normalized one-qubit state psi", str(report))
        sample = report.obligations[0].evidence.sample
        self.assertEqual(sample["pre"].free_symbols, set(state_symbols("psi")))
        self.assertIs(clean(sample["wp"] - sample["pre"]).is_zero_matrix, True)

    def test_normalization_and_effect_bounds_hold_without_dividing_by_amplitudes(self):
        rho = state_projector("psi")
        self.assertEqual(sp.simplify(sp.trace(rho)), 1)
        self.assertIs(clean(rho * rho - rho).is_zero_matrix, True)
        self.assertIs(psd(rho), True)
        self.assertIs(psd(clean(sp.eye(2) - rho)), True)
        theta, phase = state_symbols("psi")
        for angle, unit_phase, ket in (
            (0, 1, [1, 0]),
            (sp.pi / 2, 1, [0, 1]),
            (sp.pi / 4, sp.I, [1 / sp.sqrt(2), sp.I / sp.sqrt(2)]),
        ):
            self.assertEqual(clean(rho.subs({theta: angle, phase: unit_phase})),
                             projector(sp.Matrix(ket)))

    def test_measurement_cannot_be_mistaken_for_identity_on_arbitrary_inputs(self):
        p = program("program P { state psi; process A { qubit q; bit m; m:=M[q]; } }")
        report = verify("{ true ; rho(psi)[q] }", p, "{ true ; rho(psi)[q] }")
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status == "FAILED" and "psi" in o.witness for o in report.obligations))

    def test_state_is_read_only_and_must_be_declared(self):
        for p, predicate in ((self.local("psi:=0;"), "rho(psi)[q]"),
                             (self.local(declaration=""), "rho(psi)[q]"),
                             (self.local(), "rho(psi)[q,q]"),
                             (self.local(declaration="state psi,psi;"), "I"),
                             (self.local(declaration="state q;"), "I")):
            with self.subTest(source=p.source, predicate=predicate), self.assertRaises(Unsupported):
                verify(f"{{ true ; {predicate} }}", p, "{ true ; I }")

    def test_state_coordinates_are_not_a_backdoor_to_undeclared_or_singular_effects(self):
        backend = self.local()._lower()
        theta, _ = state_symbols("psi")
        for matrix in (sp.diag(sp.Symbol("unbound"), 0),
                       sp.ImmutableMatrix([[1, 1 / sp.sin(theta)], [0, 0]])):
            with self.subTest(matrix=matrix), self.assertRaises(Unsupported):
                Effect.constant(matrix).validate(backend)

    def test_projector_rule_requires_hermiticity(self):
        theta, _ = state_symbols("psi")
        nonhermitian = sp.ImmutableMatrix([[1, sp.cos(theta)], [0, 0]])
        self.assertIs(clean(nonhermitian * nonhermitian - nonhermitian).is_zero_matrix, True)
        self.assertIsNot(psd(nonhermitian), True)

    def test_passing_finite_instances_cannot_establish_a_symbolic_goal(self):
        backend = self.local()._lower()
        theta, _ = state_symbols("psi")
        residual = sp.ImmutableMatrix([[-sp.sin(4 * theta) ** 2]])
        self.assertIsNone(psd(residual))
        self.assertIsNone(state_counterexample(residual, backend))
        self.assertIs(psd(residual.subs(theta, sp.pi / 8)), False)

    def test_teleportation_matches_the_three_qubit_rocq_specification(self):
        case = teleportation()
        self.assertEqual(case.program.registers, ("A1", "A2", "B"))
        self.assertEqual(case.program.references, ())
        rho = state_projector("psi")
        self.assertEqual(case.pre.quantum.cases[0][1],
                         clean(sp.kronecker_product(rho, projector(sp.Matrix([1, 0, 0, 1]) / sp.sqrt(2)))))
        self.assertEqual(case.post.quantum.cases[0][1], sp.kronecker_product(sp.eye(4), rho))
        self.assertTrue(case.verify().verified)
        self.assertTrue(all(a["identity_channel"] for a in audit_teleportation_orders(case)))

    def test_missing_pauli_corrections_have_exact_state_counterexamples(self):
        for gate in ("X", "Z"):
            with self.subTest(gate=gate):
                report = teleportation(gate).verify()
                self.assertFalse(report.verified)
                self.assertTrue(any(o.status == "FAILED" and "psi" in o.witness
                                    for o in report.obligations))


class JointStateTests(unittest.TestCase):
    def test_four_complex_amplitudes_have_only_the_normalization_relation(self):
        coordinates = state_symbols("psi", 2)
        rho = state_projector("psi", 2)
        self.assertEqual(rho.free_symbols, set(coordinates))
        self.assertEqual(sp.trace(rho), 1)
        self.assertIs(clean(rho*rho-rho).is_zero_matrix, True)
        self.assertIs(psd(rho), True)
        self.assertIs(psd(clean(sp.eye(4)-rho)), True)
        # A rank-two coefficient array is entangled and cannot be represented
        # by a product of two single-qubit vectors. Its complex phase matters.
        ket = sp.Matrix([1, 0, 0, sp.I]) / sp.sqrt(2)
        actual = clean(rho.subs(dict(zip(coordinates, ket))))
        self.assertEqual(actual, projector(ket))
        self.assertEqual(sp.Matrix([[ket[0],ket[1]],[ket[2],ket[3]]]).det(), sp.I/2)

    def test_arbitrary_joint_state_is_transformed_by_a_gate(self):
        p = program('program P { state psi[2]; process A { qubits c,t; CNOT[c,t]; } }')
        report = verify('{ true ; rho(psi)[c,t] }', p,
                        '{ true ; CNOT[c,t] * rho(psi)[c,t] }')
        self.assertTrue(report.verified, report.details())
        self.assertIn('normalized two-qubit state psi', str(report))
        self.assertEqual(report.obligations[0].evidence.sample['pre'].free_symbols,
                         set(state_symbols('psi',2)))

    def test_partial_input_or_assuming_separability_cannot_hide_an_incorrect_gate(self):
        p = program('program P { state psi[2]; process A { qubits c,t; CNOT[c,t]; } }')
        report = verify('{ true ; rho(psi)[c,t] }', p, '{ true ; rho(psi)[c,t] }')
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status=='FAILED' and 'psi' in o.witness for o in report.obligations))

    def test_joint_state_arity_and_singular_amplitudes_are_rejected(self):
        p = program('program P { state psi[2]; process A { qubits c,t; skip; } }')
        for predicate in ('rho(psi)[c]', 'rho(psi)[c,c]'):
            with self.subTest(predicate=predicate), self.assertRaises(Unsupported):
                verify(f'{{ true ; {predicate} }}',p,'{ true ; I }')
        backend = p._lower()
        a = state_symbols('psi',2)[0]
        with self.assertRaises(Unsupported):
            Effect.constant(sp.diag(1,1,1,1/a)).validate(backend)

    def test_nonlocal_cnot_has_four_protocol_qubits_and_no_reference_registers(self):
        case = remote_cnot()
        self.assertEqual(case.program.registers, ('C','A','B','T'))
        self.assertFalse(case.program.references)
        self.assertEqual(case.program.state_parameters[0].qubits, 2)
        self.assertTrue(case.verify().verified)
        self.assertTrue(audit_pair_orders(case).verified)
        for gate in ('X','Z'):
            with self.subTest(gate=gate):
                report=remote_cnot(gate).verify()
                self.assertFalse(report.verified)
                self.assertTrue(any(o.status=='FAILED' and 'psi' in o.witness for o in report.obligations))


class PhaseDomainTests(unittest.TestCase):
    def setUp(self):
        self.p=program('program P { process A { qubit q; phase alpha; R(alpha)[q]; } }')

    def test_paper_domain_is_preserved_and_printed(self):
        domain='0 <= alpha and alpha < 2*pi'
        report=verify(f'{{ {domain} ; Zero[q] }}',self.p,f'{{ {domain} ; Zero[q] }}')
        self.assertTrue(report.verified)
        self.assertIn(domain,str(report))

    def test_nontrivial_angle_restrictions_are_not_silently_erased(self):
        for restriction in ('alpha=0','alpha<pi','alpha>1','alpha=1'):
            with self.subTest(restriction=restriction), self.assertRaises(Unsupported):
                verify(f'{{ {restriction} ; Plus[q] }}',self.p,'{ true ; Plus[q] }')

    def test_a_false_domain_condition_is_not_treated_as_true(self):
        pre=assertion('alpha < 0','Zero[q]')._compile(self.p._lower())
        self.assertEqual(str(pre.classical),'False')


class ProofHorizonTests(unittest.TestCase):
    def test_paper_horizon_uses_the_same_global_controller_invariant(self):
        from test_frontend import notebook_programs
        from test_hoare_interface import THETA, RANK
        from verilocq.frontend import RetryProof
        p=program(notebook_programs()['distill'])
        plain=RetryProof(p,THETA,RANK)._model()
        bounded=RetryProof(p,f'({THETA}) and kA<n',RANK)._model()
        solver=bounded.controller.solver()
        solver.add(z3.Xor(plain.theta,bounded.theta))
        self.assertEqual(solver.check(),z3.unsat)

    def test_unrelated_counter_restrictions_are_not_erased(self):
        from test_frontend import notebook_programs
        from test_hoare_interface import THETA, RANK
        from verilocq.frontend import RetryProof
        p=program(notebook_programs()['distill'])
        plain=RetryProof(p,THETA,RANK)._model()
        narrowed=RetryProof(p,f'({THETA}) and kA<n-1',RANK)._model()
        solver=narrowed.controller.solver()
        solver.add(z3.Xor(plain.theta,narrowed.theta))
        self.assertEqual(solver.check(),z3.sat)


if __name__ == "__main__":
    unittest.main()
