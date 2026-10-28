"""Soundness-sensitive regressions and end-to-end checks, using only unittest."""

from dataclasses import replace
import unittest

import sympy as sp
import z3

from verilocq import (Assertion, Assign, Branch, Effect, Gate, If, Measure,
                       Process, Program, Receive, Reset, Send, Unsupported,
                       Variable, check_hoare, projector, seq, verify_distributed)
from verilocq.examples import audit_teleportation_orders, teleportation
from verilocq.quantum import BELL, H, I2, X, clean, embed, psd
from verilocq.verifier import states, weakest_precondition


class ExactLocalTests(unittest.TestCase):
    def setUp(self):
        self.x = z3.Int("x")
        self.program = Program("local", (Variable("x", "P", (0, 1, 2)),),
                               ("q",), (Process("P", ("q",), (), ()),))
        self.identity = Effect.constant(I2)

    def assertion(self, classical=True, matrix=I2):
        return Assertion(classical, Effect.constant(matrix))

    def test_assignment_verifies_and_wrong_post_fails(self):
        pre = self.assertion(self.x <= 1)
        block = seq(Assign("x", self.x + 1))
        self.assertEqual(check_hoare(self.program, pre, block, self.assertion(self.x >= 1)).status, "PASSED")
        self.assertEqual(check_hoare(self.program, pre, block, self.assertion(self.x == 2)).status, "FAILED")

    def test_unused_assignment_domain_escape_is_not_hidden_by_projection(self):
        result = check_hoare(self.program, self.assertion(), seq(Assign("x", self.x + 1)), self.assertion())
        self.assertEqual(result.status, "INCOMPLETE")
        self.assertIn("escapes", result.detail)

    def test_hadamard_exact_projector(self):
        pre = self.assertion(matrix=sp.diag(1, 0))
        post = self.assertion(matrix=projector(H * sp.Matrix([1, 0])))
        self.assertEqual(check_hoare(self.program, pre, seq(Gate("H", ("q",))), post).status, "PASSED")

    def test_measurement_wp_keeps_probabilities(self):
        self.program.validate()
        post = self.assertion(self.x == 0)
        wp = weakest_precondition(self.program, seq(Measure("x", "q")), post, {"x": 2})
        self.assertEqual(wp, sp.diag(1, 0))

    def test_measurement_branches_are_summed(self):
        effect = Effect("measured state", ((self.x == 0, sp.ImmutableMatrix(sp.diag(1, 0))),
                                           (self.x != 0, sp.ImmutableMatrix(sp.diag(0, 1)))))
        result = check_hoare(self.program, self.assertion(), seq(Measure("x", "q")), Assertion(True, effect))
        self.assertEqual(result.status, "PASSED")

    def test_measurement_followed_by_conditional_correction(self):
        block = seq(Measure("x", "q"), If(self.x == 1, seq(Gate("X", ("q",)))))
        result = check_hoare(self.program, self.assertion(), block, self.assertion(matrix=sp.diag(1, 0)))
        self.assertEqual(result.status, "PASSED")

    def test_reset_is_trace_preserving_not_postselection(self):
        result = check_hoare(self.program, self.assertion(), seq(Reset("q")), self.assertion(matrix=sp.diag(1, 0)))
        self.assertEqual(result.status, "PASSED")

    def test_conditional_uses_actual_classical_values(self):
        block = seq(If(self.x == 0, seq(Assign("x", 1)), seq(Assign("x", 2))))
        result = check_hoare(self.program, self.assertion(), block, self.assertion(self.x >= 1))
        self.assertEqual(result.status, "PASSED")

    def test_unknown_limit_never_passes(self):
        result = check_hoare(self.program, self.assertion(), (), self.assertion(self.x >= 0), max_states=1)
        self.assertEqual(result.status, "INCOMPLETE")

    def test_declared_domains_are_part_of_the_specification(self):
        valuations = list(states(self.program, True, {"x"}))
        self.assertEqual({s["x"] for s in valuations}, {0, 1, 2})

    def test_nonhermitian_indefinite_and_psd(self):
        self.assertIs(psd(sp.ImmutableMatrix([[0, 1], [0, 0]])), False)
        self.assertIs(psd(sp.ImmutableMatrix([[0, 1], [1, 0]])), False)
        self.assertIs(psd(projector(BELL)), True)

    def test_exact_algebraic_psd(self):
        matrix = sp.ImmutableMatrix([[1, sp.I * sp.sqrt(2)], [-sp.I * sp.sqrt(2), 2]])
        self.assertIs(psd(matrix), True)
        self.assertIs(psd(clean(matrix - sp.eye(2))), False)

    def test_reject_float_effects(self):
        with self.assertRaises(Unsupported):
            check_hoare(self.program, self.assertion(matrix=sp.diag(0.5, 0.5)), (), self.assertion())

    def test_reject_invalid_effects(self):
        with self.assertRaises(Unsupported):
            check_hoare(self.program, self.assertion(matrix=2 * I2), (), self.assertion())

    def test_reject_overlapping_effect_cases(self):
        effect = Effect("bad", ((True, I2), (self.x == 0, I2)))
        with self.assertRaises(Unsupported):
            check_hoare(self.program, Assertion(True, effect), (), self.assertion())

    def test_ordered_nonadjacent_cnot_embedding(self):
        # Controls on register 2, targets on register 0: |001> -> |101>.
        from verilocq.quantum import CNOT
        basis = sp.eye(8)[:, 1]
        self.assertEqual(embed(CNOT, (2, 0), 3) * basis, sp.eye(8)[:, 5])

    def test_reject_aliased_gate_targets(self):
        with self.assertRaises(Unsupported):
            check_hoare(self.program, self.assertion(), seq(Gate("CNOT", ("q", "q"))), self.assertion())


class DistributedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.good = teleportation()
        cls.report = cls.good.verify()

    def test_teleportation_all_total_correctness_premises(self):
        self.assertTrue(self.report.verified, str(self.report))
        self.assertEqual(len(self.report.obligations), 9)
        self.assertEqual([o.cases for o in self.report.obligations[:3]], [4, 12, 12])

    def test_both_orders_induce_identity_on_full_matrix_space(self):
        records = audit_teleportation_orders(self.good)
        self.assertGreaterEqual(len(records), 2)
        self.assertEqual({r["order"] for r in records}, {"send_z → send_x", "send_x → send_z"})
        for record in records:
            self.assertEqual(record["measurement_paths"], 4)
            self.assertTrue(record["trace_preserving"])
            self.assertEqual(record["channel_matrix"], sp.eye(4))

    def test_missing_x_and_z_are_both_detected(self):
        for gate in ("X", "Z"):
            with self.subTest(gate=gate):
                case = teleportation(gate)
                report = case.verify()
                self.assertFalse(report.verified)
                self.assertTrue(any(o.status == "FAILED" for o in report.obligations))
                records = audit_teleportation_orders(case)
                self.assertTrue(all(not r["identity_channel"] for r in records))
                self.assertTrue(all(r["trace_preserving"] for r in records))

    def test_zero_rank_fails(self):
        case = self.good
        report = verify_distributed(case.program, case.pre, case.invariant, case.post, variant=z3.IntVal(0))
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status == "FAILED" and o.name.startswith("Ranking decreases") for o in report.obligations))

    def test_deadlock_is_detected(self):
        case = self.good
        alice, bob = case.program.processes
        bad_branch = replace(bob.branches[0], action=Receive("unmatched", "i"))
        bob = replace(bob, branches=(bad_branch, bob.branches[1]))
        program = replace(case.program, processes=(alice, bob))
        report = verify_distributed(program, case.pre, case.invariant, case.post, variant=case.variant)
        self.assertFalse(report.verified)
        self.assertEqual(next(o for o in report.obligations if o.name == "No deadlock under invariant").status, "FAILED")

    def test_limits_are_unknown_never_verified(self):
        for options in ({"max_states": 1}, {"max_paths": 1}):
            report = self.good.verify(**options)
            self.assertFalse(report.verified)
            self.assertTrue(any(o.status == "INCOMPLETE" for o in report.obligations))

    def test_partial_mode_is_explicit(self):
        case = self.good
        report = verify_distributed(case.program, case.pre, case.invariant, case.post)
        self.assertTrue(report.verified)
        self.assertEqual(report.mode, "partial correctness")
        self.assertEqual(len(report.obligations), 5)

    def test_reference_is_read_only(self):
        case = self.good
        alice, bob = case.program.processes
        alice = replace(alice, init=seq(Gate("X", ("R",)), alice.init))
        with self.assertRaises(Unsupported):
            replace(case.program, processes=(alice, bob)).validate()

    def test_classical_nonlocal_reads_are_rejected(self):
        case = self.good
        alice, bob = case.program.processes
        alice = replace(alice, init=seq(Assign("pA", case.symbols["pB"]), alice.init))
        with self.assertRaises(Unsupported):
            replace(case.program, processes=(alice, bob)).validate()

    def test_another_protocol_is_not_hardcoded_to_teleportation(self):
        sent, received = z3.Bools("sent received")
        value = z3.Int("value")
        variables = (Variable("sent", "A", (False, True)), Variable("received", "B", (False, True)),
                     Variable("value", "B", (0, 1)))
        a = Process("A", ("q",), seq(Assign("sent", False)), (
            Branch("send", z3.Not(sent), Send("c", 1), seq(Assign("sent", True))),))
        b = Process("B", (), seq(Assign("received", False)), (
            Branch("receive", z3.Not(received), Receive("c", "value"), seq(Assign("received", True))),))
        program = Program("one-bit transfer", variables, ("q",), (a, b))
        effect = Effect.constant(I2)
        invariant = Assertion(z3.And(sent == received, z3.Implies(received, value == 1)), effect)
        report = verify_distributed(program, Assertion(True, effect), invariant,
                                    Assertion(value == 1, effect), variant=1 - z3.If(sent, 1, 0))
        self.assertTrue(report.verified, str(report))


if __name__ == "__main__":
    unittest.main()
