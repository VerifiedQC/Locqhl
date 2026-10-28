"""All paper examples and adversarial regressions from the independent review."""

from contextlib import redirect_stdout
from dataclasses import replace
import io
import json
from unittest.mock import patch
import unittest

import sympy as sp
import z3

from verilocq import (Assign, Gate, If, Measure, Process, Program, Unsupported,
                       Variable, check_implication, seq)
from verilocq.__main__ import main
from verilocq.distillation import distillation
from verilocq.examples import (audit_pair_orders, audit_teleportation_orders,
                                entanglement_swapping, remote_cnot, teleportation)


class AdditionalFiniteExamples(unittest.TestCase):
    def test_swapping_and_both_orders(self):
        case = entanglement_swapping()
        self.assertTrue(case.verify().verified)
        self.assertTrue(audit_pair_orders(case).verified)

    def test_nonlocal_cnot_and_both_orders(self):
        case = remote_cnot()
        self.assertTrue(case.verify().verified)
        self.assertTrue(audit_pair_orders(case).verified)

    def test_missing_corrections_in_new_examples(self):
        for factory in (entanglement_swapping, remote_cnot):
            for correction in ("X", "Z"):
                with self.subTest(factory=factory.__name__, correction=correction):
                    report = factory(correction).verify()
                    self.assertFalse(report.verified)
                    self.assertTrue(any(o.status == "FAILED" for o in report.obligations))


class ReviewRegressions(unittest.TestCase):
    def test_channel_audit_does_not_hide_a_relevant_initial_scratch_bit(self):
        case = teleportation()
        alice, bob = case.program.processes
        changed = replace(alice, init=seq(If(case.symbols["m1"] == 1,
                                            seq(Gate("X", ("A1",)))), alice.init))
        case.program = replace(case.program, processes=(changed, bob))
        self.assertFalse(case.verify().verified)
        audits = audit_teleportation_orders(case)
        self.assertEqual({a["initial_classical"]["m1"] for a in audits}, {0, 1})
        self.assertTrue(any(not a["identity_channel"] for a in audits))

    def test_public_implication_rejects_duplicate_variable_declarations(self):
        program = Program("invalid", (Variable("x", "P", (0,)), Variable("x", "P", (1,))),
                          ("q",), (Process("P", ("q",), (), ()),))
        with self.assertRaises(Unsupported):
            check_implication(program, True, False, "must not prove False")

    def test_json_and_audits_produce_one_valid_document(self):
        output = io.StringIO()
        with patch("sys.argv", ["verilocq", "--case", "teleportation", "--json", "--audit-orders"]):
            with redirect_stdout(output):
                result = main()
        document = json.loads(output.getvalue())
        self.assertEqual(result, 0)
        self.assertEqual(document["status"], "VERIFIED")
        self.assertEqual(len({a["order"] for a in document["case_studies"][0]["audits"]}), 2)

    def test_report_html_contains_no_table(self):
        rendered = teleportation().verify()._repr_html_()
        self.assertNotIn("<table", rendered.lower())
        self.assertIn("<pre>", rendered)


class DistillationSchemaTests(unittest.TestCase):
    def test_missing_paper_hoare_proof_prevents_verification(self):
        with patch("verilocq.hoare.prove_distributed",return_value=None):
            report=distillation().verify()
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status=="INCOMPLETE" and o.kind=="Hoare proof replay" for o in report.obligations))

    def test_an_unrelated_valid_proof_cannot_replace_the_requested_indexed_goal(self):
        from verilocq.indexed import Equality, identity
        unrelated=Equality("Tensor-Linearity",identity(0,0),identity(0,0))
        with patch("verilocq.distillation.framed_attempt",return_value=unrelated):
            report=distillation().verify()
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status == "INCOMPLETE" and "actual indexed measurement WP" in o.detail for o in report.obligations))

    def test_missing_induction_proof_prevents_verification(self):
        with patch("verilocq.distillation.effect_induction",return_value=None):
            report=distillation().verify()
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status == "INCOMPLETE" and "requested family" in o.detail for o in report.obligations))

    def test_complete_parametric_schema(self):
        case = distillation()
        report = case.verify()
        self.assertTrue(report.verified, str(report))
        self.assertIn("every finite n", report.mode)
        self.assertEqual(case.controller.varmap["kA"].domain, None)

    def test_omitting_either_bilateral_gate_fails(self):
        for owner in ("Alice", "Bob"):
            report = distillation(owner).verify()
            self.assertFalse(report.verified)
            self.assertTrue(any(o.status == "FAILED" for o in report.obligations))
            induction = next(o for o in report.obligations if o.name == "Fresh-factor first-acceptance induction rule")
            self.assertEqual(induction.status, "INCOMPLETE")

    def test_corrupting_a_recorded_measurement_outcome_fails(self):
        case = distillation()

        def corrupt(block):
            result = []
            for command in block:
                if isinstance(command, If):
                    command = replace(command, then=corrupt(command.then), otherwise=corrupt(command.otherwise))
                result.append(command)
                if isinstance(command, Measure) and command.target == "mA":
                    result.append(Assign("mA", 1 - case.symbols["mA"]))
            return tuple(result)

        alice, bob = case.controller.processes
        alice = replace(alice, init=corrupt(alice.init),
                        branches=tuple(replace(b, body=corrupt(b.body)) for b in alice.branches))
        case.controller = replace(case.controller, processes=(alice, bob))
        report = case.verify()
        self.assertFalse(report.verified, str(report))
        self.assertTrue(any(o.status == "FAILED" and o.name.startswith("Indexed quantum step") for o in report.obligations))

    def test_proof_parameter_cannot_become_an_executable_variable(self):
        case = distillation()
        variables = tuple(replace(v, owner="Alice") if v.name == "n" else v for v in case.controller.variables)
        alice, bob = case.controller.processes
        alice = replace(alice, init=seq(Assign("n", 1), alice.init))
        case.controller = replace(case.controller, variables=variables, processes=(alice, bob))
        with self.assertRaises(Unsupported):
            case.verify()

    def test_reusing_the_same_resource_index_fails(self):
        case = distillation()

        def stop_incrementing(block):
            result = []
            for command in block:
                if isinstance(command, If):
                    command = replace(command, then=stop_incrementing(command.then), otherwise=stop_incrementing(command.otherwise))
                if isinstance(command, Assign) and command.target == "kA":
                    command = Assign("kA", case.symbols["kA"])
                result.append(command)
            return tuple(result)

        alice, bob = case.controller.processes
        alice = replace(alice, branches=tuple(replace(b, body=stop_incrementing(b.body)) for b in alice.branches))
        case.controller = replace(case.controller, processes=(alice, bob))
        self.assertFalse(case.verify().verified)

    def test_werner_bounds_are_exact_and_state_their_assumption(self):
        case = distillation()
        result = case.bounds(sp.Rational(4, 5), attempts=1)
        self.assertEqual(result["accepted_mass_lower_bound"], result["p"])
        self.assertEqual(result["bell_overlap_lower_bound"], result["g"])
        self.assertGreater(result["asymptotic_fidelity"], result["input_fidelity"])
        self.assertIn("Independent", result["assumption"])
        with self.assertRaises(ValueError):
            case.bounds(0.8)
        with self.assertRaises(ValueError):
            case.bounds(sp.Rational(4, 5), attempts=0)

    def test_broken_protocol_cannot_export_successful_protocol_bounds(self):
        with self.assertRaises(Unsupported):
            distillation(omit_bilateral_gate="Alice").bounds()

    def test_array_template_layout_cannot_be_silently_changed(self):
        case = distillation()
        case.controller = replace(case.controller, registers=("at", "bc", "ac", "bt"))
        with self.assertRaises(Unsupported):
            case.verify()

    def test_weakening_invariant_cannot_hide_acceptance_of_wrong_outcomes(self):
        case = distillation()
        v = case.symbols

        def accept_without_comparison(block):
            output = []
            for command in block:
                if isinstance(command, If):
                    condition = command.condition
                    if condition.eq(v["mA"] == v["rA"]) or condition.eq(v["mB"] == v["rB"]):
                        condition = z3.BoolVal(True)
                    command = replace(command, condition=condition,
                                      then=accept_without_comparison(command.then),
                                      otherwise=accept_without_comparison(command.otherwise))
                output.append(command)
            return tuple(output)

        case.controller = replace(case.controller, processes=tuple(
            replace(p, branches=tuple(replace(b, body=accept_without_comparison(b.body)) for b in p.branches))
            for p in case.controller.processes))
        case.theta = z3.And(v["kA"] == v["kB"], v["doneA"] == v["doneB"],
                            v["sentA"] == v["recvB"], v["sentB"] == v["recvA"],
                            z3.Implies(v["recvA"], v["rA"] == v["mB"]),
                            z3.Implies(v["recvB"], v["rB"] == v["mA"]),
                            v["doneA"] == z3.And(v["sentA"], v["recvA"]))
        report = case.verify()
        self.assertFalse(report.verified, str(report))
        self.assertEqual(next(o for o in report.obligations if o.name == "Exit selects the accepted quantum postcondition").status, "FAILED")


if __name__ == "__main__":
    unittest.main()
