"""RSP for every phase, scheduler-selected gate families, and actual retry traces."""

import ast
import json
from pathlib import Path
import unittest

import sympy as sp

from verilocq import Unsupported, SourceError, assertion, program, trace_retry, verify
from verilocq.frontend import _matrix_literal
from verilocq.quantum import BELL, Effect, UnitPhase, clean, embed, phase_symbol, projector, psd


def source_definitions():
    path = Path(__file__).resolve().parents[1] / "Quickstart.ipynb"
    result = {}
    for cell in json.loads(path.read_text())["cells"]:
        if cell["cell_type"] != "code":
            continue
        for node in ast.walk(ast.parse("".join(cell["source"]))):
            if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Call)
                    and isinstance(node.value.func, ast.Name) and node.value.func.id == "program"
                    and isinstance(node.value.args[0], ast.Constant)):
                result[node.targets[0].id] = node.value.args[0].value
    return result


def rsp_check(protocol):
    return verify(protocol, pre=assertion("true", "Bell[A,B]"), post=assertion("true", "Equator(alpha)[B]"),
                  invariant=assertion("d <=> p = 1", "Z[B]^((1-p)*m) * Equator(alpha)[B]"), decreases="1-[d]")


def phase_check(protocol, post="U(s)[B] * Bell[A,B]"):
    return verify(protocol, pre=assertion("true", "Bell[A,B]"), post=assertion("true", post),
                  invariant=assertion("a <=> b", "U(s)[B]^[a] * Bell[A,B]"), decreases="1-[a]")


class UniversalRSPTests(unittest.TestCase):
    def test_rsp_proof_keeps_a_universal_phase_instead_of_angle_samples(self):
        p = program(source_definitions()["rsp"])
        report = rsp_check(p)
        self.assertTrue(report.verified, str(report))
        self.assertEqual(report.mode, "total correctness")
        backend = p._lower()
        self.assertNotIn("alpha", backend.varmap)
        effect = assertion("true", "Equator(alpha)[B]")._compile(backend).quantum
        self.assertEqual(effect.cases[0][1].free_symbols, {phase_symbol("alpha")})

    def test_missing_z_correction_has_the_measurement_one_counterexample(self):
        report = rsp_check(program(source_definitions()["bad_rsp"]))
        self.assertFalse(report.verified)
        failure = next(o for o in report.obligations if o.status == "FAILED")
        self.assertEqual(failure.witness["m"], 1)

    def test_phase_parameter_cannot_be_assigned(self):
        source = source_definitions()["rsp"].replace("R(alpha)[A];", "alpha := 0; R(alpha)[A];")
        with self.assertRaises(Unsupported):
            rsp_check(program(source))

    def test_phase_parameter_obeys_process_ownership(self):
        source = source_definitions()["rsp"].replace("p := 0;", "R(alpha)[B]; p := 0;")
        with self.assertRaises(Unsupported):
            rsp_check(program(source))

    def test_phase_parameter_must_be_declared(self):
        with self.assertRaises(Unsupported):
            rsp_check(program(source_definitions()["rsp"].replace("phase alpha;", "")))

    def test_symbolic_phases_are_not_assumed_real_or_positive(self):
        z = phase_symbol("alpha")
        self.assertIsInstance(z, UnitPhase)
        self.assertIsNone(z.is_real)
        self.assertEqual(sp.conjugate(z), 1/z)
        self.assertEqual(sp.simplify(z*sp.conjugate(z)), 1)
        # This can be negative on the unit circle (take z=-1). It must not pass.
        self.assertIsNone(psd(sp.ImmutableMatrix([[z + 1/z]])))

    def test_undeclared_free_symbols_are_not_accepted_as_phases(self):
        backend = program(source_definitions()["rsp"])._lower()
        with self.assertRaises(Unsupported):
            Effect.constant(sp.diag(1, 1, sp.Symbol("unknown"), 0)).validate(backend)

    def test_nonfinite_symbolic_effect_must_have_exact_bounds(self):
        z = phase_symbol("alpha")
        pure = projector(sp.Matrix([1,z])/sp.sqrt(2))
        self.assertIs(psd(pure), True)
        self.assertIs(psd(clean(sp.eye(2)-pure)), True)
        self.assertIs(psd(clean(-pure)), False)


class PhaseChoiceTests(unittest.TestCase):
    def test_both_scheduler_choices_satisfy_the_recorded_choice_specification(self):
        p = program(source_definitions()["phase_choice"])
        report = phase_check(p)
        self.assertEqual(p.name, "PhaseChoice")
        self.assertEqual(report.program, "PhaseChoice")
        self.assertTrue(report.verified, str(report))
        self.assertEqual(sum(o.name.startswith("Invariant preserved") for o in report.obligations), 2)

    def test_outputs_have_the_two_exact_fidelities_in_the_paper(self):
        backend = program(source_definitions()["phase_choice"])._lower()
        bell = projector(BELL)
        expected = (sp.Rational(9,10),sp.Rational(7,10))
        for (key, gate), fidelity in zip(backend.gate_families[0].cases, expected):
            output = embed(gate, (1,), 2)*bell*embed(gate, (1,), 2).H
            self.assertEqual(sp.simplify(sp.trace(bell*output)), fidelity)

    def test_a_single_fixed_output_does_not_cover_both_choices(self):
        report = phase_check(program(source_definitions()["phase_choice"]), post="U(0)[B] * Bell[A,B]")
        self.assertFalse(report.verified)
        self.assertTrue(any(o.status == "FAILED" for o in report.obligations))

    def test_nonunitary_gate_definition_is_rejected(self):
        source = source_definitions()["phase_choice"].replace("sqrt(1/10)*Z", "sqrt(2/10)*Z")
        with self.assertRaises(Unsupported):
            phase_check(program(source))

    def test_gate_selector_is_a_classical_input_dependency(self):
        p = program("""program SelectorDependency {
          gate U { 0: I; 1: X; }
          process P { qubit q; bit s; U(s)[q]; }
        }""")
        report = verify(p, pre=assertion("true", "Zero[q]"), post=assertion("true", "Zero[q]"))
        self.assertFalse(report.verified)
        self.assertEqual(report.obligations[0].witness["s"], 1)

    def test_missing_gate_case_is_incomplete_and_never_passes(self):
        p = program("""program MissingGateCase {
          gate U { 0: I; }
          process P { qubit q; bit s; U(s)[q]; }
        }""")
        report = verify(p, pre=assertion(), post=assertion())
        self.assertFalse(report.verified)
        self.assertEqual(report.obligations[0].status, "INCOMPLETE")

    def test_general_gate_powers_are_not_reduced_modulo_two(self):
        p = program("""program GatePower {
          gate S { 0: 1/2*I + i*sqrt(3)/2*Z; 1: 1/2*I + i*sqrt(3)/2*Z; }
          process P { qubit q; bit s; S(s)[q]; S(s)[q]; }
        }""")
        report = verify(p, pre=assertion("true", "Plus[q]"), post=assertion("true", "S(s)[q]^2 * Plus[q]"))
        self.assertTrue(report.verified, str(report))

    def test_algebraically_equal_hermitian_entries_are_not_rejected(self):
        gate = _matrix_literal("sqrt(9/10)*I + i*sqrt(1/10)*Z")
        u = embed(gate,(1,),2)
        p = clean(u*projector(BELL)*u.H)
        self.assertIs(psd(p), True)
        self.assertIs(psd(clean(sp.eye(4)-p)), True)

    def test_gate_matrix_parser_never_executes_arbitrary_calls(self):
        with self.assertRaises(SourceError):
            _matrix_literal('__import__("os").getcwd()')
        with self.assertRaises(SourceError):
            _matrix_literal('sqrt(0.9)*I')


class RetryControlTraceTests(unittest.TestCase):
    def test_the_displayed_loop_retries_once_then_accepts(self):
        story = trace_retry(program(source_definitions()["distill"]), [(0,1),(1,1)])
        self.assertEqual(story.final_state["kA"], 1)
        self.assertEqual(story.final_state["kB"], 1)
        self.assertTrue(story.final_state["doneA"] and story.final_state["doneB"])
        self.assertIn("Attempt 0", str(story))
        self.assertIn("Attempt 1", str(story))
        self.assertIn("Recorded bits differ", str(story))
        self.assertIn("both loops exit", str(story))

    def test_trace_uses_actual_counter_updates_instead_of_a_canned_story(self):
        source = source_definitions()["distill"].replace("kA + 1", "kA + 2").replace("kB + 1", "kB + 2")
        with self.assertRaises(SourceError):
            trace_retry(program(source), [(0,1),(1,1)])

    def test_first_acceptance_can_happen_on_the_first_attempt(self):
        story = trace_retry(program(source_definitions()["distill"]), [(0,0)])
        self.assertEqual(story.final_state["kA"], 0)
        self.assertTrue(story.final_state["doneA"])

    def test_unfinished_story_is_not_presented_as_an_accepted_run(self):
        with self.assertRaises(SourceError):
            trace_retry(program(source_definitions()["distill"]), [(0,1)])

    def test_trace_distinguishes_physical_outcomes_from_postprocessed_records(self):
        source = source_definitions()["distill"].replace("mA := M[a_t[kA]];", "mA := M[a_t[kA]]; mA := 1-mA;")
        story = trace_retry(program(source), [(0,1),(1,1)])
        self.assertEqual(story.final_state["kA"], 0)
        self.assertIn("specified measurement outcomes Alice=0, Bob=1", str(story))
        self.assertIn("stored records mA=1, mB=1", str(story))

    def test_malformed_outcome_story_has_a_source_error(self):
        with self.assertRaises(SourceError):
            trace_retry(program(source_definitions()["distill"]), [1])


if __name__ == "__main__":
    unittest.main()
