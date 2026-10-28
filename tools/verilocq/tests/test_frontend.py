"""Source-level semantics, diagnostics, and the self-contained Notebook contract."""

import ast
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import unittest

from verilocq import SourceError, Unsupported, assertion, program, verify, first_acceptance


ROOT = Path(__file__).resolve().parents[1]


def notebook_cells():
    notebook = json.loads((ROOT / "Quickstart.ipynb").read_text())
    return ["".join(c["source"]) for c in notebook["cells"] if c["cell_type"] == "code"]


def notebook_programs():
    result = {}
    for source in notebook_cells():
        for node in ast.walk(ast.parse(source)):
            if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Call)
                    and isinstance(node.value.func, ast.Name) and node.value.func.id == "program"
                    and node.value.args and isinstance(node.value.args[0], ast.Constant)):
                result[node.targets[0].id] = node.value.args[0].value
    return result


class SourceFrontendTests(unittest.TestCase):
    def local(self, body, declarations="bit m;"):
        return program(f"program Local {{ process P {{ qubit q; {declarations} {body} }} }}")

    def test_source_assignment_and_wrong_postcondition(self):
        p = self.local("x := x+1;", "int x in 0..2;")
        pre = assertion("0 <= x and x <= 1")
        self.assertTrue(verify(p, pre=pre, post=assertion("x >= 1")).verified)
        self.assertFalse(verify(p, pre=pre, post=assertion("x = 2")).verified)

    def test_negative_integer_domains(self):
        p = self.local("x := -x;", "int x in -1..1;")
        self.assertTrue(verify(p, pre=assertion("x = -1"), post=assertion("x = 1")).verified)

    def test_boolean_not_precedence_and_indicators(self):
        p = self.local("x := [not (x = 0)];", "int x in 0..2;")
        self.assertTrue(verify(p, pre=assertion("x = 2"), post=assertion("x = 1")).verified)

    def test_classical_equivalence_and_implication(self):
        p = self.local("m := 1;", "bit m; bool b;")
        self.assertTrue(verify(p, pre=assertion("b <=> true"), post=assertion("b => m = 1")).verified)

    def test_gate_and_state_notation(self):
        p = self.local("H[q];")
        self.assertTrue(verify(p, pre=assertion("true", "Zero[q]"), post=assertion("true", "Plus[q]")).verified)

    def test_measurement_and_conditional_correction(self):
        p = self.local("m := M[q]; if m = 1 then X[q]; else skip; fi;")
        self.assertTrue(verify(p, pre=assertion(), post=assertion("true", "Zero[q]")).verified)

    def test_measurement_dependent_quantum_predicate(self):
        p = self.local("m := M[q];")
        self.assertTrue(verify(p, pre=assertion(), post=assertion("true", "X[q]^m * Zero[q]")).verified)

    def test_unitary_composition_order_is_preserved(self):
        p = self.local("X[q]; H[q];")
        pre = assertion("true", "Zero[q]")
        self.assertTrue(verify(p, pre=pre, post=assertion("true", "H[q] * X[q] * Zero[q]")).verified)
        self.assertFalse(verify(p, pre=pre, post=assertion("true", "X[q] * H[q] * Zero[q]")).verified)

    def test_reset_uses_the_same_source_language(self):
        self.assertTrue(verify(self.local("q := |0>;"), pre=assertion(), post=assertion("true", "Zero[q]")).verified)

    def test_unknown_variable_is_a_source_error(self):
        with self.assertRaises(SourceError):
            verify(self.local("m := missing;"), pre=assertion(), post=assertion())

    def test_invalid_program_reports_source_location(self):
        with self.assertRaisesRegex(SourceError, "line .*column"):
            program("program Broken { process P { qubit q; if true then skip; } }")

    def test_displayed_source_cannot_diverge_from_parsed_program(self):
        p = self.local("skip;")
        with self.assertRaises(AttributeError):
            p.source = p.source.replace("skip;", "X[q];")

    def test_keywords_cannot_shadow_boolean_literals(self):
        with self.assertRaises(SourceError):
            self.local("skip;", "bit true;")

    def test_parallel_separator_is_required(self):
        with self.assertRaises(SourceError):
            program("program Bad { process P { qubit p; } process Q { qubit q; } }")

    def test_assertion_does_not_execute_python(self):
        output = io.StringIO()
        with redirect_stdout(output), self.assertRaises(SourceError):
            verify(self.local("skip;"), pre=assertion("true", '__import__("builtins").print("executed")'), post=assertion())
        self.assertEqual(output.getvalue(), "")

    def test_predicates_cannot_silently_overlap(self):
        with self.assertRaises(SourceError):
            verify(self.local("skip;"), pre=assertion("true", "Zero[q] * Plus[q]"), post=assertion())

    def test_unknown_quantum_register_is_rejected(self):
        with self.assertRaises(SourceError):
            verify(self.local("skip;"), pre=assertion("true", "Zero[unknown]"), post=assertion())

    def test_reference_remains_read_only_through_frontend(self):
        p = program("program Invalid { reference R; process P { qubit q; X[R]; } }")
        with self.assertRaises(Unsupported):
            verify(p, pre=assertion(), post=assertion())

    def test_guarded_source_requires_an_invariant(self):
        p = program(notebook_programs()["tele"])
        with self.assertRaisesRegex(SourceError, "invariant"):
            verify(p, pre=assertion(), post=assertion())

    def test_bad_fresh_array_index_is_not_ignored(self):
        source = notebook_programs()["distill"].replace("a_c[kA]", "a_c[kA+1]")
        proof = first_acceptance(program(source), invariant="true", decreases="n-kA")
        with self.assertRaisesRegex(SourceError, "current counter"):
            proof.verify()

    def test_mutating_source_changes_the_retry_result(self):
        source = notebook_programs()["distill"].replace("CNOT[a_c[kA],a_t[kA]];", "skip;")
        proof = first_acceptance(program(source), invariant="true", decreases="n-kA")
        self.assertFalse(proof.verify().verified)


class NotebookInterfaceTests(unittest.TestCase):
    def test_all_programs_are_defined_in_cells_and_backend_objects_are_hidden(self):
        self.assertTrue({"rsp", "bad_rsp", "phase_choice", "tele", "swap", "cnot", "distill"} <= notebook_programs().keys())
        for source in notebook_cells():
            tree = ast.parse(source)
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    self.assertTrue(all(alias.name not in {"z3", "sympy"} for alias in node.names))
                if isinstance(node, ast.ImportFrom):
                    self.assertNotIn(node.module, {"z3", "sympy", "verilocq.examples", "verilocq.distillation"})
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                    self.assertNotIn(node.func.id, {"teleportation", "entanglement_swapping", "remote_cnot", "distillation"})

    def test_complete_notebook_uses_source_definitions_successfully(self):
        context = {}
        with redirect_stdout(io.StringIO()):
            for index, source in enumerate(notebook_cells()):
                exec(compile(source, f"Notebook cell {index}", "exec"), context)
        for name in ("rsp_report", "phase_report", "tele_report", "swap_report", "cnot_report", "distill_pass", "distill_good", "distill_bounds"):
            self.assertTrue(context[name].verified)
        self.assertFalse(context["bad_rsp_report"].verified)

    def test_first_protocol_is_rsp_and_old_abstract_demos_are_removed(self):
        sources = notebook_cells()
        defined = list(notebook_programs())
        self.assertEqual(defined[0], "rsp")
        self.assertNotIn("increment", defined)
        self.assertNotIn("max_states", "\n".join(sources))

    def test_notebook_uses_hoare_order_and_phase_choice_is_the_last_case(self):
        self.assertEqual(list(notebook_programs()), ["rsp", "bad_rsp", "tele", "swap", "cnot", "distill", "phase_choice"])
        notebook = json.loads((ROOT / "Quickstart.ipynb").read_text())
        text = "\n".join("".join(c["source"]) for c in notebook["cells"])
        self.assertNotIn("Optional", text)
        self.assertNotIn("Select **", text)
        self.assertNotIn("what probability bounds say", text.lower())
        for source in notebook_cells():
            for node in ast.walk(ast.parse(source)):
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "verify":
                    self.assertEqual(len(node.args), 3)
                    self.assertTrue(isinstance(node.args[0], ast.Constant) and node.args[0].value.startswith("{"))
                    self.assertTrue(isinstance(node.args[2], ast.Constant) and node.args[2].value.startswith("{"))
                    self.assertFalse({k.arg for k in node.keywords} & {"pre", "post"})


if __name__ == "__main__":
    unittest.main()
