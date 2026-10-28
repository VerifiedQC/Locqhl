"""Executable WP trace cross-checks against the independent Kraus interpreter."""

import ast
from itertools import product
import json
from pathlib import Path
import unittest

import sympy as sp

from verilocq import assertion, program, verify, Unsupported
from verilocq.derivation import LocalEvidence, build_wp
from verilocq.quantum import clean
from verilocq.verifier import execute


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


def forward_wp(backend, block, post, state, limit=256):
    result = sp.zeros(2 ** len(backend.registers))
    for output, kraus in execute(backend, block, state, limit):
        result += kraus.H * post.at(output, backend) * kraus
    return clean(result)


class ExecutableWPTests(unittest.TestCase):
    def test_every_transformer_agrees_with_independent_forward_semantics(self):
        p = program("""program AllTransformers {
          gate U { 0: I; 1: H; 2: Z; }
          process P {
            qubits q,r;
            phase alpha;
            int x in 0..2;
            bit m;
            bool flag;
            R(alpha)[q];
            U(x)[r];
            H[q];
            CNOT[q,r];
            m := M[q];
            if m=1 then
              x := (x+1)%3;
              r := |0>;
            else
              X[r];
              m := M[r];
            fi;
            flag := (m=1);
            skip;
          }
        }""")
        backend = p._lower()
        post = assertion("flag or x=2", "R(alpha)[q] * Bell[q,r]")._compile(backend)
        node = build_wp(backend, backend.initialization, post)
        self.assertEqual(set(node.rules()), {"Unitary", "Meas", "If", "Assign", "Init", "Skip"})
        for x, m, flag in product((0, 1, 2), (0, 1), (False, True)):
            state = {"x": x, "m": m, "flag": flag}
            calculated = node.evaluate(backend, state)
            independent = forward_wp(backend, backend.initialization, post, state)
            self.assertIs(clean(calculated-independent).is_zero_matrix, True)

    def test_measurement_path_budget_is_enforced_by_the_wp_tree(self):
        p = program("program P { process A { qubit q; bit m; m:=M[q]; q:=|0>; } }")
        backend = p._lower()
        post = assertion()._compile(backend)
        tree = build_wp(backend, backend.initialization, post)
        with self.assertRaises(Unsupported):
            tree.evaluate(backend, {"m": 0}, max_paths=1)
        with self.assertRaises(Unsupported):
            forward_wp(backend, backend.initialization, post, {"m": 0}, limit=1)

    def test_wp_evaluation_does_not_mutate_its_input_state(self):
        p = program("program P { process A { qubit q; bit m; m:=M[q]; } }")
        backend = p._lower()
        post = assertion("m=1")._compile(backend)
        state = {"m": 0}
        build_wp(backend, backend.initialization, post).evaluate(backend, state)
        self.assertEqual(state, {"m": 0})

    def test_measurement_logical_names_are_fresh(self):
        p = program("program P { process A { qubit q; bit outcome_0,m; m:=M[q]; } }")
        backend = p._lower()
        tree = build_wp(backend, backend.initialization, assertion()._compile(backend))
        self.assertNotIn(tree.outcome, backend.varmap)
        self.assertIn("is fresh", tree.explain())

    def test_long_command_chain_is_incomplete_instead_of_recursing_out(self):
        p = program("program Long { process P { qubit q; " + "skip;"*1200 + " } }")
        report = verify("{ true ; I }", p, "{ true ; I }")
        self.assertFalse(report.verified)
        self.assertEqual(report.obligations[0].status, "INCOMPLETE")
        self.assertIn("depth limit", str(report.explain()))

    def test_deep_conditional_construction_has_an_explicit_budget(self):
        body = "if true then "*270 + "skip;" + " fi;"*270
        p = program("program Nested { process P { qubit q; " + body + " } }")
        report = verify("{ true ; I }", p, "{ true ; I }")
        self.assertFalse(report.verified)
        self.assertIn("nesting limit", str(report.explain()))

    def test_empty_and_conditional_blocks_have_resolvable_predicate_names(self):
        for body in ("", "if m=1 then skip; else skip; fi;"):
            p = program(f"program P {{ process A {{ qubit q; bit m; {body} }} }}")
            report = verify("{ true ; I }", p, "{ true ; I }")
            self.assertTrue(report.verified)
            self.assertIn("Q(sigma)", str(report.explain()))


class ProofExplanationTests(unittest.TestCase):
    def rsp(self, name="rsp"):
        return verify("{ true ; Bell[A,B] }", program(source_definitions()[name]),
                      "{ true ; Equator(alpha)[B] }",
                      invariant="{ d <=> p=1 ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
                      decreases="1-[d]")

    def test_rsp_exposes_actual_rule_steps_and_smt_conditions(self):
        report = self.rsp()
        explanation = str(report.explain())
        for text in ("Distributed-tot", "[Unitary WP]", "[Meas WP]", "[Assign WP]", "[If WP]",
                     "Branch-Accum", "Conseq side condition", "Z3 checks the negation"):
            self.assertIn(text, explanation)
        self.assertNotIn("And(", explanation)

    def test_recorded_effects_are_the_wp_computed_by_the_displayed_tree(self):
        report = self.rsp()
        for obligation in report.obligations:
            evidence = obligation.evidence
            if isinstance(evidence, LocalEvidence) and evidence.sample is not None:
                sample = evidence.sample
                reconstructed = evidence.wp.evaluate(evidence.program, sample["state"])
                self.assertIs(clean(reconstructed-sample["wp"]).is_zero_matrix, True)

    def test_failed_rule_premise_is_not_presented_as_a_successful_proof(self):
        report = self.rsp("bad_rsp")
        self.assertFalse(report.verified)
        explanation = str(report.explain(matrices=True))
        self.assertIn("[FAILED]", explanation)
        self.assertIn("Residual wp - pre", explanation)
        self.assertIn("'m': 1", explanation)

    def test_incomplete_evaluation_displays_the_actual_reason(self):
        p = program("program P { process A { qubit q; bit m; m:=M[q]; } }")
        report = verify("{ true ; I }", p, "{ true ; I }", max_paths=1)
        self.assertFalse(report.verified)
        self.assertIn("path limit", str(report.explain()))
        self.assertIn("INCOMPLETE", str(report.explain()))
        self.assertEqual(report.obligations[0].cases, 0)
        self.assertEqual(report.obligations[0].evidence.checked_cases, 0)

    def test_incomplete_matrix_example_does_not_claim_full_coverage(self):
        p = program("program P { process A { qubit q; int x in 0..2; skip; } }")
        report = verify("{ true ; I }", p, "{ x>=0 ; I }", max_states=1)
        self.assertFalse(report.verified)
        self.assertEqual(report.obligations[0].cases, 1)
        self.assertEqual(report.obligations[0].evidence.checked_cases, 1)
        text = str(report.explain(matrices=True))
        self.assertIn("overall coverage depends on the obligation status", text)
        self.assertNotIn("coverage is the full case check", text)

    def test_vacuous_triple_explicitly_says_no_operator_evaluation_was_needed(self):
        p = program("program P { process A { qubit q; skip; } }")
        report = verify("{ false ; I }", p, "{ false ; I }")
        self.assertTrue(report.verified)
        self.assertEqual(report.obligations[0].cases, 0)
        self.assertIn("vacuous", str(report.explain()))

    def test_html_explanation_is_expandable_and_contains_no_table(self):
        html = self.rsp().explain()._repr_html_()
        self.assertIn("<details", html)
        self.assertIn("<summary>", html)
        self.assertNotIn("<table", html.lower())

    def test_distillation_replays_indexed_proofs_and_exact_local_identities(self):
        theta = """kA=kB and (doneA <=> doneB) and (sentA <=> recvB) and (sentB <=> recvA)
        and (recvA => rA=mB) and (recvB => rB=mA)
        and (doneA <=> (sentA and recvA)) and (doneA => mA=mB)"""
        report = verify("{ true ; E_good(0,n) }", program(source_definitions()["distill"]),
                        "{ doneA and doneB and kA=kB and kA<n ; Bell[a_c[kA],b_c[kB]] }",
                        invariant=assertion(theta, "K_good(kA,mA,mB,n)"),
                        decreases="2*(n-kA)-[sentA]-[recvA]")
        self.assertTrue(report.verified)
        explanation = str(report.explain())
        for text in ("[Interval-Induction]", "[Frame]", "[Sum-Head]", "sum_u T_uu^dagger T_uu = Pass",
                     "sum_u T_uu^dagger Bell_control T_uu = Good", "Assert-Eq", "Distributed-tot"):
            self.assertIn(text, explanation)
        bound = report.bounds()
        self.assertIn("limit lemma itself is trusted, not proved by Z3", str(bound.explain()))


if __name__ == "__main__":
    unittest.main()
