"""Hoare-ordered source API, including checked unbounded specifications."""

import ast
import json
from pathlib import Path
import unittest

import sympy as sp

from verilocq import assertion, program, verify, SourceError


def definitions():
    notebook = json.loads((Path(__file__).resolve().parents[1] / "Quickstart.ipynb").read_text())
    result = {}
    for cell in notebook["cells"]:
        if cell["cell_type"] != "code":
            continue
        for node in ast.walk(ast.parse("".join(cell["source"]))):
            if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Call)
                    and isinstance(node.value.func, ast.Name) and node.value.func.id == "program"
                    and isinstance(node.value.args[0], ast.Constant)):
                result[node.targets[0].id] = node.value.args[0].value
    return result


THETA = """kA=kB and (doneA <=> doneB)
and (sentA <=> recvB) and (sentB <=> recvA)
and (recvA => rA=mB) and (recvB => rB=mA)
and (doneA <=> (sentA and recvA)) and (doneA => mA=mB)"""
RANK = "2*(n-kA)-[sentA]-[recvA]"
ACC = "doneA and doneB and kA=kB and kA<n"


def retry_triple(protocol, kind="good", post_classical=ACC):
    target = "I" if kind == "pass" else "Bell[a_c[kA],b_c[kB]]"
    return verify(f"{{ true ; E_{kind}(0,n) }}", protocol, f"{{ {post_classical} ; {target} }}",
                  invariant=assertion(THETA, f"K_{kind}(kA,mA,mB,n)"), decreases=RANK)


class HoareSyntaxTests(unittest.TestCase):
    def setUp(self):
        self.p = program("program HTest { process P { qubit q; H[q]; } }")

    def test_positional_assertions_wrap_the_program(self):
        report = verify("{ true ; Zero[q] }", self.p, "{ true ; Plus[q] }")
        self.assertTrue(report.verified)
        self.assertEqual(str(report).splitlines()[:3], ["{ true ; Zero[q] }", "HTest", "{ true ; Plus[q] }"])

    def test_braced_assertions_preserve_both_parts(self):
        a = assertion("{ p=0 and not done ; Bell[A,B] }")
        self.assertEqual(a.classical, "p=0 and not done")
        self.assertEqual(a.quantum, "Bell[A,B]")

    def test_malformed_assertions_are_not_silently_interpreted(self):
        for source in ("{ true }", "{ true ; I ; I }", "{ ; I }", "{ true ; }", "{ true ; I"):
            with self.subTest(source=source), self.assertRaises(SourceError):
                assertion(source)

    def test_legacy_keyword_spelling_has_the_same_semantics(self):
        positional = verify("{ true ; Zero[q] }", self.p, "{ true ; Plus[q] }")
        legacy = verify(self.p, pre=assertion("true", "Zero[q]"), post=assertion("true", "Plus[q]"))
        self.assertEqual(positional.verified, legacy.verified)
        self.assertEqual([c.status for c in positional.obligations], [c.status for c in legacy.obligations])

    def test_fully_keyword_legacy_call_remains_supported(self):
        report = verify(protocol=self.p, pre=assertion("true", "Zero[q]"), post=assertion("true", "Plus[q]"))
        self.assertTrue(report.verified)

    def test_wrong_postcondition_fails_in_hoare_order(self):
        report = verify("{ true ; Zero[q] }", self.p, "{ true ; Zero[q] }")
        self.assertFalse(report.verified)
        self.assertEqual(report.obligations[0].status, "FAILED")

    def test_mixed_argument_styles_are_rejected(self):
        with self.assertRaises(SourceError):
            verify("{ true ; I }", self.p, "{ true ; I }", pre=assertion())

    def test_notebook_representation_is_concise_and_details_are_available(self):
        report = verify("{ true ; Zero[q] }", self.p, "{ true ; Plus[q] }")
        self.assertNotIn("obligations=", repr(report))
        self.assertNotIn("<table", report._repr_html_())
        self.assertIn("Local Hoare triple", report.details())


class UnboundedHoareTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = definitions()["distill"]
        cls.protocol = program(cls.source)

    def test_both_paper_triples_use_the_same_public_api(self):
        for kind in ("pass", "good"):
            report = retry_triple(self.protocol, kind)
            self.assertTrue(report.verified, report.details())
            self.assertIn(f"E_{kind}(0,n)", str(report))
            self.assertIn("every finite n", report.mode)

    def test_requested_classical_postcondition_is_actually_checked(self):
        report = retry_triple(self.protocol, post_classical=ACC + " and kA<0")
        self.assertFalse(report.verified)
        self.assertEqual(report.obligations[-1].status, "FAILED")

    def test_an_unsupported_quantum_goal_is_not_reported_as_verified(self):
        with self.assertRaises(SourceError):
            verify("{ true ; E_good(0,n) }", self.protocol, "{ true ; I }",
                   invariant=assertion(THETA, "K_good(kA,mA,mB,n)"), decreases=RANK)

    def test_wrong_invariant_family_is_not_ignored(self):
        with self.assertRaises(SourceError):
            verify("{ true ; E_good(0,n) }", self.protocol, f"{{ {ACC} ; Bell[a_c[kA],b_c[kB]] }}",
                   invariant=assertion(THETA, "K_pass(kA,mA,mB,n)"), decreases=RANK)

    def test_unknown_precondition_effect_is_rejected(self):
        with self.assertRaises(SourceError):
            verify("{ true ; E_fake(0,n) }", self.protocol, "{ true ; I }",
                   invariant=assertion(THETA, "K_pass(kA,mA,mB,n)"), decreases=RANK)

    def test_whitespace_cannot_turn_a_malformed_identifier_into_an_effect(self):
        with self.assertRaises(SourceError):
            verify("{ true ; E_pa ss(0,n) }", self.protocol, "{ true ; I }",
                   invariant=assertion(THETA, "K_pass(kA,mA,mB,n)"), decreases=RANK)

    def test_quantum_program_mutation_still_fails(self):
        changed = program(self.source.replace("CNOT[a_c[kA],a_t[kA]];", "skip;"))
        report = retry_triple(changed)
        self.assertFalse(report.verified)
        with self.assertRaises(SourceError):
            report.bounds()

    def test_bounds_are_verified_results_with_induction_evidence(self):
        report = retry_triple(self.protocol)
        bounds = report.bounds(fidelity="4/5", attempts=5)
        self.assertTrue(bounds.verified)
        self.assertEqual(bounds.values["accepted_mass_lower_bound"], 1-sp.Rational(52,225)**5)
        self.assertEqual(bounds.values["asymptotic_fidelity"], sp.Rational(145,173))
        required = {"Probability formulas have the zero-horizon base case",
                    "Geometric acceptance formula satisfies the recurrence",
                    "Geometric good-mass formula satisfies the recurrence",
                    "The rejection factor satisfies the geometric-limit hypothesis",
                    "Apply the geometric-limit rule"}
        self.assertTrue(required <= {c.name for c in bounds.evidence.obligations if c.status == "PASSED"})
        self.assertIn("independent Werner pairs", str(bounds))
        self.assertNotIn("Optional", str(bounds))

    def test_bounds_do_not_follow_from_a_failed_requested_triple(self):
        failed = retry_triple(self.protocol, post_classical="false")
        self.assertFalse(failed.verified)
        with self.assertRaises(SourceError):
            failed.bounds()

    def test_finite_protocol_does_not_claim_the_distillation_bound(self):
        p = program("program P { process Alice { qubit q; skip; } }")
        report = verify("{ true ; I }", p, "{ true ; I }")
        with self.assertRaises(SourceError):
            report.bounds()


if __name__ == "__main__":
    unittest.main()
