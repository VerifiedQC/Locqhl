"""Proof certificates: one JSON record of the derivation behind every report."""

import ast
import json
from pathlib import Path
import tempfile
import unittest

from verilocq import assertion, program, verify
from verilocq.certificate import FORMAT


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


THETA = """kA=kB and (doneA <=> doneB)
and (sentA <=> recvB) and (sentB <=> recvA)
and (recvA => rA=mB) and (recvB => rB=mA)
and (doneA <=> (sentA and recvA)) and (doneA => mA=mB)"""


def notebook_reports():
    """The Notebook's verify calls, keyed by case name."""
    d = source_definitions()
    rsp_spec = dict(invariant="{ 0 <= alpha and alpha < 2*pi and (d <=> p=1) ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
                    decreases="1-[d]")
    return {
        "rsp": verify("{ 0 <= alpha and alpha < 2*pi ; Bell[A,B] }", program(d["rsp"]),
                      "{ 0 <= alpha and alpha < 2*pi ; Equator(alpha)[B] }", **rsp_spec),
        "teleportation": verify("{ true ; rho(psi)[A1] * Bell[A2,B] }", program(d["tele"]), "{ true ; rho(psi)[B] }",
                                invariant="""{ pA=pB and dAz=dBz and dAx=dBx and ((pB=1) <=> (dBz and dBx))
                                              and (dBz => i=m1) and (dBx => j=m2)
                                              ; X[B]^((1-pB)*m2) * Z[B]^((1-pB)*m1) * rho(psi)[B] }""",
                                decreases="2-[dAz]-[dAx]"),
        "swapping": verify("{ true ; Bell[A,CA] * Bell[B,CB] }", program(d["swap"]), "{ true ; Bell[A,B] }",
                           invariant="""{ (dCA <=> pA=1) and (dCB <=> pB=1) and (pA=1 => i=m1) and (pB=1 => j=m2)
                                         ; X[B]^((1-pB)*m2) * Z[A]^((1-pA)*m1) * Bell[A,B] }""",
                           decreases="2-[dCA]-[dCB]"),
        "remote-cnot": verify("{ true ; Bell[A,B] * rho(psi)[C,T] }", program(d["cnot"]), "{ true ; CNOT[C,T] * rho(psi)[C,T] }",
                              invariant="""{ (dA <=> pB=1) and (dB <=> pA=1)
                                            ; X[T]^((1-pB)*m1) * Z[C]^((1-pA)*m2) * CNOT[C,T] * rho(psi)[C,T] }""",
                              decreases="2-[dA]-[dB]"),
        "phase-choice": verify("{ true ; Bell[A,B] }", program(d["phase_choice"]), "{ true ; U(s)[B] * Bell[A,B] }",
                               invariant="{ a <=> b ; U(s)[B]^[a] * Bell[A,B] }", decreases="1-[a]"),
        "distillation": verify("{ true ; E_good(0,n) }", program(d["distill"]),
                               "{ doneA and doneB and kA=kB and kA<n ; Bell[a_c[kA],b_c[kB]] }",
                               invariant=assertion(f"({THETA}) and kA<n", "K_good(kA,mA,mB,n)"),
                               decreases="2*(n-kA)-[sentA]-[recvA]"),
    }


def wp_nodes(node):
    count = 1
    for key in ("after", "then", "else"):
        if key in node:
            count += wp_nodes(node[key])
    return count


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reports = notebook_reports()
        cls.certificates = {name: report.certificate() for name, report in cls.reports.items()}

    def test_every_protocol_has_a_serializable_distributed_tot_certificate(self):
        for name, certificate in self.certificates.items():
            with self.subTest(case=name):
                report = self.reports[name]
                self.assertTrue(report.verified, report.details())
                text = json.dumps(certificate)
                self.assertEqual(json.loads(text), certificate)
                self.assertEqual(certificate["format"], FORMAT)
                self.assertEqual(certificate["rule"], "Distributed-tot")
                self.assertEqual(certificate["tool"]["verdict"], "VERIFIED")
                self.assertEqual(certificate["tool"]["mode"], report.mode)
                self.assertEqual(certificate["program"]["name"], report.program)
                self.assertIn("process", certificate["program"]["source"])

    def test_one_premise_per_obligation_in_order(self):
        for name, certificate in self.certificates.items():
            with self.subTest(case=name):
                obligations = self.reports[name].obligations
                premises = certificate["premises"]
                self.assertEqual([p["name"] for p in premises], [o.name for o in obligations])
                self.assertEqual([p["status"] for p in premises], [o.status for o in obligations])
                self.assertEqual([p["id"] for p in premises], [f"p{i}" for i in range(1, len(obligations) + 1)])

    def test_finite_premises_name_the_paper_rule_premises(self):
        for name in ("rsp", "teleportation", "swapping", "remote-cnot", "phase-choice"):
            with self.subTest(case=name):
                premises = self.certificates[name]["premises"]
                kinds = [p["premise"] for p in premises]
                self.assertEqual(kinds[0], "initialization")
                self.assertIn("exit_classical", kinds)
                self.assertIn("exit_quantum", kinds)
                self.assertIn("ranking_nonnegative", kinds)
                self.assertIn("no_deadlock", kinds)
                pairs = [p["label"] for p in self.certificates[name]["program"]["pairs"]]
                self.assertTrue(pairs)
                self.assertEqual([p["pair"] for p in premises if p["premise"] == "invariant_preserved"], pairs)
                self.assertEqual([p["pair"] for p in premises if p["premise"] == "ranking_decreases"], pairs)
                for p in premises:
                    self.assertIn(p["evidence"]["kind"], ("local", "implication"))
                    self.assertIsNotNone(p["statement"])

    def test_every_local_premise_has_a_derivation_tree_and_a_loewner_side_condition(self):
        found = 0
        for name, certificate in self.certificates.items():
            for premise in certificate["premises"]:
                if premise["evidence"]["kind"] != "local":
                    continue
                found += 1
                with self.subTest(case=name, premise=premise["name"]):
                    derivation = premise["evidence"]["derivation"]
                    self.assertEqual(derivation["rule"], "Conseq")
                    self.assertGreaterEqual(wp_nodes(derivation["premise"]), 1)
                    side = derivation["side_condition"]
                    self.assertEqual(side["kind"], "loewner")
                    self.assertTrue(side["exhaustive"])
                    self.assertGreaterEqual(len(side["states"]), 1)
                    self.assertEqual(side["summary"]["states"], len(side["states"]))
                    self.assertEqual(side["summary"]["checked_cases"], premise["cases"])
                    matrices = certificate["matrices"]
                    for record in side["states"]:
                        self.assertIs(record["decision"], True)
                        for key in ("pre", "wlp", "residual"):
                            self.assertIn("entries", matrices[record[key]])
                    self.assertEqual(premise["statement"]["kind"], "triple")
                    block = premise["statement"]["block"]["ast"]
                    root = derivation["premise"]
                    if block:
                        self.assertEqual(root["command"], block[0])
                        self.assertGreater(wp_nodes(root), len(block))
                    else:
                        self.assertEqual(root["rule"], "Target")
        self.assertGreater(found, 0)

    def test_classical_premises_record_the_smt_query(self):
        for name, certificate in self.certificates.items():
            for premise in certificate["premises"]:
                if premise["evidence"]["kind"] != "implication":
                    continue
                with self.subTest(case=name, premise=premise["name"]):
                    self.assertEqual(premise["evidence"]["result"], "unsat")
                    self.assertIn("(not", premise["evidence"]["query"]["smtlib"])
                    self.assertEqual(premise["statement"]["kind"], "implication")
                    self.assertIn("smtlib", premise["statement"]["hypothesis"])

    def test_symbolic_states_and_phases_stay_symbolic(self):
        teleportation = self.certificates["teleportation"]
        self.assertEqual([s["parameter"] for s in teleportation["symbols"]], ["psi"])
        self.assertTrue(any("state_psi_theta" in m["symbols"] for m in teleportation["matrices"]))
        rsp = self.certificates["rsp"]
        self.assertEqual(rsp["symbols"][0]["symbol"], "phase_alpha")
        self.assertTrue(any("phase_alpha" in m["symbols"] for m in rsp["matrices"]))
        invariant = rsp["specification"]["invariant"]["quantum"]
        self.assertEqual(invariant["syntax"]["kind"], "product")
        self.assertEqual(invariant["syntax"]["left"]["kind"], "power")

    def test_distillation_exports_the_indexed_kernel_and_hoare_proofs(self):
        certificate = self.certificates["distillation"]
        kinds = {p["evidence"]["kind"] for p in certificate["premises"]}
        self.assertTrue({"indexed_induction", "indexed_equality", "hoare_proof", "matrix_equality", "text"} <= kinds)
        induction = next(p for p in certificate["premises"] if p["evidence"]["kind"] == "indexed_induction")["evidence"]
        self.assertEqual(induction["proof"]["kind"], "induction")
        self.assertIn("hypothesis", induction["proof"]["scheme"])
        self.assertEqual(induction["proof"]["step"]["rule"], "Trans")
        self.assertTrue(induction["families"])
        hoare = next(p for p in certificate["premises"] if p["evidence"]["kind"] == "hoare_proof")["evidence"]
        rules = {step["rule"] for step in hoare["steps"]}
        self.assertTrue({"Distributed-tot", "Conseq", "Seq", "Assign", "Unitary", "Meas", "Branch-Accum"} <= rules)
        root = next(step for step in hoare["steps"] if step["id"] == hoare["root"])
        self.assertEqual(root["rule"], "Conseq")
        self.assertEqual(hoare["formulas"][root["pre"]["quantum"]]["kind"], "indexed")
        self.assertEqual(len(certificate["specification"]["hoare_triples"]), 2)
        self.assertEqual(len(certificate["groups"]), 5)
        self.assertEqual(certificate["program"]["variables"][0]["kind"], "nat")

    def test_wrong_specifications_yield_failed_premises_with_witnesses(self):
        d = source_definitions()
        spec = dict(invariant="{ 0 <= alpha and alpha < 2*pi and (d <=> p=1) ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
                    decreases="1-[d]")
        report = verify("{ 0 <= alpha and alpha < 2*pi ; Bell[A,B] }", program(d["bad_rsp"]),
                        "{ 0 <= alpha and alpha < 2*pi ; Equator(alpha)[B] }", **spec)
        certificate = report.certificate()
        json.dumps(certificate)
        self.assertEqual(certificate["tool"]["verdict"], "NOT_VERIFIED")
        failed = [p for p in certificate["premises"] if p["status"] == "FAILED"]
        self.assertEqual([p["premise"] for p in failed], ["invariant_preserved"])
        self.assertEqual(failed[0]["witness"]["m"], 1)
        states = failed[0]["evidence"]["derivation"]["side_condition"]["states"]
        self.assertIs(states[-1]["decision"], False)
        self.assertEqual(states[-1]["state"], failed[0]["witness"])
        self.assertFalse(failed[0]["evidence"]["derivation"]["side_condition"]["exhaustive"])

        report = verify("{ 0 <= alpha and alpha < 2*pi ; Bell[A,B] }", program(d["rsp"]),
                        "{ 0 <= alpha and alpha < 2*pi and m = 0 ; Equator(alpha)[B] }", **spec)
        certificate = report.certificate()
        json.dumps(certificate)
        failed = next(p for p in certificate["premises"] if p["premise"] == "exit_classical")
        self.assertEqual(failed["status"], "FAILED")
        self.assertEqual(failed["evidence"]["result"], "sat")
        self.assertEqual(failed["witness"]["m"], "1")

    def test_loop_free_programs_have_a_local_conseq_certificate(self):
        p = program("program HTest { process P { qubit q; H[q]; } }")
        certificate = verify("{ true ; Zero[q] }", p, "{ true ; Plus[q] }").certificate()
        self.assertEqual(certificate["rule"], "Local WP / Conseq")
        self.assertEqual([x["premise"] for x in certificate["premises"]], ["local_triple"])
        self.assertIsNone(certificate["specification"]["invariant"])

    def test_save_certificate_writes_the_same_document(self):
        report = self.reports["rsp"]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "rsp.json"
            report.save_certificate(path)
            saved = json.loads(path.read_text(encoding="utf-8"))
        rebuilt = report.certificate()
        for document in (saved, rebuilt):
            document["tool"].pop("timestamp")
        self.assertEqual(saved, rebuilt)


if __name__ == "__main__":
    unittest.main()
