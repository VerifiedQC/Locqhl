"""The paper's guarded teleportation, with a read-only reference qubit.

The reference is a specification device: preserving a Bell pair with R proves
the induced channel is identity on arbitrary inputs, including entangled ones.
Alice and Bob never operate on R. The protocol's executable code otherwise
follows CSTele in ../case_study_guarded_programs.tex.
"""

from dataclasses import dataclass
from itertools import permutations, product

import sympy as sp
import z3

from .quantum import (Assertion, BELL, Effect, I2, X, Z, clean, embed,
                      evaluate, projector, tensor)
from .syntax import (Assign, Branch, Gate, If, Measure, Process, Program,
                     Receive, Send, Variable, seq, Unsupported, live_before, names)
from .verifier import (execute, verify_distributed, states, Report, check_hoare,
                       check_implication, classical_wp)


@dataclass
class CaseStudy:
    program: Program
    pre: Assertion
    invariant: Assertion
    post: Assertion
    variant: object
    symbols: dict

    def verify(self, **options):
        return verify_distributed(self.program, self.pre, self.invariant,
                                  self.post, variant=self.variant, **options)


def teleportation(omit_correction=None):
    """Build executable syntax and independent specifications, not a canned result."""
    if omit_correction not in (None, "X", "Z"):
        raise ValueError("omit_correction must be None, 'X' or 'Z'")
    variables = tuple(
        Variable(name, owner, domain)
        for owner, entries in (
            ("Alice", (("m1", (0, 1)), ("m2", (0, 1)), ("pA", (0, 1)),
                       ("dAz", (False, True)), ("dAx", (False, True)))),
            ("Bob", (("i", (0, 1)), ("j", (0, 1)), ("pB", (0, 1)),
                     ("dBz", (False, True)), ("dBx", (False, True)))),
        ) for name, domain in entries
    )
    v = {var.name: var.symbol for var in variables}
    alice_finish = seq(If(z3.And(v["dAz"], v["dAx"]), seq(Assign("pA", 1))))
    correction = []
    if omit_correction != "X":
        correction.append(If(v["j"] == 1, seq(Gate("X", ("B",)))))
    if omit_correction != "Z":
        correction.append(If(v["i"] == 1, seq(Gate("Z", ("B",)))))
    correction.append(Assign("pB", 1))
    bob_finish = seq(If(z3.And(v["dBz"], v["dBx"]), seq(*correction)))
    alice = Process("Alice", ("A1", "A2"), seq(
        Gate("CNOT", ("A1", "A2")), Gate("H", ("A1",)),
        Measure("m1", "A1"), Measure("m2", "A2"),
        Assign("pA", 0), Assign("dAz", False), Assign("dAx", False)), (
            Branch("send_z", z3.And(v["pA"] == 0, z3.Not(v["dAz"])),
                   Send("c_z", v["m1"]), seq(Assign("dAz", True), alice_finish)),
            Branch("send_x", z3.And(v["pA"] == 0, z3.Not(v["dAx"])),
                   Send("c_x", v["m2"]), seq(Assign("dAx", True), alice_finish)),
        ))
    bob = Process("Bob", ("B",), seq(
        Assign("pB", 0), Assign("dBz", False), Assign("dBx", False)), (
            Branch("receive_z", z3.And(v["pB"] == 0, z3.Not(v["dBz"])),
                   Receive("c_z", "i"), seq(Assign("dBz", True), bob_finish)),
            Branch("receive_x", z3.And(v["pB"] == 0, z3.Not(v["dBx"])),
                   Receive("c_x", "j"), seq(Assign("dBx", True), bob_finish)),
        ))
    suffix = "" if omit_correction is None else f" — missing {omit_correction} correction"
    program = Program("Guarded teleportation" + suffix, variables,
                      ("R", "A1", "A2", "B"), (alice, bob), references=("R",))
    theta = z3.And(
        v["pA"] == v["pB"], v["dAz"] == v["dBz"], v["dAx"] == v["dBx"],
        (v["pB"] == 1) == z3.And(v["dBz"], v["dBx"]),
        z3.Implies(v["dBz"], v["i"] == v["m1"]),
        z3.Implies(v["dBx"], v["j"] == v["m2"]),
    )
    target = embed(projector(BELL), (0, 3), 4)  # Bell_RB ⊗ I on Alice's qubits
    cases = []
    for u in (0, 1):
        for w in (0, 1):
            for done in (0, 1):
                local = (X if w and not done else I2) * (Z if u and not done else I2)
                operator = embed(sp.ImmutableMatrix(local), (3,), 4)
                guard = z3.And(v["m1"] == u, v["m2"] == w, v["pB"] == done)
                cases.append((guard, clean(operator * target * operator.H)))
    pre = Assertion(True, Effect.constant(projector(tensor(BELL, BELL)), "Bell_RA1 ⊗ Bell_A2B"))
    invariant = Assertion(theta, Effect("outcome-dependent Bell_RB invariant", tuple(cases)))
    post = Assertion(True, Effect.constant(target, "Bell_RB ⊗ I_A1A2"))
    variant = 2 - z3.If(v["dAz"], 1, 0) - z3.If(v["dAx"], 1, 0)
    return CaseStudy(program, pre, invariant, post, variant, v)


def audit_teleportation_orders(case):
    """Additional exact channel audit for this two-message example only.

    Enumerate both pair orders and all measurement outcomes. Derive effective
    2×2 Kraus maps from the input A1 to output B by tracing out R,A1,A2.
    Compare the resulting 4×4 channel matrix with identity on the full matrix
    space, which covers every input density operator, not selected test states.
    This is an example-specific audit, not the general distributed verifier.
    """
    program = case.program
    program.validate()
    pairs = list(program.matching_pairs())
    if len(pairs) != 2 or program.registers != ("R", "A1", "A2", "B"):
        raise Unsupported("Channel audit is specific to the two-message teleportation example")
    relevant = set()
    for ordering in permutations(pairs):
        live = names(program.termination)
        for _, guard, block in reversed(ordering):
            live = names(guard) | live_before(block, live)
        relevant |= live_before(program.initialization, live)
    # |0>_R ⊗ input_A1 ⊗ |Phi+>_A2B : C^2 -> C^16.
    isometry = tensor(sp.ImmutableMatrix([1, 0]), I2, BELL)
    records = []
    for initial in states(program, True, relevant):
        init_paths = execute(program, program.initialization, initial)
        for ordering in permutations(pairs):
            paths = init_paths
            for _, guard, block in ordering:
                next_paths = []
                for state, before in paths:
                    if not evaluate(guard, state, program):
                        raise Unsupported("The requested communication order is not enabled")
                    for output, after in execute(program, block, state):
                        next_paths.append((output, clean(after * before)))
                paths = next_paths
            channel = sp.zeros(4)
            completeness = sp.zeros(2)
            nonzero_maps = 0
            for state, kraus in paths:
                if not evaluate(program.termination, state, program):
                    raise Unsupported("Two communications did not terminate this example")
                output_map = clean(kraus * isometry)
                for environment in range(8):
                    effective = output_map.extract([2 * environment, 2 * environment + 1], [0, 1])
                    if effective.is_zero_matrix:
                        continue
                    nonzero_maps += 1
                    channel += tensor(effective.conjugate(), effective)
                    completeness += effective.H * effective
            records.append({
                "initial_classical": {name: initial[name] for name in sorted(relevant)},
                "order": " → ".join(label.split(" ↔ ")[0].split(".")[1] for label, _, _ in ordering),
                "measurement_paths": len(paths),
                "nonzero_kraus_maps": nonzero_maps,
                "trace_preserving": clean(completeness) == sp.eye(2),
                "identity_channel": clean(channel) == sp.eye(4),
                "channel_matrix": clean(channel),
            })
    return records


def entanglement_swapping(omit_correction=None):
    if omit_correction not in (None, "X", "Z"):
        raise ValueError("omit_correction must be None, 'X' or 'Z'")
    variables = tuple(Variable(name, owner, domain) for owner, entries in (
        ("Charlie", (("m1", (0, 1)), ("m2", (0, 1)),
                     ("dCA", (False, True)), ("dCB", (False, True)))),
        ("Alice", (("pA", (0, 1)), ("i", (0, 1)))),
        ("Bob", (("pB", (0, 1)), ("j", (0, 1)))),
    ) for name, domain in entries)
    v = {var.name: var.symbol for var in variables}
    charlie = Process("Charlie", ("CA", "CB"), seq(
        Gate("CNOT", ("CA", "CB")), Gate("H", ("CA",)),
        Measure("m1", "CA"), Measure("m2", "CB"),
        Assign("dCA", False), Assign("dCB", False)), (
            Branch("send_a", z3.Not(v["dCA"]), Send("c_A", v["m1"]), seq(Assign("dCA", True))),
            Branch("send_b", z3.Not(v["dCB"]), Send("c_B", v["m2"]), seq(Assign("dCB", True))),
        ))
    alice = Process("Alice", ("A",), seq(Assign("pA", 0)), (
        Branch("receive", v["pA"] == 0, Receive("c_A", "i"), seq(
            () if omit_correction == "Z" else If(v["i"] == 1, seq(Gate("Z", ("A",)))),
            Assign("pA", 1))),))
    bob = Process("Bob", ("B",), seq(Assign("pB", 0)), (
        Branch("receive", v["pB"] == 0, Receive("c_B", "j"), seq(
            () if omit_correction == "X" else If(v["j"] == 1, seq(Gate("X", ("B",)))),
            Assign("pB", 1))),))
    label = "Entanglement swapping" + (f" - missing {omit_correction}" if omit_correction else "")
    program = Program(label, variables, ("A", "CA", "CB", "B"), (charlie, alice, bob))
    theta = z3.And(v["dCA"] == (v["pA"] == 1), v["dCB"] == (v["pB"] == 1),
                   z3.Implies(v["pA"] == 1, v["i"] == v["m1"]),
                   z3.Implies(v["pB"] == 1, v["j"] == v["m2"]))
    target = embed(projector(BELL), (0, 3), 4)
    initial = clean(embed(projector(BELL), (0, 1), 4) * embed(projector(BELL), (3, 2), 4))
    cases = []
    for u, w, pa, pb in product((0, 1), repeat=4):
        za = embed(Z if u and not pa else I2, (0,), 4)
        xb = embed(X if w and not pb else I2, (3,), 4)
        guard = z3.And(v["m1"] == u, v["m2"] == w, v["pA"] == pa, v["pB"] == pb)
        cases.append((guard, clean(xb * za * target * za.H * xb.H)))
    return CaseStudy(program, Assertion(True, Effect.constant(initial, "two initial Bell pairs")),
                     Assertion(theta, Effect("pending local corrections", tuple(cases))),
                     Assertion(True, Effect.constant(target, "Bell_AB")),
                     2 - z3.If(v["dCA"], 1, 0) - z3.If(v["dCB"], 1, 0), v)


def remote_cnot(omit_correction=None):
    """Choi specification covers arbitrary two-qubit inputs, including entanglement."""
    if omit_correction not in (None, "X", "Z"):
        raise ValueError("omit_correction must be None, 'X' or 'Z'")
    variables = tuple(Variable(name, owner, domain) for owner, entries in (
        ("Alice", (("m1", (0, 1)), ("pA", (0, 1)), ("j", (0, 1)), ("dA", (False, True)))),
        ("Bob", (("m2", (0, 1)), ("pB", (0, 1)), ("i", (0, 1)), ("dB", (False, True)))),
    ) for name, domain in entries)
    v = {var.name: var.symbol for var in variables}
    alice = Process("Alice", ("C", "A"), seq(
        Gate("CNOT", ("C", "A")), Measure("m1", "A"), Assign("pA", 0), Assign("dA", False)), (
            Branch("send", z3.Not(v["dA"]), Send("c_1", v["m1"]), seq(Assign("dA", True))),
            Branch("receive", v["pA"] == 0, Receive("c_2", "j"), seq(
                () if omit_correction == "Z" else If(v["j"] == 1, seq(Gate("Z", ("C",)))),
                Assign("pA", 1))),
        ))
    bob = Process("Bob", ("B", "T"), seq(
        Gate("CNOT", ("B", "T")), Gate("H", ("B",)), Measure("m2", "B"),
        Assign("pB", 0), Assign("dB", False)), (
            Branch("receive", v["pB"] == 0, Receive("c_1", "i"), seq(
                () if omit_correction == "X" else If(v["i"] == 1, seq(Gate("X", ("T",)))),
                Assign("pB", 1))),
            Branch("send", z3.Not(v["dB"]), Send("c_2", v["m2"]), seq(Assign("dB", True))),
        ))
    program = Program("Non-local CNOT" + (f" - missing {omit_correction}" if omit_correction else ""),
                      variables, ("RC", "RT", "C", "A", "B", "T"),
                      (alice, bob), references=("RC", "RT"))
    data = clean(embed(projector(BELL), (0, 2), 6) * embed(projector(BELL), (1, 5), 6))
    initial = clean(data * embed(projector(BELL), (3, 4), 6))
    from .quantum import CNOT
    desired = embed(CNOT, (2, 5), 6)
    target = clean(desired * data * desired.H)
    cases = []
    for u, w, pa, pb in product((0, 1), repeat=4):
        zc = embed(Z if w and not pa else I2, (2,), 6)
        xt = embed(X if u and not pb else I2, (5,), 6)
        guard = z3.And(v["m1"] == u, v["m2"] == w, v["pA"] == pa, v["pB"] == pb)
        cases.append((guard, clean(xt * zc * target * zc.H * xt.H)))
    theta = z3.And(v["dA"] == (v["pB"] == 1), v["dB"] == (v["pA"] == 1))
    return CaseStudy(program, Assertion(True, Effect.constant(initial, "input Choi state and shared Bell pair")),
                     Assertion(theta, Effect("pending non-local CNOT corrections", tuple(cases))),
                     Assertion(True, Effect.constant(target, "ideal CNOT Choi state")),
                     2 - z3.If(v["dA"], 1, 0) - z3.If(v["dB"], 1, 0), v)


def audit_pair_orders(case):
    """Check both complete orders for examples that use each pair exactly once."""
    program = case.program
    program.validate()
    pairs = list(program.matching_pairs())
    if len(pairs) != 2:
        raise Unsupported("This supplemental audit requires exactly two communication pairs")
    report = Report(program.name, "supplemental complete-order checks")
    for ordering in permutations(pairs):
        label = " then ".join(item[0] for item in ordering)
        requirement = program.termination
        for _, guard, block in reversed(ordering):
            requirement = z3.And(guard, classical_wp(program, block, requirement))
        requirement = classical_wp(program, program.initialization, requirement)
        report.obligations.append(check_implication(program, case.pre.classical, requirement,
                                                    f"Order is enabled and terminates: {label}"))
        block = seq(program.initialization, *(item[2] for item in ordering))
        report.obligations.append(check_hoare(program, case.pre, block, case.post,
                                             f"Order achieves the postcondition: {label}"))
    return report


def remote_state_preparation(omit_correction=None):
    """Regression/CLI fixture; the Notebook shows its source directly."""
    from .frontend import assertion
    from .syntax import PhaseParameter
    variables = (Variable("m", "Alice", (0, 1)), Variable("d", "Alice", (False, True)),
                 Variable("r", "Bob", (0, 1)), Variable("p", "Bob", (0, 1)))
    v = {var.name: var.symbol for var in variables}
    alice = Process("Alice", ("A",), seq(Gate("R", ("A",), ("alpha",)), Gate("H", ("A",)),
                                          Measure("m", "A"), Assign("d", False)), (
        Branch("send", z3.Not(v["d"]), Send("c", v["m"]), seq(Assign("d", True))),))
    correction = () if omit_correction == "Z" else If(v["r"] == 1, seq(Gate("Z", ("B",))))
    bob = Process("Bob", ("B",), seq(Assign("p", 0)), (
        Branch("receive", v["p"] == 0, Receive("c", "r"), seq(correction, Assign("p", 1))),))
    p = Program("RSP" + (" - missing Z correction" if omit_correction == "Z" else ""), variables,
                ("A", "B"), (alice, bob), parameters=(PhaseParameter("alpha", "Alice"),))
    return CaseStudy(p, assertion("true", "Bell[A,B]")._compile(p),
                     assertion("d <=> p = 1", "Z[B]^((1-p)*m) * Equator(alpha)[B]")._compile(p),
                     assertion("true", "Equator(alpha)[B]")._compile(p), 1-z3.If(v["d"], 1, 0), v)


def scheduler_phase_choice():
    """The exact additional-case-study gate family, for CLI/regressions."""
    from .frontend import assertion, _matrix_literal
    from .syntax import GateFamily
    variables = (Variable("a", "Alice", (False, True)), Variable("b", "Bob", (False, True)),
                 Variable("s", "Bob", (0, 1)))
    v = {var.name: var.symbol for var in variables}
    alice = Process("Alice", ("A",), seq(Assign("a", False)), tuple(
        Branch(f"choose_{value}", z3.Not(v["a"]), Send("c", value), seq(Assign("a", True)))
        for value in (0, 1)))
    bob = Process("Bob", ("B",), seq(Assign("b", False)), (
        Branch("receive", z3.Not(v["b"]), Receive("c", "s"), seq(Gate("U", ("B",), (v["s"],)), Assign("b", True))),))
    family = GateFamily("U", ((0, _matrix_literal("sqrt(9/10)*I + i*sqrt(1/10)*Z")),
                              (1, _matrix_literal("sqrt(7/10)*I + i*sqrt(3/10)*Z"))))
    p = Program("PhaseChoice", variables, ("A", "B"), (alice, bob), gate_families=(family,))
    return CaseStudy(p, assertion("true", "Bell[A,B]")._compile(p),
                     assertion("a <=> b", "U(s)[B]^[a] * Bell[A,B]")._compile(p),
                     assertion("true", "U(s)[B] * Bell[A,B]")._compile(p), 1-z3.If(v["a"], 1, 0), v)
