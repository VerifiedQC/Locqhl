"""Generate and discharge the finite-fragment Distributed/Distributed-tot premises.

For a loop-free block L, compute its exact Heisenberg pullback:
    wp(L, Delta)(sigma) = sum_path K_path† Delta(sigma_path) K_path.
Then Gamma <= wp is an operator inequality for every relevant classical input.
Classical cases are exhaustively enumerated with Z3, not randomly sampled.
"""

from dataclasses import dataclass, field
from html import escape

import sympy as sp
import z3

from .quantum import Assertion, clean, embed, evaluate, gate_matrix, psd
from .syntax import (Assign, Gate, If, Measure, Reset, Skip, Unsupported,
                     expr, live_before, names)
from .derivation import build_wp, LocalEvidence, ImplicationEvidence, ProofPlan


@dataclass
class Obligation:
    name: str
    kind: str
    status: str
    cases: int = 0
    detail: str = ""
    witness: dict | None = None
    evidence: object = field(default=None, repr=False, compare=False)

    def as_dict(self):
        return {"obligation": self.name, "kind": self.kind, "status": self.status,
                "cases": self.cases, "detail": self.detail, "witness": self.witness}

    def __str__(self):
        text = f"{self.status}: {self.name}"
        if self.detail:
            text += f"\n  {self.detail}"
        if self.witness is not None:
            text += f"\n  Example input: {self.witness}"
        return text


@dataclass
class Report:
    program: str
    mode: str
    obligations: list[Obligation] = field(default_factory=list)
    derivation: object = field(default=None, repr=False, compare=False)

    @property
    def verified(self):
        return bool(self.obligations) and all(o.status == "PASSED" for o in self.obligations)

    @property
    def status(self):
        return "VERIFIED" if self.verified else "NOT_VERIFIED"

    def records(self):
        return [o.as_dict() for o in self.obligations]

    def __str__(self):
        lines = [f"{self.program}: {self.status} ({self.mode})"]
        for o in self.obligations:
            count = f" ({o.cases} checked cases)" if o.cases else ""
            lines.append(f"  [{o.status}] {o.name}{count}")
            if o.detail:
                lines.append(f"    {o.detail}")
            if o.witness is not None:
                lines.append(f"    Classical witness: {o.witness}")
        return "\n".join(lines)

    def _repr_html_(self):
        return f"<pre>{escape(str(self))}</pre>"


def states(program, condition, projected, limit=4096):
    """One witness per relevant valuation; block all projected values each round.

    Projection is a dependency reduction, not a sample: every state agreeing on
    these values has the same input effect, control flow and observed output.
    """
    solver = program.solver()
    solver.add(expr(condition))
    projected = sorted(projected)
    count = 0
    while True:
        answer = solver.check()
        if answer == z3.unsat:
            return
        if answer != z3.sat:
            raise Unsupported(f"Z3 returned unknown: {solver.reason_unknown()}")
        if count >= limit:
            raise Unsupported(f"Classical case limit ({limit}) reached; exploration is incomplete")
        model = solver.model()
        state = {}
        for var in program.variables:
            value = model.eval(var.symbol, model_completion=True)
            state[var.name] = z3.is_true(value) if z3.is_bool(value) else value.as_long()
        yield state
        count += 1
        solver.add(z3.Or(*[program.varmap[name].symbol != expr(state[name])
                           for name in projected]))


def execute(program, block, state, max_paths=256):
    """Symbolic quantum execution: keep Kraus maps, never choose an input state."""
    dimension = 2 ** len(program.registers)
    paths = [(dict(state), sp.ImmutableMatrix(sp.eye(dimension)))]

    def set_value(current, target, value):
        var = program.varmap[target]
        if type(value) is not type(var.domain[0]) or value not in var.domain:
            raise Unsupported(f"Assignment {target}:={value} escapes declared finite domain {var.domain}")
        result = dict(current)
        result[target] = value
        return result

    for command in block:
        next_paths = []
        for current, kraus in paths:
            if isinstance(command, Skip):
                next_paths.append((current, kraus))
            elif isinstance(command, Assign):
                value = evaluate(command.value, current, program)
                next_paths.append((set_value(current, command.target, value), kraus))
            elif isinstance(command, Gate):
                targets = tuple(program.registers.index(q) for q in command.targets)
                operator = embed(gate_matrix(command, current, program), targets, len(program.registers))
                next_paths.append((current, clean(operator * kraus)))
            elif isinstance(command, (Measure, Reset)):
                target = program.registers.index(command.qubit)
                for outcome in (0, 1):
                    if isinstance(command, Measure):
                        local = sp.zeros(2)
                        local[outcome, outcome] = 1
                        output = set_value(current, command.target, outcome)
                    else:
                        local = sp.zeros(2)
                        local[0, outcome] = 1
                        output = current
                    operator = embed(sp.ImmutableMatrix(local), (target,), len(program.registers))
                    next_paths.append((output, clean(operator * kraus)))
            elif isinstance(command, If):
                selected = command.then if evaluate(command.condition, current, program) else command.otherwise
                for output, operator in execute(program, selected, current, max_paths):
                    next_paths.append((output, clean(operator * kraus)))
            else:
                raise Unsupported(f"Unsupported command {command!r}")
            if len(next_paths) > max_paths:
                raise Unsupported(f"Measurement path limit ({max_paths}) reached")
        paths = next_paths
    return paths


def weakest_precondition(program, block, post, state, max_paths=256):
    return build_wp(program, block, post).evaluate(program, state, max_paths)


def check_hoare(program, pre, block, post, name="Local Hoare triple",
                max_states=4096, max_paths=256, validate=True):
    if validate:
        program.validate()
        program.validate_block(block)
        pre.validate(program)
        post.validate(program)
    relevant = pre.quantum.dependencies | live_before(block, post.dependencies)
    try:
        wp = build_wp(program, block, post)
    except Unsupported as error:
        return Obligation(name, "operator inequality", "INCOMPLETE", 0, str(error))
    evidence = LocalEvidence(program, pre, block, post, wp)
    count = 0
    try:
        for state in states(program, pre.classical, relevant, max_states):
            before = pre.quantum.at(state, program)
            after = wp.evaluate(program, state, max_paths)
            difference = clean(after - before)
            decision = psd(difference)
            count += 1
            evidence.record(state, before, after, difference, decision)
            if decision is False:
                return Obligation(name, "operator inequality", "FAILED", count,
                                  "The precondition does not guarantee this intermediate proof condition. "
                                  "The program or the supplied invariant may need to change.",
                                  state, evidence=evidence)
            if decision is None:
                return Obligation(name, "operator inequality", "INCOMPLETE", count,
                                  "Exact positivity could not be decided", state, evidence=evidence)
    except Unsupported as error:
        return Obligation(name, "operator inequality", "INCOMPLETE", count, str(error), evidence=evidence)
    evidence.exhaustive = True
    return Obligation(name, "operator inequality", "PASSED", count,
                      "Exact effect ≤ weakest precondition; all relevant classical cases exhausted", evidence=evidence)


def check_implication(program, pre, post, name, validate=True):
    if validate:
        program.validate()
    program.validate_expr(pre, boolean=True)
    program.validate_expr(post, boolean=True)
    solver = program.solver()
    solver.add(expr(pre), z3.Not(expr(post)))
    answer = solver.check()
    evidence = ImplicationEvidence(expr(pre), expr(post), str(answer))
    if answer == z3.unsat:
        return Obligation(name, "classical SMT", "PASSED", detail="Negation is unsatisfiable over the declared domains", evidence=evidence)
    if answer == z3.unknown:
        return Obligation(name, "classical SMT", "INCOMPLETE", detail=solver.reason_unknown(), evidence=evidence)
    model = solver.model()
    witness = {v.name: str(model.eval(v.symbol, model_completion=True)) for v in program.variables}
    return Obligation(name, "classical SMT", "FAILED", detail="Classical implication has a counterexample", witness=witness, evidence=evidence)


def classical_wp(program, block, post):
    """Demonic WP over all measurement outcomes, for a sufficient ranking proof."""
    result = expr(post)
    for command in reversed(block):
        if isinstance(command, Assign):
            var = program.varmap[command.target]
            value = expr(command.value)
            result = z3.And(var.admits(value),
                            z3.substitute(result, (var.symbol, value)))
        elif isinstance(command, Measure):
            var = program.varmap[command.target]
            result = z3.And(*[z3.substitute(result, (var.symbol, z3.IntVal(m))) for m in (0, 1)])
        elif isinstance(command, If):
            result = z3.And(z3.Implies(expr(command.condition), classical_wp(program, command.then, result)),
                            z3.Implies(z3.Not(expr(command.condition)), classical_wp(program, command.otherwise, result)))
        elif not isinstance(command, (Skip, Gate, Reset)):
            raise Unsupported(f"Unsupported command: {command}")
    return z3.simplify(result)


def verify_distributed(program, pre, invariant, post, variant=None,
                       max_states=4096, max_paths=256):
    """Check all premises. Never report VERIFIED on incomplete/unknown checks.

    Omitting variant checks partial correctness only. With an integer variant,
    also check nonnegativity, decrease on every pair and absence of deadlock.
    No invariant or variant synthesis, floating-point reasoning or certificate
    generation is hidden in this API.
    """
    program.validate()
    for assertion in (pre, invariant, post):
        assertion.validate(program)
    mode = "partial correctness" if variant is None else "total correctness"
    report = Report(program.name, mode)
    options = {"max_states": max_states, "max_paths": max_paths, "validate": False}
    report.obligations.append(check_hoare(program, pre, program.initialization, invariant,
                                         "Initialization establishes invariant", **options))
    pairs = list(program.matching_pairs())
    for label, guard, block in pairs:
        guarded = Assertion(z3.And(expr(invariant.classical), guard), invariant.quantum)
        report.obligations.append(check_hoare(program, guarded, block, invariant,
                                             f"Invariant preserved: {label}", **options))
    exit_condition = z3.And(expr(invariant.classical), program.termination)
    report.obligations.append(check_implication(program, exit_condition, post.classical,
                                                "Exit implies classical postcondition"))
    report.obligations.append(check_hoare(program, Assertion(exit_condition, invariant.quantum), (), post,
                                         "Exit implies quantum postcondition", **options))
    if variant is not None:
        program.validate_expr(variant)
        if not z3.is_int(expr(variant)):
            raise Unsupported("The ranking function must be an integer expression")
        report.obligations.append(check_implication(program, invariant.classical, expr(variant) >= 0,
                                                    "Ranking function is nonnegative"))
        no_pair = z3.And(*[z3.Not(guard) for _, guard, _ in pairs])
        report.obligations.append(check_implication(program, z3.And(expr(invariant.classical), no_pair),
                                                    program.termination, "No deadlock under invariant"))
        old = z3.FreshInt("old_rank")
        for label, guard, block in pairs:
            requirement = classical_wp(program, block, expr(variant) < old)
            # Eliminate the fresh logical variable after WP so only input rank remains.
            requirement = z3.substitute(requirement, (old, expr(variant)))
            report.obligations.append(check_implication(program, z3.And(expr(invariant.classical), guard),
                                                        requirement, f"Ranking decreases: {label}"))
    report.derivation = ProofPlan(
        "Distributed-tot" if variant is not None else "Distributed",
        "paper rule with semantic-WP premises", report)
    return report
