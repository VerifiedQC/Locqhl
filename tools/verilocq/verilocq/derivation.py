"""Executable semantic WP trees and explanations of the checks actually made.

These trees compute predicates, not physical execution states. Local rule names
identify the corresponding paper rules; they are not Rocq proof terms. A
distributed plan records the paper rule's premises. Indexed quantum proofs
replay tensor, finite-sum and induction rules in a separate Python kernel.
"""

from dataclasses import dataclass, field
from html import escape
from itertools import count

import sympy as sp

from .pretty import format_block, format_expression
from .quantum import clean, embed, evaluate, gate_matrix
from .syntax import Assign, Gate, If, Measure, Reset, Skip, Unsupported


@dataclass(eq=False)
class WPNode:
    rule: str
    command: object = None
    after: object = None
    yes: object = None
    no: object = None
    target: object = None
    outcome: str = "u"

    def children(self):
        if self.rule == "If":
            return (self.yes, self.no)
        return (self.after,) if self.after is not None else ()

    def evaluate(self, program, state, max_paths=256):
        leaves = 0
        dimension = 2 ** len(program.registers)
        pending, depths = [(self, 1)], {}
        while pending:
            node, depth = pending.pop()
            if depth > 256:
                raise Unsupported("WP depth limit (256) reached; calculation is incomplete")
            if depth <= depths.get(id(node), 0):
                continue
            depths[id(node)] = depth
            pending.extend((child, depth+1) for child in node.children())

        def updated(current, name, value):
            variable = program.varmap[name]
            if type(value) is not type(variable.domain[0]) or value not in variable.domain:
                raise Unsupported(f"Assignment {name}:={value} escapes declared finite domain {variable.domain}")
            return {**current, name: value}

        def visit(node, current):
            nonlocal leaves
            command = node.command
            if node.rule == "Target":
                leaves += 1
                if leaves > max_paths:
                    raise Unsupported(f"Measurement path limit ({max_paths}) reached")
                return node.target.at(current, program)
            if node.rule == "Assign":
                return visit(node.after, updated(current, command.target, evaluate(command.value, current, program)))
            if node.rule == "Skip":
                return visit(node.after, current)
            if node.rule == "Unitary":
                indices = tuple(program.registers.index(q) for q in command.targets)
                unitary = embed(gate_matrix(command, current, program), indices, len(program.registers))
                return clean(unitary.H * visit(node.after, current) * unitary)
            if node.rule == "If":
                branch = node.yes if evaluate(command.condition, current, program) else node.no
                return visit(branch, current)
            if node.rule in ("Meas", "Init"):
                target = program.registers.index(command.qubit)
                result = sp.zeros(dimension)
                for outcome in (0, 1):
                    local = sp.zeros(2)
                    local[outcome if node.rule == "Meas" else 0, outcome] = 1
                    kraus = embed(sp.ImmutableMatrix(local), (target,), len(program.registers))
                    output = updated(current, command.target, outcome) if node.rule == "Meas" else current
                    result += kraus.H * visit(node.after, output) * kraus
                return clean(result)
            raise Unsupported(f"Unknown WP transformation: {node.rule}")

        return clean(visit(self, dict(state)))

    def rules(self):
        found, visited = [], set()
        pending = [self]
        while pending:
            node = pending.pop()
            if id(node) in visited:
                continue
            visited.add(id(node))
            if node.rule != "Target" and node.rule not in found:
                found.append(node.rule)
            pending.extend(reversed(node.children()))
        return tuple(found)

    def explain(self):
        order, visited = [], set()
        pending = [self]
        while pending:
            node = pending.pop()
            if id(node) in visited:
                continue
            visited.add(id(node))
            order.append(node)
            pending.extend(reversed(node.children()))
        names, counter = {}, count()
        for node in order:
            names[id(node)] = "Q" if node.rule == "Target" else f"W{next(counter)}"
        lines = ["Backward predicate calculation:"]
        for node in order:
            name = names[id(node)]
            if node.rule == "Target":
                condition = format_expression(node.target.classical)
                lines.append(f"Q(sigma) = [{condition}] * ({node.target.quantum.label})(sigma)")
                lines.append("  [Assert-Eq]")
                continue
            command = node.command
            after = names[id(node.after)] if node.after is not None else ""
            source = (f"if {format_expression(command.condition)} then ... else ... fi"
                      if node.rule == "If" else format_block((command,)).strip().rstrip(";"))
            lines.append(f"[{node.rule} WP] {{ {name} }} {source} {{ {after or 'Q_after_if'} }}")
            if node.rule == "Assign":
                lines.append(f"  {name}(sigma) = {after}(sigma[{command.target} <- {format_expression(command.value)}])")
            elif node.rule == "Unitary":
                gate = source
                lines.append(f"  {name}(sigma) = {gate}^dagger * {after}(sigma) * {gate}")
            elif node.rule == "Skip":
                lines.append(f"  {name}(sigma) = {after}(sigma)")
            elif node.rule == "Meas":
                u = node.outcome
                m = f"M_{u}[{command.qubit}]"
                lines.append(f"  {name}(sigma) = sum_{{{u}=0,1}} {m}^dagger * {after}(sigma[{command.target} <- {u}]) * {m}")
                lines.append(f"  {u} is fresh; both outcome pullbacks are added, with no normalization.")
                lines.append("  [Branch-Accum] Sum the two measurement outcomes.")
            elif node.rule == "Init":
                lines.append(f"  {name}(sigma) = sum_{{u=0,1}} (|0><u|)^dagger * {after}(sigma) * (|0><u|)")
            elif node.rule == "If":
                yes, no = names[id(node.yes)], names[id(node.no)]
                lines.append(f"  {name}(sigma) = {yes}(sigma) if {format_expression(command.condition)}; otherwise {no}(sigma)")
        return "\n".join(lines)


def build_wp(program, block, post):
    fresh = count()
    forbidden = set(program.varmap) | {p.name for p in getattr(program, "parameters", ())}

    def build(commands, tail, nesting=0):
        if nesting > 256:
            raise Unsupported("WP construction nesting limit (256) reached; calculation is incomplete")
        node = tail
        for command in reversed(commands):
            if isinstance(command, If):
                node = WPNode("If", command, after=node,
                              yes=build(command.then, node, nesting+1), no=build(command.otherwise, node, nesting+1))
                continue
            rule = next((name for kind, name in ((Assign, "Assign"), (Gate, "Unitary"), (Measure, "Meas"),
                                                  (Reset, "Init"), (Skip, "Skip")) if isinstance(command, kind)), None)
            if rule is None:
                raise Unsupported(f"Unsupported local command in WP: {command}")
            outcome = "u"
            if rule == "Meas":
                outcome = f"outcome_{next(fresh)}"
                while outcome in forbidden:
                    outcome = f"outcome_{next(fresh)}"
                forbidden.add(outcome)
            node = WPNode(rule, command=command, after=node, outcome=outcome)
        return node

    return build(block, WPNode("Target", target=post))


@dataclass
class LocalEvidence:
    program: object
    pre: object
    block: tuple
    post: object
    wp: WPNode
    checked_cases: int = 0
    sample: dict | None = None
    exhaustive: bool = False

    def record(self, state, before, after, difference, decision):
        self.checked_cases += 1
        if self.sample is None or decision is not True:
            self.sample = {"state": dict(state), "pre": before, "wp": after,
                           "difference": difference, "decision": decision}

    def summary(self):
        rules = list(self.wp.rules())
        def has_sequence(block):
            return len(block) > 1 or any(isinstance(c, If) and (has_sequence(c.then) or has_sequence(c.otherwise)) for c in block)
        if has_sequence(self.block):
            rules.insert(0, "Seq")
        return ", ".join(rules) or "assertion entailment"

    def explain(self, matrices=False):
        lines = [f"Rules: {self.summary()}", self.wp.explain(),
                 f"[Conseq side condition] ({self.pre.quantum.label})(sigma) <= W0(sigma) "
                 f"under {format_expression(self.pre.classical)}.",
                 f"Exact operator inequalities checked at {self.checked_cases} relevant classical inputs."]
        if self.exhaustive and self.checked_cases == 0:
            lines.append("The classical precondition has no satisfying input under the declared domains: the triple is vacuous. No operator evaluation is needed.")
        if self.wp.rule == "Target":
            lines[-2] = lines[-2].replace("W0", "Q")
        if matrices and self.sample is not None:
            sample = self.sample
            lines.extend(["One recorded valuation from the checks completed so far; overall coverage depends on the obligation status:",
                          str(sample["state"]), "Precondition effect:", str(sample["pre"]),
                          "Calculated weakest precondition:", str(sample["wp"]),
                          "Residual wp - pre (must be positive semidefinite):", str(sample["difference"])])
        return "\n".join(lines)


@dataclass
class ImplicationEvidence:
    pre: object
    post: object
    solver_result: str

    def explain(self, matrices=False):
        return (f"[SMT side condition] {format_expression(self.pre)} => {format_expression(self.post)}\n"
                f"Z3 checks the negation under the declared domains: {self.solver_result}.")


@dataclass
class MatrixEqualityEvidence:
    equation: str
    actual: object
    expected: object

    def explain(self, matrices=False):
        residual = clean(self.actual - self.expected)
        lines = [self.equation, f"Exact residual (left - right) is zero: {residual.is_zero_matrix}."]
        if matrices:
            lines.extend(["Computed left side:", str(self.actual), "Required right side:", str(self.expected),
                          "Residual:", str(residual)])
        return "\n".join(lines)


@dataclass
class TextEvidence:
    text: str

    def explain(self, matrices=False):
        return self.text


@dataclass
class ProofGroup:
    name: str
    basis: str
    checks: tuple

    @property
    def status(self):
        if any(o.status == "FAILED" for o in self.checks):
            return "FAILED"
        return "PASSED" if self.checks and all(o.status == "PASSED" for o in self.checks) else "INCOMPLETE"


@dataclass
class ProofPlan:
    rule: str
    basis: str
    checks: object
    note: str = ""
    groups: tuple = ()

    def __post_init__(self):
        # Keep the live obligation list, not a back-reference to its owning
        # Report. This avoids a cyclic report/derivation object graph.
        if hasattr(self.checks, "obligations"):
            self.checks = self.checks.obligations

    def summary(self):
        lines = [f"Proof: [{self.rule}]"]
        covered = set()
        for group in self.groups:
            lines.append(f"  [{group.status}] {group.name}")
            covered.update(id(c) for c in group.checks)
        for obligation in self.checks:
            if id(obligation) in covered:
                continue
            detail = getattr(obligation, "evidence", None)
            rules = f" [{detail.summary()}]" if isinstance(detail, LocalEvidence) else ""
            lines.append(f"  [{obligation.status}] {obligation.name}{rules}")
        return "\n".join(lines)

    def explain(self, matrices=False):
        lines = [self.summary()]
        if self.note:
            lines.append(self.note)
        for i, obligation in enumerate(self.checks, 1):
            lines.append(f"\n{i}. {obligation.name} [{obligation.status}]")
            evidence = getattr(obligation, "evidence", None)
            if evidence is not None:
                lines.append(evidence.explain(matrices=matrices))
                if obligation.detail:
                    lines.append(obligation.detail)
            else:
                lines.append(f"Method: {obligation.kind}. {obligation.detail}")
            if obligation.witness is not None:
                lines.append(f"Classical witness: {obligation.witness}")
        return "\n".join(lines)

    def html(self, matrices=False, expanded=False, include_summary=True):
        parts = [f"<pre>{escape(self.summary())}</pre>"] if include_summary else []
        if self.note:
            parts.append(f"<p>{escape(self.note)}</p>")
        for i, obligation in enumerate(self.checks, 1):
            evidence = getattr(obligation, "evidence", None)
            body = evidence.explain(matrices=matrices) if evidence is not None else f"{obligation.kind}: {obligation.detail}"
            if evidence is not None and obligation.detail:
                body += "\n" + obligation.detail
            if obligation.witness is not None:
                body += f"\nClassical witness: {obligation.witness}"
            opening = " open" if expanded else ""
            parts.append(f"<details{opening}><summary>{escape(f'{i}. [{obligation.status}] {obligation.name}')}</summary><pre>{escape(body)}</pre></details>")
        return "".join(parts)


@dataclass
class ProofView:
    plan: ProofPlan
    matrices: bool = False
    expanded: bool = True

    def __str__(self):
        return self.plan.explain(matrices=self.matrices)

    __repr__ = __str__

    def _repr_html_(self):
        return self.plan.html(matrices=self.matrices, expanded=self.expanded)
