"""Machine-readable proof certificates for a verification report.

A certificate records the derivation that a report implicitly performed: the
program and specification as structured syntax, the top-level rule and its
premises, every local WP tree with the Löwner side condition at every examined
classical state, every classical SMT query, and the indexed proof objects of
the distillation kernel. It is self-contained JSON for a later Rocq printer and
depends on no Rocq naming. Nothing here changes the verification itself.

Encoding conventions, format "verilocq-certificate/1":

- Classical expressions carry three views: "ast" (nested objects with a
  "kind"), "smtlib" (Z3's s-expression) and "text" (the source notation).
- Matrices are interned once in the top-level "matrices" table and referenced
  by index. Entries are exact SymPy expressions rendered by str(); the symbols
  they mention are listed per matrix and described in "symbols".
- Indexed terms and Hoare formulas (hoare.py, indexed.py) are nested objects
  with a "kind"; integer indices are SymPy expressions rendered by str().
- Lists keep the order in which VeriLocQ produced their elements.
"""

import ast
from datetime import datetime, timezone
import json
import platform

import sympy as sp
import z3

from .derivation import (ImplicationEvidence, LocalEvidence, MatrixEqualityEvidence,
                         TextEvidence, WPNode)
from .pretty import format_block, format_expression, format_program
from .quantum import Assertion as EffectAssertion, Effect, phase_symbol, state_symbols, state_vector
from .syntax import (Assign, Gate, If, Measure, Receive, Reset, Send, Skip, Unsupported, expr, seq)

FORMAT = "verilocq-certificate/1"

_PREMISES = (
    ("Initialization establishes invariant", "initialization"),
    ("Invariant preserved: ", "invariant_preserved"),
    ("Exit implies classical postcondition", "exit_classical"),
    ("Exit implies quantum postcondition", "exit_quantum"),
    ("Ranking function is nonnegative", "ranking_nonnegative"),
    ("No deadlock under invariant", "no_deadlock"),
    ("Ranking decreases: ", "ranking_decreases"),
    ("Local Hoare triple", "local_triple"),
)

_OPERATORS = {
    z3.Z3_OP_AND: "and", z3.Z3_OP_OR: "or", z3.Z3_OP_NOT: "not", z3.Z3_OP_IMPLIES: "implies",
    z3.Z3_OP_XOR: "xor", z3.Z3_OP_IFF: "iff", z3.Z3_OP_DISTINCT: "distinct", z3.Z3_OP_ITE: "ite",
    z3.Z3_OP_LE: "le", z3.Z3_OP_LT: "lt", z3.Z3_OP_GE: "ge", z3.Z3_OP_GT: "gt",
    z3.Z3_OP_ADD: "add", z3.Z3_OP_SUB: "sub", z3.Z3_OP_MUL: "mul", z3.Z3_OP_UMINUS: "neg",
    z3.Z3_OP_DIV: "div", z3.Z3_OP_IDIV: "idiv", z3.Z3_OP_MOD: "mod", z3.Z3_OP_REM: "rem",
    z3.Z3_OP_POWER: "pow",
}


def expression_ast(value):
    """A nested, solver-independent syntax tree of a classical expression."""
    value = expr(value)
    if z3.is_quantifier(value):
        return {"kind": "z3", "text": value.sexpr()}
    if z3.is_true(value):
        return {"kind": "bool", "value": True}
    if z3.is_false(value):
        return {"kind": "bool", "value": False}
    if z3.is_int_value(value):
        return {"kind": "int", "value": value.as_long()}
    if z3.is_rational_value(value):
        return {"kind": "rational", "numerator": value.numerator_as_long(),
                "denominator": value.denominator_as_long()}
    if z3.is_const(value) and value.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return {"kind": "var", "name": str(value), "sort": str(value.sort())}
    kind = value.decl().kind()
    args = [expression_ast(child) for child in value.children()]
    if kind == z3.Z3_OP_EQ:
        return {"kind": "iff" if z3.is_bool(value.children()[0]) else "eq", "args": args}
    if kind in _OPERATORS:
        return {"kind": _OPERATORS[kind], "args": args}
    return {"kind": "z3", "op": value.decl().name(), "args": args}


def classical(value):
    value = expr(value)
    return {"ast": expression_ast(value), "smtlib": value.sexpr(), "text": format_expression(value)}


def _parameter(value):
    if isinstance(value, str):
        return {"kind": "phase", "name": value}
    return classical(value)


def command_ast(command):
    if isinstance(command, Skip):
        return {"kind": "skip"}
    if isinstance(command, Assign):
        return {"kind": "assign", "target": command.target, "value": classical(command.value)}
    if isinstance(command, Gate):
        return {"kind": "gate", "name": command.name, "targets": list(command.targets),
                "parameters": [_parameter(p) for p in command.parameters]}
    if isinstance(command, Measure):
        return {"kind": "measure", "target": command.target, "qubit": command.qubit}
    if isinstance(command, Reset):
        return {"kind": "reset", "qubit": command.qubit}
    if isinstance(command, If):
        return {"kind": "if", "condition": classical(command.condition),
                "then": block_ast(command.then), "else": block_ast(command.otherwise)}
    raise Unsupported(f"No certificate syntax for {command!r}")


def block_ast(block):
    return [command_ast(command) for command in block]


def _block(block):
    return {"ast": block_ast(block), "text": format_block(block)}


class _Matrices:
    """Intern exact matrices once; references are indices into the table."""

    def __init__(self):
        self.table = []
        self.index = {}

    def __call__(self, matrix):
        matrix = sp.ImmutableMatrix(matrix)
        if matrix not in self.index:
            self.index[matrix] = len(self.table)
            self.table.append({
                "rows": matrix.rows, "cols": matrix.cols,
                "symbols": sorted(str(s) for s in matrix.free_symbols),
                "entries": [[str(matrix[r, c]) for c in range(matrix.cols)] for r in range(matrix.rows)],
            })
        return self.index[matrix]


def _symbol_table(program):
    result = []
    for parameter in getattr(program, "parameters", ()):
        result.append({"parameter": parameter.name, "kind": "phase", "owner": parameter.owner,
                       "symbol": str(phase_symbol(parameter.name)),
                       "meaning": f"exp(i*{parameter.name}); a unit phase whose conjugate is its inverse"})
    for parameter in getattr(program, "state_parameters", ()):
        result.append({"parameter": parameter.name, "kind": "state", "qubits": parameter.qubits,
                       "symbols": [str(s) for s in state_symbols(parameter.name, parameter.qubits)],
                       "vector": [str(a) for a in state_vector(parameter.name, parameter.qubits)],
                       "meaning": ("cos(theta)|0> + phase*sin(theta)|1>, real theta and unit phase"
                                   if parameter.qubits == 1 else
                                   "four complex amplitudes with sum_i a_i*conjugate(a_i) = 1")})
    return result


def _variable(variable):
    domain = getattr(variable, "domain", None)
    if domain is None:
        kind = "nat"
    elif type(domain[0]) is bool:
        kind = "bool"
    elif tuple(domain) == (0, 1):
        kind = "bit"
    else:
        kind = "int"
    return {"name": variable.name, "owner": variable.owner, "kind": kind,
            "domain": None if domain is None else list(domain)}


def _branch(branch):
    action = branch.action
    if isinstance(action, Send):
        communication = {"kind": "send", "channel": action.channel, "value": classical(action.value)}
    else:
        communication = {"kind": "receive", "channel": action.channel, "target": action.target}
    return {"name": branch.name, "guard": classical(branch.guard), "action": communication,
            "body": _block(branch.body)}


def _pairs(program):
    """The matching pairs, in the order and form of Program.matching_pairs."""
    computed = list(program.matching_pairs())
    result = []
    for i, left in enumerate(program.processes):
        for right in program.processes[i + 1:]:
            for a in left.branches:
                for b in right.branches:
                    if a.action.channel != b.action.channel:
                        continue
                    if isinstance(a.action, Send) and isinstance(b.action, Receive):
                        sender, receiver = (left, a), (right, b)
                    elif isinstance(b.action, Send) and isinstance(a.action, Receive):
                        sender, receiver = (right, b), (left, a)
                    else:
                        continue
                    label, guard, block = computed[len(result)]
                    if label != f"{left.name}.{a.name} ↔ {right.name}.{b.name}":
                        raise Unsupported("Matching pairs were not reproduced in the verifier's order")
                    result.append({
                        "label": label, "channel": a.action.channel,
                        "sender": {"process": sender[0].name, "branch": sender[1].name,
                                   "guard": classical(sender[1].guard), "value": classical(sender[1].action.value),
                                   "body": _block(sender[1].body)},
                        "receiver": {"process": receiver[0].name, "branch": receiver[1].name,
                                     "guard": classical(receiver[1].guard), "target": receiver[1].action.target,
                                     "body": _block(receiver[1].body)},
                        "guard": classical(guard),
                        "order": [left.name, right.name],
                        "block": _block(block),
                    })
    return result


def program_record(program, matrices, source=None):
    owners = {p.name: p for p in program.processes}
    processes = []
    for process in program.processes:
        processes.append({
            "name": process.name,
            "qubits": list(process.qubits),
            "variables": [_variable(v) for v in program.variables if v.owner == process.name],
            "phases": [p.name for p in getattr(program, "parameters", ()) if p.owner == process.name],
            "initialization": _block(process.init),
            "branches": [_branch(branch) for branch in process.branches],
        })
    families = [{"name": family.name,
                 "cases": [{"selector": key, "matrix": matrices(matrix)} for key, matrix in family.cases]}
                for family in getattr(program, "gate_families", ())]
    return {
        "name": program.name,
        "source": source,
        "text": format_program(program),
        "registers": list(program.registers),
        "references": list(program.references),
        "state_parameters": [{"name": p.name, "qubits": p.qubits} for p in getattr(program, "state_parameters", ())],
        "gate_families": families,
        "variables": [_variable(v) for v in program.variables if v.owner not in owners],
        "processes": processes,
        "initialization": _block(program.initialization),
        "termination": classical(program.termination),
        "domains": classical(program.domains),
        "pairs": _pairs(program),
    }


def predicate_syntax(source, program):
    """The quantum predicate notation as a syntax tree, or None if unparseable."""
    from .frontend import _formula
    if program is None:
        return None
    symbols = {v.name: v.symbol for v in program.variables}
    try:
        tree = ast.parse(source.strip().replace("^", "**"), mode="eval").body
    except (SyntaxError, ValueError):
        return None

    def build(node):
        if isinstance(node, ast.Name) and node.id == "I":
            return {"kind": "identity"}
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return {"kind": "scalar", "value": node.value}
        if isinstance(node, ast.Subscript) and isinstance(node.value, (ast.Name, ast.Call)):
            if isinstance(node.value, ast.Call):
                if not isinstance(node.value.func, ast.Name):
                    raise ValueError
                name = node.value.func.id
                arguments = node.value.args
            else:
                name, arguments = node.value.id, []
            registers = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
            if not all(isinstance(q, ast.Name) for q in registers):
                raise ValueError
            parameters = []
            for argument in arguments:
                if isinstance(argument, ast.Name) and argument.id not in symbols:
                    parameters.append({"kind": "name", "name": argument.id})
                else:
                    parameters.append(classical(_formula(ast.unparse(argument), symbols)))
            return {"kind": "apply", "name": name, "parameters": parameters, "registers": [q.id for q in registers]}
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
            return {"kind": "power", "base": build(node.left),
                    "exponent": classical(_formula(ast.unparse(node.right), symbols))}
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
            return {"kind": "product", "left": build(node.left), "right": build(node.right)}
        raise ValueError

    try:
        return build(tree)
    except (ValueError, Unsupported, AttributeError):
        return None


def effect_record(effect, program, matrices):
    return {"text": effect.label, "syntax": predicate_syntax(effect.label, program),
            "cases": [{"condition": classical(condition), "matrix": matrices(matrix)}
                      for condition, matrix in effect.cases]}


def assertion_record(assertion, program, matrices):
    if assertion is None:
        return None
    if isinstance(assertion.quantum, Effect):
        quantum = effect_record(assertion.quantum, program, matrices)
    else:
        quantum = formula_record(assertion.quantum, matrices)
    return {"classical": classical(assertion.classical), "quantum": quantum}


# Indexed terms and Hoare formulas (indexed.py, hoare.py).

def term_record(term, families):
    from .indexed import Term
    if not isinstance(term, Term):
        raise Unsupported("An indexed term is required")
    a = term.args
    if term.kind in ("I", "0"):
        return {"kind": term.kind, "lo": str(a[0]), "hi": str(a[1])}
    if term.kind == "local":
        return {"kind": "local", "name": a[0], "at": str(a[1])}
    if term.kind == "var":
        return {"kind": "var", "name": a[0], "lo": str(a[1]), "hi": str(a[2])}
    if term.kind == "call":
        return {"kind": "call", "family": family_name(a[0], families), "lo": str(a[1]), "hi": str(a[2])}
    if term.kind == "product":
        return {"kind": "product", "name": a[0], "lo": str(a[1]), "hi": str(a[2])}
    if term.kind in ("add", "sub"):
        return {"kind": term.kind, "left": term_record(a[0], families), "right": term_record(a[1], families)}
    if term.kind == "tensor":
        return {"kind": "tensor", "args": [term_record(part, families) for part in a]}
    if term.kind == "sum":
        return {"kind": "sum", "binder": str(a[0]), "lo": str(a[1]), "hi": str(a[2]),
                "body": term_record(a[3], families)}
    if term.kind == "pullback":
        return {"kind": "pullback", "name": a[0], "at": str(a[1]), "target": term_record(a[2], families)}
    raise Unsupported(f"No certificate syntax for indexed term {term.kind}")


def family_name(family, families):
    if family.name not in families:
        families[family.name] = None  # Reserve the slot before the body refers to the family.
        families[family.name] = {"name": family.name, "start": str(family.start), "end": str(family.end),
                                 "body": term_record(family.body, families), "text": str(family.body)}
    return family.name


def equality_record(proof, families):
    from .indexed import Equality, Positive
    if isinstance(proof, Equality):
        return {"kind": "equality", "rule": proof.rule, "left": term_record(proof.left, families),
                "right": term_record(proof.right, families), "path": list(proof.path),
                "premises": [equality_record(p, families) for p in proof.premises]}
    if isinstance(proof, Positive):
        return {"kind": "positive", "rule": proof.rule, "term": term_record(proof.term, families),
                "premises": [equality_record(p, families) for p in proof.premises]}
    raise Unsupported("Unknown indexed proof object")


def indexed_record(evidence, matrices):
    from .indexed import Induction
    families = {}
    proof = evidence.proof
    if isinstance(proof, Induction):
        k, n = proof.family.start, proof.family.end
        structured = {
            "kind": "induction",
            "family": family_name(proof.family, families),
            "scheme": {"measure": f"{n} - {k}", "base": f"{k} = {n}", "step": f"{k} < {n}",
                       "hypothesis": term_record(proof.family(k + 1, n), families),
                       "statement": f"0 <= {proof.family.name}({k},{n}) <= I for every 0 <= {k} <= {n}"},
            "base": equality_record(proof.base, families),
            "step": equality_record(proof.step, families),
            "lower": equality_record(proof.lower, families),
            "upper_equality": equality_record(proof.upper_equality, families),
            "upper": equality_record(proof.upper, families),
        }
        record_kind = "indexed_induction"
    else:
        structured = equality_record(proof, families)
        record_kind = "indexed_equality"
    kernel = evidence.kernel
    return {
        "kind": record_kind,
        "context": [str(c) for c in evidence.context],
        "dimension": kernel.dimension,
        "local_matrices": {name: matrices(matrix) for name, matrix in kernel.matrices.items()},
        "kraus_maps": {name: matrices(matrix) for name, matrix in kernel.maps.items()},
        "families": list(families.values()),
        "proof": structured,
        "text": evidence.explain(),
    }


def operation_record(operation, matrices):
    return {"kind": operation.kind, "name": operation.name, "at": classical(operation.at),
            "matrix": None if operation.matrix is None else matrices(operation.matrix),
            "outcome": None if operation.outcome is None else classical(operation.outcome),
            "alternatives": [matrices(m) for m in operation.alternatives]}


def formula_record(formula, matrices, families=None):
    families = {} if families is None else families
    a = formula.args
    if formula.kind in ("identity", "zero"):
        return {"kind": formula.kind}
    if formula.kind == "indexed":
        return {"kind": "indexed", "term": term_record(a[0], families), "text": str(a[0])}
    if formula.kind == "choice":
        return {"kind": "choice", "condition": classical(a[0]),
                "yes": formula_record(a[1], matrices, families), "no": formula_record(a[2], matrices, families)}
    if formula.kind == "sum":
        return {"kind": "sum", "left": formula_record(a[0], matrices, families),
                "right": formula_record(a[1], matrices, families)}
    if formula.kind == "pullback":
        return {"kind": "pullback", "operation": operation_record(a[0], matrices),
                "target": formula_record(a[1], matrices, families)}
    raise Unsupported(f"No certificate syntax for formula {formula.kind}")


class _Table:
    """Intern records by a hashable key; references are indices into the table."""

    def __init__(self):
        self.table = []
        self.index = {}

    def __call__(self, key, make):
        if key not in self.index:
            self.index[key] = len(self.table)
            self.table.append(None)
            self.table[self.index[key]] = make()
        return self.index[key]


def hoare_record(evidence, matrices):
    """A Hoare proof as a DAG: steps reference interned expressions, formulas and blocks."""
    from .hoare import DistributedData, Proof, block_key, expression_key
    checker = evidence.checker
    if not checker.steps:
        evidence.check()
    families = {}
    expressions, formulas, blocks = _Table(), _Table(), _Table()
    identifiers = {id(step): f"P{i}" for i, step in enumerate(checker.steps)}

    def expression(value):
        value = expr(value)
        return expressions(expression_key(value), lambda: classical(value))

    def formula(f):
        def make():
            a = f.args
            if f.kind in ("identity", "zero"):
                return {"kind": f.kind}
            if f.kind == "indexed":
                return {"kind": "indexed", "term": term_record(a[0], families), "text": str(a[0])}
            if f.kind == "choice":
                return {"kind": "choice", "condition": expression(a[0]), "yes": formula(a[1]), "no": formula(a[2])}
            if f.kind == "sum":
                return {"kind": "sum", "left": formula(a[0]), "right": formula(a[1])}
            if f.kind == "pullback":
                return {"kind": "pullback", "operation": operation_record(a[0], matrices), "target": formula(a[1])}
            raise Unsupported(f"No certificate syntax for formula {f.kind}")
        return formulas(f.key(), make)

    def assertion(a):
        return {"classical": expression(a.classical), "quantum": formula(a.quantum)}

    steps = []
    for step in checker.steps:
        if isinstance(step.block, tuple):
            block = blocks(block_key(step.block), lambda: _block(step.block))
        else:
            block = {"program": getattr(step.block, "name", str(step.block))}
        data = None
        if step.rule == "Distributed-tot" and step.data and isinstance(step.data[0], DistributedData):
            d = step.data[0]
            data = {"invariant": assertion(d.invariant), "rank": expression(d.rank), "old_rank": expression(d.old_rank)}
        elif step.rule == "Meas" and len(step.data) == 2:
            data = {"original": assertion(step.data[0]), "outcome_variable": expression(step.data[1])}
        elif step.rule == "Aux-Subst" and len(step.data) == 2:
            data = {"variable": expression(step.data[0]), "value": step.data[1]}
        steps.append({"id": identifiers[id(step)], "rule": step.rule, "pre": assertion(step.pre),
                      "block": block, "post": assertion(step.post),
                      "premises": [identifiers[id(p)] for p in step.premises if isinstance(p, Proof)],
                      "data": data})
    return {
        "kind": "hoare_proof",
        "encoding": "steps reference the expressions, formulas and blocks tables of this record by index; "
                    "formula children are indices into formulas",
        "definitions": list(evidence.definitions),
        "families": list(families.values()),
        "local_matrices": {name: matrices(matrix) for name, matrix in checker.quantum.kernel.matrices.items()},
        "expressions": expressions.table,
        "formulas": formulas.table,
        "blocks": blocks.table,
        "root": steps[-1]["id"] if steps else None,
        "steps": steps,
        "quantum_side_conditions": list(dict.fromkeys(checker.quantum.trace)),
    }


# Local WP derivations.

def wp_tree(node, program, matrices):
    if node.rule == "Target":
        # The target is the premise's postcondition, recorded once in its statement.
        return {"rule": "Target", "assertion": "statement.post",
                "text": f"{{ {format_expression(node.target.classical)} ; {node.target.quantum.label} }}"}
    record = {"rule": node.rule, "command": command_ast(node.command)}
    if node.rule == "Meas":
        record["outcome"] = node.outcome
    if node.rule == "If":
        record["then"] = wp_tree(node.yes, program, matrices)
        record["else"] = wp_tree(node.no, program, matrices)
    elif node.after is not None:
        record["after"] = wp_tree(node.after, program, matrices)
    return record


def local_record(evidence, matrices):
    program = evidence.program
    states = []
    counts = {"states": 0, "passed": 0, "failed": 0, "undecided": 0}
    for record in evidence.records:
        decision = record["decision"]
        counts["states"] += 1
        counts["passed" if decision is True else "failed" if decision is False else "undecided"] += 1
        states.append({"state": dict(record["state"]), "pre": matrices(record["pre"]),
                       "wlp": matrices(record["wp"]), "residual": matrices(record["difference"]),
                       "decision": decision})
    parameters = None if evidence.sample is None else evidence.sample.get("state_parameters")
    return {
        "kind": "local",
        "rules": evidence.summary(),
        "derivation": {
            "rule": "Conseq",
            "statement": "pre <= wlp(block, post) in the Löwner order at every classical state of the precondition",
            "side_condition": {
                "kind": "loewner",
                "relevant_variables": list(evidence.relevant),
                "note": "Each state represents every classical state agreeing on the relevant variables",
                "exhaustive": evidence.exhaustive,
                "summary": {**counts, "checked_cases": evidence.checked_cases},
                "states": states,
                "parameter_counterexample": parameters,
            },
            "premise": wp_tree(evidence.wp, program, matrices),
        },
        "text": evidence.wp.explain(),
    }


def implication_record(evidence, program):
    hypothesis, conclusion = expr(evidence.pre), expr(evidence.post)
    query = z3.And(hypothesis, z3.Not(conclusion))
    domains = program.domains if program is not None else z3.BoolVal(True)
    return {
        "kind": "implication",
        "query": {"smtlib": z3.And(domains, query).sexpr(),
                  "statement": "unsat establishes statement.hypothesis => statement.conclusion under program.domains"},
        "result": evidence.solver_result,
    }


def evidence_record(obligation, program, matrices):
    from .hoare import Evidence as HoareEvidence
    from .indexed import IndexedEvidence
    evidence = obligation.evidence
    if isinstance(evidence, LocalEvidence):
        return local_record(evidence, matrices)
    if isinstance(evidence, ImplicationEvidence):
        return implication_record(evidence, program)
    if isinstance(evidence, MatrixEqualityEvidence):
        from .quantum import clean
        residual = clean(evidence.actual - evidence.expected)
        return {"kind": "matrix_equality", "equation": evidence.equation,
                "left": matrices(evidence.actual), "right": matrices(evidence.expected),
                "residual": matrices(residual), "residual_is_zero": residual.is_zero_matrix}
    if isinstance(evidence, TextEvidence):
        return {"kind": "text", "text": evidence.text}
    if isinstance(evidence, IndexedEvidence):
        return indexed_record(evidence, matrices)
    if isinstance(evidence, HoareEvidence):
        return hoare_record(evidence, matrices)
    return {"kind": "none", "method": obligation.kind, "detail": obligation.detail}


def _premise_kind(name):
    for prefix, kind in _PREMISES:
        if name.startswith(prefix):
            return kind
    return None


def _pair_label(name):
    return name.split(": ", 1)[1] if _premise_kind(name) in ("invariant_preserved", "ranking_decreases") else None


def premise_record(index, obligation, program, matrices):
    evidence = obligation.evidence
    statement = None
    if isinstance(evidence, LocalEvidence):
        statement = {"kind": "triple", "pre": assertion_record(evidence.pre, program, matrices),
                     "block": _block(evidence.block), "post": assertion_record(evidence.post, program, matrices)}
    elif isinstance(evidence, ImplicationEvidence):
        statement = {"kind": "implication", "hypothesis": classical(evidence.pre), "conclusion": classical(evidence.post)}
    return {
        "id": f"p{index}",
        "name": obligation.name,
        "premise": _premise_kind(obligation.name),
        "pair": _pair_label(obligation.name),
        "method": obligation.kind,
        "status": obligation.status,
        "cases": obligation.cases,
        "detail": obligation.detail,
        "witness": obligation.witness,
        "statement": statement,
        "evidence": evidence_record(obligation, program, matrices),
    }


def _source_specification(report):
    triple = getattr(report, "triple", None)
    source = (report.specification or {}).get("source") if report.specification else None
    if triple is None and source is None:
        return None
    result = dict(source or {})
    if triple is not None:
        result.setdefault("pre", str(triple.pre))
        result.setdefault("post", str(triple.post))
        result.setdefault("triple", str(triple))
    return result


def specification_record(report, program, matrices):
    from .hoare import DistributedData, Evidence as HoareEvidence
    specification = report.specification or {}
    record = {
        "source": _source_specification(report),
        "precondition": assertion_record(specification.get("pre"), program, matrices),
        "invariant": assertion_record(specification.get("invariant"), program, matrices),
        "postcondition": assertion_record(specification.get("post"), program, matrices),
        "variant": None if specification.get("variant") is None else classical(specification["variant"]),
    }
    if "classical_invariant" in specification:
        record["classical_invariant"] = classical(specification["classical_invariant"])
    attempt = specification.get("attempt")
    if attempt is not None:
        record["attempt"] = program_record(attempt, matrices)
    triples = []
    for obligation in report.obligations:
        evidence = obligation.evidence
        if not isinstance(evidence, HoareEvidence) or not evidence.checker.steps:
            continue
        families = {}
        root = evidence.proof
        distributed = next((s for s in evidence.checker.steps if s.rule == "Distributed-tot"), None)
        data = distributed.data[0] if distributed is not None and distributed.data else None

        def assertion(a):
            return {"classical": classical(a.classical), "quantum": formula_record(a.quantum, matrices, families)}

        triples.append({
            "name": obligation.name,
            "definitions": list(evidence.definitions),
            "pre": assertion(root.pre),
            "invariant": assertion(data.invariant) if isinstance(data, DistributedData) else None,
            "post": assertion(root.post),
            "rank": classical(data.rank) if isinstance(data, DistributedData) else None,
            "families": list(families.values()),
        })
    if triples:
        record["hoare_triples"] = triples
    return record


def build(report):
    """The certificate of a report, as a JSON-compatible dictionary."""
    from . import __version__
    matrices = _Matrices()
    program = report.backend
    if program is None:
        # Reports assembled outside verify_distributed know the program only through local evidence.
        program = next((o.evidence.program for o in report.obligations
                        if isinstance(o.evidence, LocalEvidence)), None)
    plan = report.derivation
    protocol = getattr(getattr(report, "triple", None), "protocol", None)
    source = None if protocol is None else protocol.source
    premises = [premise_record(i, o, program, matrices) for i, o in enumerate(report.obligations, 1)]
    identifiers = {id(o): p["id"] for o, p in zip(report.obligations, premises)}
    groups = []
    if plan is not None:
        for group in plan.groups:
            groups.append({"name": group.name, "basis": group.basis, "status": group.status,
                           "premises": [identifiers[id(c)] for c in group.checks if id(c) in identifiers]})
    return {
        "format": FORMAT,
        "tool": {
            "name": "VeriLocQ", "version": __version__,
            "python": platform.python_version(), "z3": z3.get_version_string(), "sympy": sp.__version__,
            "mode": report.mode,
            "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "verdict": report.status,
        },
        "encoding": {
            "matrices": "interned in the top-level table; every matrix reference is an index into it",
            "matrix_entries": "exact SymPy expressions rendered by str(); free symbols are listed per matrix",
            "classical_expressions": "ast (nested kinds), smtlib (Z3 s-expression) and text (source notation)",
            "indices": "integer index expressions of indexed terms are SymPy expressions rendered by str()",
        },
        "program": None if program is None else program_record(program, matrices, source),
        "symbols": [] if program is None else _symbol_table(program),
        "specification": specification_record(report, program, matrices),
        "rule": None if plan is None else plan.rule,
        "basis": None if plan is None else plan.basis,
        "note": None if plan is None else plan.note,
        "groups": groups,
        "premises": premises,
        "matrices": matrices.table,
    }


def save(report, path):
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(build(report), handle, indent=2, ensure_ascii=False)
        handle.write("\n")
