"""Paper-style source language. Solver expressions stay behind this boundary.

Parsing never calls eval/exec. Protocol source lowers to the existing typed
command objects; assertions lower to exact effects and solver expressions.
The same source displayed in the Notebook is the source actually checked.
"""

import ast
from dataclasses import dataclass
from html import escape
import re
from textwrap import dedent

import sympy as sp
import z3
from z3.z3util import get_vars

from . import syntax as ir
from .quantum import (Assertion, BELL, Effect, GATES, clean, embed, evaluate,
                      gate_matrix, phase_symbol, projector)
from .verifier import Report, check_implication, states, verify_distributed
from .derivation import ProofPlan, ProofView


class SourceError(ir.Unsupported):
    """An invalid or unsupported construct in the user-facing source language."""


def _matrix_literal(source):
    """Read exact one-qubit gate expressions without Python/SymPy string eval."""
    from .quantum import I2

    def read(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in {"I", "X", "Z", "H", "i"}:
            return {"I": I2, "i": sp.I, **GATES}[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -read(node.operand)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "sqrt" and len(node.args) == 1 and not node.keywords:
            value = read(node.args[0])
            if not isinstance(value, sp.Expr) or value.free_symbols:
                raise SourceError("sqrt requires an exact scalar")
            return sp.sqrt(value)
        if isinstance(node, ast.BinOp):
            a, b = read(node.left), read(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.Div) and isinstance(b, sp.Expr) and b != 0:
                return a / b
        raise SourceError("Gate cases use exact integers/fractions, sqrt(...), i, I, X, Z and H")

    try:
        result = read(ast.parse(source, mode="eval").body)
        if not isinstance(result, sp.MatrixBase) or result.shape != (2, 2):
            raise SourceError("A gate case must define a 2x2 matrix")
        return clean(result)
    except (SyntaxError, TypeError, ValueError) as error:
        if isinstance(error, SourceError):
            raise
        raise SourceError(f"Invalid exact gate expression: {error}") from None


# The explicit alternatives below also preserve token offsets for source errors.
_TOKEN = re.compile(r"\s+|\#[^\n]*|<=>|=>|:=|->|\[\]|\|\||\.\.|<=|>=|!=|==|\*\*|[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]")


class Tokens:
    def __init__(self, source):
        self.source = source
        self.items = [(m.group(), m.start()) for m in _TOKEN.finditer(source)
                      if not m.group().isspace() and not m.group().startswith("#")]
        self.index = 0

    @property
    def peek(self):
        return self.items[self.index][0] if self.index < len(self.items) else "<end>"

    def error(self, message):
        offset = self.items[self.index][1] if self.index < len(self.items) else len(self.source)
        line = self.source.count("\n", 0, offset) + 1
        column = offset - self.source.rfind("\n", 0, offset)
        return SourceError(f"{message} at line {line}, column {column} (found {self.peek!r})")

    def pop(self, expected=None):
        value = self.peek
        if value == "<end>" or (expected is not None and value != expected):
            raise self.error(f"Expected {expected or 'another token'}")
        self.index += 1
        return value

    def accept(self, value):
        if self.peek == value:
            self.index += 1
            return True
        return False

    def identifier(self):
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", self.peek):
            raise self.error("Expected an identifier")
        return self.pop()

    def through(self, stops):
        start = self.index
        depth = 0
        while self.peek != "<end>":
            token = self.peek
            if depth == 0 and token in stops:
                break
            if token in ("(", "[", "{"):
                depth += 1
            elif token in (")", "]", "}"):
                depth -= 1
                if depth < 0:
                    raise self.error("Unmatched delimiter")
            self.index += 1
        if self.index == start:
            raise self.error("Expected an expression")
        if depth:
            raise self.error("Unclosed expression delimiter")
        return " ".join(t for t, _ in self.items[start:self.index])


_PRECEDENCE = {"<=>": 10, "=>": 20, "or": 30, "and": 40,
               "=": 60, "==": 60, "!=": 60, "<": 60, "<=": 60, ">": 60, ">=": 60,
               "+": 70, "-": 70, "*": 80, "%": 80}


def _formula(source, symbols):
    """Parse classical notation, including implication and Boolean indicators."""
    tokens = Tokens(source)

    def parse(minimum=0):
        token = tokens.pop()
        if token == "(":
            left = parse()
            tokens.pop(")")
        elif token == "[":
            inner = parse()
            tokens.pop("]")
            if not z3.is_bool(inner):
                raise tokens.error("An indicator [condition] requires a Boolean condition")
            left = z3.If(inner, 1, 0)
        elif token == "not":
            left = z3.Not(parse(50))
        elif token == "-":
            left = -parse(90)
        elif token in ("true", "false"):
            left = z3.BoolVal(token == "true")
        elif token.isdigit():
            left = z3.IntVal(int(token))
        elif token in symbols:
            left = symbols[token]
        else:
            raise tokens.error(f"Unknown variable or expression {token!r}")
        while tokens.peek in _PRECEDENCE and _PRECEDENCE[tokens.peek] >= minimum:
            operator = tokens.pop()
            level = _PRECEDENCE[operator]
            right = parse(level if operator == "=>" else level + 1)
            if operator == "<=>":
                if not (z3.is_bool(left) and z3.is_bool(right)):
                    raise tokens.error("Equivalence <=> requires two Boolean formulas")
                left = left == right
            elif operator in ("=", "=="):
                left = left == right
            elif operator == "!=":
                left = left != right
            elif operator == "=>":
                left = z3.Implies(left, right)
            elif operator == "and":
                left = z3.And(left, right)
            elif operator == "or":
                left = z3.Or(left, right)
            elif operator == "<":
                left = left < right
            elif operator == "<=":
                left = left <= right
            elif operator == ">":
                left = left > right
            elif operator == ">=":
                left = left >= right
            elif operator == "+":
                left = left + right
            elif operator == "-":
                left = left - right
            elif operator == "*":
                left = left * right
            elif operator == "%":
                left = left % right
        return left

    try:
        result = parse()
        if tokens.peek != "<end>":
            raise tokens.error("Unexpected expression token; use and/or/not and explicit parentheses")
        return result
    except z3.Z3Exception as error:
        raise SourceError(f"Invalid types in expression {source!r}: {error}") from None


@dataclass(frozen=True)
class _Cell:
    array: str
    index: str


class _ProgramParser(Tokens):
    def __init__(self, source):
        super().__init__(source)
        self.variables = []
        self.references = []
        self.arrays = {}
        self.processes = []
        self.has_naturals = False
        self.parameters = []
        self.families = []

    def name_list(self):
        result = [self.identifier()]
        while self.accept(","):
            result.append(self.identifier())
        return result

    def integer(self):
        sign = -1 if self.accept("-") else 1
        if not self.peek.isdigit():
            raise self.error("Expected an integer range bound")
        return sign * int(self.pop())

    def register(self):
        name = self.identifier()
        if self.accept("["):
            index = self.through({"]"})
            self.pop("]")
            return _Cell(name, index)
        return name

    def block(self, stops):
        commands = []
        while self.peek not in stops:
            if self.peek == "<end>":
                raise self.error(f"Expected one of {sorted(stops)}")
            if self.accept("if"):
                condition = self.through({"then"})
                self.pop("then")
                yes = self.block({"else", "fi"})
                no = self.block({"fi"}) if self.accept("else") else ()
                self.pop("fi")
                self.accept(";")
                commands.append(ir.If(condition, yes, no))
            elif self.accept("skip"):
                self.pop(";")
                commands.append(ir.Skip())
            elif self.peek in set(GATES) | {"R"} | {f.name for f in self.families}:
                gate = self.pop()
                parameters = ()
                if self.accept("("):
                    parameters = (self.through({")"}),)
                    self.pop(")")
                self.pop("[")
                targets = [self.register()]
                while self.accept(","):
                    targets.append(self.register())
                self.pop("]")
                self.pop(";")
                commands.append(ir.Gate(gate, tuple(targets), parameters))
            else:
                target = self.identifier()
                self.pop(":=")
                if self.accept("M"):
                    self.pop("[")
                    qubit = self.register()
                    self.pop("]")
                    commands.append(ir.Measure(target, qubit))
                elif self.accept("|"):
                    self.pop("0")
                    self.pop(">")
                    commands.append(ir.Reset(target))
                else:
                    commands.append(ir.Assign(target, self.through({";"})))
                self.pop(";")
        return tuple(commands)

    def process(self):
        self.pop("process")
        owner = self.identifier()
        self.pop("{")
        qubits = []
        while self.peek in ("qubit", "qubits", "array", "bit", "bool", "int", "nat", "phase"):
            kind = self.pop()
            declared = self.name_list()
            reserved = {"true", "false", "and", "or", "not", "if", "then", "else", "fi",
                        "do", "od", "skip", "program", "process", "reference", "in"}
            if reserved & set(declared):
                raise self.error("Declarations may not use language keywords as names")
            if kind in ("qubit", "qubits"):
                qubits.extend(declared)
            elif kind == "phase":
                self.parameters.extend(ir.PhaseParameter(name, owner) for name in declared)
            elif kind == "array":
                for name in declared:
                    if name in self.arrays:
                        raise self.error(f"Duplicate array {name}")
                    self.arrays[name] = owner
                    qubits.append(name)
            else:
                if kind == "nat":
                    from .distillation import NaturalVariable
                    self.has_naturals = True
                    self.variables.extend(NaturalVariable(name, owner) for name in declared)
                else:
                    domain = (0, 1) if kind == "bit" else (False, True)
                    if kind == "int":
                        self.pop("in")
                        first = self.integer()
                        self.pop("..")
                        last = self.integer()
                        if last < first or last - first > 255:
                            raise self.error("An integer declaration needs a finite range of at most 256 values")
                        domain = tuple(range(first, last + 1))
                    self.variables.extend(ir.Variable(name, owner, domain) for name in declared)
            self.pop(";")
        initialization = self.block({"do", "}"})
        branches = []
        if self.accept("do"):
            while self.accept("[]"):
                label = f"branch_{len(branches) + 1}"
                if self.index + 1 < len(self.items) and self.items[self.index + 1][0] == ":":
                    label = self.identifier()
                    self.pop(":")
                guard = self.through({";"})
                self.pop(";")
                channel = self.identifier()
                if self.accept("!"):
                    action = ir.Send(channel, self.through({"->"}))
                else:
                    self.pop("?")
                    action = ir.Receive(channel, self.identifier())
                self.pop("->")
                body = self.block({"[]", "od"})
                branches.append(ir.Branch(label, guard, action, body))
            self.pop("od")
            self.accept(";")
        self.pop("}")
        self.processes.append(ir.Process(owner, tuple(qubits), initialization, tuple(branches)))

    def parse(self):
        self.pop("program")
        program_name = self.identifier()
        self.pop("{")
        if self.accept("reference"):
            self.references = self.name_list()
            self.pop(";")
        while self.accept("gate"):
            name = self.identifier()
            self.pop("{")
            cases = []
            while self.peek != "}":
                selector = self.integer()
                self.pop(":")
                matrix = _matrix_literal(self.through({";"}))
                self.pop(";")
                cases.append((selector, matrix))
                if len(cases) > 64:
                    raise self.error("Gate families are limited to 64 exact cases")
            self.pop("}")
            self.families.append(ir.GateFamily(name, tuple(cases)))
        while self.peek == "process":
            self.process()
            if self.accept("||"):
                if self.peek != "process":
                    raise self.error("Expected a parallel process after ||")
            elif self.peek == "process":
                raise self.error("Separate parallel processes with ||")
        self.pop("}")
        if self.peek != "<end>":
            raise self.error("Unexpected text after the program")
        if not self.processes:
            raise self.error("A program needs at least one process")
        return program_name


class Protocol:
    def __init__(self, source):
        if not isinstance(source, str):
            raise SourceError("Define a program with a source string")
        self._source = dedent(source).strip()
        self._parsed = _ProgramParser(self.source)
        self.name = self._parsed.parse()

    @property
    def source(self):
        return self._source

    def __str__(self):
        return self.source

    __repr__ = __str__

    def _repr_html_(self):
        return f"<pre>{escape(self.source)}</pre>"

    def _lower(self, retry=False):
        parsed = self._parsed
        if bool(parsed.arrays or parsed.has_naturals) != retry:
            raise SourceError("Use first_acceptance(...) for the supported unbounded retry schema; verify(...) accepts finite protocols")
        variables = list(parsed.variables)
        if retry:
            from .distillation import NaturalVariable
            variables.append(NaturalVariable("n", "proof"))
            if parsed.parameters or parsed.families:
                raise SourceError("The specialized retry schema does not support extra phase parameters or gate families")
        if len({v.name for v in variables}) != len(variables):
            raise SourceError("Classical variable names must be unique across processes")
        symbols = {v.name: v.symbol for v in variables}
        arrays = {"a_c": "ac", "a_t": "at", "b_c": "bc", "b_t": "bt"}
        if retry and (parsed.arrays != {"a_c": "Alice", "a_t": "Alice", "b_c": "Bob", "b_t": "Bob"} or parsed.references):
            raise SourceError("The retry schema currently requires Alice's a_c/a_t arrays and Bob's b_c/b_t arrays, without references")

        def register(value, owner):
            if not isinstance(value, _Cell):
                if retry:
                    raise SourceError("Every quantum operation in the retry schema must use an indexed array cell")
                return value
            if not retry or value.array not in arrays or parsed.arrays[value.array] != owner:
                raise SourceError(f"Unknown or nonlocal indexed register {value.array}")
            counter = symbols["kA" if owner == "Alice" else "kB"]
            if not z3.is_true(z3.simplify(_formula(value.index, symbols) == counter)):
                raise SourceError("The supported retry schema accesses each local array at its current counter")
            return arrays[value.array]

        def lower_block(block, owner):
            output = []
            for command in block:
                if isinstance(command, ir.Assign):
                    command = ir.Assign(command.target, _formula(command.value, symbols))
                elif isinstance(command, ir.If):
                    command = ir.If(_formula(command.condition, symbols),
                                    lower_block(command.then, owner), lower_block(command.otherwise, owner))
                elif isinstance(command, ir.Gate):
                    parameters = (command.parameters if command.name == "R" else
                                  tuple(_formula(p, symbols) for p in command.parameters))
                    command = ir.Gate(command.name, tuple(register(q, owner) for q in command.targets), parameters)
                elif isinstance(command, ir.Measure):
                    command = ir.Measure(command.target, register(command.qubit, owner))
                elif isinstance(command, ir.Reset) and retry:
                    raise SourceError("Reset is outside the supported unbounded retry schema")
                output.append(command)
            return tuple(output)

        processes = []
        for process in parsed.processes:
            branches = []
            for branch in process.branches:
                action = branch.action
                if isinstance(action, ir.Send):
                    action = ir.Send(action.channel, _formula(action.value, symbols))
                branches.append(ir.Branch(branch.name, _formula(branch.guard, symbols), action,
                                           lower_block(branch.body, process.name)))
            qubits = tuple(arrays[q] for q in process.qubits) if retry else process.qubits
            processes.append(ir.Process(process.name, qubits, lower_block(process.init, process.name), tuple(branches)))
        if retry:
            from .distillation import ControlSchema
            result = ControlSchema(tuple(variables), tuple(processes), name=self.name)
        else:
            registers = tuple(parsed.references) + tuple(q for p in processes for q in p.qubits)
            result = ir.Program(self.name, tuple(variables), registers, tuple(processes), tuple(parsed.references),
                                parameters=tuple(parsed.parameters), gate_families=tuple(parsed.families))
        result.validate()
        return result


def program(source):
    """Define a protocol directly from paper-style source."""
    return Protocol(source)


@dataclass(frozen=True)
class AssertionSpec:
    classical: str
    quantum: str = "I"

    def __str__(self):
        return f"{{ {dedent(self.classical).strip()} ; {dedent(self.quantum).strip()} }}"

    __repr__ = __str__

    def _compile(self, backend):
        symbols = {v.name: v.symbol for v in backend.variables}
        classical = _formula(self.classical, symbols)
        quantum = _quantum_effect(self.quantum, backend, symbols)
        result = Assertion(classical, quantum)
        result.validate(backend)
        return result


def assertion(classical="true", quantum=None):
    """A cq-assertion written as a classical formula and a quantum predicate."""
    if isinstance(classical, str) and classical.strip().startswith("{"):
        if quantum is not None:
            raise SourceError("A braced assertion already contains both parts")
        source = classical.strip()
        if not source.endswith("}") or source[1:-1].count(";") != 1:
            raise SourceError("Write a Hoare assertion as '{ classical ; quantum }'")
        classical, quantum = (part.strip() for part in source[1:-1].split(";", 1))
        if not classical or not quantum:
            raise SourceError("Both parts of a Hoare assertion must be present")
    quantum = "I" if quantum is None else quantum
    if not isinstance(classical, str) or not isinstance(quantum, str):
        raise SourceError("Write assertions as source strings; backend objects are not needed")
    return AssertionSpec(classical, quantum)


def _assertion_spec(value):
    if isinstance(value, AssertionSpec):
        return value
    if isinstance(value, str) and value.strip().startswith("{"):
        return assertion(value)
    raise SourceError("Use '{ classical ; quantum }' or assertion(classical, quantum)")


@dataclass(frozen=True)
class HoareTriple:
    pre: AssertionSpec
    protocol: Protocol
    post: AssertionSpec

    def __str__(self):
        return f"{self.pre}\n{self.protocol.name}\n{self.post}"


class HoareReport(Report):
    """A source triple with a concise result; full obligations remain inspectable."""
    def __init__(self, triple, report, retry=None):
        super().__init__(report.program, report.mode, report.obligations, derivation=report.derivation)
        self.triple = triple
        self._retry = retry

    def __str__(self):
        result = f"{self.triple}\n\n{self.status} ({self.mode})"
        for condition in self.obligations:
            if condition.status != "PASSED":
                result += "\n" + str(condition)
        if self.derivation is not None:
            result += "\n\n" + self.derivation.summary()
        return result

    __repr__ = __str__

    def details(self):
        return Report.__str__(self)

    def explain(self, *, matrices=False):
        if self.derivation is None:
            raise SourceError("This report does not contain a derivation trace")
        return ProofView(self.derivation, matrices=matrices)

    def _repr_html_(self):
        result = f"<pre>{escape(str(self))}</pre>"
        if self.derivation is not None:
            result += "<details><summary>Expand the calculation and intermediate predicates</summary>"
            result += self.derivation.html(expanded=False, include_summary=False) + "</details>"
        return result

    def bounds(self, *, fidelity="4/5", attempts=5):
        if self._retry is None:
            raise SourceError("Probability bounds are provided by the distillation proof rule")
        if not self.verified:
            raise SourceError("Verify the Hoare triple successfully before deriving its bounds")
        values = self._retry.bounds(fidelity=fidelity, attempts=attempts)
        return ProbabilityBounds(self, values)


@dataclass(frozen=True)
class ProbabilityBounds:
    evidence: Report
    values: dict

    @property
    def verified(self):
        return self.evidence.verified

    @property
    def status(self):
        return "VERIFIED" if self.verified else "NOT_VERIFIED"

    def __str__(self):
        v = self.values
        return (f"{self.status}: probability and fidelity bounds\n"
                "Assumption: independent Werner pairs, 1/2 < F < 1, n >= 1.\n"
                "p = F^2 + 2*F*(1-F)/3 + 5*(1-F)^2/9\n"
                "g = F^2 + (1-F)^2/9\n"
                "Pr(accept) >= 1-(1-p)^n\n"
                "Bell overlap of accepted output >= (g/p)*(1-(1-p)^n)\n"
                "lim[n -> infinity] 1-(1-p)^n = 1; g/p > F\n\n"
                f"F = {v['input_fidelity']}, n = {v['proof_horizon']}:\n"
                f"Pr(accept) >= {v['accepted_mass_lower_bound']}\n"
                f"Bell overlap >= {v['bell_overlap_lower_bound']}\n"
                f"g/p = {v['asymptotic_fidelity']}")

    def _repr_html_(self):
        text = f"<pre>{escape(str(self))}</pre>"
        if self.evidence.derivation is not None:
            text += "<details><summary>Expand the bound derivation and its Hoare premises</summary>"
            text += self.evidence.derivation.html(expanded=False) + "</details>"
        return text

    def explain(self, *, matrices=False):
        if self.evidence.derivation is None:
            raise SourceError("No derivation trace was recorded")
        return ProofView(self.evidence.derivation, matrices=matrices)

    __repr__ = __str__


def _quantum_effect(source, backend, symbols):
    try:
        tree = ast.parse(dedent(source).strip().replace("^", "**"), mode="eval").body
    except SyntaxError as error:
        raise SourceError(f"Invalid quantum predicate: {error.msg}") from None
    dimension = 2 ** len(backend.registers)
    identity = sp.ImmutableMatrix(sp.eye(dimension))

    def build(node):
        # Return (kind, classical dependencies, quantum support, evaluator).
        if isinstance(node, ast.Name) and node.id == "I":
            return "effect", set(), set(), lambda state: identity
        if isinstance(node, ast.Constant) and type(node.value) is int and node.value in (0, 1):
            matrix = identity * node.value
            return "effect", set(), set(), lambda state: matrix
        if isinstance(node, ast.Subscript) and isinstance(node.value, (ast.Name, ast.Call)):
            arguments = ()
            if isinstance(node.value, ast.Call):
                call = node.value
                if not isinstance(call.func, ast.Name) or call.keywords:
                    raise SourceError("Use a declared gate or state name with positional parameters")
                name = call.func.id
                arguments = tuple(call.args)
            else:
                name = node.value.id
            values = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
            if not all(isinstance(q, ast.Name) and q.id in backend.registers for q in values):
                raise SourceError("Quantum predicates must name declared qubits")
            targets = tuple(q.id for q in values)
            if len(set(targets)) != len(targets):
                raise SourceError("Quantum predicate registers must be distinct")
            dependencies = set()
            matrix_at = None
            if name in {"R", "Equator"}:
                parameters = {p.name for p in backend.parameters}
                if (len(arguments) != 1 or not isinstance(arguments[0], ast.Name)
                        or arguments[0].id not in parameters or len(targets) != 1):
                    raise SourceError(f"{name} requires one declared phase parameter and one qubit")
                phase = phase_symbol(arguments[0].id)
                matrix = sp.ImmutableMatrix(sp.diag(1, phase)) if name == "R" else projector(sp.Matrix([1, phase]) / sp.sqrt(2))
                kind = "unitary" if name == "R" else "effect"
            elif name in {family.name for family in backend.gate_families}:
                if len(arguments) != 1 or len(targets) != 1:
                    raise SourceError("A gate family requires one classical selector and one qubit")
                selector = _formula(ast.unparse(arguments[0]), symbols)
                if not z3.is_int(selector):
                    raise SourceError("Gate family selectors must be integer expressions")
                dependencies = {str(v) for v in get_vars(selector)}
                command = ir.Gate(name, targets, (selector,))
                matrix_at = lambda state: gate_matrix(command, state, backend)
                kind = "unitary"
            elif name in GATES:
                if arguments:
                    raise SourceError("This primitive gate does not take parameters")
                arity = 2 if name == "CNOT" else 1
                if len(targets) != arity:
                    raise SourceError(f"{name} requires {arity} qubits")
                matrix, kind = GATES[name], "unitary"
            elif name == "Bell" and len(targets) == 2 and not arguments:
                matrix, kind = projector(BELL), "effect"
            elif name == "Zero" and len(targets) == 1 and not arguments:
                matrix, kind = sp.ImmutableMatrix([[1, 0], [0, 0]]), "effect"
            elif name == "Plus" and len(targets) == 1 and not arguments:
                matrix, kind = sp.ImmutableMatrix([[1, 1], [1, 1]]) / 2, "effect"
            else:
                raise SourceError(f"Unknown quantum predicate or wrong arity: {name}")
            indices = tuple(backend.registers.index(q) for q in targets)
            if matrix_at is not None:
                return kind, dependencies, set(targets), lambda state: embed(matrix_at(state), indices, len(backend.registers))
            embedded = embed(matrix, indices, len(backend.registers))
            return kind, dependencies, set(targets), lambda state: embedded
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
            kind, dependencies, support, value = build(node.left)
            if kind != "unitary":
                raise SourceError("Only unitary gates can have a classical exponent")
            exponent = _formula(ast.unparse(node.right), symbols)
            if not z3.is_int(exponent):
                raise SourceError("Gate exponents must be integer expressions")
            dependencies |= {str(v) for v in get_vars(exponent)}

            def powered(state):
                power = evaluate(exponent, state, backend)
                if abs(power) > 64:
                    raise SourceError("Exact gate exponents are limited to absolute value 64")
                return clean(value(state) ** power)

            return kind, dependencies, support, powered
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
            lk, ld, ls, left = build(node.left)
            rk, rd, rs, right = build(node.right)
            if lk == "effect" and rk == "unitary":
                raise SourceError("Write gate application before its predicate: U[q] * A")
            if lk == rk == "effect" and ls & rs:
                raise SourceError("Use * between predicates on disjoint registers")
            kind = "unitary" if lk == rk == "unitary" else "effect"

            def multiplied(state):
                a, b = left(state), right(state)
                return clean(a * b * a.H) if lk == "unitary" and rk == "effect" else clean(a * b)

            return kind, ld | rd, ls | rs, multiplied
        raise SourceError("Use I, Bell[a,b], Zero[q], Plus[q], Equator(alpha)[q], tensor products, and declared unitary applications")

    kind, dependencies, _, value = build(tree)
    if kind != "effect":
        raise SourceError("A quantum assertion needs a predicate after its gates")
    cases = []
    for state in states(backend, True, dependencies, limit=1024):
        condition = z3.And(*[symbols[name] == ir.expr(state[name]) for name in sorted(dependencies)])
        cases.append((condition, clean(value(state))))
    return Effect(dedent(source).strip(), tuple(cases))


def verify(precondition=None, protocol=None, postcondition=None, *, pre=None, post=None,
           invariant=None, decreases=None, **limits):
    """Verify {pre} program {post}, in that order.

    Preferred: verify("{ phi ; A }", program, "{ psi ; B }", ...).
    The earlier verify(program, pre=..., post=...) spelling remains supported.
    """
    if precondition is None and isinstance(protocol, Protocol) and postcondition is None:
        pass  # Earlier fully keyword-based spelling: protocol=..., pre=..., post=...
    elif isinstance(precondition, Protocol):
        if protocol is not None or postcondition is not None:
            raise SourceError("Use verify(precondition, program, postcondition)")
        protocol = precondition
    else:
        if pre is not None or post is not None:
            raise SourceError("Do not mix positional Hoare assertions with pre/post keywords")
        pre, post = precondition, postcondition
    if not isinstance(protocol, Protocol):
        raise SourceError("The middle argument must be a program definition")
    pre, post = _assertion_spec(pre), _assertion_spec(post)
    triple = HoareTriple(pre, protocol, post)
    if protocol._parsed.arrays or protocol._parsed.has_naturals:
        if limits:
            raise SourceError("The unbounded proof rule does not use finite exploration limits")
        return _verify_retry_triple(triple, invariant, decreases)
    backend = protocol._lower()
    initial, final = pre._compile(backend), post._compile(backend)
    if invariant is None:
        if any(p.branches for p in backend.processes):
            raise SourceError("A guarded protocol requires an explicit invariant")
        if decreases is not None:
            raise SourceError("A loop-free program does not need a ranking function")
        from .verifier import check_hoare
        report = Report(backend.name, "loop-free correctness", [check_hoare(backend, initial, backend.initialization, final, **limits)])
        report.derivation = ProofPlan("Local WP / Conseq", "semantic predicate transformers", report)
        return HoareReport(triple, report)
    invariant = _assertion_spec(invariant)
    symbols = {v.name: v.symbol for v in backend.variables}
    rank = None if decreases is None else _formula(decreases, symbols)
    report = verify_distributed(backend, initial, invariant._compile(backend), final, variant=rank, **limits)
    return HoareReport(triple, report)


def _verify_retry_triple(triple, invariant, decreases):
    if invariant is None or decreases is None:
        raise SourceError("Distillation requires its invariant and decreasing rank")
    invariant = _assertion_spec(invariant)
    def syntax(text):
        try:
            return ast.dump(ast.parse(dedent(text).strip(), mode="eval").body)
        except SyntaxError:
            raise SourceError("Malformed quantum expression in the unbounded Hoare triple") from None

    head = syntax(triple.pre.quantum)
    kind = next((kind for kind in ("pass", "good") if head == syntax(f"E_{kind}(0,n)")), None)
    if kind is None:
        raise SourceError("The supported unbounded preconditions are E_pass(0,n) and E_good(0,n)")
    expected_k = f"K_{kind}(kA,mA,mB,n)"
    expected_post = "I" if kind == "pass" else "Bell[a_c[kA],b_c[kB]]"
    if syntax(invariant.quantum) != syntax(expected_k):
        raise SourceError(f"This triple requires quantum invariant {expected_k}")
    if syntax(triple.post.quantum) != syntax(expected_post):
        raise SourceError(f"The supported {kind} postcondition is {expected_post}")
    retry = RetryProof(triple.protocol, invariant.classical, decreases)
    model = retry._model()
    schema, v = model.controller, model.symbols
    # The encoded theorem has classical precondition true, so any well-typed
    # strengthening of it is sound. Do not silently accept malformed formulas.
    schema.validate_expr(_formula(triple.pre.classical, v), boolean=True)
    report = model.verify()
    report.program = triple.protocol.name
    acc = z3.And(v["doneA"], v["doneB"], v["kA"] == v["kB"], v["kA"] < v["n"])
    report.obligations.append(check_implication(schema, acc, _formula(triple.post.classical, v),
                                                "Acceptance entails the requested classical postcondition"))
    return HoareReport(triple, report, retry=retry)


@dataclass(frozen=True)
class ControlTrace:
    lines: tuple[str, ...]
    final_state: dict

    def __str__(self):
        return "\n".join(self.lines)


@dataclass
class RetryProof:
    protocol: Protocol
    invariant: str
    decreases: str

    @property
    def specification(self):
        return ("For every proof horizon n >= 1:\n"
                "  { true ; E_pass(0,n) } " + self.protocol.name + " { doneA and doneB and kA=kB and kA<n ; I }\n"
                "  { true ; E_good(0,n) } " + self.protocol.name + " { doneA and doneB and kA=kB and kA<n ; Bell[a_c[kA],b_c[kB]] }\n"
                "E_kind(r,n) = sum over r <= k < n of (product over r <= j < k of Rej_j) Head_kind,k.\n"
                "Head_pass = Pass; Head_good = Good. The empty suffix is zero.\n"
                "K_kind(k,u,v,n) = 0 if k>=n; accepted target if u=v; E_kind(k+1,n) otherwise.\n"
                "The quantum invariant is K_kind(kA,mA,mB,n).")

    def _model(self):
        from .distillation import Distillation
        schema = self.protocol._lower(retry=True)
        # Extract the actual unconditional test from the displayed initialization,
        # not from an example factory. Retry event matching is checked by the schema.
        tests = []
        variables = []
        for process in schema.processes:
            for command in process.init:
                if isinstance(command, ir.If) and ir.access((command,))[2]:
                    raise SourceError("The retry schema requires an unconditional initial bilateral test")
            test = tuple(c for c in process.init if isinstance(c, (ir.Gate, ir.Measure)))
            tests.append(ir.Process(process.name, process.qubits, test, ()))
            variables.extend(v for v in schema.variables if isinstance(v, ir.Variable) and v.name in {c.target for c in test if isinstance(c, ir.Measure)})
        attempt = ir.Program("Bilateral test from source", tuple(variables), schema.registers, tuple(tests))
        symbols = {v.name: v.symbol for v in schema.variables}
        return Distillation(attempt, schema, _formula(self.invariant, symbols),
                            _formula(self.decreases, symbols), symbols)

    def verify(self):
        report = self._model().verify()
        report.program = self.protocol.name
        return report

    def bounds(self, *, fidelity="4/5", attempts=5):
        # SymPy's broad string parser is not exposed: accept rational literals only.
        if not isinstance(fidelity, str) or not re.fullmatch(r"\d+(?:/\d+)?", fidelity):
            raise SourceError("Write fidelity as an exact rational string such as '4/5'")
        return self._model().bounds(sp.Rational(fidelity), attempts)

    def trace(self, outcomes):
        """Execute actual control bodies for a specified measurement-outcome story.

        This is a control-flow illustration, not a quantum simulation, random
        experiment, or proof. The proof remains the separate verify() call.
        """
        from .distillation import _symbolic_paths
        schema = self._model().controller
        if (not isinstance(outcomes, (list, tuple)) or not outcomes
                or any(not isinstance(pair, (list, tuple)) or len(pair) != 2
                       or any(type(v) is not int or v not in (0, 1) for v in pair) for pair in outcomes)):
            raise SourceError("Supply a nonempty sequence of pairs of measurement bits")
        if outcomes[-1][0] != outcomes[-1][1]:
            raise SourceError("End this control-flow illustration with an agreeing pair")
        state = {v.name: (v.domain[0] if v.domain is not None else 0) for v in schema.variables}
        state["n"] = 1  # A logical parameter, never read by the executable controller.

        def value(expression):
            substitutions = [(v.symbol, ir.expr(state[v.name])) for v in schema.variables]
            result = z3.simplify(z3.substitute(ir.expr(expression), *substitutions))
            if z3.is_true(result) or z3.is_false(result):
                return z3.is_true(result)
            if z3.is_int_value(result):
                return result.as_long()
            raise SourceError("The control trace did not reduce to a concrete value")

        def advance(block):
            for guard, output, events in _symbolic_paths(schema, block):
                if not value(guard):
                    continue
                compatible = True
                for event in events:
                    if event[0] == "measure":
                        index = value(event[2])
                        owner = 0 if event[1] == "A" else 1
                        if index < 0 or index >= len(outcomes) or value(event[5]) != outcomes[index][owner]:
                            compatible = False
                if compatible:
                    updated = {name: value(expression) for name, expression in output.items()}
                    state.update(updated)
                    return
            raise SourceError("These outcomes do not describe an enabled path of the displayed controller")

        advance(schema.initialization)
        lines = ["Control-flow illustration using specified outcomes; no probabilities are being simulated."]
        pairs = list(schema.matching_pairs())
        rounds = 0
        while not value(schema.termination):
            k = state["kA"]
            if k >= len(outcomes) or rounds >= len(outcomes):
                raise SourceError("The supplied story did not terminate within its listed attempts")
            physical_a, physical_b = outcomes[k]
            lines.append(f"Attempt {k}: specified measurement outcomes Alice={physical_a}, Bob={physical_b}; "
                         f"stored records mA={state['mA']}, mB={state['mB']}.")
            for label, guard, block in pairs:
                if not value(guard):
                    raise SourceError("The illustration's message order is not enabled")
                old = state["kA"]
                advance(block)
                alice_branch = label.split(" ↔ ")[0].split(".", 1)[1]
                action = next(b.action for b in schema.processes[0].branches if b.name == alice_branch)
                direction = "Alice -> Bob" if isinstance(action, ir.Send) else "Bob -> Alice"
                lines.append(f"  {direction}: exchange the recorded bit and execute both local bodies.")
                if state["kA"] != old:
                    lines.append(f"  Recorded bits differ: both counters advance to {state['kA']}; send/receive flags are cleared.")
            rounds += 1
            if state["doneA"] and state["doneB"]:
                lines.append(f"  Recorded bits agree: retain the control pair at index {state['kA']}; both loops exit.")
        return ControlTrace(tuple(lines), dict(state))


def first_acceptance(protocol, *, invariant, decreases):
    """Apply the explicitly named, specialized unbounded first-acceptance rule."""
    return RetryProof(protocol, dedent(invariant).strip(), decreases)


def trace_retry(protocol, outcomes):
    """Illustrate this source controller with specified outcomes, without proving it."""
    return RetryProof(protocol, "true", "0").trace(outcomes)
