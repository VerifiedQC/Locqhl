"""Small, explicit Python DSL for the finite fragment of the paper's language."""

from dataclasses import dataclass
from typing import Any

import z3
from z3.z3util import get_vars


class Unsupported(ValueError):
    """The requested program or specification is outside the checked fragment."""


def expr(value):
    if type(value) is bool:
        return z3.BoolVal(value)
    if type(value) is int:
        return z3.IntVal(value)
    if isinstance(value, z3.ExprRef):
        return value
    raise Unsupported(f"Expected a Boolean/integer expression, got {value!r}")


def names(value):
    return {str(v) for v in get_vars(expr(value))}


@dataclass(frozen=True)
class Variable:
    name: str
    owner: str
    domain: tuple

    def __post_init__(self):
        if not self.domain or len(set(self.domain)) != len(self.domain):
            raise Unsupported("Classical variables need a nonempty finite domain")
        kind = type(self.domain[0])
        if kind not in (bool, int) or any(type(v) is not kind for v in self.domain):
            raise Unsupported("Domains must contain only booleans or only integers")

    @property
    def symbol(self):
        return z3.Bool(self.name) if type(self.domain[0]) is bool else z3.Int(self.name)

    def admits(self, value):
        return z3.Or(*[value == expr(v) for v in self.domain])


@dataclass(frozen=True)
class Skip:
    pass


@dataclass(frozen=True)
class Assign:
    target: str
    value: Any


@dataclass(frozen=True)
class Gate:
    name: str
    targets: tuple[str, ...]
    parameters: tuple = ()


@dataclass(frozen=True)
class PhaseParameter:
    name: str
    owner: str


@dataclass(frozen=True)
class StateParameter:
    """An arbitrary normalized vector, used only in assertions."""
    name: str
    qubits: int = 1

    def __post_init__(self):
        if type(self.qubits) is not int or self.qubits not in (1, 2):
            raise Unsupported("State parameters support one or two qubits")


@dataclass(frozen=True)
class GateFamily:
    name: str
    cases: tuple


@dataclass(frozen=True)
class Measure:
    target: str
    qubit: str


@dataclass(frozen=True)
class Reset:
    qubit: str


@dataclass(frozen=True)
class If:
    condition: Any
    then: tuple
    otherwise: tuple = ()


def seq(*commands):
    """Construct a sequential local block; nested blocks are flattened."""
    result = []
    for command in commands:
        result.extend(command if isinstance(command, tuple) else (command,))
    return tuple(result)


@dataclass(frozen=True)
class Send:
    channel: str
    value: Any


@dataclass(frozen=True)
class Receive:
    channel: str
    target: str


@dataclass(frozen=True)
class Branch:
    name: str
    guard: Any
    action: Send | Receive
    body: tuple


@dataclass(frozen=True)
class Process:
    name: str
    qubits: tuple[str, ...]
    init: tuple
    branches: tuple[Branch, ...]


@dataclass(frozen=True)
class Program:
    name: str
    variables: tuple[Variable, ...]
    registers: tuple[str, ...]
    processes: tuple[Process, ...]
    references: tuple[str, ...] = ()
    parameters: tuple[PhaseParameter, ...] = ()
    gate_families: tuple[GateFamily, ...] = ()
    state_parameters: tuple[StateParameter, ...] = ()

    @property
    def varmap(self):
        return {v.name: v for v in self.variables}

    @property
    def domains(self):
        return z3.And(*[z3.Or(*[v.symbol == expr(x) for x in v.domain])
                        for v in self.variables])

    @property
    def initialization(self):
        return seq(*(p.init for p in self.processes))

    @property
    def termination(self):
        return z3.And(*[z3.Not(expr(b.guard)) for p in self.processes
                        for b in p.branches])

    def solver(self):
        solver = z3.Solver()
        solver.set(timeout=10_000)
        solver.add(self.domains)
        return solver

    def validate_expr(self, value, owner=None, boolean=False):
        value = expr(value)
        if boolean and not z3.is_bool(value):
            raise Unsupported("A guard/condition must have Boolean type")
        if not (z3.is_bool(value) or z3.is_int(value)):
            raise Unsupported("Only Boolean and integer classical expressions are supported")
        for symbol in get_vars(value):
            var = self.varmap.get(str(symbol))
            if var is None or not var.symbol.eq(symbol):
                raise Unsupported(f"Undeclared or wrongly typed variable: {symbol}")
            if owner is not None and var.owner != owner:
                raise Unsupported(f"{owner} reads another process's variable {symbol}")
        pending = [value]
        while pending:
            node = pending.pop()
            if z3.is_quantifier(node):
                raise Unsupported("Quantified classical expressions are not supported")
            if z3.is_app(node):
                if node.num_args() and node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                    raise Unsupported("Uninterpreted functions are not supported")
                pending.extend(node.children())

    def validate_block(self, block, owner=None):
        reads, writes, touched = access(block)
        for name in reads | writes:
            var = self.varmap.get(name)
            if var is None or (owner is not None and var.owner != owner):
                raise Unsupported(f"Undeclared or nonlocal classical variable: {name}")
        allowed = set(self.registers) - set(self.references)
        if owner is not None:
            allowed = set(next(p for p in self.processes if p.name == owner).qubits)
        if not touched <= allowed:
            raise Unsupported(f"Undeclared, reference, or nonlocal qubits: {touched - allowed}")
        for command in block:
            if isinstance(command, Assign):
                self.validate_expr(command.value, owner)
                if not expr(command.value).sort().eq(self.varmap[command.target].symbol.sort()):
                    raise Unsupported(f"Assignment type mismatch at {command.target}")
            elif isinstance(command, Gate):
                arity = {"H": 1, "X": 1, "Z": 1, "CNOT": 2}.get(command.name)
                if command.name == "R":
                    arity = 1
                    phase_map = {p.name: p for p in getattr(self, "parameters", ())}
                    if len(command.parameters) != 1 or command.parameters[0] not in phase_map:
                        raise Unsupported("R requires one declared read-only phase parameter")
                    parameter = phase_map[command.parameters[0]]
                    if owner is not None and parameter.owner != owner:
                        raise Unsupported("A process may only read its own phase parameters")
                elif command.name in {f.name for f in getattr(self, "gate_families", ())}:
                    arity = 1
                    if len(command.parameters) != 1 or not z3.is_int(expr(command.parameters[0])):
                        raise Unsupported("A gate family requires one integer selector")
                    self.validate_expr(command.parameters[0], owner)
                elif command.parameters:
                    raise Unsupported("This primitive gate has no parameters")
                if arity is None or len(command.targets) != arity:
                    raise Unsupported(f"Unsupported gate/arity: {command}")
                if len(set(command.targets)) != arity:
                    raise Unsupported("Gate targets must be distinct")
            elif isinstance(command, Measure):
                if type(self.varmap[command.target].domain[0]) is not int:
                    raise Unsupported("Computational measurement requires an integer target")
                if not {0, 1} <= set(self.varmap[command.target].domain):
                    raise Unsupported("Measurement target must admit outcomes 0 and 1")
            elif isinstance(command, If):
                self.validate_expr(command.condition, owner, boolean=True)
                self.validate_block(command.then, owner)
                self.validate_block(command.otherwise, owner)
            elif not isinstance(command, (Skip, Reset)):
                raise Unsupported(f"Unsupported command: {command!r}")

    def validate(self):
        if not self.processes or not self.registers:
            raise Unsupported("At least one process and one qubit are required")
        if len(self.registers) > 6:
            raise Unsupported("This prototype is limited to six total qubits")
        for items, label in (([v.name for v in self.variables], "variable"),
                             ([p.name for p in self.processes], "process"),
                             (self.registers, "register")):
            if len(items) != len(set(items)):
                raise Unsupported(f"Duplicate {label} names")
        owners = {p.name for p in self.processes}
        if any(v.owner not in owners for v in self.variables):
            raise Unsupported("Every classical variable needs a declared process owner")
        parameter_names = [p.name for p in self.parameters]
        if len(parameter_names) != len(set(parameter_names)) or set(parameter_names) & set(self.varmap):
            raise Unsupported("Phase parameters must have distinct names, separate from finite variables")
        if any(p.owner not in owners for p in self.parameters):
            raise Unsupported("Every phase parameter needs a declared process owner")
        state_names = [p.name for p in self.state_parameters]
        if (len(state_names) != len(set(state_names))
                or set(state_names) & (set(self.varmap) | set(parameter_names) | set(self.registers))):
            raise Unsupported("State parameters must have distinct names, separate from variables, phases and qubits")
        family_names = [f.name for f in self.gate_families]
        if len(family_names) != len(set(family_names)) or set(family_names) & {"H", "X", "Z", "CNOT", "R"}:
            raise Unsupported("Gate family names must be distinct and may not replace primitive gates")
        from .quantum import clean
        import sympy as sp
        for family in self.gate_families:
            keys = [key for key, _ in family.cases]
            if not keys or len(keys) != len(set(keys)) or any(type(k) is not int for k in keys):
                raise Unsupported("Gate families require distinct integer cases")
            for _, raw in family.cases:
                matrix = sp.ImmutableMatrix(raw)
                if (matrix.shape != (2, 2) or matrix.free_symbols
                        or any(x.has(sp.Float) for x in matrix)
                        or clean(matrix.H * matrix) != sp.eye(2)):
                    raise Unsupported("Each gate family case must be an exact one-qubit unitary")
        allocated = [q for p in self.processes for q in p.qubits] + list(self.references)
        if len(allocated) != len(set(allocated)) or set(allocated) != set(self.registers):
            raise Unsupported("Every qubit needs exactly one process or reference owner")
        for process in self.processes:
            self.validate_block(process.init, process.name)
            if len({b.name for b in process.branches}) != len(process.branches):
                raise Unsupported("Branch names must be unique within a process")
            for branch in process.branches:
                self.validate_expr(branch.guard, process.name, boolean=True)
                self.validate_block(branch.body, process.name)
                if isinstance(branch.action, Send):
                    self.validate_expr(branch.action.value, process.name)
                elif isinstance(branch.action, Receive):
                    var = self.varmap.get(branch.action.target)
                    if var is None or var.owner != process.name:
                        raise Unsupported("Receive target must belong to its receiving process")
                else:
                    raise Unsupported("Only synchronous classical send/receive is supported")
        # A channel may be used by several branches, but all uses must agree on type.
        channels = {}
        for process in self.processes:
            for branch in process.branches:
                action = branch.action
                sort = (expr(action.value).sort() if isinstance(action, Send)
                        else self.varmap[action.target].symbol.sort())
                if action.channel in channels and not channels[action.channel].eq(sort):
                    raise Unsupported(f"Channel type mismatch: {action.channel}")
                channels[action.channel] = sort

    def matching_pairs(self):
        """One canonical order per pair, as in the paper's Distributed rule."""
        for i, left in enumerate(self.processes):
            for right in self.processes[i + 1:]:
                for a in left.branches:
                    for b in right.branches:
                        if a.action.channel != b.action.channel:
                            continue
                        if isinstance(a.action, Send) and isinstance(b.action, Receive):
                            send, receive = a.action, b.action
                        elif isinstance(b.action, Send) and isinstance(a.action, Receive):
                            send, receive = b.action, a.action
                        else:
                            continue
                        effect = Assign(receive.target, send.value)
                        yield (f"{left.name}.{a.name} ↔ {right.name}.{b.name}",
                               z3.And(expr(a.guard), expr(b.guard)),
                               seq(effect, a.body, b.body))


def access(block):
    reads, writes, qubits = set(), set(), set()
    for command in block:
        if isinstance(command, Assign):
            reads |= names(command.value)
            writes.add(command.target)
        elif isinstance(command, Measure):
            writes.add(command.target)
            qubits.add(command.qubit)
        elif isinstance(command, Reset):
            qubits.add(command.qubit)
        elif isinstance(command, Gate):
            qubits.update(command.targets)
            if command.name != "R":
                for parameter in command.parameters:
                    reads |= names(parameter)
        elif isinstance(command, If):
            reads |= names(command.condition)
            for branch in (command.then, command.otherwise):
                r, w, q = access(branch)
                reads |= r
                writes |= w
                qubits |= q
        elif not isinstance(command, Skip):
            raise Unsupported(f"Unsupported command: {command!r}")
    return reads, writes, qubits


def live_before(block, needed_after):
    """Classical inputs affecting execution or an observed output expression."""
    live = set(needed_after)
    for command in reversed(block):
        if isinstance(command, Assign):
            live.discard(command.target)
            # Evaluate even unused assignments, to detect a finite-domain escape.
            live |= names(command.value)
        elif isinstance(command, Measure):
            live.discard(command.target)
        elif isinstance(command, Gate) and command.name != "R":
            for parameter in command.parameters:
                live |= names(parameter)
        elif isinstance(command, If):
            live = (names(command.condition) | live_before(command.then, live)
                    | live_before(command.otherwise, live))
    return live
