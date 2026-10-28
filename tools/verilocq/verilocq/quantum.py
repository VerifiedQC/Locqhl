"""Exact matrix algebra. No floating-point acceptance thresholds are used."""

from dataclasses import dataclass
from functools import lru_cache

import sympy as sp
import z3

from .syntax import Unsupported, expr, names


@lru_cache(maxsize=4096)
def _clean(matrix):
    return sp.ImmutableMatrix(matrix.rows, matrix.cols,
                              [sp.simplify(x) for x in matrix])


def clean(matrix):
    return _clean(sp.ImmutableMatrix(matrix))


def projector(ket):
    ket = sp.ImmutableMatrix(ket)
    return clean(ket * ket.H)


def tensor(*matrices):
    return sp.ImmutableMatrix(sp.kronecker_product(*matrices))


I2 = sp.ImmutableMatrix(sp.eye(2))
X = sp.ImmutableMatrix([[0, 1], [1, 0]])
Z = sp.ImmutableMatrix([[1, 0], [0, -1]])
H = sp.ImmutableMatrix([[1, 1], [1, -1]]) / sp.sqrt(2)
CNOT = sp.ImmutableMatrix([[1, 0, 0, 0], [0, 1, 0, 0],
                           [0, 0, 0, 1], [0, 0, 1, 0]])
BELL = sp.ImmutableMatrix([1, 0, 0, 1]) / sp.sqrt(2)
GATES = {"H": H, "X": X, "Z": Z, "CNOT": CNOT}


class UnitPhase(sp.Symbol):
    """A universally quantified complex phase, with exactly z* = 1/z.

    No concrete angle is substituted. The Symbol assumptions deliberately do
    not assert that this number is real or positive.
    """
    def __new__(cls, name):
        return sp.Symbol.__new__(cls, name, zero=False, finite=True)

    def _eval_conjugate(self):
        return 1 / self

    def _eval_Abs(self):
        return sp.S.One


def phase_symbol(name):
    return UnitPhase("phase_" + name)


def gate_matrix(command, state, program):
    if command.name in GATES:
        return GATES[command.name]
    if command.name == "R":
        return sp.ImmutableMatrix(sp.diag(1, phase_symbol(command.parameters[0])))
    families = {family.name: family for family in getattr(program, "gate_families", ())}
    if command.name not in families:
        raise Unsupported(f"Unknown gate: {command.name}")
    selector = evaluate(command.parameters[0], state, program)
    for key, matrix in families[command.name].cases:
        if type(selector) is int and selector == key:
            return sp.ImmutableMatrix(matrix)
    raise Unsupported(f"Gate {command.name} has no case for selector {selector}")


@lru_cache(maxsize=512)
def embed(operator, targets, nqubits):
    """Embed on arbitrary ordered targets; register 0 is the most significant bit."""
    operator = sp.ImmutableMatrix(operator)
    if len(set(targets)) != len(targets) or any(t < 0 or t >= nqubits for t in targets):
        raise Unsupported("Invalid tensor embedding targets")
    if operator.shape != (2 ** len(targets), 2 ** len(targets)):
        raise Unsupported("Operator dimension does not match its targets")
    size = 2 ** nqubits
    result = sp.zeros(size)
    for column in range(size):
        bits = [(column >> (nqubits - 1 - k)) & 1 for k in range(nqubits)]
        local_column = sum(bits[t] << (len(targets) - 1 - k)
                           for k, t in enumerate(targets))
        for local_row in range(2 ** len(targets)):
            value = operator[local_row, local_column]
            if value == 0:
                continue
            output = bits.copy()
            for k, target in enumerate(targets):
                output[target] = (local_row >> (len(targets) - 1 - k)) & 1
            row = sum(bit << (nqubits - 1 - k) for k, bit in enumerate(output))
            result[row, column] += value
    return sp.ImmutableMatrix(result)


@lru_cache(maxsize=4096)
def psd(matrix):
    """Decide PSD by exact Hermitian Schur complements; None means unknown.

    A zero diagonal in a PSD matrix forces its entire row to be zero. A positive
    diagonal allows a Schur-complement reduction. No numerical eigenvalues enter
    the decision. Unknown symbolic signs never count as a proof.
    """
    matrix = clean(matrix)
    hermitian = clean(matrix - matrix.H).is_zero_matrix
    if hermitian is False:
        return False
    if hermitian is None:
        return None
    while matrix.rows:
        positive = None
        for i in range(matrix.rows):
            diagonal = sp.simplify(matrix[i, i])
            if diagonal.is_negative is True:
                return False
            if diagonal.is_zero is True:
                for j in range(matrix.cols):
                    zero = matrix[i, j].is_zero
                    if zero is False:
                        return False
                    if zero is None:
                        return None
            elif diagonal.is_positive is True:
                positive = i
        if positive is None:
            return True if matrix.is_zero_matrix is True else None
        others = [i for i in range(matrix.rows) if i != positive]
        if not others:
            return True
        column = matrix.extract(others, [positive])
        row = matrix.extract([positive], others)
        matrix = clean(matrix.extract(others, others)
                       - column * row / matrix[positive, positive])
    return True


def evaluate(value, state, program):
    value = expr(value)
    substitutions = [(v.symbol, expr(state[v.name])) for v in program.variables]
    result = z3.simplify(z3.substitute(value, *substitutions)) if substitutions else z3.simplify(value)
    if z3.is_true(result):
        return True
    if z3.is_false(result):
        return False
    if z3.is_int_value(result):
        return result.as_long()
    raise Unsupported(f"Expression cannot be evaluated exactly: {result}")


@dataclass(frozen=True)
class Effect:
    """A finite, disjoint classical case split into exact quantum effects."""
    label: str
    cases: tuple

    @classmethod
    def constant(cls, matrix, label="effect"):
        return cls(label, ((z3.BoolVal(True), clean(matrix)),))

    @property
    def dependencies(self):
        return set().union(*(names(c) for c, _ in self.cases))

    def at(self, state, program):
        selected = [matrix for condition, matrix in self.cases
                    if evaluate(condition, state, program)]
        if len(selected) != 1:
            raise Unsupported(f"Effect {self.label!r} does not select exactly one case")
        return sp.ImmutableMatrix(selected[0])

    def validate(self, program):
        if not self.cases:
            raise Unsupported("An effect needs at least one case")
        dimension = 2 ** len(program.registers)
        guards = []
        for condition, raw in self.cases:
            program.validate_expr(condition, boolean=True)
            guards.append(expr(condition))
            matrix = sp.ImmutableMatrix(raw)
            if matrix.shape != (dimension, dimension):
                raise Unsupported(f"Wrong matrix dimension in {self.label}")
            allowed = {phase_symbol(p.name) for p in getattr(program, "parameters", ())}
            if matrix.free_symbols - allowed or any(x.has(sp.Float) for x in matrix):
                raise Unsupported("Use exact entries; only declared unit-phase symbols may remain free")
            if psd(matrix) is not True or psd(clean(sp.eye(dimension) - matrix)) is not True:
                raise Unsupported(f"Could not establish 0 ≤ {self.label} ≤ I exactly")
        solver = program.solver()
        solver.add(z3.Not(z3.Or(*guards)))
        if solver.check() != z3.unsat:
            raise Unsupported(f"Cases of {self.label} do not provably cover the finite domains")
        for i, a in enumerate(guards):
            for b in guards[i + 1:]:
                solver = program.solver()
                solver.add(a, b)
                if solver.check() != z3.unsat:
                    raise Unsupported(f"Overlapping or undecidable cases in {self.label}")


@dataclass(frozen=True)
class Assertion:
    classical: object
    quantum: Effect

    @property
    def dependencies(self):
        return names(self.classical) | self.quantum.dependencies

    def validate(self, program):
        program.validate_expr(self.classical, boolean=True)
        self.quantum.validate(program)

    def at(self, state, program):
        if evaluate(self.classical, state, program):
            return self.quantum.at(state, program)
        return sp.ImmutableMatrix(sp.zeros(2 ** len(program.registers)))
