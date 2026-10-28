"""Typed indexed operators and replayable proofs for finite tensor families.

The generator is separate from the checker. The checker knows linear tensor
algebra, finite-sum/product rules, local Kraus pullbacks and interval induction;
it does not know BBPSSW, Bell states, or any particular controller. No global
matrix is constructed. This is a Python proof kernel, not a Rocq certificate.
"""

from dataclasses import dataclass
from functools import lru_cache
from itertools import product

import sympy as sp
import z3

from .quantum import clean, psd
from .syntax import Unsupported


def index(value):
    value = sp.sympify(value)
    if value.has(sp.Float) or value.is_integer is not True:
        raise Unsupported("An array index must be an exact integer expression")
    return sp.expand(value)


@dataclass(frozen=True)
class Term:
    kind: str
    args: tuple

    def __post_init__(self):
        arities={"I":2,"0":2,"var":3,"call":3,"local":2,"product":3,
                 "add":2,"sub":2,"sum":4,"pullback":3}
        if (self.kind not in arities and self.kind!="tensor"
                or not isinstance(self.args,tuple)
                or self.kind=="tensor" and not self.args
                or self.kind in arities and len(self.args)!=arities[self.kind]):
            raise Unsupported("Malformed indexed operator syntax")
        slots={"I":(0,1),"0":(0,1),"var":(1,2),"call":(1,2),"local":(1,),
               "product":(1,2),"sum":(1,2),"pullback":(1,)}.get(self.kind,())
        if any(not isinstance(self.args[i],sp.Expr) or self.args[i].is_integer is not True or self.args[i].has(sp.Float) for i in slots):
            raise Unsupported("An indexed operator has an invalid integer index")
        if self.kind in ("add","sub","tensor") and not all(isinstance(a,Term) for a in self.args):
            raise Unsupported("An operator connective needs operator arguments")
        if self.kind in ("local","product","var","pullback") and (not isinstance(self.args[0],str) or not self.args[0]):
            raise Unsupported("An indexed operator needs a name")
        if self.kind=="call" and not isinstance(self.args[0],IndexedFamily):
            raise Unsupported("An indexed call needs a family definition")
        if self.kind=="sum" and (not isinstance(self.args[0],sp.Symbol) or self.args[0].is_integer is not True or not isinstance(self.args[3],Term)):
            raise Unsupported("Malformed finite sum")
        if self.kind=="pullback" and not isinstance(self.args[2],Term):
            raise Unsupported("A pullback needs an operator argument")

    @property
    def space(self):
        a = self.args
        if self.kind in ("I", "0", "var", "call"):
            return a[-2:]
        if self.kind == "local":
            return a[1], a[1]+1
        if self.kind == "product":
            return a[1:]
        if self.kind in ("add", "sub"):
            return a[0].space
        if self.kind == "tensor":
            return a[0].space[0], a[-1].space[1]
        if self.kind == "sum":
            return a[3].space
        if self.kind == "pullback":
            return a[2].space
        raise Unsupported(f"Unknown indexed operator: {self.kind}")

    def __str__(self):
        a = self.args
        if self.kind in ("I", "0"):
            return f"{self.kind}[{a[0]}:{a[1]}]"
        if self.kind == "local":
            return f"{a[0]}[{a[1]}]"
        if self.kind == "var":
            return f"{a[0]}[{a[1]}:{a[2]}]"
        if self.kind == "call":
            return f"{a[0].name}({a[1]},{a[2]})"
        if self.kind == "product":
            return f"tensor_{{j={a[1]}..{a[2]}-1}} {a[0]}[j]"
        if self.kind in ("add", "sub"):
            return f"({a[0]} {'+' if self.kind == 'add' else '-'} {a[1]})"
        if self.kind == "tensor":
            return "(" + " tensor ".join(map(str, a)) + ")"
        if self.kind == "sum":
            return f"sum_{{{a[0]}={a[1]}..{a[2]}-1}} {a[3]}"
        if self.kind == "pullback":
            return f"{a[0]}[{a[1]}]^dagger ({a[2]}) {a[0]}[{a[1]}]"
        return repr(self)


def identity(lo, hi):
    return Term("I", (index(lo), index(hi)))


def zero(lo, hi):
    return Term("0", (index(lo), index(hi)))


def local(name, at):
    return Term("local", (name, index(at)))


def variable(name, lo, hi):
    return Term("var", (name, index(lo), index(hi)))


def add(left, right):
    return Term("add", (left, right))


def subtract(left, right):
    return Term("sub", (left, right))


def tensor(*parts):
    if not parts:
        raise Unsupported("An empty tensor needs an explicit identity interval")
    return Term("tensor", tuple(parts))


def tensor_product(name, lo, hi):
    return Term("product", (name, index(lo), index(hi)))


def finite_sum(binder, lo, hi, body):
    if not isinstance(binder, sp.Symbol) or binder.is_integer is not True:
        raise Unsupported("A finite sum needs an integer binder")
    return Term("sum", (binder, index(lo), index(hi), body))


def pullback(name, at, target):
    return Term("pullback", (name, index(at), target))


def symbols(term):
    result = set()
    for a in term.args:
        if isinstance(a, Term):
            result.update(symbols(a))
        elif isinstance(a, sp.Basic):
            result.update(a.free_symbols)
    if term.kind == "sum":
        result.discard(term.args[0])
    return result


def substitute(term, mapping):
    """Capture-avoiding substitution of affine integer indices."""
    if term.kind == "sum":
        binder, lo, hi, body = term.args
        inner = {k: v for k, v in mapping.items() if k != binder}
        if any(binder in sp.sympify(v).free_symbols for v in inner.values()):
            fresh = sp.Dummy(binder.name, integer=True)
            body = substitute(body, {binder: fresh})
            binder = fresh
        return finite_sum(binder, lo.subs(mapping, simultaneous=True),
                          hi.subs(mapping, simultaneous=True), substitute(body, inner))
    args = tuple(substitute(a, mapping) if isinstance(a, Term) else
                 index(a.subs(mapping, simultaneous=True)) if isinstance(a, sp.Basic) else a
                 for a in term.args)
    return Term(term.kind, args)


@dataclass(frozen=True)
class IndexedFamily:
    name: str
    start: sp.Symbol
    end: sp.Symbol
    body: Term

    def __post_init__(self):
        if (not isinstance(self.start, sp.Symbol) or not isinstance(self.end, sp.Symbol)
                or self.start == self.end or self.start.is_integer is not True
                or self.end.is_integer is not True):
            raise Unsupported("An indexed family needs two distinct integer parameters")
        if symbols(self.body) - {self.start, self.end}:
            raise Unsupported("An indexed definition has an unbound index")

    def __call__(self, lo, hi):
        return Term("call", (self, index(lo), index(hi)))

    def unfold(self, lo, hi):
        return substitute(self.body, {self.start: index(lo), self.end: index(hi)})


@lru_cache(maxsize=128)
def first_acceptance(name, head, rejection):
    """A convenience definition, not an axiom or a proof rule."""
    k, n = sp.symbols("k n", integer=True)
    i = sp.Dummy("i", integer=True)
    body = tensor(tensor_product(rejection, k, i), local(head, i), identity(i+1, n))
    return IndexedFamily(name, k, n, finite_sum(i, k, n, body))


@dataclass(frozen=True)
class Equality:
    rule: str
    left: Term
    right: Term
    premises: tuple = ()
    path: tuple = ()


@dataclass(frozen=True)
class Positive:
    rule: str
    term: Term
    premises: tuple = ()


@dataclass(frozen=True)
class Induction:
    family: IndexedFamily
    base: Equality
    step: Equality
    lower: Positive
    upper_equality: Equality
    upper: Positive


class Kernel:
    """Recheck proof objects using only fixed, protocol-independent rules."""
    def __init__(self, matrices, maps=None):
        self.matrices = {name: clean(value) for name, value in matrices.items()}
        if not self.matrices:
            raise Unsupported("Indexed operators need at least one local matrix")
        self.dimension = next(iter(self.matrices.values())).rows
        if self.dimension < 1:
            raise Unsupported("A local operator space must have positive dimension")
        self.maps = {name: clean(value) for name, value in (maps or {}).items()}
        for matrix in (*self.matrices.values(), *self.maps.values()):
            if (matrix.shape != (self.dimension, self.dimension)
                    or matrix.free_symbols or matrix.has(sp.Float)):
                raise Unsupported("Local indexed matrices must be square, exact and share a dimension")
        self.steps = []
        self._conditions = set()
        self._validated = set()

    @staticmethod
    def budget(root):
        pending,depths = [(root,0)],{}
        while pending:
            item,depth = pending.pop()
            if depth > 96 or len(depths) > 16384:
                raise Unsupported("Indexed proof size/depth budget exceeded")
            if depth <= depths.get(id(item),-1):
                continue
            depths[id(item)] = depth
            if isinstance(item,Term):
                children = (a for a in item.args if isinstance(a,(Term,IndexedFamily)))
            elif isinstance(item,Equality):
                children = (item.left,item.right,*item.premises)
            elif isinstance(item,Positive):
                children = (item.term,*item.premises)
            elif isinstance(item,IndexedFamily):
                children = (item.body,)
            else:
                children = ()
            pending.extend((child,depth+1) for child in children)

    def define(self, name, matrix):
        matrix = clean(matrix)
        if matrix.shape != (self.dimension,self.dimension) or matrix.free_symbols or matrix.has(sp.Float):
            raise Unsupported("A local definition must be an exact matrix of the declared dimension")
        if name in self.matrices and self.matrices[name] != matrix:
            raise Unsupported(f"Conflicting local definition: {name}")
        self.matrices[name] = matrix

    def require(self, condition, context):
        key = (condition,tuple(context))
        if key in self._conditions:
            return
        def arithmetic(e):
            if e.is_Integer:
                return z3.IntVal(int(e))
            if isinstance(e, sp.Symbol) and e.is_integer is True:
                return z3.Int(sp.srepr(e))
            if isinstance(e, sp.Add):
                return sum((arithmetic(a) for a in e.args), z3.IntVal(0))
            if isinstance(e, sp.Mul):
                factors = [a for a in e.args if not a.is_Integer]
                if len(factors) <= 1:
                    coefficient = sp.prod(a for a in e.args if a.is_Integer)
                    return int(coefficient) * (arithmetic(factors[0]) if factors else 1)
            raise Unsupported(f"Unsupported index arithmetic: {e}")
        def logic(e):
            if e is sp.true or e is True:
                return z3.BoolVal(True)
            if e is sp.false or e is False:
                return z3.BoolVal(False)
            operators = {sp.Equality: lambda a,b: a == b, sp.LessThan: lambda a,b: a <= b,
                         sp.StrictLessThan: lambda a,b: a < b, sp.GreaterThan: lambda a,b: a >= b,
                         sp.StrictGreaterThan: lambda a,b: a > b}
            if type(e) not in operators:
                raise Unsupported(f"Unsupported index side condition: {e}")
            return operators[type(e)](arithmetic(e.lhs), arithmetic(e.rhs))
        solver = z3.Solver()
        solver.set(timeout=10_000)
        solver.add(*(logic(c) for c in context), z3.Not(logic(condition)))
        answer = solver.check()
        if answer != z3.unsat:
            raise Unsupported(f"Unproved index condition: {condition} ({answer})")
        self._conditions.add(key)

    def same_space(self, left, right, context):
        for a, b in zip(left, right):
            self.require(sp.Eq(a, b), context)

    def validate(self, term, context):
        if not isinstance(term,Term):
            raise Unsupported("An indexed operator expression is required")
        key = (term,tuple(context))
        if key not in self._validated:
            self._validate(term,context)
            self._validated.add(key)

    def _validate(self, term, context):
        a = term.args
        if term.kind in ("I", "0", "var", "call", "product"):
            lo, hi = term.space
            self.require(lo >= 0, context)
            self.require(lo <= hi, context)
            if term.kind == "product" and a[0] not in self.matrices:
                raise Unsupported(f"Unknown local operator {a[0]}")
            if term.kind == "call":
                # Definition bodies are checked when unfolded, never accepted as equations.
                if not isinstance(a[0], IndexedFamily):
                    raise Unsupported("An indexed call needs a definition")
        elif term.kind == "local":
            if a[0] not in self.matrices:
                raise Unsupported(f"Unknown local operator {a[0]}")
            self.require(a[1] >= 0, context)
        elif term.kind in ("add", "sub"):
            self.validate(a[0], context)
            self.validate(a[1], context)
            self.same_space(a[0].space, a[1].space, context)
        elif term.kind == "tensor":
            for part in a:
                self.validate(part, context)
            for left, right in zip(a, a[1:]):
                self.require(sp.Eq(left.space[1], right.space[0]), context)
        elif term.kind == "sum":
            binder, lo, hi, body = a
            if any(binder in sp.sympify(c).free_symbols for c in context):
                raise Unsupported("A sum binder must be fresh in the surrounding proof context")
            self.require(lo >= 0, context)
            self.require(lo <= hi, context)
            if binder in lo.free_symbols | hi.free_symbols:
                raise Unsupported("A sum binder occurs in its own bounds")
            self.validate(body, (*context, binder >= lo, binder < hi))
            if any(binder in endpoint.free_symbols for endpoint in body.space):
                raise Unsupported("Summands must act on the same register interval")
        elif term.kind == "pullback":
            name, at, target = a
            if name not in self.maps:
                raise Unsupported(f"Unknown local Kraus operator {name}")
            self.validate(target, context)
            self.require(sp.Eq(target.space[0], at), context)
            self.require(at+1 <= target.space[1], context)
        else:
            raise Unsupported(f"Unknown indexed operator {term.kind}")

    def _normal(self, term):
        """Tensor linearity with exact local matrix-unit coefficients."""
        def combine(left, right, sign=1):
            result = dict(left)
            for word, coefficient in right.items():
                result[word] = sp.simplify(result.get(word, 0) + sign*coefficient)
                if result[word] == 0:
                    del result[word]
            return result
        if term.kind == "0":
            return {}
        if term.kind in ("add", "sub"):
            return combine(self._normal(term.args[0]), self._normal(term.args[1]),
                           1 if term.kind == "add" else -1)
        if term.kind == "tensor":
            result = {(): sp.S.One}
            for part in term.args:
                following = {}
                for left,a in result.items():
                    for right,b in self._normal(part).items():
                        word = left+right
                        following[word] = sp.simplify(following.get(word,0)+a*b)
                result = {word:a for word,a in following.items() if a != 0}
                if len(result) > 65536:
                    raise Unsupported("Indexed algebra expansion budget exceeded")
            return result
        if term.kind == "I" and sp.expand(term.args[1]-term.args[0]) == 0:
            return {(): sp.S.One}
        if term.kind == "local" or (term.kind == "I" and sp.expand(term.args[1]-term.args[0]) == 1):
            matrix = self.matrices[term.args[0]] if term.kind == "local" else sp.eye(self.dimension)
            at = term.args[1] if term.kind == "local" else term.args[0]
            return {(("entry", at, r, c),): matrix[r,c] for r,c in product(range(self.dimension), repeat=2)
                    if matrix[r,c] != 0}
        return {(("opaque", term),): sp.S.One}

    def _equal(self, left, right):
        return self._normal(subtract(left, right)) == {}

    def check(self, proof, context, depth=0):
        if not isinstance(proof, Equality) or depth > 128:
            raise Unsupported("Invalid or excessively deep equality proof")
        if depth == 0:
            self.budget(proof)
        self.validate(proof.left, context)
        self.validate(proof.right, context)
        self.same_space(proof.left.space, proof.right.space, context)
        left, right, p = proof.left, proof.right, proof.premises
        rule = proof.rule
        if rule == "Trans":
            if len(p) != 2 or (p[0].left, p[0].right, p[1].right) != (left, p[1].left, right):
                raise Unsupported("Invalid transitivity links")
            for child in p:
                self.check(child, context, depth+1)
        elif rule == "Symm":
            if len(p) != 1 or (p[0].right, p[0].left) != (left, right):
                raise Unsupported("Invalid symmetry links")
            self.check(p[0], context, depth+1)
        elif rule == "Congruence":
            if len(p) != 1 or not proof.path:
                raise Unsupported("Congruence needs one subproof and a path")
            current_l, current_r, inner = left, right, tuple(context)
            for slot in proof.path:
                if current_l.kind != current_r.kind or len(current_l.args) != len(current_r.args):
                    raise Unsupported("Congruence changes the surrounding expression")
                if type(slot) is not int or not 0 <= slot < len(current_l.args):
                    raise Unsupported("Invalid congruence path")
                if any(a != b for j,(a,b) in enumerate(zip(current_l.args, current_r.args)) if j != slot):
                    raise Unsupported("Congruence changes an unrelated argument")
                if current_l.kind == "sum" and slot == 3:
                    binder, lo, hi, _ = current_l.args
                    inner += (binder >= lo, binder < hi)
                current_l, current_r = current_l.args[slot], current_r.args[slot]
                if not isinstance(current_l, Term) or not isinstance(current_r, Term):
                    raise Unsupported("Congruence must replace an operator")
            if (p[0].left, p[0].right) != (current_l, current_r):
                raise Unsupported("Congruence subproof has the wrong endpoints")
            self.check(p[0], inner, depth+1)
        else:
            if p:
                raise Unsupported(f"Unexpected premises for {rule}")
            valid = False
            if rule == "Definition" and left.kind == "call":
                family, lo, hi = left.args
                valid = right == family.unfold(lo, hi)
            elif rule == "Sum-Empty" and left.kind == "sum":
                _, lo, hi, _ = left.args
                self.require(sp.Eq(lo, hi), context)
                valid = right == zero(*left.space)
            elif rule == "Sum-Head" and left.kind == "sum":
                binder, lo, hi, body = left.args
                self.require(lo < hi, context)
                valid = right == add(substitute(body, {binder: lo}), finite_sum(binder, lo+1, hi, body))
            elif rule == "Product-Empty" and left.kind == "product":
                _, lo, hi = left.args
                self.require(sp.Eq(lo, hi), context)
                valid = right == identity(lo, hi)
            elif rule == "Product-Head" and left.kind == "product":
                name, lo, hi = left.args
                self.require(lo < hi, context)
                valid = right == tensor(local(name, lo), tensor_product(name, lo+1, hi))
            elif rule == "Sum-Factor" and left.kind == "sum":
                binder, lo, hi, body = left.args
                if body.kind == "tensor" and len(body.args) == 2:
                    prefix, rest = body.args
                    valid = binder not in symbols(prefix) and right == tensor(prefix, finite_sum(binder, lo, hi, rest))
            elif rule == "Identity-Split" and left.kind == "I" and right.kind == "tensor" and len(right.args) == 2:
                a,b = right.args
                valid = a.kind == b.kind == "I" and a.space[0] == left.space[0] and b.space[1] == left.space[1] and a.space[1] == b.space[0]
            elif rule == "Frame" and left.kind == "pullback" and right.kind == "tensor":
                name, at, target = left.args
                if target.kind == "tensor" and len(target.args) == len(right.args) == 2:
                    before, tail = target.args
                    after, rest = right.args
                    valid = (before.kind == after.kind == "local" and before.args[1] == after.args[1] == at
                             and tail == rest and clean(self.maps[name].H*self.matrices[before.args[0]]*self.maps[name]) == self.matrices[after.args[0]])
            elif rule in ("Tensor-Linearity", "Branch-Accum"):
                valid = self._equal(left, right)
            if not valid:
                raise Unsupported(f"Invalid indexed proof step [{rule}]: {left} = {right}")
        self.steps.append((rule, left, right))
        return True

    def positive(self, proof, context, hypothesis=None, depth=0):
        if not isinstance(proof, Positive) or depth > 128:
            raise Unsupported("A positivity proof is required")
        if depth == 0:
            self.budget(proof)
        term, children = proof.term, proof.premises
        self.validate(term, context)
        valid = False
        if proof.rule == "Local-PSD" and term.kind == "local" and not children:
            valid = psd(self.matrices[term.args[0]]) is True
        elif proof.rule in ("Identity-PSD", "Zero-PSD") and not children:
            valid = term.kind == ("I" if proof.rule == "Identity-PSD" else "0")
        elif proof.rule in ("Sum-PSD", "Tensor-PSD"):
            valid = term.kind == ("add" if proof.rule == "Sum-PSD" else "tensor") and tuple(c.term for c in children) == term.args
            if valid:
                for child in children:
                    self.positive(child, context, hypothesis,depth+1)
        elif proof.rule == "Induction-Hypothesis" and not children:
            valid = hypothesis is not None and term == hypothesis
        elif proof.rule == "Complement-Hypothesis" and not children:
            valid = hypothesis is not None and term == subtract(identity(*hypothesis.space), hypothesis)
        if not valid:
            raise Unsupported(f"Invalid positivity proof [{proof.rule}]: {term}")
        self.steps.append((proof.rule, zero(*term.space), term))
        return True

    def induction(self, proof):
        if not isinstance(proof, Induction):
            raise Unsupported("An interval induction proof is required")
        family = proof.family
        k,n = family.start, family.end
        base_context, step_context = (n >= 0,), (k >= 0, k < n)
        if (proof.base.left, proof.base.right) != (family(n,n), zero(n,n)):
            raise Unsupported("Induction base has the wrong family or interval")
        if proof.step.left != family(k,n) or proof.lower.term != proof.step.right:
            raise Unsupported("Induction step has the wrong family or lower bound")
        if proof.upper_equality.left != subtract(identity(k,n), proof.step.right) or proof.upper.term != proof.upper_equality.right:
            raise Unsupported("Induction step has the wrong upper bound")
        self.check(proof.base, base_context)
        self.check(proof.step, step_context)
        hypothesis = family(k+1,n)
        self.require(n-(k+1) >= 0, step_context)
        self.require(n-(k+1) < n-k, step_context)
        self.positive(proof.lower, step_context, hypothesis)
        self.check(proof.upper_equality, step_context)
        self.positive(proof.upper, step_context, hypothesis)
        self.steps.append(("Interval-Induction", zero(k,n), family(k,n)))
        return True


def trans(*steps):
    result = steps[0]
    for following in steps[1:]:
        result = Equality("Trans", result.left, following.right, (result, following))
    return result


def congruence(left, right, path, proof):
    return Equality("Congruence", left, right, (proof,), tuple(path))


def recurrence(family):
    """Generate, but do not trust, a sum/product recurrence derivation."""
    k,n = family.start, family.end
    expanded = family.unfold(k,n)
    if expanded.kind != "sum":
        raise Unsupported("The recurrence generator requires a finite sum")
    i,lo,hi,body = expanded.args
    if (lo,hi) != (k,n) or body.kind != "tensor" or len(body.args) != 3:
        raise Unsupported("Unsupported recurrence shape")
    prefix,head,tail = body.args
    if (prefix.kind != "product" or prefix.space != (k,i) or head.kind != "local"
            or head.args[1] != i or tail != identity(i+1,n)):
        raise Unsupported("Unsupported first-hit summand")
    rejection = prefix.args[0]
    split = add(substitute(body, {i:k}), finite_sum(i,k+1,n,body))
    p0 = Equality("Definition", family(k,n), expanded)
    p1 = Equality("Sum-Head", expanded, split)
    raw_head = split.args[0]
    head_identity = tensor(identity(k,k), local(head.args[0],k), identity(k+1,n))
    p2 = congruence(raw_head, head_identity, (0,), Equality("Product-Empty", raw_head.args[0], identity(k,k)))
    final_head = tensor(local(head.args[0],k), identity(k+1,n))
    p3 = Equality("Tensor-Linearity", head_identity, final_head)
    head_step = trans(p2,p3)
    after_head = add(final_head, split.args[1])
    p4 = congruence(split, after_head, (0,), head_step)
    product_step = Equality("Product-Head", prefix, tensor(local(rejection,k), tensor_product(rejection,k+1,i)))
    expanded_body = tensor(product_step.right, head, tail)
    body_p0 = congruence(body, expanded_body, (0,), product_step)
    rest_body = tensor(tensor_product(rejection,k+1,i), head, tail)
    factored_body = tensor(local(rejection,k), rest_body)
    body_p1 = Equality("Tensor-Linearity", expanded_body, factored_body)
    raw_tail = split.args[1]
    rewritten_tail = finite_sum(i,k+1,n,factored_body)
    tail_p0 = congruence(raw_tail, rewritten_tail, (3,), trans(body_p0,body_p1))
    factored_tail = tensor(local(rejection,k), finite_sum(i,k+1,n,rest_body))
    tail_p1 = Equality("Sum-Factor", rewritten_tail, factored_tail)
    tail_definition = Equality("Definition", family(k+1,n), family.unfold(k+1,n))
    tail_p2 = congruence(factored_tail, tensor(local(rejection,k), family(k+1,n)), (1,),
                         Equality("Symm", tail_definition.right, tail_definition.left, (tail_definition,)))
    final = add(final_head, tail_p2.right)
    p5 = congruence(after_head, final, (1,), trans(tail_p0,tail_p1,tail_p2))
    return trans(p0,p1,p4,p5)


def positivity(term, hypothesis=None):
    if term == hypothesis:
        return Positive("Induction-Hypothesis", term)
    if hypothesis is not None and term == subtract(identity(*hypothesis.space), hypothesis):
        return Positive("Complement-Hypothesis", term)
    rule = {"local":"Local-PSD", "I":"Identity-PSD", "0":"Zero-PSD",
            "add":"Sum-PSD", "tensor":"Tensor-PSD"}.get(term.kind)
    if rule is None:
        raise Unsupported(f"No positivity rule for {term}")
    children = tuple(positivity(a,hypothesis) for a in term.args) if term.kind in ("add","tensor") else ()
    return Positive(rule, term, children)


def effect_induction(family, kernel):
    """Build a proof of 0 <= family(k,n) <= I, for 0 <= k <= n."""
    k,n = family.start, family.end
    step = recurrence(family)
    base_unfolded = family.unfold(n,n)
    base = trans(Equality("Definition", family(n,n), base_unfolded),
                 Equality("Sum-Empty", base_unfolded, zero(n,n)))
    head, tail = step.right.args
    a, r = head.args[0], tail.args[0]
    residual_name = f"I-({a.args[0]})-({r.args[0]})"
    kernel.define(residual_name, sp.eye(kernel.dimension)-kernel.matrices[a.args[0]]-kernel.matrices[r.args[0]])
    rest = family(k+1,n)
    cone = add(tensor(local(residual_name,k),identity(k+1,n)),
               tensor(r,subtract(identity(k+1,n),rest)))
    residual = subtract(identity(k,n), step.right)
    split_identity = tensor(identity(k,k+1),identity(k+1,n))
    upper = trans(congruence(residual, subtract(split_identity,step.right), (0,),
                            Equality("Identity-Split", identity(k,n), split_identity)),
                  Equality("Tensor-Linearity", subtract(split_identity,step.right), cone))
    return Induction(family,base,step,positivity(step.right,rest),upper,positivity(cone,rest))


def framed_attempt(family, kernel, outcomes, accepted_target):
    """Pull actual local Kraus branches back, frame the suffix, and accumulate.

    outcomes is a sequence of (Kraus-name, accepted). The matrices and branch
    classification come from the source program's finite semantics adapter.
    """
    k,n = family.start,family.end
    kernel.define("I", sp.eye(kernel.dimension))
    branches,frames = [],[]
    for name,accepted in outcomes:
        target = accepted_target if accepted else "I"
        suffix = identity(k+1,n) if accepted else family(k+1,n)
        output_name = f"wp({name},{target})"
        kraus = kernel.maps[name]
        kernel.define(output_name, kraus.H*kernel.matrices[target]*kraus)
        before = pullback(name,k,tensor(local(target,k),suffix))
        after = tensor(local(output_name,k),suffix)
        branches.append(before)
        frames.append(Equality("Frame",before,after))
    if not branches:
        raise Unsupported("An attempt must have at least one outcome")
    result = frames[0]
    for branch,frame in zip(branches[1:],frames[1:]):
        before,mid,after = add(result.left,branch),add(result.right,branch),add(result.right,frame.right)
        result = trans(congruence(before,mid,(0,),result),congruence(mid,after,(1,),frame))
    step = recurrence(family)
    return trans(result, Equality("Branch-Accum",result.right,step.right),
                 Equality("Symm",step.right,step.left,(step,)))


@dataclass
class IndexedEvidence:
    kernel: Kernel
    proof: object
    context: tuple = ()

    def check(self):
        self.kernel.steps.clear()
        if isinstance(self.proof, Induction):
            return self.kernel.induction(self.proof)
        return self.kernel.check(self.proof,self.context)

    def explain(self, matrices=False):
        self.check()
        lines,seen = [],set()
        for rule,left,right in self.kernel.steps:
            if rule in ("Trans","Congruence","Symm"):
                continue
            row = f"[{rule}] {left} = {right}"
            if rule in ("Sum-Head","Product-Head"):
                lo,hi = left.args[1:3]
                row += f"  (under {lo} < {hi})"
            if rule.endswith("PSD") or rule.endswith("Hypothesis"):
                row = f"[{rule}] 0 <= {right}"
            if rule == "Interval-Induction":
                _,lo,hi = right.args
                row = f"[{rule}] 0 <= {right} <= I, for every 0 <= {lo} <= {hi}"
            if row not in seen:
                lines.append(row)
                seen.add(row)
        if isinstance(self.proof,Equality):
            lines.append(f"[Conclusion] {self.proof.left} = {self.proof.right}")
        if matrices:
            for name,matrix in self.kernel.matrices.items():
                lines.extend((f"{name}:",str(matrix)))
        return "\n".join(lines)
