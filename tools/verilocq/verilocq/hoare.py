"""Proof objects for the paper's local and Distributed-tot rules.

Generation, rule replay and consequence checking are separate. Indexed quantum
consequences use exact local matrix coefficients and checked family recurrences,
without constructing the global array state. All rules are implemented in Python.
"""

from dataclasses import dataclass, field, replace
from functools import lru_cache

import sympy as sp
import z3
from z3.z3util import get_vars

from . import indexed as ix
from .pretty import format_block, format_expression
from .quantum import clean, embed, gate_matrix, psd
from .syntax import Assign, Gate, If, Measure, Skip, Unsupported, access, expr


_equalities={}


def symbolic(value):
    value = z3.simplify(expr(value))
    if z3.is_int_value(value):
        return sp.Integer(value.as_long())
    if z3.is_const(value) and z3.is_int(value):
        return sp.Symbol(str(value), integer=True)
    if z3.is_add(value):
        return sp.expand(sum(symbolic(a) for a in value.children()))
    if z3.is_sub(value):
        a,*rest = value.children()
        return sp.expand(symbolic(a)-sum(symbolic(b) for b in rest))
    if z3.is_mul(value):
        return sp.expand(sp.prod(symbolic(a) for a in value.children()))
    raise Unsupported(f"Unsupported symbolic index: {value}")


def arithmetic(value):
    value = sp.sympify(value)
    if value.is_Integer:
        return z3.IntVal(int(value))
    if isinstance(value,sp.Symbol):
        if isinstance(value,sp.Dummy):
            return z3.Int("sympy-index:"+sp.srepr(value))
        return z3.Int(value.name)
    if value.is_Add:
        return sum((arithmetic(a) for a in value.args),z3.IntVal(0))
    if value.is_Mul:
        result=z3.IntVal(1)
        for a in value.args:
            result=result*arithmetic(a)
        return result
    raise Unsupported(f"Unsupported index arithmetic: {value}")


def subst(value, mapping):
    return z3.simplify(z3.substitute(expr(value),*mapping))


def logical_integer(value):
    return (isinstance(value,z3.ExprRef) and z3.is_const(value) and z3.is_int(value)
            and value.decl().kind()==z3.Z3_OP_UNINTERPRETED)


@dataclass(frozen=True)
class ASTKey:
    context: int
    identity: int
    value: object = field(compare=False,hash=False,repr=False)


def expression_key(value):
    value=expr(value)
    if not z3.is_app(value):
        raise Unsupported("Only quantifier-free applied classical expressions are supported")
    # A live Z3 AST id includes sorts, declarations and children. The key owns
    # a reference to that AST and its context, preventing either id's reuse.
    # Python equality never invokes Z3's overloaded symbolic __eq__.
    return ASTKey(id(value.ctx),value.get_id(),value)


@dataclass(frozen=True,eq=False)
class Operation:
    kind: str
    name: str
    at: object
    matrix: object
    outcome: object = None
    alternatives: tuple = ()

    def __post_init__(self):
        if self.kind not in ("Unitary","Meas") or not z3.is_int(expr(self.at)):
            raise Unsupported("Malformed indexed quantum operation")
        matrices=self.alternatives if self.kind=="Meas" else (self.matrix,)
        if self.kind=="Meas" and (len(matrices)!=2 or self.outcome is None or not z3.is_int(expr(self.outcome))):
            raise Unsupported("Malformed measurement operation")
        if any(not isinstance(m,sp.ImmutableMatrix) or m.rows!=m.cols or m.has(sp.Float) for m in matrices):
            raise Unsupported("A quantum operation needs exact immutable square matrices")

    def key(self):
        return (self.kind,self.name,expression_key(self.at),self.matrix,
                None if self.outcome is None else expression_key(self.outcome),self.alternatives)

    def substitute(self,mapping):
        return replace(self,at=subst(self.at,mapping),
                       outcome=None if self.outcome is None else subst(self.outcome,mapping))


@dataclass(frozen=True,eq=False)
class Formula:
    kind: str
    args: tuple = ()

    def __post_init__(self):
        arities={"identity":0,"zero":0,"indexed":1,"choice":3,"sum":2,"pullback":2}
        if self.kind not in arities or not isinstance(self.args,tuple) or len(self.args)!=arities[self.kind]:
            raise Unsupported("Malformed quantum predicate syntax")
        if self.kind=="indexed" and not isinstance(self.args[0],ix.Term):
            raise Unsupported("An indexed predicate needs an operator term")
        if self.kind=="choice" and (not z3.is_bool(expr(self.args[0])) or not all(isinstance(q,Formula) for q in self.args[1:])):
            raise Unsupported("Malformed conditional quantum predicate")
        if self.kind=="sum" and not all(isinstance(q,Formula) for q in self.args):
            raise Unsupported("A predicate sum needs two predicates")
        if self.kind=="pullback" and (not isinstance(self.args[0],Operation) or not isinstance(self.args[1],Formula)):
            raise Unsupported("Malformed quantum pullback predicate")

    def key(self):
        def key(a):
            if isinstance(a,Formula):
                return a.key()
            if isinstance(a,Operation):
                return a.key()
            if isinstance(a,z3.ExprRef):
                return expression_key(a)
            return a
        return self.kind,tuple(key(a) for a in self.args)

    def substitute(self,mapping):
        result=[]
        for a in self.args:
            if isinstance(a,(Formula,Operation)):
                a=a.substitute(mapping)
            elif isinstance(a,z3.ExprRef):
                a=subst(a,mapping)
            elif isinstance(a,ix.Term):
                free=ix.symbols(a)
                replacements={sp.Symbol(str(k),integer=True):symbolic(v) for k,v in mapping
                              if sp.Symbol(str(k),integer=True) in free}
                a=ix.substitute(a,replacements)
            result.append(a)
        return Formula(self.kind,tuple(result))


def leaf(term):
    return Formula("indexed",(term,))


I=Formula("identity")
ZERO=Formula("zero")


def choose(condition,yes,no):
    simplified=z3.simplify(expr(condition))
    if z3.is_true(simplified):
        return yes
    if z3.is_false(simplified):
        return no
    return Formula("choice",(expr(condition),yes,no))


def guard(condition,quantum):
    return choose(condition,quantum,ZERO)


def plus(left,right):
    return Formula("sum",(left,right))


def backward(operation,quantum):
    return Formula("pullback",(operation,quantum))


@dataclass(frozen=True,eq=False)
class Assertion:
    classical: object
    quantum: Formula

    def key(self):
        return expression_key(self.classical),self.quantum.key()

    def substitute(self,mapping):
        return Assertion(subst(self.classical,mapping),self.quantum.substitute(mapping))


def same(left,right):
    return left.key()==right.key()


def block_key(block):
    if not isinstance(block,tuple):
        return id(block)
    result=[]
    for command in block:
        if isinstance(command,Assign):
            result.append(("assign",command.target,expression_key(command.value)))
        elif isinstance(command,If):
            result.append(("if",expression_key(command.condition),block_key(command.then),block_key(command.otherwise)))
        else:
            result.append(repr(command))
    return tuple(result)


@dataclass(frozen=True,eq=False)
class Proof:
    rule: str
    pre: Assertion
    block: object
    post: Assertion
    premises: tuple = ()
    data: tuple = ()


@dataclass(frozen=True,eq=False)
class DistributedData:
    invariant: Assertion
    rank: object
    old_rank: object


class NeedCase(Exception):
    def __init__(self,condition):
        self.condition=condition


@lru_cache(maxsize=8192)
def pull_matrix(matrix,row,column):
    if row is None:
        return clean(matrix.H*matrix)
    return clean(sp.conjugate(matrix[row,:]).T*matrix[column,:])


class Layout:
    """Names the source program's local register groups and their counters."""
    def __init__(self,schema,counters):
        self.schema=schema
        self.counters=dict(counters)
        self.dimension=2**len(schema.registers)

    def operation(self,command,outcome=None):
        targets=command.targets if isinstance(command,Gate) else (command.qubit,)
        names={self.counters[q] for q in targets}
        if len(names)!=1:
            raise Unsupported("An indexed local operation crosses register groups")
        at=self.schema.varmap[next(iter(names))].symbol
        indices=tuple(self.schema.registers.index(q) for q in targets)
        if isinstance(command,Gate):
            matrix=embed(gate_matrix(command,{},self.schema),indices,len(self.schema.registers))
            return Operation("Unitary",command.name,at,matrix)
        if isinstance(command,Measure):
            matrices=[]
            for u in (0,1):
                matrix=sp.zeros(2)
                matrix[u,u]=1
                matrices.append(embed(sp.ImmutableMatrix(matrix),indices,len(self.schema.registers)))
            return Operation("Meas",command.qubit,at,None,expr(outcome),tuple(matrices))
        raise Unsupported("No quantum operation for this command")


class QuantumChecker:
    """Exact indexed operator equality under symbolic classical conditions.

    Matrix units together with the identity form a local basis. Identity factors
    are implicit, so operations on unused registers need no global allocation.
    Opaque family factors are expanded only with replayed recurrence proofs.
    """
    def __init__(self,schema,kernel,families):
        self.schema=schema
        self.kernel=kernel
        self.families=tuple(families)
        self.validated=set()
        self.decisions={}
        self.equalities=set()
        self.implications={}
        self.indices={}
        self.trace=[]
        self.logical={}
        self.classicals=set()
        self.declared={v.name:v.symbol for v in self.schema.variables}
        self.sat_cache={}
        self.solver=self.schema.solver()
        for family in self.families:
            kernel.induction(ix.effect_induction(family,kernel))
        self.environment=self.fingerprint()

    def fingerprint(self):
        return (expression_key(self.schema.domains),tuple(sorted(self.kernel.matrices.items())),self.families)

    def check_environment(self):
        if self.fingerprint()!=self.environment:
            raise Unsupported("The quantum definitions changed after proof checking began")

    def classical(self,value,boolean=True):
        value=expr(value)
        if not (z3.is_bool(value) if boolean else z3.is_int(value)):
            raise Unsupported("A classical assertion or index has the wrong type")
        key=expression_key(value)
        if key in self.classicals:
            return
        for variable in get_vars(value):
            declared=self.declared.get(str(variable))
            if declared is not None:
                if not variable.eq(declared):
                    raise Unsupported("An assertion shadows a declared variable with a different type")
            elif str(variable) not in self.logical or not logical_integer(variable):
                raise Unsupported("An assertion contains an undeclared logical variable")
        pending=[value]
        while pending:
            node=pending.pop()
            if z3.is_quantifier(node):
                raise Unsupported("Quantified classical assertions are outside this proof fragment")
            if z3.is_app(node):
                if node.num_args() and node.decl().kind()==z3.Z3_OP_UNINTERPRETED:
                    raise Unsupported("Uninterpreted classical functions are unsupported")
                pending.extend(node.children())
        self.classicals.add(key)

    def satisfiable(self,condition):
        self.classical(condition)
        key=expression_key(condition)
        if key in self.sat_cache:
            return self.sat_cache[key]
        self.solver.push()
        self.solver.add(expr(condition))
        answer=self.solver.check()
        self.solver.pop()
        if answer==z3.unknown:
            raise Unsupported("SMT could not decide a Hoare side condition")
        self.sat_cache[key]=answer==z3.sat
        return answer==z3.sat

    def implies(self,left,right):
        self.classical(left)
        self.classical(right)
        key=(expression_key(left),expression_key(right))
        if key not in self.implications:
            self.implications[key]=not self.satisfiable(z3.And(expr(left),z3.Not(expr(right))))
        return self.implications[key]

    def decide(self,condition,context):
        condition=z3.simplify(expr(condition))
        key=(expression_key(context),expression_key(condition))
        if key not in self.decisions:
            self.decisions[key]=(True if self.implies(context,condition) else
                                 False if self.implies(context,z3.Not(condition)) else None)
        answer=self.decisions[key]
        if answer is None:
            raise NeedCase(condition)
        return answer

    def index(self,value,context):
        value=sp.expand(value)
        cache=(value,expression_key(context))
        if cache in self.indices:
            return self.indices[cache]
        # Canonicalize only proved equal indices, never a sampled model value.
        candidates={sp.Integer(0),value}
        variables=sorted((v for v in self.schema.variables if getattr(v,"domain",None) is None and z3.is_int(v.symbol)),key=lambda v:v.name)
        for var in variables:
            if var.name=="n":
                continue
            candidate=sp.Symbol(var.name,integer=True)
            candidates.add(candidate)
            candidates.add(candidate+1)
        ordered=sorted(candidates,key=lambda a:(int(a!=0),len(a.free_symbols),sp.count_ops(a),str(a)))
        for candidate in ordered:
            if self.implies(context,arithmetic(value)==arithmetic(candidate)):
                self.indices[cache]=candidate
                return candidate
        self.indices[cache]=value
        return value

    def _add(self,left,right):
        result=dict(left)
        for word,a in right.items():
            value=sp.simplify(result.get(word,0)+a)
            if value==0:
                result.pop(word,None)
            else:
                result[word]=value
        if len(result)>65536:
            raise Unsupported("Hoare operator-algebra budget exceeded")
        return result

    def _matrix(self,matrix,at):
        matrix=clean(matrix)
        d=self.kernel.dimension
        a=matrix[d-1,d-1]
        result={():a} if a!=0 else {}
        for r in range(d):
            for c in range(d):
                if (r,c)==(d-1,d-1):
                    continue
                coefficient=sp.simplify(matrix[r,c]-(a if r==c else 0))
                if coefficient!=0:
                    result[(("entry",at,r,c),)]=coefficient
        return result

    @staticmethod
    def _space(token):
        return (token[1],token[1]+1) if token[0]=="entry" else (token[2],token[3])

    def _word(self,word,context):
        for i,a in enumerate(word):
            lo,hi=self._space(a)
            for b in word[i+1:]:
                start,end=self._space(b)
                if not self.implies(context,z3.Or(arithmetic(hi)<=arithmetic(start),arithmetic(end)<=arithmetic(lo))):
                    raise Unsupported("Unproved separation of quantum factors")
        return tuple(sorted(word,key=repr))

    def _multiply(self,left,right,context):
        result={}
        for a,x in left.items():
            for b,y in right.items():
                word=self._word(a+b,context)
                result=self._add(result,{word:sp.simplify(x*y)})
        return result

    def _term(self,term,context):
        a=term.args
        lo,hi=(self.index(e,context) for e in term.space)
        if not self.implies(context,z3.And(arithmetic(lo)>=0,arithmetic(lo)<=arithmetic(hi))):
            raise Unsupported("An indexed predicate is undefined in this classical case")
        if term.kind=="0":
            return {}
        if term.kind=="I":
            return {():sp.S.One}
        if term.kind=="local":
            return self._matrix(self.kernel.matrices[a[0]],lo)
        if term.kind=="call":
            family=a[0]
            if family not in self.families:
                raise Unsupported("An indexed family has no checked effect-bound proof")
            if self.implies(context,arithmetic(lo)==arithmetic(hi)):
                proof=ix.Equality("Definition",family(family.end,family.end),family.unfold(family.end,family.end))
                self.kernel.check(proof,(family.end>=0,))
                empty=ix.Equality("Sum-Empty",proof.right,ix.zero(family.end,family.end))
                self.kernel.check(empty,(family.end>=0,))
                return {}
            return {(("family",family,lo,hi),):sp.S.One}
        if term.kind in ("add","sub"):
            other=self._term(a[1],context)
            if term.kind=="sub":
                other={w:-v for w,v in other.items()}
            return self._add(self._term(a[0],context),other)
        if term.kind=="tensor":
            result={():sp.S.One}
            for part in a:
                result=self._multiply(result,self._term(part,context),context)
            return result
        raise Unsupported(f"No Hoare normal form for {term.kind}")

    def _pull(self,operation,value,context):
        at=self.index(symbolic(operation.at),context)
        if operation.kind=="Meas":
            outcome=0 if self.decide(expr(operation.outcome)==0,context) else 1
            if not self.implies(context,expr(operation.outcome)==outcome):
                raise Unsupported("A measurement outcome is outside its domain")
            matrix=operation.alternatives[outcome]
        else:
            matrix=operation.matrix
        result={}
        for word,coefficient in value.items():
            hit=None
            for j,token in enumerate(word):
                lo,hi=self._space(token)
                if token[0]=="entry" and self.implies(context,arithmetic(lo)==arithmetic(at)):
                    hit=j
                elif not self.implies(context,z3.Or(arithmetic(at)<arithmetic(lo),arithmetic(at)>=arithmetic(hi))):
                    raise Unsupported("A local operation reaches an opaque quantum suffix")
            if hit is None:
                row=column=None
                rest=word
            else:
                token=word[hit]
                row,column=token[2],token[3]
                rest=word[:hit]+word[hit+1:]
            transformed=self._matrix(pull_matrix(matrix,row,column),at)
            framed=self._multiply({rest:coefficient},transformed,context)
            result=self._add(result,framed)
        return result

    def reduce(self,formula,context):
        a=formula.args
        if formula.kind=="zero":
            return {}
        if formula.kind=="identity":
            return {():sp.S.One}
        if formula.kind=="indexed":
            return self._term(a[0],context)
        if formula.kind=="choice":
            return self.reduce(a[1] if self.decide(a[0],context) else a[2],context)
        if formula.kind=="sum":
            return self._add(self.reduce(a[0],context),self.reduce(a[1],context))
        if formula.kind=="pullback":
            return self._pull(a[0],self.reduce(a[1],context),context)
        raise Unsupported(f"Unknown quantum formula {formula.kind}")

    def _expand(self,value,selected,context):
        _,family,lo,hi=selected
        k,n=family.start,family.end
        proof=ix.recurrence(family)
        self.kernel.check(proof,(k>=0,k<n))
        if not self.implies(context,arithmetic(lo)<arithmetic(hi)):
            raise NeedCase(arithmetic(lo)<arithmetic(hi))
        unfolded=ix.substitute(proof.right,{k:lo,n:hi})
        replacement=self._term(unfolded,context)
        result={}
        for word,a in value.items():
            if selected in word:
                position=word.index(selected)
                rest=word[:position]+word[position+1:]
                result=self._add(result,self._multiply({rest:a},replacement,context))
            else:
                result=self._add(result,{word:a})
        self.trace.append(f"[Conseq / indexed equality] unfold {family.name}({lo},{hi}) by the checked recurrence")
        return result

    def equal(self,left,right,condition):
        def prune(formula,context):
            if formula.kind=="choice":
                c,yes,no=formula.args
                if self.implies(context,c):
                    return prune(yes,context)
                if self.implies(context,z3.Not(c)):
                    return prune(no,context)
                return choose(c,prune(yes,z3.And(expr(context),c)),prune(no,z3.And(expr(context),z3.Not(c))))
            if formula.kind=="sum":
                return plus(*(prune(q,context) for q in formula.args))
            if formula.kind=="pullback":
                return backward(formula.args[0],prune(formula.args[1],context))
            return formula
        left,right=prune(left,condition),prune(right,condition)
        if same(left,right):
            return True
        cache=(left.key(),right.key(),expression_key(condition))
        if cache in self.equalities:
            return True
        shared=(self.environment,cache)
        if shared in _equalities:
            self.trace.extend(_equalities[shared])
            self.equalities.add(cache)
            return True
        trace_start=len(self.trace)
        pending=[expr(condition)]
        cases=0
        while pending:
            context=pending.pop()
            if not self.satisfiable(context):
                continue
            cases+=1
            if cases>256:
                raise Unsupported("Hoare classical case-split budget exceeded")
            try:
                a,b=self.reduce(left,context),self.reduce(right,context)
                if a!=b:
                    # Expand a family occurring on only one side. Never assume
                    # the controller has the right retry shape.
                    for _ in range(4):
                        families_a={t for w in a for t in w if t[0]=="family"}
                        families_b={t for w in b for t in w if t[0]=="family"}
                        candidates=sorted(families_a^families_b,key=repr)
                        if not candidates:
                            break
                        token=candidates[0]
                        if token in families_a:
                            a=self._expand(a,token,context)
                        else:
                            b=self._expand(b,token,context)
                        if a==b:
                            break
                    if a!=b:
                        raise Unsupported("The quantum consequence has not been established by exact indexed algebra")
            except NeedCase as split:
                pending.extend((z3.And(context,split.condition),z3.And(context,z3.Not(split.condition))))
        self.equalities.add(cache)
        if len(_equalities)>1024:
            _equalities.clear()
        _equalities[shared]=tuple(self.trace[trace_start:])
        return True

    def entail(self,left,right):
        if not self.implies(left.classical,right.classical):
            raise Unsupported("A classical Conseq implication is invalid")
        return self.equal(left.quantum,right.quantum,left.classical)

    def equivalent(self,left,right):
        return self.equal(guard(left.classical,left.quantum),guard(right.classical,right.quantum),True)

    def wellformed(self,formula,condition):
        cache=(formula.key(),expression_key(condition))
        if cache in self.validated or (formula.key(),expression_key(True)) in self.validated or not self.satisfiable(condition):
            return True
        a=formula.args
        if formula.kind in ("identity","zero"):
            pass
        elif formula.kind=="choice":
            self.classical(a[0])
            self.wellformed(a[1],z3.And(expr(condition),a[0]))
            self.wellformed(a[2],z3.And(expr(condition),z3.Not(a[0])))
        elif formula.kind=="indexed":
            self.typed_effect(a[0],condition)
        elif formula.kind=="pullback":
            op,target=a
            self.classical(op.at,boolean=False)
            self.wellformed(target,condition)
            if not self.implies(condition,op.at>=0):
                raise Unsupported("A quantum operation has an invalid array index")
            if op.kind=="Meas":
                self.classical(op.outcome,boolean=False)
                if (self.logical.get(str(op.outcome))!="bit"
                        and not self.implies(condition,z3.Or(expr(op.outcome)==0,expr(op.outcome)==1))):
                    raise Unsupported("A logical measurement outcome has no finite type")
                matrices=op.alternatives
            else:
                matrices=(op.matrix,)
            for matrix in matrices:
                if psd(clean(sp.eye(self.kernel.dimension)-matrix.H*matrix)) is not True:
                    raise Unsupported("A Kraus pullback does not preserve predicate bounds")
        elif formula.kind=="sum":
            RuleChecker.measurement_sum_formula(formula,self.kernel.dimension)
            self.wellformed(a[0],condition)
            self.wellformed(a[1],condition)
        else:
            raise Unsupported("Unknown quantum predicate formula")
        self.validated.add(cache)
        return True

    def typed_effect(self,term,condition):
        allowed={sp.Symbol(v.name,integer=True) for v in self.schema.variables if z3.is_int(v.symbol)}
        allowed.update(sp.Symbol(name,integer=True) for name in self.logical)
        if ix.symbols(term)-allowed:
            raise Unsupported("An indexed predicate contains an undeclared or captured free index")
        lo,hi=term.space
        if not self.implies(condition,z3.And(arithmetic(lo)>=0,arithmetic(lo)<=arithmetic(hi))):
            raise Unsupported("Ill-typed indexed predicate interval")
        if term.kind in ("I","0"):
            return
        if term.kind=="local":
            matrix=self.kernel.matrices[term.args[0]]
            if psd(matrix) is not True or psd(clean(sp.eye(self.kernel.dimension)-matrix)) is not True:
                raise Unsupported("A local quantum predicate is outside [0,I]")
            return
        if term.kind=="call" and term.args[0] in self.families:
            return
        if term.kind=="tensor":
            for left,right in zip(term.args,term.args[1:]):
                if not self.implies(condition,arithmetic(left.space[1])==arithmetic(right.space[0])):
                    raise Unsupported("Indexed tensor factors overlap or leave an undeclared gap")
            for child in term.args:
                self.typed_effect(child,condition)
            return
        raise Unsupported("No checked predicate-bound derivation for this indexed term")


class RuleChecker:
    def __init__(self,schema,layout,quantum):
        self.schema,self.layout,self.quantum=schema,layout,quantum
        self.checked=set()
        self.steps=[]

    def require(self,condition,message):
        if not condition:
            raise Unsupported(message)

    def classical(self,condition):
        self.quantum.classical(condition)

    def check(self,proof,depth=0):
        self.require(isinstance(proof,Proof) and depth<=256,"Invalid or excessively deep Hoare proof")
        if depth==0:
            self.schema.validate()
            if isinstance(proof.block,tuple):
                self.schema.validate_block(proof.block)
            self.quantum.check_environment()
        if id(proof) in self.checked:
            return True
        p=proof.premises
        pre,post,block=proof.pre,proof.post,proof.block
        rule=proof.rule
        if rule=="Distributed-tot":
            self.distributed(proof,depth)
        elif rule=="Conseq":
            self.require(len(p)==1 and block_key(block)==block_key(p[0].block),"Conseq changes the program")
            self.check(p[0],depth+1)
            self.quantum.entail(pre,p[0].pre)
            self.quantum.entail(p[0].post,post)
        elif rule=="Assert-Eq":
            self.require(len(p)==1 and block_key(block)==block_key(p[0].block),"Assert-Eq changes the program")
            self.check(p[0],depth+1)
            self.quantum.equivalent(pre,p[0].pre)
            self.quantum.equivalent(post,p[0].post)
        elif rule=="Seq":
            self.require(len(p)==2 and isinstance(block,tuple) and block_key(block)==block_key(p[0].block+p[1].block),"Invalid Seq program")
            self.require(same(pre,p[0].pre) and same(p[0].post,p[1].pre) and same(post,p[1].post),"Seq assertion mismatch")
            for child in p:
                self.check(child,depth+1)
        elif rule=="If":
            self.require(len(p)==2 and len(block)==1 and isinstance(block[0],If),"Invalid If proof")
            command=block[0]
            for child,guard_,body in ((p[0],expr(command.condition),command.then),(p[1],z3.Not(expr(command.condition)),command.otherwise)):
                self.require(block_key(child.block)==block_key(body) and same(child.pre,Assertion(z3.And(expr(pre.classical),guard_),pre.quantum)) and same(child.post,post),"If premise mismatch")
                self.check(child,depth+1)
        elif rule=="Branch-Accum":
            self.require(len(p)==2 and all(block_key(c.block)==block_key(block) for c in p),"Branch-Accum program mismatch")
            self.require(all(expr(c.pre.classical).eq(expr(pre.classical)) and same(c.post.quantum,post.quantum) for c in p),"Branch-Accum assertions mismatch")
            self.require(same(pre.quantum,plus(p[0].pre.quantum,p[1].pre.quantum)) and expr(post.classical).eq(z3.Or(expr(p[0].post.classical),expr(p[1].post.classical))),"Branch-Accum has the wrong sum or disjunction")
            self.require(self.quantum.implies(True,z3.Not(z3.And(expr(p[0].post.classical),expr(p[1].post.classical)))),"Branch-Accum outcomes overlap")
            self.measurement_sum(pre.quantum)
            for child in p:
                self.check(child,depth+1)
        elif rule=="Aux-Subst":
            self.require(len(p)==1 and len(proof.data)==2,"Invalid Aux-Subst proof")
            variable,value=proof.data
            self.require(logical_integer(variable),"Aux-Subst needs a logical integer variable")
            reads,writes,_=access(block)
            self.require(str(variable) not in reads|writes and value in (0,1),"Aux-Subst freshness/type violation")
            mapping=((variable,z3.IntVal(value)),)
            self.require(block_key(block)==block_key(p[0].block) and same(pre,p[0].pre.substitute(mapping)) and same(post,p[0].post.substitute(mapping)),"Aux-Subst does not match the substitution")
            self.check(p[0],depth+1)
        elif rule in ("Assign","Unitary","Meas","Skip"):
            self.require(not p and isinstance(block,tuple),"A local axiom cannot have premises")
            if rule=="Skip":
                self.require((not block or len(block)==1 and isinstance(block[0],Skip)) and same(pre,post),"Invalid Skip axiom")
            else:
                self.require(len(block)==1,"An axiom must contain one command")
                command=block[0]
                if rule=="Assign":
                    self.require(isinstance(command,Assign),"Assign axiom has the wrong command")
                    expected=post.substitute(((self.schema.varmap[command.target].symbol,expr(command.value)),))
                    self.require(same(pre,expected),"Assign did not substitute both assertion parts")
                    self.require(self.quantum.implies(pre.classical,self.schema.varmap[command.target].admits(expr(command.value))),"Assignment escapes its declared domain")
                elif rule=="Unitary":
                    self.require(isinstance(command,Gate),"Unitary axiom has the wrong command")
                    expected=Assertion(post.classical,backward(self.layout.operation(command),post.quantum))
                    self.require(same(pre,expected),"Unitary pullback mismatch")
                else:
                    self.require(isinstance(command,Measure) and len(proof.data)==2,"Invalid Meas axiom")
                    original,y=proof.data
                    self.require(logical_integer(y),"Meas requires a fresh logical integer variable")
                    target=self.schema.varmap[command.target].symbol
                    self.require(str(y) not in self.schema.varmap and str(y) not in assertion_names(original) and str(y)!=str(target),"Meas logical outcome is not fresh")
                    replacement=((target,y),)
                    expected_pre=Assertion(subst(original.classical,replacement),backward(self.layout.operation(command,y),original.quantum.substitute(replacement)))
                    expected_post=Assertion(z3.And(expr(original.classical),target==y),original.quantum)
                    self.require(same(pre,expected_pre) and same(post,expected_post),"Meas axiom mismatch")
                    self.require(self.quantum.logical.get(str(y),"bit")=="bit","A measurement logical variable has a conflicting type")
                    self.quantum.logical[str(y)]="bit"
        else:
            raise Unsupported(f"Unknown Hoare rule {rule}")
        self.classical(pre.classical)
        self.classical(post.classical)
        self.quantum.wellformed(pre.quantum,pre.classical)
        self.quantum.wellformed(post.quantum,post.classical)
        self.checked.add(id(proof))
        self.steps.append(proof)
        return True

    def measurement_sum(self,formula):
        return self.measurement_sum_formula(formula,self.layout.dimension)

    @staticmethod
    def measurement_sum_formula(formula,dimension):
        def require(condition,message):
            if not condition:
                raise Unsupported(message)
        require(formula.kind=="sum","No effect-bound evidence for accumulated predicates")
        a,b=formula.args
        require(a.kind==b.kind=="pullback","Accumulated predicates are not outcome pullbacks")
        op0,op1=a.args[0],b.args[0]
        require(op0.kind==op1.kind=="Meas" and op0.name==op1.name and op0.at.eq(op1.at) and op0.alternatives==op1.alternatives,"Accumulation uses different instruments")
        require(z3.is_true(z3.simplify(expr(op0.outcome)==0)) and z3.is_true(z3.simplify(expr(op1.outcome)==1)),"Accumulation does not cover the two distinct outcomes")
        require(clean(sum((m.H*m for m in op0.alternatives),sp.zeros(dimension)))==sp.eye(dimension),"Measurement is not complete")

    def distributed(self,proof,depth):
        self.require(proof.block is self.schema and len(proof.data)==1,"Distributed proof is for a different program")
        self.schema.validate()
        data=proof.data[0]
        self.require(isinstance(data,DistributedData),"Distributed proof lacks its invariant and rank")
        inv,rank,old=data.invariant,expr(data.rank),data.old_rank
        pairs=tuple(self.schema.matching_pairs())
        p=proof.premises
        self.require(len(p)==1+2*len(pairs),"Distributed-tot omits or duplicates a premise")
        self.require(z3.is_int(rank) and logical_integer(old) and str(old) not in self.schema.varmap and str(old) not in assertion_names(inv)|{str(v) for v in get_vars(rank)},"Invalid or nonfresh ranking variable")
        self.require(self.quantum.logical.get(str(old),"integer")=="integer","The ranking logical variable has a conflicting type")
        self.quantum.logical[str(old)]="integer"
        expected_post=Assertion(z3.And(expr(inv.classical),self.schema.termination),inv.quantum)
        self.require(same(proof.post,expected_post),"Distributed conclusion does not match the invariant and TERM")
        initialization=p[0]
        self.require(block_key(initialization.block)==block_key(self.schema.initialization) and same(initialization.pre,proof.pre) and same(initialization.post,inv),"Distributed initialization mismatch")
        self.check(initialization,depth+1)
        for j,(_,enabled,body) in enumerate(pairs):
            preserved=p[1+j]
            ranked=p[1+len(pairs)+j]
            self.require(block_key(preserved.block)==block_key(body) and same(preserved.pre,Assertion(z3.And(expr(inv.classical),enabled),inv.quantum)) and same(preserved.post,inv),"Distributed communication premise mismatch")
            expected_pre=Assertion(z3.And(expr(inv.classical),enabled,rank==old),I)
            expected_rank_post=Assertion(rank<old,I)
            self.require(block_key(ranked.block)==block_key(body) and same(ranked.pre,expected_pre) and same(ranked.post,expected_rank_post),"Distributed rank triple mismatch")
            self.check(preserved,depth+1)
            self.check(ranked,depth+1)
        self.require(self.quantum.implies(inv.classical,rank>=0),"Ranking function is not nonnegative")
        no_pair=z3.And(*(z3.Not(g) for _,g,_ in pairs))
        self.require(self.quantum.implies(z3.And(expr(inv.classical),no_pair),self.schema.termination),"Distributed proof permits deadlock")


def assertion_names(assertion):
    result={str(v) for v in get_vars(expr(assertion.classical))}
    pending=[assertion.quantum]
    while pending:
        item=pending.pop()
        for a in item.args:
            if isinstance(a,Formula):
                pending.append(a)
            elif isinstance(a,z3.ExprRef):
                result.update(str(v) for v in get_vars(a))
            elif isinstance(a,Operation):
                result.update(str(v) for v in get_vars(a.at))
                if a.outcome is not None:
                    result.update(str(v) for v in get_vars(expr(a.outcome)))
            elif isinstance(a,ix.Term):
                result.update(s.name for s in ix.symbols(a))
    return result


def local_proof(schema,layout,block,post):
    """Build local rule applications backwards; no rule is trusted by its label."""
    def build(commands,target):
        if not commands:
            return Proof("Skip",target,(),target)
        command=commands[-1]
        if isinstance(command,Assign):
            pre=target.substitute(((schema.varmap[command.target].symbol,expr(command.value)),))
            final=Proof("Assign",pre,(command,),target)
        elif isinstance(command,Gate):
            pre=Assertion(target.classical,backward(layout.operation(command),target.quantum))
            final=Proof("Unitary",pre,(command,),target)
        elif isinstance(command,Skip):
            final=Proof("Skip",target,(command,),target)
        elif isinstance(command,Measure):
            if not z3.is_true(z3.simplify(expr(target.classical))):
                raise Unsupported("The local generator requires an encoded measurement postcondition")
            y=z3.FreshInt("outcome")
            variable=schema.varmap[command.target].symbol
            mapping=((variable,y),)
            pre=Assertion(subst(target.classical,mapping),backward(layout.operation(command,y),target.quantum.substitute(mapping)))
            recorded=Assertion(z3.And(expr(target.classical),variable==y),target.quantum)
            axiom=Proof("Meas",pre,(command,),recorded,data=(target,y))
            branches=[]
            for u in (0,1):
                replacement=((y,z3.IntVal(u)),)
                branches.append(Proof("Aux-Subst",pre.substitute(replacement),(command,),recorded.substitute(replacement),(axiom,),(y,u)))
            pre=Assertion(True,plus(branches[0].pre.quantum,branches[1].pre.quantum))
            joined=Assertion(z3.Or(expr(branches[0].post.classical),expr(branches[1].post.classical)),target.quantum)
            accumulated=Proof("Branch-Accum",pre,(command,),joined,tuple(branches))
            final=Proof("Conseq",pre,(command,),target,(accumulated,))
        elif isinstance(command,If):
            yes=build(command.then,target)
            no=build(command.otherwise,target)
            pre=Assertion(True,choose(command.condition,yes.pre.quantum,no.pre.quantum))
            yes_pre=Assertion(z3.And(expr(pre.classical),expr(command.condition)),pre.quantum)
            no_pre=Assertion(z3.And(expr(pre.classical),z3.Not(expr(command.condition))),pre.quantum)
            yes=Proof("Conseq",yes_pre,command.then,target,(yes,))
            no=Proof("Conseq",no_pre,command.otherwise,target,(no,))
            final=Proof("If",pre,(command,),target,(yes,no))
        else:
            raise Unsupported(f"No paper-rule generator for {command!r}")
        if len(commands)==1:
            return final
        earlier=build(commands[:-1],final.pre)
        return Proof("Seq",earlier.pre,commands,target,(earlier,final))
    return build(tuple(block),post)


def prove_local(schema,layout,pre,block,post):
    encoded=Assertion(True,guard(post.classical,post.quantum))
    generated=local_proof(schema,layout,tuple(block),encoded)
    weakened=Proof("Conseq",pre,tuple(block),encoded,(generated,))
    return Proof("Assert-Eq",pre,tuple(block),post,(weakened,))


def prove_distributed(schema,layout,pre,invariant,post,rank):
    pairs=tuple(schema.matching_pairs())
    initialization=prove_local(schema,layout,pre,schema.initialization,invariant)
    communications=tuple(prove_local(schema,layout,Assertion(z3.And(expr(invariant.classical),enabled),invariant.quantum),body,invariant)
                         for _,enabled,body in pairs)
    old=z3.FreshInt("old_rank")
    ranking=tuple(prove_local(schema,layout,Assertion(z3.And(expr(invariant.classical),enabled,expr(rank)==old),I),body,Assertion(expr(rank)<old,I))
                  for _,enabled,body in pairs)
    result=Assertion(z3.And(expr(invariant.classical),schema.termination),invariant.quantum)
    distributed=Proof("Distributed-tot",pre,schema,result,(initialization,*communications,*ranking),(DistributedData(invariant,rank,old),))
    return Proof("Conseq",pre,schema,post,(distributed,))


@dataclass
class Evidence:
    checker: RuleChecker
    proof: Proof
    definitions: tuple = ()

    def check(self):
        self.checker.checked.clear()
        self.checker.steps.clear()
        return self.checker.check(self.proof)

    def explain(self,matrices=False):
        self.check()
        labels={}
        definitions={}
        def quantum(q):
            key=q.key()
            if q.kind=="identity":
                return "I"
            if q.kind=="zero":
                return "0"
            if q.kind=="indexed":
                return str(q.args[0])
            if key in labels:
                return labels[key]
            name=f"W{len(labels)}"
            labels[key]=name
            a=q.args
            if q.kind=="choice":
                text=f"if {format_expression(a[0])} then {quantum(a[1])} else {quantum(a[2])}"
            elif q.kind=="sum":
                text=f"{quantum(a[0])} + {quantum(a[1])}"
            else:
                op,target=a
                suffix=f", outcome={format_expression(op.outcome)}" if op.outcome is not None else ""
                text=f"F_{op.name}[{format_expression(op.at)}{suffix}]({quantum(target)})"
            definitions[name]=text
            return name
        def assertion(a):
            return f"{{ {format_expression(a.classical)} ; {quantum(a.quantum)} }}"
        lines=[]
        identifiers={id(step):f"P{i}" for i,step in enumerate(self.checker.steps)}
        for step in self.checker.steps:
            if step.rule=="Seq":
                command="L1; L2"
            elif step.rule=="If":
                command=f"if {format_expression(step.block[0].condition)} then ... else ... fi"
            elif isinstance(step.block,tuple):
                command=format_block(step.block).strip() if len(step.block)<=1 else f"local block ({len(step.block)} commands)"
                command=command or "skip"
            else:
                command=self.checker.schema.name
            dependencies=", ".join(identifiers[id(child)] for child in step.premises)
            annotation=f"  (from {dependencies})" if dependencies else ""
            if step.rule=="Aux-Subst":
                variable,value=step.data
                annotation+=f"  {format_expression(variable)} := {value}"
            lines.append(f"{identifiers[id(step)]} [{step.rule}] {assertion(step.pre)} {command} {assertion(step.post)}{annotation}")
            if step.rule=="Distributed-tot":
                data=step.data[0]
                lines.append(f"  rank t = {format_expression(data.rank)}; fresh xi = {format_expression(data.old_rank)}")
        ordered_definitions=[f"{name} = {text}" for name,text in
                             sorted(definitions.items(),key=lambda item:int(item[0][1:]))]
        lines=["Intermediate predicates (local to this check):",
               "W labels name the quantum predicates used below.",
               *self.definitions,*ordered_definitions,"","Hoare rule derivation:",*lines]
        if self.checker.quantum.trace:
            lines.extend(("","Quantum side conditions:",*dict.fromkeys(self.checker.quantum.trace)))
        if matrices:
            for name,matrix in self.checker.quantum.kernel.matrices.items():
                lines.extend((f"{name}:",str(matrix)))
        return "\n".join(lines)
