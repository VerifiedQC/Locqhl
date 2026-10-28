"""Indexed quantum proofs and a checked adapter for the paper's BBPSSW loop.

This backend does not unroll or truncate retries. It combines exact four-qubit
Kraus identities, symbolic execution of the actual classical communication
bodies with unbounded counters, and a fresh-factor tensor induction. The
induction proves the two first-acceptance effect specifications for every
finite proof parameter n. It does not assert termination on every resource
state. Werner-state probability/fidelity formulas require independent inputs.

Like the finite verifier, this is trusted Python proof code, not a Rocq proof.
"""

from dataclasses import dataclass
from itertools import product

import sympy as sp
import z3

from .quantum import (BELL, CNOT, I2, X, Z, clean, embed, projector, psd,
                      tensor)
from .syntax import (Assign, Branch, Gate, If, Measure, Process, Program,
                     Receive, Send, Skip, Unsupported, Variable, access, expr, seq)
from .verifier import (Obligation, Report, check_implication, classical_wp,
                       execute)
from .derivation import (ImplicationEvidence, MatrixEqualityEvidence, TextEvidence,
                         ProofPlan, ProofGroup)
from .indexed import (Kernel, IndexedEvidence, first_acceptance, effect_induction,
                      framed_attempt, Equality, Induction)
from . import indexed as indexed_terms


@dataclass(frozen=True)
class NaturalVariable:
    name: str
    owner: str
    domain: None = None

    @property
    def symbol(self):
        return z3.Int(self.name)

    def admits(self, value):
        return value >= 0


@dataclass(frozen=True)
class ControlSchema:
    """Classical control of the indexed program; natural counters are unbounded.

    ac/at and bc/bt are fixed *templates* for cells at the corresponding current
    counter. Event checking below enforces that every retry uses index k+1.
    The four physical array names are distinct; they never wrap or get reused.
    """
    variables: tuple
    processes: tuple
    name: str = "Unbounded BBPSSW distillation"
    registers: tuple = ("ac", "bc", "at", "bt")
    references: tuple = ()

    varmap = Program.varmap
    initialization = Program.initialization
    termination = Program.termination
    matching_pairs = Program.matching_pairs
    solver = Program.solver
    validate_expr = Program.validate_expr
    validate_block = Program.validate_block

    @property
    def domains(self):
        terms = [var.admits(var.symbol) for var in self.variables]
        terms.append(self.varmap["n"].symbol >= 1)
        return z3.And(*terms)

    def validate(self):
        if self.registers != ("ac", "bc", "at", "bt") or self.references != ():
            raise Unsupported("The distillation schema requires its declared array-template layout and no reference qubits")
        names = [v.name for v in self.variables]
        if len(names) != len(set(names)) or set(names) != {
            "kA", "kB", "n", "mA", "mB", "rA", "rB",
            "doneA", "doneB", "sentA", "sentB", "recvA", "recvB",
        }:
            raise Unsupported("The distillation schema needs the declared distinct control variables")
        if tuple(p.name for p in self.processes) != ("Alice", "Bob"):
            raise Unsupported("The schema requires Alice and Bob in canonical order")
        if tuple(p.qubits for p in self.processes) != (("ac", "at"), ("bc", "bt")):
            raise Unsupported("The schema requires four distinct, locally owned array templates")
        for name in ("kA", "kB", "n"):
            if not isinstance(self.varmap[name], NaturalVariable):
                raise Unsupported("Counters and n must be unbounded natural variables")
        for var in self.variables:
            expected_owner = "proof" if var.name == "n" else "Alice" if var.name.endswith("A") else "Bob"
            if var.owner != expected_owner:
                raise Unsupported(f"Incorrect schema ownership for {var.name}; n is an immutable proof parameter")
        for name in ("mA", "mB", "rA", "rB"):
            var = self.varmap[name]
            if not isinstance(var, Variable) or var.domain != (0, 1):
                raise Unsupported("Measurement and receive variables must be bits")
        for name in ("doneA", "doneB", "sentA", "sentB", "recvA", "recvB"):
            var = self.varmap[name]
            if not isinstance(var, Variable) or any(type(v) is not bool for v in var.domain) or set(var.domain) != {False, True}:
                raise Unsupported("Control flags must be Boolean")
        for p in self.processes:
            if "n" in set.union(*access(p.init)[:2]):
                raise Unsupported("The executable program may not read or write proof parameter n")
            self.validate_block(p.init, p.name)
            for branch in p.branches:
                reads, writes, _ = access(branch.body)
                if "n" in reads | writes:
                    raise Unsupported("The executable program may not read or write proof parameter n")
                self.validate_expr(branch.guard, p.name, boolean=True)
                self.validate_block(branch.body, p.name)
                if isinstance(branch.action, Send):
                    self.validate_expr(branch.action.value, p.name)
                    if not z3.is_int(expr(branch.action.value)):
                        raise Unsupported("Distillation sends integer bits")
                elif isinstance(branch.action, Receive):
                    if self.varmap.get(branch.action.target) is None or self.varmap[branch.action.target].owner != p.name:
                        raise Unsupported("Receive target must be local")
                else:
                    raise Unsupported("Unsupported communication action")
            if len({b.name for b in p.branches}) != len(p.branches):
                raise Unsupported("Duplicate branch names")


def _smt(name, assumptions, goal):
    solver = z3.Solver()
    solver.set(timeout=10_000)
    solver.add(assumptions, z3.Not(goal))
    answer = solver.check()
    evidence = ImplicationEvidence(assumptions, goal, str(answer))
    if answer == z3.unsat:
        return Obligation(name, "symbolic arithmetic", "PASSED", detail="The negated claim is unsatisfiable", evidence=evidence)
    if answer == z3.unknown:
        return Obligation(name, "symbolic arithmetic", "INCOMPLETE", detail=solver.reason_unknown(), evidence=evidence)
    return Obligation(name, "symbolic arithmetic", "FAILED", detail="A symbolic counterexample exists",
                      witness={str(d): str(solver.model()[d]) for d in solver.model().decls()}, evidence=evidence)


def _matrix_check(name, actual, expected, equation=None):
    difference = clean(actual - expected)
    evidence = MatrixEqualityEvidence(equation or name, actual, expected)
    if difference.is_zero_matrix is True:
        return Obligation(name, "exact matrix identity", "PASSED", detail="Exact symbolic equality", evidence=evidence)
    if difference.is_zero_matrix is False:
        return Obligation(name, "exact matrix identity", "FAILED", detail="The circuit does not satisfy this required identity", evidence=evidence)
    return Obligation(name, "exact matrix identity", "INCOMPLETE", detail="Symbolic equality could not be decided", evidence=evidence)


def _psd_check(name, matrix):
    decision = psd(clean(matrix))
    status = "PASSED" if decision is True else "FAILED" if decision is False else "INCOMPLETE"
    return Obligation(name, "exact operator inequality", status,
                      detail="Exact positivity check; no numerical acceptance tolerance")


def _substitute(value, mapping, schema):
    return z3.simplify(z3.substitute(expr(value), *[(v.symbol, mapping[v.name]) for v in schema.variables]))


def _symbolic_paths(schema, block):
    """Symbolically execute classical code, recording indexed quantum test events."""
    paths = [(z3.BoolVal(True), {v.name: v.symbol for v in schema.variables}, ())]

    def step(commands, condition, mapping, events):
        current = [(condition, mapping, events)]
        for command in commands:
            following = []
            for guard, state, trace in current:
                if isinstance(command, Skip):
                    following.append((guard, state, trace))
                elif isinstance(command, Assign):
                    output = dict(state)
                    output[command.target] = _substitute(command.value, state, schema)
                    following.append((guard, output, trace))
                elif isinstance(command, If):
                    test = _substitute(command.condition, state, schema)
                    following.extend(step(command.then, z3.And(guard, test), state, trace))
                    following.extend(step(command.otherwise, z3.And(guard, z3.Not(test)), state, trace))
                elif isinstance(command, Gate):
                    owner = "A" if set(command.targets) <= {"ac", "at"} else "B"
                    event = ("gate", owner, state["k" + owner], command.name, command.targets, None)
                    following.append((guard, state, trace + (event,)))
                elif isinstance(command, Measure):
                    owner = "A" if command.qubit == "at" else "B"
                    for outcome in (0, 1):
                        output = dict(state)
                        output[command.target] = z3.IntVal(outcome)
                        event = ("measure", owner, state["k" + owner], command.target, command.qubit, z3.IntVal(outcome))
                        following.append((guard, output, trace + (event,)))
                else:
                    raise Unsupported(f"Unsupported distillation schema command: {command}")
            current = following
        return current

    return step(block, *paths[0])


def _paper_invariant(v):
    return z3.And(v["kA"] == v["kB"], v["doneA"] == v["doneB"],
                  v["sentA"] == v["recvB"], v["sentB"] == v["recvA"],
                  z3.Implies(v["recvA"], v["rA"] == v["mB"]),
                  z3.Implies(v["recvB"], v["rB"] == v["mA"]),
                  v["doneA"] == z3.And(v["sentA"], v["recvA"]),
                  z3.Implies(v["doneA"], v["mA"] == v["mB"]))


@dataclass
class Distillation:
    attempt: Program
    controller: ControlSchema
    theta: object
    variant: object
    symbols: dict

    def program_text(self):
        from .pretty import format_program
        text = format_program(self.controller)
        for old, new in (("[ac, at]", "[a_c[kA], a_t[kA]]"),
                         ("[bc, bt]", "[b_c[kB], b_t[kB]]"),
                         ("M[at]", "M[a_t[kA]]"), ("M[bt]", "M[b_t[kB]]")):
            text = text.replace(old, new)
        return text + "\nFour fresh arrays are indexed by unbounded natural counters. n is a proof parameter."

    def _control_checks(self):
        schema, v = self.controller, self.symbols
        result = [check_implication(schema, self.theta, _paper_invariant(v),
                                    "Supplied invariant includes the required quantum-selector facts")]
        init_requirement = classical_wp(schema, schema.initialization, self.theta)
        result.append(check_implication(schema, True, init_requirement, "Initialization establishes the classical invariant"))
        pairs = list(schema.matching_pairs())
        if len(pairs) != 2:
            return result + [Obligation("Both classical directions are present", "schema structure", "FAILED")]
        for label, guard, block in pairs:
            result.append(check_implication(schema, z3.And(self.theta, guard), classical_wp(schema, block, self.theta),
                                            f"Control invariant is preserved: {label}"))
        result.append(check_implication(schema, z3.And(self.theta, v["kA"] < v["n"]), self.variant >= 0,
                                        "Ranking is nonnegative below n"))
        no_pair = z3.And(*[z3.Not(guard) for _, guard, _ in pairs])
        result.append(check_implication(schema, z3.And(self.theta, no_pair), schema.termination,
                                        "No deadlock under the invariant"))
        acc = z3.And(v["doneA"], v["doneB"], v["kA"] == v["kB"], v["kA"] < v["n"])
        result.append(check_implication(schema, z3.And(self.theta, v["kA"] < v["n"], schema.termination), acc,
                                        "Termination below n implies acceptance of the same attempt"))
        result.append(check_implication(schema, z3.And(self.theta, v["kA"] < v["n"], schema.termination),
                                        v["mA"] == v["mB"], "Exit selects the accepted quantum postcondition"))
        for label, guard, block in pairs:
            old = z3.FreshInt("old_rank")
            requirement = z3.substitute(classical_wp(schema, block, self.variant < old), (old, self.variant))
            result.append(check_implication(schema, z3.And(self.theta, v["kA"] < v["n"], guard), requirement,
                                            f"Ranking decreases at every communication: {label}"))
        # Inspect the actual commands, including index changes and quantum events.
        for label, block, precondition, initialization in [
            ("initialization", schema.initialization, z3.BoolVal(True), True),
            *[(label, block, z3.And(self.theta, guard), False) for label, guard, block in pairs],
        ]:
            count = 0
            failures = []
            for path_guard, output, events in _symbolic_paths(schema, block):
                premise = z3.And(schema.domains, precondition, path_guard)
                solver = schema.solver()
                solver.add(precondition, path_guard)
                feasible = solver.check()
                if feasible == z3.unsat:
                    continue
                if feasible == z3.unknown:
                    failures.append(Obligation(label, "schema path", "INCOMPLETE"))
                    continue
                count += 1
                if not events and not initialization:
                    # No quantum work: the quantum selector and index must stay unchanged.
                    goal = z3.And(output["kA"] == v["kA"], output["kB"] == v["kB"],
                                  output["mA"] == v["mA"], output["mB"] == v["mB"])
                else:
                    expected_index = z3.IntVal(0) if initialization else v["kA"] + 1
                    shape = []
                    for owner in ("A", "B"):
                        local = [event for event in events if event[1] == owner]
                        targets = ("ac", "at") if owner == "A" else ("bc", "bt")
                        expected = [("gate", "CNOT", targets), ("measure", "m" + owner, targets[1])]
                        actual = [(event[0], event[3], event[4]) for event in local]
                        shape.append(actual == expected)
                        shape.extend(event[2] == expected_index for event in local)
                        if actual == expected:
                            shape.append(output["m" + owner] == local[1][5])
                    goal = z3.And(*shape, output["kA"] == expected_index, output["kB"] == expected_index)
                    if not initialization:
                        goal = z3.And(goal, v["mA"] != v["mB"])
                goal = z3.And(goal, output["n"] == v["n"])
                check = _smt(label, premise, goal)
                if check.status != "PASSED":
                    failures.append(check)
            status = "FAILED" if any(o.status == "FAILED" for o in failures) else "INCOMPLETE" if failures else "PASSED"
            result.append(Obligation(f"Indexed quantum step matches the induction: {label}", "symbolic command paths",
                                     status, count,
                                     "Every path preserves n and either preserves the quantum selector or records both exact fresh-test outcomes at k+1; initialization uses index 0",
                                     failures[0].witness if failures else None))
        return result

    def verify(self):
        self.attempt.validate()
        self.controller.validate()
        if set(self.symbols) != set(self.controller.varmap) or any(
            not self.controller.varmap[name].symbol.eq(value) for name, value in self.symbols.items()
        ):
            raise Unsupported("The proof's symbols must match the declared controller variables")
        # The schema must use the very same test circuit at initialization/retry.
        # Every test event is checked structurally above; matrix identities below
        # are derived independently from the actual attempt program.
        report = Report("Unbounded BBPSSW distillation", "total correctness, every finite n >= 1")
        report.obligations.extend(self._control_checks())
        control_checks = tuple(report.obligations)
        local_start = len(report.obligations)
        paths = execute(self.attempt, self.attempt.initialization, {"mA": 0, "mB": 0})
        identity = sp.ImmutableMatrix(sp.eye(16))
        good_output = embed(projector(BELL), (0, 1), 4)
        accepted, rejected, good = sp.zeros(16), sp.zeros(16), sp.zeros(16)
        for state, kraus in paths:
            if state["mA"] == state["mB"]:
                accepted += kraus.H * kraus
                good += kraus.H * good_output * kraus
            else:
                rejected += kraus.H * kraus
        bell = {(x, z): clean(tensor(I2, X ** x * Z ** z) * BELL) for x, z in product((0, 1), repeat=2)}
        expected_pass = clean(sum((projector(tensor(bell[x, z], bell[x, w]))
                                   for x, z, w in product((0, 1), repeat=3)), sp.zeros(16)))
        expected_good = clean(sum((projector(tensor(bell[0, z], bell[0, z])) for z in (0, 1)), sp.zeros(16)))
        rejection = clean(identity - expected_pass)
        report.obligations.extend([
            _matrix_check("Accepted measurement branches have effect Pass", accepted, expected_pass,
                          "[Unitary + measurement semantics] T_uv = (M_u CNOT_A)(M_v CNOT_B); sum_u T_uu^dagger T_uu = Pass"),
            _matrix_check("Rejected measurement branches have effect Rej", rejected, rejection,
                          "sum_{u!=v} T_uv^dagger T_uv = Rej"),
            _matrix_check("Accepted Bell output has effect Good", good, expected_good,
                          "sum_u T_uu^dagger Bell_control T_uu = Good"),
            _matrix_check("All measurement branches preserve total probability", accepted + rejected, identity,
                          "sum_{u,v} T_uv^dagger T_uv = I"),
            _matrix_check("Pass and Rej are orthogonal", expected_pass * rejection, sp.zeros(16)),
            _psd_check("Good is bounded by Pass", expected_pass - expected_good),
        ])
        local_checks = tuple(report.obligations[local_start:])
        induction_start = len(report.obligations)
        report.obligations.extend(self._indexed_checks(expected_pass, expected_good, rejection, paths))
        indexed_checks=tuple(report.obligations[induction_start:])
        paper_start=len(report.obligations)
        if all(o.status=="PASSED" for o in report.obligations):
            report.obligations.extend(self._paper_checks(expected_pass,expected_good,rejection))
        else:
            report.obligations.extend(Obligation(f"Paper-rule Hoare derivation: E_{kind}","Hoare proof replay","INCOMPLETE",
                                                 detail="Earlier proof conditions failed; no complete derivation") for kind in ("pass","good"))
        paper_checks=tuple(report.obligations[paper_start:])
        prerequisites_passed = all(o.status == "PASSED" for o in report.obligations)
        report.obligations.append(Obligation(
            "Fresh-factor first-acceptance induction rule", "indexed proofs and controller composition", "PASSED" if prerequisites_passed else "INCOMPLETE",
            detail="E_pass(r,n)=Pass_r + Rej_r E_pass(r+1,n); E_good uses Good_r instead. "
                   "The empty suffix is zero. Distinct array indices give disjoint tensor support. "
                   "Local Kraus identities and the checked retry paths justify the universal step, including correlated inputs.",
            evidence=TextEvidence(
                "[Distributed-tot]\n"
                "The replayed Hoare trees above establish initialization, every communication and every ranking triple.\n"
                "At tested outcomes u=v, K_pass=I and K_good=Bell_control.\n"
                "At u!=v, K_kind=I_current tensor E_kind(k+1,n); the checked fresh-test paths use the derived pullback.\n"
                "[Assert-Eq] K_kind=0 for k>=n, matching theta and k<n.\n"
                "Distributed-tot checks complete communication coverage, nonnegative rank and absence of deadlock; Conseq establishes the requested postcondition.")))
        induction_checks = tuple(report.obligations[induction_start:])
        probability_start = len(report.obligations)
        report.obligations.extend(self._werner_checks(expected_pass, expected_good))
        probability_checks = tuple(report.obligations[probability_start:])
        report.derivation = ProofPlan(
            "Distributed-tot",
            "indexed tensor proofs and checked controller premises", report,
            groups=(ProofGroup("Classical initialization/communication, rank and exit", "classical Assign/If/Seq WP; unbounded SMT and indexed paths", control_checks),
                    ProofGroup("One-attempt quantum calculation", "Unitary and measurement pullbacks; exact matrix identities", local_checks),
                    ProofGroup("Indexed tensor derivation and induction", "replayed sum, product, frame and induction rules", indexed_checks),
                    ProofGroup("Paper-rule Hoare derivations", "local rules, Distributed-tot and Conseq", paper_checks),
                    ProofGroup("Probability and fidelity bounds", "exact Werner traces, arithmetic induction, trusted limit rule", probability_checks)))
        return report

    def _indexed_checks(self, passed, good, rejected, paths):
        """Connect the actual finite circuit to protocol-independent proof rules."""
        maps = {f"T{state['mA']}{state['mB']}_{i}": kraus for i,(state,kraus) in enumerate(paths)}
        outcomes = tuple((name, state["mA"] == state["mB"])
                         for name,(state,_) in zip(maps, paths))
        result = []
        for kind,target in (("pass", sp.eye(16)), ("good", embed(projector(BELL),(0,1),4))):
            kernel = Kernel({"Pass":passed, "Good":good, "Rej":rejected,
                             "Target":target, "I":sp.eye(16)}, maps)
            family = first_acceptance(f"E_{kind}", "Pass" if kind == "pass" else "Good", "Rej")
            # Construct the requested WP from the actual source outcomes,
            # independently of the proof generator's claimed endpoints.
            k,n = family.start,family.end
            branches = []
            for name,accepted in outcomes:
                suffix = indexed_terms.identity(k+1,n) if accepted else family(k+1,n)
                output = indexed_terms.local("Target" if accepted else "I",k)
                branches.append(indexed_terms.pullback(name,k,indexed_terms.tensor(output,suffix)))
            requested_wp = branches[0]
            for branch in branches[1:]:
                requested_wp = indexed_terms.add(requested_wp,branch)
            for label,goal_kind,generate in (
                (f"Indexed effect induction: E_{kind}", "induction", lambda: effect_induction(family,kernel)),
                (f"Indexed measurement pullback: E_{kind}", "pullback", lambda: framed_attempt(family,kernel,outcomes,"Target")),
            ):
                evidence = None
                try:
                    proof = generate()
                    if goal_kind == "induction":
                        if not isinstance(proof,Induction) or proof.family != family:
                            raise Unsupported("The induction proof does not establish the requested family")
                    elif (not isinstance(proof,Equality)
                          or (proof.left,proof.right) != (requested_wp,family(k,n))):
                        raise Unsupported("The proof does not establish the actual indexed measurement WP")
                    evidence = IndexedEvidence(kernel,proof,(family.start >= 0, family.start < family.end))
                    evidence.check()
                    result.append(Obligation(label,"indexed proof replay","PASSED",
                                             detail="Checked symbolic derivation",evidence=evidence))
                except Unsupported as error:
                    # No proof object, undecided side condition, or invalid step
                    # can establish the unbounded theorem.
                    result.append(Obligation(label,"indexed proof replay","INCOMPLETE",detail=str(error)))
        return result

    def _paper_checks(self,passed,good,rejected):
        from . import hoare as h
        layout=h.Layout(self.controller,{"ac":"kA","at":"kA","bc":"kB","bt":"kB"})
        v=self.symbols
        n=sp.Symbol("n",integer=True)
        k=sp.Symbol("kA",integer=True)
        accepted=z3.And(v["doneA"],v["doneB"],v["kA"]==v["kB"],v["kA"]<v["n"])
        result=[]
        for kind,target in (("pass",sp.eye(16)),("good",embed(projector(BELL),(0,1),4))):
            family=first_acceptance(f"E_{kind}","Pass" if kind=="pass" else "Good","Rej")
            kernel=Kernel({"Pass":passed,"Good":good,"Rej":rejected,"Target":target})
            target_formula=h.leaf(indexed_terms.tensor(indexed_terms.identity(0,k),indexed_terms.local("Target",k),indexed_terms.identity(k+1,n)))
            suffix=h.leaf(indexed_terms.tensor(indexed_terms.identity(0,k+1),family(k+1,n)))
            selector=h.choose(v["kA"]<v["n"],h.choose(v["mA"]==v["mB"],target_formula,suffix),h.ZERO)
            pre=h.Assertion(True,h.leaf(family(0,n)))
            invariant=h.Assertion(z3.And(self.theta,v["kA"]<v["n"]),selector)
            post=h.Assertion(accepted,h.I if kind=="pass" else target_formula)
            try:
                quantum=h.QuantumChecker(self.controller,kernel,(family,))
                checker=h.RuleChecker(self.controller,layout,quantum)
                proof=h.prove_distributed(self.controller,layout,pre,invariant,post,self.variant)
                if not isinstance(proof,h.Proof) or not h.same(proof.pre,pre) or not h.same(proof.post,post) or proof.block is not self.controller:
                    raise Unsupported("Hoare proof does not match the requested program and specification")
                definition="Target[k] = I" if kind=="pass" else "Target[k] = Bell[a_c[k],b_c[k]]"
                evidence=h.Evidence(checker,proof,(definition,))
                evidence.check()
                result.append(Obligation(f"Paper-rule Hoare derivation: E_{kind}","Hoare proof replay","PASSED",detail="Checked local rules, invariant, rank, deadlock and final Conseq",evidence=evidence))
            except Unsupported as error:
                result.append(Obligation(f"Paper-rule Hoare derivation: E_{kind}","Hoare proof replay","INCOMPLETE",detail=str(error)))
        return result

    def _werner_checks(self, passed, good):
        f = sp.Symbol("F", real=True)
        bell_projector = projector(BELL)
        rho = f * bell_projector + (1 - f) / 3 * (sp.eye(4) - bell_projector)
        p = sp.factor(sp.trace(passed * tensor(rho, rho)))
        g = sp.factor(sp.trace(good * tensor(rho, rho)))
        expected_p = f ** 2 + 2 * f * (1 - f) / 3 + 5 * (1 - f) ** 2 / 9
        expected_g = f ** 2 + (1 - f) ** 2 / 9
        result = [
            _matrix_check("Werner acceptance probability p(F)", sp.Matrix([p]), sp.Matrix([expected_p])),
            _matrix_check("Werner good-output probability g(F)", sp.Matrix([g]), sp.Matrix([expected_g])),
        ]
        zf = z3.Real("F")
        zp = zf * zf + 2 * zf * (1 - zf) / 3 + 5 * (1 - zf) ** 2 / 9
        zg = zf * zf + (1 - zf) ** 2 / 9
        result.append(_smt("Werner range and strict fidelity improvement for 1/2 < F < 1",
                           z3.And(zf > z3.RealVal("1/2"), zf < 1),
                           z3.And(zp > 0, zp < 1, zg > zf * zp, zg <= zp)))
        q, a, b, n = sp.symbols("q p g n", real=True)
        probability = 1 - q ** n
        good_mass = b / a * (1 - q ** n)
        # Substituting q=1-p verifies both induction steps as rational identities.
        step_p = sp.expand(1 - q ** (n + 1) - (a + q * probability)).subs(a, 1 - q)
        step_g = sp.expand(b / a * (1 - q ** (n + 1)) - (b + q * good_mass)).subs(a, 1 - q)
        result.extend([
            _matrix_check("Probability formulas have the zero-horizon base case",
                          sp.Matrix([probability.subs(n, 0), good_mass.subs(n, 0)]), sp.zeros(2, 1)),
            _matrix_check("Geometric acceptance formula satisfies the recurrence", sp.Matrix([sp.simplify(step_p)]), sp.zeros(1)),
            _matrix_check("Geometric good-mass formula satisfies the recurrence", sp.Matrix([sp.simplify(step_g)]), sp.zeros(1)),
        ])
        pp, gg, ss, tt = z3.Reals("bound_p bound_g acceptance_mass good_mass")
        qz = 1 - pp
        result.append(_smt("Probability-bound induction preserves 0 <= good mass <= acceptance mass <= 1",
                           z3.And(pp > 0, pp < 1, gg >= 0, gg <= pp, tt >= 0, tt <= ss, ss <= 1),
                           z3.And(gg + qz*tt >= 0, gg + qz*tt <= pp + qz*ss, pp + qz*ss <= 1)))
        result.append(_smt("The rejection factor satisfies the geometric-limit hypothesis",
                           z3.And(pp > 0, pp < 1), z3.And(1-pp > 0, 1-pp < 1)))
        result.append(Obligation("Apply the geometric-limit rule", "trusted real-analysis rule",
                                 "PASSED" if all(o.status == "PASSED" for o in result) else "INCOMPLETE",
                                 detail="For 0 < q < 1, q^n tends to zero; applying this standard lemma gives acceptance mass tending to one. No numerical limit is sampled.",
                                 evidence=TextEvidence("[Trusted geometric-limit lemma]\n"
                                                       "Premise checked by SMT: 0 < q=1-p < 1.\n"
                                                       "Lemma: lim q^n = 0 for such q.\n"
                                                       "Conclude: lim (1-q^n)=1; the checked g>F*p gives g/p>F.\n"
                                                       "The limit lemma itself is trusted, not proved by Z3.")))
        return result

    def bounds(self, fidelity=sp.Rational(4, 5), attempts=5):
        fidelity = sp.sympify(fidelity)
        if fidelity.has(sp.Float) or fidelity.free_symbols or not (sp.Rational(1, 2) < fidelity < 1):
            raise ValueError("Use an exact fidelity strictly between 1/2 and 1")
        if type(attempts) is not int or attempts < 1:
            raise ValueError("attempts must be a positive integer proof horizon")
        if not self.verify().verified:
            raise Unsupported("Probability and fidelity bounds require successful verification of the current protocol")
        p = fidelity ** 2 + 2 * fidelity * (1 - fidelity) / 3 + 5 * (1 - fidelity) ** 2 / 9
        g = fidelity ** 2 + (1 - fidelity) ** 2 / 9
        return {"assumption": "Independent Werner pairs, with the same exact input fidelity F",
                "proof_horizon": attempts, "input_fidelity": fidelity, "p": sp.factor(p), "g": sp.factor(g),
                "accepted_mass_lower_bound": sp.factor(1 - (1 - p) ** attempts),
                "bell_overlap_lower_bound": sp.factor(g / p * (1 - (1 - p) ** attempts)),
                "asymptotic_fidelity": sp.factor(g / p)}


def distillation(omit_bilateral_gate=None):
    if omit_bilateral_gate not in (None, "Alice", "Bob"):
        raise ValueError("omit_bilateral_gate must be None, 'Alice' or 'Bob'")
    test_a = seq(() if omit_bilateral_gate == "Alice" else Gate("CNOT", ("ac", "at")), Measure("mA", "at"))
    test_b = seq(() if omit_bilateral_gate == "Bob" else Gate("CNOT", ("bc", "bt")), Measure("mB", "bt"))
    attempt = Program("One bilateral BBPSSW test", (Variable("mA", "Alice", (0, 1)), Variable("mB", "Bob", (0, 1))),
                      ("ac", "bc", "at", "bt"), (Process("Alice", ("ac", "at"), test_a, ()),
                                                   Process("Bob", ("bc", "bt"), test_b, ())))
    variables = [NaturalVariable("n", "proof")]
    for owner, suffix in (("Alice", "A"), ("Bob", "B")):
        variables.append(NaturalVariable("k" + suffix, owner))
        variables.extend(Variable(name + suffix, owner, (0, 1)) for name in ("m", "r"))
        variables.extend(Variable(name + suffix, owner, (False, True)) for name in ("done", "sent", "recv"))
    v = {var.name: var.symbol for var in variables}
    processes = []
    for owner, suffix, other, qubits, test in (("Alice", "A", "B", ("ac", "at"), test_a),
                                              ("Bob", "B", "A", ("bc", "bt"), test_b)):
        retry = seq(Assign("k" + suffix, v["k" + suffix] + 1), test,
                    Assign("sent" + suffix, False), Assign("recv" + suffix, False))
        body = seq(If(z3.And(v["sent" + suffix], v["recv" + suffix]), seq(
            If(v["m" + suffix] == v["r" + suffix], seq(Assign("done" + suffix, True)), retry))))
        init = seq(Assign("k" + suffix, 0), Assign("r" + suffix, 0), Assign("done" + suffix, False),
                   test, Assign("sent" + suffix, False), Assign("recv" + suffix, False))
        branches = (
            Branch("send", z3.And(z3.Not(v["done" + suffix]), z3.Not(v["sent" + suffix])),
                   Send("c_" + suffix, v["m" + suffix]), seq(Assign("sent" + suffix, True), body)),
            Branch("receive", z3.And(z3.Not(v["done" + suffix]), z3.Not(v["recv" + suffix])),
                   Receive("c_" + other, "r" + suffix), seq(Assign("recv" + suffix, True), body)),
        )
        processes.append(Process(owner, qubits, init, branches))
    controller = ControlSchema(tuple(variables), tuple(processes))
    theta = _paper_invariant(v)
    variant = 2 * (v["n"] - v["kA"]) - z3.If(v["sentA"], 1, 0) - z3.If(v["recvA"], 1, 0)
    return Distillation(attempt, controller, theta, variant, v)
