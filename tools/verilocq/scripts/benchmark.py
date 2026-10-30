"""Measure the Quickstart protocols for the paper's evaluation tables.

Every run executes the Notebook's own definitions in a fresh interpreter, so no
proof cache is shared between runs. Reported times are medians over the runs.

Premise time is split by kind. Classical premises are decided by Z3. Quantum
premises compute weakest preconditions and check exact operator inequalities.
For distillation, the controller checks count as classical, and the one-attempt
Kraus identities, indexed derivations and Hoare replay count as quantum. The
Werner bounds are timed separately. Compiling the quantum predicates of the
assertions into exact matrices counts as quantum, and compiling classical
formulas as classical. Parsing and report assembly are included in the total only.

    .venv/bin/python scripts/benchmark.py --runs 3 --json benchmark.json
"""

import argparse
from collections import defaultdict
import functools
import json
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
NOTEBOOK = ROOT / "Quickstart.ipynb"

CASES = ("RSP", "PhaseChoice", "Teleportation", "EntanglementSwapping", "NonlocalCNOT", "Distillation")

# Each faulty variant deletes every occurrence of the listed source lines.
MUTATIONS = {
    "RSP": {"omit Z": ("if r = 1 then Z[B]; fi;",)},
    "Teleportation": {"omit X": ("if j = 1 then X[B]; fi;",), "omit Z": ("if i = 1 then Z[B]; fi;",)},
    "EntanglementSwapping": {"omit X": ("if j = 1 then X[B]; fi;",), "omit Z": ("if i = 1 then Z[A]; fi;",)},
    "NonlocalCNOT": {"omit X": ("if i = 1 then X[T]; fi;",), "omit Z": ("if j = 1 then Z[C]; fi;",)},
    "Distillation": {"omit Alice CNOT": ("CNOT[a_c[kA],a_t[kA]];",), "omit Bob CNOT": ("CNOT[b_c[kB],b_t[kB]];",)},
}

CLASSICAL_KINDS = {"classical SMT", "symbolic arithmetic", "symbolic command paths", "schema path", "schema structure"}


class Clock:
    """Exclusive time per kind: a nested timed call is charged to its own kind."""

    def __init__(self):
        self.totals = defaultdict(float)
        self.stack = []

    def wrap(self, modules, owner, name, kind):
        original = getattr(owner, name)

        @functools.wraps(original)
        def timed(*args, **kwargs):
            start = time.perf_counter()
            self.stack.append([kind, 0.0])
            try:
                return original(*args, **kwargs)
            finally:
                elapsed = time.perf_counter() - start
                charged, children = self.stack.pop()
                self.totals[charged] += elapsed - children
                if self.stack:
                    self.stack[-1][1] += elapsed

        setattr(owner, name, timed)
        for module in modules:
            if getattr(module, name, None) is original:
                setattr(module, name, timed)

    def snapshot(self):
        return dict(self.totals)


def _commands(block):
    for command in block:
        yield command
        kind = type(command).__name__
        if kind == "If":
            yield from _commands(command.then)
            yield from _commands(command.otherwise)


def _program_statistics(protocol):
    parsed = protocol._parsed
    arrays = set(parsed.arrays)
    commands = []
    for process in parsed.processes:
        commands.extend(_commands(process.init))
        for branch in process.branches:
            commands.extend(_commands(branch.body))
    gates = set()
    for command in commands:
        kind = type(command).__name__
        if kind == "Gate":
            gates.add(command.name)
        elif kind == "Measure":
            gates.add("M")
        elif kind == "Reset":
            gates.add("reset")
    branches = [b for p in parsed.processes for b in p.branches]
    return {
        "processes": len(parsed.processes),
        "qubits": sum(len([q for q in p.qubits if q not in arrays]) for p in parsed.processes) + len(parsed.references),
        "references": len(parsed.references),
        "arrays": len(arrays),
        "classical_variables": len(parsed.variables),
        "phase_parameters": len(parsed.parameters),
        "state_parameters": len(parsed.states),
        "channels": len({b.action.channel for b in branches}),
        "branches": len(branches),
        "measurements": sum(type(c).__name__ == "Measure" for c in commands),
        "gates": sorted(gates),
        "program_lines": sum(1 for line in protocol.source.splitlines() if line.strip()),
    }


def _lines(value):
    return sum(1 for line in str(value).splitlines() if line.strip())


def worker(case, mutation, call):
    """Run one verify call of a case in this interpreter and print one JSON line."""
    import verilocq.derivation as derivation
    import verilocq.distillation as distillation
    import verilocq.frontend as frontend
    import verilocq.hoare as hoare
    import verilocq.verifier as verifier

    modules = (derivation, distillation, frontend, hoare, verifier)
    clock = Clock()
    clock.wrap(modules, verifier, "check_hoare", "quantum")
    clock.wrap(modules, verifier, "check_implication", "classical")
    clock.wrap(modules, verifier, "verify_distributed", "other")
    clock.wrap(modules, frontend, "_formula", "classical")
    clock.wrap(modules, frontend, "_classical_formula", "classical")
    clock.wrap(modules, frontend.AssertionSpec, "_compile", "quantum")
    clock.wrap(modules, distillation, "_smt", "classical")
    clock.wrap(modules, distillation, "_matrix_check", "quantum")
    clock.wrap(modules, distillation, "_psd_check", "quantum")
    clock.wrap(modules, distillation.Distillation, "verify", "quantum")
    clock.wrap(modules, distillation.Distillation, "_control_checks", "classical")
    clock.wrap(modules, distillation.Distillation, "_indexed_checks", "quantum")
    clock.wrap(modules, distillation.Distillation, "_paper_checks", "quantum")
    clock.wrap(modules, distillation.Distillation, "_werner_checks", "bounds")

    bound_names = set()
    werner = distillation.Distillation._werner_checks

    def recorded_werner(self, *args, **kwargs):
        result = werner(self, *args, **kwargs)
        bound_names.update(o.name for o in result)
        return result

    distillation.Distillation._werner_checks = recorded_werner

    cells = [c for c in json.loads(NOTEBOOK.read_text(encoding="utf-8"))["cells"] if c["cell_type"] == "code"]
    namespace = {"__name__": "__benchmark__"}
    exec(compile("".join(cells[0]["source"]), "<cell 0>", "exec"), namespace)
    real_program, real_verify = namespace["program"], namespace["verify"]
    deletions = MUTATIONS[case][mutation] if mutation else ()
    records, statistics_by_name = [], {}

    def program(source):
        match = re.search(r"program\s+(\w+)", source)
        if match and match.group(1) == case:
            for line in deletions:
                if line not in source:
                    raise SystemExit(f"Mutation line not found in {case}: {line}")
                source = source.replace(line, "")
        protocol = real_program(source)
        statistics_by_name[protocol.name] = _program_statistics(protocol)
        return protocol

    calls = [0]

    def verify(pre, protocol, post, **kwargs):
        if protocol.name != case:
            return None
        calls[0] += 1
        if calls[0] - 1 != call:
            return None
        before = clock.snapshot()
        start = time.perf_counter()
        result = real_verify(pre, protocol, post, **kwargs)
        total = time.perf_counter() - start
        after = clock.snapshot()
        spent = {k: after.get(k, 0.0) - before.get(k, 0.0) for k in ("classical", "quantum", "bounds")}
        obligations = [o for o in result.obligations if o.name not in bound_names]
        failed = [o for o in obligations if o.status != "PASSED"]
        records.append({
            "case": case,
            "specification": str(pre),
            "status": result.status,
            "premises": len(obligations),
            "classical_premises": sum(o.kind in CLASSICAL_KINDS for o in obligations),
            "quantum_premises": sum(o.kind not in CLASSICAL_KINDS for o in obligations),
            "checked_cases": sum(o.cases for o in obligations),
            "annotation_lines": _lines(kwargs.get("invariant", "")) + _lines(kwargs.get("decreases", "")),
            "time_total": total,
            "time_classical": spent["classical"],
            "time_quantum": spent["quantum"],
            "time_bounds": spent["bounds"],
            "first_failure": failed[0].name if failed else None,
            "witness": failed[0].witness if failed else None,
            "statistics": statistics_by_name[case],
        })
        return result

    namespace["program"], namespace["verify"] = program, verify
    for index, cell in enumerate(cells[1:], start=1):
        source = "".join(cell["source"])
        if ".bounds(" in source:
            continue
        exec(compile(source, f"<cell {index}>", "exec"), namespace)
    if not records:
        raise SystemExit(f"No verify call {call} for {case} in the Notebook")
    print(json.dumps({"calls": calls[0], "records": records}, default=str))


def _run(case, mutation, call):
    command = [sys.executable, str(Path(__file__).resolve()), "--worker", case, "--call", str(call)]
    if mutation:
        command += ["--mutation", mutation]
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if completed.returncode != 0:
        raise SystemExit(f"{case} {mutation or ''} failed:\n{completed.stderr}")
    return json.loads(completed.stdout.strip().splitlines()[-1])


def _measure(case, mutation, runs):
    """Run every verify call of a case in its own interpreter, `runs` times each."""
    first = _run(case, mutation, 0)
    combined = []
    for call in range(first["calls"]):
        records = [first["records"]] if call == 0 else []
        while len(records) < runs:
            records.append(_run(case, mutation, call)["records"])
        combined += _median(records)
    return combined


def _median(runs):
    """Combine per-run records (same order each run), taking medians of times."""
    combined = []
    for records in zip(*runs):
        record = dict(records[0])
        for key in ("time_total", "time_classical", "time_quantum", "time_bounds"):
            record[key] = statistics.median(r[key] for r in records)
        combined.append(record)
    return combined


def _environment():
    import sympy
    import z3
    machine = platform.processor() or platform.machine()
    memory = None
    if sys.platform == "darwin":
        read = lambda key: subprocess.run(["sysctl", "-n", key], capture_output=True, text=True).stdout.strip()
        machine, memory = read("machdep.cpu.brand_string") or machine, int(read("hw.memsize")) // 2**30
    git = lambda *a: subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    source_files = sorted((ROOT / "verilocq").glob("*.py"))
    return {
        "machine": machine, "memory_gb": memory, "os": platform.platform(),
        "python": platform.python_version(), "z3": z3.get_version_string(), "sympy": sympy.__version__,
        "commit": git("rev-parse", "--short", "HEAD"), "dirty": bool(git("status", "--porcelain", "--", ".")),
        "source_lines": sum(len(f.read_text(encoding="utf-8").splitlines()) for f in source_files),
        "source_lines_nonblank": sum(
            1 for f in source_files for line in f.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.strip().startswith("#")),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--json", type=Path)
    parser.add_argument("--worker")
    parser.add_argument("--mutation")
    parser.add_argument("--call", type=int, default=0)
    args = parser.parse_args()
    if args.worker:
        worker(args.worker, args.mutation, args.call)
        return

    results = {"environment": _environment(), "runs": args.runs, "cases": [], "faulty": []}
    for case in CASES:
        results["cases"] += _measure(case, None, args.runs)
        for mutation in MUTATIONS.get(case, {}):
            results["faulty"] += [{**r, "mutation": mutation} for r in _measure(case, mutation, args.runs)]

    env = results["environment"]
    print(f"{env['machine']}, {env['memory_gb']} GB, {env['os']}")
    print(f"Python {env['python']}, Z3 {env['z3']}, SymPy {env['sympy']}, commit {env['commit']}"
          f"{' (dirty)' if env['dirty'] else ''}, {env['source_lines']} source lines, median of {args.runs}")
    print(f"\n{'case':22s}{'spec':26s}{'prem':>5s}{'cl':>4s}{'qu':>4s}{'cases':>6s}{'ann':>5s}"
          f"{'classical':>11s}{'quantum':>9s}{'bounds':>8s}{'total':>8s}  status")
    for r in results["cases"]:
        print(f"{r['case']:22s}{r['specification'][:25]:26s}{r['premises']:5d}{r['classical_premises']:4d}"
              f"{r['quantum_premises']:4d}{r['checked_cases']:6d}{r['annotation_lines']:5d}"
              f"{r['time_classical']:11.2f}{r['time_quantum']:9.2f}{r['time_bounds']:8.2f}{r['time_total']:8.2f}  {r['status']}")
    print()
    for r in results["cases"]:
        s = r["statistics"]
        print(f"{r['case']:22s}" + ", ".join(f"{k}={v}" for k, v in s.items()))
    print()
    for r in results["faulty"]:
        print(f"{r['case']:22s}{r['mutation']:17s}{r['status']:14s}{r['time_total']:7.2f}s  "
              f"{r['first_failure']}  {r['witness']}")
    if args.json:
        args.json.write_text(json.dumps(results, indent=2, default=str), encoding="utf-8")


if __name__ == "__main__":
    main()
