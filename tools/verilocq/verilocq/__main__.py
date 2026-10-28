import argparse
import json

from .distillation import distillation
from .examples import (audit_pair_orders, audit_teleportation_orders,
                       entanglement_swapping, remote_cnot, teleportation,
                       remote_state_preparation, scheduler_phase_choice)


def main():
    parser = argparse.ArgumentParser(description="Exact LOCC case-study verifier")
    parser.add_argument("--case", choices=("rsp", "phase-choice", "teleportation", "swapping", "remote-cnot", "distillation", "all"), default="all")
    parser.add_argument("--omit", choices=("X", "Z"), help="Delete a correction in the finite examples")
    parser.add_argument("--omit-bilateral-gate", choices=("Alice", "Bob"), help="Delete a local CNOT from distillation")
    parser.add_argument("--json", action="store_true", help="Print one valid JSON document")
    parser.add_argument("--audit-orders", action="store_true", help="Also check both complete orders in the finite examples")
    args = parser.parse_args()
    factories = {"rsp": remote_state_preparation, "phase-choice": lambda omitted: scheduler_phase_choice(),
                 "teleportation": teleportation, "swapping": entanglement_swapping, "remote-cnot": remote_cnot}
    selected = list(factories) + ["distillation"] if args.case == "all" else [args.case]
    results = []
    succeeded = True
    for name in selected:
        case = distillation(args.omit_bilateral_gate) if name == "distillation" else factories[name](args.omit)
        report = case.verify()
        entry = {"case": name, "program": report.program, "status": report.status,
                 "mode": report.mode, "obligations": report.records()}
        succeeded = succeeded and report.verified
        if args.audit_orders and name in {"teleportation", "swapping", "remote-cnot"}:
            if name == "teleportation":
                audits = audit_teleportation_orders(case)
                entry["audits"] = [{k: v for k, v in a.items() if k != "channel_matrix"} for a in audits]
                succeeded = succeeded and all(a["identity_channel"] for a in audits)
            else:
                audit = audit_pair_orders(case)
                entry["audits"] = audit.records()
                succeeded = succeeded and audit.verified
        results.append(entry)
        if not args.json:
            print(report)
            if "audits" in entry:
                for audit in entry["audits"]:
                    print(audit)
            print()
    if args.json:
        print(json.dumps({"status": "VERIFIED" if succeeded else "NOT_VERIFIED", "case_studies": results}, indent=2))
    return 0 if succeeded else 1


if __name__ == "__main__":
    raise SystemExit(main())
