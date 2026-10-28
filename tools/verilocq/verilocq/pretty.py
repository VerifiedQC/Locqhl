"""Readable rendering of the actual DSL objects used by the verifier."""

import z3

from .syntax import Assign, Gate, If, Measure, Receive, Reset, Send, Skip, expr


def format_expression(value):
    """Render a backend expression in the public source notation."""
    value = expr(value)
    if z3.is_true(value):
        return "true"
    if z3.is_false(value):
        return "false"
    if value.num_args() == 0:
        return str(value)
    args = value.children()
    kind = value.decl().kind()
    if kind == z3.Z3_OP_NOT:
        return f"not ({format_expression(args[0])})"
    if kind == z3.Z3_OP_ITE:
        if z3.is_int_value(args[1]) and z3.is_int_value(args[2]) and args[1].as_long() == 1 and args[2].as_long() == 0:
            return f"[{format_expression(args[0])}]"
        return f"if {format_expression(args[0])} then {format_expression(args[1])} else {format_expression(args[2])}"
    operators = {z3.Z3_OP_AND: "and", z3.Z3_OP_OR: "or", z3.Z3_OP_IMPLIES: "=>",
                 z3.Z3_OP_EQ: "<=>" if z3.is_bool(args[0]) else "=", z3.Z3_OP_DISTINCT: "!=",
                 z3.Z3_OP_LE: "<=", z3.Z3_OP_LT: "<", z3.Z3_OP_GE: ">=", z3.Z3_OP_GT: ">",
                 z3.Z3_OP_ADD: "+", z3.Z3_OP_SUB: "-", z3.Z3_OP_MUL: "*", z3.Z3_OP_MOD: "%"}
    if kind == z3.Z3_OP_UMINUS:
        return f"-({format_expression(args[0])})"
    if kind in operators:
        return "(" + f" {operators[kind]} ".join(format_expression(a) for a in args) + ")"
    return str(value)


def format_block(block, indent=0):
    prefix = " " * indent
    lines = []
    for command in block:
        if isinstance(command, Assign):
            lines.append(f"{prefix}{command.target} := {format_expression(command.value)};")
        elif isinstance(command, Gate):
            parameters = "(" + ", ".join(str(p) for p in command.parameters) + ")" if command.parameters else ""
            lines.append(f"{prefix}{command.name}{parameters}[{', '.join(command.targets)}];")
        elif isinstance(command, Measure):
            lines.append(f"{prefix}{command.target} := M[{command.qubit}];")
        elif isinstance(command, Reset):
            lines.append(f"{prefix}{command.qubit} := |0>;")
        elif isinstance(command, Skip):
            lines.append(prefix + "skip;")
        elif isinstance(command, If):
            lines.append(f"{prefix}if {format_expression(command.condition)} then")
            lines.append(format_block(command.then, indent + 2) or prefix + "  skip;")
            if command.otherwise:
                lines.append(prefix + "else")
                lines.append(format_block(command.otherwise, indent + 2))
            lines.append(prefix + "fi;")
    return "\n".join(lines)


def format_program(program):
    lines = [program.name, f"Registers (tensor order): {', '.join(program.registers)}"]
    if program.references:
        lines.append(f"Read-only reference: {', '.join(program.references)}")
    for process in program.processes:
        lines.append(f"\nProcess {process.name}, owns {process.qubits}:")
        lines.append(format_block(process.init, 2))
        if process.branches:
            lines.append("  do")
            for branch in process.branches:
                action = branch.action
                communication = (f"{action.channel}!{expr(action.value)}" if isinstance(action, Send)
                                 else f"{action.channel}?{action.target}")
                lines.append(f"    [] {expr(branch.guard)}; {communication} ->  # {branch.name}")
                lines.append(format_block(branch.body, 6))
            lines.append("  od")
    return "\n".join(lines)
