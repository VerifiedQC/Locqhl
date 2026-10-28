"""Build the concise Hoare-triple walkthrough."""

from pathlib import Path
from textwrap import dedent
import nbformat as nbf

ROOT = Path(__file__).resolve().parents[1]


def md(source):
    return nbf.v4.new_markdown_cell(dedent(source).strip())


def code(source):
    return nbf.v4.new_code_cell(dedent(source).strip())


cells = [
    md(r'''
    # VeriLocQ
    '''),
    code(r'''
    from pathlib import Path
    import sys

    candidates = [Path.cwd(), Path.cwd() / "tools" / "verilocq", Path.cwd() / "verilocq", Path.cwd().parent]
    ROOT = next(p.resolve() for p in candidates if (p / "verilocq" / "frontend.py").is_file())
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))

    from verilocq import program, assertion, verify
    '''),
    md(r'''
    ## RSP

    $R(\alpha)=\operatorname{diag}(1,e^{i\alpha})$,
    $|\psi_\alpha\rangle=(|0\rangle+e^{i\alpha}|1\rangle)/\sqrt2$.
    `Equator(alpha)[B]` is its projector.
    '''),
    code(r'''
    rsp = program("""
    program RSP {
      process Alice {
        qubit A;
        phase alpha;
        bit m;
        bool d;

        R(alpha)[A];
        H[A];
        m := M[A];
        d := false;
        do
          [] send: not d; c!m -> d := true;
        od
      }
      ||
      process Bob {
        qubit B;
        bit r, p;

        p := 0;
        do
          [] receive: p = 0; c?r ->
            if r = 1 then Z[B]; fi;
            p := 1;
        od
      }
    }
    """)
    '''),
    code(r'''
    rsp_report = verify(
        "{ true ; Bell[A,B] }",
        rsp,
        "{ true ; Equator(alpha)[B] }",
        invariant="{ d <=> p=1 ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
        decreases="1-[d]",
    )
    # Use rsp_report.explain() to open all proof steps at once.
    rsp_report
    '''),
    md(r'''
    ### Failure: missing Z correction

    For measurement outcome `m=1`, Bob gets $Z|\psi_\alpha\rangle$ instead of $|\psi_\alpha\rangle$.
    '''),
    code(r'''
    bad_rsp = program("""
    program RSPMissingCorrection {
      process Alice {
        qubit A;
        phase alpha;
        bit m;
        bool d;

        R(alpha)[A];
        H[A];
        m := M[A];
        d := false;
        do
          [] send: not d; c!m -> d := true;
        od
      }
      ||
      process Bob {
        qubit B;
        bit r, p;

        p := 0;
        do
          [] receive: p = 0; c?r ->
            # BUG: the conditional Z correction is missing.
            p := 1;
        od
      }
    }
    """)
    '''),
    code(r'''
    bad_rsp_report = verify(
        "{ true ; Bell[A,B] }",
        bad_rsp,
        "{ true ; Equator(alpha)[B] }",
        invariant="{ d <=> p=1 ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
        decreases="1-[d]",
    )
    bad_rsp_report
    '''),
    md(r'''
    ## Teleportation

    `R` is a read-only reference; preserving its Bell pair specifies transfer of an arbitrary input state.
    '''),
    code(r'''
    tele = program("""
    program Teleportation {
      reference R;

      process Alice {
        qubits A1, A2;
        bit m1, m2, pA;
        bool dAz, dAx;

        CNOT[A1,A2];
        H[A1];
        m1 := M[A1];
        m2 := M[A2];
        pA := 0;
        dAz := false;
        dAx := false;
        do
          [] send_z: pA = 0 and not dAz; c_z!m1 ->
            dAz := true;
            if dAz and dAx then pA := 1; fi;
          [] send_x: pA = 0 and not dAx; c_x!m2 ->
            dAx := true;
            if dAz and dAx then pA := 1; fi;
        od
      }
      ||
      process Bob {
        qubit B;
        bit i, j, pB;
        bool dBz, dBx;

        pB := 0;
        dBz := false;
        dBx := false;
        do
          [] receive_z: pB = 0 and not dBz; c_z?i ->
            dBz := true;
            if dBz and dBx then
              if j = 1 then X[B]; fi;
              if i = 1 then Z[B]; fi;
              pB := 1;
            fi;
          [] receive_x: pB = 0 and not dBx; c_x?j ->
            dBx := true;
            if dBz and dBx then
              if j = 1 then X[B]; fi;
              if i = 1 then Z[B]; fi;
              pB := 1;
            fi;
        od
      }
    }
    """)
    '''),
    code(r'''
    tele_report = verify(
        "{ true ; Bell[R,A1] * Bell[A2,B] }",
        tele,
        "{ true ; Bell[R,B] }",
        invariant="""{
          pA=pB and dAz=dBz and dAx=dBx
          and ((pB=1) <=> (dBz and dBx))
          and (dBz => i=m1) and (dBx => j=m2)
          ; X[B]^((1-pB)*m2) * Z[B]^((1-pB)*m1) * Bell[R,B]
        }""",
        decreases="2-[dAz]-[dAx]",
    )
    tele_report
    '''),
    md(r'''
    ## Entanglement swapping
    '''),
    code(r'''
    swap = program("""
    program EntanglementSwapping {
      process Charlie {
        qubits CA, CB;
        bit m1, m2;
        bool dCA, dCB;

        CNOT[CA,CB];
        H[CA];
        m1 := M[CA];
        m2 := M[CB];
        dCA := false;
        dCB := false;
        do
          [] send_a: not dCA; c_A!m1 -> dCA := true;
          [] send_b: not dCB; c_B!m2 -> dCB := true;
        od
      }
      ||
      process Alice {
        qubit A;
        bit i, pA;

        pA := 0;
        do
          [] receive: pA = 0; c_A?i ->
            if i = 1 then Z[A]; fi;
            pA := 1;
        od
      }
      ||
      process Bob {
        qubit B;
        bit j, pB;

        pB := 0;
        do
          [] receive: pB = 0; c_B?j ->
            if j = 1 then X[B]; fi;
            pB := 1;
        od
      }
    }
    """)
    '''),
    code(r'''
    swap_report = verify(
        "{ true ; Bell[A,CA] * Bell[B,CB] }",
        swap,
        "{ true ; Bell[A,B] }",
        invariant="""{
          (dCA <=> pA=1) and (dCB <=> pB=1)
          and (pA=1 => i=m1) and (pB=1 => j=m2)
          ; X[B]^((1-pB)*m2) * Z[A]^((1-pA)*m1) * Bell[A,B]
        }""",
        decreases="2-[dCA]-[dCB]",
    )
    swap_report
    '''),
    md(r'''
    ## Non-local CNOT

    Read-only references `RC,RT` specify the complete two-qubit channel.
    '''),
    code(r'''
    cnot = program("""
    program NonlocalCNOT {
      reference RC, RT;

      process Alice {
        qubits C, A;
        bit m1, j, pA;
        bool dA;

        CNOT[C,A];
        m1 := M[A];
        pA := 0;
        dA := false;
        do
          [] send: not dA; c_1!m1 -> dA := true;
          [] receive: pA = 0; c_2?j ->
            if j = 1 then Z[C]; fi;
            pA := 1;
        od
      }
      ||
      process Bob {
        qubits B, T;
        bit m2, i, pB;
        bool dB;

        CNOT[B,T];
        H[B];
        m2 := M[B];
        pB := 0;
        dB := false;
        do
          [] receive: pB = 0; c_1?i ->
            if i = 1 then X[T]; fi;
            pB := 1;
          [] send: not dB; c_2!m2 -> dB := true;
        od
      }
    }
    """)
    '''),
    code(r'''
    cnot_report = verify(
        "{ true ; Bell[RC,C] * Bell[RT,T] * Bell[A,B] }",
        cnot,
        "{ true ; CNOT[C,T] * (Bell[RC,C] * Bell[RT,T]) }",
        invariant="""{
          (dA <=> pB=1) and (dB <=> pA=1)
          ; X[T]^((1-pB)*m1) * Z[C]^((1-pA)*m2) * CNOT[C,T] * (Bell[RC,C] * Bell[RT,T])
        }""",
        decreases="2-[dA]-[dB]",
    )
    cnot_report
    '''),
    md(r'''
    ## Distillation

    A rejection increments `kA,kB` and tests fresh pairs. Agreement sets `doneA,doneB` and exits the loops.
    '''),
    code(r'''
    distill = program("""
    program Distillation {
      process Alice {
        array a_c, a_t;
        nat kA;
        bit mA, rA;
        bool doneA, sentA, recvA;

        kA := 0;
        rA := 0;
        doneA := false;
        CNOT[a_c[kA],a_t[kA]];
        mA := M[a_t[kA]];
        sentA := false;
        recvA := false;
        do
          [] send: not doneA and not sentA; c_A!mA ->
            sentA := true;
            if sentA and recvA then
              if mA = rA then doneA := true;
              else
                kA := kA + 1;
                CNOT[a_c[kA],a_t[kA]];
                mA := M[a_t[kA]];
                sentA := false;
                recvA := false;
              fi;
            fi;
          [] receive: not doneA and not recvA; c_B?rA ->
            recvA := true;
            if sentA and recvA then
              if mA = rA then doneA := true;
              else
                kA := kA + 1;
                CNOT[a_c[kA],a_t[kA]];
                mA := M[a_t[kA]];
                sentA := false;
                recvA := false;
              fi;
            fi;
        od
      }
      ||
      process Bob {
        array b_c, b_t;
        nat kB;
        bit mB, rB;
        bool doneB, sentB, recvB;

        kB := 0;
        rB := 0;
        doneB := false;
        CNOT[b_c[kB],b_t[kB]];
        mB := M[b_t[kB]];
        sentB := false;
        recvB := false;
        do
          [] send: not doneB and not sentB; c_B!mB ->
            sentB := true;
            if sentB and recvB then
              if mB = rB then doneB := true;
              else
                kB := kB + 1;
                CNOT[b_c[kB],b_t[kB]];
                mB := M[b_t[kB]];
                sentB := false;
                recvB := false;
              fi;
            fi;
          [] receive: not doneB and not recvB; c_A?rB ->
            recvB := true;
            if sentB and recvB then
              if mB = rB then doneB := true;
              else
                kB := kB + 1;
                CNOT[b_c[kB],b_t[kB]];
                mB := M[b_t[kB]];
                sentB := false;
                recvB := false;
              fi;
            fi;
        od
      }
    }
    """)
    '''),
    md(r'''
    ### Hoare triples

    $E_n^{pass}$ and $E_n^{good}$ are the paper's first-acceptance effects.
    `K_pass` and `K_good` are its quantum invariants. The proof parameter $n\ge1$ does not bound execution.
    '''),
    code(r'''
    theta = """
    kA=kB and (doneA <=> doneB)
    and (sentA <=> recvB) and (sentB <=> recvA)
    and (recvA => rA=mB) and (recvB => rB=mA)
    and (doneA <=> (sentA and recvA)) and (doneA => mA=mB)
    """
    t = "2*(n-kA)-[sentA]-[recvA]"

    distill_pass = verify(
        "{ true ; E_pass(0,n) }",
        distill,
        "{ doneA and doneB and kA=kB and kA<n ; I }",
        invariant=assertion(theta, "K_pass(kA,mA,mB,n)"),
        decreases=t,
    )
    distill_pass
    '''),
    code(r'''
    distill_good = verify(
        "{ true ; E_good(0,n) }",
        distill,
        "{ doneA and doneB and kA=kB and kA<n ; Bell[a_c[kA],b_c[kB]] }",
        invariant=assertion(theta, "K_good(kA,mA,mB,n)"),
        decreases=t,
    )
    distill_good
    '''),
    md(r'''
    ### Probability and fidelity bounds

    For independent Werner pairs with $1/2<F<1$, the checked first-acceptance triples give the acceptance
    and Bell-overlap bounds below. The bound proof checks the one-attempt probabilities, zero base case,
    geometric recurrences, and strict fidelity improvement.
    '''),
    code(r'''
    distill_bounds = distill_good.bounds(fidelity="4/5", attempts=5)
    distill_bounds
    '''),
    md(r'''
    ## PhaseChoice

    The scheduler chooses 0 or 1; the output predicate records that choice in `s`.
    '''),
    code(r'''
    phase_choice = program("""
    program PhaseChoice {
      gate U {
        0: sqrt(9/10)*I + i*sqrt(1/10)*Z;
        1: sqrt(7/10)*I + i*sqrt(3/10)*Z;
      }

      process Alice {
        qubit A;
        bool a;

        a := false;
        do
          [] choose_zero: not a; c!0 -> a := true;
          [] choose_one:  not a; c!1 -> a := true;
        od
      }
      ||
      process Bob {
        qubit B;
        bit s;
        bool b;

        b := false;
        do
          [] receive: not b; c?s ->
            U(s)[B];
            b := true;
        od
      }
    }
    """)
    '''),
    code(r'''
    phase_report = verify(
        "{ true ; Bell[A,B] }",
        phase_choice,
        "{ true ; U(s)[B] * Bell[A,B] }",
        invariant="{ a <=> b ; U(s)[B]^[a] * Bell[A,B] }",
        decreases="1-[a]",
    )
    phase_report
    '''),
]
cells[1].metadata["jupyter"] = {"source_hidden": True}
notebook = nbf.v4.new_notebook(cells=cells)
notebook.metadata = {
    "kernelspec": {"display_name": "Python (VeriLocQ .venv)", "language": "python", "name": "python3"},
    "language_info": {"name": "python", "file_extension": ".py", "mimetype": "text/x-python"},
}
nbf.write(notebook, ROOT / "Quickstart.ipynb")
print(ROOT / "Quickstart.ipynb")
