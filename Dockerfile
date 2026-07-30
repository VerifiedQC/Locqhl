# Reproducible build of the LocQHL Rocq mechanization.
#
# Pins the Rocq Prover 9.1 toolchain and compiles the vendored QuantumLib +
# Core/ from a clean checkout. One command reproduces the full verified build:
#
#   docker build -t locqhl .
#   docker run --rm locqhl scripts/check-admits.sh   # optional: re-run the gate
#
# Base image: the official Rocq image (rocq/rocq-prover:<version>), which ships
# Rocq 9.1.1 on OCaml 4.14.2+flambda. It runs as the non-root `rocq` user with
# an `opam exec --` entrypoint; inside RUN steps we prefix `opam exec --` so the
# `rocq` binary (needed by `rocq makefile`) is on PATH.
# NOTE: this image is published for linux/amd64; on arm64 hosts it runs under
# emulation (slower). CI runners (ubuntu-latest, amd64) build it natively.
FROM rocq/rocq-prover:9.1

WORKDIR /home/rocq/locqhl
COPY --chown=rocq:rocq . .

# Build vendored QuantumLib then Core/. `make` invokes `rocq makefile`.
RUN opam exec -- make -j"$(nproc)"

# Default: show that the artifact builds and report the admit gate.
CMD ["bash", "-lc", "bash scripts/check-admits.sh"]
