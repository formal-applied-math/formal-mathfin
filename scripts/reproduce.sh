#!/usr/bin/env bash
# Reproduce a release's claims from a clean clone, with elan installed.
#
#   scripts/reproduce.sh            the proofs and their axioms (lake build), then the Python gates
#   scripts/reproduce.sh --corpus   also re-elaborate every benchmark snippet against the library
#
# `lake build` checks every proof in MathFin/ and, through MathFin/AxiomAudit.lean and
# MathFin/AxiomAuditGen.lean, pins the axioms of every headline theorem and of every library
# constant a benchmark entry cites: a `sorry` or a non-standard axiom fails the build. The corpus
# pass runs `lake env lean` on each of the benchmark snippets in turn (about a minute each, so
# hours in all; CI shards it across runners in ledger-sweep.yml) and exits non-zero if any fails.
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe cache get
lake build

# Host-side gates (pure Python, no Lean): no sorry in the sources, a declared status for every
# entry, prose that does not outrun the statements, fresh generated audits and ledger hashes.
python3 -c "import pytest" 2>/dev/null \
  || { echo "install the test extras first: pip install -e '.[dev]'" >&2; exit 2; }
python3 -m pytest -q tests
python3 -m tools.verify.ledger status

if [[ "${1:-}" == "--corpus" ]]; then
  LEDGER_EXEC_LOCAL=1 python3 -m tools.verify.ledger verify --all --exec --timeout 600
fi
