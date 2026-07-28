"""Structural guards for the benchmark verification ledger.

Presence-only: every benchmark entry must have a ledger row, and entry ids
must be globally unique (the ledger is keyed by id). Freshness — whether each
row's input hash still matches the entry's code + transitive MathFin imports +
toolchain pins — is deliberately NOT asserted here: a library edit legitimately
stales entries until re-verification, and the test suite must stay green in
that window. Freshness is checked by

    python3 -m tools.verify.ledger status   # exit 1 when stale/missing

run after any MathFin/ or benchmark edit (re-verify with `verify --stale`).
"""

import json
from collections import Counter
from pathlib import Path


def _benchmark_ids():
    for path in Path("benchmarks").glob("*.json"):
        data = json.loads(path.read_text())
        theorems = data.get("theorems", data) if isinstance(data, dict) else data
        for theorem in theorems:
            yield path.name, theorem["id"]


def test_benchmark_ids_are_globally_unique() -> None:
    counts = Counter(tid for _, tid in _benchmark_ids())
    dupes = {tid: n for tid, n in counts.items() if n > 1}
    assert not dupes, dupes


def test_every_benchmark_entry_has_a_ledger_row() -> None:
    ledger = json.loads(Path("verification_ledger.json").read_text())
    rows = set(ledger["entries"])
    missing = [(fname, tid) for fname, tid in _benchmark_ids() if tid not in rows]
    assert not missing, missing


def test_shard_spec_parses_one_based() -> None:
    from tools.verify.ledger import _parse_shard

    assert _parse_shard("1/12") == (0, 12)
    assert _parse_shard("12/12") == (11, 12)


def test_shards_partition_the_corpus_exactly_once() -> None:
    """The sweep is only sound if the shards cover every entry and none twice.

    A sharded sweep is the only way back to a fresh ledger after a pin bump, and
    a silent gap in the partition would leave entries stale while every shard
    reported success — the ledger would then claim less than it should, or (if
    a gap coincided with a `--fragment` merge) more.
    """
    from tools.verify.ledger import _parse_shard

    entries = list(range(len(list(_benchmark_ids()))))
    count = 12
    covered: list[int] = []
    for shard in range(1, count + 1):
        index, n = _parse_shard(f"{shard}/{count}")
        assert n == count
        covered += [e for i, e in enumerate(entries) if i % n == index]
    assert sorted(covered) == entries
