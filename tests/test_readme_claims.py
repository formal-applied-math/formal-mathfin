"""The README's corpus counts are the corpus's.

The front page states how many entries the corpus has and how they split by status. Those numbers
drifted once (870 stated, 904 recorded, 2026-11-20) because nothing compared them; this does.
"""
from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORDS = {w: i for i, w in enumerate(
    "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen "
    "fifteen sixteen seventeen eighteen nineteen twenty".split())}


def _statuses() -> Counter:
    counts: Counter = Counter()
    for path in sorted((ROOT / "benchmarks").glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        for t in data["theorems"] if isinstance(data, dict) else data:
            counts[t["metadata"]["formalization_status"]] += 1
    return counts


def _spelled(text: str) -> int:
    parts = text.lower().split("-")
    return sum(20 if p == "twenty" else WORDS[p] for p in parts) if parts[0] == "twenty" \
        else WORDS[text.lower()]


def test_readme_counts_match_the_corpus() -> None:
    readme = re.sub(r"\s+", " ", (ROOT / "README.md").read_text(encoding="utf-8"))
    c = _statuses()
    m = re.search(r"records (\d+) results.*? Of these, (\d+) are proved in full, (\d+) restate a "
                  r"lemma .*?, and (\d+) are \[?reduced cores", readme)
    assert m, "README no longer states the corpus split in the expected sentence; update this test"
    stated = tuple(int(g) for g in m.groups())
    actual = (sum(c.values()), c["full"], c["library_wrapper"], c["reduced_core"])
    assert stated == actual, f"README states {stated}, the corpus records {actual}"
    words = re.search(r"\*\*Reduced cores\.\*\* ([A-Za-z-]+) of the results", readme)
    assert words and _spelled(words.group(1)) == c["reduced_core"], (
        "README Limitations gives the wrong number of reduced cores")
