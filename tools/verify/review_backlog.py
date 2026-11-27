"""The values reviews' backlogs, each item with its outcome.

Every entry of ``docs/values-review.md`` ends in a ranked backlog. ``docs/status.md`` says the
items are filed as issues and the lists are a record, not a second tracker. This module holds
that rule mechanically. Every numbered item under a backlog heading ends with one outcome tag:

* ``[#123]`` (or ``[#123, #456]``): the issue that tracks it;
* ``[done: <where>]``: delivered, naming the declaration, file or pull request;
* ``[retired: <why>]``: made moot, superseded or declined, with the reason.

``tests/test_values.py::test_every_review_backlog_item_has_an_outcome`` fails on an item
without a tag. A review records its backlog with the issues already filed, so an untagged item
cannot pile up. On 2026-11-25 the first audit found 102 of 326 items in no issue and not done.

    python3 -m tools.verify.review_backlog           # counts per outcome
    python3 -m tools.verify.review_backlog --open    # the items without a tag
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path

REVIEW_PATH = Path("docs/values-review.md")

ENTRY_RE = re.compile(r"^## \d{4}-\d{2}-\d{2}", re.M)
BACKLOG_HEADING_RE = re.compile(r"^### (?:Ranked backlog|Backlog(?! executed)|Ranked follow-up)", re.M)
ITEM_START_RE = re.compile(r"^\s*\d+\.\s", re.M)
OUTCOME_RE = re.compile(
    r"\[(?:#\d+(?:, #\d+)*|done: [^\]\n]+|retired: [^\]\n]+)\]\s*$"
)


@dataclass(frozen=True)
class Item:
    entry: str
    line: int
    text: str

    @property
    def outcome(self) -> str | None:
        m = OUTCOME_RE.search(self.text)
        if not m:
            return None
        tag = m.group(0).strip()[1:-1]
        return "issue" if tag.startswith("#") else tag.split(":", 1)[0]


def items(text: str) -> list[Item]:
    """The numbered items under every entry's backlog heading, in file order."""
    lines = text.split("\n")
    out: list[Item] = []
    starts = [m.start() for m in ENTRY_RE.finditer(text)] + [len(text)]
    for a, b in zip(starts, starts[1:]):
        body = text[a:b]
        entry = body.split("\n", 1)[0][3:]
        for h in BACKLOG_HEADING_RE.finditer(body):
            sec_start = body.index("\n", h.start()) + 1
            nxt = body.find("\n### ", sec_start - 1)
            section = body[sec_start: nxt if nxt != -1 else len(body)]
            marks = [m.start() for m in ITEM_START_RE.finditer(section)]
            for i, s in enumerate(marks):
                e = marks[i + 1] if i + 1 < len(marks) else len(section)
                chunk = section[s:e].rstrip()
                line = text.count("\n", 0, a + sec_start + s) + 1
                while not lines[line - 1].strip():
                    line += 1
                out.append(Item(entry, line, chunk.strip()))
    return out


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--open", action="store_true", help="list the items without an outcome tag")
    args = p.parse_args()
    its = items(REVIEW_PATH.read_text())
    if args.open:
        for it in its:
            if it.outcome is None:
                print(f"{REVIEW_PATH}:{it.line}: {it.text.splitlines()[0][:100]}")
        return
    counts: dict[str, int] = {}
    for it in its:
        k = it.outcome or "untagged"
        counts[k] = counts.get(k, 0) + 1
    print(f"{len(its)} items: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
