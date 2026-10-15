"""Attribution gate — contributors stay credited, in their headers and in the README.

A `MathFin/` file first committed by a contributor must name that contributor
on both its `Copyright` line and its `Authors:` line. The copyright stays with
the author (no CLA assigns it here), and Apache-2.0 §4(c) requires keeping the
attribution notices of a contribution, so the header is not ours to reassign.
And everyone with a commit on main is listed under `## Contributors` in
`README.md`.

Why it is a gate and not a review item: #244 landed eight modules whose
headers named the maintainer — the contributor had copied the house header —
and the review that merged them saw it and let it through. #247, from the
contributor, put the attribution right. The check reads authorship from git,
so it cannot be satisfied by the header alone.

How it decides:
- Who added a file is the author of the commit that created the current path
  (renames followed), with names canonicalized by `.mailmap` (`%aN`). A
  contributor whose git name differs from the name in their headers gets a
  `.mailmap` line, not an exemption.
- Files the maintainer or a bot added are not checked: a port credits whoever
  wrote the original (the SVI files credit Robert Martin), and the
  maintainer's own modules are not at risk. Commits from the maintainer's
  earlier agent sessions, authored `Claude <noreply@anthropic.com>`, map to
  the maintainer through `.mailmap`.
- `PENDING` exempts files whose header the *contributor* wrote with another
  copyright holder, until they say which they intend. Each entry names the
  open question; `test_pending_exemptions_are_still_needed` fails once the
  header is fixed, so the entry cannot outlive its reason.

Needs full history: CI checks out with `fetch-depth: 0`. A shallow clone fails
under GitHub Actions (the gate must not silently disappear) and skips
elsewhere; so does a tree with no git, such as the `verify` container.
"""

import os
import re
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent

#: Canonical (`.mailmap`) names whose commits need no credit line; bots
#: (`…[bot]`) are exempt as well.
MAINTAINERS = frozenset({"Raphael Coelho"})

#: Files whose contributor-written header names another copyright holder,
#: pending the contributor's answer. Path → the open question.
PENDING: dict[str, str] = {
    "MathFin/Foundations/PricePathDrift.lean": (
        "Alfredo Garcia wrote `Copyright (c) 2026 Raphael Coelho` with "
        "`Authors: Alfredo Garcia`; asking which copyright holder they intend"
    ),
    "MathFin/Performance/DownsideMetrics.lean": (
        "Aleksey Salkutsan wrote `Copyright (c) 2026 Raphael Coelho` with "
        "`Authors: Aleksey Salkutsan`; asking which copyright holder they intend"
    ),
}

COPYRIGHT_RE = re.compile(
    r"^Copyright \(c\) \d{4}(?:\s*[-–]\s*\d{4})? (?P<who>.+?)\. All rights reserved\.\s*$",
    re.MULTILINE,
)
AUTHORS_RE = re.compile(r"^Authors?:\s*(?P<who>.+?)\s*$", re.MULTILINE)
CONTRIBUTORS_RE = re.compile(
    r"^## Contributors\n(?P<body>.*?)(?=^## |\Z)", re.MULTILINE | re.DOTALL
)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=REPO_ROOT, capture_output=True, text=True, check=True
    ).stdout


def _require_history() -> None:
    try:
        shallow = _git("rev-parse", "--is-shallow-repository").strip() == "true"
    except (OSError, subprocess.CalledProcessError):
        pytest.skip("no git repository (e.g. the verify container)")
    if shallow:
        if os.environ.get("GITHUB_ACTIONS") == "true":
            pytest.fail("shallow checkout: the attribution gate needs `fetch-depth: 0`")
        pytest.skip("shallow clone: attribution needs full history (`git fetch --unshallow`)")


def _is_maintainer(name: str) -> bool:
    return name in MAINTAINERS or name.endswith("[bot]")


def first_authors(ref: str = "HEAD") -> dict[str, str]:
    """Path → canonical name of the author who created the file now at that path.

    Walks history oldest-first; an add sets the author (a re-add after a
    deletion overrides), a rename carries the author to the new path.
    """
    log = _git(
        "log", ref, "--topo-order", "--reverse", "-M", "--diff-filter=AR",
        "--name-status", "--format=@@%aN",
    )
    author: dict[str, str] = {}
    current = ""
    for line in log.splitlines():
        if line.startswith("@@"):
            current = line[2:]
            continue
        fields = line.split("\t")
        if fields[0].startswith("R") and len(fields) == 3:
            author[fields[2]] = author.get(fields[1], current)
        elif fields[0] == "A" and len(fields) == 2:
            author[fields[1]] = current
    return author


def _names(field: str) -> set[str]:
    return {name.strip() for name in re.split(r",|\band\b", field) if name.strip()}


def header_holders(source: str) -> tuple[set[str], set[str]]:
    """The names on the `Copyright` line and on the `Authors:` line."""
    head = source[:1500]
    copyright_ = COPYRIGHT_RE.search(head)
    authors = AUTHORS_RE.search(head)
    return (
        _names(copyright_["who"]) if copyright_ else set(),
        _names(authors["who"]) if authors else set(),
    )


def misattributed(ref: str = "HEAD") -> dict[str, str]:
    """Contributor-added `MathFin/` files whose header does not name the contributor."""
    added_by = first_authors(ref)
    files = _git("ls-tree", "-r", "--name-only", ref, "--", "MathFin").split()
    problems = {}
    for path in files:
        who = added_by.get(path)
        if not path.endswith(".lean") or who is None or _is_maintainer(who):
            continue
        holders, authors = header_holders(_git("show", f"{ref}:{path}"))
        missing = [line for line, names in (("Copyright", holders), ("Authors", authors))
                   if who not in names]
        if missing:
            problems[path] = (
                f"added by {who}, who is missing from: {', '.join(missing)} "
                f"(Copyright: {sorted(holders) or 'none'}; Authors: {sorted(authors) or 'none'})"
            )
    return problems


def contributors(ref: str = "HEAD") -> set[str]:
    """Canonical names of everyone with a commit on `ref`, maintainers and bots aside."""
    return {name for name in _git("log", ref, "--format=%aN").splitlines()
            if not _is_maintainer(name)}


def test_contributed_files_credit_their_author() -> None:
    _require_history()
    problems = {p: why for p, why in misattributed().items() if p not in PENDING}
    assert not problems, (
        "contributed modules must name their author on both the Copyright and the "
        "Authors line (fix the header; if the author's git name differs from the name "
        "they use, add a `.mailmap` line):\n"
        + "\n".join(f"  {path}: {why}" for path, why in sorted(problems.items()))
    )


def test_pending_exemptions_are_still_needed() -> None:
    _require_history()
    problems = misattributed()
    stale = sorted(path for path in PENDING if path not in problems)
    assert not stale, (
        "these PENDING exemptions no longer apply (header fixed or file gone); "
        f"remove them: {stale}"
    )


def test_readme_credits_every_contributor() -> None:
    _require_history()
    section = CONTRIBUTORS_RE.search((REPO_ROOT / "README.md").read_text(encoding="utf-8"))
    assert section, "README.md has no `## Contributors` section"
    missing = sorted(name for name in contributors() if name not in section["body"])
    assert not missing, (
        "commit authors missing from `## Contributors` in README.md (add them, linked to "
        f"their GitHub profile; a different git name needs a `.mailmap` line): {missing}"
    )
