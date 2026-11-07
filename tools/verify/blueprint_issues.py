"""The blueprint and the issue tracker stay connected, in both directions.

The blueprint is the map of the whole program (docs/specs/2026-11-05-library-practices-design.md
§7). Its nodes come from two places: the ``@[blueprint]`` tags in ``MathFin/Blueprint.lean``
(exported to ``docs/blueprint_nodes.json`` — results with a Lean proof) and
``docs/blueprint_frontier.toml`` (frontier results: stated, not yet formalized). The link
between a node and its issues is stored once, in the issue: a body line

    Blueprint: thm:dalang-morton-willinger, thm:continuous-ftap

names the node(s) the issue (or pull request) advances. Every other view — the node's
issue list in ``docs/blueprint.md``, the bot comment — is derived from that line, so there
is no second copy to drift.

The invariants, checked by ``check``:

1. every open issue labelled ``type:proof``, ``type:research``, ``open-problem`` or
   ``frontier`` names at least one node (``tracking`` umbrellas are exempt);
2. every name in a ``Blueprint:`` line is a node;
3. every frontier node is named by at least one open issue — a frontier result nobody is
   working towards is not on the program, and one whose issues all closed has either been
   delivered (tag it in ``MathFin/Blueprint.lean`` and delete the frontier entry) or dropped;
4. every proved MathFin node is named by at least one issue or pull request, open or closed:
   its delivery record.

    python3 -m tools.verify.blueprint_issues check            # all issues, via `gh api`
    python3 -m tools.verify.blueprint_issues check --issues issues.json
    python3 -m tools.verify.blueprint_issues comment 412      # bot comment on one issue

Host-side; reads GitHub through the ``gh`` CLI (``GH_TOKEN`` in CI).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

REPO = "formal-applied-math/formal-mathfin"
NODES_JSON = Path("docs/blueprint_nodes.json")
FRONTIER_TOML = Path("docs/blueprint_frontier.toml")

MATH_LABELS = frozenset({"type:proof", "type:research", "open-problem", "frontier"})
EXEMPT_LABELS = frozenset({"tracking"})

# `Blueprint: a, b` at the start of a line; tolerate markdown bold and list bullets.
_LINE = re.compile(r"^[\s>*-]*\**blueprint\**\s*:\**\s*(.+?)\s*$", re.I | re.M)
_NODE_LABEL = re.compile(r"^(?:thm|def|lem|cor|prop):[a-z0-9][a-z0-9-]*$")

MARKER = "<!-- blueprint-sync -->"


@dataclass(frozen=True)
class Node:
    label: str
    title: str
    status: str  # proved | upstream | partial | frontier
    uses: tuple[str, ...] = ()
    statement: str = ""
    area: str = ""
    ground: str = ""  # frontier only: the upstream material a Mathlib-only result builds on
    core: tuple[str, ...] = ()  # frontier only: corpus entries already proving part of it


@dataclass
class Issue:
    number: int
    title: str
    state: str  # open | closed
    labels: frozenset[str]
    body: str
    is_pr: bool = False
    nodes: list[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.nodes = named_nodes(self.body)

    @property
    def must_name_node(self) -> bool:
        return (not self.is_pr and self.state == "open" and bool(self.labels & MATH_LABELS)
                and not self.labels & EXEMPT_LABELS)


def named_nodes(body: str | None) -> list[str]:
    out: list[str] = []
    for m in _LINE.finditer(body or ""):
        for part in re.split(r"[,\s]+", m.group(1).strip("`")):
            part = part.strip("`*[]()")
            # the templates' unfilled placeholder (`thm:<node-label>`) names nothing
            if part and "<" not in part and part not in out:
                out.append(part)
    return out


# ------------------------------------------------------------------ nodes

def _lean_status(n: dict) -> str:
    # same classes as tools/blueprint_render.py
    if not n.get("leanOk", True):
        return "partial"
    if not n.get("module", "").startswith("MathFin"):
        return "upstream"
    return "proved"


def load_frontier(path: Path = FRONTIER_TOML) -> list[Node]:
    data = tomllib.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    return [Node(label=r["label"], title=r["title"], status="frontier",
                 uses=tuple(r.get("uses", ())), statement=r.get("statement", ""),
                 area=r.get("area", ""), ground=r.get("ground", ""),
                 core=tuple(r.get("core", ())))
            for r in data.get("node", [])]


def load_nodes(nodes_json: Path = NODES_JSON, frontier: Path = FRONTIER_TOML) -> dict[str, Node]:
    nodes: dict[str, Node] = {}
    for n in json.loads(nodes_json.read_text(encoding="utf-8")):
        nodes[n["label"]] = Node(label=n["label"], title=n.get("title") or n["label"],
                                 status=_lean_status(n), uses=tuple(n.get("uses", ())))
    for n in load_frontier(frontier):
        if n.label in nodes:
            raise ValueError(f"frontier node {n.label} is also a Lean-tagged node")
        nodes[n.label] = n
    return nodes


def grows_from_wood(label: str, nodes: dict[str, Node]) -> bool:
    """Whether following `uses` from a node reaches a Lean-backed node, or a frontier node that
    declares its upstream `ground`. Frontier-only chains count when they end in the wood."""
    seen: set[str] = set()
    stack = [label]
    while stack:
        n = nodes.get(stack.pop())
        if n is None or n.label in seen:
            continue
        seen.add(n.label)
        if n.status != "frontier" or n.ground:
            return True
        stack.extend(n.uses)
    return False


def frontier_problems(nodes: dict[str, Node],
                      corpus_status: dict[str, str] | None = None) -> list[str]:
    """Static checks of the frontier file (no network): label shape, `uses` resolve, every node
    grows from the proved blueprint, and `core` names corpus entries that prove something."""
    if corpus_status is None and any(n.core for n in nodes.values()):
        from .corpus import iter_entries
        corpus_status = {t["id"]: t.get("metadata", {}).get("formalization_status", "")
                         for _, t in iter_entries()}
    out = []
    for n in nodes.values():
        if n.status != "frontier":
            continue
        if not _NODE_LABEL.match(n.label):
            out.append(f"frontier node `{n.label}`: label must look like `thm:kebab-case`")
        if not n.statement.strip():
            out.append(f"frontier node `{n.label}`: missing `statement`")
        for u in n.uses:
            if u not in nodes:
                out.append(f"frontier node `{n.label}`: uses unknown node `{u}`")
        if not any(grows_from_wood(u, nodes) for u in n.uses) and not n.ground:
            out.append(f"frontier node `{n.label}`: its `uses` reach no proved node; name the "
                       "proved result it builds on, or say in `ground` what Mathlib material it "
                       "draws on")
        for c in n.core:
            status = (corpus_status or {}).get(c)
            if status is None:
                out.append(f"frontier node `{n.label}`: `core` names unknown corpus entry `{c}`")
            elif status not in ("full", "reduced_core"):
                out.append(f"frontier node `{n.label}`: `core` entry `{c}` is {status}, "
                           "not a proof")
    return out


# ------------------------------------------------------------------ issues

def fetch_issues(repo: str = REPO) -> list[Issue]:
    """Every issue and pull request, open and closed (the REST issues endpoint lists both)."""
    raw = subprocess.run(
        ["gh", "api", "--paginate", f"repos/{repo}/issues?state=all&per_page=100",
         "--jq", ".[] | {number, title, state, body, labels: [.labels[].name], "
                 "is_pr: (.pull_request != null)}"],
        check=True, capture_output=True, text=True).stdout
    return [_issue(json.loads(line)) for line in raw.splitlines() if line.strip()]


def _issue(r: dict) -> Issue:
    return Issue(number=r["number"], title=r["title"], state=r["state"],
                 labels=frozenset(r.get("labels", ())), body=r.get("body") or "",
                 is_pr=r.get("is_pr", False))


def load_issues(path: str | Path) -> list[Issue]:
    return [_issue(r) for r in json.loads(Path(path).read_text(encoding="utf-8"))]


# ------------------------------------------------------------------ the check

@dataclass(frozen=True)
class Problem:
    message: str
    issue: int | None = None  # the issue to comment on, when one is at fault


def check(issues: list[Issue], nodes: dict[str, Node],
          corpus_status: dict[str, str] | None = None) -> list[Problem]:
    problems = [Problem(m) for m in frontier_problems(nodes, corpus_status)]
    open_named: dict[str, list[int]] = {}
    any_named: dict[str, list[int]] = {}
    for i in issues:
        for label in i.nodes:
            if label not in nodes:
                problems.append(Problem(
                    f"#{i.number} names `{label}`, which is not a blueprint node", i.number))
                continue
            any_named.setdefault(label, []).append(i.number)
            if i.state == "open" and not i.is_pr:
                open_named.setdefault(label, []).append(i.number)
        if i.must_name_node and not i.nodes:
            problems.append(Problem(
                f"#{i.number} ({i.title}) is open math work but names no blueprint node",
                i.number))
    for n in nodes.values():
        if n.status in ("frontier", "partial") and n.label not in open_named:
            closed = any_named.get(n.label, [])
            why = (f"its issues ({', '.join(f'#{k}' for k in closed)}) are all closed: tag the "
                   "delivered declaration in MathFin/Blueprint.lean and remove the frontier "
                   "entry, or reopen") if closed else "no open issue names it"
            problems.append(Problem(f"{n.status} node `{n.label}`: {why}"))
        if n.status == "proved" and n.label not in any_named:
            problems.append(Problem(
                f"proved node `{n.label}` is named by no issue or pull request "
                "(add `Blueprint: {0}` to the issue that delivered it)".format(n.label)))
    return problems


def issues_url(label: str, repo: str = REPO) -> str:
    """The live list of issues and pull requests naming a node (GitHub search, no snapshot)."""
    from urllib.parse import quote

    return f"https://github.com/{repo}/issues?q=" + quote(f'"{label}" in:body')


def comment_body(issue: Issue, problems: list[Problem]) -> str:
    mine = [p.message for p in problems if p.issue == issue.number]
    if not mine:
        return (f"{MARKER}\nthanks — this issue is connected to the blueprint "
                f"({', '.join(f'`{n}`' for n in issue.nodes)}).")
    lines = [MARKER,
             "this issue needs a link to the blueprint, the program's map "
             "([docs/blueprint.md](https://github.com/formal-applied-math/formal-mathfin/blob/main/docs/blueprint.md)).", ""]
    lines += [f"- {m}" for m in mine]
    lines += ["", "add a line to the issue body naming the node(s) it advances, e.g.",
              "", "```", "Blueprint: thm:continuous-ftap", "```", "",
              "if the result is not on the blueprint yet, add a frontier node to "
              "`docs/blueprint_frontier.toml` in the PR that starts the work."]
    return "\n".join(lines)


def _upsert_comment(repo: str, number: int, body: str, resolved: bool) -> None:
    raw = subprocess.run(
        ["gh", "api", "--paginate", f"repos/{repo}/issues/{number}/comments",
         "--jq", f'.[] | select(.body | startswith("{MARKER}")) | .id'],
        check=True, capture_output=True, text=True).stdout.split()
    if raw:
        subprocess.run(["gh", "api", "-X", "PATCH",
                        f"repos/{repo}/issues/comments/{raw[0]}", "-f", f"body={body}"],
                       check=True, capture_output=True)
    elif not resolved:  # never post a comment only to say all is well
        subprocess.run(["gh", "api", "-X", "POST", f"repos/{repo}/issues/{number}/comments",
                        "-f", f"body={body}"], check=True, capture_output=True)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.blueprint_issues")
    ap.add_argument("cmd", choices=["check", "comment"])
    ap.add_argument("number", nargs="?", type=int, help="issue number (comment)")
    ap.add_argument("--issues", help="issues JSON instead of fetching with gh")
    ap.add_argument("--repo", default=REPO)
    args = ap.parse_args(argv)

    nodes = load_nodes()
    issues = load_issues(args.issues) if args.issues else fetch_issues(args.repo)
    problems = check(issues, nodes)

    if args.cmd == "comment":
        if args.number is None:
            ap.error("comment needs an issue number")
        issue = next((i for i in issues if i.number == args.number), None)
        if issue is None or issue.is_pr:
            return 0
        mine = [p for p in problems if p.issue == issue.number]
        if issue.must_name_node or issue.nodes or mine:
            _upsert_comment(args.repo, issue.number, comment_body(issue, problems),
                            resolved=not mine)
        for p in mine:
            print(p.message)
        return 1 if mine else 0

    for p in problems:
        print(p.message)
    n_frontier = sum(n.status == "frontier" for n in nodes.values())
    print(f"blueprint ↔ issues: {len(nodes)} nodes ({n_frontier} frontier), "
          f"{sum(bool(i.nodes) for i in issues)} issues/PRs naming nodes, "
          f"{len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
