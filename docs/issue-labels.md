# Issue label taxonomy

This taxonomy gives maintainers and contributors a shared vocabulary for
triaging work. Labels should answer four questions:

- **Where does the result sit?** `area:<cell>` and `family:<family>`, derived (below).
- **What kind of work is it?** Use one `type:*` label.
- **How hard is it for a contributor?** Use one `difficulty:*` label.
- **What is the current state?** Use one `status:*` label.

Use `good first issue` and `help wanted` as public entry-point labels on top of
the taxonomy when the task is ready for outside contributors.

Use `open-problem` for a sourced mathematical research-problem record. Retain
it when the problem is solved so closed issues remain discoverable. An unresolved
catalogue question uses `type:research` and `status:research`; a concrete Lean
implementation gets a separate linked `type:proof` issue. Mathematical status
and formalization status are recorded independently in the
[research catalogue](research-problems/README.md).

Colors are consistent per dimension so an issue's labels read at a glance:
`area:*` take the hue of their part (roots, trunk, valuation, choice, risk), `family:*` one
hue, `type:*` another, while `difficulty:*` and `status:*`
use a semantic scale (green → amber → red).

## Area and family labels

The library has one organization, stated once in [`docs/taxonomy.toml`](taxonomy.toml) and
explained in [`docs/organization.md`](organization.md): a **cell** says where a result sits (a
root, the trunk of positions and markets, or a branch of the valuation, choice or risk limb), a
**family** says which kind of randomness it is about (trees, diffusions, volatility, jumps, term
structures, default, insurance, mechanisms, model-free).

The issue labels are that taxonomy, one `area:<cell>` per cell (`area:valuation/term`,
`area:risk/measures`, `area:probability/brownian`, ...) and one `family:<family>` per family.
**Nobody sets them by hand.** An issue's `Blueprint:` line names its nodes; a Lean node's cell
and family are its module's, a frontier node's are its `area` and `family` in
`docs/blueprint_frontier.toml`. `blueprint-sync` writes the derived labels on every issue event
and nightly (`python3 -m tools.verify.blueprint_issues labels --apply`), and the check fails on
an open issue whose labels disagree with its nodes. To move an issue, move its node.

Three labels are not mathematics and stay hand-set:

| Label | Use for |
|---|---|
| `area:tooling` | Python verification tools, scripts, ledger logic, and generated audits under `tools/` and `scripts/`. |
| `area:docs` | Markdown docs, README content, onboarding, coverage/blueprint prose, and cross-links. |
| `area:ci` | GitHub Actions, Docker images, build gates, and release automation. |

## Type labels

| Label | Use for |
|---|---|
| `type:bug` | Something expected to work is broken. |
| `type:proof` | A new Lean theorem, proof repair, or theorem generalization. |
| `type:docs` | Documentation-only work. |
| `type:refactor` | Structure or naming changes that should preserve behavior and theorem statements. |
| `type:tooling` | Changes to verification scripts, exports, or developer tooling. |
| `type:research` | Open investigation where the implementation path is not yet clear. |
| `type:maintenance` | Routine cleanup, dependency updates, or housekeeping. |

## Difficulty labels

| Label | Use for |
|---|---|
| `difficulty:good-first` | Small, well-scoped task with enough context in the issue body. Add `good first issue` too. |
| `difficulty:small` | Straightforward change for someone familiar with the repo. |
| `difficulty:medium` | Requires repo context, Lean fluency, or careful validation. |
| `difficulty:hard` | Requires deep domain knowledge, theorem design, or upstream coordination. |

## Status labels

| Label | Use for | Written by |
|---|---|---|
| `status:needs-triage` | New issue that has not been classified yet. | human |
| `status:needs-info` | Waiting on clarification before work should start. | human |
| `status:research` | Sourced mathematical question under research, outside the `status:ready` implementation queue. | human |
| `status:ready` | Scoped enough for a contributor to pick up. | human, or the pipeline on release |
| `status:in-progress` | Someone is actively working on it. | human, or the pipeline on seed |
| `status:blocked-upstream` | Blocked on Mathlib, BrownianMotion, or another external project. | human |
| `status:blocked-design` | Blocked on a modeling, theorem-shape, or architecture decision. | human |
| `status:review` | PR exists and maintainer review is the next step. | human, or the pipeline on PR |

### Three of these are machine-written

The autoformalization pipeline in `formal-foundry` used to only READ this backlog.
It kept its own private record of which issues it had already worked, that record
drifted from reality, and the pipeline re-drafted work it had already queued. The
fix was to stop keeping a private record: **the issue is now the state machine, and
everything the pipeline stores locally is a cache of it.**

So the pipeline moves an issue between three of the eight statuses:

| transition | when |
|---|---|
| `status:ready` → `status:in-progress` | a gated Lean stub for the issue is staged in the pipeline's queue |
| `status:in-progress` → `status:review` | a PR closing the issue has been opened |
| back to `status:ready` | the PR was closed unmerged, or the staged stub was retired |
| → closed | GitHub closes it when the PR merges |

Three consequences worth knowing when you triage:

- **A label may move without a human touching it.** If an issue you filed is
  suddenly `status:in-progress` with nobody assigned, a machine drafted a statement
  for it. Nothing has been merged — see below.
- **The pre-existing manual statuses are yours alone, and the pipeline will not
  overrule them.** `status:blocked-design` in particular looks identical to "ready" from the
  machine's side (no PR, no stub), so it is explicitly excluded: parking an issue
  there reliably keeps it out of the pipeline. An issue with *no* status label is
  likewise never promoted — the pipeline repairs its own writes, it does not decide
  what is worth proving.
- **`status:review` still means a human reviews it.** Scout-not-author is unchanged:
  a machine may draft a statement and find a proof, and a person refines and merges
  it. No label transition here is an approval of anything.

Label writes are best-effort by design — a failed write must never fail a pipeline
run — so a stale status is possible. The pipeline re-derives all three from the
observable facts (open PRs, staged stubs) at the start of each run, so a stale one
corrects itself rather than needing a manual fix.

## Triage examples

| Issue | Suggested labels |
|---|---|
| Add a glossary entry for no-arbitrage terms | `area:docs`, `type:docs`, `difficulty:good-first`, `status:ready`, `good first issue` |
| Repair a stale coverage row after a theorem rename | `area:docs`, `type:docs`, `difficulty:small`, `status:ready` |
| Prove a new Black-Scholes Greek | `type:proof`, `difficulty:medium`, `status:ready` |
| Generalize an Itô-formula hypothesis | `type:proof`, `difficulty:hard`, `status:ready` |
| Draft an upstream BrownianMotion issue | `type:research`, `difficulty:hard`, `status:blocked-upstream` |
| Catalogue a sourced unresolved mathematical question | `open-problem`, `type:research`, `difficulty:hard`, `status:research` |
| Fix a failing build workflow | `area:ci`, `type:bug`, `difficulty:medium`, `status:ready` |

The mathematical rows carry no `area:` label by hand: their `Blueprint:` line gives it.

## Bootstrap commands

Maintainers can create the taxonomy with `gh label create`:

```bash
# area:<cell> and family:<family> — created from docs/taxonomy.toml, then derived per issue
python3 -m tools.verify.blueprint_issues labels --apply

# the three hand-set area labels
gh label create "area:tooling"      --color "ededed" --description "Verification tools, scripts, ledger logic, and generated audits"
gh label create "area:docs"         --color "ededed" --description "Markdown docs, onboarding, coverage/blueprint prose, and cross-links"
gh label create "area:ci"           --color "ededed" --description "GitHub Actions, Docker images, build gates, and release automation"

# type:* — one shared purple
gh label create "type:bug"         --color "5319e7" --description "Something expected to work is broken"
gh label create "type:proof"       --color "5319e7" --description "Lean theorem, proof repair, or theorem generalization"
gh label create "type:docs"        --color "5319e7" --description "Documentation-only work"
gh label create "type:refactor"    --color "5319e7" --description "Structure or naming change that should preserve behavior"
gh label create "type:tooling"     --color "5319e7" --description "Verification scripts, exports, or developer tooling"
gh label create "type:research"    --color "5319e7" --description "Open investigation where the path is not yet clear"
gh label create "type:maintenance" --color "5319e7" --description "Routine cleanup, dependency updates, or housekeeping"

# difficulty:* — green → red scale
gh label create "difficulty:good-first" --color "0e8a16" --description "Small, well-scoped task for new contributors"
gh label create "difficulty:small"      --color "c2e0c6" --description "Straightforward change for someone familiar with the repo"
gh label create "difficulty:medium"     --color "fbca04" --description "Requires repo context, Lean fluency, or careful validation"
gh label create "difficulty:hard"       --color "d93f0b" --description "Requires deep domain knowledge or upstream coordination"

# status:* — grey (new) → green (go) → amber (active) → red (blocked) → blue (review)
gh label create "status:needs-triage"     --color "ededed" --description "New issue that has not been classified yet"
gh label create "status:needs-info"       --color "fef2c0" --description "Waiting on clarification before work should start"
gh label create "status:ready"            --color "0e8a16" --description "Scoped enough for a contributor to pick up"
gh label create "status:in-progress"      --color "fbca04" --description "Someone is actively working on it"
gh label create "status:blocked-upstream" --color "b60205" --description "Blocked on Mathlib, BrownianMotion, or another external project"
gh label create "status:blocked-design"   --color "e99695" --description "Blocked on a modeling, theorem-shape, or architecture decision"
gh label create "status:review"           --color "c5def5" --description "PR exists and maintainer review is the next step"
```
