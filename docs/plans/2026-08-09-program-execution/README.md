# Program execution runbooks

Executable instruction files for the three-repo program designed in
[`docs/program-architecture.md`](../../program-architecture.md) (topology, tier
ladder, timing rules) and scoped in [`docs/applied-areas.md`](../../applied-areas.md)
(the territory audit). Each runbook is a **self-contained prompt for one local
Claude Code session**: it names the repo to open, carries its own context, and ends
in machine-checkable acceptance criteria — you should not need to re-explain the
program to the session.

## How to run one

```bash
cd <repo named in the runbook's header>
claude "Read docs/plans/2026-08-09-program-execution/<NN>-<name>.md from the
formal-mathfin repo and execute it. Follow CLAUDE.md. Stop at any kill criterion
and report instead of pushing through."
```

(For runbooks targeting other repos, pass the file by absolute path — they all
live here, in the flagship's docs tree.)

## The runbooks, in order

| # | File | Repo | Trigger | Depends on |
|---|---|---|---|---|
| 01 | [`01-architecture-metrics.md`](01-architecture-metrics.md) | `formal-mathfin` | **now** | — |
| 02 | [`02-foundry-domain-packs.md`](02-foundry-domain-packs.md) | `mathfin-foundry` | **now** | — |
| 03 | [`03-econometrics-phase0.md`](03-econometrics-phase0.md) | `formal-econometrics` (new) | **now** (after 02 is nice-to-have, not required) | — |
| 04 | [`04-apparatus-genericize.md`](04-apparatus-genericize.md) | `formal-mathfin` | **econometrics reaches ~20 entries** | 03 |
| 05 | [`05-formathlib-aging.md`](05-formathlib-aging.md) | whichever repo births the block | **first field-neutral Lean block** (likely the fixed-point tower) | 03 |

01 and 02 are independent and can run in any order (but NOT simultaneously if both
need the Lean slot — see the memory rule below). 03 opens the second library. 04
and 05 are **trigger-based: do not run them early** — running 04 before its
trigger violates the program's central timing rule (genericize exactly once,
against observed divergence, not speculation).

## Rules that bind every session

- **Memory doctrine** (`CLAUDE.md`): ONE Lean-loaded process on the box, ever.
  Before any `lake build` / daemon start in one repo, confirm no other repo's
  daemon or build is running (`docker ps`; `docker compose -f
  docker/docker-compose.yml down lean-repl`). This applies ACROSS repos, not just
  within one.
- **Gates before push** (formal-mathfin only, until 03 clones them): ledger fresh,
  pytest green, `axiom_audit_gen` byte-fresh after any benchmark edit.
- **Honesty register**: every claim in a report or commit message must be
  kernel-checked or labelled as not. No "should work". If an acceptance criterion
  was not met, the runbook FAILED — say so; a partial result honestly reported is
  a valid outcome, a rounded-up one is not.
- **Kill criteria are real.** They exist because the design says some bets should
  be re-examined cheaply instead of pushed through. Hitting one is the runbook
  *working*, not failing.
