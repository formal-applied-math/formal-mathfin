# 06 — The target plane: point the foundry at a second repo, and prove it

**Repo:** `mathfin-foundry` (plus a seeded issue in the target library) ·
**Trigger:** runbook 02 landed AND runbook 03's library builds green ·
**Est. scope:** one to two sessions, most of it CI
**Design source:** `docs/program-architecture.md` §1 (L3), §3.

## Why this exists

Runbook 02 makes `probe/` domain-free. That is necessary and not sufficient. The
pipeline does not read `probe/` to decide which repo it operates on — it reads
shell scripts, three workflows, a GHCR image with the target library's oleans
baked in, and a GitHub issue queue. All four are still welded to `formal-mathfin`
after 02 is complete, so 02 alone leaves a foundry that is *portable in principle
and immovable in practice*.

The acceptance criterion below is deliberately a live artifact rather than a test
suite: a ready-for-review PR opened by the pipeline on the second library. Nothing
short of that distinguishes "the strings are in a pack" from "the foundry runs
against two domains".

## Where the target plane lives

**Already parameterized — verify, do not rebuild.** `MAIN_REPO` and
`MAIN_REPO_SLUG` are environment variables with mathfin defaults across
`scripts/{open-pr,build-index,slot-switch,leanstral-vibe,decompose-tick}.sh`.
`probe/`'s `main_repo` is a function parameter. This is the part the original
coupling audit got right.

**Not parameterized:**

| Site | What is welded |
|---|---|
| `scripts/open-pr.sh:142` | splice sanity check greps for `end MathFin` |
| `scripts/open-pr.sh:162,170,206` | `import MathFin` corpus assumption; `lake build MathFin`; the `git add` list (`MathFin.lean`, `MathFin/AxiomAuditGen.lean`) |
| `scripts/build-index.sh:22,51-62` | `MATHFIN_IMAGE` default; `--imports MathFin`; filter to `MathFin.*` records |
| `scripts/vibe-setup.sh:42`, `slot-switch.sh:39`, `leanstral-vibe.sh:39-40` | container name `mathfin-lean-lsp` |
| `docker/docker-compose.lean-lsp.yml:13-14` | image + container name |
| `.github/workflows/pipeline.yml:67-70,114,129,196` | `repository:`, two cache keys hashing `main/MathFin/**`, `MAIN_REPO_SLUG` |
| `.github/workflows/batch-verify.yml:48-51,56,78,81` | `repository:`, image pull, `lake build MathFin` |
| `.github/workflows/build-index.yml:78-81` | `repository:` |
| `probe/autoformalize.py:57` | `_lean_lsp_mcp_config(container="mathfin-lean-lsp")` — a default runbook 02 should already have moved into `target.toml` |
| the target repo itself | `status:ready` + `type:proof` + `area:*` labels, and a live `docs/patterns.md` that `house_context.read_patterns` splices into the drafter prompt |

## Steps

1. **Write `domains/econometrics/`** against the real namespace, section list,
   pillars and house preamble that runbook 03 produced. This is the first genuine
   test of 02's pack contract; expect it to find one or two fields 02 guessed.
   Fix the contract here rather than special-casing.
2. **Lift the scripts.** Every welded site above reads from the pack (exported to
   the shell as env by a small `probe/domain_pack.py --export-env <name>` shim, so
   the shell scripts stay shell). `open-pr.sh`'s gate list becomes pack-driven —
   it must run the target's own ledger, axiom-audit generator and
   `formalization.yaml`, all of which runbook 03 stood up.
3. **Lift the workflows.** `repository:` and the cache keys come from a workflow
   input defaulting to `mathfin`; the domain becomes a `workflow_dispatch` input
   and a matrix axis. Cache keys hash `main/<LibRoot>/**`, not `main/MathFin/**`.
4. **Build an `econometrics-verify` image.** Same Dockerfile shape as the flagship's
   `docker/Dockerfile.verify`, pinned to the econometrics manifest, published from
   **CI only** — never locally. The memory doctrine forbids a local Mathlib image
   build outright, and that rule does not relax because the library is small.
5. **Seed the target's issue contract.** Create the `status:ready`, `type:proof`,
   `difficulty:*` and `area:*` labels in `formal-econometrics`, and file one real
   target (an identification result from `applied-areas.md` §3.1 — omitted-variable
   bias or Frisch–Waugh–Lovell are the natural first two). Its `docs/patterns.md`
   starts thin; that is honest, and the drafter prompt degrades gracefully rather
   than lying.
6. **One live tick.** `workflow_dispatch` the pipeline with `domain = econometrics`
   and let it run end to end: intent → agentic formalization → depth/triviality/
   kernel gates → Leanstral → refinery → PR.
7. **Re-run one mathfin tick.** The retarget is not done until *both* domains tick.
   A green econometrics run beside a broken mathfin run is a regression wearing a
   feature's clothes.

## Acceptance criteria

- [ ] A ready-for-review PR on `formal-econometrics`, opened by the pipeline, with
      the same gate evidence a mathfin PR carries (kernel-checked, axiom-pinned,
      ledger row, declared `formalization_status`).
- [ ] A mathfin tick after the change produces its usual PR shape, unregressed.
- [ ] No `MathFin`/`mathfin` literal outside `domains/mathfin/` in `probe/`,
      `scripts/` or `.github/workflows/` — extend `test_no_domain_leakage` to cover
      the latter two.
- [ ] `docs/overview.md` documents the target plane alongside the pack contract.

## Kill criteria

- If the econometrics corpus is too small for the depth gate to have anything to
  consume (the gate requires the candidate to USE a constant defined in the issue's
  pointer modules), do NOT weaken the gate. Report it, and seed a target whose
  pointers are modules that exist. A gate relaxed to make a demo pass is the exact
  failure this repo's whole apparatus is built against.
- If the second GHCR image pushes the Actions quota past what the cadence can
  afford, run econometrics ticks on `workflow_dispatch` only and say so in
  `pipeline.toml` — an honest manual cadence beats a cron that silently starves
  the flagship.
