# LeanHammer pilot goals

15 goals lifted verbatim from real MathFin proof sites, each annotated with the
tactic we actually wrote there. They are the fixed benchmark the hammer question
is decided against — see `docs/hammer-pilot-2026-06-06.md` for the 2026-06-06
baseline, why its verdict is expired rather than settled, and which of these
goals actually decide adoption.

- **PilotA** — algebra / inequalities. Pinned to `{disableGrind := true}` so it
  exercises the pure Aesop+Zipperposition+Duper path. The CI job also generates
  a default-config variant, because the kernel rejection the pilot hit came from
  hammer's *grind* driver and the committed file does not exercise it.
- **PilotB** — measure-theory premise lookups. **The discriminating goals.** The
  published LeanHammer numbers (73.5% Mathlib → 79.4% miniCTX-v2) come with
  flagged gaps in dependent types and no coverage of measure-theory-heavy code,
  which is exactly our slice.
- **PilotC** — stretch goals. Skipped in 2026-06-06 as decision-irrelevant after
  A and B; kept so a re-run can go further if A and B clear.

These files are **not** part of the library build. Nothing under `MathFin/`
imports them, `test_router.test_tooling_packages_not_imported_by_library`
enforces that, and the Hammer cluster is in `ledger.PIN_EXCLUDED_PACKAGES` so
the dependency never restales the corpus.

Run them with `.github/workflows/hammer-retest.yml` (workflow_dispatch). Do not
run them on the 10 GB dev box: the memory doctrine puts full-environment batch
work on GitHub runners.
