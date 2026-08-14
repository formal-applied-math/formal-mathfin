# 04 — Genericize the apparatus, exactly once

**Repo:** `formal-mathfin` (then a switch-over commit in each consumer) ·
**Trigger:** `formal-econometrics` reaches **~20 entries** — NOT before ·
**Design source:** `docs/program-architecture.md` §1 (L1), §4 (timing rule).

## Do not run early

The entire value of this runbook is that it is executed against **observed**
divergence, not predicted divergence. Its primary input is
`formal-econometrics/docs/apparatus-divergence.md` (produced by runbook 03 and
grown since). If that file is thin or the corpus is far below ~20 entries, stop
and tell the user it is too early — that is the correct outcome.

## Goal

Turn `tools/` into a corpus-parameterized package that BOTH libraries and the
foundry consume from **this repo** as a pip git-dependency pinned to a tag —
ending the copy from phase 0. The apparatus stays here (not the foundry) because
it must remain public: `build.yml` runs the gates in public CI and contributors
run them locally. (The foundry was private when this runbook was written; it went
public on 2026-08-14, which does not change where the apparatus belongs.)

## Steps

1. **Read the divergence log.** Classify every touched line: (a) config that
   should come from the TOML (library name, benchmarks dir, domain enum, section
   list); (b) genuine parameter the config schema lacks; (c) mathfin-ism that was
   special-cased in code. Category (c) items are bugs — fix them as such.
2. **Parameterize in place.** `tools/verify` already reads `mathfin.toml`;
   extend `config.py`'s dataclasses to carry everything in categories (a)/(b):
   library namespace, corpus paths, domain list, audit-file paths, ledger path.
   The Domain enum is the known hard case — it must become config-driven data,
   with `Router` validating against the configured list (mathfin's routing table
   moves into `mathfin.toml`).
3. **Package boundary.** Make `tools/` installable from git
   (`pip install "mathfin @ git+https://github.com/formal-applied-math/formal-mathfin@apparatus-v1"`
   — the existing `pyproject.toml` already names the package `mathfin`; keep the
   name for now, renaming is cosmetic churn). Entry points unchanged
   (`python3 -m tools.verify.ledger` etc. must keep working IN this repo).
4. **Prove no regression here first**: full mathfin gate suite + ledger status
   green with the parameterized code and `mathfin.toml` carrying the new keys.
5. **Tag `apparatus-v1`.**
6. **Cut over the consumers** (separate commits, their repos):
   - `formal-econometrics`: delete the copied `tools/`, add the pinned pip dep
     (requirements + CI install step), point its `econometrics.toml` at the new
     schema, all gates green.
   - `formal-foundry`: same for whatever `tools.verify` surface it imports
     (ledger models, `af_parse` interop — grep first).
7. **Discipline notes into both CLAUDE.md files**: apparatus upgrades are
   deliberate tag bumps; any `tools/` change that special-cases a corpus instead
   of reading config is a bug; changes motivated by econometrics still land here.

## Acceptance criteria

- [ ] One `tools/` implementation; zero copies anywhere.
- [ ] Both libraries' full gate suites green against `apparatus-v1`.
- [ ] mathfin's own CI unchanged in behavior (same gates, same commands).
- [ ] The divergence log is closed out: every line classified and resolved.

## Kill criteria

- If cut-over reveals a genuinely two-shaped requirement (the same function
  needing incompatible behavior per corpus that config cannot express cleanly),
  do NOT force an abstraction: leave that one function duplicated with a
  documented reason, and list it in a "known duplication" section. A small
  honest duplication beats a wrong seam in shared infrastructure.
