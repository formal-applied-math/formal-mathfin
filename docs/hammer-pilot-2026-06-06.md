# LeanHammer — pilot record and re-test procedure

**Status (2026-08-14): the 2026-06-06 verdict is EXPIRED, and the re-test it
asked for is now cleanly runnable for the first time.** The pilot ran hammer one
Lean version off its target and attributed its headline failure to exactly that
skew. The skew is gone: LeanHammer's main has targeted `v4.32.0` — our pin —
since 2026-07-14. Nothing here says hammer works; it says the experiment that
was supposed to decide has never actually been run under fair conditions.

| | pilot (2026-06-06) | now (2026-08-14) |
|---|---|---|
| our toolchain | `v4.30.0-rc2` | `v4.32.0` |
| LeanHammer target | `v4.30.0` **stable** — one step off | `v4.32.0` — **matched** (`c9ea5bf1`, 2026-07-14) |
| hammer rev | `c997b8dc` | main is `a841fded` (2026-08-08); **34 commits** since the pilot |
| our Mathlib | `c87cc97` | `81a5d257` |
| corpus | 267 entries | 353 entries |

## What the pilot established — and what it did not

**Established.** Build integration works, privacy configuration works, and
adding the dep is ledger-free (below). Also one capability observation that no
toolchain change explains away: *where hammer closed anything, `grind` already
closed it; where our toolkit fails — nonlinear inequalities — hammer failed
too.* That is the marginal-value bar any re-test has to clear.

**Not established: that hammer does not work for us.** The 0/10 is a kernel
*rejection* count, not a wrong-answer count — `(kernel) unknown constant
'_example._proof_N'`, auxiliary constants never reaching the kernel
environment. The report itself calls the root cause "consistent with the
one-step toolchain skew". The second disqualifier, ~31 min/goal against a paper
reporting <10 s average, is a 200x gap: a misconfiguration signature, not a
capability gap. The pilot died on infrastructure before it could test the
mathematical question.

## What moved upstream since

Three commits land directly on the pilot's *latency* disqualifier, and they are
recent:

| commit | date | why it matters here |
|---|---|---|
| `a5b550ac` | 2026-08-08 | "Ensure that `config.solverTimeout` is enforced when LeanHammer calls Lean-SMT" — a timeout that is *not* enforced produces exactly our runaway wall clock |
| `3ef1ecdc` | 2026-08-07 | "Make sure `tryAllTacsOnGoal` cancellation token is always set" — same failure family |
| `c24da67b` | 2026-08-08 | default wallclock lowered 10s → 5s |

On the *kernel* disqualifier there is no upstream issue tracking a
proof-reconstruction bug, which is weak evidence either way — but it does mean
the pilot's own skew hypothesis is now the leading explanation and is finally
testable.

**Watch before starting:** open issue
[#18](https://github.com/JOSHCLUNE/LeanHammer/issues/18) is an import-time error
(`invalid option declaration 'lazyReduce.skipProof'`). If it reproduces at our
pin it blocks the re-test at step 3.

## The re-test

Restated against the current pin. The pilot's operational findings are folded
in — they are the part that cost time to learn.

```bash
# 1. ONE Lean process (memory doctrine): the daemon must be down.
docker compose -f docker/docker-compose.yml down lean-repl

# 2. Pilot goals onto a branch off CURRENT main — do NOT check out the old
#    branch, which would revert the tree to June pins.
git checkout -b hammer-retest main
git checkout c51d683 -- tests/hammer_pilot/     # branch `hammer-pilot` is kept

# 3. Add the dep at a rev targeting v4.32.0 (main, or c9ea5bf1 or later).
#    Snapshot lean-toolchain first: `lake update` DID rewrite it last time.
cp lean-toolchain /tmp/lean-toolchain.bak
#    ...add the require to lakefile.lean, mathlib-LAST so its pins win and
#    batteries stays at Mathlib's rev (no Mathlib rebuild)...
lake update Hammer && diff /tmp/lean-toolchain.bak lean-toolchain || cp /tmp/lean-toolchain.bak lean-toolchain

# 4. Privacy is non-negotiable: every pilot file keeps
#    `set_library_suggestions sineQuaNonSelector.intersperse currentFile`,
#    or a self-hosted premise server. NEVER the default cloud selector.

# 5. Kernel replay is the metric — a tactic that "succeeds" proves nothing.
docker compose -f docker/docker-compose.yml run --rm --entrypoint sh verify \
  -c 'cd /app && lake env lean tests/hammer_pilot/PilotA.lean'
```

Ledger cost is zero: `Hammer`, `Duper`, `auto` and `«premise-selection»` are all
in `PIN_EXCLUDED_PACKAGES` (`tools/verify/ledger.py`), so adding the dep restales
no entries. The boundary test enforces that no library module imports them.

## What result changes the policy

The re-test is not "does it compile" — it is these three, in order:

1. **Does A1 land kernel-clean?** A field identity `grind` already closes. If
   this still fails at matched pins, the reconstruction bug is real rather than
   skew, and the verdict stands with much stronger evidence.
2. **Do B1–B3 close?** `Integrable.const_mul`, `Measurable` exp-affine,
   `MemLp.integrable_sq` — measure-theory premise lookups. **These are the
   discriminating goals.** The 2026-07-11 survey rates LeanHammer 73.5% Mathlib
   → 79.4% miniCTX-v2 with no OOD drop, but flags known gaps in *dependent
   types* and *no induction/arithmetic*, and calls it "untested on
   measure-theory-heavy code". That is precisely our slice. B1–B3 test the one
   thing the published numbers do not cover.
3. **Does A2/A3/A5 close?** The nonlinear-inequality class, where `grind` is 0/7
   on our corpus sample and `nlinarith [certificates]` is the incumbent. This is
   the only class where hammer would add capability rather than duplicate it.

Anything less than "clears the bar on 2 or 3" leaves the adoption answer
unchanged, because of the marginal-value observation above.

## Priority: low, but no longer blocked

This is an **authoring-loop** question for the main repo, not a foundry one. The
foundry has no hammer integration (its harness exposes `lean_loogle` /
`lean_leansearch` / `lean_state_search`, not `lean_hammer`), and its bottleneck
is the drafter/intent stage — every prove that reaches the vibe harness passes.
A working hammer would accelerate a stage that is not failing.

The standing policy this pilot produced lives in `CLAUDE.md` under "Automation
toolkit"; the gate that keeps hammer out of proof sources is
`tests/test_values.py`.

---

## The 2026-06-06 evidence

Preserved verbatim — this is the baseline any re-run measures against.

Hammer @ `c997b8dc` (main, targets Lean v4.30.0 **stable**) on our
`v4.30.0-rc2` + Mathlib `c87cc97`. Privacy held throughout: every pilot file
pins `set_library_suggestions sineQuaNonSelector.intersperse currentFile`
(local symbolic selection); no goal context left the machine.

15 goals extracted verbatim from MathFin proof sites (PilotA algebra/
inequalities, PilotB measure-theory premise lookups, PilotC stretch).
A and B were run; C was skipped as decision-irrelevant after A+B.

| Goal class | Result |
|---|---|
| A1 field identity (our `grind` CLOSES this) | tactic "succeeds" → **kernel rejects**: `(kernel) unknown constant '_example._proof_7'` |
| A2/A3/A5 nlinarith-class | `grind => sorry` suggestions + same kernel rejection / heartbeat timeout |
| A4 division-monotone | pipeline exhausted ("aesop failed") |
| A1–A5 with `{disableGrind := true}` (pure Aesop+Zipperposition+Duper) | **0/5**, suggestions degenerate to `sorry` |
| B1 `Integrable.const_mul` lookup | `grind => sorry` + kernel rejection |
| B2 `Measurable` exp-affine | same |
| B3 `MemLp.integrable_sq` lookup | same |
| B4 `Finset.sum_le_sum` | deterministic heartbeat timeout |
| B5 exp/div composite | deterministic heartbeat timeout |
| **Wall clock, PilotB (5 goals)** | **9366 s ≈ 2.6 h** (~31 min/goal; paper reports <10 s avg) |

Score: **0/10 kernel-accepted**, with a *systematic* failure mode, not a
capability gap: hammer's grind driver emits auxiliary constants
(`_example._proof_N`) that never reach the kernel environment — every
"found" proof is rejected at kernel replay, in both the REPL daemon AND
plain `lake env lean`. Root cause consistent with the one-step toolchain
skew (their main targets v4.30.0 stable; grind's internals moved between
rc2 and stable). The latency is a second, independent disqualifier.

Where hammer found *anything*, our existing toolkit already had it
(`grind` closes A1 directly — see docs/patterns.md "In-Lean automation");
where our toolkit fails (nonlinear inequalities), hammer failed too.

### What worked

- Build integration: Hammer+Duper+auto+premise-selection compile green
  against our pins (1157 jobs) with mathlib-last ordering (batteries kept
  at Mathlib's rev — no Mathlib rebuild) and the lean-toolchain rewrite
  guard (lake update DID rewrite it to v4.30.0; restored from snapshot).
- Privacy configuration: local selector ran throughout (the wall-clock
  profile is local-compute-bound; no cloud endpoint contacted).
- Ledger: the Hammer cluster is in `PIN_EXCLUDED_PACKAGES` — adding the
  dep restaled **zero** of 267 entries (boundary test enforces no library
  import).

---

*Provenance: the report was written on the `hammer-pilot` branch and moved into
`docs/` on 2026-08-14 during a stale-branch sweep. That branch is **kept** at
`c51d683` because the three pilot files (`tests/hammer_pilot/Pilot{A,B,C}.lean`)
live only there and step 2 of the re-test needs them — do not delete it without
first salvaging those files.*
