# Program architecture — owning the corner across more than one field

**Date:** 2026-08-06 (rev. 2026-08-09: three-repo constraint) · **Status:** design
proposal · **Companion:** [`applied-areas.md`](applied-areas.md)

**Constraint (owner decision, 2026-08-09):** exactly three repos —
`formal-mathfin`, `formal-econometrics`, and the foundry. The four *layers* below
survive unchanged; what changed is their mapping onto repos. The two
infrastructure layers do not get repos of their own: the apparatus anchors in
`formal-mathfin` (it must stay public — the gates run in the domain libraries'
public CI and on contributors' machines, and the foundry is private), and the
commons collapses into a `ForMathlib/` convention inside the domain libraries,
which the departure-lounge doctrine had already reduced it to in spirit.

The question: how should the repos be shaped for (1) maximum ownership of the
formally-verified-applied-mathematics corner, (2) the best autoformalization
foundry, (3) fastest theorem-coverage expansion, and (4) a mathematical
architecture that stays pristine?

---

## 0. The diagnosis — these are not four goals, they are two pairs

**Ownership and foundry quality are aligned and compounding.** Every additional
domain enriches the same three assets the foundry runs on: the proof-state cache,
the retrieval corpus, and the obstruction telemetry. A normalized goal state reached
in `Foundations/ItoIntegralL2` genuinely can recur in a time-series L² projection
argument — it is the same Hilbert machinery. `pipeline.toml` already says the state
cache is self-gating until cross-target recurrence is nonzero. **A second domain is
how that number becomes nonzero.** Multi-domain is not a tax on the foundry; it is
the foundry's training signal.

**Coverage expansion and pristine architecture are genuinely opposed.** Throughput
dilutes curation. This is the pair that needs engineering, because *discipline does
not survive contact with a working autoformalizer that lands a theorem every two
days.* Any plan that reconciles these two by resolving to be careful will fail.

So the architecture has one job in each direction: make the first pair's compounding
**mechanical** (one foundry, shared caches), and make the second pair's conflict
**structural** (a promotion ladder with machine-enforced ratios) rather than a matter
of vigilance.

---

## 1. Topology — four layers, three repos

```
                        formal-mathfin/            formal-econometrics/        foundry/  (private)
L0 commons              MathFin/ForMathlib/   ←──  Lake git-dep (or copy)
L1 apparatus            tools/verify/ (anchor) ──→ pip git-dep                 pip git-dep
L2 domain library       MathFin/ + benchmarks      Econometrics/ + benchmarks
L3 foundry                                                                     probe/ + domains/
```

The layers are roles, not repos. Two placement decisions do all the work:

### L0 commons → `ForMathlib/` inside the domain libraries

Field-neutral mathematics that several applied libraries need and Mathlib does not
have — from the substrate audit: **Brouwer and Kakutani fixed points** (absent —
verified), the **pointwise Birkhoff ergodic theorem** (absent), empirical-process
basics, mixing conditions.

The departure-lounge doctrine survives intact; only the address changes. The Lean
ecosystem already has the exact convention: a **`ForMathlib/` directory** —
"material that belongs upstream, staged here" (junwei-lu's asymptotic-statistics
repo uses it; so do many Mathlib-adjacent projects; `upstream/` here is the same
idea). So:

- A field-neutral lemma is born in **whichever domain library needs it first**,
  under `<Lib>/ForMathlib/`, upstream-tagged from day one.
- The rules that kept the commons from rotting transfer verbatim: every declaration
  carries an upstream target; a CI report ages them; nothing lives there
  permanently. A `ForMathlib/` entry with no upstream target is a `utils/` file
  with better branding.
- **Cross-library consumption, in order of preference:** (1) it lands in Mathlib
  and both libraries consume it at the next pin bump — upstreaming *is* the
  sharing mechanism, which is why aging is enforced; (2) for a single small lemma
  needed before upstream lands, **copy it**, marked with its origin — honest
  duplication with a deletion date beats infrastructure; (3) for a genuinely large
  block (the fixed-point tower), `formal-econometrics` takes a **Lake git-dependency
  on `formal-mathfin`** pinned to a tag. Lake elaborates only the imported closure,
  so the cost is not "build all of finance" — it is **pin lockstep**: both
  libraries must resolve the same Mathlib, so econometrics cannot bump until
  mathfin does. That is a real coupling; accept it only when the block is too big
  to copy, and let the aging report keep the pressure on until upstream removes
  the dependency again.

**Why this layer is still the ownership move.** Owning the most theorems in
econometrics is a weak claim — EconCSLib can outproduce us and probably will. Being
the group whose code everyone else *imports* is the claim that compounds. Brouwer is
missing from Mathlib; general equilibrium, Nash existence, and every fixed-point
equilibrium argument need it. Build and upstream it and EconCSLib, the GE projects,
and everyone after them consume our work.

> **Upstreamed lemmas are the only theorems that cannot be out-produced.**

The muscle already exists — `docs/upstreaming.md`, BrownianMotion PR #446 merged.
If anything, losing the commons repo *strengthens* this: there is now no
comfortable middle where field-neutral code can settle. It is in a domain library
on a deletion clock, or it is in Mathlib.

### L1 apparatus → anchored in `formal-mathfin`, consumed by the others

Today `tools/verify/` (ledger, coverage report, axiom-audit generator, corpus
model, blueprint render) and the three gate test-suites are excellent and are
**welded to one corpus**. The genericization still happens — but **in place**, not
into a new repo: `tools/verify` becomes corpus-parameterized (it already reads
`mathfin.toml`; the residual mathfin-isms are naming and defaults), and
`formal-econometrics` and the foundry consume it as a **pip git-dependency pinned
to a tag** (`pip install "mathfin @ git+https://github.com/raphaelrrcoelho/formal-mathfin@apparatus-v1"`),
plus `workflow_call` workflows referenced cross-repo the same way.

**Why mathfin and not the foundry:** the foundry is private, and the apparatus
must stay public — `build.yml` runs `python3 -m tools.verify.ledger status` in the
domain libraries' public CI, and outside contributors run the same gates locally.
Parking the honesty machinery in a private repo would make the public libraries'
green checkmarks irreproducible to anyone but us, which is the opposite of what
the machinery is for.

**The cost, stated honestly:** this is an asymmetric marriage — mathfin is
flagship *and* toolsmith, and apparatus changes motivated by econometrics land as
mathfin commits. Tolerable at one maintainer and two libraries; it is the first
thing to revisit if either stops being true. Two disciplines keep it honest:
apparatus releases are **tags** (`apparatus-v1`, `-v2`, …) so econometrics
upgrades deliberately rather than tracking a moving branch, and any
`tools/verify` change that special-cases mathfin's corpus (rather than reading
config) is treated as a bug.

What stays domain-side regardless: the pillar/bridge vocabulary, the blueprint
prose, the benchmark JSONs, each library's curated `AxiomAudit.lean` headliners.

### L2 Domain libraries — independent Lake projects, deliberately

Not a monorepo. Two reasons, and the first is decisive:

1. **The memory doctrine.** One Lean-loaded process on the box, ever. A shared Lake
   project means an econometrics edit re-elaborates finance, and you cannot build
   one library while checking another. Independence is what makes the box usable.
2. Each field's pillars/bridges should be answerable to that field. A shared build
   dilutes exactly the architectural claim that makes each library worth having.

The 3-repo corollary: since econometrics *may* take a Lake dep on mathfin for a
large `ForMathlib/` block, independence is now a **default with one sanctioned
exception**, entered only under the conditions in L0 above and exited at the next
successful upstream.

### L3 `foundry` — one pipeline, domain content as data

The coupling audit says this is cheap. "MathFin" appears roughly thirty times across
`probe/`, and essentially all of it is (a) library-name strings in prompts, (b) the
pedagogical example constant `MathFin.zcb`, (c) `MathFin/<Section>/` path prefixes.
There is no hardcoded repo checkout path. **The dependence is lexical, not
structural.**

So:

```
foundry/domains/<name>/
  house.md         the house doctrine (currently house_context.py's embedded prose)
  exemplars.json   the domain's example constants — replaces MathFin.zcb
  pillars.yaml     pillar/bridge vocabulary for the depth gate and the judge
  pointers.yaml    module map for the depth gate's "consumes a real def" check
  target.toml      repo, branch, namespace prefix, Lake root
```

`probe/` becomes domain-free. The depth gate, triviality gate, semantic repair
cascade, decomposer, and gate battery all transfer unchanged — they are already
domain-neutral logic wearing domain-specific prompts.

---

## 2. The promotion ladder — how (3) and (4) stop fighting

The mechanism: **let the corpus grow fast in a tier that does not claim to be
architecture, and make promotion into the architecture a separate, gated act.**

| Tier | Requirements | Growth |
|---|---|---|
| **T0 frontier** | kernel-checked · axiom-clean · ledger row · declared `formalization_status` | fast — this is what the foundry produces |
| **T1 spine** | T0 **plus** consumed by ≥1 other declaration *or* cited by a bridge · blueprint-tagged with honest prose · survived a values review | slow |
| **T2 keystone** | T1 **plus** makes two pillars one theorem (a bridge) | rare, hand-picked |

This is `formalization_status` lifted one level: from *how faithful is this to its
source* to *how load-bearing is this in the architecture*. Both are declared, both
are enforced, neither is a vibe. A T0 entry is not second-class — it is honestly
labelled, which is the whole house style.

### The two ratios, machine-enforced

**Leaf fraction.** Declarations with proof-term in-degree 0 that are not headline
results. A rising leaf fraction *is* the operational definition of drifting from a
theory toward a catalogue. This is the single most valuable number the program can
track, and it is currently not measured.

**Spine density.** Spine entries per 100 frontier entries; bridges per pillar.

**Gate the derivative, not the level.** Frontier may grow without limit. But if
spine density falls more than X% below its trailing average, or leaf fraction rises
past its trailing average, CI goes yellow and the values review is *forced* rather
than merely due. That converts "pristine architecture" from a virtue into a build
status — the same trick `test_values_review_is_current` already plays with cadence.

**Buildability.** `blueprint_export` + LeanArchitect already produce a dependency
graph, but over the 29 hand-curated spine nodes in `docs/blueprint_nodes.json`, not
the corpus. `axiom_audit_gen.collect_proof_position_names()` already extracts
corpus→MathFin citations (305 names) — that is the *outer* edge set. Whole-corpus
in-degree needs a Lean meta pass over `ConstantInfo` value dependencies, or a
coarser module-level approximation from `importGraph`, which is already a
dependency. Modest build, high leverage.

**Set the thresholds by measuring first.** Phase 1 is computing today's leaf
fraction and spine density on the 348-entry corpus. Picking a number before knowing
the current value is how you get a gate that either never fires or fires constantly.

---

## 3. Making the foundry compound

Beyond domain packs:

**Shared, domain-partitioned caches.** `runs/state-cache.json`, `runs/gate-cache.json`
and the embedding cache are per-run today. Promote to a store partitioned by domain
but queried across all of them. The gate cache must stay generation-keyed on the
Mathlib/Lean pin — that invalidation is already implemented and must not be lost in
the move.

**A held-out eval set.** To claim "best foundry" there has to be a number that is
not overfit to the targets used for tuning. Freeze N targets per domain, never tune
on them, and report per tick: first-pass close rate, tokens per accepted theorem,
gate-rejection mix, spine-promotion rate. Without a held-out set the obstruction
report measures the tuning, not the tool. This is the difference between a foundry
that is improving and one that appears to be.

**Route by tier, not only by difficulty.** The foundry may produce T0 freely; T1
promotion should require a distinct review pass. Do not let the component optimizing
throughput also decide what is architecturally load-bearing — that is precisely the
conflict §0 says cannot be resolved by good intentions.

**Point the foundry at `commons`.** A Brouwer construction is an excellent foundry
target: hard, self-contained, no domain vocabulary, and the payoff is upstream
ownership. It is also a genuine test of the decomposer, which is what that path was
built for.

---

## 4. Sequencing — one timing rule that matters more than the rest

> **Extract exactly once, when library two starts. Not before, not after.**

Before is speculative generality — the seams get guessed wrong, and a wrong seam in
shared infrastructure is worse than duplication. After is a de-duplication across
two live corpora, each with its own drift, which is the expensive version.

Concretely: **formal-econometrics phase 0 should deliberately copy the apparatus.**
Run its first ~20 entries on the copy, note what actually diverged, and genericize
`tools/verify` in place against that evidence — then delete the copy and switch
econometrics to the tagged pip dependency. The second library is the forcing
function that reveals which abstractions are real; do not pre-empt it.

| When | Move |
|---|---|
| Now | Foundry domain packs (`domains/mathfin/` first, extracted from `house_context.py` + `af_prompts.py`) — mechanical, testable against the existing corpus, and it makes library two a config change |
| Now | Measure leaf fraction and spine density on the 348-entry corpus. Numbers first, thresholds later |
| Library 2 phase 0 | Copy the apparatus into `formal-econometrics` deliberately. Do not genericize yet |
| Library 2 at ~20 entries | Genericize `tools/verify` in place in mathfin against observed divergence; tag `apparatus-v1`; econometrics and foundry switch to the tagged pip dep and delete their copies |
| First field-neutral block | `MathFin/ForMathlib/` (or the econometrics twin, whichever births it), upstream-tagged from day one, aging report wired into CI |
| If ever a library 3 | Revisit both the three-repo cap and a GitHub org together |

**On the org:** it makes the collection legible as a program rather than scattered
personal projects, which is worth real money for an ownership claim. But the repo
URL is load-bearing in the Zenodo DOI, the arXiv paper, and the HF dataset. GitHub
redirects, so a move is survivable rather than catastrophic — but the cost only
grows as more links accumulate. **This is closer to now-or-never than it appears.**
Decide deliberately rather than by drift.

---

## 5. What not to do

- **A monorepo.** The memory doctrine forbids it outright.
- **Genericizing the apparatus before library two exists.** You will guess the
  seams wrong.
- **A `ForMathlib/` without mandatory upstream targets.** That is a `utils/`
  directory.
- **Moving the apparatus into the private foundry.** The gates run in public CI
  and on contributors' machines; a private toolchain makes the public green
  checkmark irreproducible.
- **A standing Lake dependency between the domain libraries.** The sanctioned
  exception (L0) is temporary by construction — pin lockstep is the tax meter,
  and upstreaming is how the meter stops.
- **Competing on theorem count.** EconCSLib is at 40k lines. The defensible position
  is the faithfulness contract — kernel-enforced scope declarations against their
  LLM-as-judge — and the upstreamed substrate. Volume is the one axis where we lose.
- **Letting the foundry promote its own output to spine.** See §3.
