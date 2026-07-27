# Upstream consumption review — the v4.31.0 → v4.32.0 pin bump

**Date:** 2026-07-27
**Pins:** Lean `v4.31.0` → `v4.32.0`; Mathlib `fabf563a` → `81a5d257`;
BrownianMotion `bdf5ea0c` → `4d52fa77`; LeanArchitect `v4.30.0` → `v4.32.0`.
**Scope:** what the two upstreams gained in the window, what MathFin should now
*consume* instead of carrying, and what MathFin keeps — with the reason.

A version bump is the one moment when the coherence lens (consume the idiomatic
Mathlib/Degenne lemma; never re-prove it) can be applied to the whole library at
once: the upstream API just moved under us, so every local scaffold is up for
re-examination against what landed. This is that pass. It is a **backlog with
owners-by-file**, not a verdict — the executed items are listed first, the rest
are ranked candidates.

---

## Why `v4.32.0` and not BrownianMotion's `HEAD`

BrownianMotion's `HEAD` (`5077304`, 2026-07-24) is on Lean `v4.33.0-rc1`.
Taking it would strand two dependencies:

* **LeanArchitect** (the blueprint extractor) has no `v4.33.0` tag — its newest
  is `v4.32.0`, and the lakefile's contract is "tag tracks our exact toolchain".
* **lean_scout** (the foundry's index extractor) is on `v4.32.0` at its own HEAD.

`4d52fa77` — BrownianMotion's own "Update to 4.32.0" commit — is the newest BM
commit on a *stable* toolchain, and its manifest pins Mathlib `81a5d257`, which
is literally Mathlib's "bump toolchain to v4.32.0". So every pin in the tower
lands on the same stable rung. `leanprover-community/repl` also tags `v4.32.0`,
so the lean-repl daemon's REPL resolution (`_resolve_repl_source`) keeps working.

Re-test `v4.33.0` once LeanArchitect and lean_scout tag it.

---

## Executed this bump (forced by the upstreams moving)

| what | where | why |
|---|---|---|
| `eLpNorm_condExp_le` → `eLpNorm_condExp_le_eLpNorm _ (by simp)` | `Foundations/ItoIntegralProcessGeneral.lean` (×2) | The old Mathlib name is **gone** at the new pin. Its replacement is the *generalised* `(f) {p} (hp : 1 ≤ p)` form — which is BM's `Auxiliary/Jensen.eLpNorm_condExp_le_eLpNorm`, **upstreamed into Mathlib** in this window and deleted from BM. Consuming it is the coherent move, not a workaround. |
| `NoAtoms` → `NullSingletonClass`, `noAtoms_gaussianReal` → `nullSingletonClass_gaussianReal` | `Foundations/StandardNormal.lean` | Deprecated aliases (since 2026-06-09). Still compile, with warnings; the class rename is upstream's, so we follow it. |
| stale docstring names | `BlackScholes/Call.lean`, `Foundations/PoissonRandomMeasure.lean` | `MeasureTheory.NoAtoms` and `poissonPMFReal` (deprecated → `poissonMeasure`) cited as live API. |
| coherence note repointed | `Foundations/ItoIntegralProcessContinuousModification.lean` | The note justified the file by "Degenne's `exists_modification_isCadlag` is `sorry`-backed". That lemma **no longer exists**: `StochasticIntegral/CadlagModification.lean` was deleted and replaced by `Quasimartingale/CadlagModification.lean` (1162 lines, `cadlagModif`). The justification survives — the successor still carries `sorry`s — but the citation had to be re-aimed at the real file, or the note would be an honest-looking claim about a name that is gone. |
| **the index-type change** (see below) | `Foundations/ItoIntegralL2.lean`, `Foundations/ItoIntegralProcess.lean` | `SimpleProcess.integral` went from `WithTop ι → Ω → G` to `ι → Ω → G` upstream, and `integral_top` was commented out. Both MathFin call sites broke. |
| duplicated Poisson convolution replaced by consumption | `Foundations/PoissonSuperposition.lean` | see "the duplicate we were carrying" below |

### The one that actually mattered: a type changed under a name that did not

`SimpleProcess.integral`, Degenne's elementary stochastic integral, was
`WithTop ι → Ω → G` at the old pin. `⊤` named the untruncated value and
`integral_top` unfolded it to the increment sum. At the new pin it is
`ι → Ω → G`: the index dropped `WithTop`, `integral_top` is commented out
upstream, and with `ι = ℝ≥0` there is no `⊤` left to evaluate at.

Two consequences, both instructive:

* `itoSimpleProcess` (evaluation at a finite `t`) needed only the coercion
  removed — `(t : WithTop ℝ≥0)` → `t` — and its `stoppedProcess` helper
  collapsed from `untopA` bookkeeping to `rfl`. Semantics unchanged.
* `itoSimple` (the untruncated value) can no longer be *expressed* as an
  evaluation of `integral`. It is now defined as the increment sum, with
  `itoSimple_apply` definitional, and its additivity/homogeneity — which used
  to ride on `integral_add_left`/`integral_smul_left` — proved directly on the
  `Finsupp` sum. Restoring the consumption relation (`itoSimple = integral … t`
  for any `t` dominating `V`'s finite support, via a `horizon V :=
  V.value.support.sup Prod.snd`) is a **follow-up**: it needs a
  time-independence lemma (`integral … i = integral … j` once both dominate the
  support) that also repairs additivity through `integral_add_left` at a common
  time. That is the coherent end state; the current form is the honest
  intermediate.

**No name-level sweep can catch this**, and neither can a grep: every
identifier we referenced still exists upstream. Only the build finds it. That
is the argument for the `pin-bump.yml` workflow this branch adds.

### Blast radius, honestly stated

The first pin-bump build named exactly two failing targets —
`Foundations.GirsanovSimpleDoleansMoments` and `Foundations.ItoIntegralL2` — out
of 8979. That understates it: Lake reports the *roots* of a failure and silently
skips their dependents. `ItoIntegralL2` has **39 transitive dependents** inside
`MathFin/` (the entire Itô-integral tower, including `ItoIntegralProcess`, which
carries the same `WithTop` idiom); `GirsanovSimpleDoleansMoments` has 2. So the
accurate statement after run 1 was: **223 of 262 MathFin modules verified
building at the new pin, 39 blocked behind one upstream type change, 2 blocked
behind a second failure.**

### The duplicate we were carrying

`MathFin.PoissonSuperposition.poissonMeasure_conv_poissonMeasure` proved
`poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b)` from the point
masses — a Cauchy product collapsed by the binomial theorem, ~95 lines with two
private helpers. Mathlib has proved *the same statement, verbatim*, since
2026-05-26 (leanprover-community/mathlib4#34435, via characteristic functions).
It was already upstream **at the old pin**: this was not drift introduced by the
bump, it was a standing duplication that the file's own docstring denied ("**no
convolution identity** for it") and the benchmark's `formalization_scope`
repeated ("absent from Mathlib").

Now a re-export. What the file still genuinely owns is
`indepFun_map_add_poissonMeasure`: Mathlib's superposition statements are
`HasLaw`-shaped, while the Poisson-process tower states increment laws as
pushforward equalities and derives the measurability side conditions from a
nonzero pushforward instead of assuming them.

The lesson generalises: **a "Mathlib does not have this" comment is a claim with
a shelf life.** MathFin makes 29 such claims in its docstrings. Re-testing all
29 against the new pin is what found this one — and it is the cheapest audit in
this document (greps, minutes). The other 26 held: no `tanh` derivative, no
matrix-valued differentiation, no Gaussian quantile/`Φ⁻¹` API, no
Farkas/polyhedral separation, no Lindeberg/triangular-array CLT, no counting
process, no gamma/exponential convolution, no Poisson generating function, and
still no `Lᵖ`-bound producer of uniform integrability. Two more were stale
rather than false and are corrected in this branch (`exists_modification_isCadlag`
no longer exists; Degenne now proves *an* isometry, just not ours).

### Our own contribution came back to us

`docs/upstreaming.md` still listed PR #446 (stochastic intervals) as "ready for
review". It **merged** — upstream commit `eaa4391`, present in every pin we have
used since, with the defs renamed `stochasticIoc` → `stochIoc` and friends. The
draft under `upstream/brownian-motion/` was a copy of code that is now upstream,
and is deleted. The other two staged drafts were re-checked and are still
genuinely absent upstream, so they remain live candidates.

### Method (repeatable at the next bump)

Both drift sweeps are name-level set arithmetic over the two upstream diffs, and
took seconds — worth re-running verbatim on every bump *before* a build:

1. Extract every declaration name **removed and not re-added** between the two
   revs (`git diff old new -- '*.lean'`, decl-head regex on `-`/`+` lines,
   `comm -23`), then intersect with the identifiers appearing in `MathFin/` and
   `benchmarks/`. Mathlib: 610 gone → **1 real hit** (`eLpNorm_condExp_le`).
   BrownianMotion: 74 gone → **1 real hit** (`exists_modification_isCadlag`,
   docstring-only).
2. Extract every name carrying `@[deprecated …]` at the **new** pin (4511 of
   them) and intersect the same way: 50 raw hits, of which the distinctive ones
   were `NoAtoms`, `noAtoms_gaussianReal`, `poissonPMFReal` — the rest are
   short-name collisions (`of`, `one`, `id`, …) and can be filtered by length.

This catches renames and removals. It does **not** catch signature changes,
`simp`-set drift, or instance-resolution changes — those need the build, which
is what actually found the `SimpleProcess.integral` index change.

**Two bugs in the sweep as first written, both worth fixing before reuse:**
tokenising with a `(?<![A-Za-z0-9_.'])` lookbehind means a dotted use like
`SimpleProcess.integral_top` never matches the bare removed name `integral_top`
— compare the *last component* of dotted uses as well, or the sweep silently
under-reports. And a declaration that upstream **comments out** rather than
deletes still shows up as removed on the `-` side while its `+` side (`-- @[simp]
lemma …`) matches nothing, which is correct here but means "gone" should be read
as "gone from the API", not "gone from the file".

---

## Ranked backlog: consume instead of carry

### 1. The a.e.-adapted / augmented-filtration gap is now closeable upstream

`Foundations/ItoIntegralProcessContinuousModification.lean` ends on an explicit
deferral: the `IsLocalMartingale` packaging of the general-integrand Itô process
"is **not** proved here", because Degenne's `Martingale.IsLocalMartingale` wants
paths càdlàg for *every* `ω`, which needs the usual conditions that
`natFiltration` does not carry.

The new BM pin ships exactly that bridge, in `Auxiliary/Adapted.lean` and
`Auxiliary/Indistinguishable.lean`:

* `AEStronglyAdapted X 𝓕 P` — adaptedness up to a null set,
* `AEStronglyAdapted.stronglyAdapted_mk` / `.indist_mk` — the everywhere-defined
  representative and its indistinguishability from `X`,
* `Indistinguishable` (`X ≡ᵐ[P] Y`) with `congr` lemmas, plus
  `limitProcess_congr` (`Auxiliary/LimitProcess.lean`),
* `Filtration.IsComplete` (`StochasticIntegral/Predictable.lean`) — the usual
  condition as a typeclass, so the augmentation becomes an instance argument
  rather than a hand-built filtration.

**Action:** re-attempt the deferred `IsLocalMartingale` packaging by moving to
the `.stronglyAdapted_mk` representative and stating the conclusion up to
`Indistinguishable`. This is the single highest-value item in this review: it
converts a documented gap into a consumed upstream theorem.

### 2. State predictability with Mathlib's class, not the unfolded form

`Foundations/DoobDecomposition.lean` encodes predictability as
`StronglyAdapted ℱ (fun n ↦ A (n + 1))` (matching Mathlib's older uniqueness
lemmas). Mathlib now states the Doob-decomposition facts in terms of the class:
`IsStronglyPredictable.predictablePart_eq`, `IsPredictable.martingalePart_eq`
(`Probability/Martingale/Centering.lean`), with
`IsStronglyPredictable.iff_measurable_add_one` bridging to the discrete form.

**Action:** restate `doob_decomposition{,_unique}` hypotheses as
`IsStronglyPredictable ℱ A`, converting via the `iff` where the proof needs the
shifted-adapted form. Idiomatic register + coherence, no math risk.

### 3. Localisation: audit against BM's `Locally` calculus

`StochasticIntegral/Locally.lean` was substantially rewritten (289 lines) and
now carries a full local-property calculus — `locally_of_ae`, `Locally.ae`,
`isStable_pathwise`, `isStable_{rightContinuous,left_limit,isCadlag,continuous}`,
`locally_*_iff`, `locally_isCadlag_iff_locally_ae` — alongside a new
`LocalizingLeastGE.lean`.

**Action:** audit `Foundations/ItoFormulaLocalized.lean` and the
`ItoIntegralProcessLocalMartingale*` family for hand-rolled "localise a pathwise
property along a localizing sequence" steps and replace them with the
`isStable_*` / `locally_*_iff` lemmas.

**Not** an action: `Foundations/ExitTime.lean` is *not* superseded by
`isLocalizingSequence_leastGE`. That lemma requires `𝓕.IsComplete P` **and**
`𝓕.IsRightContinuous`; `exitTime` is built precisely to avoid both, by using a
*closed* hit set so `{exitTime N ≤ i}` lands in the raw Brownian filtration.
Ours is the more applicable statement in our setting — keep it, and keep this
paragraph as the reason.

### 4. Martingale convergence: check against BM `Upcrossing`

BM added `Auxiliary/Upcrossing.lean` (upcrossing-strategy congruence lemmas,
`mul_upcrossingsBefore_le_sum_add_posPart`, the alternating-crossing
characterisations). `Foundations/L2MartingaleConvergence.lean` and
`Foundations/LpContinuousMartingaleConvergence.lean` should be checked for
overlap before either grows.

### 5. Conditional-expectation `Lp` estimates: a new upstream block to consume

The window upstreamed a whole `condExp`-in-`Lp` family into Mathlib
(`ConditionalExpectation/Real.lean`): `MemLp.condExp`,
`MemLp.lpNorm_condExp_le_lpNorm`, `MemLp.ae_norm_condExp_le_essSup`,
`integral_norm_condExp_le`, `setIntegral_norm_condExp_{,rpow_}le`,
`ae_bdd_norm_condExp_of_ae_bdd_norm`, `Integrable.norm_condExp_rpow_le`.
MathFin's Itô-tower `L²` estimates hand-derive several `condExp` contraction
steps; these are now one-liners upstream.

### 6. Keep, with the reason recorded

* `Foundations/UnifIntegrableL2.lean` — re-checked against the new pin: Mathlib
  still has **no** producer of uniform integrability from an `Lᵖ` bound with
  `p > 1` (`UniformIntegrable.lean`'s producers are all
  `of_tendsto_Lp{,_zero}` / `finite` / `const` / `subsingleton` shaped), and
  BM's `StochasticIntegral/UniformIntegrable.lean` producers are
  domination-shaped (`uniformIntegrable_of_dominated{,_singleton,_enorm_singleton}`)
  or `condExp`-shaped (`UniformIntegrable.condExp'`). The `L²`-bound → `L¹`-UI
  Chebyshev truncation stays ours.

---

## New upstream surface, for the record

**BrownianMotion** (`bdf5ea0c` → `4d52fa77`, +6333/−1187 over 40 files) — new
modules: `Auxiliary/{AEEq, Adapted, ConvergenceInMeasure, DenseCountable,
Indistinguishable, LeftLimWithin, LimitProcess, SeparableSpace,
StronglyMeasurablePath, Upcrossing}`, `Continuity/LimitModification`,
`StochasticIntegral/{Jump, LocalizingLeastGE, Predictable}`,
`StochasticIntegral/Quasimartingale/{Basic, CadlagModification,
MaximalInequality}`; `SquareIntegrable` (+624) and `Locally` heavily reworked;
`Choquet/CountableClosed` and `StochasticIntegral/CadlagModification` deleted.
Its `sorry` count went 42 → 57 — the new quasimartingale tower is work in
progress, so do not treat `cadlagModif` as a finished dependency.

**Mathlib** (`fabf563a` → `81a5d257`, 2334 files) — in MathFin's consumption
surface: the `condExp`-`Lp` block above, `Probability/HasCondDistrib.lean` (new),
the `NoAtoms` → `NullSingletonClass` rename, `poissonPMFReal` → `poissonMeasure`,
and the `Martingale/Centering.lean` predictability restatements.

---

## Verification status of this bump

The pins, the regenerated `lake-manifest.json` and the four source fixes above
are in this branch. The Mathlib olean cache host
(`lakecache.blob.core.windows.net`) is unreachable from the environment this
review was written in, so **no local `lake build` was run**: the build gate is
CI, and the corpus's verification ledger is stale by construction after a
substantive pin bump (`rebase-pins` is explicitly not a shortcut for one). The
remaining work is therefore: green `lake build` at the new pin, then a
`ledger verify` sweep on a machine that can hold a Lean environment.
