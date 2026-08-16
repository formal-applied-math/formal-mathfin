# The Itô chain rule, the integral against a price, and the pricing measure — design

**Date:** 2026-08-16 · **Status:** design, approved · **Corpus at design time:** 353
**Companions:** [`mathematical-architecture.md`](../mathematical-architecture.md) (the I↔II seam),
[`leaps.md`](../leaps.md) (Leap 5, whose open hypothesis this addresses),
[`roadmap.md`](../roadmap.md) (crown-jewel conversions)

---

## 0. Summary

Build the stochastic integral `∫ψ dM` against an Itô integral `M = φ●B`, identify it with
`∫ψφ dB` (**the chain rule**), extend it to a price process, and use it to replace the
hypothesis `MarketCompleteness.PricesGainsAtZero` with a square-integrable-density
condition on the candidate pricing measure.

Three layers, all in scope:

| layer | content |
|---|---|
| **(a)** | `∫ψ dM` as a CLM on `L²(⟨M⟩)`, its isometry, the chain rule, elementary Riemann-sum agreement, uniqueness |
| **(b)** | `∫ψ dS` for a driftless Itô-process price; replication restated as a holding in `S` rather than in `B` |
| **(c)** | `IsEMM S Q` + `dQ/dμ ∈ L²(μ)` ⟹ gains-neutrality, hence EMM uniqueness on `𝓕ᴮ_T` without `PricesGainsAtZero` |

---

## 1. The gap, precisely

`Foundations/MarketCompleteness.lean:173` hypothesises

```lean
def PricesGainsAtZero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (Q : Measure Ω) : Prop :=
  ∀ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
    Integrable (itoIntegralCLM_T hB T hBmeas φ) Q ∧
      ∫ ω, itoIntegralCLM_T hB T hBmeas φ ω ∂Q = 0
```

and the module docstring names the reason: the wealth process built by martingale
representation is an integral against `B`, whereas an EMM `Q` for `S` is a measure under
which `S` is a martingale. `S` and `B` share only a filtration, so nothing in `IsEMM S Q`
makes `∫₀ᵀ φ dB` a `Q`-fair game. The same sentence appears in `ContinuousMarket.lean:34`,
`AxiomAudit.lean:1057`, `leaps.md`, `bridges.md` and `mathematical-architecture.md`: six
places recording one missing primitive, `∫ φ dS`.

**The honest ceiling of this design.** `PricesGainsAtZero` as literally stated is *false* for
a generic `Q ≪ μ`: under a measure other than `μ`, `B` acquires a drift and its stochastic
integrals do not have zero mean. The condition is not something to be derived — it is
something to be *replaced*. What this design delivers is the correct replacement: gains
measured against the **price**, whose zero-mean property does follow from `IsEMM`, under an
integrability condition on `Q` that is standard and nameable. The unconditional second FTAP
(`unique ⟹ complete`, Jacod–Yor) remains out of scope and untouched.

---

## 2. The mathematics

Fix a driver `φ ∈ L²(trim_T)` and set `M := φ●B`, i.e. `M_t = itoProcessCLM T t hBmeas φ`.
Its bracket is `d⟨M⟩ = φ² ds ⊗ dμ`, so the integrands square-integrable against `M` form

```
L²(⟨M⟩) := Lp ℝ 2 ((trimMeasure_T T hBmeas).withDensity (fun p ↦ ENNReal.ofReal (φ p ^ 2)))
```

The map `ψ ↦ ψφ` is a linear isometry `L²(⟨M⟩) → L²(trim_T)`, since
`∫|ψφ|² d(trim) = ∫|ψ|²φ² d(trim) = ∫|ψ|² d⟨M⟩`. Composing with `itoIntegralCLM_T` gives a
CLM whose isometry is exactly `‖∫ψ dM‖_{L²(μ)} = ‖ψ‖_{L²(⟨M⟩)}` — the Itô isometry against
`M`. The chain rule `∫ψ dM = ∫ψφ dB` then holds by construction, and the mathematical
content moves to the theorem that makes this *the* stochastic integral rather than a
notation:

> **Elementary agreement.** For `ψ = Z·1_{(a,b]}` with `Z` bounded and `𝓕_a`-measurable,
> `∫ψ dM =ᵐ Z·(M_b − M_a)`.

This is already nearly assembled from existing results:

* `ItoIntegralLocality.itoIntegralCLM_T_restrictAfterCLM` (`:776`) gives
  `∫ 1_{(u,T]}φ dB = ∫φ dB − (φ●B)_u`; applied at `u = a` and `u = b` and subtracted,
  `∫ 1_{(a,b]}φ dB = M_b − M_a`. Note `1_{(a,b]}φ = restrictAfterCLM a φ − restrictAfterCLM b φ`.
* `ItoIntegralLocality.itoIntegralCLM_T_smulAdapted` (`:511`) pulls the `𝓕_a`-measurable `Z`
  out, its support hypothesis being satisfied because `1_{(a,b]}φ` vanishes on `[0,a]`.

Uniqueness follows from density of the elementary integrands in `L²(⟨M⟩)`, which is also
what (c) needs. **One theorem serves both layers**, which is the main structural reason to
prefer this route.

---

## 3. Approach

**Chosen: transport the existing CLM through the multiplication isometry.**

Two alternatives were considered and rejected.

*Build `∫ dM` from scratch* — elementary sums `∑ᵢ Zᵢ(M_{tᵢ₊₁} − M_{tᵢ})`, their isometry
against `⟨M⟩`, then `extendOfNorm`. The chain rule would then be a theorem relating two
independently-constructed objects, and the construction would cover any `M` with an
absolutely continuous bracket. Rejected on two grounds: the isometry step needs the
*conditional* bracket identity `𝔼[(M_t − M_s)² | 𝓕_s] = 𝔼[⟨M⟩_t − ⟨M⟩_s | 𝓕_s]`, which the
tower does not have (only the unconditional `itoProcessCLM_norm_sq`); and at this pin
nothing except `φ●B` produces such an `M`, so the generality has no consumer. The chosen
route *proves* what this one would have assumed, and obtains the isometry free.

*Bare formula* — `∫ψ dM := itoIntegralCLM_T (ψφ)` on the flat domain with `ψφ ∈ L²` as a
side hypothesis. Rejected: not a CLM, the isometry cannot be stated in the `⟨M⟩` norm, and
without the weighted domain the uniqueness clause has nothing to quantify over. This is the
variant that would read as a definitional dodge rather than a construction.

**Upstream coherence.** `BrownianMotion/StochasticIntegral/StochasticIntegral.lean`
(van Winden) carries an axiomatic characterization of the stochastic integral —
`IsRiemannStieltjesExtension` (Riemann–Stieltjes agreement on elementary processes,
linearity, indistinguishability, dominated convergence) and `IsStochasticIntegral` (the
uniqueness clause). It is sorry-free and it is the right frame for our uniqueness statement.
It was written 2026-07-29 to 07-31 and **has only ever existed on `v4.33.0-rc1`**; our pin
`4d52fa77` (2026-07-24) is 90 commits behind, and the gap includes the toolchain bump.

Decision: **do not gate this phase on an RC toolchain bump.** State and prove our own
uniqueness-by-density now, shaped so that instantiating `IsStochasticIntegral` at the next
*stable* pin bump is mechanical. Record this as a follow-up issue.

---

## 4. Module design

Files are kept small, one theorem plus private helpers where practical, so the daemon
re-elaborates only what changed (`CLAUDE.md`, authoring-iteration note).

### 4.1 `Foundations/PredictableDensityGeneral.lean` — lift the density theorem

`ItoIntegralCLM.simpleAssembly_T_denseRange` (`:660`) proves simple processes dense in
`L²(trim_T)` by a π-λ argument over `predictableRect`. Reading its proof, it uses two
`trim_T`-specific facts: `setIntegral_eq_setIntegral_inter_supp` (that `trim_T` is supported
on `Ioc 0 T ×ˢ univ`) and that `{0} ×ˢ F₀` is `trim_T`-null. So the theorem does **not**
generalize to an arbitrary finite predictable measure. It does generalize under absolute
continuity, which transfers both facts:

```lean
theorem simpleAssembly_denseRange_of_absolutelyContinuous
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (ν : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure ν]
    (hν : ν ≪ trimMeasure_T (μ := μ) T hBmeas) :
    DenseRange (simpleAssembly_ν T hBmeas ν)
```

Work items:

1. `setIntegral_eq_zero_of_orthogonal_pred` (`:469`, already de-privatised for
   `ItoIntegralL2Dense`) restated for such a `ν`, deriving the support facts from `hν`.
2. `simpleAssembly_ν` — the assembly of a `TBoundedSP` into `Lp ℝ 2 ν`. Simple processes are
   bounded and `ν` is finite, so membership is immediate; this is the same underlying
   function as `simpleAssembly_T` with a different target space.
3. The density theorem itself, then `simpleAssembly_T_denseRange` **re-derived as the
   instance** `ν := trim_T`. The original statement must not change — it has downstream
   consumers (`ItoIntegralLocality`, `MartingaleRepresentation`, `ItoIntegralL2Dense`).

### 4.2 `Foundations/LpMulIsometry.lean` — the `p = 2` multiplication isometry

Mathlib has `MeasureTheory.withDensitySMulLI` only at `p = 1`. We need `p = 2` with the
density being the *square* of the multiplier:

```lean
noncomputable def mulLI (ν : Measure α) {f : α → ℝ} (hf : Measurable f) :
    Lp ℝ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (f x ^ 2)) →ₗᵢ[ℝ] Lp ℝ 2 ν

theorem mulLI_apply (ψ) : ⇑(mulLI ν hf ψ) =ᵐ[ν] fun x ↦ f x * ψ x
```

**The well-definedness point, which is where a naive attempt breaks.** An element of
`Lp ℝ 2 (f²·ν)` is a class modulo `(f²·ν)`-null sets, which is *coarser* than modulo
`ν`-null sets: `{f = 0}` is `(f²·ν)`-null but generally not `ν`-null. The map is nonetheless
well defined, because if `ψ =ᵐ[f²·ν] ψ'` then `fψ = fψ'` `ν`-a.e. — on `{f ≠ 0}` the
representatives agree, and on `{f = 0}` both products vanish. State this as its own lemma;
it is the load-bearing step.

The norm identity is `lintegral_withDensity_eq_lintegral_mul` after unfolding `eLpNorm`.

Tag the general-`p` form as an upstreaming candidate (`docs/upstreaming.md`); do not build
the general `p` unless it falls out.

### 4.3 `Foundations/ItoIntegralAgainstMartingale.lean` — layer (a)

```lean
noncomputable def bracketMeasure (T) (hBmeas) (φ : Lp ℝ 2 (trimMeasure_T T hBmeas)) :
    Measure (ℝ≥0 × Ω) :=
  (trimMeasure_T T hBmeas).withDensity fun p ↦ ENNReal.ofReal (φ p ^ 2)

noncomputable def itoIntegralAgainstCLM (hB) (T) (hBmeas) (φ) :
    Lp ℝ 2 (bracketMeasure T hBmeas φ) →L[ℝ] Lp ℝ 2 μ
```

with, in order of importance:

* `itoIntegralAgainst_eq` — **the chain rule**: `∫ψ dM = itoIntegralCLM_T (ψ·φ)`.
* `itoIntegralAgainst_elementary` — **elementary agreement**: for `Z` bounded and
  `𝓕_a`-measurable and `a ≤ b ≤ T`,
  `∫ (Z·1_{(a,b]}) dM =ᵐ[μ] fun ω ↦ Z ω * (M_b ω − M_a ω)`, proved from
  `itoIntegralCLM_T_restrictAfterCLM` twice plus `itoIntegralCLM_T_smulAdapted`.
* `itoIntegralAgainst_norm` — the isometry `‖∫ψ dM‖ = ‖ψ‖_{L²(⟨M⟩)}`.
* `itoIntegralAgainst_unique` — any CLM `L²(⟨M⟩) →L[ℝ] L²(μ)` agreeing with the
  Riemann–Stieltjes sums on elementary integrands equals `itoIntegralAgainstCLM`
  (`DenseRange.equalizer` against 4.1 at `ν := bracketMeasure`).
* `itoIntegralAgainst_isMartingale` — the process form is a martingale; via the chain rule
  and `itoIntegralProcessGen_isMartingale`.

`bracketMeasure` is finite (`ν(univ) = ∫φ² = ‖φ‖² < ∞`) and `≪ trim_T`, so 4.1 applies.
Both facts want their own one-line lemmas since every downstream instantiation needs them.

### 4.4 `Foundations/ItoProcessPrice.lean` — layer (b), the object

```lean
structure ItoPrice (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) where
  init : Ω → ℝ
  init_meas : StronglyMeasurable[ItoIntegralL2.natFiltration hBmeas 0] init
  vol : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)
```

`S.toProcess t ω := S.init ω + itoProcessCLM hB T t hBmeas S.vol ω`, and
`S.integral ψ := itoIntegralAgainstCLM hB T hBmeas S.vol ψ`.

**Driftless by construction, deliberately.** Both the finance results below and layer (c)
concern the *discounted* price under a martingale measure, which has no drift; carrying a
drift here would add pathwise time-integral side conditions that serve nothing in this
phase. The drift extension `S = S₀ + ∫b ds + (σ●B)` is what HJM's `dZ/Z` (#149, #150) needs
and is additive: it reuses `Foundations/DriftProcessModification.driftContinuousMod`, the
pathwise `∫₀ᵗ b ds` object the Girsanov work already built. Record it as a follow-up issue,
and say in the module docstring that the absence is a scope decision, not an oversight.

Results: `toProcess_isMartingale` (from 4.3), `integral_isometry`, `integral_zero_mean`.

### 4.5 `Foundations/MarketCompletenessInPrice.lean` — layer (b), the finance reading

```lean
theorem exists_replicating_strategy_in_price
    (S : ItoPrice T hBmeas)
    (hσ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), S.vol p ≠ 0)
    (H : Lp ℝ 2 μ)
    (hHmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] (⇑H) μ) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure T hBmeas S.vol),
      ⇑H =ᵐ[μ] fun ω ↦ (∫ ω, H ω ∂μ) + S.integral ψ ω
```

Proof: martingale representation gives `φ` with `H = 𝔼[H] + ∫φ dB`; set `ψ := φ/S.vol`.
Then `‖ψ‖²_{L²(⟨S⟩)} = ∫(φ/σ)²σ² = ∫φ² = ‖φ‖²`, so `ψ` is in the domain **automatically** —
note that only `σ ≠ 0` a.e. is needed, *not* a uniform lower bound, because the weighted norm
does the rescaling for us. Uniqueness is injectivity of an isometry.

This is the statement that makes completeness a claim about trading in the price, and it is
the one that shrinks `ContinuousMarket`'s "absent by design" paragraph. Update that
paragraph in the same commit; do not leave it asserting an absence that has been filled.

### 4.6 `Foundations/ContinuousMarket.lean` — minimal edit

`increment_integrable` (`:131`) and `increment_integral_zero` (`:143`) are `private` and are
exactly layer (c)'s base case: a bounded `𝓕_s`-measurable weight against a `Q`-martingale
increment is `Q`-integrable with zero `Q`-integral. De-privatise both, with docstrings
unchanged in content.

Do **not** build a `SimpleProcess → SimpleStrategy` bridge. The two simple-process notions in
the repo (Degenne's `SimpleProcess`, which `simpleAssembly` uses, and
`ContinuousMarket.SimpleStrategy`) are different types, and (c) does not need them
reconciled: summing `increment_integral_zero` over a simple process's rectangles directly is
shorter than any bridge. `isEMM_noArbitrageSimple` keeps its statement and its proof.

### 4.7 `Foundations/PricingMeasureL2Density.lean` — layer (c)

```lean
theorem emm_integral_gains_eq_zero
    (S : ItoPrice T hBmeas) {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hEMM : ContinuousMarket.IsEMM (P := μ) (𝓕 := ItoIntegralL2.natFiltration hBmeas)
              S.toProcess Q)
    (hQ : Q ≪ μ) (hd : MemLp (fun ω ↦ (Q.rnDeriv μ ω).toReal) 2 μ)
    (ψ : Lp ℝ 2 (bracketMeasure T hBmeas S.vol)) :
    Integrable (S.integral ψ) Q ∧ ∫ ω, S.integral ψ ω ∂Q = 0
```

The argument, in four steps, each landing on something that exists after 4.1–4.6:

1. For elementary `ψ`, `S.integral ψ` is the Riemann sum `∑ᵢ Zᵢ·(S_{tᵢ₊₁} − S_{tᵢ})`
   — this is 4.3's elementary agreement.
2. That sum is `Q`-integrable with zero `Q`-mean — 4.6, summed over the rectangles.
3. `ψ ↦ 𝔼_Q[S.integral ψ]` is a bounded linear functional on `L²(⟨S⟩)`:
   `|𝔼_Q[X]| = |𝔼_μ[X·dQ/dμ]| ≤ ‖X‖_{L²(μ)}·‖dQ/dμ‖_{L²(μ)}` by Cauchy–Schwarz, and
   `‖S.integral ψ‖_{L²(μ)} = ‖ψ‖_{L²(⟨S⟩)}` by 4.3. The same bound gives `Q`-integrability.
4. It vanishes on the elementary integrands (steps 1–2) which are dense (4.1), hence
   everywhere.

Then the payoff, mirroring the existing statements one-for-one so the diff is readable:

```lean
theorem measure_eq_of_sqIntegrableDensity   -- price-side analogue of measure_eq_of_pricesGainsAtZero
theorem emm_unique_of_complete_of_sqIntegrableDensity  -- price-side analogue of emm_unique_of_complete
```

**Keep the existing `PricesGainsAtZero` theorems.** They are not superseded — they are the
statement for an arbitrary strategy class with no price attached, and
`pricesGainsAtZero_self` remains the witness that nothing is vacuous. The new theorems are
additive, and the module docstring of `MarketCompleteness` should be rewritten to say which
statement a reader should reach for and why, rather than deleting the old framing.

---

## 5. Not in scope

Stated explicitly so no docstring claims them:

* the unconditional second FTAP `unique ⟹ complete` (Jacod–Yor extreme points);
* the drift term in `ItoPrice`, and therefore HJM's `dZ/Z` (follow-up issue);
* the integral against a general semimartingale, and NFLVR / Delbaen–Schachermayer
  ("meaning 2") — `ContinuousMarket`'s scope paragraph narrows but does not close;
* instantiating upstream's `IsStochasticIntegral` (blocked on a stable `v4.33.0` pin);
* the finite-state Farkas gap of `Foundations/SuperhedgingDuality` (#39), untouched and
  unrelated.

---

## 6. Risks and kill criteria

| # | risk | mitigation | kill |
|---|---|---|---|
| R1 | 4.1's lift hits a further `trim_T`-specific dependence beyond the two identified | read `setIntegral_eq_zero_of_orthogonal_pred` end-to-end before writing; the `hν ≪ trim_T` hypothesis was chosen precisely to transfer the support facts | fall back to proving density directly for `bracketMeasure` only — enough for (a) and (c), loses the reusable lemma |
| R2 | 4.2 well-definedness on `{f = 0}` | isolate it as its own lemma before building the isometry | none — this is a correctness point, not a scope one |
| R3 | (c) step 3's change-of-measure lemma has an awkward Mathlib form | confirm the `∫ X dQ = ∫ X·(dQ/dμ) dμ` API early (`Measure.rnDeriv`, `withDensity_rnDeriv_eq` family) | if the RN route is bad, hypothesise `Q = μ.withDensity g` with `g ∈ L²` directly — same theorem, slightly less idiomatic hypothesis |
| R4 | (c) does not land at all | (a) and (b) do not depend on it | ship 4.1–4.6, open an issue carrying §4.7's four-step argument verbatim |

**Memory doctrine binds every step**: one Lean-loaded process on this box. The daemon is the
default slot occupant; `lake build` takes the slot only with the daemon down. Never a second
env-loading command into a container already serving one.

**Daemon caveat**: `lean-check` runs with `autoImplicit true` while `lake build` runs with it
false. A file that checks clean in the daemon can still fail the build. Always
`lake build MathFin && lake lint` before calling anything green.

---

## 7. Acceptance criteria

- [ ] `lake build MathFin` green; `lake lint` green.
- [ ] Every new headline result has an `AxiomAudit.lean` entry, `#print axioms`-clean.
- [ ] `MathFin/AxiomAuditGen.lean` regenerated byte-fresh
      (`python3 -m tools.verify.axiom_audit_gen --write`) after the benchmark edits.
- [ ] New corpus entries, each with `metadata.formalization_status` and a
      `metadata.formalization_scope` disclosure:
      `sc-ito-chain-rule`, `sc-ito-integral-against-martingale`,
      `sc-predictable-density-ac`, `mf-replication-in-price`,
      `mf-emm-unique-l2-density` (the last conditional on (c) landing).
- [ ] `description` on each states what the entry **proves**, not the textbook theorem it is
      named after.
- [ ] `docs/coverage.md` rows; `docs/bridges.md` updated (the MRT.2 row's honest-scope
      paragraph changes materially); `docs/leaps.md` Leap 5's abstraction-boundary
      paragraph rewritten; `mathematical-architecture.md` I↔II row updated.
- [ ] `python3 -m tools.verify.ledger status` → all fresh.
- [ ] Full pytest green, including `test_values.py` and `test_router.py`.
- [ ] Every new `MathFin/` file carries `@[expose] public section` after its docstring.
- [ ] **Prose-vs-statement pass** over every docstring, `description` and doc paragraph the
      session touched, before the values review — per `CLAUDE.md`, this is the failure the
      other gates structurally cannot see.
- [ ] Values review recorded in `docs/values-review.md` with a ranked backlog, not a pass mark.
- [ ] Follow-up issues opened: the drift extension; `IsStochasticIntegral` instantiation at
      the next stable pin; (c) if it was killed.

---

## 8. Order of work

4.2 and 4.1 are independent and both are prerequisites for 4.3. 4.6 is independent of
everything and can be done at any point. Suggested order: 4.2 → 4.1 → 4.3 → 4.4 → 4.5 →
4.6 → 4.7, with 4.3's elementary-agreement theorem as the first real checkpoint, since it is
the one that proves the construction deserves its name.
