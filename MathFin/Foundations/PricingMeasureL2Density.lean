/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.MarketCompletenessInPrice

/-! # The pricing measure, from a square-integrable density

`MarketCompleteness.emm_unique_of_complete` pins the pricing measure only among measures
assumed to satisfy `PricesGainsAtZero` — that every terminal Itô integral against `B` has zero
`Q`-mean. That hypothesis is not something to derive: under a measure other than `μ` the driver
`B` acquires a drift, and its integrals do not have zero mean. It has to be *replaced*, by a
condition on gains against the **price**, which is what an equivalent martingale measure
actually controls.

This file makes that replacement. For the discounted price `S = S₀ + (σ●B)` with `σ ≠ 0` a.e.,
if `S` is a `Q`-martingale and `Q` has a square-integrable density with respect to `μ`, then
`Q` prices the traded gains at zero — and hence, by the theorem already proved, agrees with `μ`
on the whole Brownian σ-algebra `𝓕ᴮ_T`. The hypothesis `PricesGainsAtZero` becomes a
*conclusion*.

## The argument

The map `ψ ↦ 𝔼_Q[∫ψ dS]` is a continuous linear functional on `L²(⟨S⟩)`: writing `Q = D·μ`, it
is `ψ ↦ ⟪D, ∫ψ dS⟫`, an inner product against a fixed `L²(μ)` element composed with an
isometry. So it suffices that it vanish on a dense set, and:

* on a **single band** `Z·1_{(a,b]}` the integral is `Z·(S_b − S_a)`
  (`itoIntegralAgainst_elementary`, the price's increments being the Itô integral's), whose
  `Q`-mean is zero because `S` is a `Q`-martingale and `Z` is bounded and `𝓕_a`-measurable —
  this is `ContinuousMarket.increment_integral_zero`, needing no stochastic integration at all;
* a **simple process** is the finite sum of its bands (`simpleAssemblyOfMeasure_eq_sum_bands`),
  so the functional vanishes there by linearity;
* the simple processes are **dense** in `L²(⟨S⟩)`
  (`PredictableDensityGeneral.simpleAssembly_sqWeight_denseRange`).

Square-integrability of the density is what makes the functional continuous: it is what lets
the `Q`-integral be written as `⟪D, ·⟫` for an `L²(μ)` element `D`, and continuity is then
`innerSL`'s, not something proved here by hand.

## The price is an abstract adapted process, deliberately

The martingale hypothesis is carried on an **abstract** `S : ℝ≥0 → Ω → ℝ` that agrees a.e. with
`pricePath` at each time up to the horizon, not on `pricePath` itself. This is not extra
generality for its own sake — it is the only form in which the hypothesis has a witness.
`Martingale` requires adaptedness on the nose, and `pricePath` is built from `Lp` classes whose
representatives are only *a.e.* `𝓕_t`-measurable, so `Martingale (pricePath …) 𝓕 Q` is a
hypothesis nothing is known to satisfy. `MarketCompletenessInPrice.pricePathCondExp` is the
witness at `Q = μ`, and `exists_density_price_martingale` below assembles it: the theorems here
are about a nonempty situation. It is also the form `ContinuousMarket.IsEMM` already uses, for
the same reason.

## Scope

Only `complete ⟹ unique` is reached, as before; the converse still needs Jacod–Yor. The density
is a hypothesis of the form `Q = μ.withDensity (ENNReal.ofReal ∘ D)` for `D ∈ L²(μ)`, rather
than a statement about `Measure.rnDeriv` — the same condition for `Q ≪ μ`, phrased so the
change-of-measure step is the `withDensity` transfer already in `LpMulIsometry`'s neighbourhood.

## Result

* `integral_eq_inner_density` — `𝔼_Q[X] = ⟪D, X⟫` for `X ∈ L²(μ)`.
* `gainsFunctional` — `ψ ↦ 𝔼_Q[∫ψ dS]`, as a continuous linear functional.
* `gainsFunctional_eq_zero` — it vanishes, by band → simple → dense.
* `pricesGainsAtZero_of_density` — **the hypothesis becomes a conclusion**.
* `measure_eq_of_density` — `Q` agrees with `μ` on `𝓕ᴮ_T`.
* `exists_density_price_martingale` — **the hypotheses have a witness**, so none of the above is
  vacuous.
-/

@[expose] public section

namespace MathFin
namespace PricingMeasureL2Density

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM LpMulIsometry
  ItoIntegralAgainstMartingale PredictableDensityGeneral ItoIntegralProcessGeneral
  MarketCompletenessInPrice
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ}

/-! ### The `Q`-integral as an inner product -/

omit [IsProbabilityMeasure μ] in
/-- **Change of measure, as an inner product.** With `Q = D·μ` and `D ≥ 0` square-integrable,
the `Q`-integral of a square-integrable `X` is `⟪D, X⟫`. Both the integrability and the bound
that make the gains functional continuous come from this one identity.

`D` needs no measurability hypothesis: an `Lp` element carries a strongly measurable
representative (`Lp.stronglyMeasurable`). -/
theorem integral_eq_inner_density {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω}
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω)) (X : Lp ℝ 2 μ) :
    ∫ ω, (X : Ω → ℝ) ω ∂Q = ⟪D, X⟫_ℝ := by
  rw [hQ, integral_withDensity_eq_integral_toReal_smul
    (Lp.stronglyMeasurable D).measurable.ennreal_ofReal
    (Eventually.of_forall fun ω ↦ ENNReal.ofReal_lt_top), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hD] with ω hω
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hω, RCLike.inner_apply, conj_trivial]
  ring

omit [IsProbabilityMeasure μ] in
/-- `Q`-integrability of a square-integrable variable, from the same identity. -/
theorem integrable_of_density {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω}
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω)) (X : Lp ℝ 2 μ) :
    Integrable (⇑X) Q := by
  rw [hQ, integrable_withDensity_iff_integrable_smul'
    (Lp.stronglyMeasurable D).measurable.ennreal_ofReal
    (Eventually.of_forall fun ω ↦ ENNReal.ofReal_lt_top)]
  refine Integrable.congr (L2.integrable_inner D X) ?_
  filter_upwards [hD] with ω hω
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hω, RCLike.inner_apply, conj_trivial]
  ring

/-! ### The gains functional -/

/-- `ψ ↦ 𝔼_Q[∫ψ dS]`, as a continuous linear functional on `L²(⟨S⟩)`: the integral against `S`
is an isometry, and the `Q`-integral is an inner product against the density. -/
noncomputable def gainsFunctional (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (D : Lp ℝ 2 μ) : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ) →L[ℝ] ℝ :=
  (innerSL ℝ D).comp (itoIntegralAgainstCLM hB T hBmeas σ)

theorem gainsFunctional_apply (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (D : Lp ℝ 2 μ)
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ)) :
    gainsFunctional hB T hBmeas σ D ψ = ⟪D, itoIntegralAgainstCLM hB T hBmeas σ ψ⟫_ℝ := rfl

/-- **The functional vanishes on a single band.** The integral of `Z·1_{(a,b]}` against the
price is `Z·(S_b − S_a)`, a predictable weight against a `Q`-martingale increment. The band's
endpoints lie below the horizon, which is where the modification hypothesis is used. -/
theorem gainsFunctional_bandLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {S₀ : ℝ}
    {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω))
    {S : ℝ≥0 → Ω → ℝ} (hSmod : ∀ t ≤ T, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t)
    (hmart : Martingale S (ItoIntegralL2.natFiltration hBmeas) Q)
    (V : TBoundedSP T hBmeas) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.val.value.support) :
    gainsFunctional hB T hBmeas σ D (bandLp T hBmeas σ V p) = 0 := by
  obtain ⟨C, hC⟩ := V.val.bounded_value
  have hab : p.1 ≤ p.2 := V.val.le_of_mem_support_value p hp
  have hbT : p.2 ≤ T := V.property p hp
  -- the band's integral is the increment, weighted
  have hband := itoIntegralAgainst_elementary (hB := hB) T hBmeas σ hab hbT
    (V.val.value p) (V.val.measurable_value p) C (fun ω ↦ by
      simpa [Real.norm_eq_abs] using hC p hp ω)
    (bandLp T hBmeas σ V p) (coeFn_bandLp T hBmeas σ V hp)
  -- its `Q`-mean is zero: a bounded `𝓕_{p.1}`-measurable weight against a martingale increment
  have hincr := ContinuousMarket.increment_integral_zero hmart hab
    ((V.val.measurable_value p).stronglyMeasurable)
    (K := C) (fun ω ↦ by simpa [Real.norm_eq_abs] using hC p hp ω)
  have hQac : Q ≪ μ := by rw [hQ]; exact withDensity_absolutelyContinuous _ _
  rw [gainsFunctional_apply, ← integral_eq_inner_density hD hQ]
  refine Eq.trans ?_ hincr
  refine integral_congr_ae ?_
  filter_upwards [Filter.Eventually.filter_mono hQac.ae_le hband,
    Filter.Eventually.filter_mono hQac.ae_le (hSmod p.1 (hab.trans hbT)),
    Filter.Eventually.filter_mono hQac.ae_le (hSmod p.2 hbT)] with ω hb h1 h2
  rw [hb, h1, h2]
  simp only [pricePath_sub, RCLike.inner_apply, conj_trivial]
  ring

/-- **The functional vanishes on every simple process**, being the finite sum of its bands. -/
theorem gainsFunctional_simpleAssembly (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {S₀ : ℝ}
    {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω))
    {S : ℝ≥0 → Ω → ℝ} (hSmod : ∀ t ≤ T, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t)
    (hmart : Martingale S (ItoIntegralL2.natFiltration hBmeas) Q)
    (V : TBoundedSP T hBmeas) :
    gainsFunctional hB T hBmeas σ D
      (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas σ) V) = 0 := by
  rw [simpleAssemblyOfMeasure_eq_sum_bands, map_sum]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  exact gainsFunctional_bandLp T hBmeas σ hD hQ hSmod hmart V hp

/-- **The functional vanishes.** It is continuous and zero on a dense set. -/
theorem gainsFunctional_eq_zero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {S₀ : ℝ}
    {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω))
    {S : ℝ≥0 → Ω → ℝ} (hSmod : ∀ t ≤ T, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t)
    (hmart : Martingale S (ItoIntegralL2.natFiltration hBmeas) Q) :
    gainsFunctional hB T hBmeas σ D = 0 := by
  haveI : IsFiniteMeasure (sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑σ)) :=
    instIsFiniteMeasureBracketMeasure (μ := μ) T hBmeas σ
  refine ContinuousLinearMap.ext fun ψ ↦ ?_
  refine congrFun (DenseRange.equalizer
    (simpleAssembly_sqWeight_denseRange T hBmeas (Lp.stronglyMeasurable σ).measurable)
    (gainsFunctional hB T hBmeas σ D).continuous continuous_const
    (funext fun V ↦ ?_)) ψ
  exact gainsFunctional_simpleAssembly T hBmeas σ hD hQ hSmod hmart V

/-! ### The payoff -/

/-- **The hypothesis becomes a conclusion.** A measure with a square-integrable density under
which the price is a martingale prices the traded gains at zero — the condition
`MarketCompleteness.emm_unique_of_complete` had to assume. The bridge from gains against `S` to
gains against `B` is surjectivity of multiplication by `σ`, which is where `σ ≠ 0` is used. -/
theorem pricesGainsAtZero_of_density (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hσ : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), (σ : ℝ≥0 × Ω → ℝ) z ≠ 0) {S₀ : ℝ}
    {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω))
    {S : ℝ≥0 → Ω → ℝ} (hSmod : ∀ t ≤ T, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t)
    (hmart : Martingale S (ItoIntegralL2.natFiltration hBmeas) Q) :
    PricesGainsAtZero hB T hBmeas Q := by
  intro φ
  refine ⟨integrable_of_density hD hQ _, ?_⟩
  -- every `B`-integrand is `σψ` for some holding `ψ` in the price
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ),
      mulLI (trimMeasure_T (μ := μ) T hBmeas) (Lp.stronglyMeasurable σ).measurable ψ = φ :=
    exists_mulLI_eq (Lp.stronglyMeasurable σ).measurable hσ φ
  have hval : itoIntegralAgainstCLM hB T hBmeas σ ψ = itoIntegralCLM_T hB T hBmeas φ := by
    rw [itoIntegralAgainstCLM_apply, hψ]
  have h0 := DFunLike.congr_fun
    (gainsFunctional_eq_zero (hB := hB) T hBmeas σ hD hQ hSmod hmart) ψ
  rw [gainsFunctional_apply, hval, ← integral_eq_inner_density hD hQ] at h0
  exact h0

/-- **`μ` is the pricing measure.** A probability measure with a square-integrable density under
which the price is a martingale agrees with `μ` on the whole of `𝓕ᴮ_T`. This is
`MarketCompleteness.measure_eq_of_pricesGainsAtZero` with its hypothesis discharged. -/
theorem measure_eq_of_density (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hσ : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), (σ : ℝ≥0 × Ω → ℝ) z ≠ 0) {S₀ : ℝ}
    {D : Lp ℝ 2 μ} (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQ : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω))
    {S : ℝ≥0 → Ω → ℝ} (hSmod : ∀ t ≤ T, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t)
    (hmart : Martingale S (ItoIntegralL2.natFiltration hBmeas) Q)
    {A : Set Ω} (hA : MeasurableSet[ItoIntegralL2.natFiltration hBmeas T] A) :
    Q A = μ A :=
  measure_eq_of_pricesGainsAtZero hB hBmeas hBcont T
    (by rw [hQ]; exact withDensity_absolutelyContinuous _ _)
    (pricesGainsAtZero_of_density T hBmeas σ hσ hD hQ hSmod hmart) hA

/-- **Nothing above is vacuous.** The density condition and the martingale condition are jointly
satisfiable: take `Q = μ` with the constant density `1`, and for the price the
conditional-expectation version `pricePathCondExp`, which is adapted on the nose and a
`μ`-martingale.

This is the price-side counterpart of `MarketCompleteness.pricesGainsAtZero_self`, and it is
worth stating because the martingale hypothesis is the one that could silently have had no
witness: `Martingale` demands adaptedness, and the `Lp`-valued `pricePath` supplies only its
a.e. version. -/
theorem exists_density_price_martingale (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∃ (D : Lp ℝ 2 μ) (S : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
        ∧ μ = μ.withDensity (fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω))
        ∧ (∀ t ≤ T, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t)
        ∧ Martingale S (ItoIntegralL2.natFiltration hBmeas) μ := by
  have hconst : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ := memLp_const 1
  refine ⟨hconst.toLp _, pricePathCondExp hB T hBmeas S₀ σ, ?_, ?_,
    fun t _ ↦ pricePathCondExp_ae_eq T hBmeas S₀ σ t,
    pricePathCondExp_isMartingale T hBmeas S₀ σ⟩
  · filter_upwards [hconst.coeFn_toLp] with ω hω
    rw [hω]
    norm_num
  · have h1 : (fun ω ↦ ENNReal.ofReal ((hconst.toLp _ : Ω → ℝ) ω)) =ᵐ[μ] (1 : Ω → ℝ≥0∞) := by
      filter_upwards [hconst.coeFn_toLp] with ω hω
      rw [hω]
      simp
    rw [withDensity_congr_ae h1, withDensity_one]

end PricingMeasureL2Density
end MathFin
