/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.AdaptedStochasticIntegralFreezing
public import MathFin.Foundations.WeightedQuadraticVariation

/-! # Quadratic variation of an Itô process with adapted coefficients

Step B2 of the adapted-coefficient Itô formula
(`docs/specs/2026-07-05-adapted-ito-formula-design.md`, status of 2026-10-03), in progress. The
target is `∑ₖ wₖ(ΔXₖ)² → ∫₀ᵀ w σ² ds` for `X = X₀ + A + σ●B` with a Lipschitz drift `A` and a
bounded adapted continuous weight `w`, by splitting `(ΔXₖ)²` into a drift part, a cross part, the
freezing defect of `AdaptedStochasticIntegralFreezing`, and the weighted quadratic variation of
`B`.

## Result so far

* `norm_sq_increment_le` — the increment of `M = σ●B` over `(a, b]` has squared `L²` norm at most
  `C²·(b − a)`, read off the bracket identity `norm_sq_increment_eq_bracket`.
-/

@[expose] public section

namespace MathFin
namespace AdaptedQuadraticVariation

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralAgainstMartingale ItoIntegralBrownian QuadraticVariationL2
  AdaptedStochasticIntegralFreezing LpMulIsometry
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

/-! ### The increments of `M = σ●B` -/

/-- **The increment of `M = σ●B` over `(a, b]` has squared `L²` norm at most `C²·(b − a)`.** By the
bracket identity the squared norm is `⟨M⟩((a,b] × Ω)`, the integral of `σ²` over the band. -/
theorem norm_sq_increment_le {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    ‖itoProcessCLM hB T b hBmeas (processToLp T hBmeas hadap hcont hbdd)
      - itoProcessCLM hB T a hBmeas (processToLp T hBmeas hadap hcont hbdd)‖ ^ 2
      ≤ C ^ 2 * ((b : ℝ) - a) := by
  rw [norm_sq_increment_eq_bracket (hB := hB) T hBmeas _ hab hbT]
  have hS : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod a b MeasurableSet.univ
  -- the density `σ²` is at most `C²`
  have hbound : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      ‖(processToLp (μ := μ) T hBmeas hadap hcont hbdd : ℝ≥0 × Ω → ℝ) z‖ₑ ^ 2
        ≤ ENNReal.ofReal (C ^ 2) := by
    filter_upwards [processToLp_coeFn (μ := μ) T hBmeas hadap hcont hbdd] with z hz
    rw [hz, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hbdd z.1 z.2) 2)
  -- the trim measure of the band is its length
  have htrim : trimMeasure_T (μ := μ) T hBmeas (Set.Ioc a b ×ˢ (Set.univ : Set Ω))
      = ENNReal.ofReal ((b : ℝ) - a) := by
    unfold trimMeasure_T
    rw [trim_measurableSet_eq _ hS, Measure.prod_prod, measure_univ, mul_one, timeMeasure_T,
      Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc zero_le hbT), timeMeasure_Ioc]
  have hle : bracketMeasure (μ := μ) T hBmeas (processToLp T hBmeas hadap hcont hbdd)
      (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((b : ℝ) - a) := by
    rw [bracketMeasure_eq, sqWeight, withDensity_apply _ hS, ← htrim, ← setLIntegral_const]
    exact setLIntegral_mono_ae measurable_const.aemeasurable (by
      filter_upwards [hbound] with z hz _ using hz)
  calc _ ≤ (ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((b : ℝ) - a)).toReal :=
        ENNReal.toReal_mono (by finiteness) hle
    _ = C ^ 2 * ((b : ℝ) - a) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg C),
        ENNReal.toReal_ofReal (sub_nonneg.2 (by exact_mod_cast hab))]

end AdaptedQuadraticVariation

end MathFin
