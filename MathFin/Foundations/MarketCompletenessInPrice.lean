/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralAgainstMartingale
public import MathFin.Foundations.MarketCompleteness

/-! # Replication as a holding in the price

`MarketCompleteness.exists_replicating_strategy` hedges a claim with an integrand against the
**driver** `B`. That is not what a trader holds. A trader holds units of the *price*, and the
gains are an integral against `S`. This file closes that gap for the discounted price

  `S_t = S₀ + (σ●B)_t`,

driftless by construction, which is what a discounted price is under the reference measure.

Two observations do the work.

* `pricePath_sub` — the increments of `S` are exactly the increments of `M = σ●B`. So
  integrating against `S` *is* integrating against `M`, and `ItoIntegralAgainstMartingale`
  already built that integral.
* `LpMulIsometry.exists_mulLI_eq` — when `σ ≠ 0` a.e., multiplication by `σ` is onto. So the
  hedge `φ` against `B` that martingale representation returns is `σψ` for a unique `ψ`, and
  `ψ` is the holding in the price.

**Only `σ ≠ 0` a.e. is needed, not a uniform lower bound.** The weighted norm does the
rescaling: `‖ψ‖²_{L²(⟨S⟩)} = ∫(φ/σ)²σ² = ∫φ² = ‖φ‖²`, so `ψ` is automatically an admissible
integrand however small `σ` gets. A uniform bound would be a real restriction on the model and
is not required.

## Scope

The hedge is produced and is unique; nothing here says the *wealth process* is a martingale
under a second measure, which is what the second FTAP needs and what
`PricingMeasureL2Density` takes up. And the price is driftless: a drift term
`∫b ds` is additive (it reuses the pathwise drift object of `DriftProcessModification`) and is
what the HJM bond dynamics need, but no result here requires it.

## Result

* `pricePath` — the discounted price `S₀ + (σ●B)`.
* `pricePath_sub` — its increments are the Itô integral's, which is why `∫ψ dS := ∫ψ dM`.
* `exists_replicating_strategy_in_price` — every square-integrable `𝓕ᴮ_T`-claim is the
  terminal wealth of a **unique** holding in the price.
-/

@[expose] public section

namespace MathFin
namespace MarketCompletenessInPrice

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM LpMulIsometry
  ItoIntegralAgainstMartingale ItoIntegralProcessGeneral
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ}

/-- The discounted price driven by `B` with volatility `σ`: `S_t = S₀ + (σ●B)_t`. -/
noncomputable def pricePath (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ S₀ + (itoProcessCLM hB T t hBmeas σ : Ω → ℝ) ω

/-- **The price's increments are the Itô integral's.** The initial value cancels, so a
Riemann–Stieltjes sum against `S` is one against `M = σ●B` — which is why integrating against
the price is `ItoIntegralAgainstMartingale`'s integral and needs no separate construction. -/
theorem pricePath_sub (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (s t : ℝ≥0) (ω : Ω) :
    pricePath hB T hBmeas S₀ σ t ω - pricePath hB T hBmeas S₀ σ s ω
      = (itoProcessCLM hB T t hBmeas σ : Ω → ℝ) ω
          - (itoProcessCLM hB T s hBmeas σ : Ω → ℝ) ω := by
  simp [pricePath]

/-- **Completeness, in the price.** Every square-integrable `𝓕ᴮ_T`-claim is the terminal
wealth `𝔼_μ[H] + ∫₀ᵀ ψ dS` of a **unique** holding `ψ` in the price, provided the volatility
is a.e. nonzero.

Martingale representation supplies the hedge `φ` against `B`; surjectivity of multiplication by
`σ` rewrites it as `σψ`; and the chain rule turns `∫ψ dS` back into `∫φ dB`. Uniqueness is
injectivity of an isometry. -/
theorem exists_replicating_strategy_in_price (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hσ : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), (σ : ℝ≥0 × Ω → ℝ) z ≠ 0)
    (H : Lp ℝ 2 μ)
    (hHmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] (⇑H) μ) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ),
      (⇑H) =ᵐ[μ] fun ω ↦ (∫ ω, H ω ∂μ)
        + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω := by
  obtain ⟨φ, hφ, -⟩ := exists_replicating_strategy hB hBmeas hBcont T H hHmeas
  -- the type ascription matters: `exists_mulLI_eq` produces the `sqWeight` form, which is
  -- `bracketMeasure` only up to unfolding, and instance search does not unfold it
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ),
      mulLI (trimMeasure_T (μ := μ) T hBmeas) (Lp.stronglyMeasurable σ).measurable ψ = φ :=
    exists_mulLI_eq (Lp.stronglyMeasurable σ).measurable hσ φ
  have hval : itoIntegralAgainstCLM hB T hBmeas σ ψ = itoIntegralCLM_T hB T hBmeas φ := by
    rw [itoIntegralAgainstCLM_apply, hψ]
  refine ⟨ψ, ?_, ?_⟩
  · show (⇑H) =ᵐ[μ] fun ω ↦ (∫ ω, H ω ∂μ)
        + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω
    rw [hval]
    exact hφ
  -- uniqueness: two holdings with the same terminal wealth have the same image, and the
  -- integral against `S` is an isometry, hence injective
  intro ψ' hψ'
  have hsame : itoIntegralAgainstCLM hB T hBmeas σ ψ'
      = itoIntegralAgainstCLM hB T hBmeas σ ψ := by
    refine Lp.ext ?_
    have h1 : (fun ω ↦ (∫ ω, H ω ∂μ)
        + (itoIntegralAgainstCLM hB T hBmeas σ ψ' : Ω → ℝ) ω) =ᵐ[μ]
        fun ω ↦ (∫ ω, H ω ∂μ) + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω := by
      refine hψ'.symm.trans ?_
      rw [hval]
      exact hφ
    filter_upwards [h1] with ω hω
    linarith [hω]
  have hnorm : ‖ψ' - ψ‖ = 0 := by
    rw [← norm_itoIntegralAgainstCLM (hB := hB) T hBmeas σ (ψ' - ψ), map_sub, hsame, sub_self,
      norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end MarketCompletenessInPrice
end MathFin
