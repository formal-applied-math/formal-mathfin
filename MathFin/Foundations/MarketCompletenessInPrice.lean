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

## An adapted version, and why it is needed

`pricePath` is assembled from `Lp` classes. An `Lp` element's representative is strongly
measurable for the *ambient* σ-algebra; for the filtration it is only **a.e.** strongly
measurable (`ItoIntegralProcessGeneral.itoProcessCLM_aeStronglyMeasurable`). That is all the
`L²` theory needs, and it is strictly less than `Martingale` asks for, which is adaptedness on
the nose. So `Martingale (pricePath …) 𝓕 Q` is a hypothesis with no exhibited witness, and a
theorem assuming it risks being true and empty.

`pricePathCondExp` fixes this at no mathematical cost: `μ[X | 𝓕_t]` is `𝓕_t`-strongly
measurable *by construction*, and `(σ●B)_t` is a.e. equal to it — that is
`itoProcessCLM_eq_condExpL2`, the identity the tower is already built on. So the price has an
adapted martingale version, and downstream statements can be made about an abstract adapted `S`
with this as the witness.

## Result

* `pricePath` — the discounted price `S₀ + (σ●B)`.
* `pricePath_sub` — its increments are the Itô integral's, which is why `∫ψ dS := ∫ψ dM`.
* `exists_replicating_strategy_in_price` — every square-integrable `𝓕ᴮ_T`-claim is the
  terminal wealth of a **unique** holding in the price.
* `pricePathCondExp`, `pricePathCondExp_ae_eq`, `pricePathCondExp_isMartingale`, and
  `exists_adapted_price_martingale` — the adapted version, and the witness it provides.
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

/-! ### An adapted martingale version of the price -/

/-- **The price, with a representative a martingale statement can be made about.** Same process
as `pricePath` up to a null set (`pricePathCondExp_ae_eq`), but built from `μ[· | 𝓕_t]`, which is
`𝓕_t`-strongly measurable by construction rather than merely a.e. so. -/
noncomputable def pricePathCondExp (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ S₀ + (μ[⇑(itoIntegralCLM_T hB T hBmeas σ) | ItoIntegralL2.natFiltration hBmeas t]) ω

/-- **It is the same price.** `(σ●B)_t` is the `𝓕_t`-projection of the terminal integral
(`itoProcessCLM_eq_condExpL2`), and the `L²` projection agrees a.e. with the conditional
expectation. -/
theorem pricePathCondExp_ae_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (t : ℝ≥0) :
    pricePathCondExp hB T hBmeas S₀ σ t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t := by
  have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas σ)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) ((ItoIntegralL2.natFiltration hBmeas).le t)
  rw [Lp.toLp_coeFn] at h
  filter_upwards [h] with ω hω
  simp only [pricePathCondExp, pricePath, itoProcessCLM_eq_condExpL2]
  rw [hω]

/-- **The adapted price is a martingale**, being a constant plus a conditional-expectation
process. -/
theorem pricePathCondExp_isMartingale (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Martingale (pricePathCondExp hB T hBmeas S₀ σ) (ItoIntegralL2.natFiltration hBmeas) μ :=
  (martingale_const (ItoIntegralL2.natFiltration hBmeas) μ S₀).add
    (martingale_condExp (⇑(itoIntegralCLM_T hB T hBmeas σ))
      (ItoIntegralL2.natFiltration hBmeas) μ)

/-- **The price has an adapted martingale version.** This is what makes a hypothesis of the form
"`S` is an adapted `Q`-martingale agreeing a.e. with the price" satisfiable rather than empty —
at `Q = μ` the witness is `pricePathCondExp`. -/
theorem exists_adapted_price_martingale (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∃ S : ℝ≥0 → Ω → ℝ, Martingale S (ItoIntegralL2.natFiltration hBmeas) μ
      ∧ ∀ t, S t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t :=
  ⟨pricePathCondExp hB T hBmeas S₀ σ, pricePathCondExp_isMartingale T hBmeas S₀ σ,
    pricePathCondExp_ae_eq T hBmeas S₀ σ⟩

end MarketCompletenessInPrice
end MathFin
