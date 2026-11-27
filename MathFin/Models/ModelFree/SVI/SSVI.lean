/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.ModelFree.SVI.TailCondition
public import MathFin.Models.ModelFree.MarketCallPrice

/-!
# SSVI slices are raw SVI slices

The surface SVI (SSVI) parametrisation writes the total implied variance at log-moneyness `k` of
a slice with at-the-money total variance `θ` as

  `w(k) = (θ/2) · (1 + ρ φ k + √((φ k + ρ)² + 1 − ρ²))`,

where `φ = φ(θ)` is the surface's skew-scale function evaluated at the slice. For `φ > 0` and
`ρ² ≤ 1` this is the raw SVI variance (`SVI.variance`) at the parameters read off `(θ, φ, ρ)`:

  `a = θ(1 − ρ²)/2`, `b = θφ/2`, `ρ`, `m = −ρ/φ`, `σ = √(1 − ρ²)/φ`.

So every result proved for raw SVI slices applies to an SSVI slice by instantiation; the tail
condition is one example (`tendsto_bsSmile_ssviParams_zero_iff`). This file is the slice-wise
statement: the surface (the dependence of `φ` on `θ`) and its calendar-spread conditions are not
formalised.

## Main definitions

* `ssviVariance`: the SSVI total variance of one slice.
* `ssviParams`: the raw SVI parameters of that slice.

## Main results

* `ssviVariance_eq_variance`: for `φ > 0` and `ρ² ≤ 1`, `variance (ssviParams θ φ ρ) k` is
  `ssviVariance θ φ ρ k`.
* `tendsto_bsSmile_ssviParams_zero_iff`: for `θ ≥ 0`, `φ > 0`, `ρ² ≤ 1` and positive variance,
  the SSVI-smiled call tends to `0` at large strikes iff `θ φ (1 + ρ) < 4`.
* `ssvi_tail_of_isPricingMeasure`: a pricing measure whose normalised calls are the SSVI-smiled
  call forces `θ φ (1 + ρ) < 4`.

## References

* [Gatheral and Jacquier, *Arbitrage-free SVI volatility surfaces*][GatheralJacquier2014], §4

## Tags

SSVI, surface SVI, implied variance, volatility surface, raw SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

open Filter Topology
open scoped NNReal

/-- The SSVI total variance of the slice with at-the-money variance `θ`, skew-scale `φ` and
correlation `ρ`, at log-moneyness `k`. -/
noncomputable def ssviVariance (θ φ ρ k : ℝ) : ℝ :=
  θ / 2 * (1 + ρ * φ * k + Real.sqrt ((φ * k + ρ) ^ 2 + 1 - ρ ^ 2))

/-- The raw SVI parameters of an SSVI slice: `a = θ(1 − ρ²)/2`, `b = θφ/2`, `ρ`, `m = −ρ/φ`,
`σ = √(1 − ρ²)/φ`. -/
noncomputable def ssviParams (θ φ ρ : ℝ) : Params where
  a := θ * (1 - ρ ^ 2) / 2
  b := θ * φ / 2
  rho := ρ
  m := -ρ / φ
  sigma := Real.sqrt (1 - ρ ^ 2) / φ

/-- **An SSVI slice is a raw SVI slice**: for `φ > 0` and `ρ² ≤ 1`, the SSVI variance is the raw
SVI variance at `ssviParams θ φ ρ`. The square root is `φ` times the raw one, since
`(φk + ρ)² + 1 − ρ² = φ²((k − m)² + σ²)`. -/
theorem ssviVariance_eq_variance {θ φ ρ : ℝ} (hφ : 0 < φ) (hρ : ρ ^ 2 ≤ 1) (k : ℝ) :
    variance (ssviParams θ φ ρ) k = ssviVariance θ φ ρ k := by
  have hσ : (Real.sqrt (1 - ρ ^ 2) / φ) ^ 2 = (1 - ρ ^ 2) / φ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have hφm : φ * (-ρ / φ) = -ρ := mul_div_cancel₀ _ hφ.ne'
  have hφ0 := hφ.ne'
  have hrad : (φ * k + ρ) ^ 2 + 1 - ρ ^ 2
      = φ ^ 2 * ((k - -ρ / φ) ^ 2 + (Real.sqrt (1 - ρ ^ 2) / φ) ^ 2) := by
    rw [hσ]
    field_simp
    ring
  have hs : Real.sqrt ((φ * k + ρ) ^ 2 + 1 - ρ ^ 2)
      = φ * Real.sqrt ((k - -ρ / φ) ^ 2 + (Real.sqrt (1 - ρ ^ 2) / φ) ^ 2) := by
    rw [hrad, Real.sqrt_mul (sq_nonneg φ), Real.sqrt_sq hφ.le]
  simp only [variance, ssviParams, ssviVariance]
  linear_combination (-(θ * ρ) / 2) * hφm + (-θ / 2) * hs

/-- **The SSVI tail condition**: for `θ ≥ 0`, `φ > 0`, `ρ² ≤ 1` and positive variance everywhere,
the SSVI-smiled call tends to `0` at large strikes iff `θ φ (1 + ρ) < 4`. The instance of
`tendsto_bsSmile_zero_iff` at `b = θφ/2`. -/
theorem tendsto_bsSmile_ssviParams_zero_iff {θ φ ρ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hρ : ρ ^ 2 ≤ 1) (hw : ∀ k : ℝ, 0 < ssviVariance θ φ ρ k) :
    Tendsto (bsSmile (ssviParams θ φ ρ)) atTop (𝓝 0) ↔ θ * φ * (1 + ρ) < 4 := by
  have hw' (k : ℝ) : 0 < variance (ssviParams θ φ ρ) k := by
    rw [ssviVariance_eq_variance hφ hρ]; exact hw k
  rw [tendsto_bsSmile_zero_iff _ (by simp only [ssviParams]; positivity) hw']
  simp only [ssviParams]
  constructor <;> intro h <;> linarith

/-- **A market that prices an SSVI slice satisfies the tail condition.** In a market with unit
numéraire and a positive asset, priced at `T` by `Q`, if the calls at the strikes `k F`, in units
of the forward `F`, have the SSVI-smiled Black price at every `k > 0` (with `θ ≥ 0`, `φ > 0`,
`ρ² ≤ 1` and positive variance), then `θ φ (1 + ρ) < 4`: the market's normalised calls vanish at
large strikes (`Market.IsPricingMeasure.isNormalizedCallPrice`), so the smiled call does, and
`tendsto_bsSmile_ssviParams_zero_iff` turns that into the condition. -/
theorem ssvi_tail_of_isPricingMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {M : Market Unit Ω} {T : ℝ≥0} {Q : MeasureTheory.Measure Ω} {θ φ ρ : ℝ} (hθ : 0 ≤ θ)
    (hφ : 0 < φ) (hρ : ρ ^ 2 ≤ 1) (hw : ∀ k : ℝ, 0 < ssviVariance θ φ ρ k)
    (hQ : M.IsPricingMeasure T Q) (hN : ∀ t ω, M.numeraire t ω = 1)
    (hpos : ∀ ω, 0 < M.asset () T ω) {F : ℝ} (hF : F = M.price Q (.pay T (.obs () T)))
    (hsmile : ∀ k > 0,
      M.price Q (Contracts.europeanCall (k * F) T) / F = bsSmile (ssviParams θ φ ρ) k) :
    θ * φ * (1 + ρ) < 4 :=
  (tendsto_bsSmile_ssviParams_zero_iff hθ hφ hρ hw).1
    ((hQ.isNormalizedCallPrice hN hpos hF).of_eqOn fun j hj ↦ hsmile j hj).tendsto_zero

end SVI
end MathFin
