/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.Caplet
public import MathFin.FixedIncome.VasicekBondPriceAt

/-!
# Bond prices at `t > 0` in the Vasicek model

`bondPrice Q 𝓕 D t T = 𝔼_Q[D T | 𝓕 t] / D t` (`Contracts/Models/Caplet.lean`) is the price at `t`
of one unit paid at `T`, for any stochastic discount factor `D`. For the Vasicek discount factor
`D t = exp(−∫₀ᵗ r)` and the natural filtration of the driving Brownian motion it is the affine
form of the time-`0` price at the remaining maturity (`bondPrice_vasicek`), read off the
conditional Laplace transform of the Wiener integral (`vasicekBondPrice_condExp`):

  `P(t, T) = A(T − t)·exp(−B(T − t)·r_t)`.

## Main results

* `bondPrice_vasicek` — `bondPrice` in the Vasicek model, almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The Vasicek bond price at time `t`.** With `D t = exp(−∫₀ᵗ r)` along the Vasicek integrated
rate and `𝓕` the natural filtration of the driving Brownian motion, the price at `t` of one unit
paid at `T` is `P(t, T) = A(T − t)·exp(−B(T − t)·r_t)` almost surely, where `r_t` is the short
rate in its Wiener representation and `A`, `B` are the coefficients of the time-`0` price at the
remaining maturity (`vasicekBondPrice_affine`). The measure is read as the pricing measure. -/
theorem bondPrice_vasicek (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
        (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) t T
      =ᵐ[μ] fun ω ↦ vasicekBondA θ σ κ ((T - t : ℝ≥0) : ℝ)
        * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
          * (vasicekSDEMean r₀ θ κ t + vasicekDiffusionTerm hB κ σ hκ.le t ω))) := by
  filter_upwards [vasicekBondPrice_condExp hB hBm r₀ θ σ hκ htT] with ω h
  change (μ[fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ T ω) | _]) ω
    / Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ t ω) = _
  rw [h, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

end MathFin.Contracts
