/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Rates.VasicekMarket
public import MathFin.Models.Rates.AffineTermStructurePDE

/-!
# The Vasicek market price solves the Vasicek pricing PDE

The Vasicek bond market (`Models/Rates/VasicekMarket.lean`) and the term-structure PDE
(`Models/Rates/AffineTermStructurePDE.lean`) share the loadings `vasicekBondA`, `vasicekBondB`:
the market prices a unit payment at `T` at `A(T) e^{-B(T) r₀}`, and `u(τ, r) = A(τ) e^{-B(τ) r}`
solves the PDE. This module names that function (`vasicekBondPrice`) and states the two facts
about the one object: the market price of the unit payment at `T` is `vasicekBondPrice` at
`(T, r₀)`, and `vasicekBondPrice` satisfies the Vasicek PDE at `(T, r₀)`.

The PDE is verified for the function; that the market price solves it is by the identification
of the price with that function at the single point `(T, r₀)`. Feynman–Kac for the family of
markets started at every `r₀` is not proved.

## Main definitions

* `MathFin.Rates.vasicekBondPrice`: `A(τ) exp(−B(τ) r)`.

## Main results

* `MathFin.Rates.vasicekMarket_price_solves_pde`: the reference measure prices the Vasicek
  market, the price of a unit payment at `T` is `vasicekBondPrice θ σ κ T r₀`, and that function
  solves the Vasicek PDE at `(T, r₀)`.

## References

* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.3

## Tags

Vasicek model, bond price, term-structure PDE, pricing measure, MSC 91G30, JEL E43
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathFin MathFin.Contracts
open scoped NNReal
open ItoIntegralL2

namespace MathFin.Rates

/-- **The Vasicek bond price function** `u(τ, r) = A(τ) exp(−B(τ) r)`, in the time to maturity
`τ` and the short rate `r`. -/
noncomputable def vasicekBondPrice (θ σ κ τ r : ℝ) : ℝ :=
  vasicekBondA θ σ κ τ * Real.exp (-(vasicekBondB κ τ * r))

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
  (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)

/-- **The Vasicek market price solves the Vasicek pricing PDE.** The reference measure prices the
Vasicek market at the horizon `T`, the market price of a unit payment at `T` is
`vasicekBondPrice θ σ κ T r₀`, and `vasicekBondPrice` satisfies
`−∂_τ u + κ(θ − r)·∂_r u + ½σ²·∂²_r u − r·u = 0` at `(T, r₀)`. -/
theorem vasicekMarket_price_solves_pde (T : ℝ≥0) :
    (vasicekMarket hB hBm r₀ θ σ hκ T).IsPricingMeasure T μ ∧
      (vasicekMarket hB hBm r₀ θ σ hκ T).price μ (.pay T (.const 1))
        = vasicekBondPrice θ σ κ T r₀ ∧
      -deriv (fun t ↦ vasicekBondPrice θ σ κ t r₀) T
        + κ * (θ - r₀) * deriv (vasicekBondPrice θ σ κ T) r₀
        + σ ^ 2 / 2 * deriv (deriv (vasicekBondPrice θ σ κ T)) r₀
        - r₀ * vasicekBondPrice θ σ κ T r₀ = 0 :=
  ⟨isPricingMeasure_vasicekMarket hB hBm r₀ θ σ hκ T, price_pay_vasicekMarket hB hBm r₀ θ σ hκ T,
    vasicekBondPrice_solves_pde θ σ hκ.ne' T r₀⟩

end MathFin.Rates
