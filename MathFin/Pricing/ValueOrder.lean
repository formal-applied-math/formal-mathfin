/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Pricing.Value
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The order on contract values

A pricing functional that is positive and preserves order: the value-level face of the
no-arbitrage monotonicity argument. A contract whose present value is non-negative along
every outcome is worth at least `0`; a contract whose present value dominates another's
along almost every outcome is worth at least as much; and a family of contracts whose
present value is convex in a real parameter prices to a convex function of that parameter.
These are what let a spread, a floor or a dominance relation proved on `pathPV` lift to
`Contract.value` — the continuous counterpart of the finite-state order results of
`ConvexPricingFunctional.lean` (`statePricePricing_nonneg`, `statePricePricing_convexOn`),
which price by summing non-negative state prices.

The proofs add no machinery: each statement is the corresponding order property of the
Bochner integral (`integral_nonneg`, `integral_mono_of_nonneg`, `integral_mono_ae`,
`integral_convexOn_of_integrand_ae`) applied to `Contract.value`, which *is* the integral
of `pathPV` against `Q`.

## Main results

* `Contract.value_nonneg` — present value non-negative along every outcome gives a
  non-negative value, with **no** integrability hypothesis: `integral_nonneg` holds
  unconditionally, and a non-integrable integrand integrates to the junk value `0`,
  which is still non-negative.
* `Contract.value_le_value_of_pathPV_le_ae` — almost-everywhere dominance gives the order
  on values, with the lower contract's present value non-negative almost everywhere and
  the upper contract's integrable. The integrability hypothesis is `integral_mono_of_nonneg`'s:
  without it the non-integrable side integrates to `0`, and `0` can exceed the upper
  value (take the upper contract's present value constant `-1`).
* `Contract.value_le_value` — the two-integrable form: when both contracts are integrable,
  dominance alone orders the values (`integral_mono_ae`).
* `Contract.value_convexOn` — a family of contracts whose present value is convex in a
  real parameter, on a convex set of parameters and with each member integrable, has a
  `ConvexOn` value function. The convexity hypothesis is stated almost everywhere, what
  `integral_convexOn_of_integrand_ae` consumes.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 1.1
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], ch. 5
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

contract value, monotonicity, dominance, non-negativity, convexity, pricing functional,
MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A contract whose present value is non-negative along every outcome has a non-negative
value.** No integrability hypothesis: the Bochner integral of a non-integrable function is
`0`, and `0 ≤ 0`. -/
theorem Contract.value_nonneg (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (c : Contract ι)
    (h : ∀ ω, 0 ≤ c.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) :
    0 ≤ c.value Q D X := by
  simp only [value]
  exact integral_nonneg h

/-- **A contract that dominates another almost everywhere is worth at least as much**, given
the lower contract's present value is non-negative almost everywhere and the upper
contract's is integrable. The integrability hypothesis is load-bearing: `integral_mono_of_nonneg`
needs it, because a non-integrable side integrates to the junk value `0`, and `0` can
exceed the upper contract's value. -/
theorem Contract.value_le_value_of_pathPV_le_ae (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (a b : Contract ι)
    (hnn : 0 ≤ᵐ[Q] fun ω ↦ a.pathPV (fun t ↦ D t ω) (scenarioAt X ω))
    (hb : Integrable (fun ω ↦ b.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) Q)
    (hle : (fun ω ↦ a.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) ≤ᵐ[Q]
      fun ω ↦ b.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) :
    a.value Q D X ≤ b.value Q D X := by
  simp only [value]
  exact integral_mono_of_nonneg hnn hb hle

/-- **The two-integrable form of `value_le_value_of_pathPV_le_ae`**: when both contracts are
integrable, dominance alone orders the values — `integral_mono_ae` applied to `Contract.value`. -/
theorem Contract.value_le_value (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (a b : Contract ι)
    (ha : Integrable (fun ω ↦ a.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) Q)
    (hb : Integrable (fun ω ↦ b.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) Q)
    (hle : (fun ω ↦ a.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) ≤ᵐ[Q]
      fun ω ↦ b.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) :
    a.value Q D X ≤ b.value Q D X := by
  simp only [value]
  exact integral_mono_ae ha hb hle

/-- **Convexity in a parameter is preserved by the value.** If a family of contracts has,
for almost every outcome, a present value that is convex in a real parameter `k` on a
convex set `s`, and each member of the family is integrable, then the value function is
convex on `s`: the `Contract.value` counterpart of `statePricePricing_convexOn`, with the
integral in place of the state-price sum. -/
theorem Contract.value_convexOn (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) {c : ℝ → Contract ι} {s : Set ℝ} (hs : Convex ℝ s)
    (hconv : ∀ᵐ ω ∂Q, ConvexOn ℝ s (fun k ↦ (c k).pathPV (fun t ↦ D t ω) (scenarioAt X ω)))
    (hint : ∀ k ∈ s, Integrable (fun ω ↦ (c k).pathPV (fun t ↦ D t ω) (scenarioAt X ω)) Q) :
    ConvexOn ℝ s (fun k ↦ (c k).value Q D X) := by
  simp only [value]
  exact integral_convexOn_of_integrand_ae (f := fun ω k ↦
    (c k).pathPV (fun t ↦ D t ω) (scenarioAt X ω)) hs hconv hint

end MathFin.Contracts
