/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connectors: insurance premiums are prices

A net premium is the value of a survival-contingent contract, and the Esscher premium is a price
under the tilted measure.
-/

open MathFin MathFin.Contracts MeasureTheory
open scoped NNReal

/-- **The life annuity-due is a contract value.** If the lifetime `τ` has the survival
probabilities of the force of mortality `μ` at the dates `k < n`, the annuity-due is the value, on
the flat-rate discount `zcb r 0`, of the contract paying one at each date `k < n` while the
default indicator `1{τ ≤ k}` is still zero. -/
theorem MathFinFrontier.lifeAnnuityDue_eq_value {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q] {τ : Ω → ℝ} (hτ : Measurable τ) (r : ℝ) (μ : ℝ → ℝ)
    (n : ℕ) (hS : ∀ k < n, SurvivalModel.survivalFunction Q τ k = survivalFromForce μ k) :
    lifeAnnuityDue r μ n =
      (payFlows (fun k ↦ (k : ℝ≥0)) (fun k ↦ (.sub (.const 1) (.obs () k) : Payoff Unit)) n).value
        Q (fun t _ ↦ zcb r 0 t) fun _ t ω ↦ {ω | τ ω ≤ (t : ℝ)}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  sorry

/-- **The Esscher premium is the price under the Esscher tilt.** With the unit numéraire and the
insured loss `X` as the asset at `T`, the claim paying `X` at `T` is worth
`𝔼[X e^{hX}]/𝔼[e^{hX}]` under the tilted measure with density `e^{hX}/𝔼[e^{hX}]`. -/
theorem MathFinFrontier.esscherPremium_eq_price {Ω : Type*} [MeasurableSpace Ω]
    (M : Market Unit Ω) [IsProbabilityMeasure M.P] (hN : ∀ t ω, M.numeraire t ω = 1) (T : ℝ≥0)
    (h : ℝ) :
    M.price (M.P.withDensity fun ω ↦
        ENNReal.ofReal (Real.exp (h * M.asset () T ω) / ∫ ω', Real.exp (h * M.asset () T ω') ∂M.P))
      (.pay T (.obs () T)) =
      (∫ ω, M.asset () T ω * Real.exp (h * M.asset () T ω) ∂M.P) /
        ∫ ω, Real.exp (h * M.asset () T ω) ∂M.P := by
  sorry
