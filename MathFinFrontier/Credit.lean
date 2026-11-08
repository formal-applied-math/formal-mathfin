/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connectors: the credit portfolio is Merton's

Gordy's one-factor model is Merton's firm-value model with correlated drivers: given the systematic
factor, a name defaults with probability `oneFactorPD` of its Merton default probability `kmvPD`,
and a CDO tranche is a contract on the portfolio loss.
-/

open MathFin MathFin.Contracts MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **The conditional default probability of a Merton name is `oneFactorPD`.** If the standardised
log firm value is `√ρ M + √(1 − ρ) ε` with `M`, `ε` independent standard normals, then given `M`
the name defaults at `T` (firm value below the face value `F`) with probability
`oneFactorPD (kmvPD V₀ F r σ T) ρ M`. -/
theorem MathFinFrontier.condDefault_eq_oneFactorPD {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {M ε : Ω → ℝ} (hM : HasLaw M (gaussianReal 0 1) Q)
    (hε : HasLaw ε (gaussianReal 0 1) Q) (hind : M ⟂ᵢ[Q] ε) {V₀ F r σ T ρ : ℝ} (hV₀ : 0 < V₀)
    (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Q[{ω | bsTerminal V₀ r σ T (Real.sqrt ρ * M ω + Real.sqrt (1 - ρ) * ε ω) < F}.indicator
        (fun _ ↦ (1 : ℝ)) | MeasurableSpace.comap M inferInstance]
      =ᵐ[Q] fun ω ↦ oneFactorPD (kmvPD V₀ F r σ T) ρ (M ω) := by
  sorry

/-- **A tranche leg is worth the discounted expected tranche loss.** On a deterministic discount
curve `D`, with the portfolio loss fraction as the underlying `X ()`, the leg `trancheLeg a d T`
is worth `D T · 𝔼_Q[tranchePayoff a d (X () T)]`. -/
theorem MathFinFrontier.value_trancheLeg {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (D : ℝ≥0 → ℝ) (X : Unit → ℝ≥0 → Ω → ℝ) (a d : ℝ) (T : ℝ≥0) :
    (trancheLeg a d T).value Q (fun t _ ↦ D t) X = D T * ∫ ω, tranchePayoff a d (X () T ω) ∂Q := by
  sorry
