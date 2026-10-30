/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalContact
public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalBridge

/-!
# The remaining stochastic obligations on the constructed Brownian model

The contact rule is constructed, not hypothesized. Actual-boundary curvature
still depends on proving the candidate supermartingale and its first-contact
stopped martingale, as well as existence of the classical pair.

## Result

Public entry points include `brownianClassicalContactRule`,
`brownian_price_identification_of_martingales`, `brownian_boundary_curvature_of_martingales`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory Boundary
open scoped NNReal

/-- The classical first-contact rule `classicalContactRule`, instantiated on the constructed
Brownian model and its raw natural filtration. -/
noncomputable def brownianClassicalContactRule {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) : StoppingRule brownianFiltration T :=
  classicalContactRule (r := r) (q := q) (σ := σ) hp brownian_adapted continuous_brownian hK hS T

theorem brownian_price_identification_of_martingales {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S)
    (hsuper : Supermartingale (classicalCandidate brownian K r q σ S p T)
        brownianFiltration gaussianLimit)
    (hmart : Martingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t ((brownianClassicalContactRule hp hK hS T).time ω)) ω) brownianFiltration
          gaussianLimit) :
    brownianAmericanPut K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) :=
  classical_price_eq_value_of_contact_verification hp measurable_brownian_uncurry brownian_adapted
    continuous_brownian isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr hS hsuper hmart

/-- The stochastic/PDE bridge with the remaining obligations exposed for the
precise candidate and contact rule on the constructed probability space. -/
theorem brownian_boundary_curvature_of_martingales {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hsuper : ∀ (T : ℝ≥0) (S : ℝ), 0 < S →
      Supermartingale (classicalCandidate brownian K r q σ S p T) brownianFiltration gaussianLimit)
    (hmart : ∀ (T : ℝ≥0) (S : ℝ) (hS : 0 < S),
      Martingale (fun t ω => classicalCandidate brownian K r q σ S p T
        (min t ((brownianClassicalContactRule hp hK hS T).time ω)) ω)
            brownianFiltration gaussianLimit)
    {τ : ℝ} (hτ : 0 < τ) :
    0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal)) τ := by
  apply brownian_boundary_curvature_of_price_identification hp hK hr hσ _ hτ
  intro u hu S hS
  simpa only [Real.coe_toNNReal u hu.le] using
    brownian_price_identification_of_martingales hp hK hr hS (hsuper u.toNNReal S hS)
        (hmart u.toNNReal S hS)

end MathFin.BlackScholes.AmericanPut.Stopping
