/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalHeatComparison
public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalTransition
public import MathFin.BlackScholes.AmericanPut.Stopping.ContactMartingale

/-! # Global supermartingality and identification with the American stopping value

The classical PDE contract supplies both stochastic verification properties: the envelope and the
waiting inequality (`DividendPutSolution.putWaiting`) give the supermartingale
(`brownianClassicalCandidate_supermartingale`, generic, in `ClassicalTransition`), and the
contact martingale comes from the PDE. Existence of a pair satisfying that contract is a
separate obligation.

## Result

Public entry points include `brownian_price_identification`, `brownian_boundary_curvature`,
`brownian_boundary_eq_classical`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem brownian_price_identification {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (hσ : 0 < σ) :
    brownianAmericanPut K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) :=
  brownian_price_identification_of_supermartingale hp hK hr hS hσ
    (brownianClassicalCandidate_supermartingale hp.toPutEnvelope hp.putWaiting hK.le hr hσ T)

theorem brownian_boundary_curvature {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal)) τ :=
  brownian_boundary_curvature_of_supermartingales hp hK hr hσ
    (fun T _ _ => brownianClassicalCandidate_supermartingale hp.toPutEnvelope hp.putWaiting
      hK.le hr hσ T) hτ

theorem brownian_boundary_eq_classical {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    brownianExerciseBoundary K r q σ τ.toNNReal = K*Real.exp (b (σ^2/2*τ)) := by
  apply threshold_eq_of_price_identification hp measurable_brownian_uncurry
    isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr
    (mul_pos (div_pos (sq_pos_of_pos hσ) (by norm_num)) hτ)
  intro S hS
  simpa only [brownianAmericanPut,Real.coe_toNNReal _ hτ.le] using
    brownian_price_identification (T := τ.toNNReal) hp hK hr hS hσ

theorem brownian_logBoundary_curvature {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ deriv
        (deriv (fun s : ℝ => Real.log (brownianExerciseBoundary K r q σ s.toNNReal/K))) τ := by
  have heq : (fun s : ℝ => Real.log (brownianExerciseBoundary K r q σ s.toNNReal/K)) =ᶠ[𝓝 τ]
      (fun s => b (σ^2/2*s)) := by
    filter_upwards [Ioi_mem_nhds hτ] with s hs
    rw [brownian_boundary_eq_classical hp hK hr hσ hs,
      mul_div_cancel_left₀ _ (ne_of_gt hK),Real.log_exp]
  rw [heq.deriv.deriv_eq]
  have hd : deriv (fun s => b (σ^2/2*s)) = fun s => (σ^2/2)*deriv b (σ^2/2*s) := by
    funext s
    simpa only [smul_eq_mul] using deriv_comp_mul_left (σ^2/2) b s
  rw [hd,deriv_const_mul_field,deriv_comp_mul_left]
  exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
    (Comparison.dividend_log_curvature hp _ (mul_pos (by positivity) hτ)))

theorem brownian_boundary_conclusions {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    (0 ≤ deriv (deriv (fun s : ℝ => Real.log (brownianExerciseBoundary K r q σ s.toNNReal/K))) τ) ∧
      0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal)) τ :=
  ⟨brownian_logBoundary_curvature hp hK hr hσ hτ,brownian_boundary_curvature hp hK hr hσ hτ⟩

/-- The zero-dividend financial milestone, specializing the new comparison proof. -/
theorem brownian_zeroDividend_boundary_conclusions {K r σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : NormalizedPutSolution (normalizedRate r σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    (0 ≤ deriv (deriv (fun s : ℝ => Real.log (brownianExerciseBoundary K r 0 σ s.toNNReal/K))) τ) ∧
      0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r 0 σ s.toNNReal)) τ :=
  brownian_boundary_conclusions (q := 0) (by simpa [normalizedRate] using hp) hK hr hσ hτ

/-- Liu's physical parameter range as an explicit financial milestone.
This specializes the new proof rather than formalizing Liu's published argument. -/
theorem brownian_liuRange_boundary_conclusions {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (_hLiu : q + σ ^ 2 / 2 ≤ r) (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    (0 ≤ deriv (deriv (fun s : ℝ => Real.log (brownianExerciseBoundary K r q σ s.toNNReal/K))) τ) ∧
      0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal)) τ :=
  brownian_boundary_conclusions hp hK hr hσ hτ

end MathFin.BlackScholes.AmericanPut.Stopping
