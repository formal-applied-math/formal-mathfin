/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionBrownian
public import MathFin.BlackScholes.CallSpreadDigital
public import MathFin.BlackScholes.StrikeGreeks

/-!
# Digital options in a jump-diffusion: minus the strike derivative of the call

The cash-or-nothing digital pays `1` when the price ends above the strike. Its price function,
`D(S, K, τ) = e^{−rτ}P(Se^Y > K)` with `Y` the log-return over `τ`, is `jumpDiffusionDigitalPrice`.

* `nullSingletonClass_jumpDiffusionIncrementLaw`: with a Gaussian part (`σ ≠ 0`, `τ > 0`) the
  log-return law has no atoms. Given the jumps, the log-return is an affine function of the
  standard normal sample with slope `σ√τ ≠ 0`.
* `hasDerivAt_jumpDiffusionCallPrice_strike`: so the call price function is differentiable in the
  strike at every `K`, and `∂C/∂K = −D`. This is the general strike derivative
  `hasDerivAt_integral_call`, for any law with no atom at the strike, applied to the price `Se^Y`.
* `jumpDiffusionDigitalPrice_zero`: without jumps the digital price is `e^{−rτ}Φ(d₂)`, read off the
  strike derivative of the Black–Scholes price (`hasDerivAt_bsV_K`) instead of computed. It is the
  value of `bs_cash_or_nothing_formula`, which computes it as a Gaussian integral.

Without a Gaussian part the law has the atom `bτ` (no jumps), and at the strike `Se^{bτ}` only the
one-sided derivatives exist (`tendsto_call_spread`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal Topology

/-- **With a Gaussian part the log-return law has no atoms**: for `σ ≠ 0` and `τ > 0` every point
has probability `0`. Given the jumps, the log-return is an affine function of the standard normal
sample with slope `σ√τ ≠ 0`, and the standard normal has no atoms
(`nullSingletonClass_gaussianReal`). -/
lemma nullSingletonClass_jumpDiffusionIncrementLaw (b : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (Λ : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    NullSingletonClass (jumpDiffusionIncrementLaw b σ Λ ν τ) := by
  have hs : σ * Real.sqrt τ ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.2 (NNReal.coe_pos.2 hτ)).ne'
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  refine ⟨fun y ↦ ?_⟩
  have hL := measurable_jumpDiffusionLogReturn b σ τ (measurableSet_singleton y)
  -- given the jumps, at most one Gaussian sample gives the log-return `y`
  have h0 (ω' : ℕ × (ℕ → ℝ)) :
      gaussianReal 0 1 ((fun z ↦ (z, ω')) ⁻¹' (jumpDiffusionLogReturn b σ τ ⁻¹' {y})) = 0 := by
    refine Set.Subsingleton.measure_zero (fun z₁ h₁ z₂ h₂ ↦ ?_) _
    simp only [mem_preimage, mem_singleton_iff, jumpDiffusionLogReturn] at h₁ h₂
    exact mul_left_cancel₀ hs (by linear_combination h₁ - h₂)
  rw [jumpDiffusionIncrementLaw, Measure.map_apply (measurable_jumpDiffusionLogReturn b σ τ)
    (measurableSet_singleton y), jumpDiffusionMeasure, Measure.prod_apply_symm hL]
  simp only [h0, lintegral_zero]

/-- **The digital price function** of a jump-diffusion: the cash-or-nothing digital paying `1`
when the price ends above the strike, discounted at the rate `r` and integrated against the
log-return law over `τ`, `D = ∫ e^{−rτ}1_{Seʸ > K} dμ_τ(y)`. -/
noncomputable def jumpDiffusionDigitalPrice (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    ℝ :=
  ∫ y, rexp (-r * τ) * (Ioi K).indicator (fun _ ↦ (1 : ℝ)) (S * rexp y)
    ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)

/-- The digital price is the discounted probability that the price ends above the strike,
`D = e^{−rτ}P(Se^Y > K)`. -/
lemma jumpDiffusionDigitalPrice_eq (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    jumpDiffusionDigitalPrice S K r b σ Λ ν τ
      = rexp (-r * τ) * (jumpDiffusionIncrementLaw b σ Λ ν τ).real {y | K < S * rexp y} := by
  have hset : MeasurableSet {y : ℝ | K < S * rexp y} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [jumpDiffusionDigitalPrice, integral_const_mul, ← integral_indicator_one hset]
  -- the two indicators agree pointwise by definition
  congr 1

/-- **The strike derivative of the jump-diffusion call price is minus the digital price.** With a
Gaussian part (`σ ≠ 0`, `τ > 0`) and a finite forward, the call price function is differentiable
in the strike at every `K`, and `∂C/∂K = −D`. The law has no atoms
(`nullSingletonClass_jumpDiffusionIncrementLaw`), so the general strike derivative
`hasDerivAt_integral_call` applies to the price `Se^Y`. -/
theorem hasDerivAt_jumpDiffusionCallPrice_strike {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) (hτ : 0 < τ) (K : ℝ) :
    HasDerivAt (fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      (-jumpDiffusionDigitalPrice S K r b σ Λ ν τ) K := by
  have := nullSingletonClass_jumpDiffusionIncrementLaw b hσ Λ ν hτ
  -- the price `Seʸ` has no atom at `K`, since `y ↦ Seʸ` is injective
  have hK : jumpDiffusionIncrementLaw b σ Λ ν τ {y | S * rexp y = K} = 0 :=
    Set.Subsingleton.measure_zero (fun y₁ (h₁ : S * rexp y₁ = K) y₂ (h₂ : S * rexp y₂ = K) ↦
      Real.exp_injective (mul_left_cancel₀ hS.ne' (h₁.trans h₂.symm))) _
  have h := (hasDerivAt_integral_call (by fun_prop : Measurable fun y ↦ S * rexp y)
    (hY.const_mul S) hK).const_mul (rexp (-r * τ))
  have hC : (fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      = fun k ↦ rexp (-r * τ)
          * ∫ y, max (S * rexp y - k) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ) := by
    funext k
    rw [jumpDiffusionCallPrice, integral_const_mul]
  rw [hC, jumpDiffusionDigitalPrice_eq, ← mul_neg]
  exact h

/-- **Without jumps the digital price is `e^{−rτ}Φ(d₂)`**, read off the strike derivative of the
call. The digital price is minus the strike derivative of the call price
(`hasDerivAt_jumpDiffusionCallPrice_strike`). Near `K` the call price is the Black–Scholes price
(`jumpDiffusionCallPrice_zero`), whose strike derivative is `−e^{−rτ}Φ(d₂)` (`hasDerivAt_bsV_K`).
This is the value that `bs_cash_or_nothing_formula` computes as a Gaussian integral. -/
theorem jumpDiffusionDigitalPrice_zero {S K r σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionDigitalPrice S K r (r - σ ^ 2 / 2) σ 0 ν τ
      = rexp (-r * τ) * Phi (bsd2 S K r σ τ) := by
  have hY : Integrable rexp (jumpDiffusionIncrementLaw (r - σ ^ 2 / 2) σ 0 ν τ) := by
    rw [jumpDiffusionIncrementLaw_zero]
    exact (integrable_exp_mul_gaussianReal 1).congr (ae_of_all _ fun x ↦ by simp)
  have h₂ : HasDerivAt (fun k ↦ jumpDiffusionCallPrice S k r (r - σ ^ 2 / 2) σ 0 ν τ)
      (-(rexp (-(r * τ)) * Phi (bsd2 S K r σ τ))) K :=
    (hasDerivAt_bsV_K hS hσ hK (NNReal.coe_pos.2 hτ)).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hK) fun k hk ↦ jumpDiffusionCallPrice_zero hS hk hσ ν hτ)
  rw [neg_mul]
  exact neg_injective ((hasDerivAt_jumpDiffusionCallPrice_strike hS hσ.ne' hY hτ K).unique h₂)

end MathFin
