/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Call
public import MathFin.Foundations.StandardGaussianMGF

/-!
# Forward and futures pricing under the BS lognormal hypothesis

Under `BSCallHyp` (risk-neutral lognormal model), the risk-neutral
expectation of the terminal asset price equals the no-arbitrage forward
price:

    E_Q[S_T] = S_0 · e^{rT}.

This is the classical no-arbitrage relation `F = S_0 · e^{rT}` derived as
a direct consequence of the Gaussian MGF identity. The discounted asset
price is automatically a Q-martingale (at maturity):

    E_Q[e^{-rT} · S_T] = S_0.

No Itô calculus is required — pure Gaussian integration.

## Interpretation as a no-arbitrage price

A long forward contract pays `S_T − F` at maturity. The **forward price**
`F` is conventionally defined as the unique value making the contract
worth zero at inception. Under any risk-neutral measure `Q`, the zero-value
condition is

    0 = E_Q[e^{-rT}(S_T − F)] = e^{-rT}(E_Q[S_T] − F),

so `F = E_Q[S_T]`. Combined with `expected_terminal_eq_forward`, this gives
`F = S_0 · e^{rT}`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Risk-neutral expectation of terminal asset price -/

/-- **`n`-th moment of the terminal price against the standard normal**:
`∫ (bsTerminal z)^n dN(0,1) = S_0^n · exp(n·r·T + n(n−1)/2 · σ²T)` for `0 ≤ T`.

Direct instance of the affine-shifted standard-normal MGF: with `α = n(r − σ²/2)T` and
`β = nσ√T`, the integrand equals `S_0^n · exp(α + β·z)`, so the integral is
`S_0^n · exp(α + β²/2)`. -/
theorem integral_bsTerminal_pow_gaussianReal (S_0 r σ T : ℝ) (n : ℕ) (hT : 0 ≤ T) :
    ∫ z, (bsTerminal S_0 r σ T z)^n ∂(gaussianReal 0 1) =
      S_0^n *
        Real.exp ((n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  set α : ℝ := (n : ℝ) * (r - σ^2 / 2) * T with α_def
  set β : ℝ := (n : ℝ) * σ * Real.sqrt T with β_def
  have h_β_sq : β^2 = (n : ℝ)^2 * σ^2 * T := by
    rw [β_def]; ring_nf; rw [Real.sq_sqrt hT]
  have h_algebra :
      α + β^2 / 2 =
        (n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T := by
    rw [h_β_sq]; ring
  have h_pow : ∀ z : ℝ,
      (bsTerminal S_0 r σ T z)^n = S_0^n * Real.exp (α + β * z) := by
    intro z
    unfold bsTerminal
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    rw [α_def, β_def]; ring
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simp_rw [smul_eq_mul, h_pow]
  rw [show
        (fun z : ℝ ↦ gaussianPDFReal 0 1 z * (S_0^n * Real.exp (α + β * z)))
        =
        (fun z ↦ S_0^n * (Real.exp (α + β * z) * gaussianPDFReal 0 1 z))
      from funext (fun z ↦ by ring)]
  rw [integral_const_mul, integral_exp_affine_gaussianPDFReal_univ, h_algebra]

/-- **`n`-th moment of the terminal asset price** under `BSCallHyp`:
`E_Q[S_T^n] = S_0^n · exp(n · r · T + n(n−1)/2 · σ²T)`, the HasLaw transfer of
`integral_bsTerminal_pow_gaussianReal`. -/
theorem nthMoment_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q =
      S_0^n *
        Real.exp ((n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  obtain ⟨_hS_0, _hK, _hσ, hT, hZ⟩ := h
  have h_meas : Measurable fun z : ℝ ↦ (bsTerminal S_0 r σ T z)^n := by
    unfold bsTerminal; fun_prop
  rw [show (fun ω ↦ (bsTerminal S_0 r σ T (Z ω))^n) =
        (fun z ↦ (bsTerminal S_0 r σ T z)^n) ∘ Z from rfl,
      hZ.integral_comp h_meas.aestronglyMeasurable]
  exact integral_bsTerminal_pow_gaussianReal S_0 r σ T n hT.le

/-- **Terminal price is the forward in expectation** — the standard-normal-driver
form: `E[S_T] = F = S_0·e^{rT}`, the `n = 1` moment. -/
lemma integral_bsTerminal_eq_forward (S_0 r σ T : ℝ) (hT : 0 ≤ T) :
    ∫ z, S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z) ∂(gaussianReal 0 1)
      = S_0 * Real.exp (r * T) := by
  simpa [bsTerminal] using integral_bsTerminal_pow_gaussianReal S_0 r σ T 1 hT

/-- **No-arbitrage forward price**: under `BSCallHyp`,
    `E_Q[S_T] = S_0 · e^{rT}`.

This is the risk-neutral expectation of the terminal asset price, which is
the no-arbitrage forward price `F` for delivery at time `T`: the `n = 1` case of
`nthMoment_terminal`. -/
theorem expected_terminal_eq_forward
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, bsTerminal S_0 r σ T (Z ω) ∂Q = S_0 * Real.exp (r * T) := by
  simpa using nthMoment_terminal 1 h

/-! ### Discounted asset is a Q-martingale at maturity -/

/-- **Discounted terminal price equals spot**: under `BSCallHyp`,
    `E_Q[e^{-rT} S_T] = S_0`. This is the integrated form of the
    risk-neutral martingale property at maturity. -/
theorem discounted_terminal_eq_S0
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-(r * T)) * bsTerminal S_0 r σ T (Z ω) ∂Q = S_0 := by
  rw [integral_const_mul, expected_terminal_eq_forward h]
  rw [show Real.exp (-(r * T)) * (S_0 * Real.exp (r * T))
        = S_0 * (Real.exp (-(r * T)) * Real.exp (r * T)) from by ring,
      ← Real.exp_add,
      show -(r * T) + r * T = 0 from by ring, Real.exp_zero, mul_one]

end MathFin
