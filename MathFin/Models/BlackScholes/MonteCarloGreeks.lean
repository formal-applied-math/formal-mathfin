/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Call
public import MathFin.Models.BlackScholes.GBMLogMoments
public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.PDE
public import MathFin.Probability.Gaussian.GaussianCDFDeriv
public import MathFin.Probability.Gaussian.GaussianMoments
public import MathFin.Probability.Gaussian.GaussianPartialMoments
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.HasLaw

/-!
# Monte Carlo Greeks and the Euler step

PLACEHOLDER DOCSTRING — finalized as the theorems land.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### The one-step Euler–Maruyama scheme for geometric Brownian motion -/

/-- **The one-step Euler–Maruyama terminal** for geometric Brownian motion
`dS = r·S dt + σ·S dW`: one step of length `Δ` from `S₀` gives `S₀·(1 + r·Δ + σ·√Δ·z)`
for a standard-normal sample `z` (the Brownian increment `ΔW = √Δ·z`). -/
noncomputable def eulerGbmStep (S_0 r σ Δ z : ℝ) : ℝ :=
  S_0 * (1 + r * Δ + σ * Real.sqrt Δ * z)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {S r σ Δ : ℝ} {Z : Ω → ℝ}

/-- The Euler step is an affine function of the standard normal. -/
private lemma eulerGbmStep_affine (S r σ Δ z : ℝ) :
    eulerGbmStep S r σ Δ z = S * (1 + r * Δ) + (σ * S * Real.sqrt Δ) * z := by
  unfold eulerGbmStep
  ring

omit [IsProbabilityMeasure Q] in
/-- The Euler step is Gaussian: an affine image of the standard normal. -/
private lemma eulerGbmStep_hasLaw (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    HasLaw (fun ω ↦ eulerGbmStep S r σ Δ (Z ω))
      (gaussianReal (S * (1 + r * Δ))
        (NNReal.mk ((σ * S * Real.sqrt Δ) ^ 2) (sq_nonneg _) * 1)) Q := by
  have hfun : (fun ω ↦ eulerGbmStep S r σ Δ (Z ω))
      = (fun ω ↦ S * (1 + r * Δ) + (σ * S * Real.sqrt Δ) * Z ω) := by
    funext ω; rw [eulerGbmStep_affine]
  rw [hfun]
  have hL := gaussianReal_const_add (gaussianReal_const_mul hZ (σ * S * Real.sqrt Δ))
    (S * (1 + r * Δ))
  rw [mul_zero, zero_add] at hL
  exact hL

omit [IsProbabilityMeasure Q] in
/-- The Euler step's mean is the linearized drift `S₀(1 + rΔ)`. -/
private lemma eulerGbmStep_mean_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q = S * (1 + r * Δ) := by
  rw [(eulerGbmStep_hasLaw hZ).integral_eq, integral_id_gaussianReal]

omit [IsProbabilityMeasure Q] in
/-- The Euler step's variance is `σ²S₀²Δ` for a nonnegative step, in the second-moment form
`𝔼[X²] − 𝔼[X]²`. -/
private lemma eulerGbmStep_variance_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) (hΔ : 0 ≤ Δ) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q) ^ 2
      = σ ^ 2 * S ^ 2 * Δ := by
  have hsq : (σ * S * Real.sqrt Δ) ^ 2 = σ ^ 2 * S ^ 2 * Δ := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hΔ]
  rw [integral_sq_of_hasLaw_gaussianReal (eulerGbmStep_hasLaw hZ), eulerGbmStep_mean_eq hZ,
    NNReal.coe_mul, NNReal.coe_one, mul_one, NNReal.coe_mk, hsq]
  ring

omit [IsProbabilityMeasure Q] in
/-- The exact GBM step's mean is `S₀e^{rΔ}` (the MGF of the lognormal step). -/
private lemma bsTerminal_mean_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) (hΔ : 0 ≤ Δ) :
    ∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q = S * Real.exp (r * Δ) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ ↦ bsTerminal S r σ Δ z) (gaussianReal 0 1) := by
    unfold bsTerminal
    exact (by fun_prop : Measurable fun z : ℝ ↦
      S * Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * z)).aestronglyMeasurable
  have hkey : (r - σ ^ 2 / 2) * Δ + (σ * Real.sqrt Δ) ^ 2 / 2 = r * Δ := by
    have hsq : (σ * Real.sqrt Δ) ^ 2 = σ ^ 2 * Δ := by
      rw [mul_pow, Real.sq_sqrt hΔ]
    rw [hsq]; ring
  rw [show (fun ω : Ω ↦ bsTerminal S r σ Δ (Z ω))
        = (fun z : ℝ ↦ bsTerminal S r σ Δ z) ∘ Z from rfl,
    hZ.integral_comp hmeas]
  simp only [bsTerminal]
  rw [integral_const_mul,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    show (fun x : ℝ ↦ gaussianPDFReal 0 1 x •
        Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x))
      = fun x : ℝ ↦ Real.exp ((r - σ ^ 2 / 2) * Δ)
          * (Real.exp (σ * Real.sqrt Δ * x) * gaussianPDFReal 0 1 x) from
      funext fun x ↦ by rw [smul_eq_mul, Real.exp_add]; ring,
    integral_const_mul, integral_exp_mul_gaussianPDFReal_univ,
    ← Real.exp_add, hkey]

omit [IsProbabilityMeasure Q] in
/-- The exact GBM step's variance is `S₀²e^{2rΔ}(e^{σ²Δ} − 1)` for a nonnegative step, in the
second-moment form `𝔼[X²] − 𝔼[X]²` (`variance_terminal`'s form). -/
private lemma bsTerminal_variance_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) (hΔ : 0 ≤ Δ) :
    ∫ ω, bsTerminal S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q) ^ 2
      = S ^ 2 * Real.exp (2 * r * Δ) * (Real.exp (σ ^ 2 * Δ) - 1) := by
  have hmeas2 : AEStronglyMeasurable (fun z : ℝ ↦ bsTerminal S r σ Δ z ^ 2)
      (gaussianReal 0 1) := by
    unfold bsTerminal
    exact (by fun_prop : Measurable fun z : ℝ ↦
      (S * Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * z)) ^ 2).aestronglyMeasurable
  have hkey2 : (r - σ ^ 2 / 2) * Δ * 2 + (σ * Real.sqrt Δ * 2) ^ 2 / 2
      = 2 * r * Δ + σ ^ 2 * Δ := by
    have hsq : (σ * Real.sqrt Δ * 2) ^ 2 = σ ^ 2 * Δ * 4 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hΔ]; ring
    rw [hsq]; ring
  have hsplit2int : ∀ x : ℝ,
      gaussianPDFReal 0 1 x * ((S * Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x)) ^ 2)
        = (S * Real.exp ((r - σ ^ 2 / 2) * Δ)) ^ 2
            * (Real.exp ((σ * Real.sqrt Δ * 2) * x) * gaussianPDFReal 0 1 x) := by
    intro x
    have hsq : Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x) ^ 2
        = Real.exp ((r - σ ^ 2 / 2) * Δ * 2) * Real.exp ((σ * Real.sqrt Δ * 2) * x) := by
      conv_lhs => rw [pow_two, ← Real.exp_add]
      rw [show ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x)
          + ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x)
        = (r - σ ^ 2 / 2) * Δ * 2 + σ * Real.sqrt Δ * 2 * x from by ring]
      exact Real.exp_add _ _
    have hsq2 : Real.exp ((r - σ ^ 2 / 2) * Δ) ^ 2 = Real.exp ((r - σ ^ 2 / 2) * Δ * 2) := by
      conv_lhs => rw [pow_two, ← Real.exp_add]
      rw [show ((r - σ ^ 2 / 2) * Δ) + ((r - σ ^ 2 / 2) * Δ)
        = (r - σ ^ 2 / 2) * Δ * 2 from by ring]
    rw [mul_pow, mul_pow, hsq, hsq2]
    ring
  have hsquare (A : ℝ) : (S * Real.exp A) ^ 2 = S ^ 2 * Real.exp (A * 2) := by
    conv_lhs => rw [mul_pow, pow_two, pow_two, ← Real.exp_add]
    rw [show A + A = A * 2 from by ring, ← pow_two]
  rw [show (fun ω : Ω ↦ bsTerminal S r σ Δ (Z ω) ^ 2)
        = (fun z : ℝ ↦ bsTerminal S r σ Δ z ^ 2) ∘ Z from rfl,
    hZ.integral_comp hmeas2,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    show (fun x : ℝ ↦ gaussianPDFReal 0 1 x • bsTerminal S r σ Δ x ^ 2)
        = fun x : ℝ ↦ (S * Real.exp ((r - σ ^ 2 / 2) * Δ)) ^ 2
            * (Real.exp ((σ * Real.sqrt Δ * 2) * x) * gaussianPDFReal 0 1 x) from
      funext fun x ↦ by rw [smul_eq_mul]; exact hsplit2int x,
    integral_const_mul, integral_exp_mul_gaussianPDFReal_univ,
    hsquare ((r - σ ^ 2 / 2) * Δ), mul_assoc,
    ← Real.exp_add, hkey2]
  rw [bsTerminal_mean_eq hZ hΔ, hsquare (r * Δ)]
  have hexp : r * Δ * 2 = 2 * r * Δ := by ring
  rw [hexp, Real.exp_add]
  ring

/-! ### The Euler step against the exact step -/

omit [IsProbabilityMeasure Q] in
/-- **The Euler step's mean underestimates the exact GBM step's mean.** The one-step
Euler–Maruyama terminal has mean `S₀(1 + rΔ)` — the linearization of the exact step's mean
`𝔼[S_Δ] = S₀e^{rΔ}` — so it underestimates it for a nonnegative spot and step. (The measure
`Q` carries the standard-normal law of `Z`, so it is a probability measure.) -/
theorem eulerGbmStep_mean_le_exact (hZ : HasLaw Z (gaussianReal 0 1) Q) (hS : 0 ≤ S)
    (hΔ : 0 ≤ Δ) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q
      ≤ ∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q := by
  rw [eulerGbmStep_mean_eq hZ, bsTerminal_mean_eq hZ hΔ]
  have h1 : 1 + r * Δ ≤ Real.exp (r * Δ) := by linarith [Real.add_one_le_exp (r * Δ)]
  exact mul_le_mul_of_nonneg_left h1 hS

omit [IsProbabilityMeasure Q] in
/-- **The Euler step's variance underestimates the exact GBM step's variance** for a
nonnegative rate times step, in the second-moment form `𝔼[X²] − 𝔼[X]²`: the Euler step's
variance `σ²S₀²Δ` is at most the exact step's `S₀²e^{2rΔ}(e^{σ²Δ} − 1)`, since
`σ²Δ ≤ e^{σ²Δ} − 1` and `1 ≤ e^{2rΔ}`. (The measure `Q` carries the standard-normal law of
`Z`, so it is a probability measure.) -/
theorem eulerGbmStep_variance_le_exact (hZ : HasLaw Z (gaussianReal 0 1) Q) (hrΔ : 0 ≤ r * Δ)
    (hΔ : 0 ≤ Δ) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q) ^ 2
      ≤ ∫ ω, bsTerminal S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q) ^ 2 := by
  rw [eulerGbmStep_variance_eq hZ hΔ, bsTerminal_variance_eq hZ hΔ]
  have h1 : σ ^ 2 * Δ ≤ Real.exp (σ ^ 2 * Δ) - 1 := by
    have := Real.add_one_le_exp (σ ^ 2 * Δ)
    linarith
  have h2 : (1 : ℝ) ≤ Real.exp (2 * r * Δ) := by
    have := Real.add_one_le_exp (2 * r * Δ)
    linarith
  calc σ ^ 2 * S ^ 2 * Δ
      = S ^ 2 * (σ ^ 2 * Δ) := by ring
    _ ≤ S ^ 2 * (Real.exp (σ ^ 2 * Δ) - 1) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg S)
    _ ≤ S ^ 2 * Real.exp (2 * r * Δ) * (Real.exp (σ ^ 2 * Δ) - 1) := by
      have hstep : S ^ 2 ≤ S ^ 2 * Real.exp (2 * r * Δ) := by
        have h1' := mul_le_mul_of_nonneg_left h2 (sq_nonneg S)
        rwa [mul_one] at h1'
      exact mul_le_mul_of_nonneg_right hstep
        (by linarith [mul_nonneg (sq_nonneg σ) hΔ])

end MathFin
