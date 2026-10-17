/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.GaussianGirsanov
public import MathFin.FixedIncome.VasicekSDEGaussian

/-!
# Vasicek short rate: real-world and risk-neutral measures (constant market price of risk)

With a constant market price of risk `λ`, the Vasicek short rate has real-world dynamics
`dr = κ(θ − r)dt + σ dz` and risk-neutral dynamics `dr = [κ(θ − r) − λσ]dt + σ dz̃`, i.e. the
risk-neutral long-run level is `θ − λσ/κ`. The terminal means differ by `λσ·B(T)` with
`B(T) = (1 − e^{−κT})/κ`.

## Main results

* `vasicekSDEMean_physical_eq_riskNeutral`: the real-world mean equals the risk-neutral mean
  plus `λσ·B(T)`; the analogue of `bsTerminal_physical_eq_riskNeutral`.
* `vasicekShortRate_physical_eq_riskNeutral`: a static Girsanov (Esscher) tilt of the
  real-world measure under which the same terminal short rate `r_T` has the risk-neutral
  Gaussian law `N(mean_θ − λσ·B(T), var)`.

The tilt is on the normalised terminal driver of `r_T` alone, so it is a terminal-law
statement, not the pathwise Girsanov change of the whole Brownian path.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open WienerIntegralL2

/-- **Real-world vs. risk-neutral Vasicek mean.** Replacing the long-run level `θ` by the
risk-neutral level `θ − lamσ/κ` lowers the terminal mean by `lamσ·(1 − e^{−κT})/κ`. -/
theorem vasicekSDEMean_physical_eq_riskNeutral (r₀ θ κ σ lam T : ℝ) (hκ : κ ≠ 0) :
    vasicekSDEMean r₀ θ κ T
      = vasicekSDEMean r₀ (θ - lam * σ / κ) κ T
        + lam * σ * ((1 - Real.exp (-(κ * T))) / κ) := by
  unfold vasicekSDEMean
  field_simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Vasicek terminal law under the risk-neutral measure, from the real-world one.**
Let `r_T = mean_θ + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` be the real-world terminal short rate, and
`Z = (∫₀ᵀ e^{−κ(T−s)} dB_s)/√v` its standard-normal driver (`v = (1 − e^{−2κT})/(2κ)`).
Under the Esscher tilt `Q = μ.withDensity(exp(cZ − c²/2))` with `c = −lam·B(T)/√v`, the same
`r_T` has law `N(mean_θ − lamσ·B(T), var)`: the mean of the model with long-run level
`θ − lamσ/κ`, i.e. the risk-neutral law under market price of risk `lam`. -/
theorem vasicekShortRate_physical_eq_riskNeutral (hB : IsPreBrownianReal B μ)
    (r₀ θ σ lam : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < T) :
    let I : Ω → ℝ := fun ω ↦ wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω
    let s : ℝ := Real.sqrt (vasicekSDEVariance 1 κ T)
    let c : ℝ := -(lam * ((1 - Real.exp (-(κ * T))) / κ)) / s
    HasLaw (fun ω ↦ vasicekSDEMean r₀ θ κ T + σ * I ω)
      (gaussianReal (vasicekSDEMean r₀ θ κ T - lam * σ * ((1 - Real.exp (-(κ * T))) / κ))
        (vasicekSDEVariance σ κ T).toNNReal)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (c * (I ω / s) - c ^ 2 / 2))) := by
  intro I s c
  -- `I ~ N(0, v)`: the σ = 1, zero-mean instance of the derived terminal law.
  have hI : HasLaw I (gaussianReal 0 (vasicekSDEVariance 1 κ T).toNNReal) μ := by
    have h := vasicekShortRate_hasLaw_gaussian hB 0 0 1 hκ T
    simp only [vasicekSDEMean, zero_mul, add_zero, one_mul, zero_add] at h
    exact h
  have hv : 0 < vasicekSDEVariance 1 κ T := by
    unfold vasicekSDEVariance
    have : Real.exp (-(2 * κ * T)) < 1 :=
      Real.exp_lt_one_iff.mpr (by have : (0 : ℝ) < T := hT; nlinarith)
    exact div_pos (by linarith) (by linarith)
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hss : s ^ 2 = vasicekSDEVariance 1 κ T := Real.sq_sqrt hv.le
  have hImeas : Measurable I := (Lp.stronglyMeasurable _).measurable
  -- `Z = I/s ~ N(0, 1)`.
  have hZ : HasLaw (fun ω ↦ I ω / s) (gaussianReal 0 1) μ := by
    have h := gaussianReal_const_mul hI s⁻¹
    convert h using 2
    · rw [div_eq_inv_mul]
    · simp
    · ext
      simp [← hss, hs.ne', max_eq_left (sq_nonneg s)]
  have hZQ := hasLaw_esscher_tilt c (hImeas.div_const s) hZ
  have h := gaussianReal_const_add (gaussianReal_const_mul hZQ (σ * s)) (vasicekSDEMean r₀ θ κ T)
  convert h using 2
  · field_simp
  · simp only [c]; field_simp; ring
  · ext
    have hvσ : 0 ≤ vasicekSDEVariance σ κ T := by
      unfold vasicekSDEVariance
      have : Real.exp (-(2 * κ * T)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have : (0 : ℝ) ≤ T := T.2; nlinarith)
      exact div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith)) (by linarith)
    simp only [Real.coe_toNNReal _ hvσ, NNReal.coe_mk, mul_one]
    rw [mul_pow, hss]
    unfold vasicekSDEVariance
    ring

end MathFin
