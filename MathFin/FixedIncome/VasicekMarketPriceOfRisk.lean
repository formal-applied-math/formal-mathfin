/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.GaussianGirsanov
public import MathFin.FixedIncome.VasicekBondPrice
public import MathFin.FixedIncome.VasicekSDEGaussian

/-!
# Vasicek short rate: real-world vs. risk-neutral terminal law (constant market price of risk)

Textbook background (not formalized here): with a constant market price of risk `λ`, the
Vasicek short rate has real-world dynamics `dr = κ(θ − r)dt + σ dz` and risk-neutral dynamics
`dr = [κ(θ − r) − λσ]dt + σ dz̃`, i.e. the risk-neutral long-run level is `θ − λσ/κ`, and the
terminal means differ by `λσ·B(T)` with `B(T) = (1 − e^{−κT})/κ`. Neither SDE nor either
measure is constructed below.

## Main results

* `vasicekSDEMean_physical_eq_riskNeutral`: an algebraic identity of closed forms
  (`κ ≠ 0`): `vasicekSDEMean` at level `θ` equals `vasicekSDEMean` at the risk-neutral level
  `θ − λσ/κ` plus `λσ·B(T)`; the analogue of `bsTerminal_physical_eq_riskNeutral`.
* `vasicekShortRate_hasLaw_esscherTilt`: a static Girsanov (Esscher) tilt of the
  real-world measure under which the same terminal short rate `r_T` has the Gaussian law
  `N(mean_θ − λσ·B(T), var)` (`κ > 0`, `T > 0`), the law that the risk-neutral measure
  assigns it in the textbook model (not proved here).

The tilt is on the normalised terminal driver of `r_T` alone, so it is a terminal-law
statement, not the pathwise Girsanov change of the whole Brownian path; the tilted measure
is not the risk-neutral measure.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open WienerIntegralL2

/-- **Real-world vs. risk-neutral Vasicek mean.** An algebraic identity of the closed form
`vasicekSDEMean`, for `κ ≠ 0`: replacing the long-run level `θ` by the risk-neutral level
`θ − lamσ/κ` changes the terminal mean by `−lamσ·(1 − e^{−κT})/κ`. -/
theorem vasicekSDEMean_physical_eq_riskNeutral (r₀ θ κ σ lam T : ℝ) (hκ : κ ≠ 0) :
    vasicekSDEMean r₀ θ κ T
      = vasicekSDEMean r₀ (θ - lam * σ / κ) κ T
        + lam * σ * vasicekBondB κ T := by
  unfold vasicekSDEMean vasicekBondB
  field_simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Vasicek terminal law with the risk-neutral mean, under a static Esscher tilt.**
For `κ > 0` and `T > 0`, let `r_T = mean_θ + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` be the real-world
terminal short rate, and
`Z = (∫₀ᵀ e^{−κ(T−s)} dB_s)/√v` its standard-normal driver (`v = (1 − e^{−2κT})/(2κ)`).
Under the Esscher tilt `Q = μ.withDensity(exp(cZ − c²/2))` with `c = −lam·B(T)/√v`, the same
`r_T` has law `N(mean_θ − lamσ·B(T), var)`: the mean of the model with long-run level
`θ − lamσ/κ`, i.e. the law the risk-neutral measure assigns to `r_T` under market price of
risk `lam` (a textbook fact, not proved here). `Q` is *not* the risk-neutral measure: it is a
`T`-dependent tilt of `r_T`'s own normalised driver, so it reproduces the terminal marginal
only — under `Q` the rest of the path (e.g. `∫₀ᵀ r_s ds`) does not have its risk-neutral
law, and `Q` does not price discounted payoffs. The market-price-of-risk Girsanov density
`exp(−lam·B_T − lam²T/2)` is a different measure with the same `r_T`-marginal; that
identification needs the joint Gaussian law of `(B_T, ∫₀ᵀ e^{−κ(T−s)} dB_s)` and is not
proved. As in `vasicekShortRate_hasLaw_gaussian`, `r_T` is the Wiener representation of the
OU solution; that it solves the Vasicek SDE is cited, not proved. -/
theorem vasicekShortRate_hasLaw_esscherTilt (hB : IsPreBrownianReal B μ)
    (r₀ θ σ lam : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < T) :
    let I : Ω → ℝ := fun ω ↦ wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω
    let s : ℝ := Real.sqrt (vasicekSDEVariance 1 κ T)
    let c : ℝ := -(lam * vasicekBondB κ T) / s
    HasLaw (fun ω ↦ vasicekSDEMean r₀ θ κ T + σ * I ω)
      (gaussianReal (vasicekSDEMean r₀ θ κ T - lam * σ * vasicekBondB κ T)
        (vasicekSDEVariance σ κ T).toNNReal)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (c * (I ω / s) - c ^ 2 / 2))) := by
  intro I s c
  -- `I ~ N(0, v)`: the σ = 1, zero-mean instance of the derived terminal law.
  have hI : HasLaw I (gaussianReal 0 (vasicekSDEVariance 1 κ T).toNNReal) μ := by
    have h := vasicekShortRate_hasLaw_gaussian hB 0 0 1 hκ T
    simp only [vasicekSDEMean, zero_mul, add_zero, one_mul, zero_add] at h
    exact h
  have hv : 0 < vasicekSDEVariance 1 κ T := vasicekSDE_variance_pos 1 κ T hκ hT one_ne_zero
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
  · simp only [c, vasicekBondB]; field_simp; ring
  · ext
    have hvσ : 0 ≤ vasicekSDEVariance σ κ T := vasicekSDEVariance_nonneg σ hκ T.2
    simp only [Real.coe_toNNReal _ hvσ, NNReal.coe_mk, mul_one]
    rw [mul_pow, hss]
    unfold vasicekSDEVariance
    ring

end MathFin
