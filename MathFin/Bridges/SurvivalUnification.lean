/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Actuarial.Mortality
public import MathFin.Actuarial.SurvivalModel
public import MathFin.FixedIncome.HazardCurve
public import MathFin.FixedIncome.DefaultDensity

/-!
# Bridge: actuarial survival ≡ reduced-form credit survival

The actuarial survival function built from a force of mortality `μ` (`survivalFromForce`,
`Actuarial/Mortality.lean`) and the reduced-form credit survival curve built from a hazard rate `h`
(`hazardSurvival`, `FixedIncome/HazardCurve.lean`) are both *defined* as
`survivalFromIntensity = exp(−∫₀ᵗ ·)` (`Foundations/ExponentialDiscount.lean`), so
`survivalFromForce_eq_hazardSurvival` is `rfl`: it records that the two names denote one function,
not a theorem about either.

The probabilistic content is the link to a random lifetime. The survival model of
`Actuarial/SurvivalModel.lean` starts from an age-at-death random variable `X` and its survival
function `S_X(t) = P(X > t)`. Take for `X` a random time `τ` whose law has the hazard `h`, in the
form the credit layer uses: `P(τ ≤ a) = 1 − exp(−∫₀ᵃ h)` for `a ≥ 0` (the hypothesis of
`DefaultDensity.map_eq_withDensity`), with `h` continuous and nonnegative. Then

* `survivalFunction_eq_hazardSurvival`: `S_τ(t) = hazardSurvival h t` for `t ≥ 0`;
* `survive_eq_exp_neg_integral`: `ₜpₓ = P(τ > x + t ∣ τ > x) = exp(−∫ₓ^{x+t} h)` for `x, t ≥ 0`;
* `hasDerivAt_survivalFunction`: `S_τ' = −h · S_τ` on `t > 0`, so `h` is the force of mortality
  `−S_τ'/S_τ` of the lifetime;
* `survive_coxDefaultTime`: the hypotheses hold for the Cox default time of `FixedIncome/Cox.lean`
  (a unit-exponential clock inverted through `∫₀ᵗ h`, for `h` continuous and positive with
  `∫₀ᵗ h → ∞`), so they are satisfiable.

The single exponential holds for a deterministic intensity only. With a stochastic intensity `Λ`
the survival probability is the mixture `E[exp(−Λ_t)]` (`Cox.cox_mixing_survival`), which is not
`exp(−E[Λ_t])` in general; that case is not covered here.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology

/-- **The two survival curves are one definition.** The actuarial `survivalFromForce` and the
credit `hazardSurvival` both unfold to `survivalFromIntensity`, so this is `rfl`: it identifies two
names, and it says nothing about a random lifetime (see `survivalFunction_eq_hazardSurvival`). -/
theorem survivalFromForce_eq_hazardSurvival (μ : ℝ → ℝ) (t : ℝ) :
    survivalFromForce μ t = hazardSurvival μ t := rfl

/-- **Gompertz law as a credit hazard curve.** A Gompertz-shaped intensity
`h(u) = B · e^{c u}` has cumulative hazard `(B/c) · (e^{c t} − 1)` — the actuarial
Gompertz cumulative force, reused as a reduced-form credit term structure. -/
theorem gompertz_cumHazard (B c t : ℝ) (hc : c ≠ 0) :
    cumHazard (fun u ↦ B * Real.exp (c * u)) t = (B / c) * (Real.exp (c * t) - 1) := by
  unfold cumHazard
  exact gompertz_cumulative_force B c t hc

/-! ### A lifetime with a hazard rate -/

section Lifetime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : ℝ → ℝ} {τ : Ω → ℝ}

/-- **The actuarial survival function of a lifetime with hazard `h` is the credit survival
curve**: if `P(τ ≤ a) = 1 − exp(−∫₀ᵃ h)` for `a ≥ 0`, with `h ≥ 0`, then
`S_τ(t) = P(τ > t) = hazardSurvival h t` for `t ≥ 0`. -/
theorem survivalFunction_eq_hazardSurvival (hnn : ∀ s, 0 ≤ h s) (hτ : Measurable τ)
    (hcdf : ∀ a, 0 ≤ a → P {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a)) {t : ℝ}
    (ht : 0 ≤ t) : SurvivalModel.survivalFunction P τ t = hazardSurvival h t := by
  have hQ : hazardSurvival h t ≤ 1 := by
    show Real.exp (-∫ u in (0 : ℝ)..t, h u) ≤ 1
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (intervalIntegral.integral_nonneg ht fun s _ ↦ hnn s))
  have hcompl : SurvivalModel.alive τ t = {ω | τ ω ≤ t}ᶜ := by
    ext ω
    simp [SurvivalModel.alive]
  rw [SurvivalModel.survivalFunction, hcompl,
    measure_compl (measurableSet_le hτ measurable_const) (measure_ne_top _ _), measure_univ,
    hcdf t ht, ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.ofReal_le_one.2 hQ),
    ENNReal.toReal_ofReal (hazardSurvival_pos h t).le]

/-- **The actuarial `ₜpₓ` of a lifetime with hazard `h`**: under the hypotheses of
`survivalFunction_eq_hazardSurvival` with `h` continuous, a life aged `x ≥ 0` survives a further
`t ≥ 0` years with probability `ₜpₓ = exp(−∫ₓ^{x+t} h)`. -/
theorem survive_eq_exp_neg_integral (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) (hτ : Measurable τ)
    (hcdf : ∀ a, 0 ≤ a → P {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a)) {x t : ℝ}
    (hx : 0 ≤ x) (ht : 0 ≤ t) :
    SurvivalModel.survive P τ t x = Real.exp (-∫ s in x..x + t, h s) := by
  rw [SurvivalModel.survive_eq_survivalFunction_ratio hτ x ht,
    survivalFunction_eq_hazardSurvival hnn hτ hcdf (add_nonneg hx ht),
    survivalFunction_eq_hazardSurvival hnn hτ hcdf hx]
  simp only [hazardSurvival, survivalFromIntensity, cumulativeIntensity]
  rw [← Real.exp_sub]
  congr 1
  rw [← intervalIntegral.integral_interval_sub_left (hh.intervalIntegrable 0 (x + t))
    (hh.intervalIntegrable 0 x)]
  ring

/-- **The hazard is the force of mortality of the lifetime**: under the hypotheses of
`survivalFunction_eq_hazardSurvival` with `h` continuous, `S_τ' = −h · S_τ` at every `t > 0`,
that is `h(t) = −S_τ'(t) / S_τ(t)`. -/
theorem hasDerivAt_survivalFunction (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) (hτ : Measurable τ)
    (hcdf : ∀ a, 0 ≤ a → P {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a)) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (SurvivalModel.survivalFunction P τ)
      (-(h t * SurvivalModel.survivalFunction P τ t)) t := by
  have hev : SurvivalModel.survivalFunction P τ =ᶠ[𝓝 t] hazardSurvival h :=
    eventually_of_mem (Ioi_mem_nhds ht) fun s hs ↦
      survivalFunction_eq_hazardSurvival hnn hτ hcdf (le_of_lt hs)
  rw [survivalFunction_eq_hazardSurvival hnn hτ hcdf ht.le]
  exact (DefaultDensity.hasDerivAt_hazardSurvival hh.locallyIntegrable
    hh.continuousAt).congr_of_eventuallyEq hev

/-- **The Cox default time is a lifetime with hazard `h`**: for `h` continuous and positive with
`∫₀ᵗ h → ∞`, and `τ` the unit-exponential clock `ξ` inverted through `∫₀ᵗ h`
(`Cox.coxDefaultTime`), `ₜpₓ = exp(−∫ₓ^{x+t} h)` for `x, t ≥ 0`. -/
theorem survive_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Tendsto (cumHazard h) atTop atTop) {ξ : Ω → ℝ} (hξmeas : Measurable ξ)
    (hξlaw : P.map ξ = expMeasure 1) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    SurvivalModel.survive P (Cox.coxDefaultTime h ξ) t x = Real.exp (-∫ s in x..x + t, h s) :=
  survive_eq_exp_neg_integral hh (fun s ↦ (hpos s).le)
    (Cox.measurable_coxDefaultTime hh hpos hξmeas)
    (fun _ ha ↦ Cox.cox_cdf_timeVarying hh hpos hdiv hξmeas hξlaw ha) hx ht

end Lifetime

end MathFin
