/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.FixedIncome.VasicekBondPrice
public import MathFin.FixedIncome.VasicekSDEGaussian
public import MathFin.Foundations.WienerIntegralFiltration

/-!
# The Vasicek bond price at a time `t > 0`

`FixedIncome/VasicekBondPrice.lean` prices the zero-coupon bond at time `0`,
`P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = A(T)·exp(−B(T) r₀)`. This file prices it at a later time `t`,
given the information `𝓕_t = σ(B_s : s ≤ t)` of the driving Brownian motion:

  `𝔼[exp(−∫₀ᵀ r_s ds) | 𝓕_t] = exp(−∫₀ᵗ r_s ds)·A(T − t)·exp(−B(T − t)·r_t)`   almost surely,

so the price at `t` of one unit paid at `T`, the conditional mean of the discount over `[t, T]`, is
`A(T − t)·exp(−B(T − t)·r_t)`, with `A`, `B` the coefficients of the time-`0` price at the remaining
maturity `T − t`: the Vasicek model is time-homogeneous, so the price depends on `t` only through
`r_t` and `T − t`.

The integrated rate is carried in its Wiener representation (`vasicekIntegratedRate`), so
`∫₀ᵀ r` and `∫₀ᵗ r` are Wiener integrals over different horizons. Given the past
(`Foundations/WienerIntegralFiltration.lean`, `condExp_exp_wienerIntegralLp`), the integrated
kernel `g_T(u) = (1 − e^{−κ(T−u)})/κ` of the horizon `T`, restricted to `(0, t]`, is
`g_t + B(T − t)·e^{−κ(t−u)}`: the past part of `∫₀ᵀ r` depends on the past through `∫₀ᵗ r` and the
Wiener integral `∫₀ᵗ e^{−κ(t−u)} dB_u`, which is `(r_t − mean)/σ`; and the remainder is an
independent centred Gaussian of variance `∫_t^T g_T² = V(T − t)`. The bridge to
`bondPrice` is `Contracts/Models/VasicekBond.lean`.

## Main results

* `kernelRestrict_vasicekIntegratedKernelLp` — `g_T|_{(0,t]} = g_t + B(T − t)·e^{−κ(t−·)}`.
* `integral_sq_vasicekIntegratedKernelLp_Ioc` — `∫_t^T g_T² = V(T − t)`.
* `vasicekIntegratedMean_sub` — the mean identity `M(t) − M(T) = −θ(τ − B(τ)) − B(τ) m_t`.
* `vasicekBondPrice_condExp` — the conditional discount factor, affine in `r_t`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma vasicekIntegratedKernelLp_coeFn {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    vasicekIntegratedKernelLp hκ T =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)]
      vasicekIntegratedKernel κ T :=
  (vasicekIntegratedKernel_memLp hκ T).coeFn_toLp

lemma vasicekKernelLp_coeFn (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ≥0) :
    vasicekKernelLp κ hκ T =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] vasicekKernel κ T :=
  (vasicekKernel_memLp κ hκ T).coeFn_toLp

/-- **The horizon-`T` kernel seen from time `t`.** On `(0, t]`, the integrated kernel
`g_T(u) = (1 − e^{−κ(T−u)})/κ` is `g_t(u) + B(T − t)·e^{−κ(t−u)}`, since
`e^{−κ(T−u)} = e^{−κ(t−u)} e^{−κ(T−t)}`. -/
lemma kernelRestrict_vasicekIntegratedKernelLp {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    kernelRestrict htT (vasicekIntegratedKernelLp hκ T)
      = vasicekIntegratedKernelLp hκ t
        + vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • vasicekKernelLp κ hκ.le t := by
  refine Lp.ext ?_
  filter_upwards [kernelRestrict_coeFn htT (vasicekIntegratedKernelLp hκ T),
    (vasicekIntegratedKernelLp_coeFn hκ T).filter_mono (ae_mono (volume_restrict_Ioc_mono htT)),
    Lp.coeFn_add (vasicekIntegratedKernelLp hκ t)
      (vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • vasicekKernelLp κ hκ.le t),
    Lp.coeFn_smul (vasicekBondB κ ((T - t : ℝ≥0) : ℝ)) (vasicekKernelLp κ hκ.le t),
    vasicekIntegratedKernelLp_coeFn hκ t, vasicekKernelLp_coeFn κ hκ.le t]
    with u h1 h2 h3 h4 h5 h6
  rw [h3, Pi.add_apply, h1, h4, Pi.smul_apply, h5, h6, h2]
  simp only [vasicekIntegratedKernel, vasicekKernel, vasicekBondB, smul_eq_mul, NNReal.coe_sub htT]
  have : Real.exp (-(κ * ((T : ℝ) - u)))
      = Real.exp (-(κ * ((t : ℝ) - u))) * Real.exp (-(κ * ((T : ℝ) - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  field_simp
  ring

/-- **The variance of the remainder.** `∫_t^T g_T(u)² du = V(T − t)`, the variance function at the
remaining maturity. -/
lemma integral_sq_vasicekIntegratedKernelLp_Ioc {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    ∫ s in Set.Ioc (t : ℝ) T, (vasicekIntegratedKernelLp hκ T s) ^ 2
      = vasicekBondV κ ((T - t : ℝ≥0) : ℝ) := by
  have ht : (t : ℝ) ≤ T := NNReal.coe_le_coe.2 htT
  rw [integral_congr_ae (g := fun s ↦ (vasicekIntegratedKernel κ T s) ^ 2)
    (((vasicekIntegratedKernelLp_coeFn hκ T).filter_mono (ae_mono
      (Measure.restrict_mono (Set.Ioc_subset_Ioc_left t.coe_nonneg) le_rfl))).mono
        fun u hu ↦ congrArg (· ^ 2) hu),
    ← intervalIntegral.integral_of_le ht,
    integral_vasicekIntegratedKernel_sq_eq_sub κ T t T hκ.ne']
  simp only [vasicekIntegratedKernelSqAntideriv, vasicekBondV, NNReal.coe_sub htT, sub_self,
    mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- The change in the integrated mean from `t` to `T`: the price coefficient at the remaining
maturity, less the mean sensitivity `B(T − t)` to the short-rate mean at `t`. -/
lemma vasicekIntegratedMean_sub (r₀ θ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) {t T : ℝ≥0} (htT : t ≤ T) :
    vasicekIntegratedMean r₀ θ κ t - vasicekIntegratedMean r₀ θ κ T
      = -(θ * (((T - t : ℝ≥0) : ℝ) - vasicekBondB κ ((T - t : ℝ≥0) : ℝ)))
        - vasicekBondB κ ((T - t : ℝ≥0) : ℝ) * vasicekSDEMean r₀ θ κ t := by
  have hT : Real.exp (-(κ * (T : ℝ)))
      = Real.exp (-(κ * (t : ℝ))) * Real.exp (-(κ * ((T : ℝ) - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [vasicekIntegratedMean, vasicekBondB, vasicekSDEMean, NNReal.coe_sub htT, hT]
  field_simp
  ring

/-- **The Vasicek bond price at time `t`.** Given the information `𝓕_t` of the driving Brownian
motion, the discount factor `exp(−∫₀ᵀ r)` along the Vasicek integrated rate has conditional mean

  `𝔼[exp(−∫₀ᵀ r) | 𝓕_t] = exp(−∫₀ᵗ r)·A(T − t)·exp(−B(T − t)·r_t)`

almost surely, where `r_t = vasicekSDEMean + σ∫₀ᵗ e^{−κ(t−u)} dB_u` is the short rate in its Wiener
representation (`vasicekShortRate_hasLaw_gaussian`) and `A`, `B` are the coefficients of the
time-`0` price (`vasicekBondPrice_affine`), at the remaining maturity. Dividing by the discount
factor `exp(−∫₀ᵗ r)` known at `t`, the price at `t` of one unit paid at `T` is
`A(T − t)·exp(−B(T − t)·r_t)`. The measure is read as the pricing measure. -/
theorem vasicekBondPrice_condExp [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    μ[fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ T ω)
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ t ω)
        * (vasicekBondA θ σ κ ((T - t : ℝ≥0) : ℝ)
          * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
            * (vasicekSDEMean r₀ θ κ t + vasicekDiffusionTerm hB κ σ hκ.le t ω)))) := by
  have hfun : (fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ T ω))
      = fun ω ↦ Real.exp (-vasicekIntegratedMean r₀ θ κ T
          + 0 * wienerIntegralLp B hB t 0 ω
          - σ * wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω) := by
    funext ω
    simp only [vasicekIntegratedRate]
    congr 1
    ring
  rw [hfun]
  refine (condExp_exp_wienerIntegralLp hB hBm htT 0 (vasicekIntegratedKernelLp hκ T) _ 0 σ).trans ?_
  rw [kernelRestrict_vasicekIntegratedKernelLp hκ htT, map_add, map_smul,
    integral_sq_vasicekIntegratedKernelLp_Ioc hκ htT]
  filter_upwards [Lp.coeFn_add (wienerIntegralLp B hB t (vasicekIntegratedKernelLp hκ t))
      (vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • wienerIntegralLp B hB t (vasicekKernelLp κ hκ.le t)),
    Lp.coeFn_smul (vasicekBondB κ ((T - t : ℝ≥0) : ℝ))
      (wienerIntegralLp B hB t (vasicekKernelLp κ hκ.le t))] with ω h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  simp only [vasicekBondA, vasicekDiffusionTerm, vasicekIntegratedRate, ← Real.exp_add]
  congr 1
  have := vasicekIntegratedMean_sub r₀ θ hκ.ne' htT
  linear_combination this

end MathFin
