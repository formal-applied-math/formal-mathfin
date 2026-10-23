/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.Problem
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded logarithmic put-payoff difference quotients

The log-payoff is globally 1-Lipschitz, even though the stock multiplier is
unbounded. This supplies a constant dominating function for stopped slopes.

## Result

Public entry points include `putPayoff_sub_bounds`, `putPayoff_norm_sub_le`,
`putPayoff_hasDerivAt_neg`, `discountedPutSlope`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology

theorem putPayoff_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ putPayoff x-putPayoff y ∧ putPayoff x-putPayoff y ≤ y-x := by
  by_cases hy : y ≤ 0
  · rw [putPayoff_of_nonpos (hxy.trans hy),putPayoff_of_nonpos hy]
    have he : Real.exp x = Real.exp y*Real.exp (x-y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexy := Real.exp_le_exp.mpr hxy
    have hlin := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
    have hb := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hy) (sub_nonneg.mpr hxy)
    constructor
    · linarith
    · rw [← he] at hlin
      nlinarith
  · have hy0 : 0 < y := lt_of_not_ge hy
    have hpy : putPayoff y = 0 := by
      unfold putPayoff
      rw [max_eq_right (sub_nonpos.mpr (Real.one_le_exp_iff.mpr hy0.le))]
    rw [hpy,sub_zero]
    refine ⟨putPayoff_nonneg x,?_⟩
    by_cases hx : x ≤ 0
    · rw [putPayoff_of_nonpos hx]
      linarith [Real.add_one_le_exp x]
    · unfold putPayoff
      rw [max_eq_right (sub_nonpos.mpr (Real.one_le_exp_iff.mpr (le_of_not_ge hx)))]
      linarith

theorem putPayoff_norm_sub_le (x y : ℝ) : ‖putPayoff x-putPayoff y‖ ≤ ‖x-y‖ := by
  rcases le_total x y with hxy | hyx
  · obtain ⟨hn,hb⟩ := putPayoff_sub_bounds hxy
    rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  · obtain ⟨hn,hb⟩ := putPayoff_sub_bounds hyx
    rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : putPayoff x-putPayoff y ≤ 0),
      Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith

theorem putPayoff_hasDerivAt_neg {b : ℝ} (hb : b < 0) : HasDerivAt putPayoff (-Real.exp b) b := by
  have hd := (Real.hasDerivAt_exp b).const_sub 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hb] with x hx
  exact putPayoff_of_nonpos (show x < 0 from hx).le

/-- The difference quotient
`exp (-k*t) * (putPayoff (x+D) - putPayoff (b+D)) / (x-b)`: a discounted log-payoff slope
between `b` and `x`, both displaced by `D`. -/
noncomputable def discountedPutSlope (k b x t D : ℝ) : ℝ :=
  (Real.exp (-k*t)*(putPayoff (x+D)-putPayoff (b+D)))/(x-b)

theorem discountedPutSlope_bound {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) (b x D : ℝ) :
    ‖discountedPutSlope k b x t D‖ ≤ 1 := by
  by_cases hx : x = b
  · simp only [discountedPutSlope,hx,sub_self,mul_zero,div_zero,norm_zero,zero_le_one]
  · have hd : 0 < ‖x-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have hp := putPayoff_norm_sub_le (x+D) (b+D)
    have he : Real.exp (-k*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hnorm : ‖Real.exp (-k*t)‖ = Real.exp (-k*t) := Real.norm_of_nonneg (Real.exp_pos _).le
    unfold discountedPutSlope
    rw [norm_div,norm_mul,hnorm]
    apply (div_le_one hd).mpr
    have hdiff : x+D-(b+D) = x-b := by ring
    rw [hdiff] at hp
    exact (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (x-b)))

theorem discountedPutSlope_eq_exp {k b x t D : ℝ} (hx : x + D ≤ 0) (hb : b + D ≤ 0) :
    discountedPutSlope k b x t D = -Real.exp (-k*t+D)*slope Real.exp b x := by
  rw [discountedPutSlope,putPayoff_of_nonpos hx,putPayoff_of_nonpos hb]
  simp only [Real.exp_add,slope,vsub_eq_sub,smul_eq_mul,div_eq_mul_inv]
  ring

theorem discountedPutSlope_tendsto {b k : ℝ} (hb : b < 0) {t D : ℝ → ℝ}
    (ht : Tendsto t (𝓝 b) (𝓝 0)) (hD : Tendsto D (𝓝 b) (𝓝 0)) :
    Tendsto (fun x => discountedPutSlope k b x (t x) (D x)) (𝓝[>] b) (𝓝 (-Real.exp b)) := by
  have hxd : Tendsto (fun x => x+D x) (𝓝 b) (𝓝 b) := by
    simpa only [id_eq,add_zero] using tendsto_id.add hD
  have hbd : Tendsto (fun x => b+D x) (𝓝 b) (𝓝 b) := by
    simpa only [add_zero] using tendsto_const_nhds.add hD
  have he : (fun x => discountedPutSlope k b x (t x) (D x)) =ᶠ[𝓝[>] b]
      (fun x => -Real.exp (-k*t x+D x)*slope Real.exp b x) := by
    filter_upwards [nhdsWithin_le_nhds (hxd.eventually (Iio_mem_nhds hb)),
      nhdsWithin_le_nhds (hbd.eventually (Iio_mem_nhds hb))] with x hx hb'
    exact discountedPutSlope_eq_exp (show x+D x < 0 from hx).le (show b+D x < 0 from hb').le
  have hf : Tendsto (fun x => -Real.exp (-k*t x+D x)) (𝓝 b) (𝓝 (-1)) := by
    have he : Tendsto (fun x => -k*t x+D x) (𝓝 b) (𝓝 0) := by
      simpa only [mul_zero,add_zero] using (ht.const_mul (-k)).add hD
    simpa only [Function.comp_def,Real.exp_zero] using ((Real.continuous_exp.tendsto 0).comp he).neg
  have hs := (Real.hasDerivAt_exp b).tendsto_slope.mono_left (nhdsGT_le_nhdsNE b)
  have hp := (hf.mono_left nhdsWithin_le_nhds).mul hs
  simp only [neg_one_mul] at hp
  exact hp.congr' he.symm

end MathFin.BlackScholes.AmericanPut.Stopping
