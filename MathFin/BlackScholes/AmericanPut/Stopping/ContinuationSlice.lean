/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PositiveExerciseBoundary
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Excluding an instantaneous interval of continuation

Positive-time interior PDE regularity and maturity monotonicity give an
elliptic inequality on each continuation slice. A quadratic maximum argument
prevents a whole interval of payoff contact from instantly becoming continuation.
Only price values, not derivatives, are passed to the initial-time limit.

## Result

Public entry points include `canonicalPrice_monotone_time`, `canonicalPrice_time_deriv_nonneg`,
`canonicalIntrinsicPremium`, `canonicalIntrinsicPremium_nonneg`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped Topology ContDiff NNReal

theorem canonicalPrice_monotone_time {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) :
    Monotone (canonicalPrice k h x) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  intro s t hst
  exact value_mono_horizon (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable (by norm_num) hk (Real.exp_pos x).le
    (Real.toNNReal_mono hst)

theorem canonicalPrice_time_deriv_nonneg {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    0 ≤ deriv (canonicalPrice k h x) t := (canonicalPrice_monotone_time hk x).deriv_nonneg

/-- The canonical price above its unclipped payoff: `canonicalPrice k h x t-(1-Real.exp x)`. -/
noncomputable def canonicalIntrinsicPremium (k h x t : ℝ) : ℝ :=
  canonicalPrice k h x t - (1-Real.exp x)

theorem canonicalIntrinsicPremium_nonneg {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    0 ≤ canonicalIntrinsicPremium k h x t :=
  sub_nonneg.mpr ((le_max_left _ _).trans (canonicalPrice_bounds hk x t).1)

theorem canonicalIntrinsicPremium_continuous {k h : ℝ} (hk : 0 ≤ k) :
    Continuous (fun z : ℝ × ℝ => canonicalIntrinsicPremium k h z.1 z.2) :=
  (canonicalPrice_continuous hk).sub (by fun_prop)

theorem canonicalIntrinsicPremium_contDiffAt {k h x t : ℝ} (hk : 0 ≤ k)
    (hz : (x, t) ∈ canonicalContinuationRegion k h) :
    ContDiffAt ℝ 2 (fun y => canonicalIntrinsicPremium k h y t) x := by
  have hp := (canonicalPrice_contDiffAt hk hz).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  exact (hp.comp (f := fun y : ℝ => (y,t)) x (by fun_prop)).sub (by fun_prop)

theorem canonicalIntrinsicPremium_forcing {k h x t : ℝ} (hk : 0 ≤ k)
    (hz : (x, t) ∈ canonicalContinuationRegion k h) :
    k-h*Real.exp x ≤
      deriv (deriv (fun y => canonicalIntrinsicPremium k h y t)) x +
        (k-h-1)*deriv (fun y => canonicalIntrinsicPremium k h y t) x -
        k*canonicalIntrinsicPremium k h x t := by
  have hp : ContDiffAt ℝ 2 (fun y => canonicalPrice k h y t) x :=
    ((canonicalPrice_contDiffAt hk hz).of_le (WithTop.coe_le_coe.mpr le_top)).comp
      (f := fun y : ℝ => (y,t)) x (by fun_prop)
  have hg : ContDiffAt ℝ 2 (fun y : ℝ => 1-Real.exp y) x := by fun_prop
  have hsecond : deriv (deriv (fun y => canonicalIntrinsicPremium k h y t)) x =
      deriv (deriv (fun y => canonicalPrice k h y t)) x + Real.exp x := by
    have he := iteratedDeriv_fun_sub (n := 2) hp hg
    simpa only [canonicalIntrinsicPremium,show (2 : ℕ) = 1+1 from rfl,
      iteratedDeriv_succ,iteratedDeriv_zero,deriv_const_sub',Real.deriv_exp,
      deriv.fun_neg',sub_neg_eq_add] using he
  have hfirst : deriv (fun y => canonicalIntrinsicPremium k h y t) x =
      deriv (fun y => canonicalPrice k h y t) x + Real.exp x := by
    unfold canonicalIntrinsicPremium
    rw [deriv_fun_sub (hp.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    simp only [deriv_const_sub',Real.deriv_exp,sub_neg_eq_add]
  rw [hsecond,hfirst]
  have hpde := canonicalPrice_continuation_pde hk hz
  have htime := canonicalPrice_time_deriv_nonneg (h := h) hk x t
  unfold canonicalIntrinsicPremium
  nlinarith

/-- A nonnegative profile with strictly positive elliptic forcing cannot have
both endpoint values arbitrarily small. The quantitative constants are explicit. -/
theorem no_small_forced_profile {f : ℝ → ℝ} {k α c ρ δ η : ℝ}
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hη : 0 < η)
    (hscale : 2 * η*(1 + |α| * ρ) < δ)
    (hf : ContinuousOn f (Icc (c - ρ) (c + ρ)))
    (hfs : ∀ x ∈ Ioo (c - ρ) (c + ρ), ContDiffAt ℝ 2 f x)
    (hn : ∀ x ∈ Icc (c - ρ) (c + ρ), 0 ≤ f x)
    (hforce : ∀ x ∈ Ioo (c - ρ) (c + ρ), δ ≤ deriv (deriv f) x + α*deriv f x - k*f x)
    (hleft : f (c - ρ) < η * ρ^2) (hright : f (c + ρ) < η * ρ^2) : False := by
  let V : ℝ → ℝ := fun x => f x-η*(x-c)^2
  have hc : c ∈ Icc (c-ρ) (c+ρ) := ⟨by linarith,by linarith⟩
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨c,hc⟩
    (show ContinuousOn V (Icc (c-ρ) (c+ρ)) from hf.sub (by fun_prop))
  have hVn : 0 ≤ V x := by
    have hh : V c ≤ V x := hmax hc
    simp only [V,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,sub_zero] at hh
    exact (hn c hc).trans hh
  have hxl : c-ρ < x := lt_of_le_of_ne hx.1 (by
    intro he
    dsimp [V] at hVn
    rw [← he] at hVn
    nlinarith)
  have hxr : x < c+ρ := lt_of_le_of_ne hx.2 (by
    intro he
    dsimp [V] at hVn
    rw [he] at hVn
    nlinarith)
  have hi : x ∈ Ioo (c-ρ) (c+ρ) := ⟨hxl,hxr⟩
  have hm : IsLocalMax V x := by
    filter_upwards [Ioo_mem_nhds hxl hxr] with y hy
    exact hmax ⟨hy.1.le,hy.2.le⟩
  have hpoly (y : ℝ) : HasDerivAt (fun z : ℝ => η*(z-c)^2) (2*η*(y-c)) y := by
    convert! (((hasDerivAt_id y).sub_const c).pow 2).const_mul η using 1
    simp only [id_eq]
    ring
  have hpolyEq : deriv (fun z : ℝ => η*(z-c)^2) = fun y => 2*η*(y-c) :=
    funext fun y => (hpoly y).deriv
  have hfirst := hm.deriv_eq_zero
  change deriv (fun y => f y-η*(y-c)^2) x = 0 at hfirst
  rw [deriv_fun_sub ((hfs x hi).differentiableAt (by norm_num)) (hpoly x).differentiableAt,
    (hpoly x).deriv] at hfirst
  have hsecond := second_deriv_nonpos_at_local_max hm
    ((hfs x hi).continuousAt.sub (by fun_prop))
  have hsecondEq : deriv (deriv V) x = deriv (deriv f) x-2*η := by
    have he := iteratedDeriv_fun_sub (n := 2) (hfs x hi)
      (show ContDiffAt ℝ 2 (fun z : ℝ => η*(z-c)^2) x by fun_prop)
    have hp2 : deriv (deriv (fun z : ℝ => η*(z-c)^2)) x = 2*η := by
      rw [hpolyEq,deriv_const_mul_field,deriv_sub_const,deriv_id'']
      ring
    simpa only [V,show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero,hp2] using he
  rw [hsecondEq] at hsecond
  have habs : |x-c| ≤ ρ := abs_le.mpr ⟨by linarith,by linarith⟩
  have hα : α*(x-c) ≤ |α| * ρ := calc
    α*(x-c) ≤ |α*(x-c)| := le_abs_self _
    _ = |α| * |x-c| := abs_mul _ _
    _ ≤ |α| * ρ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have hkill := mul_nonneg hk (hn x hx)
  have hF := hforce x hi
  rw [sub_eq_zero.mp hfirst] at hF
  nlinarith [mul_le_mul_of_nonneg_left hα (show 0 ≤ 2*η by positivity)]

/-- An interval below strike cannot instantly enter continuation when its two
endpoints were in contact. No initial derivative convergence is required. -/
theorem canonicalPrice_no_instantaneous_interval {k h c ρ a : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hρ : 0 < ρ) (hR : c + ρ < 0)
    (hinitL : canonicalPrice k h (c - ρ) a = 1 - Real.exp (c - ρ))
    (hinitR : canonicalPrice k h (c + ρ) a = 1 - Real.exp (c + ρ))
    (hcont : ∀ t : ℝ, a < t → ∀ x ∈ Ioo (c-ρ) (c+ρ),
      (x,t) ∈ canonicalContinuationRegion k h) : False := by
  let δ := k-h*Real.exp (c+ρ)
  let D := 1+|k-h-1| * ρ
  let η := δ/(4*D)
  have hδ : 0 < δ := by
    have he : Real.exp (c+ρ) < 1 := Real.exp_lt_one_iff.mpr hR
    have hprod := mul_le_mul_of_nonneg_right hhk (Real.exp_pos (c+ρ)).le
    dsimp [δ]
    nlinarith [mul_pos hk (sub_pos.mpr he)]
  have hD : 0 < D := by dsimp [D]; positivity
  have hη : 0 < η := div_pos hδ (by positivity)
  have hscale : 2*η*(1+|k-h-1| * ρ) < δ := by
    have he : η*(4*D) = δ := div_mul_cancel₀ δ (by positivity : 4*D ≠ 0)
    change 2*η*D < δ
    nlinarith
  have hbound : 0 < η*ρ^2 := mul_pos hη (sq_pos_of_pos hρ)
  have hpL : Continuous (fun t => canonicalIntrinsicPremium k h (c-ρ) t) :=
    (canonicalIntrinsicPremium_continuous hk.le).comp (continuous_const.prodMk continuous_id)
  have hpR : Continuous (fun t => canonicalIntrinsicPremium k h (c+ρ) t) :=
    (canonicalIntrinsicPremium_continuous hk.le).comp (continuous_const.prodMk continuous_id)
  have heL : canonicalIntrinsicPremium k h (c-ρ) a < η*ρ^2 := by
    simpa only [canonicalIntrinsicPremium,hinitL,sub_self] using hbound
  have heR : canonicalIntrinsicPremium k h (c+ρ) a < η*ρ^2 := by
    simpa only [canonicalIntrinsicPremium,hinitR,sub_self] using hbound
  have hsmall : ∀ᶠ t in 𝓝[>] a,
      canonicalIntrinsicPremium k h (c-ρ) t < η*ρ^2 ∧
      canonicalIntrinsicPremium k h (c+ρ) t < η*ρ^2 :=
    nhdsWithin_le_nhds (((hpL.tendsto a).eventually (Iio_mem_nhds heL)).and
      ((hpR.tendsto a).eventually (Iio_mem_nhds heR)))
  have hta : ∀ᶠ t in 𝓝[>] a, a < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hsmallL,hsmallR⟩ := (hta.and hsmall).exists
  apply no_small_forced_profile (f := fun x => canonicalIntrinsicPremium k h x t)
    hk.le hρ hη hscale
    (((canonicalIntrinsicPremium_continuous hk.le).comp
      (continuous_id.prodMk continuous_const)).continuousOn)
    (fun x hx => canonicalIntrinsicPremium_contDiffAt hk.le (hcont t ht x hx))
    (fun x _ => canonicalIntrinsicPremium_nonneg hk.le x t) _ hsmallL hsmallR
  intro x hx
  have hforce := canonicalIntrinsicPremium_forcing hk.le (hcont t ht x hx)
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.2.le) hh
  dsimp [δ]
  linarith

end MathFin.BlackScholes.AmericanPut.Stopping
