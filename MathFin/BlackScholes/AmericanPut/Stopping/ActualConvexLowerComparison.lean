/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualSpatialRegularity
public import MathFin.BlackScholes.AmericanPut.Boundary.OneSidedContact
public import MathFin.BlackScholes.AmericanPut.Boundary.ObstacleComparison

/-! # Convex spatial subsolutions lie below the actual stopping price

A smooth spatially convex test cannot have a local maximum over the price
in exercise: smooth fit and the exercise-side test give negative curvature.
In continuation the pricing PDE rules out a positive space-time maximum.
No boundary time derivative is used.

## Result

Public entry points include `canonicalPrice_spatial_test_in_exercise`,
`canonicalPrice_no_positive_convex_lower_max`, `convex_subsolution_le_canonicalPrice_on_strip`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

theorem canonicalPrice_spatial_test_in_exercise {k h x t : ℝ} {F : ℝ → ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t)
    (hx : x ≤ canonicalLogBoundary k h t) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMax (fun y => F y - canonicalPrice k h y t) x) :
    deriv (deriv F) x ≤ -Real.exp x := by
  have hdF := hF.differentiableAt (by norm_num)
  have hfit := canonicalPrice_hasDerivAt_exercise hk hh hhk ht hx
  have hsub := (hdF.hasDerivAt.sub hfit).deriv
  change deriv (fun y => F y-canonicalPrice k h y t) x = deriv F x- -Real.exp x at hsub
  rw [hm.deriv_eq_zero] at hsub
  have hslope : deriv F x = -Real.exp x := by linarith
  let G : ℝ → ℝ := fun y => F y-(1-Real.exp y)
  have hg : ContDiffAt ℝ 2 (fun y : ℝ => 1-Real.exp y) x := by fun_prop
  have hdg : deriv G x = 0 := by
    change deriv (fun y => F y-(1-Real.exp y)) x = 0
    rw [deriv_fun_sub hdF
        (hg.differentiableAt (by norm_num)),deriv_const_sub',Real.deriv_exp,hslope]
    ring
  have hsecond : deriv (deriv G) x = deriv (deriv F) x+Real.exp x := by
    simpa only [G,iteratedDeriv_succ,iteratedDeriv_zero,deriv_const_sub',Real.deriv_exp,
      deriv.fun_neg',sub_neg_eq_add] using iteratedDeriv_fun_sub (n := 2) hF hg
  have hgm : ∀ᶠ y in 𝓝[<] x, G y ≤ G x := by
    filter_upwards [nhdsWithin_le_nhds hm,self_mem_nhdsWithin] with y hy hyx
    change F y-canonicalPrice k h y t ≤ F x-canonicalPrice k h x t at hy
    rw [canonicalPrice_exercise_value hk hh hhk ht hx,
      canonicalPrice_exercise_value hk hh hhk ht ((show y < x from hyx).le.trans hx)] at hy
    exact hy
  have he :=
      second_deriv_nonpos_at_left_stationary_max (hF.continuousAt.sub hg.continuousAt) hdg hgm
  change deriv (deriv G) x ≤ 0 at he
  rw [hsecond] at he
  linarith

theorem canonicalPrice_no_positive_convex_lower_max {k h x t : ℝ} {U : ℝ → ℝ → ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t)
    (hU : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hconvex : 0 ≤ deriv (deriv (fun y => U y t)) x)
    (hspace : IsLocalMax (fun y => U y t-canonicalPrice k h y t) x)
    (htime : ∀ᶠ s in 𝓝[<] t, U x s-canonicalPrice k h x s ≤ U x t-canonicalPrice k h x t)
    (hpos : canonicalPrice k h x t < U x t)
    (hsub : pricingOperator k h (fun z => U z.1 z.2) (x,t) ≤ 0) : False := by
  have hUx : ContDiffAt ℝ 2 (fun y => U y t) x :=
    hU.comp (f := fun y : ℝ => (y,t)) x (by fun_prop)
  have hx : canonicalLogBoundary k h t < x := by
    by_contra! hn
    have he := canonicalPrice_spatial_test_in_exercise hk hh hhk ht hn hUx hspace
    linarith [Real.exp_pos x]
  have hz : (x,t) ∈ canonicalContinuationRegion k h := by
    rw [canonicalContinuationRegion_eq_logBoundary hk hh hhk]
    exact ⟨ht,hx⟩
  have hp : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => canonicalPrice k h z.1 z.2) (x,t) :=
    (canonicalPrice_contDiffAt hk.le hz).of_le (WithTop.coe_le_coe.mpr le_top)
  let V : ℝ × ℝ → ℝ := fun z => U z.1 z.2-canonicalPrice k h z.1 z.2
  have hV : ContDiffAt ℝ 2 V (x,t) := hU.sub hp
  have hd : DifferentiableAt ℝ (fun s => V (x,s)) t :=
    (hV.comp (f := fun s : ℝ => (x,s)) t (by fun_prop)).differentiableAt (by norm_num)
  have hdt := deriv_nonneg_at_left_max hd htime
  have hddx := second_deriv_nonpos_at_local_max hspace
    (hV.continuousAt.comp (f := fun y : ℝ => (y,t)) (by fun_prop))
  have hsum := pricingOperator_add hV hp k h
  simp only [V,sub_add_cancel] at hsum
  change pricingOperator k h (fun z => U z.1 z.2) (x,t) = pricingOperator k h V (x,t)+
    pricingOperator k h (fun z => canonicalPrice k h z.1 z.2) (x,t) at hsum
  rw [canonicalPrice_pricingOperator hk.le hz,add_zero] at hsum
  have hPV : pricingOperator k h V (x,t) ≤ 0 := by rw [← hsum]; exact hsub
  unfold pricingOperator at hPV
  dsimp only at hPV
  have hzero : deriv (fun y => V (y,t)) x = 0 := hspace.deriv_eq_zero
  rw [hzero,mul_zero,sub_zero] at hPV
  have hkill : 0 < k*V (x,t) := mul_pos hk (sub_pos.mpr hpos)
  change deriv (deriv (fun y => V (y,t))) x ≤ 0 at hddx
  linarith

theorem convex_subsolution_le_canonicalPrice_on_strip {k h T : ℝ} {U : ℝ → ℝ → ℝ}
    {L R : ℝ → ℝ} (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k)
    (hL : Continuous L) (hR : Continuous R) (hQ : IsCompact (twoSidedStrip L R T))
    (hUc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (twoSidedStrip L R T))
    (hUs : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hconvex : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      0 ≤ deriv (deriv (fun y => U y t)) x)
    (hsub : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      pricingOperator k h (fun z => U z.1 z.2) (x,t) ≤ 0)
    (hinit : ∀ x, L 0 ≤ x → x ≤ R 0 → U x 0 ≤ canonicalPrice k h x 0)
    (hleft : ∀ t, 0 ≤ t → t ≤ T → U (L t) t ≤ canonicalPrice k h (L t) t)
    (hright : ∀ t, 0 ≤ t → t ≤ T → U (R t) t ≤ canonicalPrice k h (R t) t) :
    ∀ z ∈ twoSidedStrip L R T, U z.1 z.2 ≤ canonicalPrice k h z.1 z.2 := by
  intro z hz
  by_contra! hn
  let V : ℝ × ℝ → ℝ := fun z => U z.1 z.2-canonicalPrice k h z.1 z.2
  have hVc : ContinuousOn V (twoSidedStrip L R T) :=
      hUc.sub (canonicalPrice_continuous hk.le).continuousOn
  obtain ⟨w,hw,hmax⟩ := hQ.exists_isMaxOn ⟨z,hz⟩ hVc
  have hpos : 0 < V w := (sub_pos.mpr hn).trans_le (hmax hz)
  obtain ⟨hw0,hwT,hwL,hwR⟩ := hw
  have hwt : 0 < w.2 := lt_of_le_of_ne hw0 (by
    intro he
    have hi := hinit w.1 (by simpa [← he] using hwL) (by simpa [← he] using hwR)
    have hh : U w.1 w.2 ≤ canonicalPrice k h w.1 w.2 := by simpa [he] using hi
    exact not_lt_of_ge hh (sub_pos.mp hpos))
  have hl : L w.2 < w.1 := lt_of_le_of_ne hwL (by
    intro he
    have hh := hleft w.2 hw0 hwT
    rw [he] at hh
    exact not_lt_of_ge hh (sub_pos.mp hpos))
  have hr : w.1 < R w.2 := lt_of_le_of_ne hwR (by
    intro he
    have hh := hright w.2 hw0 hwT
    rw [← he] at hh
    exact not_lt_of_ge hh (sub_pos.mp hpos))
  have hspace : IsLocalMax (fun x => V (x,w.2)) w.1 := by
    filter_upwards [Ioo_mem_nhds hl hr] with x hx
    exact hmax ⟨hw0,hwT,hx.1.le,hx.2.le⟩
  have hxl : ∀ᶠ s in 𝓝[<] w.2, L s < w.1 :=
    nhdsWithin_le_nhds (hL.continuousAt.eventually_lt continuousAt_const hl)
  have hxr : ∀ᶠ s in 𝓝[<] w.2, w.1 < R s :=
    nhdsWithin_le_nhds (continuousAt_const.eventually_lt hR.continuousAt hr)
  have htime : ∀ᶠ s in 𝓝[<] w.2, V (w.1,s) ≤ V w := by
    filter_upwards [hxl,hxr,nhdsWithin_le_nhds (Ioi_mem_nhds hwt),self_mem_nhdsWithin]
      with s hls hrs hs hsw
    exact hmax ⟨hs.le,(show s < w.2 from hsw).le.trans hwT,hls.le,hrs.le⟩
  exact canonicalPrice_no_positive_convex_lower_max hk hh hhk hwt (hUs _ _ hwt hwT hl hr)
    (hconvex _ _ hwt hwT hl hr) hspace htime (sub_pos.mp hpos) (hsub _ _ hwt hwT hl hr)

end MathFin.BlackScholes.AmericanPut.Stopping
