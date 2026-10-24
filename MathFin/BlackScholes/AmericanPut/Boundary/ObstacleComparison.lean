/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.BoundaryTest

/-!
# Comparison with smooth subsolutions across the exercise obstacle

The comparison domain may cross the free boundary. Its two lateral curves
are independent of the exercise boundary and may meet at expiry. A contact
on the exercise boundary is handled by the one-sided test-function argument,
not by asserting that the price has a classical PDE there.

## Result

Public entry points include `twoSidedStrip`, `twoSidedStrip_isCompact`,
`DividendPutSolution.no_positive_max_off_boundary`,
`DividendPutSolution.obstacle_comparison_of_local_tests`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- Closed space-time strip on `0 ≤ t ≤ T`, between the two moving endpoints `L` and `R`. -/
def twoSidedStrip (L R : ℝ → ℝ) (T : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ T ∧ L z.2 ≤ z.1 ∧ z.1 ≤ R z.2}

/-- Continuous endpoints give a compact finite-time strip even when its
width vanishes, as it does for the square-root strip at expiry. -/
theorem twoSidedStrip_isCompact {L R : ℝ → ℝ} {T : ℝ}
    (hL : Continuous L) (hR : Continuous R)
    (hLR : ∀ t ∈ Icc 0 T, L t ≤ R t) : IsCompact (twoSidedStrip L R T) := by
  let F : ℝ × ℝ → ℝ × ℝ := fun z => (L z.2 + (R z.2 - L z.2) * z.1,z.2)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have heq : F '' (Icc (0 : ℝ) 1 ×ˢ Icc 0 T) = twoSidedStrip L R T := by
    ext z
    constructor
    · rintro ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩
      have hwidth := hLR t ht
      refine ⟨ht.1,ht.2,?_,?_⟩ <;> dsimp [F] <;> nlinarith [hs.1,hs.2]
    · rintro ⟨ht0,htT,hxl,hxr⟩
      by_cases he : L z.2 = R z.2
      · refine ⟨(0,z.2),⟨by norm_num,ht0,htT⟩,?_⟩
        have hx : z.1 = L z.2 := by linarith
        ext <;> simp [F,hx]
      · have hw : 0 < R z.2 - L z.2 :=
          sub_pos.mpr (lt_of_le_of_ne (hLR z.2 ⟨ht0,htT⟩) he)
        refine ⟨((z.1-L z.2)/(R z.2-L z.2),z.2),⟨?_,ht0,htT⟩,?_⟩
        · exact ⟨div_nonneg (sub_nonneg.mpr hxl) hw.le,
            (div_le_one hw).mpr (by linarith)⟩
        · ext <;> dsimp [F]
          · field_simp
            ring
  rw [← heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hF

/-- A positive maximum off the free boundary contradicts the two classical
PDE inequalities. The strictly positive killing rate handles a weak
subsolution inequality without a time perturbation. -/
theorem DividendPutSolution.no_positive_max_off_boundary
    {k h : ℝ} {p U : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) {x t : ℝ} (ht : 0 < t) (hxb : x ≠ b t)
    (hU : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hspace : IsLocalMax (fun y => U y t - p y t) x)
    (htime : ∀ᶠ s in 𝓝[<] t, U x s - p x s ≤ U x t - p x t)
    (hpos : p x t < U x t)
    (hsub : deriv (U x) t ≤ dividendSpatialOperator k h (fun y => U y t) x) : False := by
  obtain ⟨hps, hpde⟩ := hp.price_supersolution_off_boundary ht hxb
  have hps2 : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => p z.1 z.2) (x,t) :=
    hps.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpx : ContDiffAt ℝ 2 (fun y => p y t) x := by
    simpa only [Function.comp_def] using
      hps2.comp x (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hUx : ContDiffAt ℝ 2 (fun y => U y t) x := by
    simpa only [Function.comp_def] using
      hU.comp x (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hpt : DifferentiableAt ℝ (p x) t :=
    (hps2.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt
        (by norm_num)
  have hUt : DifferentiableAt ℝ (U x) t :=
    (hU.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt
        (by norm_num)
  have hdt := deriv_nonneg_at_left_max (hUt.sub hpt) htime
  rw [deriv_sub hUt hpt] at hdt
  have hdx : deriv (fun y => U y t) x = deriv (fun y => p y t) x := by
    have hd := hspace.deriv_eq_zero
    rw [deriv_fun_sub (hUx.differentiableAt (by norm_num))
      (hpx.differentiableAt (by norm_num))] at hd
    linarith
  have hdxx := second_deriv_nonpos_at_local_max hspace (hUx.continuousAt.sub hpx.continuousAt)
  have hsecond : deriv (deriv (fun y => U y t - p y t)) x =
      deriv (deriv (fun y => U y t)) x - deriv (deriv (fun y => p y t)) x := by
    simpa [iteratedDeriv_succ] using iteratedDeriv_fun_sub (n := 2) hUx hpx
  rw [hsecond] at hdxx
  unfold dividendSpatialOperator at hsub hpde
  rw [hdx] at hsub
  nlinarith [hp.rate_pos]

/-- Smooth pricing subsolutions below the price on the parabolic boundary
stay below it throughout a compact moving strip, even when it crosses the
exercise region. Compactness of the chosen strip is an explicit topological
premise; no comparison result is assumed in the pricing contract. -/
theorem DividendPutSolution.obstacle_comparison_of_local_tests
    {k h T : ℝ} {p U : ℝ → ℝ → ℝ} {b L R : ℝ → ℝ}
    (hp : DividendPutSolution k h p b)
    (hL : Continuous L) (hR : Continuous R)
    (hQ : IsCompact (twoSidedStrip L R T))
    (hUc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (twoSidedStrip L R T))
    (hUj : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      p x t < U x t →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hsub : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      p x t < U x t →
      deriv (U x) t ≤ dividendSpatialOperator k h (fun y => U y t) x)
    (hinit : ∀ x, L 0 ≤ x → x ≤ R 0 → U x 0 ≤ p x 0)
    (hleft : ∀ t, 0 ≤ t → t ≤ T → U (L t) t ≤ p (L t) t)
    (hright : ∀ t, 0 ≤ t → t ≤ T → U (R t) t ≤ p (R t) t) :
    ∀ z ∈ twoSidedStrip L R T, U z.1 z.2 ≤ p z.1 z.2 := by
  intro z hz
  by_contra hn
  have hpos : 0 < U z.1 z.2 - p z.1 z.2 := sub_pos.mpr (lt_of_not_ge hn)
  have hc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2 - p z.1 z.2) (twoSidedStrip L R T) :=
    hUc.sub (hp.price_continuous.mono (fun _ hw => hw.1))
  obtain ⟨w,hw,hmax⟩ := hQ.exists_isMaxOn ⟨z,hz⟩ hc
  have hwpos : 0 < U w.1 w.2 - p w.1 w.2 := hpos.trans_le (hmax hz)
  obtain ⟨hwt,hwT,hwL,hwR⟩ := hw
  have ht : 0 < w.2 := lt_of_le_of_ne hwt (by
    intro he
    have hi := hinit w.1 (by simpa [← he] using hwL) (by simpa [← he] using hwR)
    have hh : U w.1 w.2 ≤ p w.1 w.2 := by simpa [he] using hi
    linarith)
  have hl : L w.2 < w.1 := lt_of_le_of_ne hwL (by
    intro he; have hh := hleft w.2 hwt hwT; rw [he] at hh; linarith)
  have hr : w.1 < R w.2 := lt_of_le_of_ne hwR (by
    intro he; have hh := hright w.2 hwt hwT; rw [← he] at hh; linarith)
  have hspace : IsLocalMax (fun x => U x w.2 - p x w.2) w.1 := by
    filter_upwards [Ioo_mem_nhds hl hr] with x hx
    exact hmax (show (x,w.2) ∈ twoSidedStrip L R T from ⟨hwt,hwT,hx.1.le,hx.2.le⟩)
  have htimebound : ∀ᶠ s in 𝓝[<] w.2, 0 ≤ s ∧ s ≤ T := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht), self_mem_nhdsWithin] with s hs hsw
    exact ⟨hs.le,(show s < w.2 from hsw).le.trans hwT⟩
  by_cases he : w.1 = b w.2
  · have hb : ContinuousAt b w.2 := hp.boundary_continuous.continuousAt (Ici_mem_nhds ht)
    have hbl : ∀ᶠ s in 𝓝[<] w.2, L s < b s :=
      nhdsWithin_le_nhds ((hL.continuousAt).eventually_lt hb (by simpa [he] using hl))
    have hbr : ∀ᶠ s in 𝓝[<] w.2, b s < R s :=
      nhdsWithin_le_nhds (hb.eventually_lt hR.continuousAt (by simpa [he] using hr))
    have hbtmax : ∀ᶠ s in 𝓝[<] w.2,
        U (b s) s - p (b s) s ≤ U (b w.2) w.2 - p (b w.2) w.2 := by
      filter_upwards [htimebound,hbl,hbr] with s hs hls hrs
      simpa [he] using hmax
        (show (b s,s) ∈ twoSidedStrip L R T from ⟨hs.1,hs.2,hls.le,hrs.le⟩)
    have hsp : IsLocalMax (fun x => U x w.2 - p x w.2) (b w.2) := by simpa [he] using hspace
    have hj : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (b w.2,w.2) := by
      simpa [he] using hUj w.1 w.2 ht hwT hl hr (sub_pos.mp hwpos)
    have hxs : ContDiffAt ℝ 2 (fun x => U x w.2) (b w.2) := by
      simpa only [Function.comp_def] using hj.comp (b w.2)
        (show ContDiffAt ℝ 2 (fun x : ℝ => (x,w.2)) (b w.2) by fun_prop)
    have hres := hp.boundary_test_residual_pos ht (hj.differentiableAt (by norm_num)) hxs hsp hbtmax
      (by simpa [he] using (sub_pos.mp hwpos).le)
    have hineq := hsub w.1 w.2 ht hwT hl hr (sub_pos.mp hwpos)
    rw [he] at hineq
    linarith
  · have hxl : ∀ᶠ s in 𝓝[<] w.2, L s < w.1 :=
      nhdsWithin_le_nhds (hL.continuousAt.eventually_lt continuousAt_const hl)
    have hxr : ∀ᶠ s in 𝓝[<] w.2, w.1 < R s :=
      nhdsWithin_le_nhds (continuousAt_const.eventually_lt hR.continuousAt hr)
    have htm : ∀ᶠ s in 𝓝[<] w.2, U w.1 s - p w.1 s ≤ U w.1 w.2 - p w.1 w.2 := by
      filter_upwards [htimebound,hxl,hxr] with s hs hls hrs
      exact hmax (show (w.1,s) ∈ twoSidedStrip L R T from ⟨hs.1,hs.2,hls.le,hrs.le⟩)
    exact hp.no_positive_max_off_boundary ht he (hUj w.1 w.2 ht hwT hl hr (sub_pos.mp hwpos))
      hspace htm (sub_pos.mp hwpos) (hsub w.1 w.2 ht hwT hl hr (sub_pos.mp hwpos))

/-- The globally smooth spatial-test formulation remains available. The
stronger local version above only needs smoothness and the PDE inequality at
points where the candidate exceeds the price. -/
theorem DividendPutSolution.obstacle_comparison
    {k h T : ℝ} {p U : ℝ → ℝ → ℝ} {b L R : ℝ → ℝ}
    (hp : DividendPutSolution k h p b)
    (hL : Continuous L) (hR : Continuous R)
    (hQ : IsCompact (twoSidedStrip L R T))
    (hUc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (twoSidedStrip L R T))
    (_hUs : ∀ t, 0 < t → t ≤ T → ContDiff ℝ 2 (fun x => U x t))
    (hUj : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hsub : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      deriv (U x) t ≤ dividendSpatialOperator k h (fun y => U y t) x)
    (hinit : ∀ x, L 0 ≤ x → x ≤ R 0 → U x 0 ≤ p x 0)
    (hleft : ∀ t, 0 ≤ t → t ≤ T → U (L t) t ≤ p (L t) t)
    (hright : ∀ t, 0 ≤ t → t ≤ T → U (R t) t ≤ p (R t) t) :
    ∀ z ∈ twoSidedStrip L R T, U z.1 z.2 ≤ p z.1 z.2 :=
  hp.obstacle_comparison_of_local_tests hL hR hQ hUc
    (fun x t ht hT hl hr _ => hUj x t ht hT hl hr)
    (fun x t ht hT hl hr _ => hsub x t ht hT hl hr) hinit hleft hright

/-- Zero-dividend milestone on the original normalized solution contract.
This specializes the newly proved obstacle comparison, without using a
published comparison theorem as an axiom. -/
theorem zeroDividend_obstacle_comparison
    {k T : ℝ} {p U : ℝ → ℝ → ℝ} {b L R : ℝ → ℝ}
    (hp : NormalizedPutSolution k p b)
    (hL : Continuous L) (hR : Continuous R)
    (hQ : IsCompact (twoSidedStrip L R T))
    (hUc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (twoSidedStrip L R T))
    (hUs : ∀ t, 0 < t → t ≤ T → ContDiff ℝ 2 (fun x => U x t))
    (hUj : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hsub : ∀ x t, 0 < t → t ≤ T → L t < x → x < R t →
      deriv (U x) t ≤ spatialOperator k (fun y => U y t) x)
    (hinit : ∀ x, L 0 ≤ x → x ≤ R 0 → U x 0 ≤ p x 0)
    (hleft : ∀ t, 0 ≤ t → t ≤ T → U (L t) t ≤ p (L t) t)
    (hright : ∀ t, 0 ≤ t → t ≤ T → U (R t) t ≤ p (R t) t) :
    ∀ z ∈ twoSidedStrip L R T, U z.1 z.2 ≤ p z.1 z.2 :=
  (dividendPutSolution_zero_iff.mpr hp).obstacle_comparison hL hR hQ hUc hUs hUj
    (fun x t ht hT hl hr => by simpa using hsub x t ht hT hl hr) hinit hleft hright

end MathFin.BlackScholes.AmericanPut.Boundary
