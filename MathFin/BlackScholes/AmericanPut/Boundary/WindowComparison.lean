/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.TimeMonotonicity

/-!
# Obstacle comparison from an arbitrary initial time

The initial slice may be at any nonnegative time, not only expiry. This is
needed to compare a linear pricing evolution of a later price slice against
the American candidate. The boundary contact is tested one-sidedly, without
assuming second differentiability of the price across the free boundary.

## Result

Public entry points include `DividendPutSolution.obstacle_comparison_window`,
`localization_penalty_subsolution`, `DividendPutSolution.obstacle_comparison_unbounded_window`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

theorem DividendPutSolution.obstacle_comparison_window
    {k h a T L R : ℝ} {p U : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (ha : 0 ≤ a)
    (hUc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (Icc L R ×ˢ Icc a T))
    (hUj : ∀ x t, a < t → t ≤ T → L < x → x < R →
      p x t < U x t → ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hsub : ∀ x t, a < t → t ≤ T → L < x → x < R →
      p x t < U x t → deriv (U x) t ≤ dividendSpatialOperator k h (fun y => U y t) x)
    (hinit : ∀ x ∈ Icc L R, U x a ≤ p x a)
    (hleft : ∀ t ∈ Icc a T, U L t ≤ p L t)
    (hright : ∀ t ∈ Icc a T, U R t ≤ p R t) :
    ∀ z ∈ Icc L R ×ˢ Icc a T, U z.1 z.2 ≤ p z.1 z.2 := by
  intro z hz
  by_contra hn
  have hpos : 0 < U z.1 z.2-p z.1 z.2 := sub_pos.mpr (lt_of_not_ge hn)
  have hc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2-p z.1 z.2)
      (Icc L R ×ˢ Icc a T) := hUc.sub (hp.price_continuous.mono (fun _ hw => ha.trans hw.2.1))
  obtain ⟨w,hw,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn ⟨z,hz⟩ hc
  have hwpos : 0 < U w.1 w.2-p w.1 w.2 := hpos.trans_le (hmax hz)
  have ht : a < w.2 := lt_of_le_of_ne hw.2.1 (by
    intro he
    have hi := hinit w.1 hw.1
    rw [he] at hi
    linarith)
  have ht0 : 0 < w.2 := ha.trans_lt ht
  have hl : L < w.1 := lt_of_le_of_ne hw.1.1 (by
    intro he; have hh := hleft w.2 hw.2; rw [he] at hh; linarith)
  have hr : w.1 < R := lt_of_le_of_ne hw.1.2 (by
    intro he; have hh := hright w.2 hw.2; rw [← he] at hh; linarith)
  have hspace : IsLocalMax (fun x => U x w.2-p x w.2) w.1 := by
    filter_upwards [Ioo_mem_nhds hl hr] with x hx
    exact hmax (show (x,w.2) ∈ Icc L R ×ˢ Icc a T from ⟨⟨hx.1.le,hx.2.le⟩,hw.2⟩)
  have htime : ∀ᶠ s in 𝓝[<] w.2, s ∈ Icc a T := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht),self_mem_nhdsWithin] with s hs hsw
    exact ⟨hs.le,(show s < w.2 from hsw).le.trans hw.2.2⟩
  have hj := hUj w.1 w.2 ht hw.2.2 hl hr (sub_pos.mp hwpos)
  have hi := hsub w.1 w.2 ht hw.2.2 hl hr (sub_pos.mp hwpos)
  by_cases he : w.1 = b w.2
  · have hb : ContinuousAt b w.2 := hp.boundary_continuous.continuousAt (Ici_mem_nhds ht0)
    have hbl : ∀ᶠ s in 𝓝[<] w.2, L < b s :=
      nhdsWithin_le_nhds (continuousAt_const.eventually_lt hb (by simpa [he] using hl))
    have hbr : ∀ᶠ s in 𝓝[<] w.2, b s < R :=
      nhdsWithin_le_nhds (hb.eventually_lt continuousAt_const (by simpa [he] using hr))
    have hcurve : ∀ᶠ s in 𝓝[<] w.2,
        U (b s) s-p (b s) s ≤ U (b w.2) w.2-p (b w.2) w.2 := by
      filter_upwards [htime,hbl,hbr] with s hs hls hrs
      simpa [he] using hmax
        (show (b s,s) ∈ Icc L R ×ˢ Icc a T from ⟨⟨hls.le,hrs.le⟩,hs⟩)
    have hj' : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (b w.2,w.2) := by
      simpa [he] using hj
    have hxs : ContDiffAt ℝ 2 (fun x => U x w.2) (b w.2) := by
      simpa only [Function.comp_def] using hj'.comp (b w.2)
        (show ContDiffAt ℝ 2 (fun x : ℝ => (x,w.2)) (b w.2) by fun_prop)
    have hres := hp.boundary_test_residual_pos ht0 (hj'.differentiableAt (by norm_num)) hxs
      (by simpa [he] using hspace) hcurve (by simpa [he] using (sub_pos.mp hwpos).le)
    rw [he] at hi
    linarith
  · have htm : ∀ᶠ s in 𝓝[<] w.2, U w.1 s-p w.1 s ≤ U w.1 w.2-p w.1 w.2 := by
      filter_upwards [htime] with s hs
      exact hmax (show (w.1,s) ∈ Icc L R ×ˢ Icc a T from ⟨hw.1,hs⟩)
    exact hp.no_positive_max_off_boundary ht0 he hj hspace htm (sub_pos.mp hwpos) hi

theorem localization_penalty_subsolution {k h ε x t : ℝ} {U : ℝ → ℝ → ℝ}
    (hk : 0 ≤ k) (hε : 0 ≤ ε)
    (hU : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hsub : deriv (U x) t ≤ dividendSpatialOperator k h (fun y => U y t) x) :
    deriv (fun s => U x s-ε*localizationBarrier k h x s) t ≤
      dividendSpatialOperator k h (fun y => U y t-ε*localizationBarrier k h y t) x := by
  have hUx : ContDiffAt ℝ 2 (fun y => U y t) x := by
    simpa only [Function.comp_def] using hU.comp x
      (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hWx : ContDiffAt ℝ 2 (fun y => localizationBarrier k h y t) x := by
    unfold localizationBarrier
    fun_prop
  have hUt : DifferentiableAt ℝ (U x) t :=
    (hU.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt
        (by norm_num)
  rw [deriv_fun_sub hUt ((localizationBarrier_hasDeriv_t k h x t).differentiableAt.const_mul ε),
    deriv_const_mul_field,dividendSpatialOperator_sub_const_mul hUx hWx]
  have hsup := localizationBarrier_supersolution (h := h) hk x t
  nlinarith

/-- A bounded-above pricing subsolution starting below the price stays below
it on the whole spatial line, from any nonnegative initial time. Local
smoothness is needed only where the test exceeds the price. -/
theorem DividendPutSolution.obstacle_comparison_unbounded_window
    {k h a T C : ℝ} {p U : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (ha : 0 ≤ a)
    (hUc : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) {z | z.2 ∈ Icc a T})
    (hUb : ∀ x t, t ∈ Icc a T → U x t ≤ C)
    (hUj : ∀ x t, a < t → t ≤ T → p x t < U x t →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hsub : ∀ x t, a < t → t ≤ T → p x t < U x t →
      deriv (U x) t ≤ dividendSpatialOperator k h (fun y => U y t) x)
    (hinit : ∀ x, U x a ≤ p x a) :
    ∀ x t, t ∈ Icc a T → U x t ≤ p x t := by
  have hpen (ε : ℝ) (hε : 0 < ε) (x t : ℝ) (ht : t ∈ Icc a T) :
      U x t-ε*localizationBarrier k h x t ≤ p x t := by
    let R := max (|x|+1) (max 1 (max C 1/ε))
    have hR1 : 1 ≤ R := (le_max_left 1 (max C 1/ε)).trans (le_max_right _ _)
    have hRe : max C 1/ε ≤ R := (le_max_right 1 (max C 1/ε)).trans (le_max_right _ _)
    have hRx : |x| ≤ R := by dsimp [R]; linarith [le_max_left (|x|+1) (max 1 (max C 1/ε))]
    have hquad : C ≤ ε*(1+R^2) := by
      have hεR := (div_le_iff₀ hε).mp hRe
      nlinarith [le_max_left C 1,mul_le_mul_of_nonneg_left (show R ≤ R^2 by nlinarith) hε.le]
    let V : ℝ → ℝ → ℝ := fun y s => U y s-ε*localizationBarrier k h y s
    have hVgt {y s : ℝ} (hgt : p y s < V y s) : p y s < U y s := by
      dsimp [V] at hgt
      nlinarith [localizationBarrier_pos k h y s]
    have hedge (y : ℝ) (hy : y^2 = R^2) (s : ℝ) (hs : s ∈ Icc a T) : V y s ≤ p y s := by
      have hW := localizationBarrier_ge_quad k h y (ha.trans hs.1)
      rw [hy] at hW
      have hP := hp.price_nonneg y (ha.trans hs.1)
      have hB := hUb y s hs
      dsimp [V]
      nlinarith
    have hc : ContinuousOn (fun z : ℝ × ℝ => V z.1 z.2) (Icc (-R) R ×ˢ Icc a T) :=
      (hUc.mono (fun _ hz => hz.2)).sub
        ((localizationBarrier_contDiff k h).continuous.const_mul ε).continuousOn
    have hcomp := hp.obstacle_comparison_window ha hc
      (fun y s has hsT _ _ hgt => (hUj y s has hsT (hVgt hgt)).sub
        (contDiffAt_const.mul (localizationBarrier_contDiff k h).contDiffAt))
      (fun y s has hsT _ _ hgt => localization_penalty_subsolution hp.rate_pos.le hε.le
        (hUj y s has hsT (hVgt hgt)) (hsub y s has hsT (hVgt hgt)))
      (fun y _ => by
        dsimp [V]
        nlinarith [hinit y,localizationBarrier_pos k h y a])
      (fun s hs => hedge (-R) (by ring) s hs)
      (fun s hs => hedge R rfl s hs)
    exact hcomp (x,t) ⟨⟨(neg_le_neg hRx).trans (neg_abs_le x),(le_abs_self x).trans hRx⟩,ht⟩
  intro x t ht
  by_contra hn
  have hgap : 0 < U x t-p x t := sub_pos.mpr (lt_of_not_ge hn)
  let W := localizationBarrier k h x t
  have hW : 0 < W := localizationBarrier_pos k h x t
  let ε := (U x t-p x t)/(2*W)
  have hε : 0 < ε := div_pos hgap (by positivity)
  have hbound := hpen ε hε x t ht
  have he : ε*W = (U x t-p x t)/2 := by dsimp [ε]; field_simp
  change U x t-ε*W ≤ p x t at hbound
  rw [he] at hbound
  linarith

end MathFin.BlackScholes.AmericanPut.Boundary
