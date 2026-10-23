/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ContinuousContact

/-! # Derivative-free convexity from negative-intercept line intervals

The expiry condition first makes `b(t)/t` monotone. Every chord then has
nonpositive intercept, so the line-interval property controls all chords.
This is a geometric replacement for selecting a twice-differentiable tangent.

## Result

Public entry points include `boundaryRatio_monotone_of_line_intervals`,
`convexOn_of_ratio_monotone_and_line_intervals`, `convexOn_of_negative_line_intervals`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set

theorem boundaryRatio_monotone_of_line_intervals {b : ℝ → ℝ}
    (hneg : ∀ t, 0 < t → b t < 0)
    (hnear : ∀ c T : ℝ, 0 < c → 0 < T → ∃ v, 0 < v ∧ v < T ∧ b v < -c*v)
    (hline : ∀ c d : ℝ, 0 < c → d ≤ 0 → OrdConnected {t | 0 < t ∧ b t < d-c*t}) :
    MonotoneOn (fun t => b t/t) (Ioi 0) := by
  intro s hs u hu hsu
  change 0 < s at hs
  change 0 < u at hu
  by_contra! hn
  let c := -b s/s
  have hc : 0 < c := div_pos (neg_pos.mpr (hneg s hs)) hs
  have hcs : c*s = -b s := div_mul_cancel₀ _ hs.ne'
  have hru : b u/u < -c := by simpa only [c,neg_div,neg_neg] using hn
  have hbu : b u+c*u < 0 := by
    have he := (div_lt_iff₀ hu).mp hru
    linarith
  obtain ⟨v,hv,hvs,hbv⟩ := hnear c s hc hs
  have hfv : b v+c*v < 0 := by linarith
  obtain ⟨d,hdlo,hd⟩ := exists_between (max_lt hfv hbu)
  have hvl : b v < d-c*v := by have := (le_max_left _ _).trans_lt hdlo; linarith
  have hul : b u < d-c*u := by have := (le_max_right _ _).trans_lt hdlo; linarith
  have hmid := (hline c d hc hd.le).out ⟨hv,hvl⟩ ⟨hu,hul⟩
    (show s ∈ Icc v u from ⟨hvs.le,hsu⟩)
  have hmid' : b s < d-c*s := hmid.2
  linarith

theorem convexOn_of_ratio_monotone_and_line_intervals {b : ℝ → ℝ}
    (hanti : AntitoneOn b (Ioi 0))
    (hratio : MonotoneOn (fun t => b t / t) (Ioi 0))
    (hline : ∀ c d : ℝ, 0 < c → d ≤ 0 → OrdConnected {t | 0 < t ∧ b t < d-c*t}) :
    ConvexOn ℝ (Ioi 0) b := by
  apply convexOn_of_slope_mono_adjacent (convex_Ioi (0 : ℝ))
  intro x y z hx hz hxy hyz
  change 0 < x at hx
  change 0 < z at hz
  have hy : 0 < y := hx.trans hxy
  have hxz : x < z := hxy.trans hyz
  have hbxz := hanti hx hz hxz.le
  have hrxz := (div_le_div_iff₀ hx hz).mp (hratio hx hz hxz.le)
  let c := (b x-b z)/(z-x)
  let d := b x+c*x
  have hcxz : c*(z-x) = b x-b z := div_mul_cancel₀ _ (sub_pos.mpr hxz).ne'
  have hd : d ≤ 0 := by
    have hdprod : d*(z-x) = b x*z-b z*x := by dsimp [d]; nlinarith
    have hp : d*(z-x) ≤ 0 := by rw [hdprod]; linarith
    exact nonpos_of_mul_nonpos_left hp (sub_pos.mpr hxz)
  have hxfit : b x = d-c*x := by dsimp [d]; ring
  have hzfit : b z = d-c*z := by dsimp [d]; nlinarith
  have hby : b y ≤ d-c*y := by
    rcases hbxz.eq_or_lt with he | he
    · have hmid := hanti hx hy hxy.le
      have hc0 : c = 0 := by simp only [c,he,sub_self,zero_div]
      simpa only [d,hc0,zero_mul,add_zero,sub_zero] using hmid
    · have hc : 0 < c := div_pos (sub_pos.mpr he) (sub_pos.mpr hxz)
      rcases hd.eq_or_lt with hde | hdn
      · have hyr := (div_le_div_iff₀ hy hz).mp (hratio hy hz hyz.le)
        rw [hde,zero_sub] at hzfit
        have hp : (b y+c*y)*z ≤ 0 := by rw [hzfit] at hyr; nlinarith
        have hn := nonpos_of_mul_nonpos_left hp hz
        rw [hde]
        linarith
      · by_contra! hgap
        obtain ⟨ε,hε,hεsmall⟩ := exists_between (lt_min (neg_pos.mpr hdn) (sub_pos.mpr hgap))
        have hde : d+ε ≤ 0 := by linarith [(min_le_left _ _).trans' hεsmall.le]
        have hxe : b x < d+ε-c*x := by rw [hxfit]; linarith
        have hze : b z < d+ε-c*z := by rw [hzfit]; linarith
        have hm := (hline c (d+ε) hc hde).out ⟨hx,hxe⟩ ⟨hz,hze⟩
          (show y ∈ Icc x z from ⟨hxy.le,hyz.le⟩)
        have hme : b y < d+ε-c*y := hm.2
        have hεgap := hεsmall.trans_le (min_le_right _ _)
        linarith
  apply (div_le_div_iff₀ (sub_pos.mpr hxy) (sub_pos.mpr hyz)).mpr
  have hm := mul_le_mul_of_nonneg_right hby (sub_pos.mpr hxz).le
  rw [hxfit,hzfit]
  nlinarith

theorem convexOn_of_negative_line_intervals {b : ℝ → ℝ}
    (hneg : ∀ t, 0 < t → b t < 0) (hanti : AntitoneOn b (Ioi 0))
    (hnear : ∀ c T : ℝ, 0 < c → 0 < T → ∃ v, 0 < v ∧ v < T ∧ b v < -c*v)
    (hline : ∀ c d : ℝ, 0 < c → d ≤ 0 → OrdConnected {t | 0 < t ∧ b t < d-c*t}) :
    ConvexOn ℝ (Ioi 0) b :=
  convexOn_of_ratio_monotone_and_line_intervals hanti
    (boundaryRatio_monotone_of_line_intervals hneg hnear hline) hline

end MathFin.BlackScholes.AmericanPut.Boundary
