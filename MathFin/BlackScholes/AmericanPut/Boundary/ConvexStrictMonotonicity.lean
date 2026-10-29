/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Strict decrease and strict exponential convexity without derivatives 
## Result

Public entry points include `strictAntiOn_of_convex_antitone_no_flat_tail`,
`strictConvexOn_exp_of_convex_injective`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set

/-- A nonincreasing convex function on the positive half-line can fail to
strictly decrease only by having a constant tail. -/
theorem strictAntiOn_of_convex_antitone_no_flat_tail {b : ℝ → ℝ}
    (hc : ConvexOn ℝ (Ioi 0) b) (ha : AntitoneOn b (Ioi 0))
    (hn : ∀ A, 0 < A → ¬ (∀ u, A ≤ u → b u = b A)) : StrictAntiOn b (Ioi 0) := by
  intro s hs t ht hst
  apply lt_of_le_of_ne (ha hs ht hst.le)
  intro heq
  apply hn t ht
  intro u htu
  rcases htu.eq_or_lt with hu | hu
  · rw [← hu]
  · have hupos : u ∈ Ioi (0 : ℝ) := lt_trans ht hu
    have hslope := hc.slope_mono_adjacent hs hupos hst hu
    rw [heq,sub_self,zero_div] at hslope
    have hnonneg : 0 ≤ b u-b t := by
      simpa only [zero_mul,heq] using (le_div_iff₀ (sub_pos.mpr hu)).mp hslope
    exact le_antisymm (ha ht hupos hu.le) (by linarith)

/-- Strict convexity of `exp` upgrades convexity of any injective real profile.
The inner profile need not be strictly convex or differentiable. -/
theorem strictConvexOn_exp_of_convex_injective {b : ℝ → ℝ} {s : Set ℝ}
    (hc : ConvexOn ℝ s b) (hi : s.InjOn b) :
    StrictConvexOn ℝ s (fun t => Real.exp (b t)) := by
  refine ⟨hc.1,?_⟩
  intro x hx y hy hxy a c ha hcpos hac
  have hinner := hc.2 hx hy ha.le hcpos.le hac
  have houter := strictConvexOn_exp.2 (mem_univ (b x)) (mem_univ (b y))
    (fun he => hxy (hi hx hy he)) ha hcpos hac
  exact (Real.exp_le_exp.mpr hinner).trans_lt houter

end MathFin.BlackScholes.AmericanPut.Boundary
