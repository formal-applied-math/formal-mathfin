/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicValley

/-! # Removing smoothing from the three-point maximum principle 
## Result

Public entry points include `three_point_bound_of_positive_superlevels`,
`parabolic_three_point_bound`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set
open scoped ContDiff

theorem three_point_bound_of_positive_superlevels {F : ℝ → ℝ} {S : Set ℝ}
    (hlevels : ∀ ε : ℝ, 0 < ε → OrdConnected {x | x ∈ S ∧ ε < F x})
    {x y z : ℝ} (hx : x ∈ S) (hz : z ∈ S) (hxy : x ≤ y) (hyz : y ≤ z) :
    min (F x) (F z) ≤ max (F y) 0 := by
  by_contra hn
  have hgap := lt_of_not_ge hn
  let ε := (min (F x) (F z)+max (F y) 0)/2
  have hε : 0 < ε := by dsimp [ε]; linarith [le_max_right (F y) 0]
  have hex : ε < F x := by dsimp [ε]; linarith [min_le_left (F x) (F z)]
  have hez : ε < F z := by dsimp [ε]; linarith [min_le_right (F x) (F z)]
  have hh := (hlevels ε hε).out ⟨hx,hex⟩ ⟨hz,hez⟩ ⟨hxy,hyz⟩
  dsimp [ε] at hh
  linarith [le_max_left (F y) 0,hh.2]

/-- The positive part remains unimodal, by the proved three-point maximum
principle. This bypasses both zero-count initialization and Sturm propagation. -/
theorem parabolic_three_point_bound {U D : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {R T : ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (hbR : ∀ t ∈ Icc 0 T, b t ≤ R)
    (hU : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (movingStrip b R 0 T))
    (hs : ∀ x t, 0 < t → t ≤ T → b t < x → x < R →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hpde : ∀ x t, 0 < t → t ≤ T → b t < x → x < R →
      deriv (U x) t = deriv (deriv (fun y => U y t)) x + D x t * deriv (fun y => U y t) x)
    (hleft : ∀ t, 0 ≤ t → t ≤ T → U (b t) t ≤ 0)
    (hright : ∀ t, 0 ≤ t → t ≤ T → U R t ≤ 0)
    (hinit : ∀ x y z, b 0 ≤ x → x ≤ y → y ≤ z → z ≤ R →
      min (U x 0) (U z 0) ≤ max (U y 0) 0)
    {x y z t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hbx : b t ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzR : z ≤ R) :
    min (U x t) (U z t) ≤ max (U y t) 0 := by
  by_contra hn
  let gap := min (U x t) (U z t)-max (U y t) 0
  have hg : 0 < gap := sub_pos.mpr (lt_of_not_ge hn)
  let δ := gap/4
  have hδ : 0 < δ := div_pos hg (by norm_num)
  let η := δ/(t+1)
  have hden : 0 < t+1 := by linarith
  have hη : 0 < η := div_pos hδ hden
  have hpen : η*(t+1) = δ := by dsimp [η]; field_simp
  have hh := parabolic_smoothValley_nonpos hδ hη hb hbR hU hs hpde hleft hright hinit
    _ (sameTimeTriple_mem ht htT hbx hxy hyz hzR)
  change smoothValley δ (U x t) (U y t) (U z t)-η*t ≤ 0 at hh
  have hlo := (smoothValley_bounds hδ.le (U x t) (U y t) (U z t)).1
  change gap-δ ≤ smoothValley δ (U x t) (U y t) (U z t) at hlo
  have hδeq : 4*δ = gap := by dsimp [δ]; ring
  nlinarith

end MathFin.BlackScholes.AmericanPut.Boundary
