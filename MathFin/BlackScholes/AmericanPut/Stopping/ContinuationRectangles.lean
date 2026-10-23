/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StrictExerciseGeometry

/-! # Closed backward rectangles inside the actual continuation region 
## Result

Public entry points include `InContinuationRectangle`, `exists_continuationRectangle`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal Topology

/-- Every point `(y,T-s)` with `|y-x| ≤ R` and `s ≤ δ` lies in the canonical continuation
region: the closed backward rectangle at `(x,T)` of spatial radius `R` and time depth `δ`. -/
def InContinuationRectangle (k h x : ℝ) (T : ℝ≥0) (R : ℝ) (δ : ℝ≥0) : Prop :=
  ∀ s : ℝ≥0, s ≤ δ → ∀ y : ℝ, |y-x| ≤ R → (y,(T : ℝ)-(s : ℝ)) ∈ canonicalContinuationRegion k h

theorem exists_continuationRectangle {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h) :
    ∃ R : ℝ, 0 < R ∧ ∃ δ : ℝ≥0, 0 < δ ∧ δ < T ∧ InContinuationRectangle k h x T R δ := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (canonicalContinuationRegion_isOpen hk) _ hp
  have hT : (0 : ℝ) < T := hp.1
  let d : ℝ := min (ε/2) ((T : ℝ)/2)
  have hd : 0 < d := lt_min (half_pos hε) (half_pos hT)
  have hdε : d ≤ ε/2 := min_le_left _ _
  have hdT : d < T := (min_le_right _ _).trans_lt (half_lt_self hT)
  refine ⟨ε/2,half_pos hε,d.toNNReal,Real.toNNReal_pos.mpr hd,?_,?_⟩
  · exact_mod_cast (show (d.toNNReal : ℝ) < T by rw [Real.coe_toNNReal _ hd.le]; exact hdT)
  · intro s hs y hy
    apply hball
    change dist (y,(T : ℝ)-(s : ℝ)) (x,(T : ℝ)) < ε
    rw [Prod.dist_eq]
    apply max_lt
    · exact (show dist y x ≤ ε/2 by simpa only [Real.dist_eq] using hy).trans_lt (half_lt_self hε)
    · have hsd : (s : ℝ) ≤ d := by
        have hh : (s : ℝ) ≤ d.toNNReal := by exact_mod_cast hs
        simpa only [Real.coe_toNNReal _ hd.le] using hh
      rw [Real.dist_eq,show ((T : ℝ)-(s : ℝ))-(T : ℝ) = -(s : ℝ) by ring,
        abs_neg,abs_of_nonneg s.coe_nonneg]
      exact (hsd.trans hdε).trans_lt (half_lt_self hε)

end MathFin.BlackScholes.AmericanPut.Stopping
