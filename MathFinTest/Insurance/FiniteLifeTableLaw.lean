/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Finite life-table law tests

Tests for `MathFin.SurvivalModel.survive_lifeTable`:
conditional survival ratios on a concrete four-year table, survival `1` on a
constant table, the first death cell weight, and the probability-law instance.
Values go through the endpoint and its helpers, not bare definitions.
-/

namespace MathFinTest.FiniteLifeTableLaw

open MathFin.SurvivalModel

/-- Concrete test table `l = [100, 90, 70, 40]`: `l 0 = 100`, `l 1 = 90`,
`l 2 = 70`, `l 3 = 40`. -/
def testTable : ℕ → ℝ := fun k => [100, 90, 70, 40].getD k 0

theorem testTable_hl0 : 0 < testTable 0 := by
  change (0 : ℝ) < 100
  norm_num

theorem testTable_hmono : ∀ k < 3, testTable (k + 1) ≤ testTable k := by
  intro k hk
  interval_cases k
  · change (90 : ℝ) ≤ 100
    norm_num
  · change (70 : ℝ) ≤ 90
    norm_num
  · change (40 : ℝ) ≤ 70
    norm_num

theorem testTable_hnonneg : ∀ k ≤ 3, 0 ≤ testTable k := by
  intro k hk
  interval_cases k
  · change (0 : ℝ) ≤ 100
    norm_num
  · change (0 : ℝ) ≤ 90
    norm_num
  · change (0 : ℝ) ≤ 70
    norm_num
  · change (0 : ℝ) ≤ 40
    norm_num

/-- Surviving one year from age 1: `l 2 / l 1 = 70 / 90 = 7 / 9`. -/
example : survive (lifeTableMeasure 3 testTable) (lifeTableLifetime 3)
    ((1 : ℕ) : ℝ) ((1 : ℕ) : ℝ) = 7 / 9 := by
  rw [survive_lifeTable 3 testTable testTable_hl0 testTable_hmono
    testTable_hnonneg 1 1 (by norm_num)
    (by change (0 : ℝ) < 90; norm_num)]
  change (70 : ℝ) / 90 = 7 / 9
  norm_num

/-- Surviving three years from age 0: `l 3 / l 0 = 40 / 100 = 2 / 5`. The
residual mass at the horizon stays in the table; nothing renormalizes. -/
example : survive (lifeTableMeasure 3 testTable) (lifeTableLifetime 3)
    ((3 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = 2 / 5 := by
  rw [survive_lifeTable 3 testTable testTable_hl0 testTable_hmono
    testTable_hnonneg 0 3 (by norm_num) testTable_hl0]
  change (40 : ℝ) / 100 = 2 / 5
  norm_num

/-- A constant table survives with probability 1 out to the horizon. -/
example : survive (lifeTableMeasure 3 (fun _ => (100 : ℝ)))
    (lifeTableLifetime 3) ((2 : ℕ) : ℝ) ((1 : ℕ) : ℝ) = 1 := by
  have hl0c : (0 : ℝ) < (fun _ => (100 : ℝ)) 0 := by
    change (0 : ℝ) < 100
    norm_num
  have hmonoc : ∀ k < 3,
      (fun _ => (100 : ℝ)) (k + 1) ≤ (fun _ => (100 : ℝ)) k :=
    fun k _ => le_rfl
  have hnonnegc : ∀ k ≤ 3, (0 : ℝ) ≤ (fun _ => (100 : ℝ)) k := by
    intro k _
    change (0 : ℝ) ≤ 100
    norm_num
  rw [survive_lifeTable 3 _ hl0c hmonoc hnonnegc 1 2 (by norm_num)
    (by norm_num)]
  change (100 : ℝ) / 100 = 1
  norm_num

/-- The first death cell `(0, 1]` carries `(l 0 - l 1) / l 0 = 1 / 10`. -/
example : lifeTableWeights 3 testTable ⟨0, by norm_num⟩ = 1 / 10 := by
  change ((100 : ℝ) - 90) / 100 = 1 / 10
  norm_num

/-- The table law is a probability measure, from the two helper theorems. -/
example : MeasureTheory.IsProbabilityMeasure (lifeTableMeasure 3 testTable) := by
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.ofWeights Finset.univ (lifeTableWeights 3 testTable))
  apply MeasureTheory.Measure.isProbabilityMeasure_ofWeights
  · intro a _
    exact lifeTableWeights_nonneg 3 testTable testTable_hl0 testTable_hmono
      testTable_hnonneg a
  · exact lifeTableWeights_sum 3 testTable testTable_hl0

end MathFinTest.FiniteLifeTableLaw
