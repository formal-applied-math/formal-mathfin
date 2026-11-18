/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Chain-ladder monotonicity checks

Hand-checkable evaluations pinning `MathFin.le_chainComplete` on the monotone
triangle with rows `100, 150, 180 / 80, 120 / 50` and `n = 2`: predicted outstanding
claims `90 - 50 = 40` (row `2`) and `144 - 120 = 24` (row `1`), a decreasing-row
triangle where the conclusion fails, and the degenerate `n = 0` equality.
-/

namespace MathFinTest

open MathFin

/-- The monotone run-off triangle: row `0` holds `100, 150, 180`, row `1` holds
`80, 120`, and row `2` holds `50`. Every other cell is `0`. -/
def monoC : ℕ → ℕ → ℝ
  | 0, 0 => 100
  | 0, 1 => 150
  | 0, 2 => 180
  | 1, 0 => 80
  | 1, 1 => 120
  | 2, 0 => 50
  | _, _ => 0

/-- Every cell of the monotone triangle is nonnegative. -/
theorem monoC_nonneg : ∀ i j, 0 ≤ monoC i j := by
  intro i j
  unfold monoC
  split <;> norm_num

/-- The observed rows of the monotone triangle are nondecreasing. -/
theorem monoC_mono : ∀ i j, i + (j + 1) ≤ 2 → monoC i j ≤ monoC i (j + 1) := by
  intro i j h
  have hdisj : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hdisj with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [monoC]

/-- Both selected-factor denominators of the monotone triangle are positive. -/
theorem monoC_denom : ∀ j < 2, 0 < ∑ i ∈ Finset.range (2 - j), monoC i j := by
  intro j hj
  have hj0 : 0 ≤ j := Nat.zero_le j
  interval_cases j <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, monoC] <;> norm_num

/-- First selected factor: `(150 + 120) / (100 + 80) = 3 / 2`. -/
theorem monoC_factor0 : chainFactor 2 monoC 0 = 3 / 2 := by
  rw [chainFactor]
  change (∑ i ∈ Finset.range 2, monoC i 1) / (∑ i ∈ Finset.range 2, monoC i 0)
    = 3 / 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, monoC]
  norm_num

/-- Final factor: `180 / 150 = 6 / 5`. -/
theorem monoC_factor1 : chainFactor 2 monoC 1 = 6 / 5 := by
  rw [chainFactor]
  change (∑ i ∈ Finset.range 1, monoC i 2) / (∑ i ∈ Finset.range 1, monoC i 1)
    = 6 / 5
  simp only [Finset.sum_range_one, monoC]
  norm_num

/-- Ultimate forecast for row `1`: `120 * (6 / 5) = 144`. -/
theorem monoC_ultimate_row1 : chainComplete 2 monoC 1 2 = 144 := by
  change chainComplete 2 monoC 1 (1 + 1) = _
  simp only [chainComplete, (by decide : ¬ 1 + (1 + 1) ≤ 2),
    (by decide : 1 + (0 + 1) ≤ 2), ↓reduceIte]
  rw [monoC_factor1]
  change (120 : ℝ) * (6 / 5) = 144
  norm_num

/-- Ultimate forecast for row `2`: `(50 * (3 / 2)) * (6 / 5) = 90`. -/
theorem monoC_ultimate_row2 : chainComplete 2 monoC 2 2 = 90 := by
  change chainComplete 2 monoC 2 (1 + 1) = _
  simp only [chainComplete, (by decide : ¬ 2 + (1 + 1) ≤ 2),
    (by decide : ¬ 2 + (0 + 1) ≤ 2), ↓reduceIte]
  rw [monoC_factor0, monoC_factor1]
  change ((50 : ℝ) * (3 / 2)) * (6 / 5) = 90
  norm_num

/-- The monotonicity bound on row `2`, from `le_chainComplete`. -/
theorem monoC_bound_row2 : monoC 2 (2 - 2) ≤ chainComplete 2 monoC 2 2 :=
  le_chainComplete 2 monoC monoC_nonneg monoC_mono monoC_denom 2

/-- The monotonicity bound on row `1`, from `le_chainComplete`. -/
theorem monoC_bound_row1 : monoC 1 (2 - 1) ≤ chainComplete 2 monoC 1 2 :=
  le_chainComplete 2 monoC monoC_nonneg monoC_mono monoC_denom 1

/-- Row-`2` outstanding claims: `90 - 50 = 40`. -/
theorem monoC_outstanding_row2 :
    chainComplete 2 monoC 2 2 - monoC 2 (2 - 2) = 40 := by
  rw [monoC_ultimate_row2]
  change (90 : ℝ) - 50 = 40
  norm_num

/-- Row-`1` outstanding claims: `144 - 120 = 24`. -/
theorem monoC_outstanding_row1 :
    chainComplete 2 monoC 1 2 - monoC 1 (2 - 1) = 24 := by
  rw [monoC_ultimate_row1]
  change (144 : ℝ) - 120 = 24
  norm_num

/-- Row-`2` outstanding claims are nonnegative, via the theorem. -/
theorem monoC_outstanding_nonneg_row2 :
    0 ≤ chainComplete 2 monoC 2 2 - monoC 2 (2 - 2) :=
  sub_nonneg.mpr monoC_bound_row2

/-- Row-`1` outstanding claims are nonnegative, via the theorem. -/
theorem monoC_outstanding_nonneg_row1 :
    0 ≤ chainComplete 2 monoC 1 2 - monoC 1 (2 - 1) :=
  sub_nonneg.mpr monoC_bound_row1

/-- A decreasing-row triangle: row `0` falls from `100` to `50`. -/
def decC : ℕ → ℕ → ℝ
  | 0, 0 => 100
  | 0, 1 => 50
  | 1, 0 => 100
  | _, _ => 0

/-- Selected factor below one: `50 / 100 = 1 / 2`. -/
theorem decC_factor0 : chainFactor 1 decC 0 = 1 / 2 := by
  rw [chainFactor]
  change (∑ i ∈ Finset.range 1, decC i 1) / (∑ i ∈ Finset.range 1, decC i 0)
    = 1 / 2
  simp only [Finset.sum_range_one, decC]
  norm_num

/-- Ultimate forecast for the decreasing triangle: `100 * (1 / 2) = 50`. -/
theorem decC_ultimate : chainComplete 1 decC 1 1 = 50 := by
  change chainComplete 1 decC 1 (0 + 1) = _
  simp only [chainComplete, (by decide : ¬ 1 + (0 + 1) ≤ 1), ↓reduceIte]
  rw [decC_factor0]
  change (100 : ℝ) * (1 / 2) = 50
  norm_num

/-- Without monotonicity the conclusion fails: `100 ≤ 50` is false. -/
theorem decC_conclusion_fails : ¬ decC 1 (1 - 1) ≤ chainComplete 1 decC 1 1 := by
  rw [decC_ultimate]
  change ¬ (100 : ℝ) ≤ 50
  norm_num

/-- With `n = 0` the completion is the identity on the first column. -/
theorem complete_zero (C : ℕ → ℕ → ℝ) (i : ℕ) :
    chainComplete 0 C i 0 = C i 0 := rfl

/-- With `n = 0` the row-`2` cell is preserved: `50`. -/
example : chainComplete 0 monoC 2 0 = 50 := rfl

/-- With `n = 0` the monotonicity bound holds with vacuous denominators. -/
example : monoC 2 (0 - 2) ≤ chainComplete 0 monoC 2 0 :=
  le_chainComplete 0 monoC monoC_nonneg (fun i j h => monoC_mono i j (by omega))
    (fun j hj => absurd hj (by omega)) 2

end MathFinTest
