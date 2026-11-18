/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Chain-ladder product formula checks

Hand-checkable evaluations of `MathFin.chainFactor` and `MathFin.chainComplete` on
the triangle with rows `100, 150, 180 / 80, 120 / 50` and `n = 2`: selected factors
`3 / 2` and `6 / 5`, forecasts `144`, `75` and `90`, the degenerate `n = 0` case,
the one-row final factor, and preservation of observed cells.
-/

namespace MathFinTest

open MathFin

/-- Hand-checkable run-off triangle: row `0` holds `100, 150, 180`, row `1` holds
`80, 120`, and row `2` holds `50`. Every other cell is `0`. -/
def triC : ℕ → ℕ → ℝ
  | 0, 0 => 100
  | 0, 1 => 150
  | 0, 2 => 180
  | 1, 0 => 80
  | 1, 1 => 120
  | 2, 0 => 50
  | _, _ => 0

/-- First selected factor: `(150 + 120) / (100 + 80) = 3 / 2`. -/
theorem triC_factor0 : chainFactor 2 triC 0 = 3 / 2 := by
  rw [chainFactor]
  change (∑ i ∈ Finset.range 2, triC i 1) / (∑ i ∈ Finset.range 2, triC i 0) = 3 / 2
  simp only [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  change ((150 + 120 : ℝ) / (100 + 80)) = 3 / 2
  norm_num

/-- Final factor: `180 / 150 = 6 / 5`. Only row `0` is observed in both columns, so
each sum has a single term (the one-row final factor case). -/
theorem triC_factor1 : chainFactor 2 triC 1 = 6 / 5 := by
  rw [chainFactor]
  change (∑ i ∈ Finset.range 1, triC i 2) / (∑ i ∈ Finset.range 1, triC i 1) = 6 / 5
  simp only [Finset.sum_range_one]
  change ((180 : ℝ) / 150) = 6 / 5
  norm_num

/-- The final factor is one-row: both sums range over `range 1`. -/
example : chainFactor 2 triC 1 = triC 0 2 / triC 0 1 := by
  rw [chainFactor]
  change (∑ i ∈ Finset.range 1, triC i 2) / (∑ i ∈ Finset.range 1, triC i 1) = _
  simp only [Finset.sum_range_one]

/-- Forecast cell `(1, 2)`: `120 * (6 / 5) = 144`. -/
example : chainComplete 2 triC 1 2 = 144 := by
  change chainComplete 2 triC 1 (1 + 1) = _
  simp only [chainComplete, show (¬ 1 + (1 + 1) ≤ 2) from by decide, ↓reduceIte]
  change chainComplete 2 triC 1 (0 + 1) * chainFactor 2 triC 1 = _
  simp only [chainComplete, show (1 + (0 + 1) ≤ 2) from by decide, ↓reduceIte]
  rw [triC_factor1]
  change (120 : ℝ) * (6 / 5) = 144
  norm_num

/-- Forecast cell `(2, 1)`: `50 * (3 / 2) = 75`. -/
example : chainComplete 2 triC 2 1 = 75 := by
  change chainComplete 2 triC 2 (0 + 1) = _
  simp only [chainComplete, show (¬ 2 + (0 + 1) ≤ 2) from by decide, ↓reduceIte]
  rw [triC_factor0]
  change (50 : ℝ) * (3 / 2) = 75
  norm_num

/-- Forecast cell `(2, 2)`: `(50 * (3 / 2)) * (6 / 5) = 90`. -/
example : chainComplete 2 triC 2 2 = 90 := by
  change chainComplete 2 triC 2 (1 + 1) = _
  simp only [chainComplete, show (¬ 2 + (1 + 1) ≤ 2) from by decide, ↓reduceIte]
  change chainComplete 2 triC 2 (0 + 1) * chainFactor 2 triC 1 = _
  simp only [chainComplete, show (¬ 2 + (0 + 1) ≤ 2) from by decide, ↓reduceIte]
  rw [triC_factor0, triC_factor1]
  change ((50 : ℝ) * (3 / 2)) * (6 / 5) = 90
  norm_num

/-- With `n = 0` only cell `(0, 0)` is observed; it is preserved. -/
example (C : ℕ → ℕ → ℝ) : chainComplete 0 C 0 0 = C 0 0 :=
  chainComplete_eq 0 C 0 0 (by decide)

/-- With `n = 0` the development factors range over no rows, so the factor is
`0 / 0 = 0` and every unobserved forecast is `0`. -/
example : chainComplete 0 triC 0 1 = 0 := by
  have hfac : chainFactor 0 triC 0 = 0 := by
    rw [chainFactor]
    change (∑ i ∈ Finset.range 0, triC i 1) / (∑ i ∈ Finset.range 0, triC i 0) = 0
    simp
  change chainComplete 0 triC 0 (0 + 1) = _
  simp [chainComplete, show (¬ 0 + (0 + 1) ≤ 0) from by decide, hfac]

/-- Observed cells are preserved: `(0, 0)`, `(0, 2)` and `(1, 1)`. -/
example : chainComplete 2 triC 0 0 = 100 := by
  rw [chainComplete_eq 2 triC 0 0 (by decide)]
  rfl

example : chainComplete 2 triC 0 2 = 180 := by
  rw [chainComplete_eq 2 triC 0 2 (by decide)]
  rfl

example : chainComplete 2 triC 1 1 = 120 := by
  rw [chainComplete_eq 2 triC 1 1 (by decide)]
  rfl

end MathFinTest
