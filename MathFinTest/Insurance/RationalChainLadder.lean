/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Rational chain-ladder evaluator checks

Hand-checkable evaluations of `MathFin.chainFactorRat?` and
`MathFin.chainCompleteRat?` on the rational triangle with rows
`100, 150, 180 / 120, 170 / 90` and `n = 2`: selected factors `16 / 11` and
`6 / 5`, forecasts `204`, `1440 / 11` and `1728 / 11` decoding to the real
completion, denominator failure returning `none`, and out-of-horizon rejection.
-/

namespace MathFinTest

open MathFin

/-- Rational run-off triangle: row `0` holds `100, 150, 180`, row `1` holds
`120, 170`, and row `2` holds `90`. Every other cell is `0`. -/
def triQRat : ℕ → ℕ → ℚ
  | 0, 0 => 100
  | 0, 1 => 150
  | 0, 2 => 180
  | 1, 0 => 120
  | 1, 1 => 170
  | 2, 0 => 90
  | _, _ => 0

/-- First selected factor: `(150 + 170) / (100 + 120) = 16 / 11`. -/
theorem triQRat_factor0 : chainFactorRat? 2 triQRat 0 = some (16 / 11) := by
  rw [chainFactorRat?]
  change (if (∑ i ∈ Finset.range 2, triQRat i 0) = 0 then none
    else some ((∑ i ∈ Finset.range 2, triQRat i 1)
      / ∑ i ∈ Finset.range 2, triQRat i 0)) = _
  have hne : (100 + 120 : ℚ) ≠ 0 := by norm_num
  simp only [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, triQRat, hne, ↓reduceIte]
  congr 1
  norm_num

/-- Final factor: `180 / 150 = 6 / 5`. Only row `0` is observed in both columns, so
each sum has a single term (the one-row final factor case). -/
theorem triQRat_factor1 : chainFactorRat? 2 triQRat 1 = some (6 / 5) := by
  rw [chainFactorRat?]
  change (if (∑ i ∈ Finset.range 1, triQRat i 1) = 0 then none
    else some ((∑ i ∈ Finset.range 1, triQRat i 2)
      / ∑ i ∈ Finset.range 1, triQRat i 1)) = _
  have hne : (150 : ℚ) ≠ 0 := by norm_num
  simp only [Finset.sum_range_one, triQRat, hne, ↓reduceIte]
  congr 1
  norm_num

/-- Forecast cell `(1, 2)`: `170 * (6 / 5) = 204`. -/
theorem triQRat_fc12 : chainCompleteRat? 2 triQRat 1 2 = some 204 := by
  change chainCompleteRat? 2 triQRat 1 (1 + 1) = _
  simp only [chainCompleteRat?, show (¬ 1 + (1 + 1) ≤ 2) from by decide,
    show (1 + (0 + 1) ≤ 2) from by decide, ↓reduceIte,
    show triQRat 1 (0 + 1) = 170 from rfl, triQRat_factor1]
  change some ((170 : ℚ) * (6 / 5)) = some 204
  congr 1
  norm_num

/-- Forecast cell `(2, 1)`: `90 * (16 / 11) = 1440 / 11`. -/
theorem triQRat_fc21 : chainCompleteRat? 2 triQRat 2 1 = some (1440 / 11) := by
  change chainCompleteRat? 2 triQRat 2 (0 + 1) = _
  simp only [chainCompleteRat?, show (¬ 2 + (0 + 1) ≤ 2) from by decide, ↓reduceIte,
    triQRat, triQRat_factor0]
  change some ((90 : ℚ) * (16 / 11)) = some (1440 / 11)
  congr 1
  norm_num

/-- Forecast cell `(2, 2)`: `(1440 / 11) * (6 / 5) = 1728 / 11`. -/
theorem triQRat_fc22 : chainCompleteRat? 2 triQRat 2 2 = some (1728 / 11) := by
  change chainCompleteRat? 2 triQRat 2 (1 + 1) = _
  simp only [chainCompleteRat?, show (¬ 2 + (1 + 1) ≤ 2) from by decide,
    show (¬ 2 + (0 + 1) ≤ 2) from by decide, ↓reduceIte, triQRat, triQRat_factor0,
    triQRat_factor1]
  change some (((90 : ℚ) * (16 / 11)) * (6 / 5)) = some (1728 / 11)
  congr 1
  norm_num

/-- Every in-horizon denominator sum of `triQRat` is nonzero. -/
theorem triQRat_hdenom :
    ∀ j, j < 2 → (∑ i ∈ Finset.range (2 - j), triQRat i j) ≠ 0 := by
  intro j hj
  have hj2 : j = 0 ∨ j = 1 := by omega
  rcases hj2 with rfl | rfl
  · simp only [show (2 - 0 : ℕ) = 2 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, triQRat]
    norm_num
  · simp only [show (2 - 1 : ℕ) = 1 from rfl, Finset.sum_range_one, triQRat]
    norm_num

/-- The rational forecast `(2, 2)` decodes to the real completion. -/
example : ∃ q : ℚ, chainCompleteRat? 2 triQRat 2 2 = some q
    ∧ ((q : ℝ)) = chainComplete 2 (fun a b => ((triQRat a b : ℚ) : ℝ)) 2 2 :=
  cast_chainCompleteRat?_some 2 triQRat triQRat_hdenom 2 2 (by decide)

/-- The decoded forecast `(1, 2)` equals the real forecast `204`. -/
example : chainComplete 2 (fun a b => ((triQRat a b : ℚ) : ℝ)) 1 2 = 204 := by
  obtain ⟨q, hq, hcast⟩ :=
    cast_chainCompleteRat?_some 2 triQRat triQRat_hdenom 1 2 (by decide)
  rw [triQRat_fc12] at hq
  have h2 : q = 204 := by simpa using hq.symm
  subst h2
  rw [← hcast]
  norm_num

/-- The decoded forecast `(2, 1)` equals the real forecast `1440 / 11`. -/
example : chainComplete 2 (fun a b => ((triQRat a b : ℚ) : ℝ)) 2 1 = 1440 / 11 := by
  obtain ⟨q, hq, hcast⟩ :=
    cast_chainCompleteRat?_some 2 triQRat triQRat_hdenom 2 1 (by decide)
  rw [triQRat_fc21] at hq
  have h2 : q = 1440 / 11 := by simpa using hq.symm
  subst h2
  rw [← hcast]
  norm_num

/-- The decoded forecast `(2, 2)` equals the real forecast `1728 / 11`. -/
example : chainComplete 2 (fun a b => ((triQRat a b : ℚ) : ℝ)) 2 2 = 1728 / 11 := by
  obtain ⟨q, hq, hcast⟩ :=
    cast_chainCompleteRat?_some 2 triQRat triQRat_hdenom 2 2 (by decide)
  rw [triQRat_fc22] at hq
  have h2 : q = 1728 / 11 := by simpa using hq.symm
  subst h2
  rw [← hcast]
  norm_num

/-- A triangle whose column-`0` denominator sum vanishes: the two rows cancel. -/
def triQZero : ℕ → ℕ → ℚ
  | 0, 0 => 100
  | 1, 0 => -100
  | _, _ => 0

/-- The column-`0` denominator sum of `triQZero` is zero. -/
theorem triQZero_denom0 : (∑ a ∈ Finset.range (2 - 0), triQZero a 0) = 0 := by
  simp only [show (2 - 0 : ℕ) = 2 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, triQZero]
  norm_num

/-- A zero denominator makes the completion `none`. -/
example : chainCompleteRat? 2 triQZero 2 2 = none :=
  chainCompleteRat?_none_of_denom_eq_zero 2 triQZero 2 2 0 (by decide) (by decide)
    triQZero_denom0

/-- Past the horizon the factor ranges over no rows, so its denominator is zero. -/
theorem triQRat_empty_denom : (∑ a ∈ Finset.range (2 - 2), triQRat a 2) = 0 := by
  simp only [show (2 - 2 : ℕ) = 0 from rfl, Finset.sum_range_zero]

/-- Past the horizon the evaluator rejects. -/
example : chainCompleteRat? 2 triQRat 0 3 = none :=
  chainCompleteRat?_none_of_denom_eq_zero 2 triQRat 0 3 2 (by decide) (by decide)
    triQRat_empty_denom

/-- Observed cells are preserved: `(0, 2)`. -/
example : chainCompleteRat? 2 triQRat 0 2 = some 180 := by
  change chainCompleteRat? 2 triQRat 0 (1 + 1) = _
  simp only [chainCompleteRat?, show (0 + (1 + 1) ≤ 2) from by decide, ↓reduceIte,
    show triQRat 0 (1 + 1) = 180 from rfl]

/-- With `n = 0` only cell `(0, 0)` is observed; it is preserved. -/
example (C : ℕ → ℕ → ℚ) : chainCompleteRat? 0 C 0 0 = some (C 0 0) := rfl

/-- With `n = 0` every factor denominator is an empty sum, so unobserved forecasts
are `none`. -/
example : chainCompleteRat? 0 triQRat 0 1 = none := by
  change chainCompleteRat? 0 triQRat 0 (0 + 1) = _
  simp only [chainCompleteRat?, show (¬ 0 + (0 + 1) ≤ 0) from by decide, ↓reduceIte]
  have hfac : chainFactorRat? 0 triQRat 0 = none := by
    simp [chainFactorRat?]
  simp only [hfac, Option.bind_some, Option.map_none]

end MathFinTest
