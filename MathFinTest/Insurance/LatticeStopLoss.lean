/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
import MathFin

/-!
# Lattice stop-loss recurrence tests

Concrete checks of `MathFin.stopLoss_succ` on one-point (finite uniform) spaces with explicit
constant severities: mass at the deductible, zero loss, a nonunit layer width, and an
off-lattice rejection showing the lattice hypothesis cannot be dropped.
-/

open MeasureTheory

namespace MathFinTest

/-- Mass at the deductible: `S ≡ 2`, `h = 1`, `j = 2`. -/
theorem stopLoss_mass_at_deductible :
    ∫ ω : Unit, max ((fun _ => (2 : ℝ)) ω - ((2 + 1 : ℕ) : ℝ) * 1) 0 ∂(Measure.dirac ())
      = 0 := by
  have h := MathFin.stopLoss_succ Unit (Measure.dirac ()) (fun _ => (2 : ℝ))
    measurable_const (integrable_const 2)
    (Filter.Eventually.of_forall fun _ => show (0 : ℝ) ≤ 2 by norm_num)
    1 zero_lt_one
    (Filter.Eventually.of_forall fun _ =>
      ⟨2, by norm_num⟩)
    2
  rw [h]
  have hSL : ∫ ω : Unit, max ((fun _ => (2 : ℝ)) ω - ((2 : ℕ) : ℝ) * 1) 0
      ∂(Measure.dirac ()) = 0 := by
    simp only [integral_dirac]
    rw [show ((2 : ℕ) : ℝ) * 1 = (2 : ℝ) by norm_num]
    exact max_eq_right (by norm_num)
  have hP : (Measure.dirac ()).real {ω : Unit | ((2 : ℕ) : ℝ) * 1 < (fun _ => (2 : ℝ)) ω}
      = 0 := by
    change ((Measure.dirac ()) {ω : Unit | ((2 : ℕ) : ℝ) * 1 < (fun _ => (2 : ℝ)) ω}).toReal
      = 0
    rw [Measure.dirac_apply]
    have hmem : (()) ∉ {ω : Unit | ((2 : ℕ) : ℝ) * 1 < (fun _ => (2 : ℝ)) ω} := by
      simp only [Set.mem_ofPred_eq]
      norm_num
    rw [Set.indicator_of_notMem hmem]
    simp
  rw [hSL, hP]
  norm_num

/-- Zero loss: `S ≡ 0`, `h = 1`, `j = 0`. -/
theorem stopLoss_zero_loss :
    ∫ ω : Unit, max ((fun _ => (0 : ℝ)) ω - ((0 + 1 : ℕ) : ℝ) * 1) 0 ∂(Measure.dirac ())
      = 0 := by
  have h := MathFin.stopLoss_succ Unit (Measure.dirac ()) (fun _ => (0 : ℝ))
    measurable_const (integrable_const 0)
    (Filter.Eventually.of_forall fun _ => show (0 : ℝ) ≤ 0 by norm_num)
    1 zero_lt_one
    (Filter.Eventually.of_forall fun _ =>
      ⟨0, by norm_num⟩)
    0
  rw [h]
  have hSL : ∫ ω : Unit, max ((fun _ => (0 : ℝ)) ω - ((0 : ℕ) : ℝ) * 1) 0
      ∂(Measure.dirac ()) = 0 := by
    simp only [integral_dirac]
    rw [show ((0 : ℕ) : ℝ) * 1 = (0 : ℝ) by norm_num, sub_zero]
    exact max_eq_right le_rfl
  have hP : (Measure.dirac ()).real {ω : Unit | ((0 : ℕ) : ℝ) * 1 < (fun _ => (0 : ℝ)) ω}
      = 0 := by
    change ((Measure.dirac ()) {ω : Unit | ((0 : ℕ) : ℝ) * 1 < (fun _ => (0 : ℝ)) ω}).toReal
      = 0
    rw [Measure.dirac_apply]
    have hmem : (()) ∉ {ω : Unit | ((0 : ℕ) : ℝ) * 1 < (fun _ => (0 : ℝ)) ω} := by
      simp only [Set.mem_ofPred_eq]
      norm_num
    rw [Set.indicator_of_notMem hmem]
    simp
  rw [hSL, hP]
  norm_num

/-- Nonunit layer width: `S ≡ 6`, `h = 2`, `j = 1`, so both sides equal `2`. -/
theorem stopLoss_nonunit_layer :
    ∫ ω : Unit, max ((fun _ => (6 : ℝ)) ω - ((1 + 1 : ℕ) : ℝ) * 2) 0 ∂(Measure.dirac ())
      = 2 := by
  have h := MathFin.stopLoss_succ Unit (Measure.dirac ()) (fun _ => (6 : ℝ))
    measurable_const (integrable_const 6)
    (Filter.Eventually.of_forall fun _ => show (0 : ℝ) ≤ 6 by norm_num)
    2 (by norm_num)
    (Filter.Eventually.of_forall fun _ =>
      ⟨3, by norm_num⟩)
    1
  rw [h]
  have hSL : ∫ ω : Unit, max ((fun _ => (6 : ℝ)) ω - ((1 : ℕ) : ℝ) * 2) 0
      ∂(Measure.dirac ()) = 4 := by
    simp only [integral_dirac]
    rw [show ((1 : ℕ) : ℝ) * 2 = (2 : ℝ) by norm_num]
    have hle : (0 : ℝ) ≤ 6 - 2 := by norm_num
    rw [max_eq_left hle]
    norm_num
  have hP : (Measure.dirac ()).real {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (6 : ℝ)) ω}
      = 1 := by
    change ((Measure.dirac ()) {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (6 : ℝ)) ω}).toReal
      = 1
    rw [Measure.dirac_apply]
    have hmem : (()) ∈ {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (6 : ℝ)) ω} := by
      simp only [Set.mem_ofPred_eq]
      norm_num
    rw [Set.indicator_of_mem hmem]
    simp
  rw [hSL, hP]
  norm_num

/-- Off-lattice rejection: `S ≡ 3`, `h = 2`, `j = 1`. The claimed recurrence
`0 = 1 - 2 * 1` is false, so the lattice hypothesis cannot be dropped. -/
theorem stopLoss_off_lattice_false :
    ¬ (∫ ω : Unit, max ((fun _ => (3 : ℝ)) ω - ((1 + 1 : ℕ) : ℝ) * 2) 0
        ∂(Measure.dirac ())
      = ∫ ω : Unit, max ((fun _ => (3 : ℝ)) ω - ((1 : ℕ) : ℝ) * 2) 0
        ∂(Measure.dirac ())
        - 2 * (Measure.dirac ()).real
            {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (3 : ℝ)) ω}) := by
  have hL : ∫ ω : Unit, max ((fun _ => (3 : ℝ)) ω - ((1 + 1 : ℕ) : ℝ) * 2) 0
      ∂(Measure.dirac ()) = 0 := by
    simp only [integral_dirac]
    rw [show ((1 + 1 : ℕ) : ℝ) * 2 = (4 : ℝ) by norm_num]
    exact max_eq_right (by norm_num)
  have hR : ∫ ω : Unit, max ((fun _ => (3 : ℝ)) ω - ((1 : ℕ) : ℝ) * 2) 0
      ∂(Measure.dirac ()) = 1 := by
    simp only [integral_dirac]
    rw [show ((1 : ℕ) : ℝ) * 2 = (2 : ℝ) by norm_num]
    have hle : (0 : ℝ) ≤ 3 - 2 := by norm_num
    rw [max_eq_left hle]
    norm_num
  have hP : (Measure.dirac ()).real
      {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (3 : ℝ)) ω} = 1 := by
    change ((Measure.dirac ())
        {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (3 : ℝ)) ω}).toReal = 1
    rw [Measure.dirac_apply]
    have hmem : (()) ∈ {ω : Unit | ((1 : ℕ) : ℝ) * 2 < (fun _ => (3 : ℝ)) ω} := by
      simp only [Set.mem_ofPred_eq]
      norm_num
    rw [Set.indicator_of_mem hmem]
    simp
  intro hEq
  rw [hL, hR, hP] at hEq
  norm_num at hEq

end MathFinTest
