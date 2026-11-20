/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Adam Kiezun
-/
module

public import MathFin

/-!
# Using the library: a chain-ladder reserve, computed exactly and certified

A worked use of the library from outside it, the way a reserving actuary completes a run-off
triangle. A triangle of cumulative paid claims is recorded at calendar date `3`, one row per
accident year. This file

1. records the triangle as rational data;
2. computes the chain-ladder ultimates exactly, by evaluation over `ℚ` (`ultimates_computed`);
3. carries them to the real chain ladder of the library (`ultimates`), with no hypothesis to
   check by hand, since a value the evaluator returns certifies itself;
4. reads the youngest year's ultimate as Mack's prediction from its first development year
   (`youngest_prediction`), and totals the reserve (`reserve`).

## What the library supplies

* `MathFin.chainCompleteRat?`: the exact chain-ladder completion of a rational triangle.
* `MathFin.chainComplete_eq_of_chainCompleteRat?_eq_some`: a value it returns is the real
  completion `chainComplete` of the cast triangle.
* `MathFin.chainPrediction_eq_of_chainCompleteRat?_eq_some`: on an unobserved cell that value is
  the prediction `chainPrediction` by the selected factors. Under Mack's model with these factors
  the prediction is the conditional expectation of the ultimate (`MathFin.IsMackRow.condExp_eq`).

## What it does not

The selected factors are point estimates. That they estimate Mack's factors without bias, the
standard error of the reserve, tail factors beyond the last development year and discounting are
outside this file and outside the library.

## Source

The shape of the file follows the bootstrapping example
(`MathFinExamples/Applications/Bootstrapping.lean`); the exact evaluator is Adam Kiezun's (#524).
The claim amounts below are illustrative.
-/

@[expose] public section

namespace MathFin.Examples.ChainLadderReserve

open MathFin

/-- An illustrative triangle of cumulative paid claims at calendar date `3`: `triangle i j` is
accident year `i` after `j` development years, observed when `i + j ≤ 3`; the other cells are
unused and set to `0`. -/
def triangle : ℕ → ℕ → ℚ
  | 0, 0 => 1000 | 0, 1 => 1500 | 0, 2 => 1750 | 0, 3 => 1800
  | 1, 0 => 1100 | 1, 1 => 1680 | 1, 2 => 1960
  | 2, 0 => 1200 | 2, 1 => 1750
  | 3, 0 => 1300
  | _, _ => 0

/-- The triangle in `ℝ`, the input of the library's chain ladder. -/
noncomputable abbrev triangleℝ (i j : ℕ) : ℝ := triangle i j

/-- **The ultimates, computed exactly.** The selected factors are `493/330`, `7/6` and `36/35`. -/
theorem ultimates_computed :
    chainCompleteRat? 3 triangle 0 3 = some 1800 ∧ chainCompleteRat? 3 triangle 1 3 = some 2016 ∧
      chainCompleteRat? 3 triangle 2 3 = some 2100 ∧
      chainCompleteRat? 3 triangle 3 3 = some (25636 / 11) := by
  decide +kernel

/-- **The real chain-ladder ultimates**, certified by the computation. -/
theorem ultimates :
    chainComplete 3 triangleℝ 0 3 = 1800 ∧ chainComplete 3 triangleℝ 1 3 = 2016 ∧
      chainComplete 3 triangleℝ 2 3 = 2100 ∧ chainComplete 3 triangleℝ 3 3 = 25636 / 11 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := ultimates_computed
  exact ⟨(chainComplete_eq_of_chainCompleteRat?_eq_some h₀).trans (by norm_num),
    (chainComplete_eq_of_chainCompleteRat?_eq_some h₁).trans (by norm_num),
    (chainComplete_eq_of_chainCompleteRat?_eq_some h₂).trans (by norm_num),
    (chainComplete_eq_of_chainCompleteRat?_eq_some h₃).trans (by norm_num)⟩

/-- **The youngest year as Mack's prediction**: its ultimate is the prediction from its first
development year, `1300 · (493/330) · (7/6) · (36/35)`, by the selected factors. -/
theorem youngest_prediction :
    chainPrediction (chainFactor 3 triangleℝ) (triangleℝ 3) 3 0 = 25636 / 11 :=
  (chainPrediction_eq_of_chainCompleteRat?_eq_some (by norm_num)
    ultimates_computed.2.2.2).trans (by norm_num)

/-- **The reserve**: the predicted outstanding claims, the sum over accident years of the
ultimate less the latest observed value, is `15802/11 ≈ 1436.55`. -/
theorem reserve :
    ∑ i ∈ Finset.range 4, (chainComplete 3 triangleℝ i 3 - triangleℝ i (3 - i)) = 15802 / 11 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := ultimates
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h₀, h₁, h₂, h₃,
    triangleℝ, triangle]
  norm_num

end MathFin.Examples.ChainLadderReserve
