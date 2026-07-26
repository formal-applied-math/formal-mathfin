/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

-- pointers: MathFin/Performance/RatiosExtended.lean
-- main-module: MathFin/Performance/PerformanceRatiosExtended.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-performance-upside_capture
-- source-issue: 162
-- new-defs: upCapture

/-!
Upside-capture ratio and its homogeneity.
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open scoped BigOperators

/-- Upside-capture ratio: sum of portfolio returns over `up` periods divided by sum of benchmark returns over `up` periods. -/
noncomputable def upCapture {S : Type*} (up : Finset S) (p : S → ℝ) (b : S → ℝ) : ℝ :=
  (∑ i ∈ up, p i) / (∑ i ∈ up, b i)

example : upCapture ({0,1,2} : Finset ℕ) (fun i => (i : ℝ)) (fun i => (i : ℝ) + 1) = (1/2 : ℝ) := by
  norm_num [upCapture]

theorem upCapture_smul {S : Type*} (up : Finset S) (p : S → ℝ) (b : S → ℝ) (c : ℝ)
    (h : ∑ i ∈ up, b i ≠ 0) : upCapture up (c • p) b = c * upCapture up p b := by
  dsimp [upCapture]
  field_simp [h]
  simp [Finset.mul_sum]

end MathFin
