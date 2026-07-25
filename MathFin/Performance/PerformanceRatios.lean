/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

-- pointers: MathFin/Performance/RatiosExtended.lean
-- main-module: MathFin/Performance/PerformanceRatios.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-performance-gain_to_pain
-- source-issue: 161
-- new-defs: gainToPain

/-!
The gain-to-pain ratio is nonnegative when defined.
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The gain-to-pain ratio for returns r over a finite set S.
    Defined as (sum of positive returns) / (sum of absolute values of negative returns). -/
noncomputable def gainToPain (S : Type*) (finset_S : Finset S) (r : S → ℝ) : ℝ :=
  (∑ s ∈ finset_S, max (r s) 0) / (∑ s ∈ finset_S, max (-r s) 0)

@[simp]
example : gainToPain (Fin 1) (Finset.univ : Finset (Fin 1)) (fun _ => -1) = 0 := by
  unfold gainToPain; norm_num

@[simp]
example : gainToPain (Fin 2) (Finset.univ : Finset (Fin 2)) (fun s => if s = 0 then 1 else -1) = 1 := by
  unfold gainToPain; norm_num

theorem gainToPain_nonneg_of_denom_pos {S : Type*} (finset_S : Finset S) (r : S → ℝ)
    (h : 0 < ∑ s ∈ finset_S, max (-r s) 0) : 0 ≤ gainToPain S finset_S r := by
  unfold gainToPain
  refine div_nonneg ?_ (le_of_lt h)
  exact Finset.sum_nonneg fun s _ => le_max_right _ _

end MathFin
