/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Average-uniqueness bound for overlapping-label samples

López de Prado (*Advances in Financial Machine Learning*, ch. 4) measures how
much an overlapping-label observation `i` (with span `[t0 i, t1 i]`) overlaps
its peers via the concurrency `c_t = Σᵢ 1[t ∈ [t0 i, t1 i]]` and the
per-observation uniqueness `u_{t,i} = 1[t ∈ span i] / c_t`.

This file states both over a finite index type `ι` and proves the basic bound
used to justify uniqueness-weighted sampling: whenever `i`'s span actually
contains `t`, `u_{t,i} ∈ (0, 1]`.

## Main results

* `concurrency_pos`: `c_t > 0` whenever some span contains `t`.
* `uniqueness_mem_Ioc`: `u_{t,i} ∈ (0, 1]` whenever `t ∈ span i`.
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} [Fintype ι]

/-- Concurrency at time `t`: the number of observations whose span
`[t0 i, t1 i]` contains `t`. -/
noncomputable def concurrency (t0 t1 : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if t ∈ Set.Icc (t0 i) (t1 i) then (1 : ℝ) else 0

/-- Per-observation uniqueness at time `t`: `1 / c_t` if `i`'s span contains
`t`, else `0`. -/
noncomputable def uniqueness (t0 t1 : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  (if t ∈ Set.Icc (t0 i) (t1 i) then (1 : ℝ) else 0) / concurrency t0 t1 t

theorem one_le_concurrency (t0 t1 : ι → ℝ) {t : ℝ} {i : ι}
    (hi : t ∈ Set.Icc (t0 i) (t1 i)) : 1 ≤ concurrency t0 t1 t := by
  have h := Finset.single_le_sum
    (f := fun j ↦ if t ∈ Set.Icc (t0 j) (t1 j) then (1 : ℝ) else 0)
    (fun j _ ↦ by split <;> norm_num) (Finset.mem_univ i)
  rwa [if_pos hi] at h

theorem concurrency_pos (t0 t1 : ι → ℝ) {t : ℝ} {i : ι}
    (hi : t ∈ Set.Icc (t0 i) (t1 i)) : 0 < concurrency t0 t1 t :=
  zero_lt_one.trans_le (one_le_concurrency t0 t1 hi)

/-- The headline bound: an observation whose span contains `t` has uniqueness
strictly positive and at most `1`. -/
theorem uniqueness_mem_Ioc (t0 t1 : ι → ℝ) {t : ℝ} {i : ι}
    (hi : t ∈ Set.Icc (t0 i) (t1 i)) : uniqueness t0 t1 t i ∈ Set.Ioc (0 : ℝ) 1 := by
  have hpos := concurrency_pos t0 t1 hi
  refine ⟨?_, ?_⟩
  · rw [uniqueness, if_pos hi]
    exact div_pos one_pos hpos
  · rw [uniqueness, if_pos hi, div_le_one hpos]
    exact one_le_concurrency t0 t1 hi

end MathFin
