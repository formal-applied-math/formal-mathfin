/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The uniform partition of `[0, T]`

The library's one equipartition: `unifPart T n k = (k/n)·T`, the `k`-th of the `n + 1` nodes
`0 = t₀ ≤ … ≤ tₙ = T` that cut `[0, T]` into `n` cells of length `T/n`. Every Riemann sum,
Riemann–Stieltjes sum and quadratic-variation sum of the Itô stack runs along it, so the
facts about it are proved here once: monotone, `≤ T`, endpoints, cell length, the telescoping
`∑ (t_{k+1} − t_k) = T`.

`unifPartIcc s t` is the same partition of `[s, t]`, shifted to start at `s`.

## Main definitions and results

* `unifPart`, `unifPartIcc` — the partitions of `[0, T]` and of `[s, t]`.
* `unifPart_mono`, `unifPart_le_T`, `unifPart_zero`, `unifPart_self` — monotone, bounded by
  `T`, and the endpoints `0` and `T`.
* `unifPart_succ_sub`, `unifPart_mesh_sum` — every cell has length `T/n`, and the lengths
  telescope to `T`.
-/

@[expose] public section

namespace MathFin

open scoped NNReal

/-- The uniform partition of `[0, T]`: the `n`-th refinement places its `k`-th node at `kT/n`. -/
noncomputable def unifPart (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n : ℝ≥0) * T

@[simp] lemma unifPart_zero (T : ℝ≥0) (n : ℕ) : unifPart T n 0 = 0 := by simp [unifPart]

/-- The last node of the uniform partition into `n ≠ 0` cells is `T`. -/
lemma unifPart_self (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : unifPart T n n = T := by
  have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp [unifPart, hn0]

/-- The partition points `unifPart T n = (k/n)·T` are monotone in `k`. -/
lemma unifPart_mono (T : ℝ≥0) (n : ℕ) : Monotone (unifPart T n) :=
  fun _ _ hab ↦ by unfold unifPart; gcongr

/-- A partition point `unifPart T n j ≤ T` whenever `j ≤ n`. -/
lemma unifPart_le_T {T : ℝ≥0} {n j : ℕ} (hj : j ≤ n) : unifPart T n j ≤ T := by
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl := Nat.le_zero.1 hj; simp
  · exact (unifPart_mono T n hj).trans_eq (unifPart_self T hn)

/-- The cells of the uniform partition have length `T/n`. -/
lemma unifPart_succ_sub (T : ℝ≥0) (n k : ℕ) :
    ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n := by
  push_cast [unifPart]
  ring

/-- The uniform-partition mesh telescopes: `∑_{k<n} (t_{k+1} − t_k) = T` for `n ≠ 0`. -/
lemma unifPart_mesh_sum (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) := by
  rw [Finset.sum_range_sub (fun k ↦ (unifPart T n k : ℝ)), unifPart_self T hn, unifPart_zero]
  simp

/-! ### The uniform partition of `[s, t]` -/

/-- The uniform partition of `[s, t]` into `n` cells: the library's `unifPart` of `[0, t − s]`,
shifted to start at `s`. -/
noncomputable def unifPartIcc (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := s + unifPart (t - s) n k

lemma unifPartIcc_mono (s t : ℝ≥0) (n : ℕ) : Monotone (unifPartIcc s t n) :=
  fun _ _ hij ↦ by unfold unifPartIcc; gcongr; exact unifPart_mono _ n hij

lemma unifPartIcc_zero (s t : ℝ≥0) (n : ℕ) : unifPartIcc s t n 0 = s := by
  simp [unifPartIcc]

lemma unifPartIcc_self {s t : ℝ≥0} (hst : s ≤ t) {n : ℕ} (hn : n ≠ 0) :
    unifPartIcc s t n n = t := by
  rw [unifPartIcc, unifPart_self _ hn, add_tsub_cancel_of_le hst]

lemma unifPartIcc_succ_sub {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    ((unifPartIcc s t n (k + 1) : ℝ) - unifPartIcc s t n k) = ((t : ℝ) - s) / n := by
  rw [unifPartIcc, unifPartIcc, NNReal.coe_add, NNReal.coe_add, add_sub_add_left_eq_sub,
    unifPart_succ_sub, NNReal.coe_sub hst]

end MathFin
