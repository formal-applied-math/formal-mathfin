/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Finite liquidation tests

Tests for the finite-horizon liquidation unique minimizer.
Each test obtains its witness from
`existsUnique_minimizer_liquidationCost` and pins it down through the
endpoint's clauses: the cost of the forced path for `N = 1`, the linear
path for zero risk, and a positive-risk value beating a suboptimal path.
-/

namespace MathFinTest

open MathFin

/-- For `N = 1` the endpoint's path has the directly computed cost of
the only feasible path `(X0, 0)`. -/
theorem minimizer_N1_forced (Δ η c X0 : ℝ) (hΔ : 0 < Δ) (hη : 0 < η)
    (hc : 0 ≤ c) :
    ∃ x : Fin (1 + 1) → ℝ, x 0 = X0 ∧ x (Fin.last 1) = 0
      ∧ liquidationCost 1 Δ η c x
        = Δ * (η * (X0 / Δ) ^ 2 + c * X0 ^ 2) := by
  obtain ⟨x, hx0, hxN, _, _, _⟩ :=
    existsUnique_minimizer_liquidationCost 1 (by omega) Δ η c X0 hΔ hη hc
  have pcast : (0 : Fin 1).castSucc = (0 : Fin (1 + 1)) := by decide
  have psucc : (0 : Fin 1).succ = Fin.last 1 := by decide
  refine ⟨x, hx0, hxN, ?_⟩
  simp only [liquidationCost, Fin.sum_univ_one, pcast, psucc, hx0, hxN]
  ring

/-- With `c = 0` (`N = 2`, `Δ = η = 1`, `X0 = 2`) the endpoint's path is
the linear path `(2, 1, 0)`: stationarity plus the endpoints force it. -/
theorem minimizer_zero_risk_linear :
    ∃ x : Fin (2 + 1) → ℝ, x 0 = 2 ∧ x (Fin.last 2) = 0
      ∧ (∀ j : Fin (2 + 1), x j = 2 * (1 - (j.val : ℝ) / 2)) := by
  obtain ⟨x, hx0, hxN, _, hstat, _⟩ :=
    existsUnique_minimizer_liquidationCost 2 (by omega) 1 1 0 2
      (by norm_num) (by norm_num) (by norm_num)
  have hstat1 : -(x 0) + 2 * x 1 - x (Fin.last 2)
      + (0 * 1 ^ 2 / 1) * x 1 = 0 :=
    hstat (⟨1, by omega⟩ : Fin 2) (by decide)
  have hx1 : x 1 = 1 := by
    rw [hx0, hxN] at hstat1
    norm_num at hstat1
    linarith
  have n0 : (0 : Fin (2 + 1)).val = 0 := by decide
  have n1 : (1 : Fin (2 + 1)).val = 1 := by decide
  have nlast : (Fin.last 2).val = 2 := by decide
  refine ⟨x, hx0, hxN, ?_⟩
  intro j
  have hj2 := j.2
  have hvo : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hvo with h0 | h1v | h2
  · have hj0 : j = 0 := Fin.ext_iff.mpr (by rw [h0, n0])
    rw [hj0, hx0, n0]
    norm_num
  · have hj1 : j = 1 := Fin.ext_iff.mpr (by rw [h1v, n1])
    rw [hj1, hx1, n1]
    norm_num
  · have hjL : j = Fin.last 2 := Fin.ext_iff.mpr (by rw [h2, nlast])
    rw [hjL, hxN, nlast]
    norm_num

/-- Hold-then-dump path for the positive-risk test: `(3, 3, 0)`. -/
def subPathPos : Fin (2 + 1) → ℝ :=
  fun j => if j.val = 0 then 3 else if j.val = 1 then 3 else 0

/-- With `c = 1` (`N = 2`, `Δ = η = 1`, `X0 = 3`) the endpoint's path
satisfies `x 1 = 1` by stationarity, has cost `15`, and beats the
hold-then-dump path (cost `27`) by minimality. -/
theorem minimizer_pos_risk_value :
    ∃ x : Fin (2 + 1) → ℝ, x 0 = 3 ∧ x (Fin.last 2) = 0
      ∧ x 1 = 1 ∧ liquidationCost 2 1 1 1 x = 15
      ∧ liquidationCost 2 1 1 1 x
        < liquidationCost 2 1 1 1 subPathPos := by
  obtain ⟨x, hx0, hxN, hopt, hstat, _⟩ :=
    existsUnique_minimizer_liquidationCost 2 (by omega) 1 1 1 3
      (by norm_num) (by norm_num) (by norm_num)
  have hstat1 : -(x 0) + 2 * x 1 - x (Fin.last 2)
      + (1 * 1 ^ 2 / 1) * x 1 = 0 :=
    hstat (⟨1, by omega⟩ : Fin 2) (by decide)
  have hx1 : x 1 = 1 := by
    rw [hx0, hxN] at hstat1
    norm_num at hstat1
    linarith
  have p00 : (0 : Fin 2).castSucc = (0 : Fin (2 + 1)) := by decide
  have p01 : (0 : Fin 2).succ = (1 : Fin (2 + 1)) := by decide
  have p10 : (1 : Fin 2).castSucc = (1 : Fin (2 + 1)) := by decide
  have p11 : (1 : Fin 2).succ = Fin.last 2 := by decide
  have hcx : liquidationCost 2 1 1 1 x = 15 := by
    simp only [liquidationCost, Fin.sum_univ_two, p00, p01, p10, p11,
      hx0, hx1, hxN]
    norm_num
  have h20 : (2 : ℕ) ≠ 0 := by decide
  have h21 : (2 : ℕ) ≠ 1 := by decide
  have w00 : subPathPos (0 : Fin 2).castSucc = 3 := by simp [subPathPos]
  have w01 : subPathPos (0 : Fin 2).succ = 3 := by simp [subPathPos]
  have w10 : subPathPos (1 : Fin 2).castSucc = 3 := by simp [subPathPos]
  have w11 : subPathPos (1 : Fin 2).succ = 0 := by
    simp [subPathPos, h20, h21]
  have hcw : liquidationCost 2 1 1 1 subPathPos = 27 := by
    simp only [liquidationCost, Fin.sum_univ_two]
    rw [w00, w01, w10, w11]
    norm_num
  have hw0 : subPathPos 0 = 3 := by simp [subPathPos]
  have hwN : subPathPos (Fin.last 2) = 0 := by
    simp [subPathPos, h20, h21]
  have hle := hopt subPathPos hw0 hwN
  refine ⟨x, hx0, hxN, hx1, hcx, ?_⟩
  linarith

end MathFinTest
