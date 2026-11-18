/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Finite liquidation tests

Tests for the finite-horizon liquidation unique minimizer:
the forced path for `N = 1`, the linear path for zero risk,
and a numeric comparison against a suboptimal path.
-/

namespace MathFinTest

open MathFin

/-- For `N = 1` the feasible path is forced to `(X0, 0)`. -/
theorem minimizer_N1_forced (Δ η c X0 : ℝ) (hΔ : 0 < Δ) (hη : 0 < η)
    (hc : 0 ≤ c) :
    ∃ x : Fin (1 + 1) → ℝ, x 0 = X0 ∧ x (Fin.last 1) = 0
      ∧ (∀ y : Fin (1 + 1) → ℝ, y 0 = X0 → y (Fin.last 1) = 0 → y = x) := by
  obtain ⟨x, hx0, hxN, _, _, huniq⟩ :=
    existsUnique_minimizer_liquidationCost 1 (by omega) Δ η c X0 hΔ hη hc
  have hcases : ∀ j : Fin (1 + 1), j = 0 ∨ j = Fin.last 1 := by
    intro j
    have hj2 := j.2
    have hvo : j.val = 0 ∨ j.val = 1 := by omega
    cases hvo with
    | inl h0 =>
      exact Or.inl (Fin.ext_iff.mpr (by simp [h0]))
    | inr h1 =>
      exact Or.inr (Fin.ext_iff.mpr (by simp [h1]))
  refine ⟨x, hx0, hxN, ?_⟩
  intro y hy0 hyN
  have hall : ∀ z : Fin (1 + 1) → ℝ, z 0 = X0 → z (Fin.last 1) = 0 →
      z = y := by
    intro z hz0 hzN
    ext i
    cases hcases i with
    | inl hi0 => rw [hi0, hz0, hy0]
    | inr hiL => rw [hiL, hzN, hyN]
  have hymin : ∀ z : Fin (1 + 1) → ℝ, z 0 = X0 → z (Fin.last 1) = 0 →
      liquidationCost 1 Δ η c y ≤ liquidationCost 1 Δ η c z := by
    intro z hz0 hzN
    rw [hall z hz0 hzN]
  exact huniq y hy0 hyN hymin

/-- Linear candidate path for zero risk coefficient. -/
noncomputable def linPathZero (N : ℕ) (X0 : ℝ) : Fin (N + 1) → ℝ :=
  fun j => X0 * (1 - (j.val : ℝ) / (N : ℝ))

/-- With `c = 0` the minimizer is the linear path. -/
theorem minimizer_zero_risk_linear (N : ℕ) (hN : 0 < N) (Δ η X0 : ℝ)
    (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ x : Fin (N + 1) → ℝ, x 0 = X0 ∧ x (Fin.last N) = 0
      ∧ (∀ j : Fin (N + 1), x j = X0 * (1 - (j.val : ℝ) / (N : ℝ))) := by
  obtain ⟨x, hx0, hxN, _, _, huniq⟩ :=
    existsUnique_minimizer_liquidationCost N hN Δ η 0 X0 hΔ hη (le_refl 0)
  have hNne : (N : ℝ) ≠ 0 := by
    have hN0 : N ≠ 0 := by omega
    exact_mod_cast hN0
  have hηne : η ≠ 0 := ne_of_gt hη
  have hz0 : linPathZero N X0 0 = X0 := by
    simp [linPathZero]
  have hzN : linPathZero N X0 (Fin.last N) = 0 := by
    have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self hNne
    simp [linPathZero, hNN]
  have hzstat : ∀ k : Fin N, 0 < k.val →
      -(linPathZero N X0 ⟨k.val - 1, by omega⟩)
        + 2 * linPathZero N X0 k.castSucc - linPathZero N X0 k.succ
        + ((0 : ℝ) * Δ ^ 2 / η) * linPathZero N X0 k.castSucc = 0 := by
    intro k hk
    have hcastV : (k.castSucc).val = k.val := by simp only [Fin.val_castSucc]
    have hsuccV : (k.succ).val = k.val + 1 := by simp only [Fin.val_succ]
    simp only [linPathZero]
    rw [hcastV, hsuccV]
    field_simp [hNne, hηne]
    have hk1 : 1 ≤ k.val := hk
    rw [Nat.cast_sub hk1, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    ring
  have hzstatX := stationarity_ext N Δ η 0 (linPathZero N X0) hzstat
  have hymin : ∀ w : Fin (N + 1) → ℝ, w 0 = X0 → w (Fin.last N) = 0 →
      liquidationCost N Δ η 0 (linPathZero N X0)
        ≤ liquidationCost N Δ η 0 w := by
    intro w hw0 hwN
    have hkey := cost_sub_eq_energy N hN Δ η 0 hΔ hη (linPathZero N X0) X0
      hz0 hzN hzstatX w hw0 hwN
    have hEge : 0 ≤ energyR N Δ η 0
        (fun j => extPath N w j - extPath N (linPathZero N X0) j) :=
      energyR_nonneg N Δ η 0 hΔ hη (le_refl 0) _
    linarith [hkey, hEge]
  have hxeq : x = linPathZero N X0 := (huniq _ hz0 hzN hymin).symm
  refine ⟨x, hx0, hxN, ?_⟩
  intro j
  simp [hxeq, linPathZero]

/-- Linear path for the numeric test: `(2, 1, 0)`. -/
def linPathTest : Fin (2 + 1) → ℝ :=
  fun j => if j.val = 0 then 2 else if j.val = 1 then 1 else 0

/-- Suboptimal hold-then-dump path for the numeric test: `(2, 2, 0)`. -/
def subPathTest : Fin (2 + 1) → ℝ :=
  fun j => if j.val = 0 then 2 else if j.val = 1 then 2 else 0

/-- Numeric check: the minimizer beats a hold-then-dump path. -/
theorem minimizer_beats_suboptimal :
    ∃ x : Fin (2 + 1) → ℝ, x 0 = 2 ∧ x (Fin.last 2) = 0
      ∧ liquidationCost 2 1 1 0 x
        < liquidationCost 2 1 1 0 subPathTest := by
  obtain ⟨x, hx0, hxN, hopt, _, _⟩ :=
    existsUnique_minimizer_liquidationCost 2 (by omega) 1 1 0 2
      (by norm_num) (by norm_num) (by norm_num)
  have h20 : (2 : ℕ) ≠ 0 := by decide
  have h21 : (2 : ℕ) ≠ 1 := by decide
  have hz00 : linPathTest (0 : Fin 2).castSucc = 2 := by simp [linPathTest]
  have hz01 : linPathTest (0 : Fin 2).succ = 1 := by simp [linPathTest]
  have hz10 : linPathTest (1 : Fin 2).castSucc = 1 := by simp [linPathTest]
  have hz11 : linPathTest (1 : Fin 2).succ = 0 := by
    simp [linPathTest, h20, h21]
  have hw00 : subPathTest (0 : Fin 2).castSucc = 2 := by simp [subPathTest]
  have hw01 : subPathTest (0 : Fin 2).succ = 2 := by simp [subPathTest]
  have hw10 : subPathTest (1 : Fin 2).castSucc = 2 := by simp [subPathTest]
  have hw11 : subPathTest (1 : Fin 2).succ = 0 := by
    simp [subPathTest, h20, h21]
  have hcostZ : liquidationCost 2 1 1 0 linPathTest = 2 := by
    simp only [liquidationCost, Fin.sum_univ_two]
    rw [hz00, hz01, hz10, hz11]
    norm_num
  have hcostW : liquidationCost 2 1 1 0 subPathTest = 4 := by
    simp only [liquidationCost, Fin.sum_univ_two]
    rw [hw00, hw01, hw10, hw11]
    norm_num
  have hz0 : linPathTest 0 = 2 := by simp [linPathTest]
  have hzN : linPathTest (Fin.last 2) = 0 := by
    simp [linPathTest, h20, h21]
  have hoptZ := hopt linPathTest hz0 hzN
  refine ⟨x, hx0, hxN, ?_⟩
  linarith [hoptZ, hcostZ, hcostW]

end MathFinTest
