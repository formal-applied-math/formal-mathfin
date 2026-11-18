/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Analysis.DerivOfDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Almgren-Chriss optimal execution (deterministic closed form)

Liquidating `X_0` units of an asset over horizon `T` with linear temporary
impact (coefficient `η`) and price-variance risk aversion (coefficient `λ`),
the optimal trajectory `X(t)` (remaining inventory) minimises the
deterministic cost functional

  `∫_0^T (σ² λ · X(t)² + η · X'(t)²) dt`

subject to `X(0) = X_0` and `X(T) = 0`. The Euler-Lagrange equation reduces
to

  `X''(t) = κ² · X(t)`,    `κ² := σ² λ / η`,

a linear ODE with hyperbolic-cosine/sinh solutions. The boundary-condition-
satisfying solution is

  `X(t) = X_0 · sinh(κ · (T − t)) / sinh(κ · T)`.

We verify the closed form satisfies:
- the initial condition `X(0) = X_0`,
- the terminal condition `X(T) = 0`,
- the EL equation `X''(t) = κ² · X(t)`.

The full minimisation theorem (this closed form is optimal among all
admissible trajectories) is a calculus-of-variations claim that requires
function-space machinery beyond Mathlib's current pin.

## Main definitions

* `almgrenChrissPath`: the closed-form trajectory `X(t) = X_0 · sinh (κ (T − t)) / sinh (κ T)`.
* `liquidationCost`: the finite quadratic liquidation cost over `N` periods.

## Main results

* `almgrenChrissPath_at_zero`: `X(0) = X_0`.
* `almgrenChrissPath_at_terminal`: `X(T) = 0`.
* `hasDerivAt_almgrenChrissPath`: first derivative.
* `almgrenChrissPath_satisfies_EL`: `X''(t) = κ² · X(t)`.
* `existsUnique_minimizer_liquidationCost`: the finite liquidation cost has a unique
  feasible minimizing inventory path, and its interior solves the stationarity equations.

Neither derivative needs `sinh(κT) ≠ 0`: under Lean's `x / 0 = 0` the degenerate
closed form is the zero path, which satisfies both. Only the initial condition
uses it.

## References

* [Almgren and Chriss (2000)][AlmgrenChriss2000]

## Tags

optimal execution, market impact, liquidation, calculus of variations, Euler–Lagrange equation,
inventory, JEL G11, MSC 91G80, MSC 49L20
-/

@[expose] public section

namespace MathFin

open Real

/-- **Almgren-Chriss optimal-execution trajectory**:
`X(t) = X_0 · sinh(κ (T − t)) / sinh(κ T)`. Liquidation rate `−X'(t)` is
slow at the start and accelerates near `T`. -/
noncomputable def almgrenChrissPath (X_0 κ T t : ℝ) : ℝ :=
  X_0 * Real.sinh (κ * (T - t)) / Real.sinh (κ * T)

/-- **Initial condition**: `X(0) = X_0`. -/
theorem almgrenChrissPath_at_zero (X_0 κ T : ℝ) (hT : Real.sinh (κ * T) ≠ 0) :
    almgrenChrissPath X_0 κ T 0 = X_0 := by
  unfold almgrenChrissPath
  rw [sub_zero]
  field_simp

/-- **Terminal condition**: `X(T) = 0`. -/
theorem almgrenChrissPath_at_terminal (X_0 κ T : ℝ) :
    almgrenChrissPath X_0 κ T T = 0 := by
  unfold almgrenChrissPath
  rw [sub_self, mul_zero, Real.sinh_zero]
  simp

/-- **First derivative**: `X'(t) = −X_0 · κ · cosh(κ (T − t)) / sinh(κ T)`. -/
theorem hasDerivAt_almgrenChrissPath (X_0 κ T t : ℝ) :
    HasDerivAt (almgrenChrissPath X_0 κ T)
      (-(X_0 * κ * Real.cosh (κ * (T - t)) / Real.sinh (κ * T))) t := by
  have hd : HasDerivAt (fun t : ℝ ↦ κ * (T - t)) (-κ) t := by
    simpa using ((hasDerivAt_id t).const_sub T).const_mul κ
  unfold almgrenChrissPath
  convert (hd.sinh.const_mul X_0).div_const (Real.sinh (κ * T)) using 1; ring

/-- The t-derivative of the first-derivative formula `−X₀ κ cosh(κ (T − t)) / sinh(κ T)` is
`κ² · X(t)`: the same `sinh(κ (T − t))` shape, multiplied by `κ²`. -/
private lemma hasDerivAt_almgrenChrissPath_deriv_formula (X_0 κ T t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ -(X_0 * κ * Real.cosh (κ * (T - s)) / Real.sinh (κ * T)))
      (κ ^ 2 * almgrenChrissPath X_0 κ T t) t := by
  have hd : HasDerivAt (fun t : ℝ ↦ κ * (T - t)) (-κ) t := by
    simpa using ((hasDerivAt_id t).const_sub T).const_mul κ
  unfold almgrenChrissPath
  convert ((hd.cosh.const_mul (X_0 * κ)).div_const (Real.sinh (κ * T))).neg using 1; ring

/-- **Almgren-Chriss EL equation**: the closed-form trajectory satisfies `X''(t) = κ² · X(t)`,
the Euler-Lagrange equation of the cost functional: `hasDerivAt_almgrenChrissPath` gives `X'`
at every `t`, and the derivative of that formula is `κ² · X(t)`. -/
theorem almgrenChrissPath_satisfies_EL (X_0 κ T t : ℝ) :
    HasDerivAt (deriv (almgrenChrissPath X_0 κ T)) (κ ^ 2 * almgrenChrissPath X_0 κ T t) t :=
  hasDerivAt_deriv_of_eventually (.of_forall (hasDerivAt_almgrenChrissPath X_0 κ T))
    (hasDerivAt_almgrenChrissPath_deriv_formula X_0 κ T t)

noncomputable def liquidationCost (N : ℕ) (Δ η c : ℝ) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ k : Fin N, Δ * (η * ((x k.succ - x k.castSucc) / Δ) ^ 2 + c * (x k.castSucc) ^ 2)

/-- Extend a path on `Fin (N+1)` to a total function on `ℕ`. -/
def extPath (N : ℕ) (x : Fin (N + 1) → ℝ) : ℕ → ℝ :=
  fun j => if h : j < N + 1 then x ⟨j, h⟩ else 0

/-- The extension at a path index recovers the path value. -/
theorem extPath_val (N : ℕ) (x : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    extPath N x j.val = x j := by
  simp only [extPath]
  exact dite_eq_left j.2

/-- The extension at `0` recovers the initial value. -/
theorem extPath_zero (N : ℕ) (x : Fin (N + 1) → ℝ) (X0 : ℝ)
    (hx0 : x 0 = X0) : extPath N x 0 = X0 := by
  have h0lt : 0 < N + 1 := by omega
  have h1 : extPath N x 0 = x ⟨0, h0lt⟩ := by
    simp only [extPath]
    exact dite_eq_left h0lt
  have hmk : (⟨0, h0lt⟩ : Fin (N + 1)) = 0 :=
    Fin.ext_iff.mpr (by simp)
  rw [h1, hmk, hx0]

/-- The extension at `N` recovers the terminal value. -/
theorem extPath_last (N : ℕ) (x : Fin (N + 1) → ℝ)
    (hxN : x (Fin.last N) = 0) : extPath N x N = 0 := by
  have hNlt : N < N + 1 := by omega
  have h1 : extPath N x N = x ⟨N, hNlt⟩ := by
    simp only [extPath]
    exact dite_eq_left hNlt
  have hmk : (⟨N, hNlt⟩ : Fin (N + 1)) = Fin.last N :=
    Fin.ext_iff.mpr (by simp)
  rw [h1, hmk, hxN]

/-- The extension at `k.val` agrees with `castSucc`. -/
theorem extPath_castSucc (N : ℕ) (x : Fin (N + 1) → ℝ) (k : Fin N) :
    x k.castSucc = extPath N x k.val := by
  have hk2 := k.2
  have hlt : k.val < N + 1 := by omega
  have h1 : extPath N x k.val = x ⟨k.val, hlt⟩ := by
    simp only [extPath]
    exact dite_eq_left hlt
  have h2 : k.castSucc = (⟨k.val, hlt⟩ : Fin (N + 1)) :=
    Fin.ext_iff.mpr (by rw [Fin.val_castSucc])
  rw [h2]
  exact h1.symm

/-- The extension at `k.val + 1` agrees with `succ`. -/
theorem extPath_succ (N : ℕ) (x : Fin (N + 1) → ℝ) (k : Fin N) :
    x k.succ = extPath N x (k.val + 1) := by
  have hk2 := k.2
  have hlt : k.val + 1 < N + 1 := by omega
  have h1 : extPath N x (k.val + 1) = x ⟨k.val + 1, hlt⟩ := by
    simp only [extPath]
    exact dite_eq_left hlt
  have hsuccV : (k.succ).val = k.val + 1 := by
    simp only [Fin.val_succ]
  have h2 : k.succ = (⟨k.val + 1, hlt⟩ : Fin (N + 1)) :=
    Fin.ext_iff.mpr (by rw [hsuccV])
  rw [h2]
  exact h1.symm

/-- The extension at a literal index agrees with `mk`. -/
theorem extPath_mk (N : ℕ) (x : Fin (N + 1) → ℝ) (j : ℕ)
    (h : j < N + 1) : x ⟨j, h⟩ = extPath N x j := by
  have h1 : extPath N x j = x ⟨j, h⟩ := by
    simp only [extPath]
    exact dite_eq_left h
  exact h1.symm

/-- Left-neighbor lookup for the stationarity system on `ℕ`. -/
def sysL (V : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else V (j - 1)

/-- Right-neighbor lookup for the stationarity system on `ℕ`. -/
def sysR (M : ℕ) (V : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j + 1 = M then 0 else V (j + 1)

/-- The left lookup vanishes at `0`. -/
theorem sysL_zero (V : ℕ → ℝ) : sysL V 0 = 0 := by
  simp [sysL]

/-- The left lookup at a successor. -/
theorem sysL_succ (V : ℕ → ℝ) (j : ℕ) : sysL V (j + 1) = V j := by
  have hsub : j + 1 - 1 = j := by omega
  simp only [sysL]
  rw [ite_eq_right (by omega), hsub]

/-- The right lookup vanishes at the last index. -/
theorem sysR_last (M : ℕ) (V : ℕ → ℝ) (hM : 1 ≤ M) :
    sysR M V (M - 1) = 0 := by
  have hcond : M - 1 + 1 = M := by omega
  simp only [sysR]
  rw [ite_eq_left hcond]

/-- The right lookup before the last index. -/
theorem sysR_of_lt (M : ℕ) (V : ℕ → ℝ) (j : ℕ) (hj : j < M - 1) :
    sysR M V j = V (j + 1) := by
  have hne : ¬ (j + 1 = M) := by omega
  simp only [sysR]
  rw [ite_eq_right hne]

/-- Energy identity for the tridiagonal stationarity system. -/
theorem sysTEnergy (V : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) (a : ℝ) :
    (∑ j ∈ Finset.range M, V j * ((2 + a) * V j - sysL V j - sysR M V j))
      = (∑ j ∈ Finset.range (M - 1), (V (j + 1) - V j) ^ 2)
        + ((V 0) ^ 2 + (V (M - 1)) ^ 2)
        + a * (∑ j ∈ Finset.range M, (V j) ^ 2) := by
  have hM2 : M = (M - 1) + 1 := by omega
  have hA : (∑ j ∈ Finset.range M, V j * ((2 + a) * V j - sysL V j
      - sysR M V j))
      = (∑ j ∈ Finset.range M, (2 + a) * (V j) ^ 2)
        - (∑ j ∈ Finset.range M, V j * sysL V j)
        - (∑ j ∈ Finset.range M, V j * sysR M V j) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hP1 : (∑ j ∈ Finset.range M, V j * sysL V j)
      = ∑ j ∈ Finset.range (M - 1), V (j + 1) * V j := by
    conv_lhs => rw [hM2]
    rw [Finset.sum_range_succ']
    simp only [sysL_succ, sysL_zero, mul_zero, add_zero]
  have hP2 : (∑ j ∈ Finset.range M, V j * sysR M V j)
      = ∑ j ∈ Finset.range (M - 1), V j * V (j + 1) := by
    conv_lhs => rw [hM2]
    rw [Finset.sum_range_succ]
    have hM' : (M - 1) + 1 = M := by omega
    rw [hM']
    have hRend : sysR M V (M - 1) = 0 := sysR_last M V hM
    simp only [hRend, mul_zero, add_zero]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < M - 1 := Finset.mem_range.mp hj
    have hRj := sysR_of_lt M V j hj'
    rw [hRj]
  have hS1 : (∑ j ∈ Finset.range M, (2 + a) * (V j) ^ 2)
      = (2 + a) * (∑ j ∈ Finset.range M, (V j) ^ 2) := by
    rw [Finset.mul_sum]
  have hPP : (∑ j ∈ Finset.range (M - 1), V j * V (j + 1))
      = ∑ j ∈ Finset.range (M - 1), V (j + 1) * V j := by
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hD1 : (∑ j ∈ Finset.range (M - 1), (V (j + 1) - V j) ^ 2)
      = (∑ j ∈ Finset.range (M - 1), (V (j + 1)) ^ 2)
        - (∑ j ∈ Finset.range (M - 1), 2 * (V (j + 1) * V j))
        + (∑ j ∈ Finset.range (M - 1), (V j) ^ 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hX : (∑ j ∈ Finset.range (M - 1), 2 * (V (j + 1) * V j))
      = 2 * (∑ j ∈ Finset.range (M - 1), V (j + 1) * V j) := by
    rw [Finset.mul_sum]
  have hShift : (∑ j ∈ Finset.range (M - 1), (V (j + 1)) ^ 2)
      = (∑ j ∈ Finset.range M, (V j) ^ 2) - (V 0) ^ 2 := by
    have hSeq : (∑ j ∈ Finset.range M, (V j) ^ 2)
        = (∑ j ∈ Finset.range (M - 1), (V (j + 1)) ^ 2) + (V 0) ^ 2 := by
      conv_lhs => rw [hM2]
      rw [Finset.sum_range_succ']
    linarith
  have hPrefix : (∑ j ∈ Finset.range (M - 1), (V j) ^ 2)
      = (∑ j ∈ Finset.range M, (V j) ^ 2) - (V (M - 1)) ^ 2 := by
    have hSeq : (∑ j ∈ Finset.range M, (V j) ^ 2)
        = (∑ j ∈ Finset.range (M - 1), (V j) ^ 2) + (V (M - 1)) ^ 2 := by
      conv_lhs => rw [hM2]
      rw [Finset.sum_range_succ]
    linarith
  have hE2 : (∑ j ∈ Finset.range M, V j * ((2 + a) * V j - sysL V j
      - sysR M V j))
      = (2 + a) * (∑ j ∈ Finset.range M, (V j) ^ 2)
        - 2 * (∑ j ∈ Finset.range (M - 1), V (j + 1) * V j) := by
    rw [hA, hP1, hP2, hPP, hS1]
    ring
  have hD2 : (∑ j ∈ Finset.range (M - 1), (V (j + 1) - V j) ^ 2)
      = 2 * (∑ j ∈ Finset.range M, (V j) ^ 2) - (V 0) ^ 2
        - (V (M - 1)) ^ 2
        - 2 * (∑ j ∈ Finset.range (M - 1), V (j + 1) * V j) := by
    rw [hD1, hX, hShift, hPrefix]
    ring
  rw [hE2, hD2]
  ring

/-- The stationarity system as a function on interior vectors. -/
def sysT (M : ℕ) (a : ℝ) (v : Fin M → ℝ) : Fin M → ℝ :=
  fun i =>
    (2 + a) * v i
      - (if hL : i.val = 0 then 0 else v ⟨i.val - 1, by have h2 := i.2; omega⟩)
      - (if hR : i.val + 1 = M then 0 else v ⟨i.val + 1, by have h2 := i.2; omega⟩)

/-- Right-hand side of the stationarity system. -/
def sysRHS (M : ℕ) (X0 : ℝ) : Fin M → ℝ :=
  fun i => if i.val = 0 then X0 else 0

/-- The system map preserves addition. -/
theorem sysT_add (M : ℕ) (a : ℝ) (v w : Fin M → ℝ) :
    sysT M a (v + w) = sysT M a v + sysT M a w := by
  ext i
  simp only [sysT, Pi.add_apply]
  by_cases hL : i.val = 0
  · by_cases hR : i.val + 1 = M
    · simp only [dite_eq_left hL, dite_eq_left hR]
      ring
    · simp only [dite_eq_left hL, dite_eq_right hR]
      ring
  · by_cases hR : i.val + 1 = M
    · simp only [dite_eq_right hL, dite_eq_left hR]
      ring
    · simp only [dite_eq_right hL, dite_eq_right hR]
      ring

/-- The system map preserves scalar multiplication. -/
theorem sysT_smul (M : ℕ) (a : ℝ) (c : ℝ) (v : Fin M → ℝ) :
    sysT M a (c • v) = c • sysT M a v := by
  ext i
  simp only [sysT, Pi.smul_apply, smul_eq_mul]
  by_cases hL : i.val = 0
  · by_cases hR : i.val + 1 = M
    · simp only [dite_eq_left hL, dite_eq_left hR]
      ring
    · simp only [dite_eq_left hL, dite_eq_right hR]
      ring
  · by_cases hR : i.val + 1 = M
    · simp only [dite_eq_right hL, dite_eq_left hR]
      ring
    · simp only [dite_eq_right hL, dite_eq_right hR]
      ring

/-- The stationarity system as a linear map. -/
def sysTMap (M : ℕ) (a : ℝ) : (Fin M → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun := sysT M a
  map_add' := sysT_add M a
  map_smul' := sysT_smul M a

/-- Extend a vector on `Fin M` to a total function on `ℕ`. -/
def extVec (M : ℕ) (v : Fin M → ℝ) : ℕ → ℝ :=
  fun j => if h : j < M then v ⟨j, h⟩ else 0

/-- Values of the vector extension agree with the vector below `M`. -/
theorem extVec_of_lt (M : ℕ) (v : Fin M → ℝ) (j : ℕ)
    (h : j < M) : extVec M v j = v ⟨j, h⟩ := by
  simp only [extVec]
  exact dite_eq_left h

/-- The vector extension at an index recovers the vector value. -/
theorem extVec_val (M : ℕ) (v : Fin M → ℝ) (i : Fin M) :
    extVec M v i.val = v i := by
  simp only [extVec]
  exact dite_eq_left i.2

/-- The system map has trivial kernel. -/
theorem sysT_ker_eq_zero (M : ℕ) (hM : 1 ≤ M) (a : ℝ) (ha : 0 ≤ a)
    (v : Fin M → ℝ) (hv : sysTMap M a v = 0) : v = 0 := by
  have hrow : ∀ i : Fin M, sysT M a v i = 0 := fun i => congrFun hv i
  have hET0 : (∑ i : Fin M, v i * sysT M a v i) = 0 := by
    simp [hrow, Finset.sum_const_zero]
  have hBridge : (∑ i : Fin M, v i * sysT M a v i)
      = ∑ j ∈ Finset.range M, extVec M v j * ((2 + a) * extVec M v j
        - sysL (extVec M v) j - sysR M (extVec M v) j) := by
    have hpoint : ∀ i : Fin M, v i * sysT M a v i
        = (fun j => extVec M v j * ((2 + a) * extVec M v j
          - sysL (extVec M v) j - sysR M (extVec M v) j)) ↑i := by
      intro i
      change v i * sysT M a v i = extVec M v ↑i * ((2 + a) * extVec M v ↑i
        - sysL (extVec M v) ↑i - sysR M (extVec M v) ↑i)
      have hk2 := i.2
      have hkc : (↑i : ℕ) = i.val := by simp
      rw [hkc]
      have pL : i.val - 1 < M := by omega
      have hV0 : extVec M v i.val = v i := extVec_val M v i
      have hVL : extVec M v (i.val - 1) = v ⟨i.val - 1, pL⟩ :=
        extVec_of_lt M v (i.val - 1) pL
      have hsysU : sysT M a v i = (2 + a) * v i
          - (if _ : i.val = 0 then (0 : ℝ) else v ⟨i.val - 1, pL⟩)
          - (if hR : i.val + 1 = M then (0 : ℝ)
            else v ⟨i.val + 1, by have h2 := i.2; omega⟩) := rfl
      rw [hV0]
      simp only [sysL, sysR]
      by_cases hL : i.val = 0
      · by_cases hR : i.val + 1 = M
        · rw [hsysU, dite_eq_left hL, dite_eq_left hR, ite_eq_left hL, ite_eq_left hR]
        · have pR : i.val + 1 < M := by omega
          have hVR : extVec M v (i.val + 1) = v ⟨i.val + 1, pR⟩ :=
            extVec_of_lt M v (i.val + 1) pR
          have hsysU' : sysT M a v i = (2 + a) * v i
              - (if _ : i.val = 0 then (0 : ℝ) else v ⟨i.val - 1, pL⟩)
              - (if _ : i.val + 1 = M then (0 : ℝ) else v ⟨i.val + 1, pR⟩) :=
            rfl
          rw [hsysU', dite_eq_left hL, dite_eq_right hR, ite_eq_left hL, ite_eq_right hR, hVR]
      · by_cases hR : i.val + 1 = M
        · rw [hsysU, dite_eq_right hL, dite_eq_left hR, ite_eq_right hL, ite_eq_left hR, hVL]
        · have pR : i.val + 1 < M := by omega
          have hVR : extVec M v (i.val + 1) = v ⟨i.val + 1, pR⟩ :=
            extVec_of_lt M v (i.val + 1) pR
          have hsysU' : sysT M a v i = (2 + a) * v i
              - (if _ : i.val = 0 then (0 : ℝ) else v ⟨i.val - 1, pL⟩)
              - (if _ : i.val + 1 = M then (0 : ℝ) else v ⟨i.val + 1, pR⟩) :=
            rfl
          rw [hsysU', dite_eq_right hL, dite_eq_right hR, ite_eq_right hL,
            ite_eq_right hR, hVL, hVR]
    have hcongr : (∑ i : Fin M, v i * sysT M a v i)
        = ∑ i : Fin M, (fun j => extVec M v j * ((2 + a) * extVec M v j
          - sysL (extVec M v) j - sysR M (extVec M v) j)) ↑i :=
      Finset.sum_congr rfl (fun i _ => hpoint i)
    rw [hcongr]
    exact Fin.sum_univ_eq_sum_range (fun j => extVec M v j * ((2 + a)
      * extVec M v j - sysL (extVec M v) j - sysR M (extVec M v) j)) M
  have hE := sysTEnergy (extVec M v) M hM a
  rw [← hBridge, hET0] at hE
  have hDnn : 0 ≤ ∑ j ∈ Finset.range (M - 1),
      ((extVec M v) (j + 1) - (extVec M v) j) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hBnn : 0 ≤ ((extVec M v) 0) ^ 2 + ((extVec M v) (M - 1)) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSnn : 0 ≤ a * (∑ j ∈ Finset.range M, ((extVec M v) j) ^ 2) :=
    mul_nonneg ha (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hD0 : (∑ j ∈ Finset.range (M - 1),
      ((extVec M v) (j + 1) - (extVec M v) j) ^ 2) = 0 := by
    linarith [hE, hDnn, hBnn, hSnn]
  have hB0 : ((extVec M v) 0) ^ 2 + ((extVec M v) (M - 1)) ^ 2 = 0 := by
    linarith [hE, hDnn, hBnn, hSnn]
  have hV0sq : ((extVec M v) 0) ^ 2 = 0 := by
    have hx := sq_nonneg ((extVec M v) 0)
    have hy := sq_nonneg ((extVec M v) (M - 1))
    linarith [hB0, hx, hy]
  have hV0 : extVec M v 0 = 0 := sq_eq_zero_iff.mp hV0sq
  have hconsec : ∀ j, j < M - 1 → (extVec M v) (j + 1) = (extVec M v) j := by
    intro j hj
    have hmem : j ∈ Finset.range (M - 1) := Finset.mem_range.mpr hj
    have hnn : ∀ k ∈ Finset.range (M - 1),
        0 ≤ ((extVec M v) (k + 1) - (extVec M v) k) ^ 2 := by
      intro k _
      exact sq_nonneg _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hD0
    have hterm := hall j hmem
    have hdiff : (extVec M v) (j + 1) - (extVec M v) j = 0 :=
      sq_eq_zero_iff.mp hterm
    exact sub_eq_zero.mp hdiff
  have hconst : ∀ j, j < M → extVec M v j = 0 := by
    intro j hj
    have hj' : j ≤ M - 1 := by omega
    have hchain : ∀ k, k ≤ M - 1 → extVec M v k = extVec M v 0 := by
      intro k
      induction k with
      | zero => exact fun _ => rfl
      | succ m ih =>
        intro hm
        have hmN : m < M - 1 := by omega
        have h1 : extVec M v (m + 1) = extVec M v m := hconsec m hmN
        have h2 : extVec M v m = extVec M v 0 := ih (by omega)
        exact h1.trans h2
    have hc := hchain j hj'
    rw [hc, hV0]
  ext i
  have hi : i.val < M := i.2
  have hVi := hconst i.val hi
  have hback : extVec M v i.val = v i := extVec_val M v i
  rw [hback] at hVi
  simpa using hVi

/-- The system map is injective. -/
theorem sysT_injective (M : ℕ) (hM : 1 ≤ M) (a : ℝ) (ha : 0 ≤ a) :
    Function.Injective ⇑(sysTMap M a) := by
  intro v w hvw
  have h1 : sysTMap M a (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero : v - w = 0 := sysT_ker_eq_zero M hM a ha (v - w) h1
  exact sub_eq_zero.mp hzero

/-- The stationarity system is solvable. -/
theorem sysT_solution (M : ℕ) (hM : 1 ≤ M) (a : ℝ) (ha : 0 ≤ a) (X0 : ℝ) :
    ∃ u : Fin M → ℝ, sysT M a u = sysRHS M X0 := by
  have hinj := sysT_injective M hM a ha
  have hsurj := LinearMap.surjective_of_injective hinj
  obtain ⟨u, hu⟩ := hsurj (sysRHS M X0)
  exact ⟨u, hu⟩

/-- Candidate minimizer from an interior solution. -/
def xStar (N : ℕ) (hN : 2 ≤ N) (u : Fin (N - 1) → ℝ) (X0 : ℝ) :
    Fin (N + 1) → ℝ :=
  fun j =>
    if h1 : j.val = 0 then X0
    else if h2 : j.val = N then 0
    else u ⟨j.val - 1, by have h3 := j.2; omega⟩

/-- The candidate starts at `X0`. -/
theorem xStar_zero (N : ℕ) (hN : 2 ≤ N) (u : Fin (N - 1) → ℝ) (X0 : ℝ) :
    xStar N hN u X0 0 = X0 := by
  have h0 : (0 : Fin (N + 1)).val = 0 := by simp
  simp only [xStar]
  rw [dite_eq_left h0]

/-- The candidate ends at `0`. -/
theorem xStar_last (N : ℕ) (hN : 2 ≤ N) (u : Fin (N - 1) → ℝ) (X0 : ℝ) :
    xStar N hN u X0 (Fin.last N) = 0 := by
  have hlast : (Fin.last N).val = N := by simp
  have hn0 : ¬ ((Fin.last N).val = 0) := by
    rw [hlast]
    omega
  simp only [xStar]
  rw [dite_eq_right hn0, dite_eq_left hlast]

/-- The candidate at interior indices. -/
theorem xStar_interior {N : ℕ} {hN : 2 ≤ N} {u : Fin (N - 1) → ℝ}
    {X0 : ℝ} (j : ℕ) (hj1 : 1 ≤ j) (_hjN : j ≤ N - 1) {h : j < N + 1}
    (hu : j - 1 < N - 1) :
    xStar N hN u X0 ⟨j, h⟩ = u ⟨j - 1, hu⟩ := by
  have hn0 : ¬ (j = 0) := by omega
  have hnN : ¬ (j = N) := by omega
  have hn0' : ¬ (⟨j, h⟩ : Fin (N + 1)).val = 0 := hn0
  have hnN' : ¬ (⟨j, h⟩ : Fin (N + 1)).val = N := hnN
  simp only [xStar]
  rw [dite_eq_right hn0', dite_eq_right hnN']

/-- The candidate at a zero index. -/
theorem xStar_at_zero {N : ℕ} {hN : 2 ≤ N} {u : Fin (N - 1) → ℝ} {X0 : ℝ}
    (j : ℕ) (hj : j = 0) {h : j < N + 1} :
    xStar N hN u X0 ⟨j, h⟩ = X0 := by
  have hj' : (⟨j, h⟩ : Fin (N + 1)).val = 0 := hj
  simp only [xStar]
  rw [dite_eq_left hj']

/-- The candidate at the terminal index. -/
theorem xStar_at_last {N : ℕ} {hN : 2 ≤ N} {u : Fin (N - 1) → ℝ} {X0 : ℝ}
    (j : ℕ) (hj : j = N) {h : j < N + 1} :
    xStar N hN u X0 ⟨j, h⟩ = 0 := by
  have hn0 : ¬ (j = 0) := by omega
  have hn0' : ¬ (⟨j, h⟩ : Fin (N + 1)).val = 0 := hn0
  have hj' : (⟨j, h⟩ : Fin (N + 1)).val = N := hj
  simp only [xStar]
  rw [dite_eq_right hn0', dite_eq_left hj']

/-- The candidate satisfies the stationarity equations. -/
theorem xStar_stationarity (N : ℕ) (hN : 2 ≤ N) (Δ η c X0 : ℝ)
    (u : Fin (N - 1) → ℝ)
    (hTu : sysT (N - 1) (c * Δ ^ 2 / η) u = sysRHS (N - 1) X0) :
    ∀ k : Fin N, 0 < k.val →
      -(xStar N hN u X0 ⟨k.val - 1, by omega⟩)
        + 2 * xStar N hN u X0 k.castSucc - xStar N hN u X0 k.succ
        + (c * Δ ^ 2 / η) * xStar N hN u X0 k.castSucc = 0 := by
  intro k hk
  have hk2 := k.2
  have hM1 : k.val - 1 < N - 1 := by omega
  have pL : k.val - 1 - 1 < N - 1 := by omega
  have hkN1 : k.val < N + 1 := by omega
  have hcastV : (k.castSucc).val = k.val := by simp only [Fin.val_castSucc]
  have hsuccV : (k.succ).val = k.val + 1 := by
    simp only [Fin.val_succ]
  have hcastMk : k.castSucc = (⟨k.val, hkN1⟩ : Fin (N + 1)) :=
    Fin.ext_iff.mpr (by rw [hcastV])
  have hsuccMk : k.succ = (⟨k.val + 1, by omega⟩ : Fin (N + 1)) :=
    Fin.ext_iff.mpr (by rw [hsuccV])
  have hrow : sysT (N - 1) (c * Δ ^ 2 / η) u ⟨k.val - 1, hM1⟩
      = sysRHS (N - 1) X0 ⟨k.val - 1, hM1⟩ :=
    congrFun hTu _
  have hrowU : (2 + c * Δ ^ 2 / η) * u ⟨k.val - 1, hM1⟩
      - (if _ : k.val - 1 = 0 then (0 : ℝ) else u ⟨k.val - 1 - 1, pL⟩)
      - (if hR : k.val - 1 + 1 = N - 1 then (0 : ℝ)
        else u ⟨k.val - 1 + 1, by have h2 := k.2; omega⟩)
      = (if _ : k.val - 1 = 0 then X0 else 0) := hrow
  rw [hcastMk, hsuccMk]
  have hj1c : 1 ≤ k.val := by omega
  have hjNc : k.val ≤ N - 1 := by omega
  rw [xStar_interior (k.val) hj1c hjNc hM1]
  by_cases hL : k.val - 1 = 0
  · by_cases hR : k.val - 1 + 1 = N - 1
    · have hSeq : k.val + 1 = N := by omega
      rw [xStar_at_zero (k.val - 1) hL]
      rw [xStar_at_last (k.val + 1) hSeq]
      simp only [dite_eq_left hL, dite_eq_left hR] at hrowU
      linear_combination hrowU
    · have pR : k.val - 1 + 1 < N - 1 := by omega
      have pS : k.val + 1 - 1 < N - 1 := by omega
      have hj1s : 1 ≤ k.val + 1 := by omega
      have hjNs : k.val + 1 ≤ N - 1 := by omega
      rw [xStar_at_zero (k.val - 1) hL]
      rw [xStar_interior (k.val + 1) hj1s hjNs pS]
      have halign : (⟨k.val + 1 - 1, pS⟩ : Fin (N - 1))
          = ⟨k.val - 1 + 1, pR⟩ :=
        Fin.mk.inj_iff.mpr (by omega)
      rw [halign]
      simp only [dite_eq_left hL, dite_eq_right hR] at hrowU
      have hrowU' : (2 + c * Δ ^ 2 / η) * u ⟨k.val - 1, hM1⟩ - 0
          - u ⟨k.val - 1 + 1, pR⟩ = X0 := hrowU
      linear_combination hrowU'
  · by_cases hR : k.val - 1 + 1 = N - 1
    · have hSeq : k.val + 1 = N := by omega
      have hj1m : 1 ≤ k.val - 1 := by omega
      have hjNm : k.val - 1 ≤ N - 1 := by omega
      rw [xStar_interior (k.val - 1) hj1m hjNm pL]
      rw [xStar_at_last (k.val + 1) hSeq]
      simp only [dite_eq_right hL, dite_eq_left hR] at hrowU
      linear_combination hrowU
    · have pR : k.val - 1 + 1 < N - 1 := by omega
      have pS : k.val + 1 - 1 < N - 1 := by omega
      have hj1m : 1 ≤ k.val - 1 := by omega
      have hjNm : k.val - 1 ≤ N - 1 := by omega
      have hj1s : 1 ≤ k.val + 1 := by omega
      have hjNs : k.val + 1 ≤ N - 1 := by omega
      rw [xStar_interior (k.val - 1) hj1m hjNm pL]
      rw [xStar_interior (k.val + 1) hj1s hjNs pS]
      have halign : (⟨k.val + 1 - 1, pS⟩ : Fin (N - 1))
          = ⟨k.val - 1 + 1, pR⟩ :=
        Fin.mk.inj_iff.mpr (by omega)
      rw [halign]
      simp only [dite_eq_right hL, dite_eq_right hR] at hrowU
      have hrowU' : (2 + c * Δ ^ 2 / η) * u ⟨k.val - 1, hM1⟩
          - u ⟨k.val - 1 - 1, pL⟩ - u ⟨k.val - 1 + 1, pR⟩ = 0 := hrowU
      linear_combination hrowU'

/-- Range-sum form of the liquidation cost. -/
noncomputable def costR (N : ℕ) (Δ η c : ℝ) (Z : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, Δ * (η * ((Z (j + 1) - Z j) / Δ) ^ 2 + c * (Z j) ^ 2)

/-- Range-sum form of the second-order energy. -/
noncomputable def energyR (N : ℕ) (Δ η c : ℝ) (D : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (Δ * η * ((D (j + 1) - D j) / Δ) ^ 2 + Δ * c * (D j) ^ 2)

/-- Range-sum form of the first-order (linear) term. -/
noncomputable def linearR (N : ℕ) (Δ η c : ℝ) (X D : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (2 * Δ * η * ((X (j + 1) - X j) / Δ) * ((D (j + 1) - D j) / Δ)
      + 2 * Δ * c * X j * D j)

/-- Summation-by-parts weights from the candidate path. -/
noncomputable def statA (Δ η : ℝ) (X : ℕ → ℝ) : ℕ → ℝ :=
  fun k => 2 * Δ * η * ((X (k + 1) - X k) / Δ) / Δ

/-- The `Fin`-sum cost equals its range-sum form. -/
theorem cost_bridge (N : ℕ) (Δ η c : ℝ) (x : Fin (N + 1) → ℝ) :
    liquidationCost N Δ η c x = costR N Δ η c (extPath N x) := by
  have hpoint : ∀ k : Fin N,
      (Δ * (η * ((x k.succ - x k.castSucc) / Δ) ^ 2 + c * (x k.castSucc) ^ 2))
        = (fun j => Δ * (η * ((extPath N x (j + 1) - extPath N x j) / Δ) ^ 2
          + c * (extPath N x j) ^ 2)) ↑k := by
    intro k
    change (Δ * (η * ((x k.succ - x k.castSucc) / Δ) ^ 2 + c * (x k.castSucc) ^ 2))
      = Δ * (η * ((extPath N x (↑k + 1) - extPath N x ↑k) / Δ) ^ 2
        + c * (extPath N x ↑k) ^ 2)
    have hkc : (↑k : ℕ) = k.val := by simp
    rw [hkc, ← extPath_succ N x k, ← extPath_castSucc N x k]
  have hcongr : (∑ k : Fin N,
        Δ * (η * ((x k.succ - x k.castSucc) / Δ) ^ 2 + c * (x k.castSucc) ^ 2))
      = ∑ k : Fin N, (fun j => Δ * (η * ((extPath N x (j + 1)
        - extPath N x j) / Δ) ^ 2 + c * (extPath N x j) ^ 2)) ↑k :=
    Finset.sum_congr rfl (fun k _ => hpoint k)
  simp only [liquidationCost, costR]
  rw [hcongr]
  exact Fin.sum_univ_eq_sum_range (fun j => Δ * (η * ((extPath N x (j + 1)
    - extPath N x j) / Δ) ^ 2 + c * (extPath N x j) ^ 2)) N

/-- Cost difference splits into linear and energy parts. -/
theorem cost_expansion (N : ℕ) (Δ η c : ℝ) (X Y : ℕ → ℝ) :
    costR N Δ η c Y - costR N Δ η c X
      = linearR N Δ η c X (fun j => Y j - X j)
        + energyR N Δ η c (fun j => Y j - X j) := by
  simp only [costR, linearR, energyR]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The energy is nonnegative. -/
theorem energyR_nonneg (N : ℕ) (Δ η c : ℝ) (hΔ : 0 < Δ) (hη : 0 < η)
    (hc : 0 ≤ c) (D : ℕ → ℝ) : 0 ≤ energyR N Δ η c D := by
  simp only [energyR]
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg hΔ.le hη.le) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hΔ.le hc) (sq_nonneg _)

/-- Stationarity in terms of the path extension. -/
theorem stationarity_ext (N : ℕ) (Δ η c : ℝ) (x : Fin (N + 1) → ℝ)
    (hstat : ∀ k : Fin N, 0 < k.val →
      -(x ⟨k.val - 1, by omega⟩) + 2 * x k.castSucc - x k.succ
        + (c * Δ ^ 2 / η) * x k.castSucc = 0)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N - 1) :
    -(extPath N x (j - 1)) + 2 * extPath N x j - extPath N x (j + 1)
      + (c * Δ ^ 2 / η) * extPath N x j = 0 := by
  have hjN' : j < N := by omega
  have hjn : j < N := hjN'
  have h0 : 0 < (⟨j, hjn⟩ : Fin N).val := by
    change 0 < j
    omega
  have hS := hstat ⟨j, hjn⟩ h0
  have hk : (⟨j, hjn⟩ : Fin N).val = j := rfl
  have hc1 := extPath_castSucc N x ⟨j, hjn⟩
  have hc2 := extPath_succ N x ⟨j, hjn⟩
  rw [hk] at hc1 hc2
  have hsub : j - 1 < N + 1 := by omega
  have hc3 := extPath_mk N x (j - 1) hsub
  have hS' : -(x ⟨j - 1, hsub⟩) + 2 * x (⟨j, hjn⟩ : Fin N).castSucc
      - x (⟨j, hjn⟩ : Fin N).succ
      + (c * Δ ^ 2 / η) * x (⟨j, hjn⟩ : Fin N).castSucc = 0 := hS
  rw [hc1, hc2, hc3] at hS'
  exact hS'

/-- The linear term vanishes for stationary paths. -/
theorem linearR_eq_zero (N : ℕ) (hN : 0 < N) (Δ η c : ℝ) (hΔ : 0 < Δ)
    (hη : 0 < η) (X D : ℕ → ℝ)
    (hstat : ∀ j, 1 ≤ j → j ≤ N - 1 →
      -(X (j - 1)) + 2 * X j - X (j + 1) + (c * Δ ^ 2 / η) * X j = 0)
    (hD0 : D 0 = 0) (hDN : D N = 0) :
    linearR N Δ η c X D = 0 := by
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hηne : η ≠ 0 := ne_of_gt hη
  have hN1 : N = (N - 1) + 1 := by omega
  have hLsplit : linearR N Δ η c X D
      = (∑ j ∈ Finset.range N, 2 * Δ * η * ((X (j + 1) - X j) / Δ)
          * ((D (j + 1) - D j) / Δ))
        + (∑ j ∈ Finset.range N, 2 * Δ * c * X j * D j) := by
    simp only [linearR]
    rw [← Finset.sum_add_distrib]
  have hSBPgen : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1),
        statA Δ η X k * (D (k + 1) - D k))
      = statA Δ η X n * D (n + 1) - statA Δ η X 0 * D 0
        + ∑ k ∈ Finset.range n,
          (statA Δ η X k - statA Δ η X (k + 1)) * D (k + 1) := by
    intro n
    induction n with
    | zero =>
      simp
      ring
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  have hSBP := hSBPgen (N - 1)
  rw [← hN1] at hSBP
  have hAB : ∀ k ∈ Finset.range (N - 1),
      (statA Δ η X k - statA Δ η X (k + 1)) * D (k + 1)
        = (-(2 * Δ * c * X (k + 1))) * D (k + 1) := by
    intro k hk
    have hkm : k < N - 1 := Finset.mem_range.mp hk
    have hk1 : 1 ≤ k + 1 := by omega
    have hkN : k + 1 ≤ N - 1 := by omega
    have hS := hstat (k + 1) hk1 hkN
    have he : (k + 1) - 1 = k := by omega
    rw [he] at hS
    have hR : (X (k + 1) - X k) - (X ((k + 1) + 1) - X (k + 1))
        = -((c * Δ ^ 2 / η) * X (k + 1)) := by
      linear_combination hS
    have hAeq : statA Δ η X k - statA Δ η X (k + 1)
        = 2 * Δ * η * (((X (k + 1) - X k) - (X ((k + 1) + 1) - X (k + 1)))
          / Δ) / Δ := by
      simp only [statA]
      ring
    rw [hAeq, hR]
    field_simp [hΔne, hηne]
  have hform : (∑ j ∈ Finset.range N, 2 * Δ * η * ((X (j + 1) - X j) / Δ)
        * ((D (j + 1) - D j) / Δ))
      = ∑ j ∈ Finset.range N, statA Δ η X j * (D (j + 1) - D j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [statA]
    ring
  have hred : (∑ j ∈ Finset.range N, statA Δ η X j * (D (j + 1) - D j))
      = ∑ j ∈ Finset.range (N - 1),
        (statA Δ η X j - statA Δ η X (j + 1)) * D (j + 1) := by
    rw [hSBP, hDN, hD0]
    simp only [mul_zero, sub_zero, zero_add]
  have hneg : (∑ j ∈ Finset.range (N - 1),
        (statA Δ η X j - statA Δ η X (j + 1)) * D (j + 1))
      = -∑ j ∈ Finset.range (N - 1), (2 * Δ * c * X (j + 1)) * D (j + 1) := by
    have h1 : (∑ j ∈ Finset.range (N - 1),
          (statA Δ η X j - statA Δ η X (j + 1)) * D (j + 1))
        = ∑ j ∈ Finset.range (N - 1),
          (-((2 * Δ * c * X (j + 1)) * D (j + 1))) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hABj := hAB j hj
      rw [hABj]
      ring
    rw [h1, Finset.sum_neg_distrib]
  have hL1 : (∑ j ∈ Finset.range N, 2 * Δ * η * ((X (j + 1) - X j) / Δ)
        * ((D (j + 1) - D j) / Δ))
      = -∑ j ∈ Finset.range (N - 1), (2 * Δ * c * X (j + 1)) * D (j + 1) := by
    rw [hform, hred]
    exact hneg
  have hL2 : (∑ j ∈ Finset.range N, 2 * Δ * c * X j * D j)
      = (∑ j ∈ Finset.range (N - 1), (2 * Δ * c * X (j + 1)) * D (j + 1))
        + (2 * Δ * c * X 0) * D 0 := by
    conv_lhs => rw [hN1]
    rw [Finset.sum_range_succ']
  have hB0D0 : (2 * Δ * c * X 0) * D 0 = 0 := by
    rw [hD0, mul_zero]
  rw [hLsplit, hL1, hL2, hB0D0, add_zero, neg_add_cancel]

/-- Vanishing energy forces the perturbation to zero. -/
theorem energyR_eq_zero (N : ℕ) (Δ η c : ℝ) (hΔ : 0 < Δ)
    (hη : 0 < η) (hc : 0 ≤ c) (D : ℕ → ℝ) (hE : energyR N Δ η c D = 0)
    (hD0 : D 0 = 0) (j : ℕ) (hj : j ≤ N) : D j = 0 := by
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hηne : η ≠ 0 := ne_of_gt hη
  simp only [energyR] at hE
  have hDE : ∀ i, i < N → D (i + 1) = D i := by
    intro i hi
    have hmem : i ∈ Finset.range N := Finset.mem_range.mpr hi
    have hnn : ∀ k ∈ Finset.range N,
        0 ≤ Δ * η * ((D (k + 1) - D k) / Δ) ^ 2 + Δ * c * (D k) ^ 2 := by
      intro k _
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg hΔ.le hη.le) (sq_nonneg _)
      · exact mul_nonneg (mul_nonneg hΔ.le hc) (sq_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hE
    have hterm := hall i hmem
    have hAi : Δ * η * ((D (i + 1) - D i) / Δ) ^ 2 = 0 := by
      have h2 : 0 ≤ Δ * η * ((D (i + 1) - D i) / Δ) ^ 2 :=
        mul_nonneg (mul_nonneg hΔ.le hη.le) (sq_nonneg _)
      have h3 : 0 ≤ Δ * c * (D i) ^ 2 :=
        mul_nonneg (mul_nonneg hΔ.le hc) (sq_nonneg _)
      linarith [hterm, h2, h3]
    have hsq : ((D (i + 1) - D i) / Δ) ^ 2 = 0 := by
      have hne : Δ * η ≠ 0 := mul_ne_zero hΔne hηne
      exact (mul_eq_zero.mp hAi).resolve_left hne
    have hdiv : (D (i + 1) - D i) / Δ = 0 := sq_eq_zero_iff.mp hsq
    have hdiff : D (i + 1) - D i = 0 :=
      (div_eq_zero_iff.mp hdiv).resolve_right hΔne
    exact sub_eq_zero.mp hdiff
  have hchain : ∀ k, k ≤ N → D k = D 0 := by
    intro k
    induction k with
    | zero => exact fun _ => rfl
    | succ m ih =>
      intro hm
      have hmN : m < N := by omega
      have h1 : D (m + 1) = D m := hDE m hmN
      have h2 : D m = D 0 := ih (by omega)
      exact h1.trans h2
  exact (hchain j hj).trans hD0

/-- Cost difference equals the perturbation energy for stationary paths. -/
theorem cost_sub_eq_energy (N : ℕ) (hN : 0 < N) (Δ η c : ℝ) (hΔ : 0 < Δ)
    (hη : 0 < η) (x : Fin (N + 1) → ℝ) (X0 : ℝ) (hx0 : x 0 = X0)
    (hxN : x (Fin.last N) = 0)
    (hstatX : ∀ j, 1 ≤ j → j ≤ N - 1 →
      -(extPath N x (j - 1)) + 2 * extPath N x j - extPath N x (j + 1)
        + (c * Δ ^ 2 / η) * extPath N x j = 0)
    (y : Fin (N + 1) → ℝ) (hy0 : y 0 = X0) (hyN : y (Fin.last N) = 0) :
    liquidationCost N Δ η c y - liquidationCost N Δ η c x
      = energyR N Δ η c (fun j => extPath N y j - extPath N x j) := by
  have eCostX : liquidationCost N Δ η c x = costR N Δ η c (extPath N x) :=
    cost_bridge N Δ η c x
  have eCostY : liquidationCost N Δ η c y = costR N Δ η c (extPath N y) :=
    cost_bridge N Δ η c y
  have eExp : costR N Δ η c (extPath N y) - costR N Δ η c (extPath N x)
      = linearR N Δ η c (extPath N x)
          (fun j => extPath N y j - extPath N x j)
        + energyR N Δ η c (fun j => extPath N y j - extPath N x j) :=
    cost_expansion N Δ η c (extPath N x) (extPath N y)
  have hY0 : extPath N y 0 = X0 := extPath_zero N y X0 hy0
  have hX0 : extPath N x 0 = X0 := extPath_zero N x X0 hx0
  have hYN : extPath N y N = 0 := extPath_last N y hyN
  have hXN : extPath N x N = 0 := extPath_last N x hxN
  have hD0 : (fun j => extPath N y j - extPath N x j) 0 = 0 := by
    change extPath N y 0 - extPath N x 0 = 0
    rw [hY0, hX0, sub_self]
  have hDN : (fun j => extPath N y j - extPath N x j) N = 0 := by
    change extPath N y N - extPath N x N = 0
    rw [hYN, hXN, sub_self]
  have hL0 : linearR N Δ η c (extPath N x)
      (fun j => extPath N y j - extPath N x j) = 0 :=
    linearR_eq_zero N hN Δ η c hΔ hη _ _ hstatX hD0 hDN
  linarith [eCostX, eCostY, eExp, hL0]

/-- The forced path for `N = 1`. -/
def xOne (N : ℕ) (X0 : ℝ) : Fin (N + 1) → ℝ :=
  fun j => if j = 0 then X0 else 0

/-- The forced path starts at `X0`. -/
theorem xOne_zero (N : ℕ) (X0 : ℝ) : xOne N X0 0 = X0 := by
  simp only [xOne]
  exact ite_true X0 0

/-- The forced path ends at `0` when `N = 1`. -/
theorem xOne_last (N : ℕ) (X0 : ℝ) (hN1 : N = 1) :
    xOne N X0 (Fin.last N) = 0 := by
  have hlast : (Fin.last N).val = N := by simp
  have hne : Fin.last N ≠ (0 : Fin (N + 1)) := by
    intro h
    have h2 := congrArg Fin.val h
    rw [hlast] at h2
    simp at h2
    omega
  simp only [xOne]
  rw [ite_eq_right hne]

theorem existsUnique_minimizer_liquidationCost (N : ℕ) (hN : 0 < N)
    (Δ η c X0 : ℝ) (hΔ : 0 < Δ) (hη : 0 < η) (hc : 0 ≤ c) :
    ∃ x : Fin (N + 1) → ℝ, x 0 = X0 ∧ x (Fin.last N) = 0
      ∧ (∀ y : Fin (N + 1) → ℝ, y 0 = X0 → y (Fin.last N) = 0 →
          liquidationCost N Δ η c x ≤ liquidationCost N Δ η c y)
      ∧ (∀ k : Fin N, 0 < k.val →
          -(x ⟨k.val - 1, by omega⟩) + 2 * x k.castSucc - x k.succ
            + (c * Δ ^ 2 / η) * x k.castSucc = 0)
      ∧ (∀ y : Fin (N + 1) → ℝ, y 0 = X0 → y (Fin.last N) = 0 →
          (∀ z : Fin (N + 1) → ℝ, z 0 = X0 → z (Fin.last N) = 0 →
            liquidationCost N Δ η c y ≤ liquidationCost N Δ η c z) → y = x) := by
  by_cases hN1 : N = 1
  · have hcases : ∀ j : Fin (N + 1), j = 0 ∨ j = Fin.last N := by
      intro j
      have hj2 := j.2
      have hvo : j.val = 0 ∨ j.val = 1 := by omega
      cases hvo with
      | inl h0 =>
        exact Or.inl (Fin.ext_iff.mpr (by simp [h0]))
      | inr h1 =>
        exact Or.inr (Fin.ext_iff.mpr (by simp [h1, hN1]))
    have hEq : ∀ y : Fin (N + 1) → ℝ, y 0 = X0 → y (Fin.last N) = 0 →
        y = xOne N X0 := by
      intro y hy0 hyN
      ext j
      cases hcases j with
      | inl hj0 => rw [hj0, hy0, xOne_zero N X0]
      | inr hjL => rw [hjL, hyN, xOne_last N X0 hN1]
    refine ⟨xOne N X0, xOne_zero N X0, xOne_last N X0 hN1, ?_, ?_, ?_⟩
    · intro y hy0 hyN
      rw [hEq y hy0 hyN]
    · intro k hk
      have hF : False := by
        have hk2 := k.2
        omega
      exact hF.elim
    · intro y hy0 hyN _
      exact hEq y hy0 hyN
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨u, hu⟩ := sysT_solution (N - 1) (by omega) (c * Δ ^ 2 / η)
      (div_nonneg (mul_nonneg hc (sq_nonneg Δ)) hη.le) X0
    have hstatX : ∀ j, 1 ≤ j → j ≤ N - 1 →
        -(extPath N (xStar N hN2 u X0) (j - 1))
          + 2 * extPath N (xStar N hN2 u X0) j
          - extPath N (xStar N hN2 u X0) (j + 1)
          + (c * Δ ^ 2 / η) * extPath N (xStar N hN2 u X0) j = 0 :=
      stationarity_ext N Δ η c (xStar N hN2 u X0)
        (xStar_stationarity N hN2 Δ η c X0 u hu)
    have hoptH : ∀ y : Fin (N + 1) → ℝ, y 0 = X0 → y (Fin.last N) = 0 →
        liquidationCost N Δ η c (xStar N hN2 u X0)
          ≤ liquidationCost N Δ η c y := by
      intro y hy0 hyN
      have hkey := cost_sub_eq_energy N hN Δ η c hΔ hη (xStar N hN2 u X0) X0
        (xStar_zero N hN2 u X0) (xStar_last N hN2 u X0) hstatX y hy0 hyN
      have hEge : 0 ≤ energyR N Δ η c
          (fun j => extPath N y j - extPath N (xStar N hN2 u X0) j) :=
        energyR_nonneg N Δ η c hΔ hη hc _
      linarith [hkey, hEge]
    have hstatH : ∀ k : Fin N, 0 < k.val →
        -(xStar N hN2 u X0 ⟨k.val - 1, by omega⟩)
          + 2 * xStar N hN2 u X0 k.castSucc - xStar N hN2 u X0 k.succ
          + (c * Δ ^ 2 / η) * xStar N hN2 u X0 k.castSucc = 0 :=
      xStar_stationarity N hN2 Δ η c X0 u hu
    refine ⟨xStar N hN2 u X0, xStar_zero N hN2 u X0,
      xStar_last N hN2 u X0, hoptH, hstatH, ?_⟩
    intro y hy0 hyN hymin
    have hle1 := hymin (xStar N hN2 u X0) (xStar_zero N hN2 u X0)
      (xStar_last N hN2 u X0)
    have hle2 := hoptH y hy0 hyN
    have heq := le_antisymm hle1 hle2
    have hkey := cost_sub_eq_energy N hN Δ η c hΔ hη (xStar N hN2 u X0) X0
      (xStar_zero N hN2 u X0) (xStar_last N hN2 u X0) hstatX y hy0 hyN
    have hE0 : energyR N Δ η c
        (fun j => extPath N y j - extPath N (xStar N hN2 u X0) j) = 0 := by
      linarith [hkey, heq]
    have hY0 : extPath N y 0 = X0 := extPath_zero N y X0 hy0
    have hX0 : extPath N (xStar N hN2 u X0) 0 = X0 :=
      extPath_zero N _ X0 (xStar_zero N hN2 u X0)
    have hD0 : (fun j => extPath N y j - extPath N (xStar N hN2 u X0) j) 0
        = 0 := by
      change extPath N y 0 - extPath N (xStar N hN2 u X0) 0 = 0
      rw [hY0, hX0, sub_self]
    ext j
    have hjN : j.val ≤ N := by
      have h2 := j.2
      omega
    have h1 := energyR_eq_zero N Δ η c hΔ hη hc
      (fun k => extPath N y k - extPath N (xStar N hN2 u X0) k)
      hE0 hD0 j.val hjN
    have hYj : extPath N y j.val = y j := extPath_val N y j
    have hXj : extPath N (xStar N hN2 u X0) j.val
        = xStar N hN2 u X0 j :=
      extPath_val N _ j
    have h1' : extPath N y j.val - extPath N (xStar N hN2 u X0) j.val
        = 0 := h1
    rw [hYj, hXj] at h1'
    exact sub_eq_zero.mp h1'

end MathFin
