/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Adam Kiezun
-/
module

public import MathFin.Probability.Analysis.DerivOfDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Arsinh

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

The continuous minimisation (that this closed form is optimal among all admissible trajectories)
is a calculus-of-variations claim that needs function-space machinery beyond Mathlib's current
pin and is not proved here. What is proved is its discrete counterpart: over `N` periods of length
`Δ` the cost `liquidationCost` is a positive-definite quadratic form on the feasible paths
(`X_0` at the start, flat at the end), so it has exactly one minimizer
(`existsUnique_minimizer_liquidationCost`). That minimizer is the hyperbolic-sine path
`X_0 sinh(κ̃ (N − k) Δ) / sinh(κ̃ N Δ)`, `cosh (κ̃ Δ) = 1 + c Δ² / (2 η)`: the continuous
`almgrenChrissPath` at the discrete rate `κ̃` (`liquidationPath`), or the straight line when
`c = 0`.

## Main definitions

* `almgrenChrissPath`: the closed-form trajectory `X(t) = X_0 · sinh (κ (T − t)) / sinh (κ T)`.
* `liquidationCost`: the finite quadratic liquidation cost over `N` periods.
* `liquidationPaths`: the feasible inventory paths, from `X_0` down to `0`.
* `liquidationRate`, `liquidationPath`: the discrete rate `κ̃` and the candidate minimizer.

## Main results

* `almgrenChrissPath_at_zero`: `X(0) = X_0`.
* `almgrenChrissPath_at_terminal`: `X(T) = 0`.
* `hasDerivAt_almgrenChrissPath`: first derivative.
* `almgrenChrissPath_satisfies_EL`: `X''(t) = κ² · X(t)`.
* `cosh_liquidationRate_mul`: `cosh (κ̃ Δ) = 1 + c Δ² / (2 η)`.
* `isMinOn_liquidationPath`, `eq_liquidationPath_of_isMinOn`: `liquidationPath` minimizes
  `liquidationCost` on the feasible paths, and every minimizer equals it.
* `existsUnique_minimizer_liquidationCost`: the finite liquidation cost has a unique feasible
  minimizer.

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

/-- The **discrete liquidation cost** of the inventory path `x` over `N` periods of length `Δ`:
`∑ₖ Δ (η ((xₖ₊₁ − xₖ)/Δ)² + c xₖ²)`, the Riemann sum of `∫ (η X'² + c X²) dt` (impact `η`,
risk `c`). -/
noncomputable def liquidationCost (N : ℕ) (Δ η c : ℝ) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ k : Fin N, Δ * (η * ((x k.succ - x k.castSucc) / Δ) ^ 2 + c * x k.castSucc ^ 2)

/-- The **feasible inventory paths**: the paths starting at `X₀` and ending flat. -/
def liquidationPaths (N : ℕ) (X₀ : ℝ) : Set (Fin (N + 1) → ℝ) :=
  {x | x 0 = X₀ ∧ x (Fin.last N) = 0}

/-- The **discrete rate** `κ̃ = 2 arsinh (√(c/η) Δ / 2) / Δ`, the solution of
`cosh (κ̃ Δ) = 1 + c Δ² / (2 η)` (`cosh_liquidationRate_mul`); as `Δ → 0` it should tend to
the continuous rate `√(c/η)`, which is not proved here. -/
noncomputable def liquidationRate (Δ η c : ℝ) : ℝ :=
  2 * Real.arsinh (√(c / η) * Δ / 2) / Δ

/-- The **minimizing liquidation path**: `X₀ sinh(κ̃ (N − k) Δ) / sinh(κ̃ N Δ)`, that is the
continuous `almgrenChrissPath` at the discrete rate `κ̃` and the dates `k Δ`; with no risk
penalty (`c = 0`, where `κ̃ = 0` and the closed form degenerates) the straight line
`X₀ (N − k) / N`. -/
noncomputable def liquidationPath (N : ℕ) (Δ η c X₀ : ℝ) (k : Fin (N + 1)) : ℝ :=
  if c = 0 then X₀ * (N - k) / N
  else almgrenChrissPath X₀ (liquidationRate Δ η c) (N * Δ) (k * Δ)

/-- The discrete rate solves `cosh (κ̃ Δ) = 1 + c Δ² / (2 η)`. -/
theorem cosh_liquidationRate_mul {Δ η c : ℝ} (hΔ : Δ ≠ 0) (hcη : 0 ≤ c / η) :
    Real.cosh (liquidationRate Δ η c * Δ) = 1 + (c * Δ ^ 2 / η) / 2 := by
  have h : (√(c / η) * Δ / 2) ^ 2 = c / η * Δ ^ 2 / 4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hcη]
    ring
  rw [liquidationRate, div_mul_cancel₀ _ hΔ, Real.cosh_two_mul, Real.cosh_sq, Real.sinh_arsinh, h]
  ring

section Discrete

open scoped Fin.NatCast

variable {N : ℕ} {Δ η c : ℝ}

/-- The cost along `X : ℕ → ℝ`; only `X 0, …, X N` enter. -/
private noncomputable def costNat (N : ℕ) (Δ η c : ℝ) (X : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, Δ * (η * ((X (k + 1) - X k) / Δ) ^ 2 + c * X k ^ 2)

/-- A path on `Fin (N + 1)` read along `ℕ`, wrapping around after `N`. -/
private def pathNat (x : Fin (N + 1) → ℝ) (j : ℕ) : ℝ := x (j : Fin (N + 1))

private theorem pathNat_val (x : Fin (N + 1) → ℝ) (j : Fin (N + 1)) : pathNat x j.val = x j := by
  simp [pathNat]

private theorem pathNat_of_le {x : Fin (N + 1) → ℝ} {X : ℕ → ℝ} (hx : ∀ k : Fin (N + 1), x k = X k)
    {j : ℕ} (hj : j ≤ N) : pathNat x j = X j := by
  rw [pathNat, hx, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]

private theorem liquidationCost_eq_costNat (x : Fin (N + 1) → ℝ) :
    liquidationCost N Δ η c x = costNat N Δ η c (pathNat x) := by
  rw [liquidationCost, costNat, ← Fin.sum_univ_eq_sum_range (fun k ↦ Δ * (η * ((pathNat x (k + 1)
    - pathNat x k) / Δ) ^ 2 + c * pathNat x k ^ 2)) N]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h₁ := pathNat_val x k.castSucc
  have h₂ := pathNat_val x k.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
  rw [h₁, h₂]

/-- **Cross terms vanish along a stationary path.** If `X` satisfies the discrete
Euler–Lagrange equation `Xₖ − 2 Xₖ₊₁ + Xₖ₊₂ = (c Δ²/η) Xₖ₊₁` and `W` vanishes at both ends,
the cost of `X + W` is the sum of the costs. -/
private theorem costNat_add_of_stationary (hΔ : Δ ≠ 0) (hη : η ≠ 0) {X W : ℕ → ℝ}
    (hX : ∀ k, k + 2 ≤ N → X k - 2 * X (k + 1) + X (k + 2) = c * Δ ^ 2 / η * X (k + 1))
    (hW₀ : W 0 = 0) (hW : W N = 0) :
    costNat N Δ η c (fun j ↦ X j + W j) = costNat N Δ η c X + costNat N Δ η c W := by
  have key : ∑ k ∈ Finset.range N, ((X (k + 1) - X k) * (W (k + 1) - W k)
      + c * Δ ^ 2 / η * X k * W k) = 0 := by
    cases N with
    | zero => simp
    | succ n =>
      have h : ∀ m < n + 1, ∑ k ∈ Finset.range (m + 1), ((X (k + 1) - X k) * (W (k + 1) - W k)
          + c * Δ ^ 2 / η * X k * W k) = (X (m + 1) - X m) * W (m + 1) := by
        intro m
        induction m with
        | zero => intro _; simp [hW₀]
        | succ m ih =>
          intro hm
          have h₂ := hX m (by omega)
          rw [show m + 2 = m + 1 + 1 from rfl] at h₂
          rw [Finset.sum_range_succ, ih (by omega)]
          linear_combination (-W (m + 1)) * h₂
      rw [h n (by omega), hW, mul_zero]
  have hterm (k : ℕ) : Δ * (η * ((X (k + 1) + W (k + 1) - (X k + W k)) / Δ) ^ 2
      + c * (X k + W k) ^ 2) = Δ * (η * ((X (k + 1) - X k) / Δ) ^ 2 + c * X k ^ 2)
        + Δ * (η * ((W (k + 1) - W k) / Δ) ^ 2 + c * W k ^ 2)
        + 2 * η / Δ * ((X (k + 1) - X k) * (W (k + 1) - W k) + c * Δ ^ 2 / η * X k * W k) := by
    field_simp
    ring
  have hsum : costNat N Δ η c (fun j ↦ X j + W j) = costNat N Δ η c X + costNat N Δ η c W
      + 2 * η / Δ * ∑ k ∈ Finset.range N, ((X (k + 1) - X k) * (W (k + 1) - W k)
        + c * Δ ^ 2 / η * X k * W k) := by
    unfold costNat
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ hterm k
  rw [hsum, key, mul_zero, add_zero]

private theorem costNat_nonneg (hΔ : 0 < Δ) (hη : 0 < η) (hc : 0 ≤ c) (X : ℕ → ℝ) :
    0 ≤ costNat N Δ η c X :=
  Finset.sum_nonneg fun k _ ↦ by positivity

/-- A path of zero cost that starts at `0` is `0` up to `N`: the increments carry the cost. -/
private theorem eq_zero_of_costNat_eq_zero (hΔ : 0 < Δ) (hη : 0 < η) (hc : 0 ≤ c) {W : ℕ → ℝ}
    (h : costNat N Δ η c W = 0) (hW₀ : W 0 = 0) : ∀ j ≤ N, W j = 0 := by
  have hstep (k : ℕ) (hk : k < N) : W (k + 1) = W k := by
    have hnn : ∀ i ∈ Finset.range N,
        0 ≤ Δ * (η * ((W (i + 1) - W i) / Δ) ^ 2 + c * W i ^ 2) := fun i _ ↦ by positivity
    have hk₀ := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h k (Finset.mem_range.2 hk)
    have hA : 0 ≤ η * ((W (k + 1) - W k) / Δ) ^ 2 := by positivity
    have hB : 0 ≤ c * W k ^ 2 := by positivity
    have hsum := (mul_eq_zero.1 hk₀).resolve_left hΔ.ne'
    have hA₀ : η * ((W (k + 1) - W k) / Δ) ^ 2 = 0 := by linarith
    have hd := (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 hA₀).resolve_left hη.ne')
    exact sub_eq_zero.1 ((div_eq_zero_iff.1 hd).resolve_right hΔ.ne')
  intro j
  induction j with
  | zero => exact fun _ ↦ hW₀
  | succ j ih => exact fun hj ↦ (hstep j (by omega)).trans (ih (by omega))

/-- **A stationary feasible path minimizes, and uniquely.** If `x` is feasible and its values
satisfy the discrete Euler–Lagrange equation, every other feasible path costs at least as much,
and costs more unless it is `x`. -/
private theorem liquidationCost_le_and_eq_of_stationary (hΔ : 0 < Δ) (hη : 0 < η) (hc : 0 ≤ c)
    {X₀ : ℝ} {x : Fin (N + 1) → ℝ} (hx : x ∈ liquidationPaths N X₀)
    (hstat : ∀ k, k + 2 ≤ N → pathNat x k - 2 * pathNat x (k + 1) + pathNat x (k + 2)
      = c * Δ ^ 2 / η * pathNat x (k + 1))
    {y : Fin (N + 1) → ℝ} (hy : y ∈ liquidationPaths N X₀) :
    liquidationCost N Δ η c x ≤ liquidationCost N Δ η c y
      ∧ (liquidationCost N Δ η c y ≤ liquidationCost N Δ η c x → y = x) := by
  obtain ⟨hx₀, hxN⟩ := hx
  obtain ⟨hy₀, hyN⟩ := hy
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℝ, ∀ j, W j = pathNat y j - pathNat x j := ⟨_, fun _ ↦ rfl⟩
  have hW₀ : W 0 = 0 := by simp [hW, pathNat, hx₀, hy₀]
  have hWN : W N = 0 := by simp [hW, pathNat, Fin.natCast_eq_last, hxN, hyN]
  have hsplit : liquidationCost N Δ η c y
      = liquidationCost N Δ η c x + costNat N Δ η c W := by
    rw [liquidationCost_eq_costNat, liquidationCost_eq_costNat,
      ← costNat_add_of_stationary hΔ.ne' hη.ne' hstat hW₀ hWN]
    congr 1
    funext j
    rw [hW]
    ring
  have hnonneg := costNat_nonneg (N := N) hΔ hη hc W
  refine ⟨by linarith, fun hle ↦ ?_⟩
  have hzero := eq_zero_of_costNat_eq_zero hΔ hη hc (by linarith) hW₀
  funext j
  have := hzero j (Nat.le_of_lt_succ j.2)
  rw [hW, pathNat_val, pathNat_val] at this
  exact sub_eq_zero.1 this

/-- A profile `φ` with `φ (t + 1) + φ (t − 1) = (2 + a) φ t` and `φ 0 = 0`, `φ N ≠ 0`, scaled to
`X k = X₀ φ (N − k) / φ N`, starts at `X₀`, ends at `0`, and satisfies the discrete
Euler–Lagrange equation with coefficient `a`. -/
private theorem stationary_of_profile {φ : ℝ → ℝ} {a X₀ : ℝ}
    (hφ : ∀ t, φ (t + 1) + φ (t - 1) = (2 + a) * φ t) (h₀ : φ 0 = 0) (hN : φ N ≠ 0)
    {X : ℕ → ℝ} (hX : ∀ k, X k = X₀ * φ (N - k) / φ N) :
    X 0 = X₀ ∧ X N = 0 ∧ ∀ k, k + 2 ≤ N → X k - 2 * X (k + 1) + X (k + 2) = a * X (k + 1) := by
  refine ⟨by simp [hX, hN], by simp [hX, h₀], fun k _ ↦ ?_⟩
  have h := hφ ((N : ℝ) - (k + 1))
  rw [show (N : ℝ) - (k + 1) + 1 = N - k by ring,
    show (N : ℝ) - (k + 1) - 1 = N - (k + 2) by ring] at h
  simp only [hX]
  push_cast
  linear_combination (X₀ / φ N) * h

/-- The candidate is feasible and satisfies the discrete Euler–Lagrange equation. -/
private theorem liquidationPath_spec (hN : 0 < N) (hΔ : 0 < Δ) (hη : 0 < η) (hc : 0 ≤ c)
    (X₀ : ℝ) :
    ∃ X : ℕ → ℝ, (∀ k : Fin (N + 1), liquidationPath N Δ η c X₀ k = X k) ∧ X 0 = X₀ ∧ X N = 0
      ∧ ∀ k, k + 2 ≤ N → X k - 2 * X (k + 1) + X (k + 2) = c * Δ ^ 2 / η * X (k + 1) := by
  rcases hc.eq_or_lt with h₀ | hpos
  · subst h₀
    obtain ⟨h₁, h₂, h₃⟩ := stationary_of_profile (N := N) (φ := fun t ↦ t) (a := 0 * Δ ^ 2 / η)
      (X₀ := X₀) (X := fun k ↦ X₀ * ((N : ℝ) - k) / N) (fun t ↦ by ring) rfl
      (by simpa using hN.ne') fun k ↦ rfl
    exact ⟨_, fun k ↦ by simp [liquidationPath], h₁, h₂, h₃⟩
  · have hθ : 0 < 2 * Real.arsinh (√(c / η) * Δ / 2) := by
      refine mul_pos two_pos (Real.sinh_pos_iff.1 ?_)
      rw [Real.sinh_arsinh]
      exact div_pos (mul_pos (Real.sqrt_pos.2 (div_pos hpos hη)) hΔ) two_pos
    have hcosh := cosh_liquidationRate_mul hΔ.ne' (div_nonneg hc hη.le)
    rw [liquidationRate, div_mul_cancel₀ _ hΔ.ne'] at hcosh
    obtain ⟨h₁, h₂, h₃⟩ := stationary_of_profile (N := N)
      (φ := fun t ↦ Real.sinh (2 * Real.arsinh (√(c / η) * Δ / 2) * t))
      (a := c * Δ ^ 2 / η) (X₀ := X₀)
      (X := fun k ↦ X₀ * Real.sinh (2 * Real.arsinh (√(c / η) * Δ / 2) * (N - k))
        / Real.sinh (2 * Real.arsinh (√(c / η) * Δ / 2) * N))
      (fun t ↦ by
        rw [mul_add, mul_sub, mul_one, Real.sinh_add, Real.sinh_sub]
        linear_combination (2 * Real.sinh (2 * Real.arsinh (√(c / η) * Δ / 2) * t)) * hcosh)
      (by simp) (Real.sinh_pos_iff.2 (mul_pos hθ (Nat.cast_pos.2 hN))).ne' fun k ↦ rfl
    refine ⟨_, fun k ↦ ?_, h₁, h₂, h₃⟩
    have hΔ' := hΔ.ne'
    have e : ∀ t : ℝ, liquidationRate Δ η c * (t * Δ)
        = 2 * Real.arsinh (√(c / η) * Δ / 2) * t := fun t ↦ by
      rw [liquidationRate]
      field_simp
    simp only [liquidationPath, hpos.ne', ↓reduceIte]
    rw [almgrenChrissPath, ← mul_sub_right_distrib, e, e]

end Discrete

/-- **The liquidation path is feasible.** -/
theorem liquidationPath_mem_liquidationPaths {N : ℕ} (hN : 0 < N) {Δ η c : ℝ} (hΔ : 0 < Δ)
    (hη : 0 < η) (hc : 0 ≤ c) (X₀ : ℝ) :
    liquidationPath N Δ η c X₀ ∈ liquidationPaths N X₀ := by
  obtain ⟨X, hX, h₀, h₁, -⟩ := liquidationPath_spec hN hΔ hη hc X₀
  exact ⟨by simpa [hX] using h₀, by simpa [hX] using h₁⟩

/-- **The liquidation path minimizes the cost** on the feasible paths. -/
theorem isMinOn_liquidationPath {N : ℕ} (hN : 0 < N) {Δ η c : ℝ} (hΔ : 0 < Δ) (hη : 0 < η)
    (hc : 0 ≤ c) (X₀ : ℝ) :
    IsMinOn (liquidationCost N Δ η c) (liquidationPaths N X₀) (liquidationPath N Δ η c X₀) := by
  obtain ⟨X, hX, h₀, h₁, hstat⟩ := liquidationPath_spec hN hΔ hη hc X₀
  refine isMinOn_iff.2 fun y hy ↦ (liquidationCost_le_and_eq_of_stationary hΔ hη hc
    (liquidationPath_mem_liquidationPaths hN hΔ hη hc X₀) (fun k hk ↦ ?_) hy).1
  simp only [pathNat_of_le hX (show k ≤ N by omega), pathNat_of_le hX (show k + 1 ≤ N by omega),
    pathNat_of_le hX (show k + 2 ≤ N by omega)]
  exact hstat k hk

/-- **Every minimizer of the cost on the feasible paths is the liquidation path.** -/
theorem eq_liquidationPath_of_isMinOn {N : ℕ} (hN : 0 < N) {Δ η c : ℝ} (hΔ : 0 < Δ) (hη : 0 < η)
    (hc : 0 ≤ c) (X₀ : ℝ) {x : Fin (N + 1) → ℝ} (hx : x ∈ liquidationPaths N X₀)
    (hmin : IsMinOn (liquidationCost N Δ η c) (liquidationPaths N X₀) x) :
    x = liquidationPath N Δ η c X₀ := by
  obtain ⟨X, hX, h₀, h₁, hstat⟩ := liquidationPath_spec hN hΔ hη hc X₀
  refine (liquidationCost_le_and_eq_of_stationary hΔ hη hc
    (liquidationPath_mem_liquidationPaths hN hΔ hη hc X₀) (fun k hk ↦ ?_) hx).2
    (isMinOn_iff.1 hmin _ (liquidationPath_mem_liquidationPaths hN hΔ hη hc X₀))
  simp only [pathNat_of_le hX (show k ≤ N by omega), pathNat_of_le hX (show k + 1 ≤ N by omega),
    pathNat_of_le hX (show k + 2 ≤ N by omega)]
  exact hstat k hk

/-- **The discrete liquidation problem has exactly one solution.** Over `N > 0` periods of length
`Δ > 0`, with impact `η > 0` and risk `c ≥ 0`, the cost `liquidationCost` has a unique minimizer
among the paths from `X₀` to `0`; it is `liquidationPath`, the discrete hyperbolic-sine path. -/
theorem existsUnique_minimizer_liquidationCost {N : ℕ} (hN : 0 < N) {Δ η c : ℝ} (hΔ : 0 < Δ)
    (hη : 0 < η) (hc : 0 ≤ c) (X₀ : ℝ) :
    ∃! x : Fin (N + 1) → ℝ, x ∈ liquidationPaths N X₀
      ∧ IsMinOn (liquidationCost N Δ η c) (liquidationPaths N X₀) x :=
  ⟨liquidationPath N Δ η c X₀, ⟨liquidationPath_mem_liquidationPaths hN hΔ hη hc X₀,
    isMinOn_liquidationPath hN hΔ hη hc X₀⟩,
    fun _ hy ↦ eq_liquidationPath_of_isMinOn hN hΔ hη hc X₀ hy.1 hy.2⟩

end MathFin
