/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaRemainder
public import MathFin.Probability.Brownian.UnifPart

/-! # Itô's formula for `f(t, X_t, Y_t)` along one path: the Taylor argument

The deterministic half of the two-factor Itô formula, for `f(t, x, y)` with partial derivatives
`f_t`, `f_x`, `f_y`, `f_xx`, `f_xy = ∂_y f_x`, `f_yy`. Along a time grid `tₖ`, and paths `xₖ`, `yₖ`
the telescoping sum of `f(tₖ₊₁, xₖ₊₁, yₖ₊₁) − f(tₖ, xₖ, yₖ)` is an exact sum of the first-order
terms, the second-order terms `½ f_xx Δx² + f_xy Δx Δy + ½ f_yy Δy²` and the remainders
`discreteTaylorRemainder3D` (`discrete_ito_formula_3d`). The remainder is estimated without a
third derivative and without a chain rule through `(x, y)`: it splits into the time increment at
frozen `(x₁, y₁)`, the `x`-Taylor remainder of the section `u ↦ f(t₀, u, y₁)`, the `y`-Taylor
remainder of `v ↦ f(t₀, x₀, v)`, and two mean-value corrections, one for `f_x(t₀, x₀, ·)` and one
for `f_xx(t₀, x₀, ·)`. Once `f_t`, `f_xx`, `f_xy`, `f_yy` oscillate by less than `η` on a cell, the
remainder is at most `η (Δt + 3 Δx² + 2 Δy²)` (`abs_discreteTaylorRemainder3D_le_of_osc`). Along
continuous paths with bounded squared-increment sums the remainders vanish
(`tendsto_sum_discreteTaylorRemainder3D`), by uniform continuity on a compact box. With convergent
Riemann sums for the first-order and second-order terms, the formula holds along the path
(`ito_formula_3d_of_tendsto`).

The one-factor case is `ItoFormulaAdaptedTD`: `abs_discreteTaylorRemainder2D_le_of_osc`,
`tendsto_sum_discreteTaylorRemainder2D`, `ito_formula_td_of_tendsto`. The section Taylor bound is
`abs_discreteTaylorRemainder_le_of_abs_sub_le`, shared with it.

## Main definitions

* `discreteTaylorRemainder3D`: the deviation of `f(t₁, x₁, y₁) − f(t₀, x₀, y₀)` from its Taylor
  expansion at `(t₀, x₀, y₀)`, first order in time and second order in `(x, y)`.

## Main results

* `discrete_ito_formula_3d`: the exact telescoping decomposition along a grid.
* `abs_discreteTaylorRemainder3D_le_of_osc`: the remainder under oscillation bounds on `f_t`,
  `f_xx`, `f_xy`, `f_yy`.
* `tendsto_sum_discreteTaylorRemainder3D`: the remainders along uniform partitions of a continuous
  path with bounded squared increments sum to `0`.
* `ito_formula_3d_of_tendsto`: Itô's formula along one path, given the limits of the time and
  drift sums and of the combined martingale and second-order sums.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.3.6
* [Revuz and Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], Theorem IV.3.3

## Tags

Itô formula, Itô lemma, two-dimensional Itô formula, Taylor remainder, space-time function,
discrete Itô formula, MSC 60H05, MSC 60H10
-/

@[expose] public section

namespace MathFin

open MeasureTheory Filter Topology Set
open scoped NNReal

/-- **The Taylor remainder of `f(t, x, y)` over one step**: the deviation of
`f(t₁, x₁, y₁) − f(t₀, x₀, y₀)` from its expansion at `(t₀, x₀, y₀)`, first order in time and
second order in `(x, y)`,

`R := f(t₁, x₁, y₁) − f(t₀, x₀, y₀) − f_t Δt − f_x Δx − f_y Δy − ½ f_xx Δx² − f_xy Δx Δy
  − ½ f_yy Δy²`,

with the partials evaluated at `(t₀, x₀, y₀)`. It is *defined* so that the discrete formula
`discrete_ito_formula_3d` is an identity; the content is the bound on `R`
(`abs_discreteTaylorRemainder3D_le_of_osc`). -/
noncomputable def discreteTaylorRemainder3D
    (f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ) (t₀ t₁ x₀ x₁ y₀ y₁ : ℝ) : ℝ :=
  f t₁ x₁ y₁ - f t₀ x₀ y₀ - f_t t₀ x₀ y₀ * (t₁ - t₀) - f_x t₀ x₀ y₀ * (x₁ - x₀)
    - f_y t₀ x₀ y₀ * (y₁ - y₀) - 1 / 2 * (f_xx t₀ x₀ y₀ * (x₁ - x₀) ^ 2)
    - f_xy t₀ x₀ y₀ * ((x₁ - x₀) * (y₁ - y₀)) - 1 / 2 * (f_yy t₀ x₀ y₀ * (y₁ - y₀) ^ 2)

/-- **The discrete Itô formula for `f(t, x, y)`.** For any grid `t`, paths `X`, `Y` and formal
partials,

`f(t_N, X_N, Y_N) − f(t₀, X₀, Y₀) = ∑ f_t Δt + ∑ f_x ΔX + ∑ f_y ΔY + ½ ∑ f_xx ΔX²
  + ∑ f_xy ΔX ΔY + ½ ∑ f_yy ΔY² + ∑ R_k`,

the partials at `(tₖ, Xₖ, Yₖ)` and `R_k = discreteTaylorRemainder3D …`. No probability: telescoping
and the definition of `R_k`. -/
theorem discrete_ito_formula_3d
    (N : ℕ) (t X Y : ℕ → ℝ) (f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ) :
    f (t N) (X N) (Y N) - f (t 0) (X 0) (Y 0) =
      (∑ k ∈ Finset.range N, f_t (t k) (X k) (Y k) * (t (k + 1) - t k)) +
      (∑ k ∈ Finset.range N, f_x (t k) (X k) (Y k) * (X (k + 1) - X k)) +
      (∑ k ∈ Finset.range N, f_y (t k) (X k) (Y k) * (Y (k + 1) - Y k)) +
      (1 / 2) * (∑ k ∈ Finset.range N, f_xx (t k) (X k) (Y k) * (X (k + 1) - X k) ^ 2) +
      (∑ k ∈ Finset.range N,
        f_xy (t k) (X k) (Y k) * ((X (k + 1) - X k) * (Y (k + 1) - Y k))) +
      (1 / 2) * (∑ k ∈ Finset.range N, f_yy (t k) (X k) (Y k) * (Y (k + 1) - Y k) ^ 2) +
      ∑ k ∈ Finset.range N, discreteTaylorRemainder3D f f_t f_x f_y f_xx f_xy f_yy
        (t k) (t (k + 1)) (X k) (X (k + 1)) (Y k) (Y (k + 1)) := by
  have h_tele : f (t N) (X N) (Y N) - f (t 0) (X 0) (Y 0) =
      ∑ k ∈ Finset.range N, (f (t (k + 1)) (X (k + 1)) (Y (k + 1)) - f (t k) (X k) (Y k)) :=
    (Finset.sum_range_sub (fun n ↦ f (t n) (X n) (Y n)) N).symm
  have h_summand (k : ℕ) :
      f (t (k + 1)) (X (k + 1)) (Y (k + 1)) - f (t k) (X k) (Y k) =
        f_t (t k) (X k) (Y k) * (t (k + 1) - t k) +
        f_x (t k) (X k) (Y k) * (X (k + 1) - X k) +
        f_y (t k) (X k) (Y k) * (Y (k + 1) - Y k) +
        (1 / 2) * (f_xx (t k) (X k) (Y k) * (X (k + 1) - X k) ^ 2) +
        f_xy (t k) (X k) (Y k) * ((X (k + 1) - X k) * (Y (k + 1) - Y k)) +
        (1 / 2) * (f_yy (t k) (X k) (Y k) * (Y (k + 1) - Y k) ^ 2) +
        discreteTaylorRemainder3D f f_t f_x f_y f_xx f_xy f_yy
          (t k) (t (k + 1)) (X k) (X (k + 1)) (Y k) (Y (k + 1)) := by
    unfold discreteTaylorRemainder3D
    ring
  rw [h_tele, Finset.sum_congr rfl fun k _ ↦ h_summand k]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### The remainder under oscillation bounds -/

/-- **The Taylor remainder of `f(t, x, y)` under oscillation bounds.** Suppose `f_t` stays within
`η` of `f_t(t₀, x₀, y₀)` on `[t₀, t₁] × {(x₁, y₁)}`, `f_xx` within `η` of `f_xx(t₀, x₀, y₀)` on
`{t₀} × [x₀, x₁] × {y₁}`, and `f_xy`, `f_yy` within `η` of their values at `(t₀, x₀, y₀)` on
`{(t₀, x₀)} × [y₀, y₁]`. Then the remainder is at most `η |Δt| + 3 η Δx² + 2 η Δy²`.

With `R = P₁ + P₂ + P₃ + P₄ Δx + P₅`: `P₁` the time increment at frozen `(x₁, y₁)` (mean value
inequality); `P₂` the `x`-Taylor remainder of `u ↦ f(t₀, u, y₁)` (at most `2 η Δx²`, as `f_xx`
moves by at most `2 η` from the base point `(t₀, x₀, y₁)`); `P₃` the `y`-Taylor remainder of
`v ↦ f(t₀, x₀, v)` (at most `η Δy²`); `P₄ = f_x(t₀, x₀, y₁) − f_x(t₀, x₀, y₀) − f_xy Δy`
(mean value inequality, at most `η |Δy|`); `P₅ = ½ (f_xx(t₀, x₀, y₁) − f_xx(t₀, x₀, y₀)) Δx²`.
Only the partial derivatives enter, never a chain rule through `(x, y)`. -/
theorem abs_discreteTaylorRemainder3D_le_of_osc
    {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
    (hf_t : ∀ t x y, HasDerivAt (fun s ↦ f s x y) (f_t t x y) t)
    (hf_x : ∀ t x y, HasDerivAt (fun u ↦ f t u y) (f_x t x y) x)
    (hf_y : ∀ t x y, HasDerivAt (fun v ↦ f t x v) (f_y t x y) y)
    (hf_xx : ∀ t x y, HasDerivAt (fun u ↦ f_x t u y) (f_xx t x y) x)
    (hf_xy : ∀ t x y, HasDerivAt (fun v ↦ f_x t x v) (f_xy t x y) y)
    (hf_yy : ∀ t x y, HasDerivAt (fun v ↦ f_y t x v) (f_yy t x y) y)
    {t₀ t₁ x₀ x₁ y₀ y₁ η : ℝ}
    (hηt : ∀ s ∈ uIcc t₀ t₁, |f_t s x₁ y₁ - f_t t₀ x₀ y₀| ≤ η)
    (hηxx : ∀ u ∈ uIcc x₀ x₁, |f_xx t₀ u y₁ - f_xx t₀ x₀ y₀| ≤ η)
    (hηxy : ∀ v ∈ uIcc y₀ y₁, |f_xy t₀ x₀ v - f_xy t₀ x₀ y₀| ≤ η)
    (hηyy : ∀ v ∈ uIcc y₀ y₁, |f_yy t₀ x₀ v - f_yy t₀ x₀ y₀| ≤ η) :
    |discreteTaylorRemainder3D f f_t f_x f_y f_xx f_xy f_yy t₀ t₁ x₀ x₁ y₀ y₁|
      ≤ η * |t₁ - t₀| + 3 * η * (x₁ - x₀) ^ 2 + 2 * η * (y₁ - y₀) ^ 2 := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hηt t₀ left_mem_uIcc)
  -- `P₁`: the time increment at frozen `(x₁, y₁)`
  have hd1 (s : ℝ) : HasDerivAt (fun r ↦ f r x₁ y₁ - f_t t₀ x₀ y₀ * r)
      (f_t s x₁ y₁ - f_t t₀ x₀ y₀) s :=
    ((hf_t s x₁ y₁).sub ((hasDerivAt_id s).const_mul (f_t t₀ x₀ y₀))).congr_deriv (by simp)
  have hP1 : |(f t₁ x₁ y₁ - f_t t₀ x₀ y₀ * t₁) - (f t₀ x₁ y₁ - f_t t₀ x₀ y₀ * t₀)|
      ≤ η * |t₁ - t₀| := by
    have h := (convex_uIcc t₀ t₁).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ ↦ (hd1 s).hasDerivWithinAt) (fun s hs ↦ (Real.norm_eq_abs _).trans_le (hηt s hs))
      left_mem_uIcc right_mem_uIcc
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  -- `P₂`: the `x`-Taylor remainder of the section through `(t₀, ·, y₁)`
  have hxx (u : ℝ) (hu : u ∈ uIcc x₀ x₁) : |f_xx t₀ u y₁ - f_xx t₀ x₀ y₁| ≤ 2 * η := by
    have h1 := abs_le.1 (hηxx u hu)
    have h2 := abs_le.1 (hηxx x₀ left_mem_uIcc)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hP2 := abs_discreteTaylorRemainder_le_of_abs_sub_le (f := fun u ↦ f t₀ u y₁)
    (f' := fun u ↦ f_x t₀ u y₁) (f'' := fun u ↦ f_xx t₀ u y₁) (fun u ↦ hf_x t₀ u y₁)
    (fun u ↦ hf_xx t₀ u y₁) (x := x₀) (y := x₁) (η := 2 * η) hxx
  -- `P₃`: the `y`-Taylor remainder of the section through `(t₀, x₀, ·)`
  have hP3 := abs_discreteTaylorRemainder_le_of_abs_sub_le (f := fun v ↦ f t₀ x₀ v)
    (f' := fun v ↦ f_y t₀ x₀ v) (f'' := fun v ↦ f_yy t₀ x₀ v) (fun v ↦ hf_y t₀ x₀ v)
    (fun v ↦ hf_yy t₀ x₀ v) (x := y₀) (y := y₁) (η := η) hηyy
  -- `P₄`: the mean value correction of `f_x(t₀, x₀, ·)`
  have hd4 (v : ℝ) : HasDerivAt (fun r ↦ f_x t₀ x₀ r - f_xy t₀ x₀ y₀ * r)
      (f_xy t₀ x₀ v - f_xy t₀ x₀ y₀) v :=
    ((hf_xy t₀ x₀ v).sub ((hasDerivAt_id v).const_mul (f_xy t₀ x₀ y₀))).congr_deriv (by simp)
  have hP4 : |(f_x t₀ x₀ y₁ - f_xy t₀ x₀ y₀ * y₁) - (f_x t₀ x₀ y₀ - f_xy t₀ x₀ y₀ * y₀)|
      ≤ η * |y₁ - y₀| := by
    have h := (convex_uIcc y₀ y₁).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v _ ↦ (hd4 v).hasDerivWithinAt) (fun v hv ↦ (Real.norm_eq_abs _).trans_le (hηxy v hv))
      left_mem_uIcc right_mem_uIcc
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hsplit : discreteTaylorRemainder3D f f_t f_x f_y f_xx f_xy f_yy t₀ t₁ x₀ x₁ y₀ y₁
      = ((f t₁ x₁ y₁ - f_t t₀ x₀ y₀ * t₁) - (f t₀ x₁ y₁ - f_t t₀ x₀ y₀ * t₀))
        + discreteTaylorRemainder (fun u ↦ f t₀ u y₁) (fun u ↦ f_x t₀ u y₁)
          (fun u ↦ f_xx t₀ u y₁) x₀ x₁
        + discreteTaylorRemainder (fun v ↦ f t₀ x₀ v) (fun v ↦ f_y t₀ x₀ v)
          (fun v ↦ f_yy t₀ x₀ v) y₀ y₁
        + ((f_x t₀ x₀ y₁ - f_xy t₀ x₀ y₀ * y₁) - (f_x t₀ x₀ y₀ - f_xy t₀ x₀ y₀ * y₀)) * (x₁ - x₀)
        + 1 / 2 * ((f_xx t₀ x₀ y₁ - f_xx t₀ x₀ y₀) * (x₁ - x₀) ^ 2) := by
    unfold discreteTaylorRemainder3D discreteTaylorRemainder
    ring
  have hP4x : |((f_x t₀ x₀ y₁ - f_xy t₀ x₀ y₀ * y₁) - (f_x t₀ x₀ y₀ - f_xy t₀ x₀ y₀ * y₀))
        * (x₁ - x₀)| ≤ η * ((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2) / 2 := by
    have hΔ : |y₁ - y₀| * |x₁ - x₀| ≤ ((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|x₁ - x₀| - |y₁ - y₀|), sq_abs (x₁ - x₀), sq_abs (y₁ - y₀)]
    rw [abs_mul]
    calc _ ≤ (η * |y₁ - y₀|) * |x₁ - x₀| := mul_le_mul_of_nonneg_right hP4 (abs_nonneg _)
      _ = η * (|y₁ - y₀| * |x₁ - x₀|) := mul_assoc _ _ _
      _ ≤ η * (((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2) / 2) := mul_le_mul_of_nonneg_left hΔ hη0
      _ = η * ((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2) / 2 := by ring
  -- `P₅`: the `f_xx` correction
  have hP5 : |1 / 2 * ((f_xx t₀ x₀ y₁ - f_xx t₀ x₀ y₀) * (x₁ - x₀) ^ 2)|
      ≤ 1 / 2 * (η * (x₁ - x₀) ^ 2) := by
    have h := hηxx x₀ left_mem_uIcc
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_nonneg (sq_nonneg (x₁ - x₀))]
    gcongr
  have h5 (a b c d e : ℝ) : |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
    have h1 := abs_add_le (a + b + c + d) e
    have h2 := abs_add_le (a + b + c) d
    have h3 := abs_add_le (a + b) c
    have h4 := abs_add_le a b
    linarith
  rw [hsplit]
  refine (h5 _ _ _ _ _).trans ?_
  have hy2 := mul_nonneg hη0 (sq_nonneg (y₁ - y₀))
  nlinarith [hP1, hP2, hP3, hP4x, hP5, hy2]

/-! ### The remainders vanish along a continuous path -/

private lemma dist_lt_of_triple {a b c a' b' c' δ : ℝ} (ha : |a - a'| < δ) (hb : |b - b'| < δ)
    (hc : |c - c'| < δ) : dist ((a, b, c) : ℝ × ℝ × ℝ) (a', b', c') < δ := by
  simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff]
  exact ⟨ha, hb, hc⟩

/-- **Uniform oscillation bound on a compact set**: a function of three variables, continuous on
`ℝ × ℝ × ℝ`, moves by at most `η` between two points of a compact set `K` whose coordinates are all
within `δ` of each other, for a `δ` depending on `η` and `K` alone. -/
private lemma exists_osc_of_continuous {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ a b c a' b' c' : ℝ, (a, b, c) ∈ K → (a', b', c') ∈ K → |a - a'| < δ →
      |b - b'| < δ → |c - c'| < δ → |g a b c - g a' b' c'| ≤ η := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hg.continuousOn) η hη
  refine ⟨δ, hδ, fun a b c a' b' c' hp hq ha hb hc ↦ ?_⟩
  have h' := h _ hp _ hq (dist_lt_of_triple ha hb hc)
  simpa only [Real.dist_eq] using h'.le

/-- **The remainders of `f(t, x, y)` vanish along a continuous path with bounded squared
increments.** Let `f_t`, `f_xx`, `f_xy`, `f_yy` be jointly continuous, `x`, `y` continuous on
`[0, T]`, and the sums of squared increments of `x` and of `y` along the uniform partitions
`ν i` bounded eventually. The box `[0, T] × [−R, R]²` holding the path is compact, so the four
functions are uniformly continuous there: once the mesh and the increments are small every
remainder is at most `η Δt + 3 η Δx² + 2 η Δy²`
(`abs_discreteTaylorRemainder3D_le_of_osc`), and the sum at most `η (T + 3 Qₓ + 2 Q_y)`. -/
theorem tendsto_sum_discreteTaylorRemainder3D (T : ℝ≥0)
    {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
    (hf_t : ∀ t x y, HasDerivAt (fun s ↦ f s x y) (f_t t x y) t)
    (hf_x : ∀ t x y, HasDerivAt (fun u ↦ f t u y) (f_x t x y) x)
    (hf_y : ∀ t x y, HasDerivAt (fun v ↦ f t x v) (f_y t x y) y)
    (hf_xx : ∀ t x y, HasDerivAt (fun u ↦ f_x t u y) (f_xx t x y) x)
    (hf_xy : ∀ t x y, HasDerivAt (fun v ↦ f_x t x v) (f_xy t x y) y)
    (hf_yy : ∀ t x y, HasDerivAt (fun v ↦ f_y t x v) (f_yy t x y) y)
    (hf_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2)
    (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2)
    (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2)
    {x y : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) {Qx Qy : ℝ}
    (hQx : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 ≤ Qx)
    (hQy : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2 ≤ Qy) :
    Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i),
      discreteTaylorRemainder3D f f_t f_x f_y f_xx f_xy f_yy
        (unifPart T (ν i) k) (unifPart T (ν i) (k + 1))
        (x (unifPart T (ν i) k)) (x (unifPart T (ν i) (k + 1)))
        (y (unifPart T (ν i) k)) (y (unifPart T (ν i) (k + 1)))) atTop (𝓝 0) := by
  obtain ⟨Rx, hRx⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  obtain ⟨Ry, hRy⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  set R : ℝ := max Rx Ry with hRdef
  set K : Set (ℝ × ℝ × ℝ) := Icc 0 (T : ℝ) ×ˢ Icc (-R) R ×ˢ Icc (-R) R with hKdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hS : 0 < (T : ℝ) + 3 * |Qx| + 2 * |Qy| + 1 := by positivity
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / ((T : ℝ) + 3 * |Qx| + 2 * |Qy| + 1) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηdef]
    exact div_pos hε hS
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_osc_of_continuous hf_t_cont hK hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_osc_of_continuous hf_xx_cont hK hη
  obtain ⟨δ₃, hδ₃, h₃⟩ := exists_osc_of_continuous hf_xy_cont hK hη
  obtain ⟨δ₄, hδ₄, h₄⟩ := exists_osc_of_continuous hf_yy_cont hK hη
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min δ₁ δ₂) (min δ₃ δ₄) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄)
  have hδ₁' : δ ≤ δ₁ := by
    rw [hδdef]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := by
    rw [hδdef]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδ₃' : δ ≤ δ₃ := by
    rw [hδdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ₄' : δ ≤ δ₄ := by
    rw [hδdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [hν.eventually (eventually_abs_sub_unifPart_lt T hx hδ),
    hν.eventually (eventually_abs_sub_unifPart_lt T hy hδ),
    hν.eventually ((tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually_lt_const hδ),
    hQx, hQy] with i hoscx hoscy hmesh hQxi hQyi
  have hxb {k : ℕ} (hk : k ≤ ν i) : |x (unifPart T (ν i) k)| ≤ R := by
    have h := hRx _ ⟨zero_le, unifPart_le_T hk⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hyb {k : ℕ} (hk : k ≤ ν i) : |y (unifPart T (ν i) k)| ≤ R := by
    have h := hRy _ ⟨zero_le, unifPart_le_T hk⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  have hmem {k : ℕ} (hk : k ≤ ν i) :
      (((unifPart T (ν i) k : ℝ≥0) : ℝ), x (unifPart T (ν i) k), y (unifPart T (ν i) k)) ∈ K :=
    ⟨⟨(unifPart T (ν i) k).2, NNReal.coe_le_coe.2 (unifPart_le_T hk)⟩,
      abs_le.1 (hxb hk), abs_le.1 (hyb hk)⟩
  have hstep {k : ℕ} (hk : k < ν i) :
      |discreteTaylorRemainder3D f f_t f_x f_y f_xx f_xy f_yy
        (unifPart T (ν i) k) (unifPart T (ν i) (k + 1))
        (x (unifPart T (ν i) k)) (x (unifPart T (ν i) (k + 1)))
        (y (unifPart T (ν i) k)) (y (unifPart T (ν i) (k + 1)))|
        ≤ η * ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)
          + 3 * η * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2
          + 2 * η * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2 := by
    have hle : (unifPart T (ν i) k : ℝ) ≤ unifPart T (ν i) (k + 1) :=
      NNReal.coe_le_coe.2 (unifPart_mono T (ν i) (Nat.le_succ k))
    have hdt : ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k) = (T : ℝ) / (ν i) := by
      rw [unifPart_succ_sub]
    have hpt := hmem hk.le
    have hpt' := hmem (Nat.succ_le_of_lt hk)
    have hzero (z d : ℝ) (hd : 0 < d) : |z - z| < d := by
      rw [sub_self, abs_zero]
      exact hd
    refine (abs_discreteTaylorRemainder3D_le_of_osc hf_t hf_x hf_y hf_xx hf_xy hf_yy (η := η)
      (fun s hs ↦ ?_) (fun u hu ↦ ?_) (fun v hv ↦ ?_) (fun v hv ↦ ?_)).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.2 hle)])
    · rw [uIcc_of_le hle] at hs
      refine h₁ _ _ _ _ _ _ ⟨⟨(unifPart T (ν i) k).2.trans hs.1,
        hs.2.trans (NNReal.coe_le_coe.2 (unifPart_le_T hk))⟩, hpt'.2⟩ hpt ?_
        ((hoscx k hk).trans_le hδ₁') ((hoscy k hk).trans_le hδ₁')
      rw [abs_of_nonneg (sub_nonneg.2 hs.1)]
      linarith [hs.2, hmesh, hdt, hδ₁']
    · exact h₂ _ _ _ _ _ _ ⟨hpt.1, uIcc_subset_Icc hpt.2.1 hpt'.2.1 hu, hpt'.2.2⟩ hpt
        (hzero _ _ hδ₂) (((abs_sub_left_of_mem_uIcc hu).trans_lt (hoscx k hk)).trans_le hδ₂')
        ((hoscy k hk).trans_le hδ₂')
    · exact h₃ _ _ _ _ _ _ ⟨hpt.1, hpt.2.1, uIcc_subset_Icc hpt.2.2 hpt'.2.2 hv⟩ hpt
        (hzero _ _ hδ₃) (hzero _ _ hδ₃)
        (((abs_sub_left_of_mem_uIcc hv).trans_lt (hoscy k hk)).trans_le hδ₃')
    · exact h₄ _ _ _ _ _ _ ⟨hpt.1, hpt.2.1, uIcc_subset_Icc hpt.2.2 hpt'.2.2 hv⟩ hpt
        (hzero _ _ hδ₄) (hzero _ _ hδ₄)
        (((abs_sub_left_of_mem_uIcc hv).trans_lt (hoscy k hk)).trans_le hδ₄')
  have hsum_t : ∑ k ∈ Finset.range (ν i),
      ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k) ≤ T := by
    rw [Finset.sum_range_sub (fun k ↦ (unifPart T (ν i) k : ℝ))]
    have h0 : unifPart T (ν i) 0 = 0 := unifPart_zero T (ν i)
    rw [h0, NNReal.coe_zero, sub_zero]
    exact NNReal.coe_le_coe.2 (unifPart_le_T le_rfl)
  rw [Real.dist_eq, sub_zero]
  have hη0 : 0 ≤ η := hη.le
  calc _ ≤ ∑ k ∈ Finset.range (ν i),
        (η * ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)
          + 3 * η * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2
          + 2 * η * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2) :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k hk ↦ hstep (Finset.mem_range.1 hk))
    _ = η * ∑ k ∈ Finset.range (ν i), ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)
          + 3 * η * ∑ k ∈ Finset.range (ν i),
            (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2
          + 2 * η * ∑ k ∈ Finset.range (ν i),
            (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ η * T + 3 * η * |Qx| + 2 * η * |Qy| :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsum_t hη0)
          (mul_le_mul_of_nonneg_left (hQxi.trans (le_abs_self Qx)) (mul_nonneg (by norm_num) hη0)))
          (mul_le_mul_of_nonneg_left (hQyi.trans (le_abs_self Qy)) (mul_nonneg (by norm_num) hη0))
    _ < ε := by
        have h : η * ((T : ℝ) + 3 * |Qx| + 2 * |Qy| + 1) = ε := by
          rw [hηdef]
          exact div_mul_cancel₀ ε hS.ne'
        linarith

/-- **Itô's formula along one path, for `f(t, x, y)`.** Let `x = cₓ + a + m` and
`y = c_y + a' + m'` be paths continuous on `[0, T]`, and `f` with partials `f_t`, `f_x`, `f_y`,
`f_xx`, `f_xy = ∂_y f_x`, `f_yy`, of which `f_t`, `f_xx`, `f_xy`, `f_yy` are jointly continuous. If
along a sequence of uniform partitions the Riemann sums of `f_t(t, x_t, y_t)` against `dt`, of
`f_x` against `a` and of `f_y` against `a'` converge to `E`, `Dₓ` and `D_y`; the sum of the
martingale and second-order terms

`∑ f_x Δm + ∑ f_y Δm' + ∑ ½ f_xx Δx² + ∑ f_xy Δx Δy + ∑ ½ f_yy Δy²`

converges to `P`; and the squared-increment sums of `x` and `y` stay bounded, then

`f(T, x_T, y_T) − f(0, x₀, y₀) = E + Dₓ + D_y + P`.

The martingale and second-order terms are one hypothesis because they converge in probability
together, along one subsequence, in `ItoFormulaTwoFactor`. -/
theorem ito_formula_3d_of_tendsto (T : ℝ≥0)
    {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
    (hf_t : ∀ t x y, HasDerivAt (fun s ↦ f s x y) (f_t t x y) t)
    (hf_x : ∀ t x y, HasDerivAt (fun u ↦ f t u y) (f_x t x y) x)
    (hf_y : ∀ t x y, HasDerivAt (fun v ↦ f t x v) (f_y t x y) y)
    (hf_xx : ∀ t x y, HasDerivAt (fun u ↦ f_x t u y) (f_xx t x y) x)
    (hf_xy : ∀ t x y, HasDerivAt (fun v ↦ f_x t x v) (f_xy t x y) y)
    (hf_yy : ∀ t x y, HasDerivAt (fun v ↦ f_y t x v) (f_yy t x y) y)
    (hf_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2)
    (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2)
    (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2)
    {x y a a' m m' : ℝ≥0 → ℝ} {cx cy : ℝ} (hxam : ∀ t, x t = cx + a t + m t)
    (hyam : ∀ t, y t = cy + a' t + m' t)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) {E Dx Dy P Qx Qy : ℝ}
    (hE : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_t (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
      * ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)) atTop (𝓝 E))
    (hDx : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
      * (a (unifPart T (ν i) (k + 1)) - a (unifPart T (ν i) k))) atTop (𝓝 Dx))
    (hDy : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_y (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
      * (a' (unifPart T (ν i) (k + 1)) - a' (unifPart T (ν i) k))) atTop (𝓝 Dy))
    (hP : Tendsto (fun i ↦
      ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (m (unifPart T (ν i) (k + 1)) - m (unifPart T (ν i) k))
      + ∑ k ∈ Finset.range (ν i), f_y (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (m' (unifPart T (ν i) (k + 1)) - m' (unifPart T (ν i) k))
      + ∑ k ∈ Finset.range (ν i), 1 / 2 * f_xx (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2
      + ∑ k ∈ Finset.range (ν i), f_xy (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * ((x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k))
          * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)))
      + ∑ k ∈ Finset.range (ν i), 1 / 2 * f_yy (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2) atTop (𝓝 P))
    (hQx : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 ≤ Qx)
    (hQy : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2 ≤ Qy) :
    f T (x T) (y T) - f 0 (x 0) (y 0) = E + Dx + Dy + P := by
  have hlim := (((hE.add hDx).add hDy).add hP).add
    (tendsto_sum_discreteTaylorRemainder3D T hf_t hf_x hf_y hf_xx hf_xy hf_yy hf_t_cont
      hf_xx_cont hf_xy_cont hf_yy_cont hx hy hν hQx hQy)
  rw [add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [hν.eventually (eventually_ne_atTop 0)] with i hi
  have h := discrete_ito_formula_3d (ν i) (fun k ↦ (unifPart T (ν i) k : ℝ))
    (fun k ↦ x (unifPart T (ν i) k)) (fun k ↦ y (unifPart T (ν i) k)) f f_t f_x f_y f_xx f_xy f_yy
  have hT : unifPart T (ν i) (ν i) = T := unifPart_self T hi
  have h0 : unifPart T (ν i) 0 = 0 := unifPart_zero T (ν i)
  simp only [hT, h0, NNReal.coe_zero] at h
  have hsplitx : ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (x (unifPart T (ν i) k))
        (y (unifPart T (ν i) k)) * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k))
      = ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (x (unifPart T (ν i) k))
          (y (unifPart T (ν i) k)) * (a (unifPart T (ν i) (k + 1)) - a (unifPart T (ν i) k))
        + ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (x (unifPart T (ν i) k))
          (y (unifPart T (ν i) k)) * (m (unifPart T (ν i) (k + 1)) - m (unifPart T (ν i) k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← mul_add]
    congr 1
    rw [hxam (unifPart T (ν i) (k + 1)), hxam (unifPart T (ν i) k)]
    ring
  have hsplity : ∑ k ∈ Finset.range (ν i), f_y (unifPart T (ν i) k) (x (unifPart T (ν i) k))
        (y (unifPart T (ν i) k)) * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k))
      = ∑ k ∈ Finset.range (ν i), f_y (unifPart T (ν i) k) (x (unifPart T (ν i) k))
          (y (unifPart T (ν i) k)) * (a' (unifPart T (ν i) (k + 1)) - a' (unifPart T (ν i) k))
        + ∑ k ∈ Finset.range (ν i), f_y (unifPart T (ν i) k) (x (unifPart T (ν i) k))
          (y (unifPart T (ν i) k)) * (m' (unifPart T (ν i) (k + 1)) - m' (unifPart T (ν i) k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← mul_add]
    congr 1
    rw [hyam (unifPart T (ν i) (k + 1)), hyam (unifPart T (ν i) k)]
    ring
  have hhalfxx : ∑ k ∈ Finset.range (ν i), 1 / 2 * f_xx (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2
      = 1 / 2 * ∑ k ∈ Finset.range (ν i), f_xx (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hhalfyy : ∑ k ∈ Finset.range (ν i), 1 / 2 * f_yy (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2
      = 1 / 2 * ∑ k ∈ Finset.range (ν i), f_yy (unifPart T (ν i) k)
        (x (unifPart T (ν i) k)) (y (unifPart T (ν i) k))
        * (y (unifPart T (ν i) (k + 1)) - y (unifPart T (ν i) k)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h, hsplitx, hsplity, hhalfxx, hhalfyy]
  ring

end MathFin
