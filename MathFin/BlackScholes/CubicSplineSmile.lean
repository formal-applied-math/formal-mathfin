/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathFin.BlackScholes.SVI.Reduction

/-! # The natural cubic spline over pillars: the moment system and its unique solution

A natural cubic spline interpolating values `y 0, …, y n` at strictly increasing pillars
`x 0 < ⋯ < x n` (e.g. an FX/equity vol smile sampled at pillar deltas) reduces, after
imposing the natural boundary conditions `M 0 = M n = 0`, to a linear system in the
unknown interior second derivatives (*moments*) `M 1, …, M (n-1)`. The system formalized
here is the normalized moment form of J. Stoer & R. Bulirsch, *Introduction to Numerical
Analysis*, 3rd ed. (Springer, 2002), §2.4.2: dividing each row of the standard natural-
spline system (stated on the same unknowns `M i`, with diagonal `2(h (i-1) + h i)`) by
`h (i-1) + h i` turns that diagonal into a constant `2` with off-diagonal weights
`μ i, λ i ≥ 0` summing to `1`. Existence and uniqueness of the natural cubic spline is
R. L. Burden & J. D. Faires, *Numerical Analysis*, 9th ed. (2011), Theorem 3.11; the
strict-diagonal-dominance step formalized here is the same nonsingularity argument that
theorem's proof uses, run on the normalized system.
Distinct from the parametric SVI smile already in the repository
(`MathFin.BlackScholes.SVI`): this is a pillar-interpolation scheme, not a functional form.

## Result

* `momentMatrix_invertible` — the moment system's coefficient matrix is a unit, because it
  is strictly row diagonally dominant: Mathlib's `det_ne_zero_of_sum_row_lt_diag`
  (a corollary of Gershgorin's circle theorem) applied to the fact that every row has
  diagonal entry `2` and off-diagonal entries `μ, λ ≥ 0` with `μ + λ = 1 < 2`.
* `exists_unique_moments` — consequently the moment system has exactly one solution
  (`Matrix.mulVec_injective_iff_isUnit` for uniqueness, `A⁻¹ *ᵥ d` for existence): this is
  the textbook's "the matrix is nonsingular" step of natural-cubic-spline uniqueness.
* `interpSpline` — the standard piecewise-cubic formula built from the pillars, the data
  and a candidate moment sequence, and `interpSpline_left_eq`, `interpSpline_right_eq` —
  it matches the pillar values `y i`, `y (i+1)` exactly at both ends of each piece
  `[x i, x (i+1)]`, for *any* moment sequence (the interpolation property does not depend
  on which system the moments solve).
* `svi_pillar_interpSpline_eq`, `svi_pillar_moments_unique` — the connection to the
  parametric SVI smile already in the repository: if the pillar values are samples of an
  SVI slice's total variance at the pillar log-strikes, the spline reproduces that sampled
  value exactly at both pillars of each piece, and the natural-spline moment system for
  those SVI-sampled pillars has exactly one solution.

## Scope

This module formalizes the linear-algebra core of natural-cubic-spline uniqueness (the
diagonally-dominant tridiagonal system) and the exact-interpolation identity of the
piecewise-cubic formula at the pillars. It does not construct a single global function
glued across all pieces, and does not prove the global `C²` matching of one-sided
derivatives at interior knots — the first-derivative-continuity equations are exactly
what the moment system encodes, but deriving "the glued function is `C²`" as a two-sided
`HasDerivAt` statement needs a one-sided-derivative-patching argument this module leaves
to future work.
-/

@[expose] public section

namespace MathFin
namespace CubicSpline

/-- The gap `h i = x (i+1) - x i` between consecutive pillars. -/
noncomputable def gap (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

/-- The left tridiagonal weight `μ i = h (i-1) / (h (i-1) + h i)` of the natural-cubic-spline
moment system, at interior pillar index `i`. -/
noncomputable def mu (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  gap x (i - 1) / (gap x (i - 1) + gap x i)

/-- The right tridiagonal weight `λ i = h i / (h (i-1) + h i) = 1 - μ i`. -/
noncomputable def lam (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  gap x i / (gap x (i - 1) + gap x i)

/-- The moment system's right-hand side at interior pillar index `i`:
`d i = 6/(h (i-1) + h i) · ((y (i+1) - y i)/h i - (y i - y (i-1))/h (i-1))`. -/
noncomputable def rhs (x y : ℕ → ℝ) (i : ℕ) : ℝ :=
  6 / (gap x (i - 1) + gap x i) *
    ((y (i + 1) - y i) / gap x i - (y i - y (i - 1)) / gap x (i - 1))

theorem gap_pos {n : ℕ} (x : ℕ → ℝ) (hgap : ∀ i < n, x i < x (i + 1)) {i : ℕ} (hi : i < n) :
    0 < gap x i :=
  sub_pos.mpr (hgap i hi)

theorem mu_nonneg (x : ℕ → ℝ) {i : ℕ} (h1 : 0 < gap x (i - 1)) (h2 : 0 < gap x i) :
    0 ≤ mu x i :=
  div_nonneg h1.le (by positivity)

theorem lam_nonneg (x : ℕ → ℝ) {i : ℕ} (h1 : 0 < gap x (i - 1)) (h2 : 0 < gap x i) :
    0 ≤ lam x i :=
  div_nonneg h2.le (by positivity)

theorem mu_add_lam_eq_one (x : ℕ → ℝ) {i : ℕ} (h1 : 0 < gap x (i - 1)) (h2 : 0 < gap x i) :
    mu x i + lam x i = 1 := by
  unfold mu lam
  have hne : gap x (i - 1) + gap x i ≠ 0 := by positivity
  field_simp

/-- The tridiagonal moment-system matrix for the natural cubic spline on `n + 1` pillars
`x 0 < ⋯ < x n`, acting on the interior moments `M 1, …, M (n-1)` after the natural
boundary conditions `M 0 = M n = 0` have been substituted in. Row/column `j : Fin (n - 1)`
corresponds to pillar index `j.val + 1`. -/
noncomputable def momentMatrix (x : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  Matrix.of fun j k : Fin (n - 1) =>
    if k = j then (2 : ℝ)
    else if (k : ℕ) + 1 = (j : ℕ) then mu x ((j : ℕ) + 1)
    else if (j : ℕ) + 1 = (k : ℕ) then lam x ((j : ℕ) + 1)
    else 0

theorem momentMatrix_apply_self (x : ℕ → ℝ) (n : ℕ) (j : Fin (n - 1)) :
    momentMatrix x n j j = 2 := by
  simp [momentMatrix]

/-- A finite sum of an indicator function supported on at most one point, as picked out by
an injective-on-its-support predicate `P`, is bounded by the indicator's value. -/
private theorem sum_indicator_le {m : ℕ} (P : Fin m → Prop) [DecidablePred P]
    (hP : ∀ a b, P a → P b → a = b) {c : ℝ} (hc : 0 ≤ c) :
    ∑ k : Fin m, (if P k then c else 0) ≤ c := by
  classical
  have hcard : (Finset.univ.filter P).card ≤ 1 :=
    Finset.card_le_one.mpr (by
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hP a b ha hb)
  calc ∑ k : Fin m, (if P k then c else (0 : ℝ))
      = ∑ _k ∈ Finset.univ.filter P, c := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    _ = (Finset.univ.filter P).card • c := Finset.sum_const c
    _ = ((Finset.univ.filter P).card : ℝ) * c := by rw [nsmul_eq_mul]
    _ ≤ (1 : ℝ) * c := by
        gcongr
        exact_mod_cast hcard
    _ = c := one_mul c

/-- **Strict row diagonal dominance of the moment-system matrix.** Every row has diagonal
entry `2` and off-diagonal entries `μ, λ ≥ 0` summing to at most `μ + λ = 1 < 2`, since a row
has at most two nonzero off-diagonal entries (the left and right tridiagonal neighbours). -/
theorem momentMatrix_dominant {n : ℕ} (x : ℕ → ℝ) (hn : 2 ≤ n)
    (hgap : ∀ i < n, x i < x (i + 1)) (j : Fin (n - 1)) :
    ∑ k ∈ Finset.univ.erase j, ‖momentMatrix x n j k‖ < ‖momentMatrix x n j j‖ := by
  classical
  have hjn : (j : ℕ) < n := by omega
  have hjn' : (j : ℕ) + 1 < n := by omega
  have h1 : 0 < gap x (j : ℕ) := gap_pos x hgap hjn
  have h2 : 0 < gap x ((j : ℕ) + 1) := gap_pos x hgap hjn'
  have h1' : 0 < gap x (((j : ℕ) + 1) - 1) := by
    have heq : ((j : ℕ) + 1) - 1 = (j : ℕ) := by omega
    rwa [heq]
  have hmunn : 0 ≤ mu x ((j : ℕ) + 1) := mu_nonneg x h1' h2
  have hlamnn : 0 ≤ lam x ((j : ℕ) + 1) := lam_nonneg x h1' h2
  have hsum1 : mu x ((j : ℕ) + 1) + lam x ((j : ℕ) + 1) = 1 := mu_add_lam_eq_one x h1' h2
  have hdiag : momentMatrix x n j j = 2 := momentMatrix_apply_self x n j
  rw [hdiag, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hpt : ∀ k ∈ Finset.univ.erase j, ‖momentMatrix x n j k‖ ≤
      (if (k : ℕ) + 1 = (j : ℕ) then mu x ((j : ℕ) + 1) else 0) +
        (if (j : ℕ) + 1 = (k : ℕ) then lam x ((j : ℕ) + 1) else 0) := by
    intro k hk
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    by_cases ha : (k : ℕ) + 1 = (j : ℕ)
    · have hb : ¬ (j : ℕ) + 1 = (k : ℕ) := by omega
      simp only [momentMatrix, Matrix.of_apply, ite_eq_right hkj, ite_eq_left ha, ite_eq_right hb]
      rw [Real.norm_eq_abs, abs_of_nonneg hmunn]
      simp
    · by_cases hb : (j : ℕ) + 1 = (k : ℕ)
      · simp only [momentMatrix, Matrix.of_apply, ite_eq_right hkj, ite_eq_right ha, ite_eq_left hb]
        rw [Real.norm_eq_abs, abs_of_nonneg hlamnn]
        simp
      · simp only [momentMatrix, Matrix.of_apply, ite_eq_right hkj, ite_eq_right ha,
          ite_eq_right hb]
        simp
  calc ∑ k ∈ Finset.univ.erase j, ‖momentMatrix x n j k‖
      ≤ ∑ k ∈ Finset.univ.erase j,
          ((if (k : ℕ) + 1 = (j : ℕ) then mu x ((j : ℕ) + 1) else 0) +
            (if (j : ℕ) + 1 = (k : ℕ) then lam x ((j : ℕ) + 1) else 0)) :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ k : Fin (n - 1),
          ((if (k : ℕ) + 1 = (j : ℕ) then mu x ((j : ℕ) + 1) else 0) +
            (if (j : ℕ) + 1 = (k : ℕ) then lam x ((j : ℕ) + 1) else 0)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro k _ _
        positivity
    _ = (∑ k : Fin (n - 1), (if (k : ℕ) + 1 = (j : ℕ) then mu x ((j : ℕ) + 1) else 0)) +
          ∑ k : Fin (n - 1), (if (j : ℕ) + 1 = (k : ℕ) then lam x ((j : ℕ) + 1) else 0) :=
        Finset.sum_add_distrib
    _ ≤ mu x ((j : ℕ) + 1) + lam x ((j : ℕ) + 1) := by
        gcongr
        · exact sum_indicator_le (fun k : Fin (n - 1) => (k : ℕ) + 1 = (j : ℕ))
            (fun a b ha hb => Fin.ext (by omega)) hmunn
        · exact sum_indicator_le (fun k : Fin (n - 1) => (j : ℕ) + 1 = (k : ℕ))
            (fun a b ha hb => Fin.ext (by omega)) hlamnn
    _ = 1 := hsum1
    _ < 2 := by norm_num

/-- **Uniqueness of the natural cubic spline's interior moments** (the nonsingularity step
behind Burden & Faires, *Numerical Analysis*, 9th ed. (2011), Theorem 3.11, run on the
normalized moment system of Stoer & Bulirsch, *Introduction to Numerical Analysis*, 3rd
ed. (2002), §2.4.2): the moment system's coefficient matrix is a unit. A strictly row
diagonally dominant real matrix has nonzero determinant (`det_ne_zero_of_sum_row_lt_diag`,
Mathlib's `Gershgorin.lean`), hence is a unit (`Matrix.isUnit_iff_isUnit_det`). -/
theorem momentMatrix_invertible {n : ℕ} (x : ℕ → ℝ) (hn : 2 ≤ n)
    (hgap : ∀ i < n, x i < x (i + 1)) :
    IsUnit (momentMatrix x n) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact det_ne_zero_of_sum_row_lt_diag (momentMatrix_dominant x hn hgap)

/-- **Existence and uniqueness of the natural cubic spline's interior moments.** The linear
system `momentMatrix x n *ᵥ M = d` — the natural-boundary moment system, with `d` the
right-hand side `rhs` at each interior pillar — has exactly one solution `M`. -/
theorem exists_unique_moments {n : ℕ} (x y : ℕ → ℝ) (hn : 2 ≤ n)
    (hgap : ∀ i < n, x i < x (i + 1)) :
    ∃! M : Fin (n - 1) → ℝ,
      (momentMatrix x n).mulVec M = fun j : Fin (n - 1) => rhs x y ((j : ℕ) + 1) := by
  have hU : IsUnit (momentMatrix x n) := momentMatrix_invertible x hn hgap
  have hdet : IsUnit (momentMatrix x n).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  refine ⟨(momentMatrix x n)⁻¹.mulVec (fun j : Fin (n - 1) => rhs x y ((j : ℕ) + 1)), ?_, ?_⟩
  · dsimp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · intro M' hM'
    apply Matrix.mulVec_injective_iff_isUnit.mpr hU
    rw [hM', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-! ## Exact interpolation at the pillars -/

/-- The standard piecewise-cubic formula on the piece `[x i, x (i+1)]`, built from the gap,
the two pillar values and the two candidate moments `Mi = M i`, `Mi1 = M (i+1)`: the moment
form of the natural cubic spline piece, equivalent to the one in J. Stoer & R. Bulirsch,
*Introduction to Numerical Analysis*, 3rd ed. (2002), §2.4.2 (regrouped here into two
linear-in-`t` terms rather than kept in their own `A j, B j` grouping). Defined for any
moment sequence `M`, independent of which linear system (if any) it solves. -/
noncomputable def interpSpline (x y : ℕ → ℝ) (M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  M i * (x (i + 1) - t) ^ 3 / (6 * gap x i) + M (i + 1) * (t - x i) ^ 3 / (6 * gap x i) +
    (y i / gap x i - M i * gap x i / 6) * (x (i + 1) - t) +
    (y (i + 1) / gap x i - M (i + 1) * gap x i / 6) * (t - x i)

/-- The piecewise cubic matches the left pillar value exactly:
`interpSpline x y M i (x i) = y i`. -/
theorem interpSpline_left_eq (x y M : ℕ → ℝ) {i : ℕ} (hgap : gap x i ≠ 0) :
    interpSpline x y M i (x i) = y i := by
  unfold interpSpline gap at *
  have hgap' : x (i + 1) - x i ≠ 0 := hgap
  field_simp
  ring

/-- The piecewise cubic matches the right pillar value exactly:
`interpSpline x y M i (x (i+1)) = y (i+1)`. -/
theorem interpSpline_right_eq (x y M : ℕ → ℝ) {i : ℕ} (hgap : gap x i ≠ 0) :
    interpSpline x y M i (x (i + 1)) = y (i + 1) := by
  unfold interpSpline gap at *
  have hgap' : x (i + 1) - x i ≠ 0 := hgap
  field_simp
  ring

/-! ## Connection to the SVI smile -/

/-- **Pillar interpolation of an SVI smile.** If a smile's pillar values are samples of a
raw-SVI slice's total variance `MathFin.SVI.variance p` at the pillar log-strikes `x i`, the
natural-cubic-spline piecewise formula reproduces that sampled total variance exactly at
both pillars of the piece `[x i, x (i+1)]`, for any candidate moment sequence `M`. This is
the pillar-interpolation reading of SVI's parametric smile: distinct from, and does not
derive, the parametric curve `MathFin.SVI.variance` itself between pillars. -/
theorem svi_pillar_interpSpline_eq (p : SVI.Params) (x M : ℕ → ℝ) {i : ℕ}
    (hgap : gap x i ≠ 0) :
    interpSpline x (fun j => SVI.variance p (x j)) M i (x i) = SVI.variance p (x i) ∧
      interpSpline x (fun j => SVI.variance p (x j)) M i (x (i + 1)) =
        SVI.variance p (x (i + 1)) :=
  ⟨interpSpline_left_eq x _ M hgap, interpSpline_right_eq x _ M hgap⟩

/-- **Unique natural-spline moments for an SVI-sampled smile.** Specializing
`exists_unique_moments` to pillar values `y j = MathFin.SVI.variance p (x j)` sampled from a
raw-SVI slice: the natural cubic spline interpolating an SVI smile's own pillar samples has
exactly one moment vector, for any strictly increasing pillars `x` and any SVI parameters
`p`. -/
theorem svi_pillar_moments_unique {n : ℕ} (p : SVI.Params) (x : ℕ → ℝ) (hn : 2 ≤ n)
    (hgap : ∀ i < n, x i < x (i + 1)) :
    ∃! M : Fin (n - 1) → ℝ,
      (momentMatrix x n).mulVec M =
        fun j : Fin (n - 1) => rhs x (fun k => SVI.variance p (x k)) ((j : ℕ) + 1) :=
  exists_unique_moments x (fun k => SVI.variance p (x k)) hn hgap

end CubicSpline
end MathFin
