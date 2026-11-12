/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathFin.Models.ModelFree.SVI.Reduction

/-!
# The natural cubic spline over pillars: the moment system and its unique solution

A natural cubic spline interpolating values `y 0, …, y n` at strictly increasing pillars
`x 0 < ⋯ < x n` (e.g. an FX/equity vol smile sampled at pillar deltas) reduces, by the
textbook derivation (matching first derivatives at the interior pillars and imposing the
natural boundary conditions `M 0 = M n = 0`), to a linear system in the unknown interior
second derivatives (*moments*) `M 1, …, M (n-1)`. The system is defined here as the textbook
states it, and then proved to be that condition: it holds exactly when adjacent cubic pieces
have the same slope at the shared pillar (`momentMatrix_mulVec_eq_iff`). It is the normalized
moment form of
J. Stoer & R. Bulirsch, *Introduction to Numerical Analysis*, 3rd ed. (Springer, 2002),
§2.4.2: dividing each row of the standard natural-
spline system (stated on the same unknowns `M i`, with diagonal `2(h (i-1) + h i)`) by
`h (i-1) + h i` turns that diagonal into a constant `2` with off-diagonal weights
`μ i, λ i ≥ 0` summing to `1`. Existence and uniqueness of the natural cubic spline is
R. L. Burden & J. D. Faires, *Numerical Analysis*, 9th ed. (2011), Theorem 3.11; the
strict-diagonal-dominance step formalized here is the same nonsingularity argument that
theorem's proof uses, run on the normalized system.
Distinct from the parametric SVI smile already in the repository
(`MathFin.SVI`): this is a pillar-interpolation scheme, not a functional form.

## Main definitions

* `gap`, `mu`, `lam` — the pillar gaps and the two tridiagonal weights of the normalized
  moment system (`μ i + λ i = 1` at every interior pillar).
* `rhs` — the moment system's right-hand side at an interior pillar.
* `momentMatrix` — the normalized moment-system matrix: constant diagonal `2`, off-diagonal
  entries `μ`, `λ` (the row reads `2 M j + μ j · M (j-1) + λ j · M (j+1)`).
* `interpSpline` — the standard piecewise-cubic formula built from the pillars, the data
  and a candidate moment sequence.

## Main results

* `momentMatrix_invertible` — the moment system's coefficient matrix is a unit, because it
  is strictly row diagonally dominant: Mathlib's `det_ne_zero_of_sum_row_lt_diag`
  (a corollary of Gershgorin's circle theorem) applied to the fact that every row has
  diagonal entry `2` and off-diagonal entries `μ, λ ≥ 0` with `μ + λ = 1 < 2`.
* `exists_unique_moments` — consequently the moment system has exactly one solution
  (`Matrix.mulVec_injective_iff_isUnit` for uniqueness, `A⁻¹ *ᵥ d` for existence): this is
  the textbook's "the matrix is nonsingular" step of natural-cubic-spline uniqueness.
* `hasDerivAt_interpSpline`, `hasDerivAt_deriv_interpSpline`, `deriv_interpSpline_left`,
  `deriv_interpSpline_right`, `deriv_deriv_interpSpline_left`, `deriv_deriv_interpSpline_right`
  — the slopes of a piece at its two ends, and its second derivative `M i`, `M (i+1)` there.
* `deriv_interpSpline_match_iff`, `momentMatrix_mulVec_eq_iff` — the moment equation at a pillar
  is exactly the slope matching of the two adjacent pieces, so the moment system (with natural
  ends) is exactly the `C¹` gluing condition.
* `exists_unique_natural_spline_moments` — **the natural cubic spline exists and is unique**:
  one moment sequence with `M 0 = M n = 0` makes adjacent pieces match in slope at every interior
  pillar; the pieces interpolate the data and agree in second derivative `M i` at each pillar,
  so the glued function is `C²` at the pillars with zero curvature at both ends.
* `interpSpline_left_eq`, `interpSpline_right_eq` — the piecewise cubic `interpSpline`
  matches the pillar values `y i`, `y (i+1)` exactly at both ends of each piece
  `[x i, x (i+1)]`, for *any* moment sequence (the interpolation property does not depend
  on which system the moments solve).
* `svi_pillar_interpSpline_eq`, `svi_pillar_moments_unique` — the connection to the
  parametric SVI smile already in the repository: if the pillar values are samples of an
  SVI slice's total variance at the pillar log-strikes, the spline reproduces that sampled
  value exactly at both pillars of each piece, and the natural-spline moment system for
  those SVI-sampled pillars has exactly one solution.

## Scope

The glued function is not a single Lean object: the spline is the family of pieces `interpSpline`
with the moments of `exists_unique_natural_spline_moments`, and its `C¹` and `C²` matching is the
statement that adjacent pieces agree in slope (`deriv_interpSpline_match_iff`) and in second
derivative at the shared pillar, not a `ContDiff` statement about one function on `[x 0, x n]`.
The derivation of the moment system from the spline conditions is replaced by the equivalence
`momentMatrix_mulVec_eq_iff`. The pillar values are arbitrary: nothing here says a spline through
a vol smile or call price smile is free of arbitrage.

## References

* [J. Stoer and R. Bulirsch, *Introduction to Numerical Analysis*][StoerBulirsch2002], §2.4.2
* [R. L. Burden and J. D. Faires, *Numerical Analysis*][BurdenFaires2011], Theorem 3.11

## Tags

natural cubic spline, moment system, strict diagonal dominance, pillar interpolation,
vol smile, MSC 91G60, JEL G13
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
theorem sum_indicator_le {m : ℕ} (P : Fin m → Prop) [DecidablePred P]
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

/-! ## Derivatives: the moment system is the `C¹` gluing condition -/

/-- The first derivative of the piecewise cubic on `[x i, x (i+1)]`, in moment form. -/
theorem hasDerivAt_interpSpline (x y M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (interpSpline x y M i)
      (-(M i * (x (i + 1) - t) ^ 2 / (2 * gap x i)) + M (i + 1) * (t - x i) ^ 2 / (2 * gap x i)
        - (y i / gap x i - M i * gap x i / 6) + (y (i + 1) / gap x i - M (i + 1) * gap x i / 6))
      t := by
  have h1 : HasDerivAt (fun u : ℝ ↦ x (i + 1) - u) (-1) t :=
    ((hasDerivAt_id' t).neg).const_add (x (i + 1))
  have h2 : HasDerivAt (fun u : ℝ ↦ u - x i) 1 t := (hasDerivAt_id' t).sub_const (x i)
  have h3 := (h1.mul (h1.mul h1)).const_mul (M i)
  have h4 := (h2.mul (h2.mul h2)).const_mul (M (i + 1))
  have h := (((h3.div_const (6 * gap x i)).add (h4.div_const (6 * gap x i))).add
    (h1.const_mul (y i / gap x i - M i * gap x i / 6))).add
    (h2.const_mul (y (i + 1) / gap x i - M (i + 1) * gap x i / 6))
  convert h using 1
  · funext u
    simp only [interpSpline, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [Pi.mul_apply]
    ring

/-- The second derivative of the piecewise cubic on `[x i, x (i+1)]`: linear interpolation of the
two moments. -/
theorem hasDerivAt_deriv_interpSpline (x y M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (deriv (interpSpline x y M i))
      (M i * (x (i + 1) - t) / gap x i + M (i + 1) * (t - x i) / gap x i) t := by
  have hfun : deriv (interpSpline x y M i) = fun t ↦
      -(M i * (x (i + 1) - t) ^ 2 / (2 * gap x i)) + M (i + 1) * (t - x i) ^ 2 / (2 * gap x i)
        - (y i / gap x i - M i * gap x i / 6) + (y (i + 1) / gap x i - M (i + 1) * gap x i / 6) :=
    funext fun t ↦ (hasDerivAt_interpSpline x y M i t).deriv
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ ↦ x (i + 1) - u) (-1) t :=
    ((hasDerivAt_id' t).neg).const_add (x (i + 1))
  have h2 : HasDerivAt (fun u : ℝ ↦ u - x i) 1 t := (hasDerivAt_id' t).sub_const (x i)
  have h3 := (h1.mul h1).const_mul (M i)
  have h4 := (h2.mul h2).const_mul (M (i + 1))
  have h := (((h3.div_const (2 * gap x i)).neg.add (h4.div_const (2 * gap x i))).sub_const
    (y i / gap x i - M i * gap x i / 6)).add_const
    (y (i + 1) / gap x i - M (i + 1) * gap x i / 6)
  convert h using 1
  · funext u
    simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  · ring

/-- The slope of the piece `[x i, x (i+1)]` at its right end. -/
theorem deriv_interpSpline_right (x y M : ℕ → ℝ) {i : ℕ} (hgap : gap x i ≠ 0) :
    deriv (interpSpline x y M i) (x (i + 1)) =
      (y (i + 1) - y i) / gap x i + gap x i * M i / 6 + gap x i * M (i + 1) / 3 := by
  rw [(hasDerivAt_interpSpline x y M i _).deriv]
  unfold gap at *
  field_simp
  ring

/-- The slope of the piece `[x i, x (i+1)]` at its left end. -/
theorem deriv_interpSpline_left (x y M : ℕ → ℝ) {i : ℕ} (hgap : gap x i ≠ 0) :
    deriv (interpSpline x y M i) (x i) =
      (y (i + 1) - y i) / gap x i - gap x i * M i / 3 - gap x i * M (i + 1) / 6 := by
  rw [(hasDerivAt_interpSpline x y M i _).deriv]
  unfold gap at *
  field_simp
  ring

/-- The curvature of the piece `[x i, x (i+1)]` at its left end is the moment `M i`. -/
theorem deriv_deriv_interpSpline_left (x y M : ℕ → ℝ) {i : ℕ} (hgap : gap x i ≠ 0) :
    deriv (deriv (interpSpline x y M i)) (x i) = M i := by
  rw [(hasDerivAt_deriv_interpSpline x y M i _).deriv]
  unfold gap at *
  field_simp
  ring

/-- The curvature of the piece `[x i, x (i+1)]` at its right end is the moment `M (i+1)`. -/
theorem deriv_deriv_interpSpline_right (x y M : ℕ → ℝ) {i : ℕ} (hgap : gap x i ≠ 0) :
    deriv (deriv (interpSpline x y M i)) (x (i + 1)) = M (i + 1) := by
  rw [(hasDerivAt_deriv_interpSpline x y M i _).deriv]
  unfold gap at *
  field_simp
  ring

/-- **The moment equation at an interior pillar is the first-derivative matching of the two
adjacent pieces.** For consecutive gaps `h i, h (i+1) ≠ 0` with positive sum, the pieces on
`[x i, x (i+1)]` and `[x (i+1), x (i+2)]` have the same slope at `x (i+1)` exactly when row `i`
of the moment system holds: `μ M i + 2 M (i+1) + λ M (i+2) = rhs`. -/
theorem deriv_interpSpline_match_iff (x y M : ℕ → ℝ) {i : ℕ} (h0 : 0 < gap x i)
    (h1 : 0 < gap x (i + 1)) :
    deriv (interpSpline x y M i) (x (i + 1)) = deriv (interpSpline x y M (i + 1)) (x (i + 1)) ↔
      mu x (i + 1) * M i + 2 * M (i + 1) + lam x (i + 1) * M (i + 2) = rhs x y (i + 1) := by
  rw [deriv_interpSpline_right x y M h0.ne', deriv_interpSpline_left x y M h1.ne']
  have hs : gap x i + gap x (i + 1) ≠ 0 := by positivity
  have key : mu x (i + 1) * M i + 2 * M (i + 1) + lam x (i + 1) * M (i + 2) - rhs x y (i + 1) =
      6 / (gap x i + gap x (i + 1)) *
        (((y (i + 1) - y i) / gap x i + gap x i * M i / 6 + gap x i * M (i + 1) / 3) -
          ((y (i + 1 + 1) - y (i + 1)) / gap x (i + 1) - gap x (i + 1) * M (i + 1) / 3 -
            gap x (i + 1) * M (i + 1 + 1) / 6)) := by
    simp only [mu, lam, rhs, Nat.add_sub_cancel]
    field_simp
    ring
  rw [← sub_eq_zero, ← sub_eq_zero (a := mu x (i + 1) * M i + 2 * M (i + 1) +
    lam x (i + 1) * M (i + 2)), key, mul_eq_zero]
  simp [hs]

/-- A finite sum of an indicator on `Fin m` that fires at the single index `a`. -/
theorem sum_fin_ite_eq {m : ℕ} (a : ℕ) (c : ℝ) :
    ∑ k : Fin m, (if (k : ℕ) = a then c else 0) = if a < m then c else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a, h⟩ : Fin m)]
    · simp
    · intro k _ hk
      exact ite_eq_right fun hka ↦ hk (Fin.ext hka)
    · simp
  · exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right fun hk ↦ h (by have := k.2; omega)

/-- **A row of the moment system.** Applied to the interior moments `M 1, …, M (n-1)` of a
sequence with natural ends `M 0 = M n = 0`, row `j` of `momentMatrix` reads
`μ M j + 2 M (j+1) + λ M (j+2)`: the missing neighbours at the two ends are the zero moments. -/
theorem momentMatrix_mulVec_apply {n : ℕ} (x M : ℕ → ℝ) (hM0 : M 0 = 0) (hMn : M n = 0)
    (j : Fin (n - 1)) :
    (momentMatrix x n).mulVec (fun k : Fin (n - 1) ↦ M ((k : ℕ) + 1)) j =
      mu x ((j : ℕ) + 1) * M j + 2 * M ((j : ℕ) + 1) +
        lam x ((j : ℕ) + 1) * M ((j : ℕ) + 2) := by
  have hj := j.2
  have hpt : ∀ k : Fin (n - 1), momentMatrix x n j k * M ((k : ℕ) + 1) =
      (if (k : ℕ) = j then 2 * M ((j : ℕ) + 1) else 0) +
        (if (k : ℕ) + 1 = j then mu x ((j : ℕ) + 1) * M j else 0) +
        (if (k : ℕ) = j + 1 then lam x ((j : ℕ) + 1) * M ((j : ℕ) + 2) else 0) := by
    intro k
    simp only [momentMatrix, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> try (exfalso; omega)
    all_goals (simp only [add_zero, zero_add, zero_mul]; try (congr 1; try (congr 1; try omega)))
  have s1 : ∑ k : Fin (n - 1), (if (k : ℕ) = j then 2 * M ((j : ℕ) + 1) else 0) =
      2 * M ((j : ℕ) + 1) := by
    rw [sum_fin_ite_eq]; exact ite_eq_left hj
  have s2 : ∑ k : Fin (n - 1),
      (if (k : ℕ) + 1 = j then mu x ((j : ℕ) + 1) * M j else 0) =
        mu x ((j : ℕ) + 1) * M j := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · have h : M (j : ℕ) = 0 := by rw [h0, hM0]
      rw [h, mul_zero]
      exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right (by omega)
    · obtain ⟨j', hj'⟩ : ∃ j', (j : ℕ) = j' + 1 := ⟨j - 1, by omega⟩
      simp_rw [hj', Nat.add_right_cancel_iff]
      rw [sum_fin_ite_eq]
      exact ite_eq_left (by omega)
  have s3 : ∑ k : Fin (n - 1),
      (if (k : ℕ) = j + 1 then lam x ((j : ℕ) + 1) * M ((j : ℕ) + 2) else 0) =
        lam x ((j : ℕ) + 1) * M ((j : ℕ) + 2) := by
    rw [sum_fin_ite_eq]
    by_cases hlt : (j : ℕ) + 1 < n - 1
    · exact ite_eq_left hlt
    · rw [ite_eq_right hlt, show (j : ℕ) + 2 = n by omega, hMn, mul_zero]
  simp only [Matrix.mulVec, dotProduct, hpt, Finset.sum_add_distrib, s1, s2, s3]
  ring

/-- **The moment system is exactly the `C¹` gluing condition.** For moments with natural ends
`M 0 = M n = 0`, the interior moments solve the moment system if and only if every pair of
adjacent pieces `interpSpline x y M i`, `interpSpline x y M (i+1)` has the same slope at the
shared pillar `x (i+1)`. -/
theorem momentMatrix_mulVec_eq_iff {n : ℕ} (x y M : ℕ → ℝ)
    (hgap : ∀ i < n, x i < x (i + 1)) (hM0 : M 0 = 0) (hMn : M n = 0) :
    (momentMatrix x n).mulVec (fun k : Fin (n - 1) ↦ M ((k : ℕ) + 1)) =
        (fun j : Fin (n - 1) ↦ rhs x y ((j : ℕ) + 1)) ↔
      ∀ i, i + 2 ≤ n →
        deriv (interpSpline x y M i) (x (i + 1)) =
          deriv (interpSpline x y M (i + 1)) (x (i + 1)) := by
  constructor
  · intro h i hi
    have := congrFun h ⟨i, by omega⟩
    rw [momentMatrix_mulVec_apply x M hM0 hMn] at this
    exact (deriv_interpSpline_match_iff x y M (gap_pos x hgap (by omega))
      (gap_pos x hgap (by omega))).2 this
  · intro h
    funext j
    rw [momentMatrix_mulVec_apply x M hM0 hMn]
    exact (deriv_interpSpline_match_iff x y M (gap_pos x hgap (by omega))
      (gap_pos x hgap (by omega))).1 (h j (by omega))

/-- **The natural cubic spline exists and is unique.** For strictly increasing pillars
`x 0 < ⋯ < x n` (`2 ≤ n`) and any values `y`, there is a moment sequence with natural ends
`M 0 = M n = 0` for which adjacent pieces of `interpSpline` match in slope at every interior
pillar, and it is the only one on `0, …, n`. The pieces interpolate the data
(`interpSpline_left_eq`, `interpSpline_right_eq`), have second derivative `M i` at `x i` from both
sides (`deriv_deriv_interpSpline_left`, `deriv_deriv_interpSpline_right`), so the glued function
is `C²` at the pillars with vanishing curvature at the two ends. -/
theorem exists_unique_natural_spline_moments {n : ℕ} (x y : ℕ → ℝ) (hn : 2 ≤ n)
    (hgap : ∀ i < n, x i < x (i + 1)) :
    ∃ M : ℕ → ℝ, M 0 = 0 ∧ M n = 0 ∧
      (∀ i, i + 2 ≤ n → deriv (interpSpline x y M i) (x (i + 1)) =
        deriv (interpSpline x y M (i + 1)) (x (i + 1))) ∧
      ∀ M' : ℕ → ℝ, M' 0 = 0 → M' n = 0 →
        (∀ i, i + 2 ≤ n → deriv (interpSpline x y M' i) (x (i + 1)) =
          deriv (interpSpline x y M' (i + 1)) (x (i + 1))) → ∀ k ≤ n, M' k = M k := by
  obtain ⟨Mv, hMv, huniq⟩ := exists_unique_moments x y hn hgap
  let M : ℕ → ℝ := fun k ↦ if h : 1 ≤ k ∧ k < n then Mv ⟨k - 1, by omega⟩ else 0
  have hM0 : M 0 = 0 := dite_eq_right (by omega)
  have hMn : M n = 0 := dite_eq_right (by omega)
  have hMk : (fun k : Fin (n - 1) ↦ M ((k : ℕ) + 1)) = Mv := by
    funext k
    have h : 1 ≤ (k : ℕ) + 1 ∧ (k : ℕ) + 1 < n := ⟨by omega, by have := k.2; omega⟩
    simp only [M, dite_eq_left h]
    rfl
  refine ⟨M, hM0, hMn, (momentMatrix_mulVec_eq_iff x y M hgap hM0 hMn).1 (hMk ▸ hMv), ?_⟩
  intro M' h0 hn' hmatch k hk
  have hM' := huniq (fun k : Fin (n - 1) ↦ M' ((k : ℕ) + 1))
    ((momentMatrix_mulVec_eq_iff x y M' hgap h0 hn').2 hmatch)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [h0, hM0]
  · by_cases hkn : k = n
    · rw [hkn, hn', hMn]
    · have := congrFun hM' ⟨k - 1, by omega⟩
      rw [← hMk] at this
      simpa [show k - 1 + 1 = k by omega] using this

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
