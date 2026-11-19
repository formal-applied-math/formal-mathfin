/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Raphael Coelho
-/
module

public import MathFin.Choice.Portfolio.CAPM
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# The CAPM beta is the least-squares slope

For square-integrable `Y` and `X` on a probability space with `Var X ≠ 0`, the affine predictor
`E Y + β (X - E X)` with `β = Cov(Y, X) / Var X` (the CAPM beta `MathFin.beta` of `Y` against `X`)
has the least mean squared error among all affine functions `a + b X` of `X`: the market model is
the regression of `Y` on `X`. Credibility premiums, the single-index model and the CAPM all read
this one statement.

## Main results

* `MathFin.integral_sq_affine_le`: `E[(Y - (E Y + β (X - E X)))²] ≤ E[(Y - (a + b X))²]` for all
  `a, b`.
* `MathFin.integral_sq_sub_eq_variance_add`: `E[(Z - a)²] = Var Z + (E Z - a)²`.

## References

* [H. Bühlmann and A. Gisler, *A Course in Credibility Theory and its
  Applications*][BuhlmannGisler2005], §3.1

## Tags

least squares, regression, beta, best linear predictor, MSC 62P05, MSC 91G10
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathFin

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Y X Z : Ω → ℝ}

/-- **Bias-variance decomposition**: `E[(Z - a)²] = Var Z + (E Z - a)²`. -/
theorem integral_sq_sub_eq_variance_add (hZ : MemLp Z 2 P) (a : ℝ) :
    ∫ ω, (Z ω - a) ^ 2 ∂P = Var[Z; P] + (P[Z] - a) ^ 2 := by
  have h : Var[fun ω ↦ Z ω - a; P] = ∫ ω, (Z ω - a) ^ 2 ∂P - (∫ ω, (Z ω - a) ∂P) ^ 2 :=
    variance_eq_sub (hZ.sub (memLp_const a))
  have hv : Var[fun ω ↦ Z ω - a; P] = Var[Z; P] := variance_sub_const hZ.aestronglyMeasurable a
  rw [hv, integral_sub (hZ.integrable one_le_two) (integrable_const a)] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

/-- **The CAPM beta is the least-squares slope**: for square-integrable `Y`, `X` with
`Var X ≠ 0`, the affine predictor `E Y + β (X - E X)`, `β = beta Cov(Y, X) Var X`, has mean
squared error at most that of any affine predictor `a + b X`. -/
theorem integral_sq_affine_le (hY : MemLp Y 2 P) (hX : MemLp X 2 P) (hvar : Var[X; P] ≠ 0)
    (a b : ℝ) :
    ∫ ω, (Y ω - (P[Y] + beta cov[Y, X; P] Var[X; P] * (X ω - P[X]))) ^ 2 ∂P
      ≤ ∫ ω, (Y ω - (a + b * X ω)) ^ 2 ∂P := by
  have hpos : 0 < Var[X; P] := lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvar)
  -- the mean squared error of `a + b X` is `Var (Y - bX) + (E(Y - bX) - a)²`
  have hmse (a b : ℝ) : ∫ ω, (Y ω - (a + b * X ω)) ^ 2 ∂P
      = Var[Y; P] - 2 * b * cov[Y, X; P] + b ^ 2 * Var[X; P] + (P[Y] - b * P[X] - a) ^ 2 := by
    have hZ : MemLp (fun ω ↦ Y ω - b * X ω) 2 P := hY.sub (hX.const_mul b)
    have h := integral_sq_sub_eq_variance_add hZ a
    have e (ω : Ω) : Y ω - (a + b * X ω) = (Y ω - b * X ω) - a := by ring
    have hvarZ : Var[fun ω ↦ Y ω - b * X ω; P]
        = Var[Y; P] - 2 * b * cov[Y, X; P] + b ^ 2 * Var[X; P] := by
      rw [variance_fun_sub hY (hX.const_mul b), covariance_const_mul_right,
        variance_const_mul]
      ring
    simp_rw [e]
    rw [h, hvarZ, integral_sub (hY.integrable one_le_two)
      ((hX.const_mul b).integrable one_le_two), integral_const_mul]
  have hβ : beta cov[Y, X; P] Var[X; P] = cov[Y, X; P] / Var[X; P] := rfl
  have e (ω : Ω) : Y ω - (P[Y] + beta cov[Y, X; P] Var[X; P] * (X ω - P[X]))
      = Y ω - ((P[Y] - beta cov[Y, X; P] Var[X; P] * P[X])
          + beta cov[Y, X; P] Var[X; P] * X ω) := by
    ring
  simp_rw [e]
  rw [hmse, hmse, hβ]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  have hc : 0 ≤ (P[Y] - b * P[X] - a) ^ 2 := sq_nonneg _
  have hq : 0 ≤ Var[X; P] * (b - cov[Y, X; P] / Var[X; P]) ^ 2 :=
    mul_nonneg hpos.le (sq_nonneg _)
  have hid : Var[X; P] * (b - cov[Y, X; P] / Var[X; P]) ^ 2
      = b ^ 2 * Var[X; P] - 2 * b * cov[Y, X; P] + cov[Y, X; P] ^ 2 / Var[X; P] := by
    field_simp
    ring
  have hid2 : (cov[Y, X; P] / Var[X; P]) ^ 2 * Var[X; P] = cov[Y, X; P] ^ 2 / Var[X; P] := by
    field_simp
  have hid3 : cov[Y, X; P] / Var[X; P] * cov[Y, X; P] = cov[Y, X; P] ^ 2 / Var[X; P] := by ring
  linarith [hid, hid2, hid3, hc, hq]

end MathFin
