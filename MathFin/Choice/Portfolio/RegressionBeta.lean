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

* `MathFin.integral_residual_mul_affine`: the residual `Y - (E Y + β (X - E X))` is orthogonal to
  every affine function of `X`.
* `MathFin.integral_sq_affine_eq_add`: Pythagoras, `E[(Y - (a + b X))²]` is the least-squares error
  plus the mean squared distance between the predictors.
* `MathFin.integral_sq_affine_le`: `E[(Y - (E Y + β (X - E X)))²] ≤ E[(Y - (a + b X))²]` for all
  `a, b`, the corollary.
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

/-- **The residual of the regression is orthogonal to every affine function of `X`**: for
square-integrable `Y`, `X` with `Var X ≠ 0`, the residual `Y − (E Y + β (X − E X))`,
`β = beta Cov(Y, X) Var X`, has `E[residual · (c + d X)] = 0`. The residual has mean zero, and
`E[residual · (X − E X)] = Cov(Y, X) − β Var X = 0`. -/
theorem integral_residual_mul_affine (hY : MemLp Y 2 P) (hX : MemLp X 2 P) (hvar : Var[X; P] ≠ 0)
    (c d : ℝ) :
    ∫ ω, (Y ω - (P[Y] + beta cov[Y, X; P] Var[X; P] * (X ω - P[X]))) * (c + d * X ω) ∂P = 0 := by
  rw [show beta cov[Y, X; P] Var[X; P] = cov[Y, X; P] / Var[X; P] from rfl]
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = cov[Y, X; P] / Var[X; P] := ⟨_, rfl⟩
  rw [← hβ]
  have hYc : MemLp (fun ω ↦ Y ω - P[Y]) 2 P := hY.sub (memLp_const _)
  have hXc : MemLp (fun ω ↦ X ω - P[X]) 2 P := hX.sub (memLp_const _)
  have hR : MemLp (fun ω ↦ (Y ω - P[Y]) - β * (X ω - P[X])) 2 P := hYc.sub (hXc.const_mul β)
  have hi2 : Integrable (fun ω ↦ X ω - P[X]) P := hXc.integrable one_le_two
  have h0 : ∫ ω, ((Y ω - P[Y]) - β * (X ω - P[X])) ∂P = 0 := by
    rw [integral_sub (hYc.integrable one_le_two) (hi2.const_mul β), integral_const_mul,
      integral_sub (hY.integrable one_le_two) (integrable_const _),
      integral_sub (hX.integrable one_le_two) (integrable_const _)]
    simp
  have h1 : ∫ ω, ((Y ω - P[Y]) - β * (X ω - P[X])) * (X ω - P[X]) ∂P = 0 := by
    have e (ω : Ω) : ((Y ω - P[Y]) - β * (X ω - P[X])) * (X ω - P[X])
        = (Y ω - P[Y]) * (X ω - P[X]) - β * ((X ω - P[X]) * (X ω - P[X])) := by ring
    simp_rw [e]
    rw [integral_sub (hYc.integrable_mul hXc) ((hXc.integrable_mul hXc).const_mul β),
      integral_const_mul]
    have hc : ∫ ω, (Y ω - P[Y]) * (X ω - P[X]) ∂P = cov[Y, X; P] := rfl
    have hv : ∫ ω, (X ω - P[X]) * (X ω - P[X]) ∂P = Var[X; P] := by
      rw [← covariance_self hX.aemeasurable]; rfl
    rw [hc, hv, hβ, div_mul_cancel₀ _ hvar, sub_self]
  have e (ω : Ω) : (Y ω - (P[Y] + β * (X ω - P[X]))) * (c + d * X ω)
      = (c + d * P[X]) * ((Y ω - P[Y]) - β * (X ω - P[X]))
        + d * (((Y ω - P[Y]) - β * (X ω - P[X])) * (X ω - P[X])) := by ring
  simp_rw [e]
  rw [integral_add (hR.integrable one_le_two |>.const_mul _)
      ((hR.integrable_mul hXc).const_mul d),
    integral_const_mul, integral_const_mul, h0, h1]
  simp

/-- **Pythagoras for the regression**: the mean squared error of any affine predictor `a + b X` is
that of the least-squares predictor `E Y + β (X − E X)` plus the mean squared distance between the
two predictors, because the residual is orthogonal to the difference, an affine function of `X`
(`integral_residual_mul_affine`). -/
theorem integral_sq_affine_eq_add (hY : MemLp Y 2 P) (hX : MemLp X 2 P) (hvar : Var[X; P] ≠ 0)
    (a b : ℝ) :
    ∫ ω, (Y ω - (a + b * X ω)) ^ 2 ∂P
      = ∫ ω, (Y ω - (P[Y] + beta cov[Y, X; P] Var[X; P] * (X ω - P[X]))) ^ 2 ∂P
        + ∫ ω, ((P[Y] + beta cov[Y, X; P] Var[X; P] * (X ω - P[X])) - (a + b * X ω)) ^ 2 ∂P := by
  have horth := integral_residual_mul_affine hY hX hvar (P[Y] - beta cov[Y, X; P] Var[X; P] * P[X]
    - a) (beta cov[Y, X; P] Var[X; P] - b)
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = beta cov[Y, X; P] Var[X; P] := ⟨_, rfl⟩
  rw [← hβ] at horth ⊢
  obtain ⟨R, hRd⟩ : ∃ R : Ω → ℝ, ∀ ω, R ω = Y ω - (P[Y] + β * (X ω - P[X])) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : Ω → ℝ,
      ∀ ω, A ω = (P[Y] + β * (X ω - P[X])) - (a + b * X ω) := ⟨_, fun _ ↦ rfl⟩
  have hAd' (ω : Ω) : A ω = (P[Y] - β * P[X] - a) + (β - b) * X ω := by rw [hAd]; ring
  have hRm : MemLp R 2 P := by
    rw [show R = fun ω ↦ Y ω - (P[Y] + β * (X ω - P[X])) from funext hRd]
    exact hY.sub ((memLp_const _).add ((hX.sub (memLp_const _)).const_mul β))
  have hAm : MemLp A 2 P := by
    rw [show A = fun ω ↦ (P[Y] - β * P[X] - a) + (β - b) * X ω from funext hAd']
    exact (memLp_const _).add (hX.const_mul _)
  have hRA : Integrable (fun ω ↦ R ω * A ω) P := hRm.integrable_mul hAm
  have horth' : ∫ ω, R ω * A ω ∂P = 0 := by
    simp_rw [hRd, hAd']
    exact horth
  have key (ω : Ω) : (Y ω - (a + b * X ω)) ^ 2 = R ω ^ 2 + 2 * (R ω * A ω) + A ω ^ 2 := by
    rw [hRd, hAd]; ring
  simp_rw [key, ← hRd, ← hAd]
  rw [integral_add (hRm.integrable_sq.add (hRA.const_mul 2)) hAm.integrable_sq,
    integral_add hRm.integrable_sq (hRA.const_mul 2), integral_const_mul, horth']
  ring

/-- **The CAPM beta is the least-squares slope**: for square-integrable `Y`, `X` with
`Var X ≠ 0`, the affine predictor `E Y + β (X - E X)`, `β = beta Cov(Y, X) Var X`, has mean
squared error at most that of any affine predictor `a + b X`: by Pythagoras
(`integral_sq_affine_eq_add`) the other predictor's error exceeds it by a square. -/
theorem integral_sq_affine_le (hY : MemLp Y 2 P) (hX : MemLp X 2 P) (hvar : Var[X; P] ≠ 0)
    (a b : ℝ) :
    ∫ ω, (Y ω - (P[Y] + beta cov[Y, X; P] Var[X; P] * (X ω - P[X]))) ^ 2 ∂P
      ≤ ∫ ω, (Y ω - (a + b * X ω)) ^ 2 ∂P := by
  rw [integral_sq_affine_eq_add hY hX hvar a b]
  exact le_add_of_nonneg_right (integral_nonneg fun _ ↦ sq_nonneg _)

end MathFin
