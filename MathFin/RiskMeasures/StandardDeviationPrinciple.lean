/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The standard-deviation principle: everything but monotonicity

The **standard-deviation principle** prices a loss `X` with finite variance by
`ρ(X) = E[X] + k·sd(X)` for a loading `k ≥ 0` (`stdDevPrinciple`). It satisfies three of the four
coherence axioms of `RiskMeasures/ExpectedShortfall.lean`, and fails the fourth (QRM Exercise Book, Exercises 2.19
and 8.11).

* **Translation invariance** (`stdDevPrinciple_add_const`): shifting by cash shifts the mean and
  leaves the standard deviation alone. The standard deviation alone is *not* translation
  invariant (`sqrt_variance_add_const`), which is why the mean term is there.
* **Positive homogeneity** (`stdDevPrinciple_const_mul`).
* **Subadditivity** (`stdDevPrinciple_add_le`): the standard deviation is subadditive because
  covariance obeys the Cauchy–Schwarz inequality `cov(X, Y) ≤ sd(X) sd(Y)`
  (`covariance_le_sqrt_mul_sqrt`). That inequality is the discriminant condition for the
  nonnegative quadratic `t ↦ Var(X + tY)`.
* **Monotonicity fails** (`stdDevPrinciple_not_monotone`): a loss `B ≤ 0` that equals `−1` with a
  small probability `q` and `0` otherwise has `ρ(B) > 0 = ρ(0)` once `q(1 + k²) < k²`. Its rare gains
  inflate the standard deviation more than they lower the mean. This is the counterexample of
  QRM Exercise 8.11.

## Main results

* `covariance_le_sqrt_mul_sqrt`: `cov(X, Y) ≤ √Var X · √Var Y`.
* `sqrt_variance_add_le`: the standard deviation is subadditive.
* `stdDevPrinciple_add_const`, `stdDevPrinciple_const_mul`, `stdDevPrinciple_add_le`.
* `stdDevPrinciple_not_monotone`: the principle is not monotone.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

/-- **Cauchy–Schwarz for covariance**: `cov(X, Y) ≤ √Var X · √Var Y`. The quadratic
`t ↦ Var(X + tY) = Var X + 2t·cov(X, Y) + t²·Var Y` is nonnegative, so its discriminant is not
positive. -/
theorem covariance_le_sqrt_mul_sqrt (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] ≤ √Var[X; P] * √Var[Y; P] := by
  have hquad : ∀ t : ℝ, 0 ≤ Var[Y; P] * (t * t) + 2 * cov[X, Y; P] * t + Var[X; P] := fun t ↦ by
    have h := variance_fun_add hX (hY.const_mul t)
    rw [covariance_const_mul_right, variance_const_mul] at h
    nlinarith [variance_nonneg (fun ω ↦ X ω + t * Y ω) P]
  have hsq : cov[X, Y; P] ^ 2 ≤ Var[X; P] * Var[Y; P] := by
    have := discrim_le_zero hquad
    rw [discrim] at this
    nlinarith
  calc cov[X, Y; P] ≤ |cov[X, Y; P]| := le_abs_self _
    _ = √(cov[X, Y; P] ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(Var[X; P] * Var[Y; P]) := Real.sqrt_le_sqrt hsq
    _ = √Var[X; P] * √Var[Y; P] := Real.sqrt_mul (variance_nonneg _ _) _

/-- **The standard deviation is subadditive**: `sd(X + Y) ≤ sd(X) + sd(Y)`. -/
theorem sqrt_variance_add_le (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    √Var[fun ω ↦ X ω + Y ω; P] ≤ √Var[X; P] + √Var[Y; P] := by
  rw [variance_fun_add hX hY]
  have hcs := covariance_le_sqrt_mul_sqrt hX hY
  refine Real.sqrt_le_iff.2 ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt (variance_nonneg X P), Real.sq_sqrt (variance_nonneg Y P)]

/-- The standard deviation is unchanged by a cash shift, so it is not translation invariant on
its own: `sd(X + m) = sd(X)`. -/
lemma sqrt_variance_add_const (hX : AEStronglyMeasurable X P) (m : ℝ) :
    √Var[fun ω ↦ X ω + m; P] = √Var[X; P] := by
  rw [variance_add_const hX]

/-- The **standard-deviation principle** with loading `k`: `ρ(X) = E[X] + k·sd(X)`. -/
noncomputable def stdDevPrinciple (k : ℝ) (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  P[X] + k * √Var[X; P]

/-- **Translation invariance**: `ρ(X + m) = ρ(X) + m`. -/
theorem stdDevPrinciple_add_const (k : ℝ) (hX : MemLp X 2 P) (m : ℝ) :
    stdDevPrinciple k (fun ω ↦ X ω + m) P = stdDevPrinciple k X P + m := by
  rw [stdDevPrinciple, stdDevPrinciple, integral_add (hX.integrable one_le_two)
    (integrable_const m), integral_const, sqrt_variance_add_const hX.aestronglyMeasurable]
  simp only [probReal_univ, one_smul]
  ring

omit [IsProbabilityMeasure P] in
/-- **Positive homogeneity**: `ρ(cX) = c ρ(X)` for `c ≥ 0`. -/
theorem stdDevPrinciple_const_mul (k : ℝ) (X : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    stdDevPrinciple k (fun ω ↦ c * X ω) P = c * stdDevPrinciple k X P := by
  rw [stdDevPrinciple, stdDevPrinciple, integral_const_mul, variance_const_mul,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  ring

/-- **Subadditivity**: `ρ(X + Y) ≤ ρ(X) + ρ(Y)` for a nonnegative loading. -/
theorem stdDevPrinciple_add_le {k : ℝ} (hk : 0 ≤ k) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    stdDevPrinciple k (fun ω ↦ X ω + Y ω) P ≤ stdDevPrinciple k X P + stdDevPrinciple k Y P := by
  rw [stdDevPrinciple, stdDevPrinciple, stdDevPrinciple,
    integral_add (hX.integrable one_le_two) (hY.integrable one_le_two)]
  nlinarith [mul_le_mul_of_nonneg_left (sqrt_variance_add_le hX hY) hk]

/-- **The standard-deviation principle is not monotone** (QRM Exercise 8.11). Let `B ≤ 0` take
the value `−1` with probability `q > 0` and `0` otherwise. If `q (1 + k²) < k²` then
`ρ(B) > 0 = ρ(0)`, although `B ≤ 0` pointwise. -/
theorem stdDevPrinciple_not_monotone {k : ℝ} (hk : 0 ≤ k) {B : Ω → ℝ} (hBm : Measurable B)
    (hB : ∀ ω, B ω = -1 ∨ B ω = 0) {q : ℝ} (hq : P.real {ω | B ω = -1} = q) (hq0 : 0 < q)
    (hqk : q * (1 + k ^ 2) < k ^ 2) :
    (∀ ω, B ω ≤ 0) ∧ stdDevPrinciple k (fun _ ↦ (0 : ℝ)) P < stdDevPrinciple k B P := by
  set A := {ω | B ω = -1}
  have hA : MeasurableSet A := hBm (measurableSet_singleton (-1))
  have hBeq : B = fun ω ↦ -A.indicator 1 ω := by
    ext ω
    rcases hB ω with h | h
    · simp [A, h]
    · simp [A, h]
  have hB2 : MemLp B 2 P := hBeq ▸ (memLp_indicator_const 2 hA 1 (Or.inr (measure_ne_top _ _))).neg
  have hmean : P[B] = -q := by
    rw [hBeq, integral_neg, integral_indicator_one hA, hq]
  have hsq : P[B ^ 2] = q := by
    have : B ^ 2 = A.indicator 1 := by
      ext ω
      rcases hB ω with h | h
      · simp [A, h]
      · simp [A, h]
    rw [this, integral_indicator_one hA, hq]
  have hvar : Var[B; P] = q * (1 - q) := by
    rw [variance_eq_sub hB2, hsq, hmean]
    ring
  have hq1 : q < 1 := by nlinarith
  refine ⟨fun ω ↦ (hB ω).elim (fun h ↦ h ▸ by norm_num) (fun h ↦ h.le), ?_⟩
  rw [stdDevPrinciple, stdDevPrinciple, hmean, hvar]
  have h0 : Var[fun _ ↦ (0 : ℝ); P] = 0 := by simpa using variance_const_mul 0 B P
  simp only [integral_const, smul_zero, h0, Real.sqrt_zero, mul_zero, add_zero]
  -- `q < k √(q(1 − q))` because `q² < k² q (1 − q)`
  have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have hlt : q < k * √(q * (1 - q)) := by
    have hx : (k * √(q * (1 - q))) ^ 2 = k ^ 2 * (q * (1 - q)) := by
      rw [mul_pow, Real.sq_sqrt hpos.le]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [hx]; nlinarith)
  linarith

end MathFin
