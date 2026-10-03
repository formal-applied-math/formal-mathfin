/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-! # Cauchy–Schwarz in expectation

The real `L²` inequality `∫|f·g| ≤ √(∫ f²)·√(∫ g²)`, read off Mathlib's Hölder inequality
`integral_mul_norm_le_Lp_mul_Lq` at exponents `2, 2`, and its cases against the constant `1`:
`(∫ f)² ≤ ν(univ)·∫ f²` on a finite measure, and `∫|f| ≤ √(∫ f²)` on a probability measure.
Mathlib's `L²` Cauchy–Schwarz is stated for inner products of `Lp` classes, and Jensen
(`ConvexOn.map_integral_le`) gives only the probability case of the second, so the real forms are
assembled once here.

Consumed by the drift `L²` energy bound (`DriftProcessPredictable`, at `ν = timeMeasure.restrict`),
the SDE-uniqueness drift estimate (`SDEUniqueness`, at `ν = volume.restrict (Ioc 0 s)`), and the
`L¹` bounds of the adapted quadratic variation (`AdaptedQuadraticVariation`).
-/

@[expose] public section

open MeasureTheory

namespace MathFin

variable {α : Type*} {m : MeasurableSpace α} {ν : Measure α}

/-- **Cauchy–Schwarz in expectation**: `∫|f·g| ≤ √(∫ f²)·√(∫ g²)`, Hölder at exponents `2, 2`. -/
theorem integral_abs_mul_le_sqrt_mul_sqrt {f g : α → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ∫ a, |f a * g a| ∂ν ≤ √(∫ a, f a ^ 2 ∂ν) * √(∫ a, g a ^ 2 ∂ν) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := ν) Real.HolderConjugate.two_two (f := f) (g := g)
    (by rwa [ENNReal.ofReal_ofNat]) (by rwa [ENNReal.ofReal_ofNat])
  have hsq (x : ℝ) : |x| ^ (2 : ℝ) = x ^ 2 := by rw [Real.rpow_two, sq_abs]
  simpa only [Real.norm_eq_abs, hsq, ← Real.sqrt_eq_rpow, ← abs_mul] using h

/-- **Cauchy–Schwarz on a finite measure**: `(∫ f)² ≤ ν(univ)·∫ f²`, the case `g ≡ 1`. -/
theorem sq_integral_le_measureReal_mul [IsFiniteMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    (∫ a, f a ∂ν) ^ 2 ≤ (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
  have h := integral_abs_mul_le_sqrt_mul_sqrt hf (memLp_const (1 : ℝ))
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at h
  calc (∫ a, f a ∂ν) ^ 2 = |∫ a, f a ∂ν| ^ 2 := (sq_abs _).symm
    _ ≤ (√(∫ a, f a ^ 2 ∂ν) * √(ν.real Set.univ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_integral_le_integral_abs.trans h) 2
    _ = (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
          Real.sq_sqrt measureReal_nonneg, mul_comm, measureReal_def]

/-- `∫|f| ≤ √(∫ f²)` on a probability measure, the case `g ≡ 1`. -/
theorem integral_abs_le_sqrt_integral_sq [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : MemLp f 2 ν) : ∫ a, |f a| ∂ν ≤ √(∫ a, f a ^ 2 ∂ν) := by
  simpa using integral_abs_mul_le_sqrt_mul_sqrt hf (memLp_const (1 : ℝ))

end MathFin
