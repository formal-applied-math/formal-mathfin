/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Laplace transform of the exponential law

Mathlib has the density, the distribution function and the Gaussian moment generating function,
but no moment generating function of `expMeasure`. For `T ∼ Exp(r)`, `𝔼[e^{t T}] = r / (r − t)`
for `t < r`: the density `r e^{−r x}` on `(0, ∞)` times `e^{t x}` integrates to `r / (r − t)`
(`integral_exp_mul_Ioi`). For `t ≥ r` the integral diverges, so `t < r` is the true range; in the
Laplace form `𝔼[e^{−a T}] = r / (r + a)` it is `a > −r`.

## Main results

* `MathFin.mgf_id_expMeasure`: `mgf id (expMeasure r) t = r / (r - t)` for `0 < r`, `t < r`.
* `MathFin.HasLaw.mgf_expMeasure`: the same for a random variable with law `expMeasure r`.
* `MathFin.HasLaw.mgf_neg_expMeasure`: the Laplace transform `𝔼[e^{−a T}] = r / (r + a)` for
  `a > −r`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], B.2

## Tags

exponential distribution, Laplace transform, moment generating function, MSC 60E05, MSC 60E10
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

/-- **The moment generating function of the exponential law**:
`∫ e^{t x} d Exp(r)(x) = r / (r − t)` for `t < r`. -/
theorem mgf_id_expMeasure {r t : ℝ} (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hdens : ∀ x : ℝ, (gammaPDF 1 r x).toReal = gammaPDFReal 1 r x := fun x ↦
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x)
  unfold mgf expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [hdens, smul_eq_mul, id_eq]
  have hz : ∀ x, x ∉ Ici (0 : ℝ) → gammaPDFReal 1 r x * Real.exp (t * x) = 0 := fun x hx ↦ by
    have hx' : ¬ 0 ≤ x := hx
    simp [gammaPDFReal, hx']
  have h : ∀ x ∈ Ici (0 : ℝ),
      gammaPDFReal 1 r x * Real.exp (t * x) = r * Real.exp ((t - r) * x) := fun x hx ↦ by
    rw [gammaPDFReal, if_pos hx]
    simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    setIntegral_congr_fun measurableSet_Ici h, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (sub_neg.2 ht), mul_zero, Real.exp_zero,
    show t - r = -(r - t) by ring, neg_div_neg_eq, mul_one_div]

/-- **The moment generating function of a random variable with exponential law.** -/
theorem _root_.ProbabilityTheory.HasLaw.mgf_expMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T : Ω → ℝ} {r t : ℝ} (hT : HasLaw T (expMeasure r) P) (hr : 0 < r)
    (ht : t < r) : mgf T P t = r / (r - t) := by
  rw [← mgf_id_map hT.aemeasurable, hT.map_eq, mgf_id_expMeasure hr ht]

/-- **The Laplace transform of the exponential law**: `𝔼[e^{−a T}] = r / (r + a)` for
`T ∼ Exp(r)` and `a > −r`. -/
theorem _root_.ProbabilityTheory.HasLaw.mgf_neg_expMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T : Ω → ℝ} {r a : ℝ} (hT : HasLaw T (expMeasure r) P) (hr : 0 < r)
    (ha : -r < a) : mgf T P (-a) = r / (r + a) := by
  rw [hT.mgf_expMeasure hr (by linarith), sub_neg_eq_add]

end MathFin
