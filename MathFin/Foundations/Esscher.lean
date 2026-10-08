/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The Esscher transform of a law on `ℝ`

The Esscher transform with parameter `θ` reweights a law `μ` on `ℝ` by `e^{θx}` and renormalizes
it: Mathlib's exponentially tilted measure `μ.tilted (θ * ·)`. Gerber and Shiu use it to choose a
pricing measure; here it acts on one law on `ℝ`. For a Gaussian law it is the static Girsanov change
of measure.

* `integral_exp_mul_tilted_const_mul`, `mgf_id_tilted_const_mul`: the exponential moments of the
  tilted law are ratios of those of `μ`, `∫ e^{ux} dμ_θ = ∫ e^{(u + θ)x} dμ / ∫ e^{θx} dμ`
  (Mathlib's `integral_exp_tilted` at linear exponents).
* `integrable_exp_mul_tilted_const_mul`: `μ_θ` has the exponential moment of order `u` when `μ` has
  those of orders `θ` and `u + θ`.
* `measure_eq_of_mgf_id_eq`: a probability law with exponential moments of every order is
  determined by its moment-generating function (through Mathlib's complex moment-generating
  function).
* `gaussianReal_tilted_const_mul`: the transform shifts the mean of a Gaussian law, `N(m, v)`
  tilted by `e^{θx}` is `N(m + θv, v)`.

The first three identify a tilted law by computing one function. Their users: the Esscher
transform of the jump-diffusion log-return law (`jumpDiffusionIncrementLaw_tilted`) uses all three,
and the Gaussian increments of `isQBrownianMotion_of_expMartingale` are identified by
`measure_eq_of_mgf_id_eq`. The Gaussian tilt gives the static Girsanov change of measure
(`gaussianReal_withDensity_esscher`, its case `N(0, 1)`), the no-jump tilt
(`jumpDiffusionIncrementLaw_zero_tilted`) and Merton's tilted jumps (`mertonJump_tilted`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- **A law with exponential moments of every order is determined by its moment-generating
function**: a probability law `μ` on `ℝ` with every exponential moment equals each finite measure
`μ'` with the same moment-generating function. Their complex moment-generating functions then
agree on the whole plane (Mathlib's `eqOn_complexMGF_of_mgf`), and these determine the measure
(`Measure.ext_of_complexMGF_id_eq`). -/
lemma measure_eq_of_mgf_id_eq {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsFiniteMeasure μ']
    (hμ : ∀ u, Integrable (fun x ↦ rexp (u * x)) μ) (h : mgf id μ = mgf id μ') : μ = μ' := by
  have hset : integrableExpSet id μ = Set.univ := Set.eq_univ_of_forall hμ
  refine Measure.ext_of_complexMGF_id_eq (funext fun z ↦ eqOn_complexMGF_of_mgf h ?_)
  simp [hset]

/-- **The exponential moments of an Esscher-tilted law** are ratios of those of the law:
`∫ e^{ux} dμ_θ = ∫ e^{(u + θ)x} dμ / ∫ e^{θx} dμ`, for `μ_θ = μ.tilted (θ * ·)`. This is Mathlib's
`integral_exp_tilted` at linear exponents. -/
lemma integral_exp_mul_tilted_const_mul (μ : Measure ℝ) (θ u : ℝ) :
    ∫ x, rexp (u * x) ∂(μ.tilted (θ * ·))
      = (∫ x, rexp ((u + θ) * x) ∂μ) / ∫ x, rexp (θ * x) ∂μ := by
  simp only [integral_exp_tilted, Pi.add_apply, ← add_mul, add_comm θ u]

/-- `integral_exp_mul_tilted_const_mul` in Mathlib's terms:
`mgf id μ_θ u = mgf id μ (u + θ) / mgf id μ θ`. -/
lemma mgf_id_tilted_const_mul (μ : Measure ℝ) (θ u : ℝ) :
    mgf id (μ.tilted (θ * ·)) u = mgf id μ (u + θ) / mgf id μ θ :=
  integral_exp_mul_tilted_const_mul μ θ u

/-- An Esscher-tilted law has the exponential moment of order `u` when the law has those of orders
`θ` and `u + θ`. -/
lemma integrable_exp_mul_tilted_const_mul {μ : Measure ℝ} {θ u : ℝ}
    (hθ : Integrable (fun x ↦ rexp (θ * x)) μ) (hu : Integrable (fun x ↦ rexp ((u + θ) * x)) μ) :
    Integrable (fun x ↦ rexp (u * x)) (μ.tilted (θ * ·)) := by
  rw [integrable_tilted_iff hθ]
  simpa only [smul_eq_mul, ← Real.exp_add, ← add_mul, add_comm θ u] using hu

/-- **The Esscher transform of a Gaussian law shifts its mean**: `N(m, v)` tilted by `e^{θx}` is
`N(m + θv, v)`. The Gaussian `N(m + θv, v)` has every exponential moment, and the two
moment-generating functions agree: `𝔼[e^{(u + θ)X}] / 𝔼[e^{θX}] = e^{(m + θv)u + vu²/2}` for
`X ~ N(m, v)` (Mathlib's `mgf_id_gaussianReal`). -/
lemma gaussianReal_tilted_const_mul (m : ℝ) (v : ℝ≥0) (θ : ℝ) :
    (gaussianReal m v).tilted (θ * ·) = gaussianReal (m + θ * v) v := by
  refine Eq.symm (measure_eq_of_mgf_id_eq integrable_exp_mul_gaussianReal (funext fun u ↦ ?_))
  simp only [mgf_id_tilted_const_mul, mgf_id_gaussianReal, ← Real.exp_sub]
  congr 1
  ring

end MathFin
