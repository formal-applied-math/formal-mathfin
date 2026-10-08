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

* `integral_exp_mul_tilted_const_mul`: the exponential moments of the tilted law are ratios of
  those of `μ`, `∫ e^{ux} dμ_θ = ∫ e^{(u + θ)x} dμ / ∫ e^{θx} dμ`.
* `integrable_exp_mul_tilted_const_mul`: if `μ` has exponential moments of every order, so does
  `μ_θ`.
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
function**: two probability laws on `ℝ` with the same moment-generating function are equal when
one of them has every exponential moment. Their complex moment-generating functions then agree on
the whole plane (Mathlib's `eqOn_complexMGF_of_mgf`), and these determine the law
(`Measure.ext_of_complexMGF_id_eq`). -/
lemma measure_eq_of_mgf_id_eq {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hμ : ∀ u, Integrable (fun x ↦ rexp (u * x)) μ)
    (h : mgf id μ = mgf id μ') : μ = μ' := by
  have hset : integrableExpSet id μ = Set.univ := Set.eq_univ_of_forall hμ
  refine Measure.ext_of_complexMGF_id_eq (funext fun z ↦ eqOn_complexMGF_of_mgf h ?_)
  simp [hset]

/-- **The exponential moments of an Esscher-tilted law** are ratios of those of the law:
`∫ e^{ux} dμ_θ = ∫ e^{(u + θ)x} dμ / ∫ e^{θx} dμ`, for `μ_θ = μ.tilted (θ * ·)`. -/
lemma integral_exp_mul_tilted_const_mul (μ : Measure ℝ) (θ u : ℝ) :
    ∫ x, rexp (u * x) ∂(μ.tilted (θ * ·))
      = (∫ x, rexp ((u + θ) * x) ∂μ) / ∫ x, rexp (θ * x) ∂μ := by
  rw [integral_tilted, ← integral_div]
  congr 1
  funext x
  rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

/-- If a law has exponential moments of every order, so does its Esscher transform. -/
lemma integrable_exp_mul_tilted_const_mul {μ : Measure ℝ}
    (hμ : ∀ u, Integrable (fun x ↦ rexp (u * x)) μ) (θ u : ℝ) :
    Integrable (fun x ↦ rexp (u * x)) (μ.tilted (θ * ·)) := by
  rw [integrable_tilted_iff (hμ θ)]
  simpa only [smul_eq_mul, ← Real.exp_add, ← add_mul, add_comm θ u] using hμ (u + θ)

/-- **The Esscher transform of a Gaussian law shifts its mean**: `N(m, v)` tilted by `e^{θx}` is
`N(m + θv, v)`. Both laws have every exponential moment, and their moment-generating functions
agree: `𝔼[e^{(u + θ)X}] / 𝔼[e^{θX}] = e^{(m + θv)u + vu²/2}` for `X ~ N(m, v)`. -/
lemma gaussianReal_tilted_const_mul (m : ℝ) (v : ℝ≥0) (θ : ℝ) :
    (gaussianReal m v).tilted (θ * ·) = gaussianReal (m + θ * v) v := by
  have hint (u : ℝ) : Integrable (fun x ↦ rexp (u * x)) (gaussianReal m v) :=
    integrable_exp_mul_gaussianReal u
  have : IsProbabilityMeasure ((gaussianReal m v).tilted (θ * ·)) :=
    isProbabilityMeasure_tilted (hint θ)
  refine measure_eq_of_mgf_id_eq (integrable_exp_mul_tilted_const_mul hint θ) (funext fun u ↦ ?_)
  have hmgf (s : ℝ) : ∫ x, rexp (s * x) ∂(gaussianReal m v) = rexp (m * s + v * s ^ 2 / 2) := by
    simpa only [mgf, id_eq] using congr_fun (mgf_id_gaussianReal (μ := m) (v := v)) s
  rw [mgf_id_gaussianReal]
  simp only [mgf, id_eq]
  rw [integral_exp_mul_tilted_const_mul, hmgf, hmgf, ← Real.exp_sub]
  congr 1
  ring

end MathFin
