/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionDigital
public import MathFin.BlackScholes.BreedenLitzenberger

/-!
# The density of a jump-diffusion log-return, and Breeden–Litzenberger with jumps

Given the jump count `n` and the jump sizes `j₀, j₁, …`, the log-return over `τ` is Gaussian,
`N(bτ + ∑_{i<n} jᵢ, σ²τ)` (`jumpDiffusionIncrementLaw_apply`). With a Gaussian part (`σ ≠ 0`,
`τ > 0`) the law is therefore `f(y) dy`, with `f` the mixture of the Gaussian densities over
`Poisson(Λτ) ⊗ ν^ℕ` (`jumpDiffusionDensity`), the Poisson mixture of normal densities of
Merton (1976) for any jump law.

* `jumpDiffusionIncrementLaw_eq_withDensity`: the law is `f(y) dy` (Tonelli).
* `continuous_jumpDiffusionDensity`: `f` is continuous, by dominated convergence, since a Gaussian
  density is at most `1/√(2πv)` (`gaussianPDFReal_le_inv_sqrt`).
* `hasDerivAt_measureReal_Ioi_withDensity`: for any law `f(y) dy`, the tail `x ↦ P(Y > x)` is
  differentiable wherever `f` is continuous, with derivative `−f`.
* `hasDerivAt_jumpDiffusionDigitalPrice_strike`: so the digital price has strike derivative
  `−e^{−rτ}f(log(K/S))/K`. Here `f(log(K/S))/K` is minus the strike derivative of `P(Se^Y > K)`,
  the density of the price at `K`.
* `breedenLitzenberger_jumpDiffusion`: Breeden–Litzenberger with jumps. The second strike
  derivative of the call price is `e^{−rτ}f(log(K/S))/K`, the discounted density of the price.
* `jumpDiffusionDensity_div_eq_lognormalTerminalPDF`: without jumps the density of the price at `K`
  is `lognormalTerminalPDF`. The two second derivatives, this file's and `breedenLitzenberger`'s,
  are equal, so the lognormal formula of `BreedenLitzenberger.lean` is the density of the price.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

/-- A Gaussian density is at most `1/√(2πv)`. -/
lemma gaussianPDFReal_le_inv_sqrt (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.exp_le_one_iff.2 ?_)
  rw [neg_div]
  exact neg_nonpos.2 (by positivity)

/-- A Gaussian density is continuous. -/
lemma continuous_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Continuous (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- **The density of the jump-diffusion log-return** over `τ`: the mixture, over the jump count `n`
and the jump sizes `j` (law `Poisson(Λτ) ⊗ ν^ℕ`), of the Gaussian densities
`φ(y; bτ + ∑_{i<n} jᵢ, σ²τ)`. For `σ ≠ 0` and `τ > 0` it is the density of the log-return law
(`jumpDiffusionIncrementLaw_eq_withDensity`). -/
noncomputable def jumpDiffusionDensity (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) (y : ℝ) :
    ℝ :=
  ∫ ω, gaussianPDFReal (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i) (.mk (σ ^ 2) (sq_nonneg _) * τ) y
    ∂((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν))

lemma jumpDiffusionDensity_nonneg (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) (y : ℝ) :
    0 ≤ jumpDiffusionDensity b σ Λ ν τ y :=
  integral_nonneg fun _ ↦ gaussianPDFReal_nonneg _ _ _

/-- The mixed Gaussian densities are measurable in the jumps. -/
lemma measurable_gaussianPDFReal_jumps (b : ℝ) (v : ℝ≥0) (τ : ℝ≥0) (y : ℝ) :
    Measurable fun ω : ℕ × (ℕ → ℝ) ↦
      gaussianPDFReal (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i) v y :=
  measurable_uncurry_gaussianPDFReal.comp
    ((measurable_const.add measurable_sum_range_prod).prodMk
      (measurable_const.prodMk measurable_const))

/-- **The log-return law is a mixture of Gaussian laws**: given the jump count `n` and the jump
sizes `j`, the log-return is `N(bτ + ∑_{i<n} jᵢ, σ²τ)`, the image of the standard normal sample
under an affine map. -/
lemma jumpDiffusionIncrementLaw_apply (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) :
    jumpDiffusionIncrementLaw b σ Λ ν τ A
      = ∫⁻ ω, gaussianReal (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i)
          (.mk (σ ^ 2) (sq_nonneg _) * τ) A
          ∂((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) := by
  have hL := measurable_jumpDiffusionLogReturn b σ τ
  rw [jumpDiffusionIncrementLaw, Measure.map_apply hL hA, jumpDiffusionMeasure,
    Measure.prod_apply_symm (hL hA)]
  refine lintegral_congr fun ω ↦ ?_
  have hmeas : Measurable fun z ↦ jumpDiffusionLogReturn b σ τ (z, ω) :=
    hL.comp measurable_prodMk_right
  -- given the jumps, the log-return is an affine image of the Gaussian sample
  have hG : (gaussianReal 0 1).map (fun z ↦ jumpDiffusionLogReturn b σ τ (z, ω))
      = gaussianReal (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i) (.mk (σ ^ 2) (sq_nonneg _) * τ) := by
    have hf : (fun z ↦ jumpDiffusionLogReturn b σ τ (z, ω))
        = (fun x ↦ (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i) + x) ∘ fun z ↦ σ * Real.sqrt τ * z := by
      funext z
      simp only [Function.comp_apply, jumpDiffusionLogReturn]
      ring
    rw [hf, ← Measure.map_map (measurable_const_add _) (measurable_const_mul _),
      gaussianReal_map_const_mul, gaussianReal_map_const_add, mul_zero, zero_add]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, mul_one]
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg τ)]
  rw [show (fun z ↦ (z, ω)) ⁻¹' (jumpDiffusionLogReturn b σ τ ⁻¹' A)
      = (fun z ↦ jumpDiffusionLogReturn b σ τ (z, ω)) ⁻¹' A from rfl, ← hG,
    Measure.map_apply hmeas hA]

/-- The mixed Gaussian densities are integrable in the jumps: they are bounded. -/
lemma integrable_gaussianPDFReal_jumps (b : ℝ) (v : ℝ≥0) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) (y : ℝ) :
    Integrable (fun ω : ℕ × (ℕ → ℝ) ↦
        gaussianPDFReal (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i) v y)
      ((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) :=
  Integrable.of_bound (measurable_gaussianPDFReal_jumps b v τ y).aestronglyMeasurable
    (√(2 * π * v))⁻¹ (ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact gaussianPDFReal_le_inv_sqrt _ _ _)

/-- **The log-return law has the density `f`** when `σ ≠ 0` and `τ > 0`: each Gaussian law of the
mixture is `φ(y) dy`, and the mixture of the densities is the density of the mixture (Tonelli,
Mathlib's `lintegral_lintegral_swap`). -/
theorem jumpDiffusionIncrementLaw_eq_withDensity (b : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (Λ : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionIncrementLaw b σ Λ ν τ
      = volume.withDensity fun y ↦ ENNReal.ofReal (jumpDiffusionDensity b σ Λ ν τ y) := by
  have hv : (.mk (σ ^ 2) (sq_nonneg _) * τ : ℝ≥0) ≠ 0 := by
    rw [← NNReal.coe_ne_zero, NNReal.coe_mul, NNReal.coe_mk]
    exact mul_ne_zero (pow_ne_zero 2 hσ) (NNReal.coe_ne_zero.2 hτ.ne')
  ext A hA
  have hmeas : AEMeasurable (Function.uncurry fun (ω : ℕ × (ℕ → ℝ)) (x : ℝ) ↦
      gaussianPDF (b * τ + ∑ i ∈ Finset.range ω.1, ω.2 i) (.mk (σ ^ 2) (sq_nonneg _) * τ) x)
      (((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν)).prod
        (volume.restrict A)) :=
    (measurable_uncurry_gaussianPDF.comp
      (((measurable_const.add measurable_sum_range_prod).comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))).aemeasurable
  rw [jumpDiffusionIncrementLaw_apply b σ Λ ν τ hA, withDensity_apply _ hA]
  simp_rw [gaussianReal_apply _ hv A]
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr fun y ↦ ?_
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal_jumps b _ Λ ν τ y)
    (ae_of_all _ fun _ ↦ gaussianPDFReal_nonneg _ _ _)).symm

/-- **The density of the log-return is continuous**: dominated convergence, the Gaussian densities
being continuous in `y` and bounded by `1/√(2πσ²τ)`. -/
theorem continuous_jumpDiffusionDensity (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) : Continuous (jumpDiffusionDensity b σ Λ ν τ) :=
  continuous_of_dominated
    (bound := fun _ ↦ (√(2 * π * (.mk (σ ^ 2) (sq_nonneg _) * τ : ℝ≥0)))⁻¹)
    (fun y ↦ (measurable_gaussianPDFReal_jumps b _ τ y).aestronglyMeasurable)
    (fun y ↦ ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact gaussianPDFReal_le_inv_sqrt _ _ _)
    (integrable_const _) (ae_of_all _ fun ω ↦ continuous_gaussianPDFReal _ _)

/-- **The tail of a law with a density is differentiable where the density is continuous**: for
the law `f(y) dy`, with `f ≥ 0` integrable and continuous at `a`, `x ↦ P(Y > x)` has derivative
`−f(a)` at `a` (the fundamental theorem of calculus, Mathlib's
`intervalIntegral.integral_hasDerivAt_right`). -/
theorem hasDerivAt_measureReal_Ioi_withDensity {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) {a : ℝ} (hfa : ContinuousAt f a) :
    HasDerivAt (fun x ↦ (volume.withDensity fun y ↦ ENNReal.ofReal (f y)).real (Ioi x))
      (-f a) a := by
  have hIoi (x : ℝ) : (volume.withDensity fun y ↦ ENNReal.ofReal (f y)).real (Ioi x)
      = ∫ y, f y - ∫ y in Iic a, f y - ∫ y in a..x, f y := by
    have h1 := integral_add_compl (measurableSet_Iic (a := x)) hf
    have h2 := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := x) hf.integrableOn
      hf.integrableOn
    rw [compl_Iic] at h1
    rw [Measure.real, withDensity_apply _ measurableSet_Ioi,
      ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ fun y ↦ hf0 y),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun y _ ↦ hf0 y)]
    linarith
  exact ((intervalIntegral.integral_hasDerivAt_right hf.intervalIntegrable
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hfa).const_sub _).congr_of_eventuallyEq
    (Eventually.of_forall hIoi)

/-- **The strike derivative of the digital price is minus the discounted density of the price.**
With a Gaussian part (`σ ≠ 0`, `τ > 0`), at a strike `K > 0`,
`∂D/∂K = −e^{−rτ}f(log(K/S))/K`. Here `f(log(K/S))/K` is minus the strike derivative of
`P(Se^Y > K) = P(Y > log(K/S))`, the density of the price `Se^Y` at `K`. -/
theorem hasDerivAt_jumpDiffusionDigitalPrice_strike {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) {K : ℝ}
    (hK : 0 < K) :
    HasDerivAt (fun k ↦ jumpDiffusionDigitalPrice S k r b σ Λ ν τ)
      (-(rexp (-r * τ) * (jumpDiffusionDensity b σ Λ ν τ (Real.log (K / S)) / K))) K := by
  have hlaw := jumpDiffusionIncrementLaw_eq_withDensity b hσ Λ ν hτ
  have hf := continuous_jumpDiffusionDensity b σ Λ ν τ
  -- the density integrates to `1`, so it is integrable
  have hfint : Integrable (jumpDiffusionDensity b σ Λ ν τ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have h1 : (volume.withDensity fun y ↦ ENNReal.ofReal (jumpDiffusionDensity b σ Λ ν τ y))
        univ = 1 := by
      rw [← hlaw, measure_univ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (jumpDiffusionDensity_nonneg b σ Λ ν τ)), h1]
    exact ENNReal.one_lt_top
  have htail := hasDerivAt_measureReal_Ioi_withDensity hfint
    (jumpDiffusionDensity_nonneg b σ Λ ν τ) (a := Real.log (K / S)) hf.continuousAt
  have hlog : HasDerivAt (fun k ↦ Real.log (k / S)) (1 / K) K := by
    have h := ((hasDerivAt_id' K).div_const S).log (div_pos hK hS).ne'
    have hS' := hS.ne'
    have hK' := hK.ne'
    convert h using 1
    field_simp
  -- `P(Seʸ > k) = P(Y > log(k/S))` for `k > 0`
  have hset (k : ℝ) (hk : 0 < k) : {y | k < S * rexp y} = Ioi (Real.log (k / S)) := by
    ext y
    rw [mem_ofPred_eq, mem_Ioi, Real.log_lt_iff_lt_exp (div_pos hk hS), div_lt_iff₀ hS,
      mul_comm]
  have heq : ∀ᶠ k in 𝓝 K, jumpDiffusionDigitalPrice S k r b σ Λ ν τ
      = rexp (-r * τ) * (volume.withDensity fun y ↦
          ENNReal.ofReal (jumpDiffusionDensity b σ Λ ν τ y)).real (Ioi (Real.log (k / S))) := by
    filter_upwards [Ioi_mem_nhds hK] with k hk
    rw [jumpDiffusionDigitalPrice_eq, hset k hk, hlaw]
  exact (((htail.comp K hlog).const_mul (rexp (-r * τ))).congr_of_eventuallyEq heq).congr_deriv
    (by ring)

/-- **Breeden–Litzenberger with jumps.** With a Gaussian part (`σ ≠ 0`, `τ > 0`) and a finite
forward, the second strike derivative of the call price at `K > 0` is the discounted density of
the price, `∂²C/∂K² = e^{−rτ}f(log(K/S))/K`. The first derivative is minus the digital price
(`hasDerivAt_jumpDiffusionCallPrice_strike`), and the digital's derivative is minus the discounted
density (`hasDerivAt_jumpDiffusionDigitalPrice_strike`). -/
theorem breedenLitzenberger_jumpDiffusion {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) (hτ : 0 < τ) {K : ℝ}
    (hK : 0 < K) :
    HasDerivAt (deriv fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      (rexp (-r * τ) * (jumpDiffusionDensity b σ Λ ν τ (Real.log (K / S)) / K)) K := by
  have hderiv : (deriv fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      = fun k ↦ -jumpDiffusionDigitalPrice S k r b σ Λ ν τ :=
    funext fun k ↦ (hasDerivAt_jumpDiffusionCallPrice_strike hS hσ hY hτ k).deriv
  have h := (hasDerivAt_jumpDiffusionDigitalPrice_strike hS hσ hτ hK).neg
  rw [neg_neg] at h
  rw [hderiv]
  exact h

/-- **Without jumps the density of the price is the lognormal density** `lognormalTerminalPDF`.
The second strike derivative of the call price is `e^{−rτ}f(log(K/S))/K`
(`breedenLitzenberger_jumpDiffusion`) and also `e^{−rτ}·lognormalTerminalPDF`
(`breedenLitzenberger`, the call price being `bsV` near `K`, `jumpDiffusionCallPrice_zero`). So the
lognormal formula of `BreedenLitzenberger.lean` is the density of the price at `K`, read off the
uniqueness of derivatives rather than computed. -/
theorem jumpDiffusionDensity_div_eq_lognormalTerminalPDF {S K r σ : ℝ} (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionDensity (r - σ ^ 2 / 2) σ 0 ν τ (Real.log (K / S)) / K
      = lognormalTerminalPDF S r σ τ K := by
  have hY : Integrable rexp (jumpDiffusionIncrementLaw (r - σ ^ 2 / 2) σ 0 ν τ) := by
    rw [jumpDiffusionIncrementLaw_zero]
    exact (integrable_exp_mul_gaussianReal 1).congr (ae_of_all _ fun x ↦ by simp)
  have h₁ := breedenLitzenberger_jumpDiffusion hS hσ.ne' hY hτ hK
  -- near `K` the call price function is `bsV`, so the two first derivatives agree near `K`
  have h₂ : HasDerivAt (deriv fun k ↦ jumpDiffusionCallPrice S k r (r - σ ^ 2 / 2) σ 0 ν τ)
      (rexp (-(r * τ)) * lognormalTerminalPDF S r σ τ K) K := by
    refine (breedenLitzenberger hS hσ hK (NNReal.coe_pos.2 hτ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hK] with k hk
    exact Filter.EventuallyEq.deriv_eq (eventually_of_mem (Ioi_mem_nhds hk) fun k' hk' ↦
      jumpDiffusionCallPrice_zero hS hk' hσ ν hτ)
  have h := h₁.unique h₂
  rw [neg_mul] at h
  exact mul_left_cancel₀ (Real.exp_pos _).ne' h

end MathFin
