/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionProcess

/-!
# The density of a jump-diffusion log-return

Given the jump count `n` and the jump sizes `j₀, j₁, …`, the log-return over `τ` is Gaussian,
`N(bτ + ∑_{i<n} jᵢ, σ²τ)`. So its law is a mixture of Gaussian laws over `Poisson(Λτ) ⊗ ν^ℕ`
(`jumpDiffusionIncrementLaw_apply`, for every `σ`). With a Gaussian part (`σ ≠ 0`, `τ > 0`) the
law therefore has a density, the mixture of the normal densities (`jumpDiffusionDensity`). For
lognormal jumps this is the Poisson mixture of normal densities of Merton (1976), which the library
states in price form (`jumpDiffusionDensity_gaussian_div_eq_mertonTerminalPDF`; the change of
variables back to the log-return is not formalized). Here the jump law is arbitrary and needs no
moment condition.

* `jumpDiffusionIncrementLaw_eq_withDensity`: the law is `f(y) dy` (Tonelli).
* `continuous_jumpDiffusionDensity`: `f` is continuous, by dominated convergence, since a normal
  density is at most `1/√(2πv)` (`gaussianPDFReal_le_inv_sqrt`).
* `nullSingletonClass_jumpDiffusionIncrementLaw`: so the law has no atoms (Mathlib's
  `nullSingletonClass_withDensity`).
* `ofReal_exp_le_jumpDiffusionIncrementLaw_singleton`: without a Gaussian part (`σ = 0`) the law
  has an atom at `bτ`, of mass at least `e^{−Λτ}`, the probability of no jump.
* `hasDerivAt_measureReal_Ioi_withDensity`: for any law `f(y) dy` with `f` integrable, the tail
  `x ↦ P(Y > x)` has derivative `−f(a)` at every `a` where `f` is continuous.

The option prices built on these facts are in `BlackScholes/JumpDiffusionDigital.lean`: the strike
derivatives of the call and the digital, and Breeden–Litzenberger with jumps.
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

/-- **With a Gaussian part the log-return law has no atoms**: it has a density
(`jumpDiffusionIncrementLaw_eq_withDensity`), and Lebesgue measure has none (Mathlib's
`nullSingletonClass_withDensity`). -/
lemma nullSingletonClass_jumpDiffusionIncrementLaw (b : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (Λ : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    NullSingletonClass (jumpDiffusionIncrementLaw b σ Λ ν τ) := by
  rw [jumpDiffusionIncrementLaw_eq_withDensity b hσ Λ ν hτ]
  infer_instance

/-- **Without a Gaussian part the log-return law has an atom at `bτ`**: with `σ = 0` and no jump,
which has probability `e^{−Λτ}`, the log-return is `bτ`. Each Gaussian law of the mixture
(`jumpDiffusionIncrementLaw_apply`) is then a point mass (Mathlib's `gaussianReal_zero_var`), and
the one for the jump count `0` sits at `bτ`. -/
lemma ofReal_exp_le_jumpDiffusionIncrementLaw_singleton (b : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) :
    ENNReal.ofReal (rexp (-((Λ * τ : ℝ≥0) : ℝ))) ≤ jumpDiffusionIncrementLaw b 0 Λ ν τ {b * τ} := by
  have hv : (⟨(0 : ℝ) ^ 2, sq_nonneg 0⟩ : ℝ≥0) * τ = 0 := by
    ext
    simp
  rw [jumpDiffusionIncrementLaw_apply b 0 Λ ν τ (measurableSet_singleton _)]
  simp_rw [hv, gaussianReal_zero_var]
  calc ENNReal.ofReal (rexp (-((Λ * τ : ℝ≥0) : ℝ)))
      = ((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) ({0} ×ˢ univ) := by
        rw [Measure.prod_prod, measure_univ, mul_one, poissonMeasure_singleton]
        simp
    _ = ∫⁻ ω, ({0} ×ˢ univ : Set (ℕ × (ℕ → ℝ))).indicator 1 ω
          ∂((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) :=
        (lintegral_indicator_one ((measurableSet_singleton 0).prod MeasurableSet.univ)).symm
    _ ≤ _ := lintegral_mono fun ω ↦ ?_
  -- with no jump the point mass sits at `bτ`
  by_cases hω : ω.1 = 0
  · have h0 : ω ∈ ({0} ×ˢ univ : Set (ℕ × (ℕ → ℝ))) := by simpa using hω
    rw [indicator_of_mem h0, Pi.one_apply, hω, Finset.range_zero, Finset.sum_empty, add_zero]
    exact (Measure.dirac_apply_of_mem (mem_singleton _)).symm.le
  · have h0 : ω ∉ ({0} ×ˢ univ : Set (ℕ × (ℕ → ℝ))) := by simpa using hω
    rw [indicator_of_notMem h0]
    exact zero_le _

/-- The density integrates to `1`, so it is integrable. -/
lemma integrable_jumpDiffusionDensity (b : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    Integrable (jumpDiffusionDensity b σ Λ ν τ) := by
  refine ⟨(continuous_jumpDiffusionDensity b σ Λ ν τ).aestronglyMeasurable, ?_⟩
  have h1 : (volume.withDensity fun y ↦ ENNReal.ofReal (jumpDiffusionDensity b σ Λ ν τ y))
      univ = 1 := by
    rw [← jumpDiffusionIncrementLaw_eq_withDensity b hσ Λ ν hτ, measure_univ]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (jumpDiffusionDensity_nonneg b σ Λ ν τ)), h1]
  exact ENNReal.one_lt_top

/-- **The tail of a law with a density is differentiable where the density is continuous**: for
the law `f(y) dy`, with `f ≥ 0` integrable and continuous at `a`, `x ↦ P(Y > x)` has derivative
`−f(a)` at `a` (the fundamental theorem of calculus, Mathlib's
`intervalIntegral.integral_hasDerivAt_right`). -/
theorem hasDerivAt_measureReal_Ioi_withDensity {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) {a : ℝ} (hfa : ContinuousAt f a) :
    HasDerivAt (fun x ↦ (volume.withDensity fun y ↦ ENNReal.ofReal (f y)).real (Ioi x))
      (-f a) a := by
  -- the integrals of `f`, stated in the notation of the goal
  have h1 (x : ℝ) : (∫ y in Iic x, f y) + ∫ y in Ioi x, f y = ∫ y, f y := by
    rw [← compl_Iic]
    exact integral_add_compl measurableSet_Iic hf
  have h2 (x : ℝ) : (∫ y in Iic x, f y) - ∫ y in Iic a, f y = ∫ y in a..x, f y :=
    intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn
  have hIoi (x : ℝ) : (volume.withDensity fun y ↦ ENNReal.ofReal (f y)).real (Ioi x)
      = ((∫ y, f y) - ∫ y in Iic a, f y) - ∫ y in a..x, f y := by
    have h3 : (volume.withDensity fun y ↦ ENNReal.ofReal (f y)).real (Ioi x)
        = ∫ y in Ioi x, f y := by
      rw [Measure.real, withDensity_apply _ measurableSet_Ioi,
        ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ fun y ↦ hf0 y),
        ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun y _ ↦ hf0 y)]
    linarith [h1 x, h2 x]
  have hii : IntervalIntegrable f volume a a := hf.intervalIntegrable
  have hD : HasDerivAt (fun x ↦ ((∫ y, f y) - ∫ y in Iic a, f y) - ∫ y in a..x, f y) (-f a) a :=
    (intervalIntegral.integral_hasDerivAt_right hii
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hfa).const_sub _
  exact hD.congr_of_eventuallyEq (Eventually.of_forall hIoi)

end MathFin
