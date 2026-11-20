/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.MartingaleRepresentation

/-!
# The martingale representation theorem for Brownian motion: solution

The declarations of `Palomar.MartingaleRepresentation.Challenge`, repeated verbatim, discharged
against the library. The Challenge's objects are the library's up to unfolding:
`brownianFiltration` is `MathFin.ItoIntegralL2.natFiltration`, `integrandMeasure` is
`MathFin.ItoIntegralCLM.trimMeasure`. The library's Itô integral `itoIntegralCLM` is an Itô
integral in the Challenge's sense (`isItoIntegral_itoIntegralCLM`, by `itoSimple_iocSPHorizon`),
and it is the only one (`eq_itoIntegralCLM`, by `ext_rectangleIndicators`: the rectangles span a
dense subspace). The isometry is then `itoIntegralCLM_norm` and the representation is
`MathFin.exists_itoIntegral_representation`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianRepresentation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem predictable_le_prod (𝓕 : Filtration ℝ≥0 mΩ) :
    𝓕.predictable ≤ Prod.instMeasurableSpace :=
  𝓕.predictable_le_prod

noncomputable def brownianFiltration (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 mΩ :=
  Filtration.natural B fun t ↦ (hB t).stronglyMeasurable

noncomputable def integrandMeasure (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) (T : ℝ≥0) :=
  (((Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Set.Ioc 0 T)).prod μ).trim
    (predictable_le_prod (brownianFiltration B hB))

def IsItoIntegral (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (I : Lp ℝ 2 (integrandMeasure μ B hB T) →L[ℝ] Lp ℝ 2 μ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → t ≤ T → ∀ F : Set Ω, MeasurableSet[brownianFiltration B hB s] F →
    ∀ φ : Lp ℝ 2 (integrandMeasure μ B hB T),
      ⇑φ =ᵐ[integrandMeasure μ B hB T] (Set.Ioc s t ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) →
        ⇑(I φ) =ᵐ[μ] F.indicator fun ω ↦ B t ω - B s ω

variable {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

open MathFin.ItoIntegralCLM in
/-- The library's Itô integral is an Itô integral in the Challenge's sense: an integrand equal to
the indicator of `(s, t] × F` is the embedded simple process `iocSPHorizon`, whose integral is
`𝟙_F (B_t − B_s)`. -/
theorem isItoIntegral_itoIntegralCLM [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    IsItoIntegral μ B hBmeas T (itoIntegralCLM hB T hBmeas) := by
  intro s t hst htT F hF φ hφ
  obtain rfl : φ = simpleAssemblyHorizon (μ := μ) T hBmeas (iocSPHorizon hBmeas hst htT hF) :=
    Lp.ext (hφ.trans (ae_simpleAssemblyHorizon_iocSPHorizon (μ := μ) hBmeas hst htT hF).symm)
  rw [itoIntegralCLM_simpleAssemblyHorizon, ← itoSimple_iocSPHorizon hBmeas hst htT hF]
  exact MemLp.coeFn_toLp _

open MathFin.ItoIntegralCLM in
/-- An Itô integral in the Challenge's sense is the library's: the two agree on the rectangles,
which span a dense subspace. -/
theorem eq_itoIntegralCLM [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0}
    {I : Lp ℝ 2 (integrandMeasure μ B hBmeas T) →L[ℝ] Lp ℝ 2 μ}
    (hI : IsItoIntegral μ B hBmeas T I) : I = itoIntegralCLM hB T hBmeas := by
  refine ext_rectangleIndicators ?_
  rintro _ ⟨s, t, hst, htT, F, hF, rfl⟩
  have hφ := ae_simpleAssemblyHorizon_iocSPHorizon (μ := μ) hBmeas hst htT hF
  exact Lp.ext ((hI s t hst htT F hF _ hφ).trans
    (isItoIntegral_itoIntegralCLM hB hBmeas T s t hst htT F hF _ hφ).symm)

theorem existsUnique_isItoIntegral (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (T : ℝ≥0) : ∃! I, IsItoIntegral μ B hBmeas T I :=
  have := hB.isGaussianProcess.isProbabilityMeasure
  ⟨_, isItoIntegral_itoIntegralCLM hB hBmeas T, fun _ hI ↦ eq_itoIntegralCLM hB hBmeas hI⟩

theorem norm_apply_of_isItoIntegral (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0}
    {I : Lp ℝ 2 (integrandMeasure μ B hBmeas T) →L[ℝ] Lp ℝ 2 μ}
    (hI : IsItoIntegral μ B hBmeas T I) (φ : Lp ℝ 2 (integrandMeasure μ B hBmeas T)) :
    ‖I φ‖ = ‖φ‖ := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  obtain rfl := eq_itoIntegralCLM hB hBmeas hI
  exact MathFin.ItoIntegralCLM.itoIntegralCLM_norm hB T hBmeas φ

theorem existsUnique_itoIntegral_representation (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {T : ℝ≥0}
    {I : Lp ℝ 2 (integrandMeasure μ B hBmeas T) →L[ℝ] Lp ℝ 2 μ}
    (hI : IsItoIntegral μ B hBmeas T I) (H : Lp ℝ 2 μ)
    (hH : AEStronglyMeasurable[brownianFiltration B hBmeas T] H μ) :
    ∃! φ, ⇑H =ᵐ[μ] fun ω ↦ (∫ ω', H ω' ∂μ) + I φ ω := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  obtain rfl := eq_itoIntegralCLM hB hBmeas hI
  exact MathFin.exists_itoIntegral_representation hB hBmeas hBcont T H hH

end BrownianRepresentation
