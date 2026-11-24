/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonStopping

/-!
# Cross-horizon consistency of the Itô integral on the common filtration

For horizons `s ≤ T`, kernels on `[0, T]` restrict to kernels on `[0, s]`, and the horizon-`s`
integral of the restriction equals the horizon-`T` Itô process at time `s`:

  `I_s(φ|_{(0,s]}) = I^T_s(φ)`.

Consequently the continuous modifications on the two horizons agree on `[0, t]` almost surely.
The proof extends `s`-kernels by zero (an isometry into `L²(trim_T)`) and uses density of the
bounded simple processes, whose elementary integrals do not depend on the horizon.

## Main definitions

* `restrictKernel`
* `extendKernel`
* `extendCLM`

## Main results

* `itoIntegralCLM_T_extend`
* `itoIntegralCLM_T_restrictKernel`
* `itoContinuousMod_restrictKernel`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonHorizon

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcess MathFin.FilteredIto.CommonProcessGeneral
        MathFin.FilteredIto.CommonContinuous
  MathFin.FilteredIto.CommonLocality MathFin.FilteredIto.CommonStopping
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- The predictable band `(0, s] × Ω`. -/
def band0 (s : ℝ≥0) : Set (ℝ≥0 × Ω) := Set.Ioc 0 s ×ˢ Set.univ

lemma measurableSet_band0 (s : ℝ≥0) : MeasurableSet[ℱ.predictable] (band0 (Ω := Ω) s) :=
  measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 s MeasurableSet.univ

lemma trimMeasure_T_restrict_band0 {s T : ℝ≥0} (hsT : s ≤ T) :
    (trimMeasure_T (μ := μ) T ℱ).restrict (band0 s) = trimMeasure_T (μ := μ) s ℱ := by
  rw [trimMeasure_T_eq_restrict T ℱ, trimMeasure_T_eq_restrict s ℱ,
    Measure.restrict_restrict (measurableSet_band0 s)]
  congr 1
  exact Set.inter_eq_left.mpr (Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hsT) subset_rfl)

lemma trimMeasure_T_mono {s T : ℝ≥0} (hsT : s ≤ T) :
    trimMeasure_T (μ := μ) s ℱ ≤ trimMeasure_T (μ := μ) T ℱ := by
  rw [← trimMeasure_T_restrict_band0 hsT]
  exact Measure.restrict_le_self

/-! ### Restriction of kernels -/

/-- Restriction of a horizon-`T` kernel to the horizon `s ≤ T`. -/
def restrictKernel {s T : ℝ≥0} (hsT : s ≤ T) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ) :=
  ((Lp.memLp φ).mono_measure (trimMeasure_T_mono hsT)).toLp ⇑φ

lemma coeFn_restrictKernel {s T : ℝ≥0} (hsT : s ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ⇑(restrictKernel hsT φ) =ᵐ[trimMeasure_T (μ := μ) s ℱ] ⇑φ :=
  MemLp.coeFn_toLp _

lemma restrictKernel_restrictKernel {r s T : ℝ≥0} (hrs : r ≤ s) (hsT : s ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    restrictKernel hrs (restrictKernel hsT φ) = restrictKernel (hrs.trans hsT) φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrictKernel hrs (restrictKernel hsT φ),
    ae_mono (trimMeasure_T_mono hrs) (coeFn_restrictKernel hsT φ),
    coeFn_restrictKernel (hrs.trans hsT) φ] with p h1 h2 h3
  rw [h1, h2, h3]

/-! ### Extension of kernels by zero -/

lemma memLp_extend {s T : ℝ≥0} (hsT : s ≤ T) (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    MemLp ((band0 s).indicator ⇑ψ) 2 (trimMeasure_T (μ := μ) T ℱ) := by
  rw [memLp_indicator_iff_restrict (measurableSet_band0 s).nullMeasurableSet,
        trimMeasure_T_restrict_band0 hsT]
  exact Lp.memLp ψ

/-- Extension by zero of a horizon-`s` kernel to the horizon `T ≥ s`. -/
def extendKernel {s T : ℝ≥0} (hsT : s ≤ T) (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  (memLp_extend hsT ψ).toLp ((band0 s).indicator ⇑ψ)

lemma coeFn_extendKernel {s T : ℝ≥0} (hsT : s ≤ T) (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    ⇑(extendKernel hsT ψ) =ᵐ[trimMeasure_T (μ := μ) T ℱ] (band0 s).indicator ⇑ψ :=
  MemLp.coeFn_toLp _

lemma indicator_ae_congr {s T : ℝ≥0} (hsT : s ≤ T) {f g : ℝ≥0 × Ω → ℝ}
    (h : f =ᵐ[trimMeasure_T (μ := μ) s ℱ] g) :
    (band0 s).indicator f =ᵐ[trimMeasure_T (μ := μ) T ℱ] (band0 s).indicator g := by
  rw [← trimMeasure_T_restrict_band0 hsT] at h
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  exact (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_band0 s)).mp h

lemma norm_extendKernel {s T : ℝ≥0} (hsT : s ≤ T) (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    ‖extendKernel hsT ψ‖ = ‖ψ‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_extendKernel hsT ψ),
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_band0 s).nullMeasurableSet,
          trimMeasure_T_restrict_band0 hsT]

lemma extendKernel_add {s T : ℝ≥0} (hsT : s ≤ T) (ψ ψ' : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    extendKernel hsT (ψ + ψ') = extendKernel hsT ψ + extendKernel hsT ψ' := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendKernel hsT (ψ + ψ'), indicator_ae_congr hsT (Lp.coeFn_add ψ ψ'),
    Lp.coeFn_add (extendKernel hsT ψ) (extendKernel hsT ψ'), coeFn_extendKernel hsT ψ,
    coeFn_extendKernel hsT ψ'] with p h1 h2 h3 h4 h5
  rw [h1, h2, h3, Pi.add_apply, h4, h5]
  by_cases hp : p ∈ band0 s
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp]

lemma extendKernel_smul {s T : ℝ≥0} (hsT : s ≤ T) (c : ℝ)
    (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    extendKernel hsT (c • ψ) = c • extendKernel hsT ψ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendKernel hsT (c • ψ), indicator_ae_congr hsT (Lp.coeFn_smul c ψ),
    Lp.coeFn_smul c (extendKernel hsT ψ), coeFn_extendKernel hsT ψ] with p h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, h4]
  by_cases hp : p ∈ band0 s
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp]

/-- Extension by zero as an isometric continuous linear map. -/
def extendCLM {s T : ℝ≥0} (hsT : s ≤ T) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ) →L[ℝ] Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  LinearMap.mkContinuous
    { toFun := extendKernel hsT
      map_add' := extendKernel_add hsT
      map_smul' := extendKernel_smul hsT }
    1 (fun ψ => by rw [one_mul]; exact (norm_extendKernel hsT ψ).le)

lemma extendCLM_apply {s T : ℝ≥0} (hsT : s ≤ T) (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    extendCLM hsT ψ = extendKernel hsT ψ := rfl

/-! ### Cross-horizon identities -/

/-- The horizon-`s` integral of a kernel equals the horizon-`T` integral of its extension
by zero. -/
theorem itoIntegralCLM_T_extend (hB : BrownianOn ℱ B μ) {s T : ℝ≥0} (hsT : s ≤ T)
    (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) s ℱ)) :
    itoIntegralCLM_T hB s ψ = itoIntegralCLM_T hB T (extendCLM hsT ψ) := by
  refine (simpleAssembly_T_denseRange (μ := μ) s ℱ).induction_on ψ
    (isClosed_eq (itoIntegralCLM_T hB s).continuous
      ((itoIntegralCLM_T hB T).continuous.comp (extendCLM hsT).continuous)) fun V => ?_
  have hVT : V.val ∈ TBoundedSP T ℱ := fun p hp => (V.property p hp).trans hsT
  have hE : extendCLM hsT (simpleAssembly_T (μ := μ) s ℱ V)
      = simpleAssembly_T (μ := μ) T ℱ ⟨V.val, hVT⟩ := by
    refine Lp.ext ?_
    have h1 := coeFn_extendKernel (μ := μ) hsT (simpleAssembly_T (μ := μ) s ℱ V)
    have h2 : ⇑(simpleAssembly_T (μ := μ) s ℱ V) =ᵐ[trimMeasure_T (μ := μ) s ℱ]
        Function.uncurry ⇑V.val := MemLp.coeFn_toLp (memLp_uncurry_trim_T (μ := μ) s ℱ V.val)
    have h3 : ⇑(simpleAssembly_T (μ := μ) T ℱ ⟨V.val, hVT⟩) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
        Function.uncurry ⇑V.val := MemLp.coeFn_toLp (memLp_uncurry_trim_T (μ := μ) T ℱ V.val)
    filter_upwards [h1, indicator_ae_congr hsT h2, h3,
      ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with p e1 e2 e3 e4
    rw [extendCLM_apply, e1, e2, e3]
    by_cases hp : p.1 ≤ s
    · rw [Set.indicator_of_mem (show p ∈ band0 s from ⟨⟨e4.1, hp⟩, Set.mem_univ _⟩)]
    · rw [Set.indicator_of_notMem (fun (h : p ∈ band0 s) => hp h.1.2)]
      exact (uncurry_eq_zero_of_lt V (not_le.mp hp) p.2).symm
  rw [itoIntegralCLM_T_simpleAssembly, hE, itoIntegralCLM_T_simpleAssembly]

/-- **Cross-horizon identity.** The horizon-`s` integral of the restriction of a horizon-`T`
kernel is the horizon-`T` Itô process at time `s`. -/
theorem itoIntegralCLM_T_restrictKernel (hB : BrownianOn ℱ B μ) {s T : ℝ≥0} (hsT : s ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    itoIntegralCLM_T hB s (restrictKernel hsT φ) = itoProcessCLM hB T s hBmeas φ := by
  rw [itoIntegralCLM_T_extend hB hsT, extendCLM_apply]
  have hafter : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), s < p.1 →
      extendKernel hsT (restrictKernel hsT φ) p = 0 := by
    filter_upwards [coeFn_extendKernel hsT (restrictKernel hsT φ)] with p hp hsp
    rw [hp, Set.indicator_of_notMem (fun (h : p ∈ band0 s) => (not_le.mpr hsp) h.1.2)]
  rw [itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after hB T s hsT hBmeas _ hafter]
  have hbefore : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), p.1 ≤ s →
      (φ - extendKernel hsT (restrictKernel hsT φ)) p = 0 := by
    filter_upwards [Lp.coeFn_sub φ (extendKernel hsT (restrictKernel hsT φ)),
      coeFn_extendKernel hsT (restrictKernel hsT φ),
      indicator_ae_congr hsT (coeFn_restrictKernel hsT φ),
      ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with p h1 h2 h3 h4 hps
    have hmem : p ∈ band0 s := ⟨⟨h4.1, hps⟩, Set.mem_univ _⟩
    rw [h1, Pi.sub_apply, h2, h3, Set.indicator_of_mem hmem, sub_self]
  have h0 := itoProcessCLM_eq_zero_of_vanishes_before hB T s hsT hBmeas _ hbefore
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

/-- The continuous modifications on the horizons `t ≤ T` agree on `[0, t]` almost surely. -/
theorem itoContinuousMod_restrictKernel (hB : BrownianOn ℱ B μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) {t T : ℝ≥0} (htT : t ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ∀ s ≤ t, itoContinuousMod t hB.measurable (restrictKernel htT φ) s ω
      = itoContinuousMod T hB.measurable φ s ω := by
  refine ae_forall_eq_of_continuousOn'
    (itoContinuousMod_continuousOn hB t hB.measurable hBc _)
    (by
      filter_upwards [itoContinuousMod_continuousOn hB T hB.measurable hBc φ] with ω hω
      exact hω.mono (Set.Icc_subset_Icc le_rfl htT)) fun s hs => ?_
  have e1 := itoContinuousMod_modification hB t hB.measurable hBc (restrictKernel htT φ) hs
  have e2 := itoContinuousMod_modification hB T hB.measurable hBc φ (hs.trans htT)
  have e3 : itoProcessCLM hB t s hB.measurable (restrictKernel htT φ)
      = itoProcessCLM hB T s hB.measurable φ := by
    rw [← itoIntegralCLM_T_restrictKernel hB hs hB.measurable,
      ← itoIntegralCLM_T_restrictKernel hB (hs.trans htT) hB.measurable,
      restrictKernel_restrictKernel]
  rw [e3] at e1
  exact e1.trans e2.symm

end CommonHorizon
end MathFin.FilteredIto
