/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessMartingale
public import MathFin.Probability.Brownian.Ito.Filtered.CommonIntegral

/-!
# Common Process General

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-18.

## Main definitions

* `itoProcessLM`
* `itoProcessCLM`

## Main results

* `itoProcessCLM_norm_terminal`
* `integral_itoIntegralCLM_T`
* `itoIntegralProcessGen_l2_continuous`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal
namespace MathFin.FilteredIto
namespace CommonProcessGeneral

open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise
open CommonL2 CommonPredictable CommonIntegral CommonProcess
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hB : BrownianOn ℱ B μ)

include hB

theorem itoSimpleProcessLp_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ ℱ) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    ‖itoSimpleProcessLp hB hBmeas V t‖ ≤ ‖simpleProcessL2T (μ := μ) T ℱ V‖ := by
  have : IsProbabilityMeasure μ := hB.law.isGaussianProcess.isProbabilityMeasure

  have hnorm_eq : ‖simpleProcessL2T (μ := μ) T ℱ V‖ = ‖itoSimpleLp hB hBmeas V‖ :=
    (assembly_isometry_T hB T ⟨V, hVT⟩).symm
  rw [hnorm_eq]

  have hT'eq : itoSimpleProcess hBmeas V (max t T) = itoSimple hBmeas V :=
    itoSimpleProcess_eq_itoSimple hBmeas V fun p hp ↦ (hVT p hp).trans (le_max_right t T)
  have hcond : (μ[fun ω ↦ itoSimpleProcess hBmeas V (max t T) ω | ℱ t])
      =ᵐ[μ] fun ω ↦ itoSimpleProcess hBmeas V t ω :=
    (itoSimpleProcess_isMartingale hB hBmeas V).2 t (max t T) (le_max_left t T)
  simp only [hT'eq] at hcond

  simp only [itoSimpleProcessLp, itoSimpleLp, Lp.norm_toLp]
  refine ENNReal.toReal_mono (memLp_itoSimple hB hBmeas V).eLpNorm_lt_top.ne ?_
  calc eLpNorm (itoSimpleProcess hBmeas V t) 2 μ
      = eLpNorm (μ[itoSimple hBmeas V | ℱ t]) 2 μ :=
        (eLpNorm_congr_ae hcond).symm
    _ ≤ eLpNorm (itoSimple hBmeas V) 2 μ := eLpNorm_condExp_le_eLpNorm _ (by simp)

/-- Linear map evaluating a horizon-bounded simple integral at the specified time. -/
noncomputable def itoProcessLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    TBoundedSP T ℱ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleProcessLp hB hBmeas V.val t
  map_add' V W := by
    show itoSimpleProcessLp hB hBmeas ((V + W).val) t = _
    rw [Submodule.coe_add, itoSimpleProcessLp, itoSimpleProcessLp, itoSimpleProcessLp,
        ← MemLp.toLp_add (memLp_itoSimpleProcess hB hBmeas V.val t)
          (memLp_itoSimpleProcess hB hBmeas W.val t)]
    congr 1
    exact itoSimpleProcess_add hBmeas V.val W.val t
  map_smul' c V := by
    show itoSimpleProcessLp hB hBmeas ((c • V).val) t = _
    rw [Submodule.coe_smul, itoSimpleProcessLp, itoSimpleProcessLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimpleProcess hB hBmeas V.val t)]
    congr 1
    exact itoSimpleProcess_smul hBmeas c V.val t

/-- Continuous linear evaluation of the Itô integral in the supplied filtration. -/
noncomputable def itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) →L[ℝ] Lp ℝ 2 μ :=
  (itoProcessLM hB T t hBmeas).extendOfNorm (simpleAssemblyT (μ := μ) T ℱ)

theorem itoProcessCLM_simpleAssembly_T (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP T ℱ) :
    itoProcessCLM hB T t hBmeas (simpleAssemblyT (μ := μ) T ℱ V)
      = itoSimpleProcessLp hB hBmeas V.val t := by
  rw [itoProcessCLM, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange (μ := μ) T ℱ)
    ⟨1, fun W ↦ by rw [one_mul]; exact itoSimpleProcessLp_norm_le hB T t hBmeas W.val W.property⟩]
  rfl

@[simp] theorem itoProcessCLM_zero_time (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    itoProcessCLM hB T 0 hBmeas φ = 0 := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T ℱ)
    (itoProcessCLM hB T 0 hBmeas).continuous
    (continuous_const (y := (0 : Lp ℝ 2 μ))) (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T, itoSimpleProcessLp]
  refine Lp.ext (((memLp_itoSimpleProcess hB hBmeas V.val 0).coeFn_toLp).trans ?_)
  rw [itoSimpleProcess_zero_time]
  exact (Lp.coeFn_zero ℝ 2 μ).symm

omit [IsProbabilityMeasure μ] in

theorem condExp_itoSimple_eq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ ℱ) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    μ[itoSimple hBmeas V | ℱ t]
      =ᵐ[μ] fun ω ↦ itoSimpleProcess hBmeas V t ω := by
  have hT'eq : itoSimpleProcess hBmeas V (max t T) = itoSimple hBmeas V :=
    itoSimpleProcess_eq_itoSimple hBmeas V fun p hp ↦ (hVT p hp).trans (le_max_right t T)
  simpa only [hT'eq] using (itoSimpleProcess_isMartingale hB hBmeas V).2 t (max t T)
        (le_max_left t T)

theorem itoProcessCLM_eq_condExpL2 (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    itoProcessCLM hB T t hBmeas φ
      = (condExpL2 ℝ ℝ (ℱ.le t)
          (itoIntegralCLMT hB T φ) : Lp ℝ 2 μ) := by
  have hcont_R : Continuous fun ψ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) ↦
      (condExpL2 ℝ ℝ (ℱ.le t)
        (itoIntegralCLMT hB T ψ) : Lp ℝ 2 μ) :=
    (continuous_subtype_val.comp (condExpL2 ℝ ℝ (ℱ.le t)).continuous).comp
      (itoIntegralCLMT hB T).continuous
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T ℱ)
    (itoProcessCLM hB T t hBmeas).continuous hcont_R (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply]
  rw [itoProcessCLM_simpleAssembly_T, itoIntegralCLM_T_simpleAssembly]
  refine Lp.ext ?_
  simp only [itoSimpleProcessLp, itoSimpleLp]
  filter_upwards [(memLp_itoSimpleProcess hB hBmeas V.val t).coeFn_toLp,
    (memLp_itoSimple hB hBmeas V.val).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le t),
    condExp_itoSimple_eq hB T t hBmeas V.val V.property] with ω hω1 hω2 hω3
  rw [hω1, ← hω3, hω2]

theorem itoProcessCLM_aeStronglyMeasurable (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    AEStronglyMeasurable[ℱ t]
      (itoProcessCLM hB T t hBmeas φ : Ω → ℝ) μ := by
  rw [itoProcessCLM_eq_condExpL2]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ (ℱ.le t) (itoIntegralCLMT hB T φ)).2

theorem itoIntegralProcessGen_isMartingale (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessCLM hB T j hBmeas φ : Ω → ℝ) | ℱ i]
      =ᵐ[μ] (itoProcessCLM hB T i hBmeas φ : Ω → ℝ) := by

  have hbridge : ∀ k : ℝ≥0,
      ((condExpL2 ℝ ℝ (ℱ.le k)
          (itoIntegralCLMT hB T φ) : Lp ℝ 2 μ) : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralCLMT hB T φ : Ω → ℝ) | ℱ k] := by
    intro k
    have h := (Lp.memLp (itoIntegralCLMT hB T φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (ℱ.le k)
    rwa [Lp.toLp_coeFn] at h
  rw [itoProcessCLM_eq_condExpL2, itoProcessCLM_eq_condExpL2]
  calc μ[((condExpL2 ℝ ℝ (ℱ.le j)
            (itoIntegralCLMT hB T φ) : Lp ℝ 2 μ) : Ω → ℝ) | ℱ i]
      =ᵐ[μ] μ[μ[(itoIntegralCLMT hB T φ : Ω → ℝ) | ℱ j]
              | ℱ i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralCLMT hB T φ : Ω → ℝ) | ℱ i] :=
        condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)
    _ =ᵐ[μ] ((condExpL2 ℝ ℝ (ℱ.le i)
              (itoIntegralCLMT hB T φ) : Lp ℝ 2 μ) : Ω → ℝ) := (hbridge i).symm

theorem itoProcessCLM_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ‖itoProcessCLM hB T t hBmeas φ‖ ≤ ‖φ‖ := by
  have hae : (itoProcessCLM hB T t hBmeas φ : Ω → ℝ)
      =ᵐ[μ] μ[(itoIntegralCLMT hB T φ : Ω → ℝ) | ℱ t] := by
    rw [itoProcessCLM_eq_condExpL2]
    have h := (Lp.memLp (itoIntegralCLMT hB T φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (ℱ.le t)
    rwa [Lp.toLp_coeFn] at h
  rw [Lp.norm_def, ← itoIntegralCLM_T_norm hB T φ, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top (itoIntegralCLMT hB T φ)) ?_
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_condExp_le_eLpNorm _ (by simp)

theorem itoProcessCLM_terminal_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    itoProcessCLM hB T T hBmeas φ = itoIntegralCLMT hB T φ :=
  congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T ℱ)
    (itoProcessCLM hB T T hBmeas).continuous (itoIntegralCLMT hB T).continuous
    (funext fun V ↦ by
      simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T,
        itoIntegralCLM_T_simpleAssembly, itoSimpleProcessLp, itoSimpleLp,
        itoSimpleProcess_eq_itoSimple hBmeas V.val (fun p hp ↦ V.property p hp)])) φ

theorem itoProcessCLM_norm_terminal (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ‖itoProcessCLM hB T T hBmeas φ‖ = ‖φ‖ := by
  rw [itoProcessCLM_terminal_eq hB T hBmeas φ, itoIntegralCLM_T_norm hB T φ]

theorem integral_itoIntegralCLM_T (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∫ ω, itoIntegralCLMT hB T φ ω ∂μ = 0 := by
  have hmart := itoIntegralProcessGen_isMartingale hB T hBmeas φ (i := 0) (j := T) zero_le
  rw [itoProcessCLM_zero_time hB T hBmeas φ] at hmart
  rw [← itoProcessCLM_terminal_eq hB T hBmeas φ,
    ← integral_condExp (ℱ.le 0), integral_congr_ae hmart]
  simp

theorem itoIntegralProcessGen_l2_continuous (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    Continuous (fun t ↦ itoProcessCLM hB T t hBmeas φ) := by

  obtain ⟨g, hg_range, hg_lim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssembly_T_denseRange (μ := μ) T ℱ).closure_range.ge (Set.mem_univ φ))
  choose V hV using hg_range

  have hcont_n : ∀ n, Continuous (fun t ↦ itoProcessCLM hB T t hBmeas (g n)) := fun n ↦ by
    simp only [← hV n, itoProcessCLM_simpleAssembly_T]
    exact itoSimpleProcessLp_l2_continuous hB hBmeas (V n).val

  have huniform : TendstoUniformly (fun n t ↦ itoProcessCLM hB T t hBmeas (g n))
      (fun t ↦ itoProcessCLM hB T t hBmeas φ) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hnorm_lim : Filter.Tendsto (fun n ↦ ‖φ - g n‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := φ)).sub hg_lim
      simpa using this.norm
    filter_upwards [hnorm_lim.eventually (eventually_lt_nhds hε)] with n hn t
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (itoProcessCLM_norm_le hB T t hBmeas (φ - g n)) hn
  exact huniform.continuous (Filter.Eventually.of_forall hcont_n).frequently

end CommonProcessGeneral
end MathFin.FilteredIto
