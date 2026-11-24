/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.DriftProcessModification

/-!
# Drift Continuous

Adapted from MathFin foundation proofs, copyright (c) 2026 Raphael Coelho.
Apache 2.0; original license is in vendor/LICENSE.mathfin.
Changes: drift continuity and a common-null-set integral identity at all times.

## Main results

* `driftContinuousMod_eq_setIntegral_all`
* `drift_consecutive_norm_le`
* `driftContinuousMod_continuousOn`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology MathFin
open scoped NNReal ENNReal
open MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcess
open MathFin.ItoIntegralProcessGeneral MathFin.ItoIntegralProcessContinuousModification
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

theorem driftContinuousMod_eq_setIntegral_all (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T → driftContinuousMod T hBmeas g t ω
      = ∫ s in Set.Ioc (0 : ℝ≥0) t, ⇑g (s, ω) ∂timeMeasure := by
  set V := (approxSeq T hBmeas g).choose with hVdef
  have hV := (approxSeq T hBmeas g).choose_spec
  have hg_prod : MemLp (⇑g) 2 ((timeMeasureHorizon T).prod μ) := memLp_prod_of_lp T hBmeas g
  have hg_slice : ∀ᵐ ω ∂μ, MemLp (fun s ↦ ⇑g (s, ω)) 2 (timeMeasureHorizon T) := by
    filter_upwards [hg_prod.aestronglyMeasurable.prodMk_right,
      hg_prod.integrable_sq.prod_left_ae] with ω hω1 hω2
    exact (memLp_two_iff_integrable_sq hω1).mpr hω2
  -- the ω-slice energy and its L¹(μ) decay
  set D : ℕ → Ω → ℝ := fun n ω ↦
    ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(V n).val s ω - ⇑g (s, ω)) ^ 2 ∂timeMeasure with hDdef
  have hDnn : ∀ n, 0 ≤ᵐ[μ] D n := fun n ↦ ae_of_all _ fun ω ↦ integral_nonneg fun s ↦ sq_nonneg _
  have hDint : ∀ n, Integrable (D n) μ :=
    fun n ↦ (drift_slice_sq_integrable T hBmeas g (V n)).integral_prod_right
  have hD0 : Tendsto (fun n ↦ ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ ω, D n ω ∂μ) = ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - g‖ ^ 2 :=
      fun n ↦ drift_slice_energy_eq T hBmeas g (V n)
    simp_rw [heq]
    have h0 : Tendsto (fun n ↦ ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - g‖) atTop (𝓝 0) :=
      squeeze_zero (fun n ↦ norm_nonneg _) hV
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    simpa using h0.pow 2
  -- L¹ decay ⟹ convergence in measure ⟹ a.e.-convergent subsequence
  have hDeLp : Tendsto (fun n ↦ eLpNorm (D n - fun _ ↦ (0 : ℝ)) 1 μ) atTop (𝓝 0) := by
    have hrw : ∀ n, eLpNorm (D n - fun _ ↦ (0 : ℝ)) 1 μ = ENNReal.ofReal (∫ ω, D n ω ∂μ) := by
      intro n
      have hsub : (D n - fun _ ↦ (0 : ℝ)) = D n := by funext ω; simp
      have hlint : (∫⁻ ω, ‖D n ω‖ₑ ∂μ) = ∫⁻ ω, ENNReal.ofReal (D n ω) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hDnn n] with ω hω
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
      rw [hsub, eLpNorm_one_eq_lintegral_enorm (hDint n).aestronglyMeasurable, hlint,
        ← ofReal_integral_eq_lintegral_ofReal (hDint n) (hDnn n)]
    rw [tendsto_congr hrw, ← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hD0
  have hDmeasure : TendstoInMeasure μ D atTop (fun _ ↦ (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hDeLp
  obtain ⟨ns, hns_mono, hns_ae⟩ := hDmeasure.exists_seq_tendsto_ae
  -- combine, a.e. ω
  filter_upwards [hns_ae, hg_slice, driftContinuousMod_tendsto T hBmeas g] with ω hωD hωg hωlim
  intro t ht
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hlim_sub : Tendsto (fun k ↦ driftSimpleProcess hBmeas (V (ns k)).val t ω) atTop
      (𝓝 (driftContinuousMod T hBmeas g t ω)) := (hωlim t ht).comp hns_mono.tendsto_atTop
  have hlim_int : Tendsto (fun k ↦ driftSimpleProcess hBmeas (V (ns k)).val t ω) atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) t, ⇑g (s, ω) ∂timeMeasure)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ ?_)
      (g := fun k ↦ Real.sqrt ((T : ℝ) * D (ns k) ω)) ?_
    · -- dist bound via interval Cauchy–Schwarz
      have hVt : MemLp (fun s ↦ ⇑(V (ns k)).val s ω) 2 (timeMeasure.restrict (Set.Ioc 0 t)) :=
        (memLp_slice T hBmeas (V (ns k)).val ω).mono_measure
          (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
      have hgt : MemLp (fun s ↦ ⇑g (s, ω)) 2 (timeMeasure.restrict (Set.Ioc 0 t)) :=
        hωg.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
      have hfT : MemLp (fun s ↦ ⇑(V (ns k)).val s ω - ⇑g (s, ω)) 2
          (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
        (memLp_slice T hBmeas (V (ns k)).val ω).sub hωg
      rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [driftSimpleProcess_eq_setIntegral,
        ← integral_sub (hVt.integrable (by norm_num)) (hgt.integrable (by norm_num))]
      calc (∫ s in Set.Ioc (0 : ℝ≥0) t, (⇑(V (ns k)).val s ω - ⇑g (s, ω)) ∂timeMeasure) ^ 2
          ≤ (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)).real Set.univ
              * ∫ s in Set.Ioc (0 : ℝ≥0) t, (⇑(V (ns k)).val s ω - ⇑g (s, ω)) ^ 2 ∂timeMeasure :=
            sq_integral_le_measureReal_mul (hVt.sub hgt)
        _ ≤ (T : ℝ) * D (ns k) ω := by
            rw [measureReal_def, Measure.restrict_apply_univ, timeMeasure_Ioc,
              ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact t.coe_nonneg),
              NNReal.coe_zero, sub_zero]
            refine mul_le_mul (by exact_mod_cast ht) ?_ (integral_nonneg fun s ↦ sq_nonneg _)
              T.coe_nonneg
            exact setIntegral_mono_set hfT.integrable_sq (ae_of_all _ fun s ↦ sq_nonneg _)
              (Set.Ioc_subset_Ioc_right ht).eventuallyLE
    · rw [← Real.sqrt_zero, ← mul_zero (T : ℝ)]
      exact (Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.mul hωD)
  exact tendsto_nhds_unique hlim_sub hlim_int

lemma drift_consecutive_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : ℕ → TBoundedSP T hBmeas)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) (a : ℕ) :
    ‖driftSimpleProcess hBmeas (V a).val t ω - driftSimpleProcess hBmeas (V (a + 1)).val t ω‖
      ≤ ⨆ j : Set.Iic T, ‖driftSimpleProcess hBmeas (V a - V (a + 1)).val (j : ℝ≥0) ω‖ := by
  have hcoe : ((V a - V (a + 1)).val : SimpleProcess ℝ (natFiltration hBmeas))
      = (V a).val - (V (a + 1)).val := rfl
  rw [show driftSimpleProcess hBmeas (V a).val t ω - driftSimpleProcess hBmeas (V (a + 1)).val t ω
        = driftSimpleProcess hBmeas (V a - V (a + 1)).val t ω from by
      rw [hcoe]; exact (congrFun (driftSimpleProcess_sub hBmeas (V a).val (V (a + 1)).val t)
            ω).symm]
  exact drift_norm_le_iSup_Iic hBmeas (V a - V (a + 1)).val ω ht

/-- Almost every drift path is continuous: the elementary Lebesgue integrals
converge uniformly on the horizon, with a geometric bound on the tail. -/
theorem driftContinuousMod_continuousOn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ driftContinuousMod T hBmeas φ t ω) (Set.Icc 0 T) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [drift_ae_eventually_sup_lt T hBmeas φ V hV,
    driftContinuousMod_tendsto T hBmeas φ] with ω hω htends
  rw [show (Set.Icc 0 T : Set ℝ≥0) = Set.Iic T from by
    ext x; simp only [Set.mem_Icc, Set.mem_Iic, zero_le, true_and]]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have huniform : TendstoUniformlyOn (fun n t ↦ driftSimpleProcess hBmeas (V n).val t ω)
      (fun t ↦ driftContinuousMod T hBmeas φ t ω) atTop (Set.Iic T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htend0 : Tendsto (fun n ↦ 4 * (3 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 4 * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 4
    filter_upwards [eventually_ge_atTop N, htend0.eventually_lt_const hε] with n hn hnε
    intro t ht
    rw [Set.mem_Iic] at ht
    rw [dist_comm]
    -- the uniform bound: dist (fₙ t ω) (X t ω) ≤ 4·(3/4)ⁿ
    have htendsto : Tendsto (fun k ↦ driftSimpleProcess hBmeas (V (k + n)).val t ω) atTop
        (𝓝 (driftContinuousMod T hBmeas φ t ω)) := (htends t ht).comp (tendsto_add_atTop_nat n)
    have hstep : ∀ k, dist (driftSimpleProcess hBmeas (V (k + n)).val t ω)
        (driftSimpleProcess hBmeas (V (k + 1 + n)).val t ω) ≤ (3 / 4 : ℝ) ^ n * (3 / 4 : ℝ) ^ k
              := by
      intro k
      rw [show k + 1 + n = (k + n) + 1 from by ring, dist_eq_norm]
      refine (drift_consecutive_norm_le T hBmeas V ω ht (k + n)).trans ?_
      exact (hN (k + n) (hn.trans (Nat.le_add_left n k))).le.trans
        (le_of_eq (by rw [pow_add]; ring))
    have h0 :=
      dist_le_of_le_geometric_of_tendsto₀ (3 / 4) ((3 / 4 : ℝ) ^ n) (by norm_num) hstep htendsto
    simp only [zero_add] at h0
    refine lt_of_le_of_lt (h0.trans (le_of_eq ?_)) hnε
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 from by norm_num]; ring
  have hcont : ∀ᶠ n in atTop,
      ContinuousOn (fun t ↦ driftSimpleProcess hBmeas (V n).val t ω) (Set.Iic T) :=
    Eventually.of_forall fun n ↦
      (driftSimpleProcess_continuous hBmeas (V n).val ω).continuousOn
  exact huniform.continuousOn hcont.frequently

end MathFin.FilteredIto
