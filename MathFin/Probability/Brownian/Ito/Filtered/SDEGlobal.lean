/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.LipschitzSDE

/-!
# Arbitrary-horizon Lipschitz SDE solutions

The vendored Picard map is a contraction only when `T·L_b + √T·L_σ < 1`.  This file proves the
time-resolved estimate `E_{ΦX-ΦY}(t) ≤ C ∫₀ᵗ E_{X-Y}(s) ds` for the band energy
`E_Z(t) = ∫_{(0,t]×Ω} Z²`, iterates it to `‖Φⁿ X - Φⁿ Y‖² ≤ (CT)ⁿ/n! · ‖X-Y‖²`, and concludes
that some power of the Picard map is a contraction on every finite horizon.  The fixed point is
then realized as a predictable process with a.s. continuous paths satisfying the integral equation
simultaneously for all `t ≤ T`.

## Main definitions

* `bandEnergy`
* `picardRate`

## Main results

* `fixedPoint_pathwise_decomposition`
* `exists_lipschitz_sde_solution`
* `exists_continuous_lipschitz_sde`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin.SDEExistence MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM
open MathFin.ItoIntegralProcess MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification

/-! ### Time integrals over `(0,t]` -/

/-- Integrals against `timeMeasure` over `(0,t]` are ordinary interval integrals on `ℝ`. -/
theorem setIntegral_timeMeasure_Ioc_eq (g : ℝ → ℝ) (t : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ≥0) t, g (s : ℝ) ∂timeMeasure = ∫ x in (0 : ℝ)..(t : ℝ), g x := by
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  have he := measurableEmbedding_nnrealCoe
  have hpre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Set.Ioc (0 : ℝ) (t : ℝ) = Set.Ioc (0 : ℝ≥0) t := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioc, NNReal.coe_pos, NNReal.coe_le_coe]
  rw [← hpre, ← he.setIntegral_map, timeMeasure, he.map_comap,
    Measure.restrict_restrict measurableSet_Ioc]
  have hsub : Set.Ioc (0 : ℝ) (t : ℝ) ⊆ Set.range ((↑) : ℝ≥0 → ℝ) := by
    rintro x ⟨hx, -⟩
    exact ⟨⟨x, hx.le⟩, rfl⟩
  rw [Set.inter_eq_left.mpr hsub]

/-- `∫_{(0,t]} s^n ds = t^{n+1}/(n+1)` for the time measure. -/
theorem setIntegral_timeMeasure_pow (n : ℕ) (t : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ≥0) t, (s : ℝ) ^ n ∂timeMeasure = (t : ℝ) ^ (n + 1) / (n + 1) := by
  rw [setIntegral_timeMeasure_Ioc_eq (fun x => x ^ n) t, integral_pow]
  simp

/-! ### Band energy on the predictable `L²` space -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- `(0,t] × Ω` is predictable. -/
theorem measurableSet_band_pred (hBmeas : ∀ u, Measurable (B u)) (t : ℝ≥0) :
    MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)) :=
  MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 t
    MeasurableSet.univ

/-- The band energy `∫_{(0,t]×Ω} Z²` of an element of the predictable `L²` space. -/
def bandEnergy (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) : ℝ :=
  ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (Z z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas)

section BandEnergy
variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))

theorem integrable_sq_of_Lp {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    (Z : Lp ℝ 2 ν) : Integrable (fun z => (Z z) ^ 2) ν :=
  (Lp.memLp Z).integrable_sq

theorem bandEnergy_nonneg (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    0 ≤ bandEnergy T hBmeas Z t :=
  setIntegral_nonneg (measurableSet_band_pred hBmeas t) (fun _ _ => sq_nonneg _)

theorem bandEnergy_mono (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t t' : ℝ≥0}
    (h : t ≤ t') : bandEnergy T hBmeas Z t ≤ bandEnergy T hBmeas Z t' :=
  setIntegral_mono_set (integrable_sq_of_Lp Z).integrableOn
    (ae_of_all _ fun _ => sq_nonneg _)
    (Set.prod_mono (Set.Ioc_subset_Ioc_right h) le_rfl).eventuallyLE

theorem monotone_bandEnergy (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Monotone (bandEnergy T hBmeas Z) :=
  fun _ _ h => bandEnergy_mono T hBmeas Z h

theorem bandEnergy_le_norm_sq (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    bandEnergy T hBmeas Z t ≤ ‖Z‖ ^ 2 := by
  rw [MathFin.lp_two_norm_sq]
  exact setIntegral_le_integral (integrable_sq_of_Lp Z) (ae_of_all _ fun _ => sq_nonneg _)

theorem bandEnergy_self (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    bandEnergy T hBmeas Z T = ‖Z‖ ^ 2 := by
  rw [MathFin.lp_two_norm_sq, bandEnergy]
  refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
  filter_upwards [ae_fst_mem_Ioc_trimMeasure (μ := μ) T hBmeas] with z hz hzn
  exact absurd (Set.mk_mem_prod hz (Set.mem_univ z.2)) hzn

theorem bandEnergy_add_le (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    bandEnergy T hBmeas (X + Y) t
      ≤ 2 * bandEnergy T hBmeas X t + 2 * bandEnergy T hBmeas Y t := by
  unfold bandEnergy
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · refine setIntegral_mono_ae_restrict (integrable_sq_of_Lp (X + Y)).integrableOn
      (((integrable_sq_of_Lp X).const_mul 2).add
        ((integrable_sq_of_Lp Y).const_mul 2)).integrableOn ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add X Y)] with z hz
    rw [hz, Pi.add_apply]
    nlinarith [sq_nonneg (X z - Y z)]
  · exact ((integrable_sq_of_Lp X).const_mul 2).integrableOn
  · exact ((integrable_sq_of_Lp Y).const_mul 2).integrableOn

theorem bandEnergy_lipComp_sub_le {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    bandEnergy T hBmeas (lipComp T hBmeas f L hf X - lipComp T hBmeas f L hf Y) t
      ≤ (L : ℝ) ^ 2 * bandEnergy T hBmeas (X - Y) t := by
  unfold bandEnergy
  rw [← integral_const_mul]
  refine setIntegral_mono_ae_restrict (integrable_sq_of_Lp _).integrableOn
    ((integrable_sq_of_Lp (X - Y)).const_mul _).integrableOn ?_
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (lipComp T hBmeas f L hf X)
      (lipComp T hBmeas f L hf Y)), ae_restrict_of_ae (Lp.coeFn_sub X Y),
    ae_restrict_of_ae (lipComp_coeFn T hBmeas hf X),
    ae_restrict_of_ae (lipComp_coeFn T hBmeas hf Y)] with z h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4]
  have hl := hf.dist_le_mul (X z) (Y z)
  rw [Real.dist_eq, Real.dist_eq] at hl
  have h0 : 0 ≤ |f (X z) - f (Y z)| := abs_nonneg _
  calc (f (X z) - f (Y z)) ^ 2 = |f (X z) - f (Y z)| ^ 2 := (sq_abs _).symm
    _ ≤ ((L : ℝ) * |X z - Y z|) ^ 2 := pow_le_pow_left₀ h0 hl 2
    _ = (L : ℝ) ^ 2 * (X z - Y z) ^ 2 := by rw [mul_pow, sq_abs]

end BandEnergy

section BandEnergyOperators
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

/-- Restricting the horizon measure to a sub-band. -/
theorem timeMeasure_T_restrict_Ioc {t : ℝ≥0} (htT : t ≤ T) :
    (timeMeasureHorizon T).restrict (Set.Ioc 0 t) = timeMeasure.restrict (Set.Ioc 0 t) := by
  rw [timeMeasureHorizon, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr (Set.Ioc_subset_Ioc_right htT)]

/-- A predictable function square-integrable for `trimMeasure` is square-integrable for the
underlying product measure. -/
theorem memLp_prod_of_trim {f : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    (hmem : MemLp f 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp f 2 ((timeMeasureHorizon T).prod μ) := by
  apply memLp_iff.mpr
  rw [← eLpNorm_trim (natFiltration hBmeas).predictable_le_prod hf]
  exact hmem.eLpNorm_lt_top

/-- Band energy of a predictable representative, computed slice by slice. -/
theorem bandEnergy_eq_slices {Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)}
    {f : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    (hZf : ⇑Z =ᵐ[trimMeasure (μ := μ) T hBmeas] f) {t : ℝ≥0} (htT : t ≤ T) :
    bandEnergy T hBmeas Z t = ∫ s in Set.Ioc 0 t, ∫ ω, (f (s, ω)) ^ 2 ∂μ ∂timeMeasure := by
  have hmem : MemLp f 2 (trimMeasure (μ := μ) T hBmeas) := (Lp.memLp Z).ae_eq hZf
  have hprod := memLp_prod_of_trim T hBmeas hf hmem
  have hint : Integrable (fun z => (f z) ^ 2) ((timeMeasureHorizon T).prod μ) := hprod.integrable_sq
  have h1 : bandEnergy T hBmeas Z t
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (f z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas) :=
    setIntegral_congr_ae (measurableSet_band_pred hBmeas t) (hZf.mono fun z hz _ => by rw [hz])
  have hf2 : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (fun z => (f z) ^ 2) := hf.pow 2
  rw [h1, trimMeasure, ← setIntegral_trim (natFiltration hBmeas).predictable_le_prod hf2
      (measurableSet_band_pred hBmeas t),
    setIntegral_prod _ hint.integrableOn, timeMeasure_T_restrict_Ioc T htT]
  simp only [Measure.restrict_univ]

theorem bandEnergy_itoProcessAssembled
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t : ℝ≥0} (htT : t ≤ T) :
    bandEnergy T hBmeas (itoProcessAssembled hB T hBmeas hBcont φ) t
      = ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas φ s ∂timeMeasure := by
  have hcoe : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont φ).coeFn_toLp
  rw [bandEnergy_eq_slices T hBmeas (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ)
    hcoe htT]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  have hsT : s ≤ T := hs.2.trans htT
  rw [bandEnergy, ← itoProcessCLM_norm_sq hB hsT hBmeas φ, MathFin.lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ hsT] with ω hω
  simp only [Function.uncurry]
  rw [hω]

/-- Slice Cauchy–Schwarz for the drift. -/
theorem integral_driftSlice_sq_le
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {s : ℝ≥0} (hsT : s ≤ T) :
    ∫ ω, (driftContinuousMod T hBmeas φ s ω) ^ 2 ∂μ ≤ (T : ℝ) * bandEnergy T hBmeas φ s := by
  have hφm : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] (⇑φ) :=
    Lp.stronglyMeasurable φ
  have hprod := memLp_prod_of_trim T hBmeas hφm (Lp.memLp φ)
  have hint : Integrable (fun z => (φ z) ^ 2) ((timeMeasureHorizon T).prod μ) := hprod.integrable_sq
  -- slices are square integrable for a.e. ω
  have hslice : ∀ᵐ ω ∂μ, Integrable (fun u => (φ (u, ω)) ^ 2) (timeMeasureHorizon T) :=
    hint.prod_left_ae
  have hmeas_slice : ∀ ω, StronglyMeasurable (fun u => φ (u, ω)) := fun ω =>
    (hφm.mono (natFiltration hBmeas).predictable_le_prod).comp_measurable
      measurable_prodMk_right
  -- the pathwise bound
  have hpt : ∀ᵐ ω ∂μ, (driftContinuousMod T hBmeas φ s ω) ^ 2
      ≤ (T : ℝ) * ∫ u in Set.Ioc 0 s, (φ (u, ω)) ^ 2 ∂timeMeasure := by
    filter_upwards [driftContinuousMod_eq_setIntegral T hBmeas φ hsT, hslice] with ω hω hsl
    rw [hω]
    have hmemω : MemLp (fun u => φ (u, ω)) 2 (timeMeasure.restrict (Set.Ioc 0 s)) := by
      rw [memLp_two_iff_integrable_sq (hmeas_slice ω).aestronglyMeasurable]
      rw [← timeMeasure_T_restrict_Ioc T hsT]
      exact hsl.restrict
    letI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc 0 s)) :=
      ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
    have hCS := MathFin.sq_integral_le_measureReal_mul hmemω
    rw [Measure.restrict_apply_univ, timeMeasure_Ioc,
      ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact s.coe_nonneg),
      NNReal.coe_zero, sub_zero] at hCS
    refine hCS.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsT)
      (integral_nonneg fun _ => sq_nonneg _))
  -- integrate the bound in ω
  have hswap : bandEnergy T hBmeas φ s = ∫ ω, ∫ u in Set.Ioc 0 s, (φ (u, ω)) ^ 2 ∂timeMeasure ∂μ
        := by
    rw [bandEnergy_eq_slices T hBmeas hφm (Filter.EventuallyEq.refl _ _) hsT]
    have hint' : Integrable (Function.uncurry fun (u : ℝ≥0) (ω : Ω) => (φ (u, ω)) ^ 2)
        ((timeMeasure.restrict (Set.Ioc 0 s)).prod μ) := by
      have hm : ((timeMeasureHorizon T).restrict (Set.Ioc 0 s)).prod μ
          = ((timeMeasureHorizon T).prod μ).restrict (Set.Ioc 0 s ×ˢ Set.univ) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [← timeMeasure_T_restrict_Ioc T hsT, hm]
      exact hint.restrict
    exact integral_integral_swap hint'
  rw [hswap, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) ?_ hpt
  refine Integrable.const_mul ?_ _
  have hint'' : Integrable (fun z : ℝ≥0 × Ω => (φ z) ^ 2)
      ((timeMeasure.restrict (Set.Ioc 0 s)).prod μ) := by
    have hm : ((timeMeasureHorizon T).restrict (Set.Ioc 0 s)).prod μ
        = ((timeMeasureHorizon T).prod μ).restrict (Set.Ioc 0 s ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [← timeMeasure_T_restrict_Ioc T hsT, hm]
    exact hint.restrict
  exact Integrable.integral_prod_right hint''

theorem bandEnergy_driftProcessAssembled
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t : ℝ≥0} (htT : t ≤ T) :
    bandEnergy T hBmeas (driftProcessAssembled (μ := μ) T hBmeas φ) t
      ≤ (T : ℝ) * ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas φ s ∂timeMeasure := by
  rw [bandEnergy_eq_slices T hBmeas (driftContinuousMod_isStronglyPredictable T hBmeas φ)
    (driftProcessAssembled_coeFn T hBmeas φ) htT, ← integral_const_mul]
  have hfin : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun s hs => ?_)
  · -- integrability of the slice energies: bounded by `T * ‖φ‖²`
    refine Measure.integrableOn_of_bounded (M := (T : ℝ) * ‖φ‖ ^ 2) ?_ ?_ ?_
    · rw [timeMeasure_Ioc]; exact ENNReal.ofReal_ne_top
    · have hpred := driftContinuousMod_isStronglyPredictable T hBmeas φ
      exact ((hpred.mono (natFiltration hBmeas).predictable_le_prod).pow
            2).integral_prod_right'.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsT : s ≤ T := hs.2.trans htT
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact (integral_driftSlice_sq_le T hBmeas φ hsT).trans
        (mul_le_mul_of_nonneg_left (bandEnergy_le_norm_sq T hBmeas φ s) T.coe_nonneg)
  · refine Measure.integrableOn_of_bounded (M := (T : ℝ) * ‖φ‖ ^ 2) ?_ ?_ ?_
    · rw [timeMeasure_Ioc]; exact ENNReal.ofReal_ne_top
    · exact ((monotone_bandEnergy T hBmeas φ).measurable.const_mul _).aestronglyMeasurable
    · filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg T.coe_nonneg (bandEnergy_nonneg T hBmeas φ
            s))]
      exact mul_le_mul_of_nonneg_left (bandEnergy_le_norm_sq T hBmeas φ s) T.coe_nonneg
  · exact integral_driftSlice_sq_le T hBmeas φ (hs.2.trans htT)

end BandEnergyOperators

/-! ### Iterated Picard estimate and the global fixed point -/

/-- The rate in the time-resolved Picard estimate. -/
def picardRate (T Lb Lσ : ℝ≥0) : ℝ := 2 * (T : ℝ) * (Lb : ℝ) ^ 2 + 2 * (Lσ : ℝ) ^ 2

theorem picardRate_nonneg (T Lb Lσ : ℝ≥0) : 0 ≤ picardRate T Lb Lσ := by
  unfold picardRate; positivity

section GlobalPicard
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
  {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
  (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))

theorem integrableOn_bandEnergy (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    IntegrableOn (bandEnergy T hBmeas Z) (Set.Ioc 0 t) timeMeasure := by
  refine Measure.integrableOn_of_bounded (M := ‖Z‖ ^ 2) ?_
    (monotone_bandEnergy T hBmeas Z).measurable.aestronglyMeasurable ?_
  · rw [timeMeasure_Ioc]; exact ENNReal.ofReal_ne_top
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (bandEnergy_nonneg T hBmeas Z s)]
    exact bandEnergy_le_norm_sq T hBmeas Z s

theorem picardMap_sub_eq (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    picardMap hB T hBmeas hBcont hb hσ η_E X - picardMap hB T hBmeas hBcont hb hσ η_E Y
      = driftProcessAssembled (μ := μ) T hBmeas
          (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)
        + itoProcessAssembled hB T hBmeas hBcont
          (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y) := by
  have hdrift : driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)
      - driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb Y)
      = driftProcessAssembled (μ := μ) T hBmeas
          (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y) :=
    (map_sub (driftProcessAssembled (μ := μ) T hBmeas) _ _).symm
  have hito : itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)
      - itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ Y)
      = itoProcessAssembled hB T hBmeas hBcont
          (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y) :=
    (itoProcessAssembled_sub hB T hBmeas hBcont _ _).symm
  rw [picardMap, picardMap, ← hdrift, ← hito]; abel

/-- **Time-resolved Picard estimate**: `E_{ΦX-ΦY}(t) ≤ C·∫₀ᵗ E_{X-Y}(s) ds`. -/
theorem bandEnergy_picardMap_sub_le (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t : ℝ≥0} (htT : t ≤ T) :
    bandEnergy T hBmeas (picardMap hB T hBmeas hBcont hb hσ η_E X
        - picardMap hB T hBmeas hBcont hb hσ η_E Y) t
      ≤ picardRate T Lb Lσ * ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas (X - Y) s ∂timeMeasure := by
  rw [picardMap_sub_eq hB T hBmeas hBcont hb hσ η_E X Y]
  set ΔG := lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y
  set ΔH := lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y
  set J := ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas (X - Y) s ∂timeMeasure
  have h1 := bandEnergy_add_le T hBmeas (driftProcessAssembled (μ := μ) T hBmeas ΔG)
    (itoProcessAssembled hB T hBmeas hBcont ΔH) t
  have h2 := bandEnergy_driftProcessAssembled T hBmeas ΔG htT
  have h3 := bandEnergy_itoProcessAssembled hB T hBmeas hBcont ΔH htT
  have hG : ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas ΔG s ∂timeMeasure ≤ (Lb : ℝ) ^ 2 * J := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_bandEnergy T hBmeas ΔG t)
      ((integrableOn_bandEnergy T hBmeas (X - Y) t).const_mul _) measurableSet_Ioc
      (fun s _ => bandEnergy_lipComp_sub_le T hBmeas hb X Y s)
  have hH : ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas ΔH s ∂timeMeasure ≤ (Lσ : ℝ) ^ 2 * J := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_bandEnergy T hBmeas ΔH t)
      ((integrableOn_bandEnergy T hBmeas (X - Y) t).const_mul _) measurableSet_Ioc
      (fun s _ => bandEnergy_lipComp_sub_le T hBmeas hσ X Y s)
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  calc _ ≤ 2 * bandEnergy T hBmeas (driftProcessAssembled (μ := μ) T hBmeas ΔG) t
          + 2 * bandEnergy T hBmeas (itoProcessAssembled hB T hBmeas hBcont ΔH) t := h1
    _ ≤ 2 * ((T : ℝ) * ((Lb : ℝ) ^ 2 * J)) + 2 * ((Lσ : ℝ) ^ 2 * J) := by
        rw [h3]
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left hG hT0)
    _ = picardRate T Lb Lσ * J := by unfold picardRate; ring

/-- **Iterated Picard estimate**: `E_{Φⁿ X - Φⁿ Y}(t) ≤ ‖X-Y‖² (Ct)ⁿ/n!`. -/
theorem bandEnergy_iterate_sub_le (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (n : ℕ)
    {t : ℝ≥0} (htT : t ≤ T) :
    bandEnergy T hBmeas ((picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
        - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y) t
      ≤ ‖X - Y‖ ^ 2 * (picardRate T Lb Lσ * t) ^ n / (n.factorial : ℝ) := by
  set Φ := picardMap hB T hBmeas hBcont hb hσ η_E
  set C := picardRate T Lb Lσ
  have hC : 0 ≤ C := picardRate_nonneg T Lb Lσ
  induction n generalizing t with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      mul_one]
    exact bandEnergy_le_norm_sq T hBmeas (X - Y) t
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine (bandEnergy_picardMap_sub_le hB T hBmeas hBcont hb hσ η_E _ _ htT).trans ?_
    set M := ‖X - Y‖ ^ 2
    have hM : 0 ≤ M := sq_nonneg _
    have hpoly_int : IntegrableOn (fun s : ℝ≥0 => M * (C * s) ^ n / (n.factorial : ℝ))
        (Set.Ioc 0 t) timeMeasure := by
      refine Measure.integrableOn_of_bounded (M := M * (C * t) ^ n / (n.factorial : ℝ)) ?_ ?_ ?_
      · rw [timeMeasure_Ioc]; exact ENNReal.ofReal_ne_top
      · exact (by fun_prop : Continuous fun s : ℝ≥0 => M * (C * s) ^ n / (n.factorial : ℝ)
          ).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
        have hst : (s : ℝ) ≤ t := by exact_mod_cast hs.2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr
    have hint : ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas (Φ^[n] X - Φ^[n] Y) s ∂timeMeasure
        ≤ ∫ s in Set.Ioc 0 t, M * (C * s) ^ n / (n.factorial : ℝ) ∂timeMeasure :=
      setIntegral_mono_on (integrableOn_bandEnergy T hBmeas _ t) hpoly_int measurableSet_Ioc
        (fun s hs => ih (hs.2.trans htT))
    have hcomp : ∫ s in Set.Ioc 0 t, M * (C * s) ^ n / (n.factorial : ℝ) ∂timeMeasure
        = M * C ^ n / (n.factorial : ℝ) * ((t : ℝ) ^ (n + 1) / (n + 1)) := by
      have hfun : (fun s : ℝ≥0 => M * (C * s) ^ n / (n.factorial : ℝ))
          = fun s : ℝ≥0 => (M * C ^ n / (n.factorial : ℝ)) * (s : ℝ) ^ n := by
        funext s; rw [mul_pow]; ring
      rw [hfun, integral_const_mul, setIntegral_timeMeasure_pow]
    calc C * ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas (Φ^[n] X - Φ^[n] Y) s ∂timeMeasure
        ≤ C * (M * C ^ n / (n.factorial : ℝ) * ((t : ℝ) ^ (n + 1) / (n + 1))) :=
          mul_le_mul_of_nonneg_left (hint.trans hcomp.le) hC
      _ = M * (C * t) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, mul_pow]
          have hf : (n.factorial : ℝ) ≠ 0 := by positivity
          field_simp
          push_cast
          ring

theorem norm_iterate_sub_le (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (n : ℕ) :
    ‖(picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
        - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y‖
      ≤ Real.sqrt ((picardRate T Lb Lσ * T) ^ n / (n.factorial : ℝ)) * ‖X - Y‖ := by
  have h := bandEnergy_iterate_sub_le hB T hBmeas hBcont hb hσ η_E X Y n le_rfl
  rw [bandEnergy_self] at h
  have hq : 0 ≤ (picardRate T Lb Lσ * T) ^ n / (n.factorial : ℝ) := by
    have := picardRate_nonneg T Lb Lσ; positivity
  calc _ = Real.sqrt (‖(picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
        - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg
              _)).symm
    _ ≤ Real.sqrt (‖X - Y‖ ^ 2 * ((picardRate T Lb Lσ * T) ^ n / (n.factorial : ℝ))) :=
        Real.sqrt_le_sqrt (by rw [mul_div_assoc] at h; exact h)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]

/-- Some power of the Picard map is a contraction, on every finite horizon. -/
theorem exists_contractingWith_iterate :
    ∃ (n : ℕ) (K : ℝ≥0), ContractingWith K (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] := by
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop (picardRate T Lb Lσ * T)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
  have hq : 0 ≤ (picardRate T Lb Lσ * T) ^ n / (n.factorial : ℝ) := by
    have := picardRate_nonneg T Lb Lσ; positivity
  refine ⟨n, Real.toNNReal (Real.sqrt ((picardRate T Lb Lσ * T) ^ n / (n.factorial : ℝ))), ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (Real.sqrt_nonneg _), NNReal.coe_one,
      Real.sqrt_lt' one_pos, one_pow]
    exact hn
  · refine LipschitzWith.of_dist_le_mul fun X Y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact norm_iterate_sub_le hB T hBmeas hBcont hb hσ η_E X Y n

/-- **Global existence and uniqueness** of the Picard fixed point (no smallness condition). -/
theorem picardMap_exists_unique_fixedPoint_global :
    ∃! X, picardMap hB T hBmeas hBcont hb hσ η_E X = X := by
  obtain ⟨n, K, hK⟩ := exists_contractingWith_iterate hB T hBmeas hBcont hb hσ η_E
  refine ⟨hK.fixedPoint _, hK.isFixedPt_fixedPoint_iterate, fun Y hY => ?_⟩
  exact hK.fixedPoint_unique (Function.IsFixedPt.iterate hY n)

/-- Pathwise decomposition of an arbitrary Picard fixed point. -/
theorem fixedPoint_pathwise_decomposition {Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)}
    (hfix : picardMap hB T hBmeas hBcont hb hσ η_E Z = Z) :
    ⇑Z =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => ⇑η_E z
        + Function.uncurry (driftContinuousMod T hBmeas (lipComp T hBmeas b Lb hb Z)) z
        + Function.uncurry (itoContinuousMod T hBmeas (lipComp T hBmeas σ Lσ hσ Z)) z := by
  have hX : Z = η_E + driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb Z)
      + itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ Z) := hfix.symm
  have hdrift := driftProcessAssembled_coeFn (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb Z)
  have hito : ⇑(itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ Z))
      =ᵐ[trimMeasure (μ := μ) T hBmeas]
        Function.uncurry (itoContinuousMod T hBmeas (lipComp T hBmeas σ Lσ hσ Z)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ Z)).coeFn_toLp
  filter_upwards [Lp.coeFn_add
      (η_E + driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb Z))
      (itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ Z)),
    Lp.coeFn_add η_E (driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb Z)),
    hdrift, hito] with z h1 h2 hd hi
  conv_lhs => rw [hX]
  simp only [h1, h2, hd, hi, Pi.add_apply]

end GlobalPicard

/-! ### The arbitrary-horizon Lipschitz SDE theorem -/

/-- **Strong solution of a Lipschitz SDE on an arbitrary finite horizon.**  The process is
`X = x₀ + ∫ G + ∫ H dB` with `G = b∘X`, `H = σ∘X` in the predictable `L²` space, a.s. continuous
on `[0,T]`, and the integral equation holds on one full-measure set for all `t ≤ T`. -/
theorem exists_lipschitz_sde_solution
    (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0}
    (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ) (x₀ : ℝ) :
    ∃ (X : ℝ≥0 → Ω → ℝ) (G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)),
      (∀ t ω, X t ω = x₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω) ∧
      IsStronglyPredictable (natFiltration hBmeas) X ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) ∧
      MemLp (Function.uncurry X) 2 (trimMeasure (μ := μ) T hBmeas) ∧
      (⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => b (X z.1 z.2)) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => σ (X z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
        X t ω = x₀ + (∫ s in Set.Ioc 0 t, b (X s ω) ∂timeMeasure)
          + itoContinuousMod T hBmeas H t ω) := by
  let η := Lp.const 2 (trimMeasure (μ := μ) T hBmeas) x₀
  obtain ⟨Z, hZfix, -⟩ := picardMap_exists_unique_fixedPoint_global hB T hBmeas hBcont hb hσ η
  let G := lipComp T hBmeas b Lb hb Z
  let H := lipComp T hBmeas σ Lσ hσ Z
  let X : ℝ≥0 → Ω → ℝ := fun t ω =>
    x₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω
  have hZ : ⇑Z =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry X := by
    filter_upwards [fixedPoint_pathwise_decomposition hB T hBmeas hBcont hb hσ η hZfix,
      Lp.coeFn_const (p := 2) (μ := trimMeasure (μ := μ) T hBmeas) (c := x₀)]
      with z hz hη
    have hη' : η z = x₀ := hη
    rw [hη'] at hz
    exact hz
  have hG : ⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => b (X z.1 z.2) := by
    filter_upwards [lipComp_coeFn T hBmeas hb Z, hZ] with z hg hz
    exact hg.trans (congrArg b hz)
  have hH : ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => σ (X z.1 z.2) := by
    filter_upwards [lipComp_coeFn T hBmeas hσ Z, hZ] with z hh hz
    exact hh.trans (congrArg σ hz)
  refine ⟨X, G, H, fun t ω => rfl, ?_, ?_, (Lp.memLp Z).ae_eq hZ, hG, hH, ?_⟩
  · exact (stronglyMeasurable_const.add (driftContinuousMod_isStronglyPredictable T hBmeas G)).add
      (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont H)
  · filter_upwards [driftContinuousMod_continuousOn T hBmeas G,
      itoContinuousMod_continuousOn hB T hBmeas hBcont H] with ω hd hi
    exact (continuousOn_const.add hd).add hi
  · have hGprod : ⇑G =ᵐ[(timeMeasureHorizon T).prod μ] fun z => b (X z.1 z.2) :=
      ae_eq_of_ae_eq_trim hG
    have hGswap : ∀ᵐ z ∂μ.prod (timeMeasureHorizon T), G (z.2, z.1) = b (X z.2 z.1) :=
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hGprod)
    filter_upwards [Measure.ae_ae_of_ae_prod hGswap,
      driftContinuousMod_eq_setIntegral_all T hBmeas G] with ω hcoeff hdrift
    intro t ht
    have hi : (∫ s in Set.Ioc 0 t, G (s, ω) ∂timeMeasure) =
        ∫ s in Set.Ioc 0 t, b (X s ω) ∂timeMeasure := by
      apply integral_congr_ae
      exact hcoeff.filter_mono (ae_mono
        (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl))
    change x₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω = _
    rw [hdrift t ht, hi]

/-- The small-horizon theorem of `LipschitzSDE` with the smallness hypothesis removed. -/
theorem exists_continuous_lipschitz_sde
    (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0}
    (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ) (x₀ : ℝ) :
    ∃ (X : ℝ≥0 → Ω → ℝ) (H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)),
      IsStronglyPredictable (natFiltration hBmeas) X ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) ∧
      MemLp (Function.uncurry X) 2 (trimMeasure (μ := μ) T hBmeas) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => σ (X z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
        X t ω = x₀ + (∫ s in Set.Ioc 0 t, b (X s ω) ∂timeMeasure)
          + itoContinuousMod T hBmeas H t ω) := by
  obtain ⟨X, -, H, -, h1, h2, h3, -, h5, h6⟩ :=
    exists_lipschitz_sde_solution hB T hBmeas hBcont hb hσ x₀
  exact ⟨X, H, h1, h2, h3, h5, h6⟩

end MathFin.FilteredIto
