/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonItoFormula
public import MathFin.Probability.Brownian.Ito.Filtered.CommonHorizon

/-!
# Itô's formula at all times, at random times and for stopped processes

The terminal-time formula `CommonIto.ito_formula` is transported to every `t ≤ T` through the
cross-horizon identity of `CommonHorizon`: an Itô process on `[0, T]` restricts to an Itô
process on `[0, t]` with restricted kernels, and the horizon-`t` integrals of the restricted
kernels are the horizon-`T` continuous Itô processes at time `t`. Continuity in `t` then gives
the formula simultaneously for all `t ≤ T`, hence at random times and for stopped processes.

## Main results

* `ito_formula_all`
* `ito_formula_random_time`
* `ito_formula_stopped`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonIto

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcess MathFin.FilteredIto.CommonProcessGeneral
        MathFin.FilteredIto.CommonContinuous
  MathFin.FilteredIto.CommonLocality MathFin.FilteredIto.CommonStopping
        MathFin.FilteredIto.CommonRiemann MathFin.FilteredIto.CommonCovariation
  MathFin.FilteredIto.CommonHorizon
open MathFin (unifPart)
open scoped NNReal ENNReal

local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

/-- Drift primitives of continuous paths are continuous. -/
lemma continuousOn_primitive {T : ℝ≥0} {g : ℝ≥0 → ℝ} (hg : ContinuousOn g (Set.Icc 0 T)) :
    ContinuousOn (fun t ↦ ∫ s in Set.Ioc 0 t, g s ∂leb) (Set.Icc 0 T) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hgI := integrableOn_of_continuousOn hg
  have hlip : ∀ x ∈ Set.Icc (0 : ℝ≥0) T, ∀ y ∈ Set.Icc (0 : ℝ≥0) T, x ≤ y →
      |∫ s in Set.Ioc 0 y, g s ∂leb - ∫ s in Set.Ioc 0 x, g s ∂leb| ≤ C * ((y : ℝ) - x) := by
    intro x _ y hy hxy
    rw [setIntegral_Ioc_sub hgI hxy hy.2, ← Real.norm_eq_abs]
    have hfin : leb (Set.Ioc x y) < ∞ := by
      rw [MathFin.ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top
    refine (norm_setIntegral_le_of_norm_le_const (C := C) hfin fun s hs => ?_).trans
      (le_of_eq ?_)
    · exact hC s ⟨zero_le, hs.2.trans hy.2⟩
    · rw [measureReal_def, MathFin.ItoIntegralL2.timeMeasure_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hxy))]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le⟩)
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε / (C + 1), by positivity, fun y hy hxy => ?_⟩
  rw [Real.dist_eq]
  rw [NNReal.dist_eq] at hxy
  have hlt : C * |(y : ℝ) - x| < ε := by
    calc C * |(y : ℝ) - x| ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hxy.le hC0
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  rcases le_total x y with h | h
  · have := hlip x hx y hy h
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))] at hlt
    linarith
  · have := hlip y hy x hx h
    rw [abs_sub_comm] at this
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))] at hlt
    linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ}

lemma contProcess_mono {t T : ℝ≥0} (htT : t ≤ T) {h : ℝ≥0 → Ω → ℝ}
    (hh : ContProcess ℱ μ T h) : ContProcess ℱ μ t h where
  adapted := hh.adapted
  pred := hh.pred
  cont := by
    filter_upwards [hh.cont] with ω hω
    exact hω.mono (Set.Icc_subset_Icc le_rfl htT)

variable [IsProbabilityMeasure μ]

lemma restrictKernel_mulKernel {s T : ℝ≥0} (hsT : s ≤ T) {w : ℝ≥0 → Ω → ℝ}
    (hwP : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ w p.1 p.2)) {C : ℝ}
    (hC : ∀ t ω, |w t ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    restrictKernel hsT (mulKernel T hwP hC φ) = mulKernel s hwP hC (restrictKernel hsT φ) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrictKernel hsT (mulKernel T hwP hC φ),
    ae_mono (trimMeasure_T_mono hsT) (coeFn_mulKernel T hwP hC φ),
    coeFn_mulKernel s hwP hC (restrictKernel hsT φ), coeFn_restrictKernel hsT φ]
    with p h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- An Itô process on `[0, T]` restricts to an Itô process on `[0, t]`. -/
lemma ItoProc.restrict {ι : Type*} [Countable ι] {hP : IndependentPair ℱ B Z μ} {T : ℝ≥0}
    {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {t : ℝ≥0} (htT : t ≤ T) :
    ItoProc hP t Y y a b c (fun i ↦ restrictKernel htT (φB i))
      (fun i ↦ restrictKernel htT (φZ i)) where
  proc i := contProcess_mono htT (hY.proc i)
  drift := by
    filter_upwards [hY.drift] with ω hω i
    exact (hω i).mono (Set.Icc_subset_Icc le_rfl htT)
  diffB i := contProcess_mono htT (hY.diffB i)
  diffZ i := contProcess_mono htT (hY.diffZ i)
  kerB i := (coeFn_restrictKernel htT (φB i)).trans (ae_mono (trimMeasure_T_mono htT) (hY.kerB i))
  kerZ i := (coeFn_restrictKernel htT (φZ i)).trans (ae_mono (trimMeasure_T_mono htT) (hY.kerZ i))
  eq := by
    have h1 := ae_all_iff.mpr fun i => itoContinuousMod_restrictKernel hP.left hBc htT (φB i)
    have h2 := ae_all_iff.mpr fun i => itoContinuousMod_restrictKernel hP.right hZc htT (φZ i)
    filter_upwards [hY.eq, h1, h2] with ω hω e1 e2 i s hs
    rw [hω i s (hs.trans htT), e1 i s hs, e2 i s hs]

/-- **Itô's formula at a fixed time `t ≤ T`**, with the stochastic integrals written as the
horizon-`T` continuous Itô processes at time `t`. -/
theorem ito_formula_at {ι : Type*} [Fintype ι] [DecidableEq ι] (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂) {t : ℝ≥0} (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, f (fun i ↦ Y i t ω) = f y
      + ∫ s in Set.Ioc 0 t, (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, itoContinuousMod T hP.left.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φB i)) t ω
      + ∑ i, itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i)) t ω := by
  have hY' := hY.restrict hBc hZc htT
  have key := ito_formula hP hBc hZc hY' hf
  have hB : ∀ i, ∀ᵐ ω ∂μ, itoIntegralCLM_T hP.left t (mulKernel t
      (goodProcess_pd hY'.proc hf i).pred (goodProcess_pd hY'.proc hf i).bdd
        (restrictKernel htT (φB i))) ω
      = itoContinuousMod T hP.left.measurable (mulKernel T (goodProcess_pd hY.proc hf i).pred
            (goodProcess_pd hY.proc hf i).bdd (φB i)) t ω := by
    intro i
    rw [← restrictKernel_mulKernel htT,
      itoIntegralCLM_T_restrictKernel hP.left htT hP.left.measurable]
    filter_upwards [itoContinuousMod_modification hP.left T hP.left.measurable hBc
      (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd (φB i))
            htT] with ω hω
    exact hω.symm
  have hZ : ∀ i, ∀ᵐ ω ∂μ, itoIntegralCLM_T hP.right t (mulKernel t
      (goodProcess_pd hY'.proc hf i).pred (goodProcess_pd hY'.proc hf i).bdd
        (restrictKernel htT (φZ i))) ω
      = itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hY.proc hf i).pred
            (goodProcess_pd hY.proc hf i).bdd (φZ i)) t ω := by
    intro i
    rw [← restrictKernel_mulKernel htT,
      itoIntegralCLM_T_restrictKernel hP.right htT hP.right.measurable]
    filter_upwards [itoContinuousMod_modification hP.right T hP.right.measurable hZc
      (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i))
            htT] with ω hω
    exact hω.symm
  filter_upwards [key, ae_all_iff.mpr hB, ae_all_iff.mpr hZ] with ω hω e1 e2
  rw [hω, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun i _ => e2 i]

/-- **Itô's formula, simultaneously for all `t ≤ T`.** -/
theorem ito_formula_all {ι : Type*} [Fintype ι] [DecidableEq ι] (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, f (fun i ↦ Y i t ω) = f y
      + ∫ s in Set.Ioc 0 t, (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, itoContinuousMod T hP.left.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φB i)) t ω
      + ∑ i, itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i)) t ω := by
  refine ae_forall_eq_of_continuousOn' (X := fun t ω ↦ f (fun i ↦ Y i t ω))
    (Y := fun t ω ↦ f y + ∫ s in Set.Ioc 0 t, (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, itoContinuousMod T hP.left.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φB i)) t ω
      + ∑ i, itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i)) t ω) ?_ ?_
    fun t ht => ito_formula_at hP hBc hZc hY hf ht
  · have h := ae_all_iff.mpr fun i => (hY.proc i).cont
    filter_upwards [h] with ω hω
    exact hf.contDiff.continuous.comp_continuousOn (continuousOn_pi.mpr hω)
  · have hYc := ae_all_iff.mpr fun i => (hY.proc i).cont
    have hbc := ae_all_iff.mpr fun i => (hY.diffB i).cont
    have hcc := ae_all_iff.mpr fun i => (hY.diffZ i).cont
    have hMB := ae_all_iff.mpr fun i => itoContinuousMod_continuousOn hP.left T
      hP.left.measurable hBc (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd
            hY.proc hf i).bdd (φB i))
    have hMZ := ae_all_iff.mpr fun i => itoContinuousMod_continuousOn hP.right T
      hP.right.measurable hZc (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd
            hY.proc hf i).bdd (φZ i))
    filter_upwards [hY.drift, hYc, hbc, hcc, hMB, hMZ] with ω ha hY' hb hc hB' hZ'
    have hYv : ContinuousOn (fun t l ↦ Y l t ω) (Set.Icc 0 T) := continuousOn_pi.mpr hY'
    have hg : ContinuousOn (fun s ↦ (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω))) (Set.Icc 0 T) :=
      (continuousOn_finsetSum _ fun i _ =>
        ((hf.continuous_pd i).comp_continuousOn hYv).mul (ha i)).add
      (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun k _ =>
          ((hf.continuous_pd2 i k).comp_continuousOn hYv).mul
            (((hb i).mul (hb k)).add ((hc i).mul (hc k)))))
    exact ((continuousOn_const.add (continuousOn_primitive hg)).add
      (continuousOn_finsetSum _ fun i _ => hB' i)).add (continuousOn_finsetSum _ fun i _ => hZ' i)

/-- **Itô's formula at a random time** `τ ≤ T` (no stopping property is needed). -/
theorem ito_formula_random_time {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂) {τ : Ω → ℝ≥0} (hτ : ∀ ω, τ ω ≤ T) :
    ∀ᵐ ω ∂μ, f (fun i ↦ Y i (τ ω) ω) = f y
      + ∫ s in Set.Ioc 0 (τ ω), (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, itoContinuousMod T hP.left.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φB i)) (τ ω) ω
      + ∑ i, itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hY.proc hf
            i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i)) (τ ω) ω := by
  filter_upwards [ito_formula_all hP hBc hZc hY hf] with ω hω
  exact hω (τ ω) (hτ ω)

/-- **Itô's formula for the stopped process** `Y_{t ∧ τ}`, `τ` a stopping time: the
stochastic part is the continuous Itô process of the stopped kernels `𝟙_{s ≤ τ}·∂ᵢf(Y)·bⁱ`
(resp. `cⁱ`), simultaneously for all `t ≤ T`. -/
theorem ito_formula_stopped {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, f (fun i ↦ Y i (min t (τ ω)) ω) = f y
      + ∫ s in Set.Ioc 0 (min t (τ ω)), (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, itoContinuousMod T hP.left.measurable (stopKernel T hτ (mulKernel T (goodProcess_pd
            hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd (φB i))) t ω
      + ∑ i, itoContinuousMod T hP.right.measurable (stopKernel T hτ (mulKernel T
            (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i))) t ω := by
  have hB := ae_all_iff.mpr fun i => itoContinuousMod_stopKernel hP.left T hP.left.measurable
    hBc hτ (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd (φB i))
  have hZ := ae_all_iff.mpr fun i => itoContinuousMod_stopKernel hP.right T hP.right.measurable
    hZc hτ (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd (φZ i))
  filter_upwards [ito_formula_all hP hBc hZc hY hf, hB, hZ] with ω hω e1 e2 t ht
  rw [hω (min t (τ ω)) ((min_le_left _ _).trans ht),
    Finset.sum_congr rfl fun i _ => e1 i t ht, Finset.sum_congr rfl fun i _ => e2 i t ht]

end CommonIto
end MathFin.FilteredIto
