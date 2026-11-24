/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.ItoFormulaL2

/-!
# Itô's formula at every intermediate time, and in expectation form

`ito_formula_L2` is a statement at the terminal time `T`.  Applied to the band-restricted
coefficients `𝟙_{(0,t]}·β`, `𝟙_{(0,t]}·γ` (`bandRestrict`), whose Itô process is the original one
stopped at the deterministic time `t`, it gives the formula at every `t ≤ T`:

`f(X_t) - f(x₀) = M_t + ∫₀ᵗ (f'(X_s) β_s + ½ f''(X_s) γ_s²) ds`,  `M = ∫ f'(X) γ dB`,

and, since the martingale `M_t` has mean zero, the expectation form
`E[f(X_t) - f(x₀)] = E ∫₀ᵗ (f'(X_s) β_s + ½ f''(X_s) γ_s²) ds`.

## Main results

* `ito_formula_L2_at`
* `integrable_comp_at`
* `ito_formula_L2_integral`

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
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification MathFin.ItoFormulaAdapted
open MathFin.AdaptedDrift MathFin.ItoIntegralAgainstMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

section Tools
variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))

omit [IsProbabilityMeasure μ] in
/-- Processes with a.s. continuous paths on `[0,T]` that agree a.s. at each time of `[0,T]` agree
a.s. at all times of `[0,T]` simultaneously. -/
theorem ae_forall_eq_of_continuousOn {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (h : ∀ t ≤ T, X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = Y t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  have hD : ∀ᵐ ω ∂μ, ∀ d ∈ D, X d.1 ω = Y d.1 ω := by
    rw [ae_ball_iff hDc]
    intro d _
    exact h d.1 d.2.2
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω
  intro t ht
  have hcX : Continuous fun s : Set.Icc (0 : ℝ≥0) T => X s.1 ω :=
    hXω.comp_continuous continuous_subtype_val (fun s => s.2)
  have hcY : Continuous fun s : Set.Icc (0 : ℝ≥0) T => Y s.1 ω :=
    hYω.comp_continuous continuous_subtype_val (fun s => s.2)
  have heq := Continuous.ext_on hDd hcX hcY (fun d hd => hDω d hd)
  exact congrFun heq ⟨t, zero_le, ht⟩

/-- A trim-a.e. property holds, for a.e. `ω`, at a.e. time. -/
theorem ae_ae_of_ae_trim {p : ℝ≥0 × Ω → Prop}
    (h : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), p z) :
    ∀ᵐ ω ∂μ, ∀ᵐ u ∂(timeMeasureHorizon T), p (u, ω) := by
  have h1 : ∀ᵐ z ∂((timeMeasureHorizon T).prod μ), p z :=
    ae_of_ae_trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod h
  have h2 : ∀ᵐ z ∂μ.prod (timeMeasureHorizon T), p (z.2, z.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae h1
  exact Measure.ae_ae_of_ae_prod h2

omit [IsProbabilityMeasure μ] in
/-- Under the trimmed product measure, time is a.e. strictly positive. -/
theorem ae_pos_trim : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), 0 < z.1 := by
  have hmeas : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      {z : ℝ≥0 × Ω | 0 < z.1} := by
    have hU : {z : ℝ≥0 × Ω | 0 < z.1}
        = ⋃ n : ℕ, Set.Ioc 0 (n : ℝ≥0) ×ˢ (Set.univ : Set Ω) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_Ioc, Set.mem_univ,
        and_true]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_ge z.1
        exact ⟨n, hz, hn⟩
      · rintro ⟨n, hz, -⟩
        exact hz
    rw [hU]
    exact MeasurableSet.iUnion fun n => measurableSet_band_pred hBmeas (n : ℝ≥0)
  have hprod : ∀ᵐ z ∂((timeMeasureHorizon T).prod μ), 0 < z.1 := by
    have h0 : ∀ᵐ t ∂(timeMeasureHorizon T), 0 < t := by
      rw [timeMeasureHorizon]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.1
    exact Measure.quasiMeasurePreserving_fst.ae h0
  rw [ae_iff] at hprod ⊢
  calc trimMeasure (μ := μ) T hBmeas {a | ¬0 < a.1}
      = ((timeMeasureHorizon T).prod μ) {a | ¬0 < a.1} := trim_measurableSet_eq _ hmeas.compl
    _ = 0 := hprod

/-- Slicewise form of `coeFn_bandRestrict`. -/
theorem ae_ae_bandRestrict (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ᵐ u ∂(timeMeasureHorizon T),
      bandRestrict (μ := μ) T 0 t hBmeas φ (u, ω)
        = (Set.Ioc 0 t).indicator (fun _ => (1 : ℝ)) u * φ (u, ω) :=
  ae_ae_of_ae_trim T hBmeas (coeFn_bandRestrict (μ := μ) T 0 t (zero_le) hBmeas φ)

/-- The drift of the band-restricted integrand is the original drift stopped at `t`. -/
theorem driftContinuousMod_bandRestrict (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t : ℝ≥0} :
    ∀ᵐ ω ∂μ, ∀ s ≤ T,
      driftContinuousMod T hBmeas (bandRestrict (μ := μ) T 0 t hBmeas φ) s ω
        = driftContinuousMod T hBmeas φ (min s t) ω := by
  filter_upwards [driftContinuousMod_eq_setIntegral_all T hBmeas
      (bandRestrict (μ := μ) T 0 t hBmeas φ),
    driftContinuousMod_eq_setIntegral_all T hBmeas φ, ae_ae_bandRestrict T hBmeas φ t]
    with ω h1 h2 h3 s hs
  rw [h1 s hs, h2 (min s t) ((min_le_left s t).trans hs)]
  have h3' : ∀ᵐ u ∂timeMeasure.restrict (Set.Ioc 0 s),
      bandRestrict (μ := μ) T 0 t hBmeas φ (u, ω)
        = (Set.Ioc 0 t).indicator (fun u => φ (u, ω)) u := by
    rw [← timeMeasure_T_restrict_Ioc T hs]
    refine ae_restrict_of_ae ?_
    filter_upwards [h3] with u hu
    rw [hu]
    by_cases hut : u ∈ Set.Ioc 0 t
    · rw [Set.indicator_of_mem hut, Set.indicator_of_mem hut, one_mul]
    · rw [Set.indicator_of_notMem hut, Set.indicator_of_notMem hut, zero_mul]
  rw [integral_congr_ae h3', setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc,
    max_self]

end Tools

section Band
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

/-- The Itô process of the band-restricted integrand is the original one stopped at `t`
(as `L²` classes, at each time). -/
theorem itoProcessCLM_bandRestrict (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t s : ℝ≥0} (htT : t ≤ T) (hsT : s ≤ T) :
    itoProcessCLM hB T s hBmeas (bandRestrict (μ := μ) T 0 t hBmeas φ)
      = itoProcessCLM hB T (min s t) hBmeas φ := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    have h0 : itoProcessCLM hB T s hBmeas (bandRestrict (μ := μ) T 0 t hBmeas φ - φ) = 0 := by
      refine itoProcessCLM_eq_zero_of_vanishes_before (hB := hB) T s hsT hBmeas _ ?_
      filter_upwards [Lp.coeFn_sub (bandRestrict (μ := μ) T 0 t hBmeas φ) φ,
        coeFn_bandRestrict (μ := μ) T 0 t (zero_le) hBmeas φ, ae_pos_trim T hBmeas]
        with p h1 h2 hpos hps
      rw [h1, Pi.sub_apply, h2,
        Set.indicator_of_mem (show p.1 ∈ Set.Ioc 0 t from ⟨hpos, hps.trans hst⟩), one_mul,
        sub_self]
    rwa [map_sub, sub_eq_zero] at h0
  · rw [min_eq_right hts]
    have hv : ∀ᵐ p ∂(trimMeasure (μ := μ) T hBmeas), s < p.1 →
        bandRestrict (μ := μ) T 0 t hBmeas φ p = 0 := by
      filter_upwards [coeFn_bandRestrict (μ := μ) T 0 t (zero_le) hBmeas φ] with p h2 hp
      rw [h2, Set.indicator_of_notMem
        (fun (hm : p.1 ∈ Set.Ioc 0 t) => absurd hm.2 (not_le.mpr (lt_of_le_of_lt hts hp))),
              zero_mul]
    rw [← itoIntegralCLM_eq_itoProcessCLM_of_vanishes_after (hB := hB) T s hsT hBmeas _ hv,
      itoIntegralCLM_bandRestrict (hB := hB) T hBmeas φ (zero_le) htT,
      itoProcessCLM_zero_time, sub_zero]

/-- The mean of the Itô process vanishes at every time. -/
theorem integral_itoProcessCLM (Γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t : ℝ≥0}
    (htT : t ≤ T) : ∫ ω, itoProcessCLM hB T t hBmeas Γ ω ∂μ = 0 := by
  have h := itoIntegralCLM_bandRestrict (hB := hB) T hBmeas Γ (zero_le) htT
  rw [itoProcessCLM_zero_time, sub_zero] at h
  rw [← h]
  exact integral_itoIntegralCLM (hB := hB) T hBmeas _

include hB hBcont in
/-- Pathwise form: the continuous Itô modification of the band-restricted integrand is the
original continuous modification stopped at `t`. -/
theorem itoContinuousMod_bandRestrict (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t : ℝ≥0} (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, ∀ s ≤ T,
      itoContinuousMod T hBmeas (bandRestrict (μ := μ) T 0 t hBmeas φ) s ω
        = itoContinuousMod T hBmeas φ (min s t) ω := by
  refine ae_forall_eq_of_continuousOn T
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _) ?_ ?_
  · filter_upwards [itoContinuousMod_continuousOn hB T hBmeas hBcont φ] with ω hω
    exact hω.comp (continuous_id.min continuous_const).continuousOn
      (fun s hs => ⟨zero_le, (min_le_left s t).trans hs.2⟩)
  · intro s hs
    have hst : min s t ≤ T := (min_le_left s t).trans hs
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont
        (bandRestrict (μ := μ) T 0 t hBmeas φ) hs,
      itoContinuousMod_modification hB T hBmeas hBcont φ hst] with ω h1 h2
    rw [h1, h2, itoProcessCLM_bandRestrict hB T hBmeas φ htT hs]

include hB hBcont in
/-- The Itô process with band-restricted coefficients is the original one stopped at `t`. -/
theorem l2ItoProcess_bandRestrict (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t : ℝ≥0} (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, ∀ s ≤ T,
      l2ItoProcess T hBmeas x₀ (bandRestrict (μ := μ) T 0 t hBmeas β)
          (bandRestrict (μ := μ) T 0 t hBmeas γ) s ω
        = l2ItoProcess T hBmeas x₀ β γ (min s t) ω := by
  filter_upwards [driftContinuousMod_bandRestrict T hBmeas β (t := t),
    itoContinuousMod_bandRestrict hB T hBmeas hBcont γ htT] with ω h1 h2 s hs
  simp only [l2ItoProcess]
  rw [h1 s hs, h2 s hs]

end Band

section Formula
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

include hB hBcont in
/-- **Itô's formula at an intermediate time** for predictable `L²` integrands. -/
theorem ito_formula_L2_at (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {C₁ C₂ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) (hf2 : ∀ x, |f'' x| ≤ C₂)
    {t : ℝ≥0} (htT : t ≤ T) :
    ∃ Γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      (⇑Γ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z =>
        f' (l2ItoProcess T hBmeas x₀ β γ z.1 z.2) * γ z) ∧
      (fun ω => f (l2ItoProcess T hBmeas x₀ β γ t ω) - f x₀) =ᵐ[μ] fun ω =>
        itoProcessCLM hB T t hBmeas Γ ω + ∫ s in Set.Ioc 0 t,
          (f' (l2ItoProcess T hBmeas x₀ β γ s ω) * β (s, ω)
            + 1 / 2 * (f'' (l2ItoProcess T hBmeas x₀ β γ s ω) * γ (s, ω) ^ 2)) ∂timeMeasure := by
  set X := l2ItoProcess T hBmeas x₀ β γ with hXdef
  set βt := bandRestrict (μ := μ) T 0 t hBmeas β with hβt
  set γt := bandRestrict (μ := μ) T 0 t hBmeas γ with hγt
  set Y := l2ItoProcess T hBmeas x₀ βt γt with hYdef
  have hf'c : Continuous f' := Differentiable.continuous fun x => (hf' x).differentiableAt
  have hXpred : IsStronglyPredictable (natFiltration hBmeas) X :=
    l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀ β γ
  have hYpred : IsStronglyPredictable (natFiltration hBmeas) Y :=
    l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀ βt γt
  have hΓmem := memLp_comp_mul_coeFn T hBmeas hXpred hf'c hf1 γ
  set Γ := hΓmem.toLp _ with hΓdef
  refine ⟨Γ, hΓmem.coeFn_toLp, ?_⟩
  obtain ⟨Γt, hΓt, hito⟩ := ito_formula_L2 (μ := μ) hB T hBmeas hBcont x₀ βt γt hf hf' hf''
    hf1 hf2
  rw [← hYdef] at hΓt hito
  have hYX : ∀ᵐ ω ∂μ, ∀ s ≤ T, Y s ω = X (min s t) ω :=
    l2ItoProcess_bandRestrict hB T hBmeas hBcont x₀ β γ htT
  -- on the band `(0,t]`, `Y = X` trim-a.e.
  have hYX_trim : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas),
      z ∈ Set.Ioc 0 t ×ˢ (Set.univ : Set Ω) → Y z.1 z.2 = X z.1 z.2 := by
    have hG : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        ((Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).piecewise (fun z => X z.1 z.2)
          (fun z => Y z.1 z.2)) :=
      StronglyMeasurable.piecewise (measurableSet_band_pred hBmeas t) hXpred hYpred
    have hpath : ∀ᵐ ω ∂μ, ∀ s ≤ T, (fun z : ℝ≥0 × Ω => Y z.1 z.2) (s, ω)
        = (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).piecewise (fun z => X z.1 z.2)
          (fun z => Y z.1 z.2) (s, ω) := by
      filter_upwards [hYX] with ω h s hs
      by_cases hm : (s, ω) ∈ Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)
      · rw [Set.piecewise_eq_of_mem _ _ _ hm]
        simp only
        rw [h s hs, min_eq_left hm.1.2]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hm]
    filter_upwards [ae_eq_trim_of_pathwise T hBmeas hYpred hG hpath] with z hz hm
    have := hz
    rw [Set.piecewise_eq_of_mem _ _ _ hm] at this
    exact this
  -- the stochastic integrand of the stopped formula is the band restriction of `Γ`
  have hΓt_eq : Γt = bandRestrict (μ := μ) T 0 t hBmeas Γ := by
    refine Lp.ext ?_
    filter_upwards [hΓt, coeFn_bandRestrict (μ := μ) T 0 t (zero_le) hBmeas γ,
      coeFn_bandRestrict (μ := μ) T 0 t (zero_le) hBmeas Γ, hΓmem.coeFn_toLp, hYX_trim]
      with z h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4]
    by_cases hz : z.1 ∈ Set.Ioc 0 t
    · rw [Set.indicator_of_mem hz, one_mul, one_mul, h5 ⟨hz, trivial⟩]
    · rw [Set.indicator_of_notMem hz, zero_mul, zero_mul, mul_zero]
  have hIt : itoIntegralCLM hB T hBmeas Γt = itoProcessCLM hB T t hBmeas Γ := by
    rw [hΓt_eq, itoIntegralCLM_bandRestrict (hB := hB) T hBmeas Γ (zero_le) htT,
      itoProcessCLM_zero_time, sub_zero]
  -- the time integral of the stopped formula is the time integral up to `t`
  have htime : ∀ᵐ ω ∂μ,
      ∫ s in Set.Ioc 0 T, (f' (Y s ω) * βt (s, ω) + 1 / 2 * (f'' (Y s ω) * γt (s, ω) ^ 2))
          ∂timeMeasure
        = ∫ s in Set.Ioc 0 t, (f' (X s ω) * β (s, ω) + 1 / 2 * (f'' (X s ω) * γ (s, ω) ^ 2))
          ∂timeMeasure := by
    filter_upwards [ae_ae_bandRestrict T hBmeas β t, ae_ae_bandRestrict T hBmeas γ t, hYX]
      with ω hb hg hy
    have hcongr : ∀ᵐ u ∂(timeMeasureHorizon T),
        f' (Y u ω) * βt (u, ω) + 1 / 2 * (f'' (Y u ω) * γt (u, ω) ^ 2)
          = (Set.Ioc 0 t).indicator
              (fun u => f' (X u ω) * β (u, ω) + 1 / 2 * (f'' (X u ω) * γ (u, ω) ^ 2)) u := by
      filter_upwards [hb, hg, ae_le_T_timeMeasure_T T] with u hbu hgu huT
      rw [hbu, hgu]
      by_cases hu : u ∈ Set.Ioc 0 t
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, one_mul, one_mul, hy u huT,
          min_eq_left hu.2]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul, zero_mul]
        ring
    have hcongr' : ∀ᵐ u ∂timeMeasure.restrict (Set.Ioc 0 T),
        f' (Y u ω) * βt (u, ω) + 1 / 2 * (f'' (Y u ω) * γt (u, ω) ^ 2)
          = (Set.Ioc 0 t).indicator
              (fun u => f' (X u ω) * β (u, ω) + 1 / 2 * (f'' (X u ω) * γ (u, ω) ^ 2)) u :=
      hcongr
    rw [integral_congr_ae hcongr', setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc_right htT)]
  filter_upwards [hito, hYX, htime] with ω h1 h2 h3
  have hYT : Y T ω = X t ω := by rw [h2 T le_rfl, min_eq_right htT]
  rw [← hYT, h1, h3, hIt]

include hB hBcont in
/-- Integrability of `f(X_t) - f(x₀)` for Lipschitz `f`. -/
theorem integrable_comp_at (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {C₁ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁)
    {t : ℝ≥0} (htT : t ≤ T) :
    Integrable (fun ω => f (l2ItoProcess T hBmeas x₀ β γ t ω) - f x₀) μ := by
  have hfc : Continuous f := Differentiable.continuous fun x => (hf x).differentiableAt
  have hXpred := l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀ β γ
  have hXt : StronglyMeasurable (fun ω => l2ItoProcess T hBmeas x₀ β γ t ω) :=
    (hXpred.stronglyAdapted t).mono ((natFiltration hBmeas).le t)
  have hD := (memLp_driftContinuousMod_slice T hBmeas β htT).integrable one_le_two
  have hI : Integrable (⇑(itoProcessCLM hB T t hBmeas γ)) μ :=
    (Lp.memLp _).integrable one_le_two
  refine ((hD.abs.add hI.abs).const_mul C₁).mono'
    ((hfc.comp_stronglyMeasurable hXt).sub stronglyMeasurable_const).aestronglyMeasurable ?_
  filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont γ htT] with ω hω
  rw [Real.norm_eq_abs]
  refine (abs_sub_le_of_deriv_bound hf hf1 _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hf1 0))
  simp only [l2ItoProcess, hω]
  rw [show x₀ + driftContinuousMod T hBmeas β t ω + (itoProcessCLM hB T t hBmeas γ) ω - x₀
      = driftContinuousMod T hBmeas β t ω + (itoProcessCLM hB T t hBmeas γ) ω by ring]
  exact abs_add_le _ _

include hB hBcont in
/-- **Itô's formula in expectation form** (Dynkin's formula) at any `t ≤ T`. -/
theorem ito_formula_L2_integral (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {C₁ C₂ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) (hf2 : ∀ x, |f'' x| ≤ C₂)
    {t : ℝ≥0} (htT : t ≤ T) :
    ∫ ω, (f (l2ItoProcess T hBmeas x₀ β γ t ω) - f x₀) ∂μ
      = ∫ ω, (∫ s in Set.Ioc 0 t, (f' (l2ItoProcess T hBmeas x₀ β γ s ω) * β (s, ω)
          + 1 / 2 * (f'' (l2ItoProcess T hBmeas x₀ β γ s ω) * γ (s, ω) ^ 2)) ∂timeMeasure) ∂μ := by
  obtain ⟨Γ, -, h⟩ := ito_formula_L2_at hB T hBmeas hBcont x₀ β γ hf hf' hf'' hf1 hf2 htT
  have hA := integrable_comp_at hB T hBmeas hBcont x₀ β γ hf hf1 htT
  have hM : Integrable (⇑(itoProcessCLM hB T t hBmeas Γ)) μ :=
    (Lp.memLp _).integrable one_le_two
  have hD : Integrable (fun ω => ∫ s in Set.Ioc 0 t, (f' (l2ItoProcess T hBmeas x₀ β γ s ω)
      * β (s, ω) + 1 / 2 * (f'' (l2ItoProcess T hBmeas x₀ β γ s ω) * γ (s, ω) ^ 2))
        ∂timeMeasure) μ := by
    refine (hA.sub hM).congr ?_
    filter_upwards [h] with ω hω
    simp only [Pi.sub_apply]
    rw [hω]
    ring
  rw [integral_congr_ae h, integral_add hM hD, integral_itoProcessCLM hB T hBmeas Γ htT,
    zero_add]

end Formula

end MathFin.FilteredIto
