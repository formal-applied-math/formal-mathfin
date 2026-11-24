/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.StochasticIntegralVersion
public import MathFin.Probability.Brownian.Ito.Filtered.CommonContinuous
public import MathFin.Probability.Brownian.Ito.Filtered.CommonLocality

/-!
# Joint Stochastic Integral

Process-domain argument adapted from MathFin.StochasticIntegralCharacterisation,
copyright (c) 2026 Raphael Coelho. Released under Apache 2.0 license.

## Main definitions

* `sIntegral`

## Main results

* `isStochasticIntegral_stopped`
* `sIntegral_curry`
* `sIntegral_curry_ae_eq_continuousMod`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonIntegral
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonLocality
open MathFin (tendsto_eLpNorm_sub_of_dominated_convergence)
open MathFin.StochasticIntegralCharacterisation (PredictableL2Version predictableL2Domain
      predictableL2Class)
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}
theorem ae_horizon_of_ae_forall (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) {q : ℝ≥0 × Ω → Prop}
    (hq : MeasurableSet[(ℱ).predictable] {z | q z})
    (h : ∀ᵐ ω ∂μ, ∀ t, q (t, ω)) :
    ∀ᵐ z ∂(trimMeasureT (μ := μ) T ℱ), q z := by
  apply ae_iff.2
  unfold trimMeasureT
  rw [trim_measurableSet_eq _
      (show MeasurableSet[(ℱ).predictable] {z | ¬ q z} from hq.compl)]
  refine measure_mono_null (t := Set.univ ×ˢ {ω | ¬ ∀ t, q (t, ω)})
      (fun z hz ↦ ⟨Set.mem_univ _, fun hall ↦ hz (hall z.1)⟩) ?_
  rw [Measure.prod_prod, ae_iff.1 h, mul_zero]
/-! ### The domain: processes with a predictable square-integrable version -/

variable (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ)

variable {T ℱ}

/-- Two predictable versions of one process are equal almost everywhere for the predictable time
measure. -/
theorem uncurry_ae_eq_of_isPredictableVersion {X X₁ X₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X X₁) (h₂ : PredictableL2Version
          μ ℱ (trimMeasureT (μ := μ) T ℱ) X X₂) :
    Function.uncurry X₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] Function.uncurry X₂ := by
  refine ae_horizon_of_ae_forall T ℱ
    (q := fun z ↦ Function.uncurry X₁ z = Function.uncurry X₂ z)
    (measurableSet_eq_fun h₁.1 h₂.1) ?_
  filter_upwards [h₁.2.2, h₂.2.2] with ω h1 h2 t
  exact (h1 t).symm.trans (h2 t)

/-- `integrandLp` does not depend on the version chosen. -/
theorem integrandLp_eq {X X' : ℝ≥0 → Ω → ℝ} (h : PredictableL2Version μ ℱ (trimMeasureT (μ :=
      μ) T ℱ) X X') :
    predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) X = h.2.1.toLp _ := by
  have hX : X ∈ predictableL2Domain μ ℱ (trimMeasureT (μ := μ) T ℱ) := ⟨X', h⟩
  rw [predictableL2Class, dite_eq_left hX]
  exact MemLp.toLp_congr _ _ (uncurry_ae_eq_of_isPredictableVersion hX.choose_spec h)


variable (T ℱ) in
/-- Read the terminal continuous linear Itô operator on a process with a predictable version. -/
noncomputable def sIntegral (hB : IsFilteredPreBrownian B ℱ μ) (X : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  itoIntegralCLMT hB T (predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) X)

private theorem version_band {i j : ℝ≥0} (hij : i ≤ j) {X : Ω → ℝ}
    (hm : Measurable[ℱ i] X) {C : ℝ} (hb : ∀ ω, ‖X ω‖ ≤ C) :
    PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) (fun k ω ↦ if k ∈ Set.Ioc i j then X ω
          else 0)
      (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0) := by
  let V := stepSP (B := fun _ _ ↦ 0) (fun _ ↦ measurable_const) hij (le_refl j) hm hb
  have he : (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0) = ⇑V.val := by
    funext k ω
    rw [coe_stepSP]
    simp [Set.indicator]
  rw [he]
  exact ⟨V.val.isStronglyPredictable.measurable, memLp_uncurry_trim_T T ℱ V.val, .rfl⟩

private theorem sIntegral_band (hB : IsFilteredPreBrownian B ℱ μ) {i j : ℝ≥0} (hij : i ≤ j) {X :
      Ω → ℝ}
    (hm : Measurable[ℱ i] X) {C : ℝ} (hb : ∀ ω, ‖X ω‖ ≤ C) :
    sIntegral T ℱ hB (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0)
      =ᵐ[μ] X * (B (min j T) - B (min i T)) := by
  have hv := version_band (T := T) (μ := μ) hij hm hb
  simp only [sIntegral, integrandLp_eq hv]
  by_cases hi : i ≤ T
  · let V := stepSP hB.measurable_eval (le_min hij hi) (min_le_right j T) hm hb
    have hc : hv.2.1.toLp _ = simpleAssemblyT (μ := μ) T ℱ V := by
      apply Lp.ext
      filter_upwards [hv.2.1.coeFn_toLp, (memLp_uncurry_trim_T (μ := μ) T ℱ V.val).coeFn_toLp,
        ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with z hz hz' ht
      change _ = (memLp_uncurry_trim_T (μ := μ) T ℱ V.val).toLp _ z
      rw [hz, hz']
      simp [V, Function.uncurry, coe_stepSP, Set.indicator, Set.mem_Ioc, ht.2]
    rw [hc, itoIntegralCLM_T_simpleAssembly]
    filter_upwards [(CommonL2.memLp_itoSimple hB hB.measurable_eval V.val).coeFn_toLp] with ω hω
    change (CommonL2.memLp_itoSimple hB hB.measurable_eval V.val).toLp _ ω = _
    rw [hω, itoSimple_stepSP, min_eq_left hi]
    rfl
  · have hc : hv.2.1.toLp _ = 0 := by
      apply Lp.ext
      filter_upwards [hv.2.1.coeFn_toLp, ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ,
        Lp.coeFn_zero ℝ 2 (trimMeasureT (μ := μ) T ℱ)] with z hz ht h0
      rw [hz,h0]
      simp [Function.uncurry, Set.mem_Ioc, not_lt_of_ge (ht.2.trans (le_of_not_ge hi))]
    rw [hc,map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
    simp [min_eq_right (le_of_not_ge hi), min_eq_right ((le_of_not_ge hi).trans hij)]

omit mΩ in
/-- The initial band `1_{[0,i]}(t)·X(ω)` is the elementary integrand on `(0, i]` away from the time
origin. -/
theorem uncurry_bottomBand_of_ne_zero (i : ℝ≥0) (X : Ω → ℝ) {z : ℝ≥0 × Ω} (hz : z.1 ≠ 0) :
    Function.uncurry (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0) z =
          MathFin.ItoIntegralL2.elemIntegrand 0 i X z := by
  simp only [Function.uncurry, MathFin.ItoIntegralL2.elemIntegrand, Set.indicator_apply,
        Set.mem_Iic, Set.mem_Ioc,
    pos_iff_ne_zero.2 hz, true_and]
  split_ifs <;> simp

/-- The initial band, with an `𝓕_0`-measurable coefficient, is predictable. Unlike the later bands
it charges the time origin, through `{0} × Ω`. -/
theorem measurable_bottomBand (i : ℝ≥0) {X : Ω → ℝ}
    (hXm : Measurable[ℱ ⊥] X) :
    Measurable[(ℱ).predictable]
      (Function.uncurry (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0)) := by
  have hX : Measurable[(ℱ).predictable] fun z : ℝ≥0 × Ω ↦ X z.2 :=
    fun S hS ↦ by
      have h := measurableSet_predictable_univ_prod (𝓕 := ℱ) (hXm hS)
      rw [Set.univ_prod] at h
      exact h
  convert hX.indicator
    (measurableSet_predictable_Iic_prod (i := i) (s := Set.univ) MeasurableSet.univ) using 1
  funext z
  by_cases hz : z.1 ≤ i <;> simp [Function.uncurry, hz]

/-- The initial band with a bounded `𝓕_0`-measurable coefficient is its own predictable
version. -/
theorem isPredictableVersion_bottomBand (i : ℝ≥0) {X : Ω → ℝ}
    (hXm : Measurable[ℱ ⊥] X) {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) :
    PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) (fun k ω ↦ if k ∈ Set.Iic i then X ω
          else 0)
      (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0) := by
  refine ⟨measurable_bottomBand i hXm, ?_, .rfl⟩
  refine MemLp.of_bound (measurable_bottomBand i hXm).aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ ?_)
  simp only [Function.uncurry]
  split_ifs
  · exact hC _
  · simpa using (norm_nonneg (X z.2)).trans (hC z.2)

/-- **The initial band identity**: the integral of `1_{[0,i]}·X` against the stopped driver is
`X·(B (min i T) − B 0)`. The time origin has measure zero, so this band has the class of the band
on `(0, i]`, and the band identity applies. -/
theorem sIntegral_bottomBand (hB : IsFilteredPreBrownian B ℱ μ) (i : ℝ≥0) {X : Ω → ℝ}
    (hXm : Measurable[ℱ ⊥] X) {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) :
    sIntegral T ℱ hB (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0)
      =ᵐ[μ] X * ((fun s ↦ B (min s T)) i - (fun s ↦ B (min s T)) ⊥) := by
  have hv := isPredictableVersion_bottomBand (μ := μ) (T := T) (ℱ := ℱ) i hXm hC
  have hv' := version_band (μ := μ) (T := T) (ℱ := ℱ) (zero_le : (0 : ℝ≥0) ≤ i) hXm hC
  have hclass : hv.2.1.toLp _ = hv'.2.1.toLp _ := by
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with z hz
    rw [MathFin.StochasticIntegralCharacterisation.uncurry_band, uncurry_bottomBand_of_ne_zero i
          X hz.1.ne']
  have hband := sIntegral_band (T := T) (ℱ := ℱ) hB (zero_le : (0 : ℝ≥0) ≤ i) hXm hC
  simp only [sIntegral, integrandLp_eq hv, integrandLp_eq hv'] at hband ⊢
  rw [hclass]
  exact hband

/-! ### Versions are closed under the operations the characterisation asks for -/

omit [IsProbabilityMeasure μ] in
private theorem version_add {X₁ X₂ X₁' X₂' : ℝ≥0 → Ω → ℝ}
    (h₁ : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X₁ X₁') (h₂ :
          PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X₂ X₂') :
    PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) (X₁ + X₂) (X₁' + X₂') :=
  ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, h₁.2.2.add h₂.2.2⟩

omit [IsProbabilityMeasure μ] in
private theorem version_const_smul {X X' : ℝ≥0 → Ω → ℝ}
    (h : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X X') (c : ℝ) :
    PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) (c • X) (c • X') :=
  ⟨h.1.const_smul c, h.2.1.const_smul c, h.2.2.const_smul⟩

omit [IsProbabilityMeasure μ] in
private theorem version_of_indistinguishable {X Y X' : ℝ≥0 → Ω → ℝ}
    (h : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X X') (hXY : X ≡ᵐ[μ] Y) :
    PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) Y X' :=
  ⟨h.1, h.2.1, hXY.symm.trans h.2.2⟩

theorem integrandLp_add {X₁ X₂ X₁' X₂' : ℝ≥0 → Ω → ℝ}
    (h₁ : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X₁ X₁') (h₂ :
          PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X₂ X₂') :
    predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) (X₁ + X₂) = predictableL2Class μ ℱ
          (trimMeasureT (μ := μ) T ℱ) X₁ + predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ)
          X₂ := by
  rw [integrandLp_eq (version_add h₁ h₂), integrandLp_eq h₁, integrandLp_eq h₂]
  exact MemLp.toLp_add _ _

theorem integrandLp_const_smul {X X' : ℝ≥0 → Ω → ℝ} (h : PredictableL2Version μ ℱ (trimMeasureT
      (μ := μ) T ℱ) X X')
    (c : ℝ) : predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) (c • X) = c •
          predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) X := by
  rw [integrandLp_eq (version_const_smul h c), integrandLp_eq h]
  exact MemLp.toLp_const_smul c _

/-! ### Dominated convergence -/

/-- **Dominated convergence for the integral against the stopped driver.** A sequence in the
domain, converging
at every time and outcome and dominated by one process of the domain, has its limit in the domain,
and the integrals converge in measure. -/
theorem sIntegral_dct (hB : IsFilteredPreBrownian B ℱ μ) (X : ℕ → ℝ≥0 → Ω → ℝ)
    (X_dom X_lim : ℝ≥0 → Ω → ℝ) (h₁ : ∀ n, X n ∈ predictableL2Domain μ ℱ (trimMeasureT (μ := μ)
          T ℱ))
    (h₂ : X_dom ∈ predictableL2Domain μ ℱ (trimMeasureT (μ := μ) T ℱ)) (h_dom : ∀ n i ω, |X n i
          ω| ≤ |X_dom i ω|)
    (h_lim : ∀ i ω, Tendsto (X · i ω) atTop (𝓝 (X_lim i ω))) :
    X_lim ∈ predictableL2Domain μ ℱ (trimMeasureT (μ := μ) T ℱ) ∧
      TendstoInMeasure μ (fun n ↦ sIntegral T ℱ hB (X n)) atTop
        (sIntegral T ℱ hB X_lim) := by
  have h₁' : ∀ n, ∃ V, PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) (X n) V := h₁
  choose V hV using h₁'
  obtain ⟨Vd, hVd⟩ := h₂
  set pred := (ℱ).predictable
  -- the limit version, pathwise
  set Vl : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun n ↦ V n t ω)
  have hall : ∀ᵐ ω ∂μ, (∀ n t, V n t ω = X n t ω) ∧ ∀ t, Vd t ω = X_dom t ω := by
    filter_upwards [ae_all_iff.2 fun n ↦ (hV n).2.2.symm, hVd.2.2.symm] with ω hn hd
    exact ⟨hn, hd⟩
  have htend : ∀ᵐ ω ∂μ, ∀ t, Tendsto (fun n ↦ V n t ω) atTop (𝓝 (X_lim t ω)) := by
    filter_upwards [hall] with ω hω t
    simpa only [hω.1 _ t] using h_lim t ω
  have hVl_eq : Vl ≡ᵐ[μ] X_lim := by
    filter_upwards [htend] with ω hω t
    exact (hω t).limUnder_eq
  have hVm (n : ℕ) : StronglyMeasurable[pred] (Function.uncurry (V n)) :=
    (hV n).1.stronglyMeasurable
  have hVl_meas : Measurable[pred] (Function.uncurry Vl) :=
    (StronglyMeasurable.limUnder (l := atTop) hVm).measurable
  -- domination and convergence almost everywhere for the predictable time measure
  have hdom (n : ℕ) : ∀ᵐ z ∂(trimMeasureT (μ := μ) T ℱ),
      ‖Function.uncurry (V n) z‖ ≤ ‖Function.uncurry Vd z‖ := by
    refine ae_horizon_of_ae_forall T ℱ
      (measurableSet_le (hV n).1.norm hVd.1.norm) ?_
    filter_upwards [hall] with ω hω t
    simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs, hω.1 n t, hω.2 t] using h_dom n t ω
  have hconv : ∀ᵐ z ∂(trimMeasureT (μ := μ) T ℱ),
      Tendsto (fun n ↦ Function.uncurry (V n) z) atTop (𝓝 (Function.uncurry Vl z)) := by
    have hex : ∀ᵐ z ∂(trimMeasureT (μ := μ) T ℱ),
        ∃ c, Tendsto (fun n ↦ Function.uncurry (V n) z) atTop (𝓝 c) := by
      refine ae_horizon_of_ae_forall T ℱ
        (StronglyMeasurable.measurableSet_exists_tendsto hVm) ?_
      filter_upwards [htend] with ω hω t
      exact ⟨_, hω t⟩
    filter_upwards [hex] with z hz
    exact tendsto_nhds_limUnder hz
  have hdom_lim : ∀ᵐ z ∂(trimMeasureT (μ := μ) T ℱ),
      ‖Function.uncurry Vl z‖ ≤ ‖Function.uncurry Vd z‖ := by
    filter_upwards [hconv, ae_all_iff.2 hdom] with z hz hzd
    exact le_of_tendsto' hz.norm hzd
  have hVl : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) X_lim Vl :=
    ⟨hVl_meas, hVd.2.1.of_le hVl_meas.stronglyMeasurable.aestronglyMeasurable hdom_lim,
      hVl_eq.symm⟩
  refine ⟨⟨Vl, hVl⟩, ?_⟩
  -- convergence in predictable L², then through the isometry, then in measure
  have hLp : Tendsto (fun n ↦ predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) (X n)) atTop
      (𝓝 (predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) X_lim)) := by
    have hseq : (fun n ↦ predictableL2Class μ ℱ (trimMeasureT (μ := μ) T ℱ) (X n)) = fun n ↦
          (hV n).2.1.toLp _ :=
      funext fun n ↦ integrandLp_eq (hV n)
    rw [hseq, integrandLp_eq hVl]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n ↦ (hV n).2.1) _ hVl.2.1).2
      (tendsto_eLpNorm_sub_of_dominated_convergence ENNReal.ofNat_ne_top _
        (fun n ↦ (hVm n).aestronglyMeasurable) hVd.2.1.norm hdom hconv)
  exact tendstoInMeasure_of_tendsto_Lp
    (((itoIntegralCLMT hB T).continuous.tendsto _).comp hLp)

/-! ### The integral against the stopped driver extends the Riemann–Stieltjes integral -/

/-- **The integral against the stopped driver is an extension of the Riemann–Stieltjes
integral**, in the sense of
BrownianMotion's `IsRiemannStieltjesExtension`: on elementary processes it is the Riemann–Stieltjes
sum against the driver stopped at `T`, and it respects linearity, indistinguishability and dominated
convergence. -/
theorem isRiemannStieltjesExtension (hB : IsFilteredPreBrownian B ℱ μ) :
    IsRiemannStieltjesExtension μ ((fun s ↦ B (min s T))) (ℱ)
      (sIntegral T ℱ hB) (predictableL2Domain μ ℱ (trimMeasureT (μ := μ) T ℱ)) where
  measurable _ _ := Lp.aestronglyMeasurable _
  elementary_ioc i j hij X := by
    -- a simple function over `𝓕_i` is bounded and `𝓕_i`-measurable
    obtain ⟨⟨C, hC⟩, hXm⟩ : (∃ C, ∀ ω, ‖X ω‖ ≤ C) ∧ Measurable[ℱ i] X := by
      let : MeasurableSpace Ω := ℱ i
      exact ⟨X.exists_forall_norm_le, X.measurable⟩
    exact ⟨⟨_, version_band hij hXm hC⟩, sIntegral_band hB hij hXm hC⟩
  elementary_iic i X := by
    obtain ⟨⟨C, hC⟩, hXm⟩ : (∃ C, ∀ ω, ‖X ω‖ ≤ C) ∧ Measurable[ℱ ⊥] X := by
      let : MeasurableSpace Ω := ℱ ⊥
      exact ⟨X.exists_forall_norm_le, X.measurable⟩
    exact ⟨⟨_, isPredictableVersion_bottomBand i hXm hC⟩, sIntegral_bottomBand hB i hXm hC⟩
  integral_add X₁ X₂ h₁ h₂ := by
    obtain ⟨V₁, hV₁⟩ := h₁
    obtain ⟨V₂, hV₂⟩ := h₂
    refine ⟨⟨_, version_add hV₁ hV₂⟩, ?_⟩
    simp only [sIntegral]
    rw [integrandLp_add hV₁ hV₂, map_add]
    exact Lp.coeFn_add _ _
  integral_smul X c h := by
    obtain ⟨V, hV⟩ := h
    refine ⟨⟨_, version_const_smul hV c⟩, ?_⟩
    simp only [sIntegral]
    rw [integrandLp_const_smul hV, map_smul]
    exact Lp.coeFn_smul _ _
  integral_indistinguishable X₁ X₂ h₁ h₂ := by
    obtain ⟨V, hV⟩ := h₁
    refine ⟨⟨V, version_of_indistinguishable hV h₂⟩, ?_⟩
    simp only [sIntegral]
    rw [integrandLp_eq hV, integrandLp_eq (version_of_indistinguishable hV h₂)]
  integral_dct := sIntegral_dct hB



/-- The common-filtration terminal Itô map is the BrownianMotion stochastic integral
of the stopped driver, including kernels depending on both drivers. -/
theorem isStochasticIntegral_stopped (hB : IsFilteredPreBrownian B ℱ μ) :
    IsStochasticIntegral μ (fun t ↦ B (min t T)) ℱ (sIntegral T ℱ hB) (predictableL2Domain μ ℱ
          (trimMeasureT (μ := μ) T ℱ)) :=
  MathFin.StochasticIntegralCharacterisation.General.isStochasticIntegral_of_predictable_versions
    (generateFrom_predictableRect ℱ)
    (isRiemannStieltjesExtension (T := T) hB)
    (fun _ ⟨V, hV⟩ ↦ ⟨V, hV.1.stronglyMeasurable, hV.2.2⟩)

/-- Evaluation on the predictable representative of an L² kernel recovers exactly
the terminal operator used by the common-filtration SDE. -/
theorem sIntegral_curry (hB : IsFilteredPreBrownian B ℱ μ) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T
      ℱ)) :
    sIntegral T ℱ hB (Function.curry (⇑φ)) = ⇑(itoIntegralCLMT hB T φ) := by
  have hv : PredictableL2Version μ ℱ (trimMeasureT (μ := μ) T ℱ) (Function.curry (⇑φ))
        (Function.curry (⇑φ)) :=
    ⟨(Lp.stronglyMeasurable φ).measurable, Lp.memLp φ, .rfl⟩
  rw [sIntegral, integrandLp_eq hv]
  have e : hv.2.1.toLp _ = φ := Lp.ext hv.2.1.coeFn_toLp
  rw [e]

/-- At its horizon the continuous realization of every common-filtration kernel
is a version of the BrownianMotion stochastic integral. -/
theorem sIntegral_curry_ae_eq_continuousMod (hB : IsFilteredPreBrownian B ℱ μ)
    (hc : ∀ ω, Continuous (fun s ↦ B s ω)) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    sIntegral T ℱ hB (Function.curry (⇑φ)) =ᵐ[μ]
      CommonContinuous.itoContinuousMod T hB.measurable_eval φ T := by
  have hh := CommonContinuous.itoContinuousMod_modification hB T hB.measurable_eval hc φ (le_refl T)
  rw [sIntegral_curry, ← CommonProcessGeneral.itoProcessCLM_terminal_eq hB T hB.measurable_eval]
  exact hh.symm

end MathFin.FilteredIto.CommonIntegral
