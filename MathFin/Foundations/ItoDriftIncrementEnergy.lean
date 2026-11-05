/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaItoProcess
public import MathFin.Foundations.ItoDriftExpectation
public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.AdaptedProcessToLp
public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
public import MathFin.Foundations.WeightedQuadraticVariation
public import MathFin.Foundations.ItoFormulaRemainder
public import MathFin.Foundations.DiscreteIto
public import MathFin.Foundations.ItoIntegralProcessIsometry
public import MathFin.Foundations.ItoIsometryAdapted
public import MathFin.Foundations.ItoIntegralBrownian
public import MathFin.Foundations.QuadraticVariationL2
public import MathFin.Foundations.GaussianMoments
public import MathFin.Foundations.AdaptedDrift
public import MathFin.Foundations.MartingaleTransform

/-! # The increment energy of an adapted Itô integral (the discrete route, stages 2–3)

The first layer of the integrated Itô–drift identity for adapted coefficients
(`ItoFormulaAdaptedDrift`): the band-to-slice conversion of the predictable trim measure, the
expectation pull-out `integral_mul_condExp_eq`, the martingale property `martingale_M` of the
hypothesized `M` and the exact first-order kill `mul_trueIncr_expect_eq_zero` it gives, the
increment-energy law `incrementEnergy` (`𝔼[(M_v − M_u)²] = ∫_{(u,v]} δ² d(trim)`), and the
left-endpoint step approximants `deltaStepLp` with their `L²` convergence `deltaStepLp_tendsto`.
`M` is a hypothesis: a `natFiltration`-adapted version of the Itô integral of `δ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIsometryAdapted QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-! ### Stage 2 — the bounded *adapted* coefficients (`β`, `δ` random)

(Stage 1, the constant-coefficient identity, is `ito_drift_expectation_identity` in
`MathFin/Foundations/ItoDriftExpectation`.)

The data of the integrated Itô–drift identity for an Itô process with random adapted
coefficients: a pre-Brownian motion `B` with measurable sections (path continuity of `B` is not
assumed), bounded adapted path-continuous `β, δ`, and two hypothesized processes: a
`natFiltration`-adapted `M` with `M t =ᵐ (δ●B)_t` for every `t ≥ 0` (`hD.ae_eq`, the process values
of `itoProcessCLM` at the σ-realization `processToLp δ`), and an `X` with
`X t = c + ∫₀ᵗ β_s ds + M t` (`hXrel`) whose paths are continuous almost surely (`hXcont`). For
`B` with continuous paths, the constructed Itô process provides such an `M` (see the module
docstring of `ItoFormulaAdaptedDrift`). The blocks use `M` through `hD.ae_eq` and `hD.adaptedM`;
almost
sure path continuity enters through the hypothesis `hXcont`.

The conversion below is the first ingredient: for a bounded adapted path-continuous `ψ`, the
`(u,v]`-band integral of its uncurried form over the predictable trim measure equals the plain
slice integral `∫_u^v 𝔼[ψ_s] ds`. -/

/-- **The band-slice conversion**: for a bounded adapted path-continuous `ψ`, the
`(u,v]`-band integral of its uncurried form over the predictable trim measure equals the
plain slice integral `∫_u^v 𝔼[ψ_s] ds`. Route: predictability of `(s,ω) ↦ ψ s ω`
(`isStronglyPredictable_of_bdd_adapted_cont`) drops the trim (`integral_trim`), the band
restriction moves to the time coordinate (`Measure.restrict_prod_eq_prod_univ` +
`Measure.restrict_restrict`), and the product integral Fubini-factors (`integral_prod`). -/
private theorem bandIntegral_slice (hBmeas : ∀ t, Measurable (B t)) (ψ : ℝ≥0 → Ω → ℝ)
    (hψadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (ψ t))
    (hψcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ ψ s ω)
    {Cψ : ℝ} (hψbdd : ∀ s ω, |ψ s ω| ≤ Cψ)
    (u v : ℝ≥0) (hvT : v ≤ T) :
    ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ s in Set.Ioc u v, (∫ ω, ψ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  have hpred : IsStronglyPredictable (natFiltration hBmeas) ψ :=
    isStronglyPredictable_of_bdd_adapted_cont hBmeas hψadap hψcont
  have hband : MeasurableSet[(natFiltration hBmeas).predictable]
      (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ
  -- measurability/integrability of the band-indicatored integrand
  have hsm : StronglyMeasurable[(natFiltration hBmeas).predictable]
      ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ)) :=
    (show StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry ψ) from
      hpred).indicator hband
  have hint : Integrable (Function.uncurry ψ) (trimMeasure_T (μ := μ) T hBmeas) :=
    (MemLp.of_bound hpred.aestronglyMeasurable Cψ
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hψbdd z.1 z.2)).integrable one_le_two
  have hUVamb : MeasurableSet (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  have : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator
      (Function.uncurry ψ)) ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) :=
    ⟨_, StronglyMeasurable.mono hsm (natFiltration hBmeas).predictable_le_prod,
      Eventually.of_forall fun _ ↦ rfl⟩
  have hint' : Integrable ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ))
      ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) := by
    refine Integrable.of_bound haesm (max Cψ 0) ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
    · rw [Set.indicator_of_mem hz]
      exact le_trans (hψbdd z.1 z.2) (le_max_left Cψ 0)
    · rw [Set.indicator_of_notMem hz]
      simp
  calc ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
        (integral_indicator (μ := trimMeasure_T (μ := μ) T hBmeas)
          (f := Function.uncurry ψ) hband).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(((timeMeasure_T T).prod μ).trim
            (natFiltration hBmeas).predictable_le_prod) := rfl
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((timeMeasure_T T).prod μ) :=
        (integral_trim (natFiltration hBmeas).predictable_le_prod hsm).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((ItoIntegralL2.timeMeasure.prod μ).restrict (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))) := by
        rw [show (((timeMeasure_T T).prod μ : Measure (ℝ≥0 × Ω))
            = (ItoIntegralL2.timeMeasure.prod μ).restrict
              (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))) from by
          rw [timeMeasure_T, Measure.restrict_prod_eq_prod_univ]]
    _ = ∫ z, (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator
          ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ)) z
          ∂(ItoIntegralL2.timeMeasure.prod μ) :=
        (integral_indicator (MeasurableSet.prod measurableSet_Ioc
          MeasurableSet.univ)).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(ItoIntegralL2.timeMeasure.prod μ) := by
        have hsub : (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
            ⊆ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) := by
          rintro z hz
          exact ⟨⟨lt_of_le_of_lt (NNReal.coe_nonneg _) hz.1.1, le_trans hz.1.2 hvT⟩, hz.2⟩
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        by_cases hz : z ∈ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        · rw [Set.indicator_of_mem (hsub hz), Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          by_cases hz2 : z ∈ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          · rw [Set.indicator_of_mem hz2, Set.indicator_of_notMem hz]
          · rw [Set.indicator_of_notMem hz2]
    _ = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
          ∂(ItoIntegralL2.timeMeasure.prod μ) := integral_indicator hUVamb
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) := by
        have : SFinite ItoIntegralL2.timeMeasure := inferInstance
        have hmeas : ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ)
            = (ItoIntegralL2.timeMeasure.prod μ).restrict
              (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) := by
          rw [Measure.restrict_prod_eq_prod_univ]
        rw [hmeas, integral_indicator hUVamb,
          Measure.restrict_restrict_of_subset
            (Set.Subset.refl (Set.Ioc u v ×ˢ (Set.univ : Set Ω)))]
    _ = ∫ s, (∫ ω, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) ∂μ)
          ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
        integral_prod _ hint'
    _ = ∫ s in Set.Ioc u v, (∫ ω, ψ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs ↦ ?_)
        have hslice : ∀ ω' : Ω, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator
            (Function.uncurry ψ) (s, ω') = ψ s ω' := by
          intro ω'
          rw [Set.indicator_of_mem
            (Set.mem_prod.mpr ⟨hs, Set.mem_univ ω'⟩)]
          rfl
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
          change (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) = _
          rw [hslice ω])

/-! ### Stage 3 — the expectation pull-out, the increment energy, and the step approximants

* `integral_mul_condExp_eq` — the expectation pull-out `𝔼[h · g] = 𝔼[h · 𝔼[g | 𝓕]]`;
* `mul_trueIncr_expect_eq_zero` — `𝔼[h·(M_v − M_u)] = 0` for bounded `𝓕_u`-measurable `h`
  (the martingale property of `M` against `integral_inner_sub_eq_zero` at `F = ℝ`);
* `clm_band_energy` — the energy of a CLM Itô-integral increment over a band is the band energy
  of the integrand, by the martingale pull-out `𝔼[M_u M_v] = 𝔼[M_u²]` plus the time-indexed
  isometry `itoProcessCLM_norm_sq` and the nested-band split;
* `incrementEnergy` — the unweighted increment isometry `𝔼[(M_v − M_u)²] = ∫_{(u,v]} δ² d(trim)`
  (`= ∫_u^v 𝔼[δ_s²] ds`), `clm_band_energy` transferred to `M` along `hMeq` and converted to the
  slice integral by the band-to-slice conversion;
* `deltaStepLp`, `deltaStepLp_tendsto` — the left-endpoint step approximants of `δ` on the
  uniform partition and their `L²` convergence. The terminal Itô isometry is an isometry, so
  it transfers the Riemann bridge's `L²` convergence of the Itô sums
  (`itoIntegralCLM_T_of_bdd_adapted_cont`) to the integrand classes.

`M` enters through `hMeq` and, for the martingale statements, the adaptedness `hMadap`. -/

/-- **Expectation pull-out across a sub-σ-algebra** (the tower step): an `𝓕`-measurable
factor crosses the conditional expectation, `𝔼[h·g] = 𝔼[h·𝔼[g | 𝓕]]`. -/
theorem integral_mul_condExp_eq {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ)
    {h g : Ω → ℝ} (hh : StronglyMeasurable[𝓕] h) (hgh : Integrable (h * g) μ)
    (hg : Integrable g μ) :
    ∫ ω, h ω * g ω ∂μ = ∫ ω, h ω * μ[g | 𝓕] ω ∂μ := by
  calc ∫ ω, h ω * g ω ∂μ
      = ∫ ω, μ[h * g | 𝓕] ω ∂μ := (integral_condExp h𝓕).symm
    _ = ∫ ω, h ω * μ[g | 𝓕] ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hh hgh hg)

/-- The `n`-th left-endpoint step approximant of the integrand `δ`, as an element of
the Itô-integrand space (the `simpleAssembly_T` embedding of `stepσ n`). -/
noncomputable def deltaStepLp (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) (n : ℕ) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)

/-- **`L²`-convergence of the step approximants**: `‖δⁿ − δ‖_{L²(trim)} → 0`. The
terminal Itô isometry `itoIntegralCLM_T_norm` is an isometry, so the norm of the
integrand difference equals the norm of the difference of the Itô sums — the
Riemann bridge's `L²` convergence (`itoIntegralCLM_T_of_bdd_adapted_cont`), with the
step-integrand sum identified with the Riemann sum by `itoIntegralCLM_T_stepσ`. -/
theorem deltaStepLp_tendsto (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) :
    Tendsto (fun n : ℕ ↦ (deltaStepLp hBmeas hδadap hδbdd n :
        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))) atTop
      (𝓝 (processToLp T hBmeas hδadap hδcont hδbdd)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hiso : ∀ ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ‖ψ‖ = ‖itoIntegralCLM_T hB T hBmeas ψ‖ := fun ψ ↦
    (itoIntegralCLM_T_norm hB T hBmeas ψ).symm
  have hstep : ∀ n : ℕ, itoIntegralCLM_T hB T hBmeas (deltaStepLp hBmeas hδadap hδbdd n)
      = (memLp_riemannσ hB hBmeas hδadap hδbdd T n).toLp (riemannσ δ T n) :=
    fun n ↦ itoIntegralCLM_T_stepσ hB hBmeas hδadap hδbdd T n
  have key : ∀ n : ℕ,
      ‖(deltaStepLp hBmeas hδadap hδbdd n
          - processToLp T hBmeas hδadap hδcont hδbdd : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
      = ‖((memLp_riemannσ hB hBmeas hδadap hδbdd T n).toLp (riemannσ δ T n)
          - itoIntegralCLM_T hB T hBmeas (processToLp T hBmeas hδadap hδcont hδbdd) :
            Lp ℝ 2 μ)‖ := by
    intro n
    rw [hiso _]
    congr 1
    rw [map_sub, hstep n]
  have hbridge := itoIntegralCLM_T_of_bdd_adapted_cont hB hBmeas hδadap hδcont hδbdd T
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbridge ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hN' := hN n hn
  rw [dist_eq_norm] at hN'
  rw [key n, dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact hN'

/-- **The CLM band-energy law**: the `L²` energy of the increment of the CLM Itô-integral
process of an arbitrary integrand class `φ'` over a band `(u,v]` is the band energy of the
integrand — the version-free law, proved directly at the CLM level (the a.e. pull-out for the
martingale cross term, the time-indexed isometry `itoProcessCLM_norm_sq`, and the nested-band
split); `incrementEnergy` is its transfer to a hypothesized version `M`. -/
theorem clm_band_energy {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (φ' : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, ((itoProcessCLM hB T v hBmeas φ' : Ω → ℝ) ω
        - (itoProcessCLM hB T u hBmeas φ' : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  set A := itoProcessCLM hB T v hBmeas φ' with hAdef
  set b := itoProcessCLM hB T u hBmeas φ' with hbdef
  -- the martingale congruence at CLM level
  have hmart : μ[(A : Ω → ℝ) | natFiltration hBmeas u] =ᵐ[μ] (b : Ω → ℝ) :=
    itoIntegralProcessGen_isMartingale hB T hBmeas φ' huv
  have hAmem := Lp.memLp A
  have hbmem := Lp.memLp b
  have hAint : Integrable (A : Ω → ℝ) μ := hAmem.integrable one_le_two
  have hbint : Integrable (b : Ω → ℝ) μ := hbmem.integrable one_le_two
  -- cross-term kill through the a.e. pull-out (CLM values are a.e. 𝓕_u-measurable)
  have hbae : AEStronglyMeasurable[natFiltration hBmeas u] (b : Ω → ℝ) μ :=
    itoProcessCLM_aeStronglyMeasurable (μ := μ) hB T u hBmeas φ'
  have hAprod : Integrable (fun ω ↦ (b : Ω → ℝ) ω * (A : Ω → ℝ) ω) μ :=
    hbmem.integrable_mul hAmem
  have hcross : ∫ ω, (b : Ω → ℝ) ω * (A : Ω → ℝ) ω ∂μ
      = ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ := by
    calc ∫ ω, (b : Ω → ℝ) ω * (A : Ω → ℝ) ω ∂μ
        = ∫ ω, μ[(fun ω' ↦ (b : Ω → ℝ) ω' * (A : Ω → ℝ) ω') | natFiltration hBmeas u] ω ∂μ :=
          (integral_condExp ((natFiltration hBmeas).le u)).symm
      _ = ∫ ω, (b : Ω → ℝ) ω * μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω ∂μ :=
          integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left hbae hAprod hAint)
      _ = ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hmart] with ω hω
          rw [hω]
  have hAmem2 : Integrable (fun ω ↦ (A : Ω → ℝ) ω ^ 2) μ := hAmem.integrable_sq
  have hbmem2 : Integrable (fun ω ↦ (b : Ω → ℝ) ω ^ 2) μ := hbmem.integrable_sq
  -- expansion of the squared increment
  have hsplit : ∫ ω, ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ := by
    have hsq : ∫ ω, ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 ∂μ
        = ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)
            + (b : Ω → ℝ) ω ^ 2) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      change ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 = _
      ring
    rw [hsq]
    have h1 : ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)
        + (b : Ω → ℝ) ω ^ 2) ∂μ
        = ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)) ∂μ
          + ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ :=
      integral_add (hAmem2.sub (hAprod.const_mul 2)) hbmem2
    rw [h1]
    have h2 : ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)) ∂μ
        = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω) ∂μ :=
      integral_sub hAmem2 (hAprod.const_mul 2)
    rw [h2, integral_const_mul, hcross]
    have hbb : ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ = ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω ↦ by
        change (b : Ω → ℝ) ω * (b : Ω → ℝ) ω = _
        ring)
    rw [hbb]
    ring
  -- band energies through the time-indexed isometry
  have hband : ∀ w : ℝ≥0, w ≤ T →
      ∫ ω, (itoProcessCLM hB T w hBmeas φ' : Ω → ℝ) ω ^ 2 ∂μ
        = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro w hwT
    calc ∫ ω, (itoProcessCLM hB T w hBmeas φ' : Ω → ℝ) ω ^ 2 ∂μ
        = ‖itoProcessCLM hB T w hBmeas φ'‖ ^ 2 := (lp_two_norm_sq _).symm
      _ = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := itoProcessCLM_norm_sq hB hwT hBmeas φ'
  have hint : Integrable (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp φ').integrable_sq
  have hintU : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.integrableOn
  have hintUV : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.integrableOn
  have hdisj : Disjoint
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) :=
    Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le le_rfl) _ _
  have hbandsplit : ∫ z in Set.Ioc (0:ℝ≥0) v ×ˢ (Set.univ : Set Ω),
      (φ' : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have hprod0 : (Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω))
        ∪ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        = (Set.Ioc (0:ℝ≥0) v) ×ˢ (Set.univ : Set Ω) := by
      rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ≥0) ≤ u) huv]
    rw [← hprod0]
    exact setIntegral_union hdisj
      (MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ)
      hintU hintUV
  rw [hsplit, hband v hvT, hband u (le_trans huv hvT), hbandsplit]
  ring

/-- **The setting of the adapted Itô–drift stack.** For a pre-Brownian motion `B` with measurable
sections, a bounded `natFiltration`-adapted path-continuous integrand `δ` (bound `Dd`), and a
process `M` that is `natFiltration`-adapted and, at every time, a.e. equal to the Itô integral
process `(δ●B)_t` of `itoProcessCLM` at horizon `T` (the σ-realization `processToLp δ`):
`M` is a hypothesized version of `∫ δ dB`. The drift stack (`incrementEnergy` through
`itoDrift_expectation_identity_adapted`, the Gyöngy and Dupire consumers) is conditional on this
one object. -/
structure IsAdaptedItoDrift {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (δ : ℝ≥0 → Ω → ℝ) (Dd : ℝ)
    (M : ℝ≥0 → Ω → ℝ) : Prop where
  /-- `δ` is adapted to the natural filtration of `B`. -/
  adapted : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t)
  /-- `δ` has continuous paths. -/
  continuous : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω
  /-- `δ` is bounded by `Dd`. -/
  bdd : ∀ t ω, |δ t ω| ≤ Dd
  /-- `M` is adapted to the natural filtration of `B`. -/
  adaptedM : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t)
  /-- `M t` is a.e. the CLM Itô integral process of `δ` at time `t`, horizon `T`. -/
  ae_eq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas adapted continuous bdd) : Ω → ℝ)

section AdaptedData

variable (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  {M : ℝ≥0 → Ω → ℝ} (hD : IsAdaptedItoDrift hB hBmeas T δ Dd M)

include hB hBmeas hD

/-- The Itô-integral process `M` is square-integrable at every time (its values are
a.e.-equal to `L²` CLM values). -/
theorem memLp_M (t : ℝ≥0) : MemLp (M t) 2 μ :=
  (Lp.memLp (itoProcessCLM hB T t hBmeas (processToLp T hBmeas hD.adapted hD.continuous
    hD.bdd))).ae_eq
    (hD.ae_eq t).symm

/-- The hypothesized Itô-integral process `M` is a martingale for the natural filtration of `B`:
the martingale property of `itoProcessCLM` (`itoIntegralProcessGen_isMartingale`) transferred
along the a.e. identification `hD.ae_eq`. -/
theorem martingale_M : Martingale M (natFiltration hBmeas) μ :=
  ⟨hD.adaptedM, fun u v huv ↦ condExp_congr_ae (hD.ae_eq v) |>.trans
    ((itoIntegralProcessGen_isMartingale hB T hBmeas _ huv).trans (hD.ae_eq u).symm)⟩

/-- **The martingale-kill lemma** (the exact first-order cross-term zero of the adapted
assembly): for `h` bounded and `𝓕_u`-measurable, `u ≤ v`,

  `𝔼[h·(M_v − M_u)] = 0`.

This is `integral_inner_sub_eq_zero` (a bounded predictable weight against a martingale
increment) at `F = ℝ`, for the martingale `martingale_M`. -/
theorem mul_trueIncr_expect_eq_zero {u v : ℝ≥0} (huv : u ≤ v)
    {h : Ω → ℝ} {Ch : ℝ}
    (hmadap : StronglyMeasurable[natFiltration hBmeas u] h)
    (hbdd : ∀ ω, |h ω| ≤ Ch) :
    ∫ ω, h ω * (M v ω - M u ω) ∂μ = 0 := by
  simpa only [Real.inner_apply] using
    integral_inner_sub_eq_zero (martingale_M hB hBmeas hD) huv hmadap
      (ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).le.trans (hbdd ω))

/-- **The increment-energy law** (the unweighted half of stage 3): for `u ≤ v ≤ T`,

  `𝔼[(M_v − M_u)²] = ∫_u^v 𝔼[δ_s²] ds`,

the energy of the Itô-integral increment over a time band is the predictable energy
of the band. Route: `M` agrees a.e. with the CLM process (`hD.ae_eq`), whose increment energy is the
band energy of the integrand (`clm_band_energy`), and the band-to-slice conversion of stage 2
(`bandIntegral_slice` at `δ²`) turns that into the slice integral. -/
theorem incrementEnergy {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
      = ∫ s in Set.Ioc u v, (∫ ω, δ s ω * δ s ω ∂μ)
          ∂ItoIntegralL2.timeMeasure := by
  set φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    processToLp T hBmeas hD.adapted hD.continuous hD.bdd with hφdef
  have hband : ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ s in Set.Ioc u v, (∫ ω, δ s ω * δ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
    have hcoe : ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω),
        (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω),
            Function.uncurry (fun s ω ↦ δ s ω * δ s ω) z
            ∂(trimMeasure_T (μ := μ) T hBmeas) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae
        (processToLp_coeFn T hBmeas hD.adapted hD.continuous hD.bdd)] with z hz
      show (φ : ℝ≥0 × Ω → ℝ) z ^ 2 = Function.uncurry (fun s ω ↦ δ s ω * δ s ω) z
      rw [hz, pow_two]
      rfl
    rw [hcoe, bandIntegral_slice hBmeas (μ := μ)
      (ψ := fun (t : ℝ≥0) (ω : Ω) ↦ δ t ω * δ t ω)
      (hψadap := fun t ↦ (hD.adapted t).mul (hD.adapted t))
      (hψcont := fun ω ↦ (hD.continuous ω).mul (hD.continuous ω))
      (hψbdd := fun s ω ↦ by
        rw [abs_mul]
        calc |δ s ω| * |δ s ω| ≤ Dd * |δ s ω| :=
              mul_le_mul_of_nonneg_right (hD.bdd s ω) (abs_nonneg _)
          _ ≤ Dd * Dd := mul_le_mul_of_nonneg_left (hD.bdd s ω)
              (le_trans (abs_nonneg _) (hD.bdd 0 ω)))
      u v hvT]
  rw [← hband, ← clm_band_energy hB hBmeas T φ huv hvT]
  refine integral_congr_ae ?_
  filter_upwards [hD.ae_eq u, hD.ae_eq v] with ω hu hv
  rw [hu, hv]

end AdaptedData

end MathFin.ItoDriftConditional
