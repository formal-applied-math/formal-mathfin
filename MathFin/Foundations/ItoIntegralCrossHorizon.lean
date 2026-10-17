/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.ItoIntegralProcess
public import MathFin.Foundations.AdaptedProcessToLp
public import MathFin.Foundations.ItoIntegralL2
public import MathFin.Foundations.ItoIntegralCLM
public import MathFin.Foundations.ItoIntegralLocality

/-! # Cross-horizon consistency of the CLM Itô integral

MathFin constructs the Itô integral per horizon: `itoIntegralCLM_T` and `itoProcessCLM`
live over `trimMeasure_T T`. Each finite horizon is related to the infinite-horizon process
(`ItoIntegralProcessL2Infinite.itoProcessL2Inf_eq_itoProcessCLM`), but there is no direct
lemma between two *finite* horizons. A process `M` that represents the CLM integral at
horizon `T` should represent it at *every* smaller horizon `τ ≤ T` — this module proves that
consistency directly, for the σ-realization `processToLp δ` of a bounded, adapted,
path-continuous `δ` in the process form:

* `eLpNorm_band_transfer` — the `L²` norm of a function carried by `(0,τ] × Ω` is the
  same in `trimMeasure_T τ` and `trimMeasure_T T` (both trims are the full predictable
  trim restricted to their time band; the support makes the band difference invisible
  up to the null bottom fibre `{0} × Ω`);
* `itoProcessCLM_eq_terminal_of_ge` — the CLM process freezes at its horizon:
  `itoProcessCLM hB T t φ = itoIntegralCLM_T hB T hBmeas φ` for `t ≥ T` — the same
  `DenseRange.equalizer` argument as `itoProcessCLM_terminal_eq`, at `t ≥ T`;
* `itoIntegralCLM_cross_horizon` — **the consistency kernel**: an integrand carried by
  `(0,τ] × Ω` integrates to the *same* `L²` random variable at horizon `τ` and at
  horizon `T ≥ τ`. Route: density of the τ-horizon simple embedding
  (`simpleAssembly_T_denseRange`) — for simple integrands both horizons return B1a's
  discrete sum `itoSimpleLp V` verbatim; the τ-dense approximants are `T`-bounded for
  free (endpoint bound transported by `τ ≤ T`), and their `L²(trim_T)` distance to the
  T-class equals their `L²(trim_τ)` distance to the τ-class by the band-transfer — so
  both CLM extensions are limits of the *same* sequence;
* `itoProcessCLM_consist` — the process form: for `t ≤ τ ≤ T` the T-horizon CLM
  process of `processToLp δ` at `t` and the τ-horizon one agree (band-truncate the integrand
  to `(0,t]`, where `itoProcessCLM_eq_zero_of_vanishes_before` and
  `itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after` make the process value a
  terminal integral, then apply the kernel);
* `mconsist` / `mconsist_frozen` / `mMeq_frozen` — the horizon-consistency corollaries:
  from the horizon-`T` pinning `hMeq : ∀ t, M t =ᵐ (φ●B)_t` alone, `M t` represents the
  CLM integral at every horizon `τ ≤ T` (at `t ≤ τ` directly; past `τ` the τ-horizon CLM
  is frozen, so `M τ` represents it at every `t ≥ τ`, and the frozen reversion
  `t ↦ M (min t τ)` represents it at every time).

## Result

Public API (all in `namespace MathFin`):

* `itoProcessCLM_eq_terminal_of_ge` — the CLM process freezes at its horizon:
  `itoProcessCLM hB T t φ = itoIntegralCLM_T hB T hBmeas φ` for `t ≥ T`;
* `itoIntegralCLM_cross_horizon` — the consistency kernel: an integrand carried by
  `(0, τ] × Ω` integrates to the *same* `L²` random variable at horizon `τ` and at
  horizon `T ≥ τ`;
* `itoProcessCLM_consist` — the process form: for the σ-realization `processToLp δ` of a
  bounded, adapted, path-continuous `δ`, the τ- and T-horizon CLM processes agree at every
  `t ≤ τ ≤ T`;
* `mconsist`, `mconsist_frozen`, `mMeq_frozen` — the horizon-consistency corollaries for
  a process `M` pinned to the T-horizon CLM integral by an a.e. `hMeq`.

Supporting lemmas (`eLpNorm_band_transfer` and the simple-embedding scaffolding) are
`private`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralProcess
open ItoIntegralL2 ItoIntegralCLM
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

section CrossHorizon

/-- **The `(0,t]`-band truncation** of an integrand on the time-stripe: `δ` inside the
band `(0,t] × Ω` (the bottom fibre included — it is null for every trim), zero outside. -/
private noncomputable def bandIic (δ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : ℝ≥0 × Ω) : ℝ :=
  Set.indicator (Set.Iic ↑t ×ˢ (Set.univ : Set Ω)) (Function.uncurry δ) z

private theorem bandIic_of_le {δ : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {z : ℝ≥0 × Ω} (hz : z.1 ≤ t) :
    bandIic δ t z = Function.uncurry δ z :=
  Set.indicator_of_mem (Set.mem_prod.mpr ⟨hz, Set.mem_univ _⟩) _

private theorem bandIic_of_gt {δ : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {z : ℝ≥0 × Ω} (hz : t < z.1) :
    bandIic δ t z = 0 :=
  Set.indicator_of_notMem (by rintro ⟨hle, -⟩; exact absurd hle (not_le.mpr hz)) _

/-- **`L²`-membership of the band truncation** in the σ-realization space at any horizon:
bounded (by `Dd`) and predictable-measurable — `Iic t ×ˢ univ` is the union of the basic
predictable band `Ioc 0 t ×ˢ univ` and the null bottom fibre `{0} ×ˢ univ`. The horizon
`σ` is irrelevant (the trim only serves as the measure). -/
private theorem memLp_bandIic (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    (t σ : ℝ≥0) :
    MemLp (bandIic δ t) 2 (trimMeasure_T (μ := μ) σ hBmeas) := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas with h𝓕
  have hunc : StronglyMeasurable[𝓕.predictable] (Function.uncurry δ) :=
    isStronglyPredictable_of_bdd_adapted_cont hBmeas hδadap hδcont
  have hband : MeasurableSet[𝓕.predictable] (Set.Iic ↑t ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Iic_prod (𝓕 := 𝓕)
      (s := (Set.univ : Set Ω)) (i := ↑t) MeasurableSet.univ
  have hsm : StronglyMeasurable[𝓕.predictable] (bandIic δ t) :=
    hunc.indicator hband
  refine MemLp.of_bound hsm.aestronglyMeasurable Dd (ae_of_all _ fun z ↦ ?_)
  rcases le_or_gt z.1 t with hle | hlt
  · rw [bandIic_of_le hle, Real.norm_eq_abs]
    exact hδbdd z.1 z.2
  · rw [bandIic_of_gt hlt, norm_zero]
    exact le_trans (abs_nonneg _) (hδbdd 0 z.2)

/-- **The `L²` band-transfer**: a function carried by `(0,τ] × Ω` has the same `L²` norm
in `trimMeasure_T τ` and in `trimMeasure_T T` for `τ ≤ T`. Both trims are the full
predictable trim restricted to their time band, and the support makes the band difference
invisible up to the null bottom fibre `{0} × Ω`. No measurability hypotheses needed. -/
private theorem eLpNorm_band_transfer (hBmeas : ∀ t, Measurable (B t))
    {τ T : ℝ≥0} (hτT : τ ≤ T) {h : ℝ≥0 × Ω → ℝ}
    (h0 : ∀ z : ℝ≥0 × Ω, τ < z.1 → h z = 0) :
    eLpNorm h 2 (trimMeasure_T (μ := μ) T hBmeas)
      = eLpNorm h 2 (trimMeasure_T (μ := μ) τ hBmeas) := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas with h𝓕
  -- the bottom fibre `{0} × Ω` is null for the full predictable trim
  have hbotnull : ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod)
      ({(⊥:ℝ≥0)} ×ˢ (Set.univ : Set Ω)) = 0 := by
    rw [MeasureTheory.trim_measurableSet_eq 𝓕.predictable_le_prod
      (MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕)
        (s := (Set.univ : Set Ω)) MeasurableSet.univ),
      Measure.prod_prod, ItoIntegralL2.timeMeasure_singleton, zero_mul]
  have haene0 : {z : ℝ≥0 × Ω | z.1 ≠ 0}
      ∈ MeasureTheory.ae ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) := by
    have hcompl : {z : ℝ≥0 × Ω | z.1 ≠ 0} = ({(⊥:ℝ≥0)} ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext ⟨t, ω⟩
      simp
    rw [hcompl]
    exact compl_mem_ae_iff.mpr hbotnull
  have hbandmeas : ∀ σ : ℝ≥0,
      MeasurableSet[𝓕.predictable] (Set.Ioc 0 σ ×ˢ (Set.univ : Set Ω)) :=
    fun σ ↦ MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 σ
      MeasurableSet.univ
  have hae : ∀ σ : ℝ≥0, τ ≤ σ →
      (Set.Ioc 0 σ ×ˢ (Set.univ : Set Ω)).indicator h
        =ᵐ[(ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod] h := by
    intro σ hστ
    filter_upwards [haene0] with z hz
    by_cases hzτ : τ < z.1
    · rw [h0 z hzτ]
      by_cases hzσ : z ∈ Set.Ioc 0 σ ×ˢ (Set.univ : Set Ω)
      · rw [Set.indicator_of_mem hzσ, h0 z hzτ]
      · rw [Set.indicator_of_notMem hzσ]
    · rw [Set.indicator_of_mem (by
        exact ⟨⟨pos_iff_ne_zero.mpr hz, (le_of_not_gt hzτ).trans hστ⟩,
          Set.mem_univ _⟩)]
  have key : ∀ σ : ℝ≥0, τ ≤ σ →
      eLpNorm h 2 (trimMeasure_T (μ := μ) σ hBmeas)
        = eLpNorm h 2 ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) := by
    intro σ hστ
    rw [trimMeasure_T_eq_restrict (μ := μ) σ hBmeas,
      ← eLpNorm_indicator_eq_eLpNorm_restrict (hbandmeas σ), eLpNorm_congr_ae (hae σ hστ)]
  rw [key T hτT, key τ le_rfl]

/-- **The CLM process freezes at its horizon.** For `t ≥ T` the general CLM integral
process `itoProcessCLM hB T t φ` equals the terminal integral `itoIntegralCLM_T φ`:
both are continuous-linear in the integrand and agree on the dense `simpleAssembly_T`
range, where the simple process has finished by `t` (`itoSimpleProcess_eq_itoSimple`). -/
theorem itoProcessCLM_eq_terminal_of_ge (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T t : ℝ≥0} (hTt : T ≤ t)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoProcessCLM hB T t hBmeas φ = itoIntegralCLM_T hB T hBmeas φ := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    (itoProcessCLM hB T t hBmeas).continuous (itoIntegralCLM_T hB T hBmeas).continuous
    (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T,
    itoIntegralCLM_T_simpleAssembly_T, itoSimpleProcessLp, itoSimpleLp,
    itoSimpleProcess_eq_itoSimple hBmeas V.val
      (fun p hp ↦ (V.property p hp).trans hTt)]

/-- **The cross-horizon consistency kernel.** An integrand carried by `(0,τ] × Ω`
integrates to the *same* `L²` random variable at horizon `τ` and at horizon `T ≥ τ`.

Route: density of the τ-horizon simple embedding (`simpleAssembly_T_denseRange`). For a
τ-bounded simple `V`, both horizons return B1a's discrete sum `itoSimpleLp V` verbatim
(the same `simpleAssembly` bridge at both horizons — the endpoints are `≤ τ ≤ T`, so the
T-embedding of the transport `W'` is the same integrand). The τ-dense approximants
transport to `T`-bounded integrands (`W'`), and their `L²(trim_T)` distance to the
T-class equals their `L²(trim_τ)` distance to the τ-class by `eLpNorm_band_transfer`
(the approximants vanish past `τ`), so the two CLM extensions are limits of the same
sequence. -/
theorem itoIntegralCLM_cross_horizon (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {τ T : ℝ≥0} (hτT : τ ≤ T)
    {g : ℝ≥0 × Ω → ℝ} (hg0 : ∀ z : ℝ≥0 × Ω, τ < z.1 → g z = 0)
    (hgmτ : MemLp g 2 (trimMeasure_T (μ := μ) τ hBmeas))
    (hgmT : MemLp g 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoIntegralCLM_T hB τ hBmeas (hgmτ.toLp g) = itoIntegralCLM_T hB T hBmeas (hgmT.toLp g) := by
  classical
  set qτ := MemLp.toLp g hgmτ with hqτ
  set qT := MemLp.toLp g hgmT with hqT
  -- τ-dense simple approximants of the τ-class
  obtain ⟨gn, hg_range, hg_lim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssembly_T_denseRange (μ := μ) τ hBmeas).closure_range.ge (Set.mem_univ qτ))
  choose W hW using hg_range
  -- transport of a τ-bounded simple process to a T-bounded one (same integrand)
  set W' : ℕ → TBoundedSP T hBmeas :=
    fun n ↦ ⟨(W n).val, fun p hp ↦ (W n).property p hp |>.trans hτT⟩ with hW'
  -- both sides' error norms coincide (the approximants vanish past `τ`)
  have hnormeq : ∀ n : ℕ,
      ‖(simpleAssembly_T (μ := μ) T hBmeas (W' n) - qT
          : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
      = ‖((gn n : Lp ℝ 2 (trimMeasure_T (μ := μ) τ hBmeas)) - qτ
          : Lp ℝ 2 (trimMeasure_T (μ := μ) τ hBmeas))‖ := by
    intro n
    have hcoeT : ⇑(simpleAssembly_T (μ := μ) T hBmeas (W' n))
        =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry ⇑(W n).val := by
      have hdef : simpleAssembly_T (μ := μ) T hBmeas (W' n)
          = (memLp_uncurry_trim_T (μ := μ) T hBmeas (W' n).val).toLp
            (Function.uncurry ⇑(W' n).val) := rfl
      rw [hdef]
      exact (memLp_uncurry_trim_T (μ := μ) T hBmeas (W' n).val).coeFn_toLp
    have hcoeτ : ⇑(simpleAssembly_T (μ := μ) τ hBmeas (W n))
        =ᵐ[trimMeasure_T (μ := μ) τ hBmeas] Function.uncurry ⇑(W n).val := by
      have hdef : simpleAssembly_T (μ := μ) τ hBmeas (W n)
          = (memLp_uncurry_trim_T (μ := μ) τ hBmeas (W n).val).toLp
            (Function.uncurry ⇑(W n).val) := rfl
      rw [hdef]
      exact (memLp_uncurry_trim_T (μ := μ) τ hBmeas (W n).val).coeFn_toLp
    have h1 : ⇑(simpleAssembly_T (μ := μ) T hBmeas (W' n) - qT)
        =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
          (fun z : ℝ≥0 × Ω ↦ Function.uncurry ⇑(W n).val z - g z) := by
      have hstep1 : ⇑(simpleAssembly_T (μ := μ) T hBmeas (W' n) - qT)
          =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
            (⇑(simpleAssembly_T (μ := μ) T hBmeas (W' n)) - ⇑qT) := Lp.coeFn_sub _ _
      have hstep2 : (⇑(simpleAssembly_T (μ := μ) T hBmeas (W' n)) - ⇑qT)
          =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
            (fun z : ℝ≥0 × Ω ↦ Function.uncurry ⇑(W n).val z - g z) := by
        filter_upwards [hcoeT, MemLp.coeFn_toLp hgmT] with z hc hq
        simp only [hqT, hc, hq, Pi.sub_apply]
      exact hstep1.trans hstep2
    have h2 : ⇑((gn n : Lp ℝ 2 (trimMeasure_T (μ := μ) τ hBmeas)) - qτ)
        =ᵐ[trimMeasure_T (μ := μ) τ hBmeas]
          (fun z : ℝ≥0 × Ω ↦ Function.uncurry ⇑(W n).val z - g z) := by
      have hstep1 : ⇑((gn n : Lp ℝ 2 (trimMeasure_T (μ := μ) τ hBmeas)) - qτ)
          =ᵐ[trimMeasure_T (μ := μ) τ hBmeas]
            (⇑(simpleAssembly_T (μ := μ) τ hBmeas (W n)) - ⇑qτ) := by
        rw [← hW n]
        exact Lp.coeFn_sub _ _
      have hstep2 : (⇑(simpleAssembly_T (μ := μ) τ hBmeas (W n)) - ⇑qτ)
          =ᵐ[trimMeasure_T (μ := μ) τ hBmeas]
            (fun z : ℝ≥0 × Ω ↦ Function.uncurry ⇑(W n).val z - g z) := by
        filter_upwards [hcoeτ, MemLp.coeFn_toLp hgmτ] with z hc hq
        simp only [hqτ, hc, hq, Pi.sub_apply]
      exact hstep1.trans hstep2
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae h1, eLpNorm_congr_ae h2]
    refine congrArg ENNReal.toReal (eLpNorm_band_transfer hBmeas hτT fun z hz ↦ ?_)
    have hW0 : Function.uncurry ⇑(W n).val z = 0 :=
      uncurry_eq_zero_of_lt (T := τ) (hBmeas := hBmeas) (V := W n)
        (t := z.1) (ht := hz) z.2
    simp only [hW0, hg0 z hz, sub_self]
  -- the T-side approximants converge to the T-class
  have hnormT : Tendsto (fun n ↦ ‖(simpleAssembly_T (μ := μ) T hBmeas (W' n) - qT
      : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖) atTop (𝓝 0) := by
    have hτn := tendsto_iff_norm_sub_tendsto_zero.mp hg_lim
    have hpt : (fun n ↦ ‖((gn n : Lp ℝ 2 (trimMeasure_T (μ := μ) τ hBmeas))
            - qτ : Lp ℝ 2 (trimMeasure_T (μ := μ) τ hBmeas))‖)
        = (fun n ↦ ‖(simpleAssembly_T (μ := μ) T hBmeas (W' n) - qT
          : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖) := funext fun n ↦ (hnormeq n).symm
    rw [hpt] at hτn
    exact hτn
  have hWTendsto : Tendsto (fun n ↦ (simpleAssembly_T (μ := μ) T hBmeas (W' n) :
      Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))) atTop (𝓝 qT) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnormT
  -- on the approximants both CLMs return the same discrete Itô sum
  have hval : ∀ n : ℕ,
      itoIntegralCLM_T hB T hBmeas (simpleAssembly_T (μ := μ) T hBmeas (W' n))
        = itoIntegralCLM_T hB τ hBmeas (gn n) := by
    intro n
    rw [← hW n, itoIntegralCLM_T_simpleAssembly_T hB T hBmeas (W' n),
      itoIntegralCLM_T_simpleAssembly_T hB τ hBmeas (W n)]
  -- uniqueness of limits
  have hlimT : Tendsto (fun n ↦ itoIntegralCLM_T hB T hBmeas
      (simpleAssembly_T (μ := μ) T hBmeas (W' n))) atTop
      (𝓝 (itoIntegralCLM_T hB T hBmeas qT)) :=
    ((itoIntegralCLM_T hB T hBmeas).continuous.tendsto qT).comp hWTendsto
  have hlimτ : Tendsto (fun n ↦ itoIntegralCLM_T hB τ hBmeas (gn n)) atTop
      (𝓝 (itoIntegralCLM_T hB τ hBmeas qτ)) :=
    ((itoIntegralCLM_T hB τ hBmeas).continuous.tendsto qτ).comp hg_lim
  rw [funext hval] at hlimT
  exact (tendsto_nhds_unique hlimT hlimτ).symm

/-- **Cross-horizon consistency of the CLM process**: for the σ-realization `processToLp δ`
of a bounded, adapted, path-continuous `δ` and `t ≤ τ ≤ T`, the T-horizon CLM process at `t`
and the τ-horizon CLM process at `t` agree as `L²` random variables.
Route: band-truncate the integrand to `(0,t]` — `itoProcessCLM_eq_zero_of_vanishes_before`
kills the band tail in the process value and
`itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after` makes the truncated process value a
terminal integral — then apply the cross-horizon kernel. -/
theorem itoProcessCLM_consist (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {t τ T : ℝ≥0} (htτ : t ≤ τ) (hτT : τ ≤ T)
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) :
    (itoProcessCLM hB T t hBmeas (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)
      = (itoProcessCLM hB τ t hBmeas (processToLp τ hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) := by
  classical
  have hmemσ : ∀ σ : ℝ≥0, MemLp (bandIic δ t) 2 (trimMeasure_T (μ := μ) σ hBmeas) :=
    fun σ ↦ memLp_bandIic hBmeas hδadap hδcont hδbdd t σ
  -- the process value at `t` only sees the `(0,t]` band of the integrand
  have hband : ∀ σ : ℝ≥0, t ≤ σ →
      itoProcessCLM hB σ t hBmeas (processToLp σ hBmeas hδadap hδcont hδbdd)
        = itoIntegralCLM_T hB σ hBmeas (MemLp.toLp (bandIic δ t) (hmemσ σ)) := by
    intro σ hσ
    have hzero : itoProcessCLM hB σ t hBmeas ((processToLp σ hBmeas hδadap hδcont hδbdd
        - MemLp.toLp (bandIic δ t) (hmemσ σ) :
          Lp ℝ 2 (trimMeasure_T (μ := μ) σ hBmeas))) = 0 := by
      refine itoProcessCLM_eq_zero_of_vanishes_before hB σ t hσ hBmeas
        (processToLp σ hBmeas hδadap hδcont hδbdd
          - MemLp.toLp (bandIic δ t) (hmemσ σ)) ?_
      filter_upwards [processToLp_coeFn σ hBmeas hδadap hδcont hδbdd,
        Lp.coeFn_sub (processToLp σ hBmeas hδadap hδcont hδbdd)
          (MemLp.toLp (bandIic δ t) (hmemσ σ)), MemLp.coeFn_toLp (hmemσ σ)]
        with p hp1 hp2 hp3 hp4
      simp only [hp2, hp1, hp3, Pi.sub_apply, bandIic_of_le hp4, sub_self]
    have hsplit := map_sub (itoProcessCLM hB σ t hBmeas)
      (processToLp σ hBmeas hδadap hδcont hδbdd) (MemLp.toLp (bandIic δ t) (hmemσ σ))
    rw [hzero, eq_comm, sub_eq_zero] at hsplit
    have hvanish : ∀ᵐ p ∂(trimMeasure_T (μ := μ) σ hBmeas), t < p.1 →
        MemLp.toLp (bandIic δ t) (hmemσ σ) p = 0 := by
      filter_upwards [MemLp.coeFn_toLp (hmemσ σ)] with p hp hpt
      rw [hp, bandIic_of_gt hpt]
    have hterm := itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after hB σ t hσ hBmeas
      (MemLp.toLp (bandIic δ t) (hmemσ σ)) hvanish
    rw [hsplit, ← hterm]
  calc (itoProcessCLM hB T t hBmeas (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)
      = itoIntegralCLM_T hB T hBmeas (MemLp.toLp (bandIic δ t) (hmemσ T)) :=
        hband T (htτ.trans hτT)
    _ = itoIntegralCLM_T hB τ hBmeas (MemLp.toLp (bandIic δ t) (hmemσ τ)) :=
        (itoIntegralCLM_cross_horizon hB hBmeas hτT
          (fun z hz ↦ bandIic_of_gt (lt_of_le_of_lt htτ hz)) (hmemσ τ) (hmemσ T)).symm
    _ = (itoProcessCLM hB τ t hBmeas (processToLp τ hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) :=
        (hband τ htτ).symm

/-- **The horizon-consistency corollary**: from the horizon-`T` pinning
`hMeq : ∀ t, M t =ᵐ (φ●B)_t` alone, `M t` represents the CLM Itô integral of `δ` at
every horizon `τ ≤ T` and every time `t ≤ τ`. -/
theorem mconsist (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {τ : ℝ≥0} (hτT : τ ≤ T) {t : ℝ≥0} (htτ : t ≤ τ) :
    M t =ᵐ[μ] (itoProcessCLM hB τ t hBmeas
      (processToLp τ hBmeas hδadap hδcont hδbdd) : Ω → ℝ) := by
  have hLp := itoProcessCLM_consist hB hBmeas htτ hτT hδadap hδcont hδbdd
  exact (hMeq t).trans (Eventually.of_forall
    (congrFun (congrArg (fun z : Lp ℝ 2 μ ↦ (z : Ω → ℝ)) hLp)))

/-- **The frozen corollary**: past the horizon the CLM process freezes
(`itoProcessCLM_eq_terminal_of_ge`), so `M τ` represents the τ-horizon CLM integral at
*every* time `t ≥ τ`. -/
theorem mconsist_frozen (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {τ t : ℝ≥0} (hτT : τ ≤ T) (hτt : τ ≤ t) :
    M τ =ᵐ[μ] (itoProcessCLM hB τ t hBmeas
      (processToLp τ hBmeas hδadap hδcont hδbdd) : Ω → ℝ) := by
  have hLp := itoProcessCLM_consist hB hBmeas (le_refl τ) hτT hδadap hδcont hδbdd
  have hfrz : (itoProcessCLM hB τ t hBmeas
        (processToLp τ hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)
      = (itoProcessCLM hB τ τ hBmeas
        (processToLp τ hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) := by
    rw [itoProcessCLM_eq_terminal_of_ge hB hBmeas hτt, itoProcessCLM_terminal_eq]
  exact (hMeq τ).trans (Eventually.of_forall
    (congrFun (congrArg (fun z : Lp ℝ 2 μ ↦ (z : Ω → ℝ)) (hLp.trans hfrz.symm))))

/-- **The frozen-reversion corollary**: the time-frozen reversion `t ↦ M (min t τ)`
represents the τ-horizon CLM process at *every* time — at `t ≤ τ` by `mconsist`, past
`τ` by the freeze law. -/
theorem mMeq_frozen (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    (τ : ℝ≥0) (hτT : τ ≤ T) :
    ∀ t : ℝ≥0, M (min t τ) =ᵐ[μ] (itoProcessCLM hB τ t hBmeas
      (processToLp τ hBmeas hδadap hδcont hδbdd) : Ω → ℝ) := by
  intro t
  rcases le_total t τ with hle | hge
  · rw [min_eq_left hle]
    exact mconsist hB hBmeas hδadap hδcont hδbdd hMeq hτT hle
  · rw [min_eq_right hge]
    exact mconsist_frozen hB hBmeas hδadap hδcont hδbdd hMeq hτT hge

end CrossHorizon

end MathFin
