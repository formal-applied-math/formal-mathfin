/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.ItoIntegralProcess
public import MathFin.Foundations.AdaptedProcessToLp
public import MathFin.Foundations.ItoIntegralL2
public import MathFin.Foundations.ItoIntegralCLM
public import MathFin.Foundations.ItoIntegralProcessL2Infinite
public import MathFin.Foundations.ItoIntegralLocality

/-! # Cross-horizon consistency of the CLM Itô integral

MathFin constructs the Itô integral per horizon: `itoIntegralCLM_T` and `itoProcessCLM`
live over `trimMeasure_T T`. Each finite horizon is related to the infinite-horizon process
(`ItoIntegralProcessL2Infinite.itoProcessL2Inf_eq_itoProcessCLM`), but there is no direct
lemma between two *finite* horizons. A process `M` that represents the CLM integral at
horizon `T` should represent it at *every* smaller horizon `τ ≤ T` — this module proves that
consistency directly, for the σ-realization `processToLp δ` of a bounded, adapted,
path-continuous `δ` in the process form:

* `itoProcessCLM_eq_terminal_of_ge` — the CLM process freezes at its horizon:
  `itoProcessCLM hB T t φ = itoIntegralCLM_T hB T hBmeas φ` for `t ≥ T` — the same
  `DenseRange.equalizer` argument as `itoProcessCLM_terminal_eq`, at `t ≥ T`;
* `itoIntegralCLM_cross_horizon` — **the consistency kernel**: an integrand carried by
  `(0,τ] × Ω` integrates to the *same* `L²` random variable at horizon `τ` and at
  horizon `T ≥ τ`. Both are the infinite-horizon integral of the integrand extended by zero
  (`itoIntegralCLM_T_eq_itoIntegralL2_bandExtend`), and the two extensions by zero are the same
  class of the same function (`bandExtend_toLp_ae_eq`);
* `itoProcessCLM_consist` — the process form: for `t ≤ τ ≤ T` the T-horizon CLM
  process of `processToLp δ` at `t` and the τ-horizon one agree (band-truncate the integrand
  to `(0,t]`, where `itoProcessCLM_eq_zero_of_vanishes_before` and
  `itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after` make the process value a
  terminal integral, then apply the kernel);
* `ae_eq_itoProcessCLM_of_le` / `ae_eq_itoProcessCLM_of_horizon_le` /
  `ae_eq_itoProcessCLM_min` — the horizon-consistency corollaries:
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
* `ae_eq_itoProcessCLM_of_le`, `ae_eq_itoProcessCLM_of_horizon_le`,
  `ae_eq_itoProcessCLM_min` — the horizon-consistency corollaries for
  a process `M` pinned to the T-horizon CLM integral by an a.e. `hMeq`.

`ItoFormulaAdaptedDriftConstructed` uses `ae_eq_itoProcessCLM_min` and
`itoProcessCLM_eq_terminal_of_ge` to state the integrated Itô–drift identity for the constructed
process at every time `τ ≤ T` of its horizon.

Supporting lemmas (the band truncation `bandIic` and its `L²` membership) are `private`.
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

Both are the infinite-horizon integral `itoIntegralL2` of the integrand extended by zero
(`itoIntegralCLM_T_eq_itoIntegralL2_bandExtend`), and the two extensions by zero are the same
class of the same function (`bandExtend_toLp_ae_eq`). -/
theorem itoIntegralCLM_cross_horizon (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {τ T : ℝ≥0} (hτT : τ ≤ T)
    {g : ℝ≥0 × Ω → ℝ} (hg0 : ∀ z : ℝ≥0 × Ω, τ < z.1 → g z = 0)
    (hgmτ : MemLp g 2 (trimMeasure_T (μ := μ) τ hBmeas))
    (hgmT : MemLp g 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoIntegralCLM_T hB τ hBmeas (hgmτ.toLp g) = itoIntegralCLM_T hB T hBmeas (hgmT.toLp g) := by
  rw [ItoIntegralProcessL2Infinite.itoIntegralCLM_T_eq_itoIntegralL2_bandExtend,
    ItoIntegralProcessL2Infinite.itoIntegralCLM_T_eq_itoIntegralL2_bandExtend]
  congr 1
  exact Lp.ext ((ItoIntegralProcessL2Infinite.bandExtend_toLp_ae_eq τ hBmeas hg0 hgmτ).trans
    (ItoIntegralProcessL2Infinite.bandExtend_toLp_ae_eq T hBmeas
      (fun z hz ↦ hg0 z (hτT.trans_lt hz)) hgmT).symm)

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
theorem ae_eq_itoProcessCLM_of_le (hB : IsPreBrownianReal B μ)
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
theorem ae_eq_itoProcessCLM_of_horizon_le (hB : IsPreBrownianReal B μ)
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
represents the τ-horizon CLM process at *every* time — at `t ≤ τ` by
`ae_eq_itoProcessCLM_of_le`, past
`τ` by the freeze law. -/
theorem ae_eq_itoProcessCLM_min (hB : IsPreBrownianReal B μ)
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
    exact ae_eq_itoProcessCLM_of_le hB hBmeas hδadap hδcont hδbdd hMeq hτT hle
  · rw [min_eq_right hge]
    exact ae_eq_itoProcessCLM_of_horizon_le hB hBmeas hδadap hδcont hδbdd hMeq hτT hge

end CrossHorizon

end MathFin
