/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy

/-! # The weighted increment isometry of an adapted Itô integral (the discrete route, stage 4)

The per-cell weighted second-moment identity `weightedCellSq_step` on the left-endpoint step
approximants, the band energy of the CLM process (`clm_band_energy`), the mean-function Riemann
limit `frozenRiemann_tendsto`, and the summed weighted increment isometry
`quadraticSqSum_tendsto` (with its gap hypothesis `hgap`, discharged in `ItoDriftGapDecay`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! #### Stage 4 — the weighted increment isometry (per-cell step identification, the
gap decay, and the summed isometry)

The route: for the left-endpoint step approximant `δⁿ` of `δ`
on the uniform partition, the per-cell increment of the approximant process is the single
rectangle `δ(tₖ)·ΔBₖ` (min-algebra on `itoSimpleProcess_apply`), so the weighted
second-moment identity on the approximant is the independence isometry kernel
`integral_adapted_mul_increment_sq` at `χ = wₖ·δ(tₖ)²`; the true increment decomposes as
`ΔMₖ = δ(tₖ)ΔBₖ + δεₖ` with `δεₖ` the band-restricted CLM increment of the integrand
error `φ − δⁿ`, whose `L²` norm is exactly the cell band energy (`clm_band_energy`),
and Cauchy–Schwarz pairs each cell band with the cell energy. Summing kills the gap at
rate `√T·‖δ − δⁿ‖_{L²(trim)} → 0` (`deltaStepLp_tendsto`). -/

section StageFour

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Real `L²` pairing bound: `∫ |f g| ≤ ‖f‖₂·‖g‖₂` (Hölder at exponents `2, 2`). -/
theorem integral_abs_mul_le_L2L2 {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, |f ω * g ω| ∂μ
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf' : MemLp |f| (ENNReal.ofReal 2) μ := by simpa using hf.abs
  have hg' : MemLp |g| (ENNReal.ofReal 2) μ := by simpa using hg.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hp
    (f := fun ω ↦ |f ω|) (g := fun ω ↦ |g ω|)
    (ae_of_all μ fun ω ↦ abs_nonneg _) (ae_of_all μ fun ω ↦ abs_nonneg _)
    hf' hg'
  have h2f : ∫ a, |f a| ^ (2 : ℝ) ∂μ = ∫ a, f a ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    change |f a| ^ (2 : ℝ) = f a ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have h2g : ∫ a, |g a| ^ (2 : ℝ) ∂μ = ∫ a, g a ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    change |g a| ^ (2 : ℝ) = g a ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h2f, h2g] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hfin : ∫ a, |f a| * |g a| ∂μ = ∫ a, |f a * g a| ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    change |f a| * |g a| = |f a * g a|
    rw [abs_mul]
  rw [hfin] at h
  exact h

/-- The process-level elementary Itô integral is additive over finite sums of simple
processes (the `itoSimpleProcess` analogue of `ItoIntegralBrownian.itoSimple_sum`). -/
private lemma itoSimpleProcess_finsetSum {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {ι' : Type*} (s : Finset ι') (V : ι' → SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (∑ i ∈ s, V i) t = ∑ i ∈ s, itoSimpleProcess hBmeas (V i) t := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimpleProcess]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimpleProcess_add, ih]

/-- A single bounded adapted step evaluated at an arbitrary time is the coefficient times
the truncated increment. -/
private lemma itoSimpleProcess_stepSP_apply {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {T a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[natFiltration hBmeas a] φ) {Mφ : ℝ} (hφM : ∀ ω, |φ ω| ≤ Mφ)
    (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas (stepSP hBmeas hab hbT hφ hφM).val t ω
      = φ ω * (B (min b t) ω - B (min a t) ω) := by
  rw [itoSimpleProcess_apply]
  change (Finsupp.single (a, b) φ).sum (fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω)) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- **Per-cell step identification** (min-algebra): over cell `k` of the uniform partition,
the `n`-step left-endpoint step process increments by exactly the single rectangle
`δ(tₖ)·(B_{tₖ₊₁} − B_{tₖ})` — every other cell telescopes to zero and the diagonal cell
is untruncated. -/
lemma itoSimpleProcess_stepσ_incr {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) (T : ℝ≥0) {n k : ℕ} (hk : k < n) (ω : Ω) :
    itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val (unifPart T n (k + 1)) ω
        - itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val (unifPart T n k) ω
      = δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) := by
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  set t : ℕ → ℝ≥0 := unifPart T n with ht
  -- both process values as sums of per-cell single-rectangle evaluations
  have hstepval : ∀ t' : ℝ≥0,
      itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val t' ω
        = ∑ j ∈ (Finset.range n).attach,
            δ (t j.1) ω * (B (min (t (j.1 + 1)) t') ω - B (min (t j.1) t') ω) := by
    intro t'
    rw [stepσ, AddSubmonoidClass.coe_finsetSum, itoSimpleProcess_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [itoSimpleProcess_stepSP_apply hBmeas (unifPart_mono T n (Nat.le_succ j.1))
      (unifPart_le_T (Finset.mem_range.mp j.2)) (hδadap (t j.1)).measurable]
  rw [hstepval, hstepval, ← Finset.sum_sub_distrib]
  have hzero : ∀ j ∈ (Finset.range n).attach,
      j ≠ ⟨k, Finset.mem_range.mpr hk⟩ →
        δ (t ↑j) ω * (B (min (t (↑j + 1)) (t (k + 1))) ω - B (min (t ↑j) (t (k + 1))) ω)
          - δ (t ↑j) ω * (B (min (t (↑j + 1)) (t k)) ω - B (min (t ↑j) (t k)) ω) = 0 := by
    rintro j _ hj
    have hjk : (j : ℕ) ≠ k := fun h ↦ hj (Subtype.ext h)
    by_cases hlt : (j : ℕ) < k
    · have h1 : min (t ((j : ℕ) + 1)) (t (k + 1)) = t ((j : ℕ) + 1) :=
        min_eq_left (hmono (by omega))
      have h2 : min (t (j : ℕ)) (t (k + 1)) = t (j : ℕ) := min_eq_left (hmono (by omega))
      have h3 : min (t ((j : ℕ) + 1)) (t k) = t ((j : ℕ) + 1) := min_eq_left (hmono (by omega))
      have h4 : min (t (j : ℕ)) (t k) = t (j : ℕ) := min_eq_left (hmono (by omega))
      rw [h1, h2, h3, h4]; ring
    · have h1 : min (t ((j : ℕ) + 1)) (t (k + 1)) = t (k + 1) :=
        min_eq_right (hmono (by omega))
      have h2 : min (t (j : ℕ)) (t (k + 1)) = t (k + 1) := min_eq_right (hmono (by omega))
      have h3 : min (t ((j : ℕ) + 1)) (t k) = t k := min_eq_right (hmono (by omega))
      have h4 : min (t (j : ℕ)) (t k) = t k := min_eq_right (hmono (by omega))
      rw [h1, h2, h3, h4]; ring
  rw [Finset.sum_eq_single_of_mem (f := fun j : {x // x ∈ Finset.range n} ↦
      δ (t j.1) ω * (B (min (t (j.1 + 1)) (t (k + 1))) ω - B (min (t j.1) (t (k + 1))) ω)
        - δ (t j.1) ω * (B (min (t (j.1 + 1)) (t k)) ω - B (min (t j.1) (t k)) ω))
    (⟨k, Finset.mem_range.mpr hk⟩) (Finset.mem_attach _ _) hzero]
  change δ (t k) ω * (B (min (t (k + 1)) (t (k + 1))) ω - B (min (t k) (t (k + 1))) ω)
      - δ (t k) ω * (B (min (t (k + 1)) (t k)) ω - B (min (t k) (t k)) ω)
    = δ (t k) ω * (B (t (k + 1)) ω - B (t k) ω)
  rw [min_self, min_self,
    min_eq_left (hmono (Nat.le_succ k)), min_eq_right (hmono (Nat.le_succ k))]
  ring

/-- **The CLM band-energy law**: the `L²` energy of the increment of the CLM Itô-integral
process of an arbitrary integrand class `φ'` over a band `(u,v]` is the band energy of the
integrand — the version-free analogue of `incrementEnergy`, proved directly at the CLM
level (the a.e. pull-out for the martingale cross term, the time-indexed isometry
`itoProcessCLM_norm_sq`, and the nested-band split). -/
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
        = ‖itoProcessCLM hB T w hBmeas φ'‖ ^ 2 := sqIntegral_of_Lp _
      _ = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := itoProcessCLM_norm_sq hB hwT hBmeas φ'
  have hint : Integrable (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp φ').integrable_sq
  have hintU : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hintUV : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hdisj : Disjoint
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) :=
    Set.disjoint_left.2 fun a ha hb ↦ by
      have h1 : (u : ℝ) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
      have h2 : (a.1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast ha.1.2
      linarith
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

end StageFour

/-! #### Stage 4 (headline) — the per-cell weighted identity, the gap decay, and the
summed weighted increment isometry -/

section StageFourB

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The uniform-partition band split: the `(0,T]`-band integral of an integrable
space-time function is the sum of its uniform cell integrals (iterated
`setIntegral_union` over the nested left endpoints). -/
lemma uniform_band_split (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {n : ℕ}
    (hn : 0 < n) {F : ℝ≥0 × Ω → ℝ}
    (hFint : Integrable F (trimMeasure_T (μ := μ) T hBmeas)) :
    ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω), F z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∑ k ∈ Finset.range n,
          ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
            F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  have hTn : unifPart T n n = T := unifPart_self T hn.ne'
  have hintOn : ∀ m : ℕ, m ≤ n →
      IntegrableOn F ((Set.Ioc (0:ℝ≥0) (unifPart T n m)) ×ˢ (Set.univ : Set Ω))
        (trimMeasure_T (μ := μ) T hBmeas) := by
    intro m hm
    exact hFint.mono_measure (Measure.restrict_le_self)
  have key : ∀ m : ℕ, 0 < m → m ≤ n →
      ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω), F z
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∑ k ∈ Finset.range m,
            ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
              F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro m
    induction m with
    | zero => intro hm; exact absurd hm (Nat.not_lt_zero 0)
    | succ m ih =>
      intro hm hmT
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        rw [Finset.range_one, Finset.sum_singleton, unifPart_zero]
      · have hmt : unifPart T n m ≤ unifPart T n (m + 1) :=
          unifPart_mono T n (Nat.le_succ m)
        have hunion : (Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω))
            ∪ (Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω))
            = (Set.Ioc (0:ℝ≥0) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω) := by
          rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc
            zero_le hmt]
        have hdisj : Disjoint
            ((Set.Ioc (0:ℝ≥0) (unifPart T n m)) ×ˢ (Set.univ : Set Ω))
            ((Set.Ioc (unifPart T n m) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω)) :=
          Set.disjoint_left.2 fun a ha hb ↦ by
            have h1 : ((unifPart T n m : ℝ)) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
            have h2 : (a.1 : ℝ) ≤ ((unifPart T n m : ℝ)) := by exact_mod_cast ha.1.2
            linarith
        have hintV : IntegrableOn F
            ((Set.Ioc (unifPart T n m) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω))
            (trimMeasure_T (μ := μ) T hBmeas) := by
          exact hFint.mono_measure (Measure.restrict_le_self)
        calc ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω), F z
              ∂(trimMeasure_T (μ := μ) T hBmeas)
            = ∫ z in (Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω))
                ∪ (Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω)),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by rw [hunion]
          _ = ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω), F z
                ∂(trimMeasure_T (μ := μ) T hBmeas)
              + ∫ z in Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) :=
              setIntegral_union hdisj
                (MeasureTheory.measurableSet_predictable_Ioc_prod (unifPart T n m)
                  (unifPart T n (m + 1)) MeasurableSet.univ)
                (hintOn m (by omega)) hintV
          _ = ∑ k ∈ Finset.range m,
                ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  F z ∂(trimMeasure_T (μ := μ) T hBmeas)
              + ∫ z in Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
              rw [ih hm0 (by omega)]
          _ = ∑ k ∈ Finset.range (m + 1),
                ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  F z ∂(trimMeasure_T (μ := μ) T hBmeas) := (Finset.sum_range_succ _ m).symm
  have hkey := key n hn (le_refl n)
  rw [hTn] at hkey
  exact hkey

/-- **Per-cell step identification at CLM level**: the increment over cell `k` of the
uniform partition of the step-approximant CLM process is a.e. the single rectangle
`δ(tₖ)·ΔBₖ`. -/
theorem stepIncr_stepCLM_ae (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) {n k : ℕ} (hk : k < n) :
    (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω)
      =ᵐ[μ] (fun ω ↦ δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) := by
  have hcoe : ∀ t : ℝ≥0,
      (itoProcessCLM hB T t hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ)
        =ᵐ[μ] itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val t := by
    intro t
    rw [itoProcessCLM_simpleAssembly_T hB T t hBmeas (stepσ hBmeas hδadap hδbdd T n)]
    exact (memLp_itoSimpleProcess hB hBmeas (stepσ hBmeas hδadap hδbdd T n).val t).coeFn_toLp
  filter_upwards [hcoe (unifPart T n (k + 1)), hcoe (unifPart T n k)] with ω h2 h3
  show (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
    = δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
  rw [h2, h3, itoSimpleProcess_stepσ_incr hBmeas hδadap hδbdd T hk ω]

omit [IsProbabilityMeasure μ] in
/-- **The per-cell weighted identity** (the stage-4 core): for an `𝓕_{tₖ}`-measurable
weight `w`, the weighted second moment of the single rectangle `δ(tₖ)·ΔBₖ` is the frozen
rectangle energy `𝔼[w·δ(tₖ)²]·(tₖ₊₁ − tₖ)` — the isometry kernel
`integral_adapted_mul_increment_sq` at `χ = w·δ(tₖ)²` (`𝓕_{tₖ}`-measurable as a product of
`𝓕_{tₖ}`-measurable factors). -/
theorem weightedCellSq_step {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    {n k : ℕ} {w : Ω → ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w) :
    ∫ ω, w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = (∫ ω, w ω * δ (unifPart T n k) ω ^ 2 ∂μ)
        * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
  have hcongr : (fun ω ↦ w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2)
      =ᵐ[μ] (fun ω ↦ (w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω))
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) := by
    filter_upwards [] with ω
    show w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 = _
    ring
  have hχ : Measurable[natFiltration hBmeas (unifPart T n k)]
      (fun ω ↦ w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω)) :=
    hwm.mul ((hδadap (unifPart T n k)).measurable.mul (hδadap (unifPart T n k)).measurable)
  have hcongr2 : (∫ ω, w ω * δ (unifPart T n k) ω ^ 2 ∂μ)
      = ∫ ω, w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by
      change w ω * δ (unifPart T n k) ω ^ 2 = _
      rw [pow_two])
  rw [integral_congr_ae hcongr, hcongr2]
  exact integral_adapted_mul_increment_sq (hB.isFilteredPreBrownian hBmeas)
    (unifPart_mono T n (Nat.le_succ k)) hχ

end StageFourB

/-! #### Stage 4 (headline) — the gap decay, the summed weighted increment isometry,
and the convergence of the quadratic block -/

section StageFourC

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))

omit hB in
/-- The mean function of a bounded measurable family with almost surely continuous paths is
continuous (the stage-1 DCT interchange, factored out). -/
lemma continuous_mean_of_bdd_cont {g : ℝ≥0 → Ω → ℝ}
    (hgmeas : ∀ s, Measurable (g s)) (hgcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ g s ω)
    {C : ℝ} (hgbdd : ∀ s ω, |g s ω| ≤ C) :
    Continuous fun s : ℝ≥0 ↦ ∫ ω, g s ω ∂μ :=
  continuous_iff_continuousAt.mpr fun s₀ ↦
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : Ω ↦ C)
      (Eventually.of_forall fun s ↦ (hgmeas s).aestronglyMeasurable)
      (Eventually.of_forall fun s ↦ Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using hgbdd s ω)
      (integrable_const C)
      (hgcont.mono fun _ h ↦ h.continuousAt)

omit hB in
/-- `expectation_pathIntegral_eq` (`ItoDriftExpectation`) for a bounded measurable family whose
paths are continuous only almost surely: set the family to `0` on a measurable null set
containing every discontinuous path, apply the everywhere-continuous version, and undo the
change on both sides (it alters each integrand on a null set only). -/
lemma expectation_pathIntegral_eq_of_ae {w : ℝ≥0 → Ω → ℝ}
    (hw_meas : ∀ s, Measurable (w s)) (hw_cont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    ∫ ω, (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  obtain ⟨t, hbad, ht, hμt⟩ := exists_measurable_superset_of_null (ae_iff.1 hw_cont)
  have hgood : ∀ᵐ ω ∂μ, ω ∈ tᶜ := measure_eq_zero_iff_ae_notMem.1 hμt
  have hw'_cont (ω : Ω) : Continuous fun s ↦ tᶜ.indicator (w s) ω := by
    by_cases hω : ω ∈ t
    · simp only [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
      exact continuous_const
    · simp only [Set.indicator_of_mem (Set.mem_compl hω)]
      exact Classical.byContradiction fun h ↦ hω (hbad h)
  have hw'_bdd (s : ℝ≥0) (ω : Ω) : |tᶜ.indicator (w s) ω| ≤ C := by
    by_cases hω : ω ∈ tᶜ
    · rw [Set.indicator_of_mem hω]
      exact hw_bdd s ω
    · rw [Set.indicator_of_notMem hω, abs_zero]
      exact hC0
  calc ∫ ω, (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ ω, (∫ s in Set.Ioc 0 T, tᶜ.indicator (w s) ω ∂ItoIntegralL2.timeMeasure) ∂μ :=
        integral_congr_ae (hgood.mono fun ω hω ↦ by simp only [Set.indicator_of_mem hω])
    _ = ∫ s in Set.Ioc 0 T, (∫ ω, tᶜ.indicator (w s) ω ∂μ) ∂ItoIntegralL2.timeMeasure :=
        expectation_pathIntegral_eq (w := fun s ↦ tᶜ.indicator (w s))
          (fun s ↦ (hw_meas s).indicator ht.compl) hw'_cont hC0 hw'_bdd T
    _ = ∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure :=
        setIntegral_congr_fun measurableSet_Ioc fun s _ ↦
          integral_congr_ae (hgood.mono fun ω hω ↦ by simp only [Set.indicator_of_mem hω])

omit hB in
/-- **The frozen Riemann convergence**: the left-endpoint Riemann sums of the deterministic
mean function of a bounded measurable family with almost surely continuous paths converge to
the time integral of the means (the deterministic `tendsto_riemann_continuous` applied to the
mean function). -/
theorem frozenRiemann_tendsto {g : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hgmeas : ∀ s, Measurable (g s)) (hgcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ g s ω)
    {C : ℝ} (hgbdd : ∀ s ω, |g s ω| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        (∫ ω, g (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hmeanbdd : ∀ s : ℝ≥0, |∫ ω, g s ω ∂μ| ≤ C := fun s ↦ by
    calc |∫ ω, g s ω ∂μ| ≤ ∫ ω, |g s ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ abs_nonneg _)
          (integrable_const C)
          (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hgbdd s ω)
      _ = C := by rw [integral_const]; simp
  exact tendsto_riemann_continuous (continuous_mean_of_bdd_cont hgmeas hgcont hgbdd) T
    (fun s _ ↦ hmeanbdd s)

variable {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

/-- The energy of the true increment: `𝔼[(M_v − M_u)²] ≤ D_δ²·(v−u)` for `u ≤ v ≤ T`
(`incrementEnergy` plus the pointwise `δ`-bound on the mean function). -/
theorem trueIncr_sq_le {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, (M v ω - M u ω) ^ 2 ∂μ ≤ Dd ^ 2 * ((v : ℝ) - u) := by
  rw [incrementEnergy hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv hvT]
  have hgmeas : ∀ s : ℝ≥0, Measurable (fun ω ↦ δ s ω * δ s ω) :=
    fun s ↦ (((hδadap s).measurable.mul (hδadap s).measurable).mono
      ((natFiltration hBmeas).le s) le_rfl)
  have hgcont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ δ s ω * δ s ω :=
    fun ω ↦ (hδcont ω).mul (hδcont ω)
  have hDsq2 : |Dd| * |Dd| = Dd * Dd := by
    rcases le_total 0 Dd with h | h
    · rw [abs_of_nonneg h]
    · rcases eq_or_lt_of_le h with rfl | h'
      · simp
      · rw [abs_of_neg h']
        ring
  have hmeanbdd : ∀ s : ℝ≥0, |∫ ω, δ s ω * δ s ω ∂μ| ≤ Dd * Dd := by
    intro s
    calc |∫ ω, δ s ω * δ s ω ∂μ| ≤ ∫ ω, |δ s ω * δ s ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|Dd| * |Dd|) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            (integrable_const (μ := μ) (|Dd| * |Dd|)) ?_
          filter_upwards [] with ω
          change |δ s ω * δ s ω| ≤ |Dd| * |Dd|
          rw [abs_mul]
          calc |δ s ω| * |δ s ω| ≤ |Dd| * |δ s ω| :=
                mul_le_mul_of_nonneg_right
                  (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
            _ ≤ |Dd| * |Dd| := mul_le_mul_of_nonneg_left
                  (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
      _ = Dd * Dd := by
          rw [integral_const, hDsq2]
          simp
  have hmeanmeas : Measurable (fun s : ℝ≥0 ↦ ∫ ω, δ s ω * δ s ω ∂μ) :=
    (continuous_mean_of_bdd_cont hgmeas (ae_of_all _ hgcont) (fun s ω ↦ by
      rw [abs_mul]
      calc |δ s ω| * |δ s ω| ≤ |Dd| * |δ s ω| :=
            mul_le_mul_of_nonneg_right (le_trans (hδbdd s ω) (le_abs_self Dd))
              (abs_nonneg _)
        _ ≤ |Dd| * |Dd| := mul_le_mul_of_nonneg_left
            (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _))).measurable
  haveI : IsFiniteMeasure
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top
  have hconst : ∫ s in Set.Ioc u v, (|Dd| * |Dd|) ∂ItoIntegralL2.timeMeasure
      = (|Dd| * |Dd|) * ((v : ℝ) - u) := by
    rw [MeasureTheory.setIntegral_const, measureReal_def,
      ItoIntegralL2.timeMeasure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv))]
    ring
  refine le_trans (integral_mono_of_nonneg
    (Eventually.of_forall fun s ↦ integral_nonneg (μ := μ)
      (f := fun ω ↦ δ s ω * δ s ω)
      (fun ω ↦ by
        change (0:ℝ) ≤ δ s ω * δ s ω
        rw [← pow_two]
        exact sq_nonneg (δ s ω)))
    (integrable_const (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v))
      (|Dd| * |Dd|))
    (Eventually.of_forall fun s ↦ by
      change (fun s : ℝ≥0 ↦ ∫ ω, δ s ω * δ s ω ∂μ) s
        ≤ (fun _ : ℝ≥0 ↦ |Dd| * |Dd|) s
      exact le_trans (le_of_eq rfl)
        (le_trans (le_abs_self (∫ ω, δ s ω * δ s ω ∂μ))
          (le_trans (hmeanbdd s) (le_of_eq hDsq2.symm))))) ?_
  calc ∫ s in Set.Ioc u v, (|Dd| * |Dd|) ∂ItoIntegralL2.timeMeasure
      = (|Dd| * |Dd|) * ((v : ℝ) - u) := hconst
    _ ≤ Dd ^ 2 * ((v : ℝ) - u) := by
        show |Dd| * |Dd| * ((v : ℝ) - u) ≤ Dd ^ 2 * ((v : ℝ) - u)
        rw [sq Dd, hDsq2]

set_option maxHeartbeats 1600000 in
-- a long estimate: elaborating the whole proof exceeds the default budget
omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **The convergence of the quadratic block** (the summed weighted increment isometry,
conditional on a gap bound): if for some null sequence `r` the weighted second-moment sum
along the uniform partition differs from the frozen rectangle sum by at most
`2·|C_w|·|D_δ|·√T·r n` for `n > 0` (`gapSum_le` supplies one, with
`r n = ‖φ − δⁿ‖_{L²(trim)}`), then the sum converges to the quadratic block
`∫₀ᵀ 𝔼[w·δ²] ds`. -/
theorem quadraticSqSum_tendsto (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ w s ω)
    (hwbdd : ∀ s ω, |w s ω| ≤ Cw)
    (hgap : ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n →
      |∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ) * r n) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T,
          (∫ ω, w s ω * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hgmeas : ∀ s, Measurable (fun ω ↦ w s ω * (δ s ω * δ s ω)) := by
    intro s
    exact (((hwadap s).mono ((natFiltration hBmeas).le s) le_rfl).mul
      (((hδadap s).mono ((natFiltration hBmeas).le s)).measurable.mul
        ((hδadap s).mono ((natFiltration hBmeas).le s)).measurable))
  have hgcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ w s ω * (δ s ω * δ s ω) :=
    hwcont.mono fun ω h ↦ h.mul ((hδcont ω).mul (hδcont ω))
  have hgbdd : ∀ s ω, |w s ω * (δ s ω * δ s ω)| ≤ |Cw| * (Dd * Dd) := by
    intro s ω
    have hDd : |Dd| * |Dd| = Dd * Dd := by
      rcases le_total 0 Dd with h | h
      · rw [abs_of_nonneg h]
      · rcases eq_or_lt_of_le h with rfl | h'
        · simp
        · rw [abs_of_neg h']
          ring
    have hd2 : |δ s ω * δ s ω| ≤ |Dd| * |Dd| := by
      rw [abs_mul]
      exact mul_le_mul (le_trans (hδbdd s ω) (le_abs_self Dd))
        (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
        (abs_nonneg Dd)
    change |w s ω * (δ s ω * δ s ω)| ≤ |Cw| * (Dd * Dd)
    rw [abs_mul]
    exact (mul_le_mul (le_trans (hwbdd s ω) (le_abs_self Cw)) hd2 (abs_nonneg _)
      (abs_nonneg _)).trans (by rw [hDd])
  -- the frozen sums converge to the quadratic block
  have hF := frozenRiemann_tendsto (μ := μ) (T := T) hgmeas hgcont hgbdd
  have hFeq : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        = ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ by show _ = _; ring)
  obtain ⟨r, hr0, hgap'⟩ := hgap
  -- the gap dies along the null sequence r
  have hSFabs : Tendsto (fun n : ℕ ↦ |(∑ k ∈ Finset.range n,
      ∫ ω, w (unifPart T n k) ω
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
    - ∑ k ∈ Finset.range n,
        (∫ ω, w (unifPart T n k) ω
          * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
          * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ) * r n)
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have h := hgap' n hn
      rw [hFeq n] at h
      exact h
    · simpa using (tendsto_const_nhds
        (x := 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ))).mul hr0
  have hSF : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      - ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) atTop (𝓝 0) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    refine Filter.Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hSFabs
    change |(∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
      = dist ((∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) 0
    rw [Real.dist_eq, sub_zero]
  have key := hSF.add hF
  rw [zero_add] at key
  exact key.congr' (Eventually.of_forall fun n ↦ by
    show (∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      + ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
      = _
    ring)

end StageFourC

end MathFin.ItoDriftConditional
