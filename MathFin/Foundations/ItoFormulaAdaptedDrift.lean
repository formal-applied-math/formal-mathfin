/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftWeightedIsometry
public import MathFin.Foundations.ItoDriftGapDecay
public import MathFin.Foundations.ItoDriftBlock
public import MathFin.Foundations.ItoDriftQuadraticCorrections
public import MathFin.Foundations.ItoDriftTaylorRemainder

/-! # The integrated Itô–drift identity for adapted coefficients: the discrete route

The bounded-adapted case of the integrated Itô–drift identity — the expectation form of
Itô's formula along an Itô process with random coefficients,

  `𝔼[f(X_T)] = 𝔼[f(X_0)] + ∫₀ᵀ (𝔼[f'(X_s)·β_s] + ½·𝔼[f''(X_s)·δ_s²]) ds`,

for `β, δ` bounded, `natFiltration`-adapted and path-continuous, and `f` three times
differentiable with `f'`, `f''`, `f'''` bounded, proved from the discrete Itô formula on uniform
partitions. `M` and `X` are hypotheses. The integrand `δ` and a `natFiltration`-adapted `M` with
`M t =ᵐ (δ●B)_t` for every `t ≥ 0` (the process values of `itoProcessCLM` at the σ-realization
`processToLp δ`) are the bundle `IsAdaptedItoDrift` (`hD`), which every layer below takes; `X` is
a process with `X t = c + ∫₀ᵗ β_s ds + M t` (`hXrel`) whose paths are continuous almost surely
(`hXcont`). `B` is a pre-Brownian motion with measurable sections; its paths need not be
continuous.

## Relation to the constructed process

The hypotheses are met by the process the library constructs. When every path of `B` is
continuous, the Itô term `itoContinuousMod` of `ItoFormulaAdapted.adaptedItoProcess`, frozen
after the horizon `T`, is `natFiltration`-adapted, pinned to `δ●B` at every time, and almost
surely path-continuous; so `itoDrift_expectation_identity_adapted` applies to the constructed
process (`itoDrift_expectation_identity_adapted_at_adaptedItoProcess` in
`ItoFormulaAdaptedDriftConstructed`). That module also derives the same identity from the
pathwise formula `ItoFormulaAdapted.ito_formula_adapted` by centering and Fubini, with weaker
hypotheses on `f` (no third derivative), and for every version `M` of `δ●B`
(`itoDrift_expectation_identity_adapted_of_adaptedItoProcess`). The two derivations are
independent: this file never uses the pathwise formula. What the statement here covers beyond
them is a `B` whose paths are not all continuous; for such a `B` no lemma in the library supplies
an `M` satisfying the hypotheses.

Route: the per-path discrete Itô formula (`MathFin.discrete_ito_formula`) at the grid
values of `X`, integrated over `Ω`; the first-order martingale terms die exactly
(`mul_trueIncr_expect_eq_zero`, the martingale property of the adapted Itô integral
transferred along the a.e. `hD.ae_eq`); the drift block converges by pathwise Riemann–Stieltjes
sums + DCT + the Fubini interchange (`driftBlock_tendsto`); the quadratic block converges by
the summed weighted increment isometry (`quadraticSqSum_tendsto'`, discharged from its
conditional form by the step-approximant `L²` convergence `deltaStepLp_tendsto`); the
drift² corrections (`quadDriftSqSum_tendsto`), the drift–martingale cross corrections
(`quadCrossSum_tendsto`) and the Taylor remainder (the cubic bound + the third-moment
estimate, `taylorRemainderSum_tendsto`, `trueIncr_pow3_le`) tend to `0` — the proofs bound
them by `O(mesh)`, `O(√mesh)` and `O(√mesh)`; only the limits are stated. Path continuity of
`X` enters only through dominated convergence and the Fubini interchange
(`expectation_pathIntegral_eq`, stated for almost surely continuous paths), so almost sure
continuity suffices.

Supporting layers, bottom-up: the band-to-slice conversion of the predictable trim measure
(a private lemma of `ItoDriftIncrementEnergy`; the Fubini interchange
`expectation_pathIntegral_eq` comes from `ItoDriftExpectation`), `clm_band_energy` (the band
energy of the CLM Itô integral, `ItoIntegralProcessIsometry`) and `incrementEnergy` (its transfer
to `M`), `mul_trueIncr_expect_eq_zero` (the martingale kill),
`deltaStepLp`/`deltaStepLp_tendsto` (the step approximants), the per-cell weighted isometry
(`weightedCellSq_step`, `stepIncr_stepCLM_ae`), the gap decay (`errorIncr_ae`,
`cellGap_le`, `gapSum_le`) and the quadratic block with its gap hypothesis discharged
(`quadraticSqSum_tendsto'`, for the hypothesized `M`), the
fourth/third-moment bounds (`stepSum_pow4_le` of `ItoStepSumFourthMoment`, `trueIncr_pow4_le`,
`trueIncr_pow3_le`),
the drift primitive (`AdaptedDrift.driftPath` reused, with its adaptedness
`stronglyMeasurable_driftPath`, from `Foundations/AdaptedDrift`), the drift
block, the two quadratic corrections and the Taylor-remainder convergence.

## Result

All public names are in the namespace `MathFin.ItoDriftConditional`.

* `itoDrift_expectation_identity_adapted` — the identity above, conditional on `M` and `X`.
* Foundations: `IsAdaptedItoDrift`, `memLp_M`, `incrementEnergy` (the increment
  isometry), `weightedCellSq_step` (the per-cell weighted isometry), the step approximants
  `deltaStepLp` / `deltaStepLp_tendsto`.
* Convergence blocks: `driftBlock_tendsto` (with the drift primitive `AdaptedDrift.driftPath`
  and `driftSum_expect_tendsto`), `quadraticSqSum_tendsto` / `quadraticSqSum_tendsto'`
  (via `gapSum_le` and the mean-function Riemann limit `frozenRiemann_tendsto`), the exact
  martingale kill `mul_trueIncr_expect_eq_zero`, the Taylor bound `taylorRemainderSum_tendsto`
  (`trueIncr_pow3_le`, `trueIncr_pow4_le`, `trueIncr_pow4_integrable`), and the dying
  corrections `quadDriftSqSum_tendsto` / `quadCrossSum_tendsto`.

The constant-coefficient case and the Fubini interchange are `ito_drift_expectation_identity`
and `expectation_pathIntegral_eq` in `ItoDriftExpectation`.

The supporting layers are the modules `ItoDriftIncrementEnergy`, `ItoDriftWeightedIsometry`,
`ItoDriftGapDecay`, `ItoStepSumFourthMoment`, `ItoDriftMomentBounds`, `ItoDriftBlock`,
`ItoDriftQuadraticCorrections` and `ItoDriftTaylorRemainder`; this file is the assembly of
`itoDrift_expectation_identity_adapted` from them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

section StageFiveD

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 ItoIntegralBrownian AdaptedDrift MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  {M : ℝ≥0 → Ω → ℝ} (hD : IsAdaptedItoDrift hB hBmeas T δ Dd M)

include hD


set_option maxHeartbeats 1600000 in
-- a long estimate: elaborating the whole proof exceeds the default budget
/-- **The integrated Itô–drift identity for adapted coefficients**, conditional on the
process `M`. For `β, δ` bounded, `natFiltration`-adapted and path-continuous, a hypothesized
`natFiltration`-adapted `M` with `M t =ᵐ (δ●B)_t` for every `t` (`hD.ae_eq`), and a hypothesized
`X` with `X_t = c + ∫₀ᵗ β_s ds + M_t` (`hXrel`, the `AdaptedDrift.driftPath β` decomposition)
with almost every path continuous (`hXcont`), and `f` three times differentiable with `f'`,
`f''`, `f'''` bounded,

  `𝔼[f(X_T)] = 𝔼[f(X_0)] + ∫₀ᵀ (𝔼[f'(X_s)·β_s] + ½·𝔼[f''(X_s)·δ_s²]) ds`.

For `B` with continuous paths the constructed Itô process satisfies these hypotheses
(`itoDrift_expectation_identity_adapted_at_adaptedItoProcess`, see the module docstring).

Route: the per-path discrete Itô formula (`MathFin.discrete_ito_formula`) at the grid
values of `X`, integrated over `Ω`; the first-order martingale terms die exactly
(`mul_trueIncr_expect_eq_zero` at the `𝓕_{tₖ}`-measurable bounded test `f' ∘ X`); the
drift block converges to `∫₀ᵀ 𝔼[f'∘X·β]` (`driftBlock_tendsto`); the quadratic block
converges to `∫₀ᵀ 𝔼[f''∘X·δ²]` (`quadraticSqSum_tendsto'` at the weight `f''∘X`);
the drift² corrections, the drift–martingale cross corrections and the Taylor remainder
die (`quadDriftSqSum_tendsto`, `quadCrossSum_tendsto`,
`taylorRemainderSum_tendsto`); the two time integrals cross the expectation by the
stage-1 Fubini lemma (already folded into the sub-lemma conclusions). -/
theorem itoDrift_expectation_identity_adapted
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + driftPath β t ω + M t ω)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3) :
    ∫ ω, f (X T ω) ∂μ
      = ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ
        + ∫ s in Set.Ioc (0 : ℝ≥0) T,
            ((∫ ω, f' (X s ω) * β s ω ∂μ)
              + (1 / 2) * (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ))
          ∂ItoIntegralL2.timeMeasure := by
  have hC1 : (0 : ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf''c : Continuous f'' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  -- `X` is adapted, by the decomposition (the one new measurability fact of 5d)
  have hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t) := by
    intro t
    rw [hXrel t]
    exact (((stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd t).measurable.const_add c).add
      (hD.adaptedM t).measurable).stronglyMeasurable
  -- `f ∘ X` is integrable (linear growth of `f` from `|f'| ≤ C₁`)
  have hf_lin : ∀ x, |f x| ≤ |f 0| + C1 * |x| := by
    intro x
    have hmv : |f x - f 0| ≤ C1 * |x| := by
      have h := abs_sub_le_of_hasDerivAt (g := f) (g' := f') hf hg1 0 x
      simpa using h
    calc |f x| = |f 0 + (f x - f 0)| := by congr 1; ring
      _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
      _ ≤ |f 0| + C1 * |x| := by linarith
  have hMint : ∀ t : ℝ≥0, Integrable (fun ω ↦ |M t ω|) μ :=
    fun t ↦ (memLp_M hB hBmeas hD t).norm.integrable one_le_two
  have hdpb : ∀ t : ℝ≥0, ∀ ω, |driftPath β t ω| ≤ |Db| * (t : ℝ) := by
    intro t ω
    have h0 : driftPath β (0 : ℝ≥0) ω = 0 := by
      simp only [driftPath, Set.Ioc_self, setIntegral_empty]
    have h := abs_driftPath_sub_le hβcont hβbdd
      (show (0 : ℝ≥0) ≤ t from zero_le) ω
    rw [h0, sub_zero, NNReal.coe_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Db) (NNReal.coe_nonneg t))
  have hXint : ∀ t : ℝ≥0, Integrable (fun ω ↦ f (X t ω)) μ := by
    intro t
    have hmeas : AEStronglyMeasurable (fun ω ↦ f (X t ω)) μ :=
      (hfcont.measurable.comp
        ((hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl)).aestronglyMeasurable
    have hdom : Integrable (fun ω ↦ (|f 0| + C1 * (|c| + |Db| * ((t : ℝ) + 1)))
        + C1 * |M t ω|) μ :=
      (integrable_const _).add ((hMint t).const_mul C1)
    refine Integrable.mono' hdom hmeas (Eventually.of_forall fun ω ↦ ?_)
    have harg : |X t ω| ≤ |c| + |Db| * ((t : ℝ) + 1) + |M t ω| := by
      have h1 : |X t ω| = |c + driftPath β t ω + M t ω| := by rw [hXrel t]
      rw [h1]
      calc |c + driftPath β t ω + M t ω| ≤ |c + driftPath β t ω| + |M t ω| :=
            abs_add_le _ _
        _ ≤ |c| + |driftPath β t ω| + |M t ω| := by
            have := abs_add_le c (driftPath β t ω); linarith
        _ ≤ |c| + |Db| * ((t : ℝ) + 1) + |M t ω| := by
            have h2 := hdpb t ω
            have h3 : |Db| * (t : ℝ) ≤ |Db| * ((t : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (t : ℝ) + 1 by
                linarith [NNReal.coe_nonneg t]) (abs_nonneg Db)
            linarith
    calc |f (X t ω)| ≤ |f 0| + C1 * |X t ω| := hf_lin _
      _ ≤ |f 0| + C1 * (|c| + |Db| * ((t : ℝ) + 1) + |M t ω|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left harg hC1)
      _ = (|f 0| + C1 * (|c| + |Db| * ((t : ℝ) + 1))) + C1 * |M t ω| := by ring
  -- the five block convergences
  have hA : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
    atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T,
        (∫ ω, f' (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) :=
    driftBlock_tendsto hBmeas T hβadap hβcont hβbdd hXadap hXcont hf'c hg1
  have hB0 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
    atTop (𝓝 0) :=
    quadDriftSqSum_tendsto hBmeas T hβadap hβcont hβbdd hXadap hf''c hg2
  have hC0 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
    atTop (𝓝 0) :=
    quadCrossSum_tendsto hB hBmeas hD
      hβadap hβcont hβbdd hXadap hf''c hg2
  have hE0 : Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω) ∂μ) atTop (𝓝 0) :=
    taylorRemainderSum_tendsto hB hBmeas hD hBmeas c
      hβcont hβbdd hXrel hXadap hf hf' hf'' hg3
  have hD0 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f'' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
    atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T,
        (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) :=
    quadraticSqSum_tendsto' hB hBmeas hD
      (w := fun s ω ↦ f'' (X s ω)) (Cw := C2)
      (fun t ↦ hf''c.measurable.comp (hXadap t).measurable)
      (hXcont.mono fun ω h ↦ hf''c.comp h)
      (fun s ω ↦ hg2 (X s ω))
  -- the per-partition identity (expectation of the discrete Itô expansion)
  have key : ∀ n : ℕ, 0 < n →
      (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ)
        = (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ∂μ)
          + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
            + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
            + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
          + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ) := by
    intro n hn
    have hTnn : unifPart T n n = T := unifPart_self T hn.ne'
    have hTn0 : unifPart T n 0 = 0 := unifPart_zero T n
    have hcellen : ∀ k : ℕ, ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
        = (T : ℝ) / (n : ℝ) := fun k ↦ unifPart_succ_sub T n k
    have hcellT : ∀ k : ℕ, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ≤ (T : ℝ) := by
      intro k
      rw [hcellen k]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hT0 : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
      rw [div_le_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hn1 hT0]
    have hTfrac : ((T : ℝ) / (n : ℝ)) ≤ (T : ℝ) + 1 := by
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hT0 : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
      rw [div_le_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hn1 hT0]
    -- the per-cell increment decomposition
    have hΔ : ∀ k : ℕ, ∀ ω : Ω, X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω
        = (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          + (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
      intro k ω
      rw [hXrel (unifPart T n (k + 1)), hXrel (unifPart T n k)]
      change (c + driftPath β (unifPart T n (k + 1)) ω + M (unifPart T n (k + 1)) ω)
          - (c + driftPath β (unifPart T n k) ω + M (unifPart T n k) ω) = _
      ring
    -- measurability of the grid-value factors
    have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t ↦
      (hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
    have hdpm : ∀ t : ℝ≥0, Measurable (driftPath β t) := fun t ↦
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd t).measurable.mono
        ((natFiltration hBmeas).le t) le_rfl
    have hf'Xk : ∀ k : ℕ, Measurable (fun ω ↦ f' (X (unifPart T n k) ω)) := fun k ↦
      hf'c.measurable.comp (hXm (unifPart T n k))
    have hf''Xk : ∀ k : ℕ, Measurable (fun ω ↦ f'' (X (unifPart T n k) ω)) := fun k ↦
      hf''c.measurable.comp (hXm (unifPart T n k))
    have hdMm : ∀ k : ℕ, Measurable (fun ω ↦ M (unifPart T n (k + 1)) ω
        - M (unifPart T n k) ω) := fun k ↦
      ((hD.adaptedM (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl).sub
      ((hD.adaptedM (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl)
    have hdIb : ∀ k : ℕ, ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k) := fun k ω ↦
      abs_driftPath_sub_le hβcont
        (fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db))
        (unifPart_mono T n (Nat.le_succ k)) ω
    have hdIbT : ∀ k : ℕ, ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω| ≤ |Db| * ((T : ℝ) + 1) := by
      intro k ω
      calc |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω|
          ≤ |Db| * ((T : ℝ) / (n : ℝ)) := by
            have h := hdIb k ω
            rw [← hcellen k]
            exact h
        _ ≤ |Db| * ((T : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hTfrac (abs_nonneg Db)
    -- per-cell integrabilities
    have hdMint : ∀ k : ℕ, Integrable (fun ω ↦ M (unifPart T n (k + 1)) ω
        - M (unifPart T n k) ω) μ := fun k ↦
      ((memLp_M hB hBmeas hD (unifPart T n (k + 1))).sub
        (memLp_M hB hBmeas hD (unifPart T n k))).integrable
          one_le_two
    have hint1 : ∀ k : ℕ, Integrable (fun ω ↦ f' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω)) μ := by
      intro k
      refine Integrable.of_bound
        (((hf'Xk k).mul ((hdpm (unifPart T n (k + 1))).sub
          (hdpm (unifPart T n k)))).aestronglyMeasurable)
        (C1 * |Db| * ((T : ℝ) + 1)) ?_
      filter_upwards with ω
      change ‖f' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      have hstep : |f' (X (unifPart T n k) ω)| * |driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω| ≤ C1 * (|Db| * ((T : ℝ) + 1)) :=
        mul_le_mul (hg1 (X (unifPart T n k) ω)) (hdIbT k ω) (abs_nonneg _) hC1
      exact hstep.trans (le_of_eq (by ring))
    have hint2 : ∀ k : ℕ, Integrable (fun ω ↦ f' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) μ := fun k ↦
      Integrable.mono' (hdMint k |>.abs.const_mul C1)
        (((hf'Xk k).mul (hdMm k)).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          change ‖f' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hg1 _) (abs_nonneg _))
    have hint3 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω) ^ 2) μ := by
      intro k
      refine Integrable.of_bound
        (((hf''Xk k).mul (((hdpm (unifPart T n (k + 1))).sub
          (hdpm (unifPart T n k))).pow_const 2)).aestronglyMeasurable)
        (C2 * |Db| ^ 2 * ((T : ℝ) + 1) ^ 2) ?_
      filter_upwards with ω
      change ‖f'' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω) ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hstep : |f'' (X (unifPart T n k) ω)| * |driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω| ^ 2
          ≤ C2 * ((|Db| * ((T : ℝ) + 1)) ^ 2) :=
        mul_le_mul (hg2 _) (pow_le_pow_left₀ (abs_nonneg _) (hdIbT k ω) 2)
          (sq_nonneg _) hC2
      refine hstep.trans ?_
      rw [show ((|Db| * ((T : ℝ) + 1)) ^ 2)
            = |Db| ^ 2 * ((T : ℝ) + 1) ^ 2 from by ring, mul_assoc]
    have hint4 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) μ := fun k ↦
      Integrable.mono' (hdMint k |>.abs.const_mul (C2 * (|Db| * ((T : ℝ) + 1))))
        (((hf''Xk k).mul ((hdpm (unifPart T n (k + 1))).sub
          (hdpm (unifPart T n k)))).mul (hdMm k) |>.aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          change ‖f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have hstep : |f'' (X (unifPart T n k) ω)| * |driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω| ≤ C2 * (|Db| * ((T : ℝ) + 1)) :=
            mul_le_mul (hg2 _) (hdIbT k ω) (abs_nonneg _) hC2
          exact mul_le_mul_of_nonneg_right hstep (abs_nonneg _))
    have hint5 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) μ := fun k ↦
      Integrable.mono'
        (((memLp_M hB hBmeas hD
            (unifPart T n (k + 1))).sub
          (memLp_M hB hBmeas hD (unifPart T n k))).integrable_sq.const_mul C2)
        (((hf''Xk k).mul ((hdMm k).pow_const 2)).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          change ‖f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
          exact mul_le_mul_of_nonneg_right (hg2 _) (sq_nonneg _))
    have hintStwo : ∀ k : ℕ, Integrable (fun ω : Ω ↦ 2 * (f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
        + f'' (X (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) μ := fun k ↦
      ((hint4 k).const_mul 2).add (hint5 k)
    have hint6 : ∀ k ∈ Finset.range n, Integrable (fun ω ↦
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)) μ := fun k hk ↦
      remainderCell_integrable hB hBmeas hD
        (n := n) hn (k := k) (Finset.mem_range.mp hk) c hβcont hβbdd hXrel hXadap
        hf hf' hf'' hg3
    -- integrability of the full increments `f'·ΔX`, `f''·ΔX²`
    have hintΔX : ∀ k : ℕ, Integrable (fun ω ↦ f' (X (unifPart T n k) ω)
        * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) μ := by
      intro k
      refine ((hint1 k).add (hint2 k)).congr (Eventually.of_forall fun ω ↦ ?_)
      change f' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          + f' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        = f' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
      rw [hΔ k ω]
      ring
    have hintΔX2 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) μ := by
      intro k
      refine ((hint3 k).add (((hint4 k).const_mul 2).add (hint5 k))).congr
        (Eventually.of_forall fun ω ↦ ?_)
      change f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2
          + (2 * (f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
            + f'' (X (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2)
        = f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
      rw [hΔ k ω]
      ring
    have hintS1int : Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
        f' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) μ :=
      integrable_finsetSum _ fun k _ ↦ hintΔX k
    have hintS2int : Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
        f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) μ :=
      integrable_finsetSum _ fun k _ ↦ hintΔX2 k
    have hintS3int : Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)) μ :=
      integrable_finsetSum _ fun k hk ↦ hint6 k hk
    have hintShalf : Integrable (fun ω : Ω ↦ (1 / 2) * (∑ k ∈ Finset.range n,
        f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)) μ :=
      hintS2int.const_mul (1 / 2)
    have hintShalfS3 : Integrable (fun ω : Ω ↦ (1 / 2) * (∑ k ∈ Finset.range n,
        f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
        + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
          (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω))) μ :=
      hintShalf.add hintS3int
    -- the per-path discrete Itô identity at the grid values of `X`
    have hpath : ∀ ω : Ω, f (X T ω) - f (X (0 : ℝ≥0) ω)
        = (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω))
          + ((1 / 2) * (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
          + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω))) := by
      intro ω
      have hformula := discrete_ito_formula (N := n)
        (X := fun j : ℕ ↦ X (unifPart T n j) ω) f f' f''
      simp only [hTnn, hTn0] at hformula
      rw [add_assoc] at hformula
      exact hformula
    -- the first-order martingale terms die exactly
    have hzero1 : (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) = 0 := by
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      exact mul_trueIncr_expect_eq_zero hB hBmeas hD
        (unifPart_mono T n (Nat.le_succ k))
        ((hf'c.measurable.comp (hXadap (unifPart T n k)).measurable).stronglyMeasurable)
        (fun ω ↦ hg1 (X (unifPart T n k) ω))
    -- the per-cell integral splits
    have hintS1 : (∫ ω, (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ∂μ)
        = (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) := by
      rw [integral_finsetSum (μ := μ) (s := Finset.range n)
          (f := fun (k : ℕ) (ω : Ω) ↦ f' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω))
          (fun k _ ↦ hintΔX k)]
      have hsplit : ∀ k ∈ Finset.range n,
          (∫ ω, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ∂μ)
            = (∫ ω, f' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ∂μ)
              + (∫ ω, f' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) := by
        intro k _
        rw [← integral_add (hint1 k) (hint2 k)]
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
          change f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
            = f' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω)
              + f' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          rw [hΔ k ω]
          ring)
      rw [Finset.sum_congr rfl (fun k hk ↦ hsplit k hk), Finset.sum_add_distrib]
    have hintS2 : (∫ ω, (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) ∂μ)
        = (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
          + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ) := by
      rw [integral_finsetSum (μ := μ) (s := Finset.range n)
          (f := fun (k : ℕ) (ω : Ω) ↦ f'' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
          (fun k _ ↦ hintΔX2 k)]
      have hsplit : ∀ k ∈ Finset.range n,
          (∫ ω, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2 ∂μ)
            = (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
              + (2 * (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
              + (∫ ω, f'' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)) := by
        intro k _
        calc ∫ ω, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2 ∂μ
            = ∫ ω, (f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2
              + (2 * (f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
              + f'' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2)) ∂μ :=
              integral_congr_ae (Eventually.of_forall fun ω ↦ by
                change f'' (X (unifPart T n k) ω)
                    * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2 = _
                rw [hΔ k ω]
                ring)
          _ = (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
              + (∫ ω, (2 * (f'' (X (unifPart T n k) ω)
                  * (driftPath β (unifPart T n (k + 1)) ω
                    - driftPath β (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
                + f'' (X (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) ∂μ) :=
              integral_add (hint3 k) (hintStwo k)
          _ = (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
              + (2 * (∫ ω, f'' (X (unifPart T n k) ω)
                  * (driftPath β (unifPart T n (k + 1)) ω
                    - driftPath β (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
                + (∫ ω, f'' (X (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)) := by
              rw [integral_add ((hint4 k).const_mul 2) (hint5 k), integral_const_mul]
      rw [Finset.sum_congr rfl (fun k hk ↦ hsplit k hk), Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    -- assemble the per-partition identity
    calc (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ)
        = (∫ ω, ((∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω))
            + ((1 / 2) * (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
            + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)))) ∂μ) := by
          rw [← integral_sub (hXint T) (hXint (0 : ℝ≥0))]
          exact integral_congr_ae (Eventually.of_forall fun ω ↦ hpath ω)
      _ = (∫ ω, (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ∂μ)
          + (∫ ω, ((1 / 2) * (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
            + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω))) ∂μ) := by
          rw [integral_add hintS1int hintShalfS3]
      _ = (∫ ω, (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ∂μ)
          + (1 / 2) * (∫ ω, (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) ∂μ)
          + (∫ ω, (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) ∂μ) := by
          rw [integral_add hintShalf hintS3int, integral_const_mul]
          ring
      _ = (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ∂μ)
          + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
            + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
            + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
          + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ) := by
          rw [hintS1, hintS2, hzero1]
          ring
  -- the limit of the right-hand side
  have hR : Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
        + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
          + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
        + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ))
    atTop (𝓝 ((∫ s in Set.Ioc (0 : ℝ≥0) T,
          (∫ ω, f' (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)
        + (1 / 2) * ((0 : ℝ) + 2 * 0
          + (∫ s in Set.Ioc (0 : ℝ≥0) T,
              (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure))
        + 0)) :=
    (hA.add ((tendsto_const_nhds (x := (1 : ℝ) / 2)).mul
      ((hB0.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hC0)).add hD0))).add hE0
  have hL : Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
        + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
          + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
        + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ))
    atTop (𝓝 (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ)) := by
    refine (tendsto_const_nhds
      (x := (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact key n hn
  have hfin := tendsto_nhds_unique hL hR
  -- the band integrabilities and the merge of the two time integrals
  have hbdd_d : ∀ s : ℝ≥0, ∀ ω : Ω, |f' (X s ω) * β s ω| ≤ C1 * |Db| := by
    intro s ω
    rw [abs_mul]
    exact mul_le_mul (hg1 (X s ω)) (le_trans (hβbdd s ω) (le_abs_self Db)) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hg1 0))
  have hbdd_q : ∀ s : ℝ≥0, ∀ ω : Ω, |f'' (X s ω) * (δ s ω * δ s ω)| ≤ C2 * (Dd * Dd) := by
    intro s ω
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hg2 (X s ω)) (mul_self_le_mul_self (abs_nonneg _) (hD.bdd s ω))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (le_trans (abs_nonneg _) (hg2 0))
  have hdm : ∀ s : ℝ≥0, Measurable (fun ω ↦ f' (X s ω) * β s ω) := fun s ↦
    (hf'c.measurable.comp
      ((hXadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)).mul
      ((hβadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)
  have hqm : ∀ s : ℝ≥0, Measurable (fun ω ↦ f'' (X s ω) * (δ s ω * δ s ω)) := fun s ↦
    (hf''c.measurable.comp
      ((hXadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)).mul
      (((hD.adapted s).measurable.mono ((natFiltration hBmeas).le s) le_rfl).mul
        ((hD.adapted s).measurable.mono ((natFiltration hBmeas).le s) le_rfl))
  have hcontd : Continuous fun s : ℝ≥0 ↦ ∫ ω, f' (X s ω) * β s ω ∂μ :=
    continuous_mean_of_bdd_cont hdm (hXcont.mono fun ω h ↦ (hf'c.comp h).mul (hβcont ω))
      hbdd_d
  have hcontq : Continuous fun s : ℝ≥0 ↦ ∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ :=
    continuous_mean_of_bdd_cont hqm
      (hXcont.mono fun ω h ↦ (hf''c.comp h).mul ((hD.continuous ω).mul (hD.continuous ω))) hbdd_q
  have hdint : IntegrableOn (fun s : ℝ≥0 ↦ (∫ ω, f' (X s ω) * β s ω ∂μ))
      (Set.Ioc (0 : ℝ≥0) T) ItoIntegralL2.timeMeasure := by
    have : IsFiniteMeasure
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
    refine Integrable.of_bound
      (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
      ((hcontd.measurable.aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      (C1 * |Db|) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s _
    change ‖(fun s : ℝ≥0 ↦ (∫ ω, f' (X s ω) * β s ω ∂μ)) s‖ ≤ C1 * |Db|
    rw [Real.norm_eq_abs]
    calc |∫ ω, f' (X s ω) * β s ω ∂μ| ≤ ∫ ω, |f' (X s ω) * β s ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C1 * |Db|) ∂μ := integral_mono_of_nonneg
            (Eventually.of_forall fun ω ↦ abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun ω ↦ hbdd_d s ω)
      _ = C1 * |Db| := by rw [integral_const]; simp
  have hqint : IntegrableOn (fun s : ℝ≥0 ↦ (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ))
      (Set.Ioc (0 : ℝ≥0) T) ItoIntegralL2.timeMeasure := by
    have : IsFiniteMeasure
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
    refine Integrable.of_bound
      (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
      ((hcontq.measurable.aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      (C2 * (Dd * Dd)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s _
    change ‖(fun s : ℝ≥0 ↦ (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ)) s‖ ≤ C2 * (Dd * Dd)
    rw [Real.norm_eq_abs]
    calc |∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ|
          ≤ ∫ ω, |f'' (X s ω) * (δ s ω * δ s ω)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C2 * (Dd * Dd)) ∂μ := integral_mono_of_nonneg
            (Eventually.of_forall fun ω ↦ abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun ω ↦ hbdd_q s ω)
      _ = C2 * (Dd * Dd) := by rw [integral_const]; simp
  have hintqhalf : IntegrableOn (fun s : ℝ≥0 ↦ (1 / 2) * (∫ ω, f'' (X s ω)
      * (δ s ω * δ s ω) ∂μ)) (Set.Ioc (0 : ℝ≥0) T) ItoIntegralL2.timeMeasure :=
    hqint.const_mul (1 / 2)
  have hmerge : (∫ s in Set.Ioc (0 : ℝ≥0) T,
        ((∫ ω, f' (X s ω) * β s ω ∂μ)
          + (1 / 2) * (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ)) ∂ItoIntegralL2.timeMeasure)
      = (∫ s in Set.Ioc (0 : ℝ≥0) T, (∫ ω, f' (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)
        + (1 / 2) * (∫ s in Set.Ioc (0 : ℝ≥0) T,
            (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure) := by
    rw [integral_add (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
      hdint hintqhalf, integral_const_mul]
  -- conclude
  simp only [add_zero, mul_zero, zero_add] at hfin
  rw [hmerge]
  linarith

end StageFiveD

end MathFin.ItoDriftConditional
