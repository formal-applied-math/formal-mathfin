/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonMixed
public import MathFin.Probability.Brownian.Ito.Filtered.CommonQv

/-!
# Common Mixed Qv

Mixed quadratic variation of independent drivers, with weights adapted to
their COMMON filtration. The vanishing cross variation is a proved L2 limit
of actual partition sums, obtained by polarization with a unit Brownian rotation.

## Main definitions

* `weightedSquareSum`
* `weightedCrossSum`

## Main results

* `IndependentPair.memLp_weightedCrossSum`
* `weightedCrossSum_correlated`
* `IndependentPair.correlated_crossVariation_L2`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonNoise
open MeasureTheory ProbabilityTheory Filter
open MathFin MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B Z : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- Weighted sum of squared Brownian increments on the uniform partition. -/
def weightedSquareSum (B w : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, w (unifPart T n k) ω *
    (B (unifPart T n (k+1)) ω - B (unifPart T n k) ω)^2

/-- Weighted sum of products of increments of the two drivers on the uniform partition. -/
def weightedCrossSum (B Z w : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, w (unifPart T n k) ω *
    (B (unifPart T n (k+1)) ω - B (unifPart T n k) ω) *
    (Z (unifPart T n (k+1)) ω - Z (unifPart T n k) ω)

omit [IsProbabilityMeasure μ] in
theorem memLp_weightedSquareSum (hB : IsFilteredPreBrownian B ℱ μ)
    {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t))
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ t ω, |w t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (weightedSquareSum B w T n) 2 μ := by
  apply memLp_finsetSum
  intro k _
  have hd : MemLp (fun ω => (B (unifPart T n (k+1)) ω - B (unifPart T n k) ω)^2) 2 μ := by
    simpa only [sub_zero] using memLp_increment_sq_centered_two hB.toIsPreBrownianReal
      (unifPart T n k) (unifPart T n (k+1)) 0
  have hm := ((hw (unifPart T n k)).mono (ℱ.le _) le_rfl).aestronglyMeasurable.mul
    hd.aestronglyMeasurable
  apply MemLp.mono (hd.const_mul C) hm
  filter_upwards [] with ω
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hbdd _ ω) (abs_nonneg _)

omit mΩ [IsProbabilityMeasure μ] in
theorem weightedCrossSum_rotation (B Z w : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    weightedCrossSum B Z w T n ω =
      (25/24 : ℝ) * weightedSquareSum (linearNoise (3/5) (4/5) B Z) w T n ω -
      (3/8 : ℝ) * weightedSquareSum B w T n ω -
      (2/3 : ℝ) * weightedSquareSum Z w T n ω := by
  unfold weightedCrossSum weightedSquareSum
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [linearNoise]
  ring

theorem IndependentPair.weighted_crossVariation_L2 (h : IndependentPair ℱ B Z μ)
    {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t))
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ t ω, |w t ω| ≤ C) (T : ℝ≥0)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => w t ω) (Set.Icc 0 T)) :
    Tendsto (fun n : ℕ => ∫ ω, weightedCrossSum B Z w T n ω ^ 2 ∂μ) atTop (𝓝 0) := by
  let R := linearNoise (3/5) (4/5) B Z
  have hR : IsFilteredPreBrownian R ℱ μ := h.linear_brownian (3/5) (4/5) (by norm_num)
  let I := fun ω => ∫ t in Set.Ioc 0 T, w t ω ∂MathFin.ItoIntegralL2.timeMeasure
  let eB := fun n ω => weightedSquareSum B w T n ω - I ω
  let eZ := fun n ω => weightedSquareSum Z w T n ω - I ω
  let eR := fun n ω => weightedSquareSum R w T n ω - I ω
  have hb : Tendsto (fun n : ℕ => ∫ ω, eB n ω ^ 2 ∂μ) atTop (𝓝 0) :=
    CommonQv.tendsto_weighted_qv_process_of_ae_continuous h.left h.left.measurable_eval hw hC hbdd T
          hcont
  have hz : Tendsto (fun n : ℕ => ∫ ω, eZ n ω ^ 2 ∂μ) atTop (𝓝 0) :=
    CommonQv.tendsto_weighted_qv_process_of_ae_continuous h.right h.right.measurable_eval hw hC hbdd
          T hcont
  have hr : Tendsto (fun n : ℕ => ∫ ω, eR n ω ^ 2 ∂μ) atTop (𝓝 0) :=
    CommonQv.tendsto_weighted_qv_process_of_ae_continuous hR hR.measurable_eval hw hC hbdd T hcont
  have hi : MemLp I 2 μ :=
    MathFin.memLp_pathIntegral_process_of_ae_continuous
      (fun t => (hw t).mono (ℱ.le t) le_rfl) hC hbdd T hcont
  have hib (n : ℕ) : Integrable (fun ω => eB n ω ^ 2) μ :=
    ((memLp_weightedSquareSum h.left hw hC hbdd T n).sub hi).integrable_sq
  have hiz (n : ℕ) : Integrable (fun ω => eZ n ω ^ 2) μ :=
    ((memLp_weightedSquareSum h.right hw hC hbdd T n).sub hi).integrable_sq
  have hir (n : ℕ) : Integrable (fun ω => eR n ω ^ 2) μ :=
    ((hR.memLp_weightedSquareSum hw hC hbdd T n).sub hi).integrable_sq
  have heq (n : ℕ) (ω : Ω) : weightedCrossSum B Z w T n ω =
      (25/24 : ℝ) * eR n ω - (3/8 : ℝ) * eB n ω - (2/3 : ℝ) * eZ n ω := by
    rw [weightedCrossSum_rotation]
    dsimp [eB, eZ, eR, R]
    ring
  have hbound (n : ℕ) (ω : Ω) : weightedCrossSum B Z w T n ω ^ 2 ≤
      4 * (eR n ω ^ 2 + eB n ω ^ 2 + eZ n ω ^ 2) := by
    rw [heq]
    nlinarith [sq_nonneg (eR n ω), sq_nonneg (eB n ω), sq_nonneg (eZ n ω),
      sq_nonneg (25 * eR n ω + 9 * eB n ω),
      sq_nonneg (25 * eR n ω + 16 * eZ n ω),
      sq_nonneg (9 * eB n ω - 16 * eZ n ω)]
  have hupper : Tendsto (fun n : ℕ => 4 * ((∫ ω, eR n ω ^ 2 ∂μ) +
      (∫ ω, eB n ω ^ 2 ∂μ) + ∫ ω, eZ n ω ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using ((hr.add hb).add hz).const_mul 4
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) _ hupper
  intro n
  calc
    (∫ ω, weightedCrossSum B Z w T n ω ^ 2 ∂μ) ≤
        ∫ ω, 4 * (eR n ω ^ 2 + eB n ω ^ 2 + eZ n ω ^ 2) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        ((((hir n).add (hib n)).add (hiz n)).const_mul 4)
        (Filter.Eventually.of_forall (hbound n))
    _ = _ := by
      have hirb : Integrable (fun ω => eR n ω ^ 2 + eB n ω ^ 2) μ := (hir n).add (hib n)
      rw [integral_const_mul, integral_add hirb (hiz n),
        integral_add (hir n) (hib n)]

omit [IsProbabilityMeasure μ] in
theorem IndependentPair.memLp_weightedCrossSum (h : IndependentPair ℱ B Z μ)
    {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t))
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ t ω, |w t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (weightedCrossSum B Z w T n) 2 μ := by
  have hR := h.linear_brownian (3/5) (4/5) (by norm_num)
  have he : weightedCrossSum B Z w T n = fun ω =>
      (25/24 : ℝ) * weightedSquareSum (linearNoise (3/5) (4/5) B Z) w T n ω -
      (3/8 : ℝ) * weightedSquareSum B w T n ω -
      (2/3 : ℝ) * weightedSquareSum Z w T n ω :=
    funext (weightedCrossSum_rotation B Z w T n)
  rw [he]
  exact (((hR.memLp_weightedSquareSum hw hC hbdd T n).const_mul (25/24)).sub
    ((memLp_weightedSquareSum h.left hw hC hbdd T n).const_mul (3/8))).sub
    ((memLp_weightedSquareSum h.right hw hC hbdd T n).const_mul (2/3))

omit mΩ [IsProbabilityMeasure μ] in
theorem weightedCrossSum_correlated (ρ : ℝ) (B Z w : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    weightedCrossSum (correlatedNoise ρ B Z) B w T n ω =
      ρ * weightedSquareSum B w T n ω + orthogonalWeight ρ * weightedCrossSum B Z w T n ω := by
  unfold weightedCrossSum weightedSquareSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [correlatedNoise, linearNoise]
  ring

/-- The correlation term is proved as a weighted partition-sum L2 limit.
For |rho|<=1 the separate `correlated_brownian` theorem certifies that W is
Brownian on the supplied filtration. This algebraic limit also holds outside
that range, where the same linear combination need not be standard Brownian. -/
theorem IndependentPair.correlated_crossVariation_L2 (h : IndependentPair ℱ B Z μ)
    (ρ : ℝ) {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t))
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ t ω, |w t ω| ≤ C) (T : ℝ≥0)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => w t ω) (Set.Icc 0 T)) :
    Tendsto (fun n : ℕ => ∫ ω, (weightedCrossSum (correlatedNoise ρ B Z) B w T n ω -
      ρ * ∫ t in Set.Ioc 0 T, w t ω ∂MathFin.ItoIntegralL2.timeMeasure)^2 ∂μ) atTop (𝓝 0) := by
  let I := fun ω => ∫ t in Set.Ioc 0 T, w t ω ∂MathFin.ItoIntegralL2.timeMeasure
  let eB := fun n ω => weightedSquareSum B w T n ω - I ω
  let Q := fun n ω => weightedCrossSum B Z w T n ω
  have hbl : Tendsto (fun n : ℕ => ∫ ω, eB n ω^2 ∂μ) atTop (𝓝 0) :=
    CommonQv.tendsto_weighted_qv_process_of_ae_continuous h.left h.left.measurable_eval hw hC hbdd T
          hcont
  have hcl := h.weighted_crossVariation_L2 hw hC hbdd T hcont
  have hi : MemLp I 2 μ := MathFin.memLp_pathIntegral_process_of_ae_continuous
    (fun t => (hw t).mono (ℱ.le t) le_rfl) hC hbdd T hcont
  have hib (n : ℕ) : Integrable (fun ω => (2*ρ^2) * eB n ω^2) μ :=
    (((memLp_weightedSquareSum h.left hw hC hbdd T n).sub hi).integrable_sq).const_mul _
  have hiq (n : ℕ) : Integrable (fun ω => (2*orthogonalWeight ρ^2) * Q n ω^2) μ :=
    (h.memLp_weightedCrossSum hw hC hbdd T n).integrable_sq.const_mul _
  have heq (n : ℕ) (ω : Ω) : weightedCrossSum (correlatedNoise ρ B Z) B w T n ω - ρ * I ω =
      ρ * eB n ω + orthogonalWeight ρ * Q n ω := by
    rw [weightedCrossSum_correlated]
    dsimp [eB, Q]
    ring
  have hupper : Tendsto (fun n : ℕ => (2*ρ^2) * (∫ ω, eB n ω^2 ∂μ) +
      (2*orthogonalWeight ρ^2) * (∫ ω, Q n ω^2 ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hbl.const_mul (2*ρ^2)).add (hcl.const_mul (2*orthogonalWeight ρ^2))
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) _ hupper
  intro n
  calc
    _ ≤ ∫ ω, (2*ρ^2) * eB n ω^2 + (2*orthogonalWeight ρ^2) * Q n ω^2 ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        ((hib n).add (hiq n))
      filter_upwards [] with ω
      change (weightedCrossSum (correlatedNoise ρ B Z) B w T n ω - ρ * I ω)^2 ≤ _
      rw [heq]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (ρ * eB n ω - orthogonalWeight ρ * Q n ω)]
    _ = _ := by rw [integral_add (hib n) (hiq n), integral_const_mul, integral_const_mul]

end MathFin.FilteredIto.CommonNoise
