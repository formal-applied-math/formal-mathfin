/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Finite credibility variance checks

Concrete two-risk two-observation checks of
`MathFin.variance_sampleMean`: a nonconjugate mixture with exact
rational values, computed directly and via the theorem, plus the degenerate
cases `a = 0` (both risks share one conditional mean) and `v = 0`
(degenerate conditional laws with distinct means).
-/

open MeasureTheory ProbabilityTheory

namespace FiniteCredibilityVarianceTest

instance : MeasurableSpace (Fin 2) := ⊤

instance : DiscreteMeasurableSpace (Fin 2) := ⟨fun _ ↦ trivial⟩

instance : MeasurableSingletonClass (Fin 2) := ⟨fun _ ↦ MeasurableSet.of_discrete⟩

/-- Sums over `Fin 2 → Fin 2` expand into four explicit terms. -/
private theorem sum_fin2_arrow (G : (Fin 2 → Fin 2) → ℝ) :
    (∑ x, G x) = (G ![0, 0] + G ![0, 1]) + (G ![1, 0] + G ![1, 1]) := by
  have h := (Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm G).symm
  rw [h]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Main two-risk mixture weights. -/
private noncomputable def p_main : Fin 2 → ℝ := ![1 / 3, 2 / 3]

/-- Main conditional weights (nonconjugate). -/
private noncomputable def w_main : Fin 2 → Fin 2 → ℝ := ![![1 / 4, 3 / 4], ![1 / 2, 1 / 2]]

/-- Observation values shared by all scenarios. -/
private def v_main : Fin 2 → ℝ := ![0, 10]

private theorem hp_main : ∀ θ, 0 ≤ p_main θ := by
  intro θ
  fin_cases θ <;> simp [p_main] ; norm_num

private theorem hp1_main : ∑ θ, p_main θ = 1 := by
  norm_num [p_main, Fin.sum_univ_two]

private theorem hw_main : ∀ θ ξ, 0 ≤ w_main θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> simp [w_main] ; norm_num

private theorem hw1_main : ∀ θ, ∑ ξ, w_main θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_main, Fin.sum_univ_two]

private theorem hnonneg_main :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_main a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_main θ (x i)))

/-- The identity on the main mixture, via the theorem. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_main)
      = variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main :=
  MathFin.variance_sampleMean 2 (by norm_num) p_main w_main v_main
    hp_main hp1_main hw_main hw1_main

/-- Direct sample-mean variance computation on the main mixture. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_main) = 925 / 72 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_main) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
      ∂(MathFin.mixtureLaw 2 p_main w_main)) = 35 / 6 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_main, v_main]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main]
  norm_num

/-- Direct conditional-mean variance computation on the main mixture. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_main) = 25 / 18 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_main) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, MathFin.condMean (w_main ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_main)) = 35 / 6 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
  norm_num

/-- Mean conditional variance on the main mixture. -/
example : ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main = 275 / 12 := by
  norm_num [p_main, w_main, v_main, MathFin.condVar, MathFin.condMean,
    Fin.sum_univ_two]

/-- The main-mixture values satisfy the decomposition. -/
example : (925 / 72 : ℝ) = 25 / 18 + ((2 : ℕ) : ℝ)⁻¹ * (275 / 12) := by
  norm_num

/-- Conditional weights with a shared conditional mean (`a = 0` case). -/
private noncomputable def w_zeroMean :
    Fin 2 → Fin 2 → ℝ := ![![1 / 2, 1 / 2], ![1 / 2, 1 / 2]]

private theorem hw_zeroMean : ∀ θ ξ, 0 ≤ w_zeroMean θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> simp [w_zeroMean]

private theorem hw1_zeroMean : ∀ θ, ∑ ξ, w_zeroMean θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_zeroMean, Fin.sum_univ_two]

private theorem hnonneg_zeroMean :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_zeroMean a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_zeroMean θ (x i)))

/-- The identity when both risks share one conditional mean. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_zeroMean)
      = variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
          MathFin.condMean (w_zeroMean ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_zeroMean)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_zeroMean θ)
          v_main :=
  MathFin.variance_sampleMean 2 (by norm_num) p_main w_zeroMean v_main
    hp_main hp1_main hw_zeroMean hw1_zeroMean

/-- The conditional-mean variance vanishes when means coincide. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
        MathFin.condMean (w_zeroMean ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_zeroMean) = 0 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
        MathFin.condMean (w_zeroMean ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_zeroMean) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, MathFin.condMean (w_zeroMean ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_zeroMean)) = 5 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroMean _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_zeroMean, v_main, MathFin.condMean]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroMean _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_zeroMean, v_main, MathFin.condMean]
  norm_num

/-- Direct sample-mean variance when both risks share one mean. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_zeroMean) = 25 / 2 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_zeroMean) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
      ∂(MathFin.mixtureLaw 2 p_main w_zeroMean)) = 5 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroMean _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_zeroMean, v_main]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroMean _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_zeroMean, v_main]
  norm_num

/-- Mean conditional variance when both risks share one mean. -/
example : ∑ θ, p_main θ * MathFin.condVar (w_zeroMean θ) v_main = 25 := by
  norm_num [p_main, w_zeroMean, v_main, MathFin.condVar, MathFin.condMean,
    Fin.sum_univ_two]

/-- The shared-mean values satisfy the decomposition. -/
example : (25 / 2 : ℝ) = 0 + ((2 : ℕ) : ℝ)⁻¹ * 25 := by
  norm_num

/-- Degenerate conditional weights with distinct means (`v = 0` case). -/
private noncomputable def w_zeroVar : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

private theorem hw_zeroVar : ∀ θ ξ, 0 ≤ w_zeroVar θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> simp [w_zeroVar]

private theorem hw1_zeroVar : ∀ θ, ∑ ξ, w_zeroVar θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_zeroVar, Fin.sum_univ_two]

private theorem hnonneg_zeroVar :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_zeroVar a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_zeroVar θ (x i)))

/-- The identity for degenerate conditional laws with distinct means. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_zeroVar)
      = variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
          MathFin.condMean (w_zeroVar ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_zeroVar)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_zeroVar θ)
          v_main :=
  MathFin.variance_sampleMean 2 (by norm_num) p_main w_zeroVar v_main
    hp_main hp1_main hw_zeroVar hw1_zeroVar

/-- Direct sample-mean variance for degenerate conditional laws. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_zeroVar) = 200 / 9 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_zeroVar) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
      ∂(MathFin.mixtureLaw 2 p_main w_zeroVar)) = 20 / 3 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroVar _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_zeroVar, v_main]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroVar _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_zeroVar, v_main]
  norm_num

/-- Direct conditional-mean variance for degenerate conditional laws. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
        MathFin.condMean (w_zeroVar ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_zeroVar) = 200 / 9 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
        MathFin.condMean (w_zeroVar ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_zeroVar) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, MathFin.condMean (w_zeroVar ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_zeroVar)) = 20 / 3 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroVar _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_zeroVar, v_main, MathFin.condMean]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_zeroVar _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_zeroVar, v_main, MathFin.condMean]
  norm_num

/-- Mean conditional variance vanishes for degenerate laws. -/
example : ∑ θ, p_main θ * MathFin.condVar (w_zeroVar θ) v_main = 0 := by
  norm_num [p_main, w_zeroVar, v_main, MathFin.condVar, MathFin.condMean,
    Fin.sum_univ_two]

/-- The degenerate-law values satisfy the decomposition. -/
example : (200 / 9 : ℝ) = 200 / 9 + ((2 : ℕ) : ℝ)⁻¹ * 0 := by
  norm_num

end FiniteCredibilityVarianceTest
