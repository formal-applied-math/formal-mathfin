/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Finite credibility covariance checks

Concrete two-risk two-observation checks of
`MathFin.covariance_condMean_sampleMean`: a nonconjugate mixture with exact
rational values, computed directly and via the theorem, plus the degenerate
cases `a = 0` (both risks share one conditional mean) and `v = 0`
(degenerate conditional laws with distinct means).
-/

open MeasureTheory ProbabilityTheory

namespace FiniteCredibilityCovarianceTest

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
example : covariance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_main)
      = variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main) :=
  MathFin.covariance_condMean_sampleMean 2 (by norm_num) p_main w_main v_main
    hp_main hp1_main hw_main hw1_main

/-- Direct variance computation on the main mixture. -/
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

/-- Direct covariance computation on the main mixture. -/
example : covariance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_main) = 25 / 18 := by
  have hmeanX : (∫ ω, MathFin.condMean (w_main ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_main)) = 35 / 6 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
    norm_num
  have hmeanY : (∫ ω, ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
      ∂(MathFin.mixtureLaw 2 p_main w_main)) = 35 / 6 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_main, v_main]
    norm_num
  simp only [covariance]
  rw [hmeanX, hmeanY]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
  norm_num

/-- Conditional weights with a shared conditional mean (`a = 0` case). -/
private noncomputable def w_eq : Fin 2 → Fin 2 → ℝ := ![![1 / 2, 1 / 2], ![1 / 2, 1 / 2]]

private theorem hw_eq : ∀ θ ξ, 0 ≤ w_eq θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> simp [w_eq]

private theorem hw1_eq : ∀ θ, ∑ ξ, w_eq θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_eq, Fin.sum_univ_two]

private theorem hnonneg_eq :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_eq a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_eq θ (x i)))

/-- The identity in the `a = 0` case, via the theorem. -/
example : covariance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_eq ω.1) v_main)
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_eq)
      = variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_eq ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_eq) :=
  MathFin.covariance_condMean_sampleMean 2 (by norm_num) p_main w_eq v_main
    hp_main hp1_main hw_eq hw1_eq

/-- Direct variance computation in the `a = 0` case. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_eq ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_eq) = 0 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_eq ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_eq) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, MathFin.condMean (w_eq ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_eq)) = 5 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_eq _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_eq, v_main, MathFin.condMean]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_eq _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_eq, v_main, MathFin.condMean]
  norm_num

/-- Direct covariance computation in the `a = 0` case. -/
example : covariance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_eq ω.1) v_main)
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_eq) = 0 := by
  have hmeanX : (∫ ω, MathFin.condMean (w_eq ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_eq)) = 5 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_eq _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_eq, v_main, MathFin.condMean]
    norm_num
  have hmeanY : (∫ ω, ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
      ∂(MathFin.mixtureLaw 2 p_main w_eq)) = 5 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_eq _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_eq, v_main]
    norm_num
  simp only [covariance]
  rw [hmeanX, hmeanY]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_eq _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_eq, v_main, MathFin.condMean]
  norm_num

/-- Degenerate conditional weights with distinct means (`v = 0` case). -/
private def w_deg : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

private theorem hw_deg : ∀ θ ξ, 0 ≤ w_deg θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> simp [w_deg]

private theorem hw1_deg : ∀ θ, ∑ ξ, w_deg θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_deg, Fin.sum_univ_two]

private theorem hnonneg_deg :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_deg a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_deg θ (x i)))

/-- The identity in the `v = 0` case, via the theorem. -/
example : covariance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_deg ω.1) v_main)
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_deg)
      = variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_deg ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_deg) :=
  MathFin.covariance_condMean_sampleMean 2 (by norm_num) p_main w_deg v_main
    hp_main hp1_main hw_deg hw1_deg

/-- Direct variance computation in the `v = 0` case. -/
example : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_deg ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_deg) = 200 / 9 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_deg ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_deg) :=
    (measurable_of_finite _).aemeasurable
  have hmean : (∫ ω, MathFin.condMean (w_deg ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_deg)) = 20 / 3 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_deg _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_deg, v_main, MathFin.condMean]
    norm_num
  rw [variance_eq_integral hX, hmean]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_deg _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_deg, v_main, MathFin.condMean]
  norm_num

/-- Direct covariance computation in the `v = 0` case. -/
example : covariance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_deg ω.1) v_main)
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i))
      (MathFin.mixtureLaw 2 p_main w_deg) = 200 / 9 := by
  have hmeanX : (∫ ω, MathFin.condMean (w_deg ω.1) v_main
      ∂(MathFin.mixtureLaw 2 p_main w_deg)) = 20 / 3 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_deg _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_deg, v_main, MathFin.condMean]
    norm_num
  have hmeanY : (∫ ω, ((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
      ∂(MathFin.mixtureLaw 2 p_main w_deg)) = 20 / 3 := by
    simp only [MathFin.mixtureLaw]
    rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_deg _]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
      sum_fin2_arrow, p_main, w_deg, v_main]
    norm_num
  simp only [covariance]
  rw [hmeanX, hmeanY]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_deg _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_deg, v_main, MathFin.condMean]
  norm_num

end FiniteCredibilityCovarianceTest
