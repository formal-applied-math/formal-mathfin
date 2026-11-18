/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Finite credibility optimality checks

Concrete two-risk two-observation checks of `MathFin.buhlmann_mse_le` and
`MathFin.buhlmann_coefficient_bounds`: a nonconjugate mixture with exact
rational values, plus the degenerate cases `a = 0` (both risks share one
conditional mean, so `Z = 0`) and `v = 0` (degenerate conditional laws
with distinct means, so `Z = 1`), and a comparison of the affine optimum
with the posterior mean at `X = (0, 0)`.
-/

open MeasureTheory ProbabilityTheory

namespace FiniteCredibilityOptimalityTest

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

/-- Mixture mean of the main mixture: `μ = 35 / 6`. -/
private theorem hmu_main :
    (∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main) = 35 / 6 := by
  norm_num [Fin.sum_univ_two, p_main, w_main, v_main, MathFin.condMean]

/-- Expectation of the conditional mean on the main mixture. -/
private theorem hmean_main : (∫ ω, MathFin.condMean (w_main ω.1) v_main
    ∂(MathFin.mixtureLaw 2 p_main w_main)) = 35 / 6 := by
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
  norm_num

/-- Variance of the conditional mean on the main mixture: `a = 25 / 18`. -/
private theorem hVar_main : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_main) = 25 / 18 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_main) :=
    (measurable_of_finite _).aemeasurable
  rw [variance_eq_integral hX, hmean_main]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
  norm_num

/-- Mean conditional variance on the main mixture: `v = 275 / 12`. -/
private theorem hv_main :
    (∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main) = 275 / 12 := by
  norm_num [Fin.sum_univ_two, p_main, w_main, v_main,
    MathFin.condVar, MathFin.condMean]

/-- Bühlmann coefficient on the main mixture: `Z = 4 / 37`. -/
private theorem hZ_main :
    variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main)
      = 4 / 37 := by
  rw [hVar_main, hv_main]
  norm_num

/-- Positivity side condition for the main mixture endpoints. -/
private theorem hd_main : 0 < variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_main)
      + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main := by
  rw [hVar_main, hv_main]
  norm_num

/-- Direct optimal mean squared error on the main mixture: `275 / 222`. -/
private theorem hMSEopt_main : (∫ ω, (MathFin.condMean (w_main ω.1) v_main
      - ((∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main)
        + (variance
            (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
              MathFin.condMean (w_main ω.1) v_main)
            (MathFin.mixtureLaw 2 p_main w_main)
          / (variance
              (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
                MathFin.condMean (w_main ω.1) v_main)
              (MathFin.mixtureLaw 2 p_main w_main)
            + ((2 : ℕ) : ℝ)⁻¹
              * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main))
        * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
          - ∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_main)) = 275 / 222 := by
  rw [hVar_main, hv_main, hmu_main]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
  norm_num

/-- Direct mean-only mean squared error on the main mixture: `25 / 18`. -/
private theorem hMSEmean_main : (∫ ω, (MathFin.condMean (w_main ω.1) v_main
      - (35 / 6 + 0 * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_main)) = 25 / 18 := by
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_main _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_main, v_main, MathFin.condMean]
  norm_num

/-- The Bühlmann bound on the main mixture, via the theorem. -/
example : (∫ ω, (MathFin.condMean (w_main ω.1) v_main
      - ((∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main)
        + (variance
            (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
              MathFin.condMean (w_main ω.1) v_main)
            (MathFin.mixtureLaw 2 p_main w_main)
          / (variance
              (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
                MathFin.condMean (w_main ω.1) v_main)
              (MathFin.mixtureLaw 2 p_main w_main)
            + ((2 : ℕ) : ℝ)⁻¹
              * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main))
        * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
          - ∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_main))
    ≤ (∫ ω, (MathFin.condMean (w_main ω.1) v_main
      - (35 / 6 + 0 * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_main)) :=
  MathFin.buhlmann_mse_le 2 (by norm_num) p_main w_main v_main
    hp_main hp1_main hw_main hw1_main hd_main (35 / 6) 0

/-- The coefficient bounds on the main mixture, via the theorem. -/
example : 0 ≤ variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main)
    ∧ variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_main ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_main)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main)
      ≤ 1 :=
  MathFin.buhlmann_coefficient_bounds 2 (by norm_num) p_main w_main v_main
    hp_main hp1_main hw_main hw1_main hd_main

/-- Conditional weights for the `a = 0` branch (shared conditional mean). -/
private noncomputable def w_a0 : Fin 2 → Fin 2 → ℝ := ![![1 / 2, 1 / 2], ![1 / 2, 1 / 2]]

private theorem hw_a0 : ∀ θ ξ, 0 ≤ w_a0 θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> norm_num [w_a0]

private theorem hw1_a0 : ∀ θ, ∑ ξ, w_a0 θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_a0, Fin.sum_univ_two]

private theorem hnonneg_a0 :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_a0 a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_a0 θ (x i)))

/-- Mixture mean for the `a = 0` branch: `μ = 5`. -/
private theorem hmu_a0 :
    (∑ θ, p_main θ * MathFin.condMean (w_a0 θ) v_main) = 5 := by
  norm_num [Fin.sum_univ_two, p_main, w_a0, v_main, MathFin.condMean]

/-- Expectation of the conditional mean for the `a = 0` branch. -/
private theorem hmean_a0 : (∫ ω, MathFin.condMean (w_a0 ω.1) v_main
    ∂(MathFin.mixtureLaw 2 p_main w_a0)) = 5 := by
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_a0 _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_a0, v_main, MathFin.condMean]
  norm_num

/-- Variance of the conditional mean for the `a = 0` branch: `a = 0`. -/
private theorem hVar_a0 : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_a0) = 0 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_a0) :=
    (measurable_of_finite _).aemeasurable
  rw [variance_eq_integral hX, hmean_a0]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_a0 _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_a0, v_main, MathFin.condMean]
  norm_num

/-- Mean conditional variance for the `a = 0` branch: `v = 25`. -/
private theorem hv_a0 :
    (∑ θ, p_main θ * MathFin.condVar (w_a0 θ) v_main) = 25 := by
  norm_num [Fin.sum_univ_two, p_main, w_a0, v_main,
    MathFin.condVar, MathFin.condMean]

/-- Bühlmann coefficient for the `a = 0` branch: `Z = 0`. -/
private theorem hZ_a0 :
    variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_a0)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_a0)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_a0 θ) v_main)
      = 0 := by
  rw [hVar_a0, hv_a0]
  norm_num

/-- Positivity side condition for the `a = 0` branch endpoints. -/
private theorem hd_a0 : 0 < variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_a0)
      + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_a0 θ) v_main := by
  rw [hVar_a0, hv_a0]
  norm_num

/-- The Bühlmann bound for the `a = 0` branch, via the theorem. -/
example : (∫ ω, (MathFin.condMean (w_a0 ω.1) v_main
      - ((∑ θ, p_main θ * MathFin.condMean (w_a0 θ) v_main)
        + (variance
            (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
              MathFin.condMean (w_a0 ω.1) v_main)
            (MathFin.mixtureLaw 2 p_main w_a0)
          / (variance
              (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
                MathFin.condMean (w_a0 ω.1) v_main)
              (MathFin.mixtureLaw 2 p_main w_a0)
            + ((2 : ℕ) : ℝ)⁻¹
              * ∑ θ, p_main θ * MathFin.condVar (w_a0 θ) v_main))
        * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
          - ∑ θ, p_main θ * MathFin.condMean (w_a0 θ) v_main))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_a0))
    ≤ (∫ ω, (MathFin.condMean (w_a0 ω.1) v_main
      - (0 + 0 * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_a0)) :=
  MathFin.buhlmann_mse_le 2 (by norm_num) p_main w_a0 v_main
    hp_main hp1_main hw_a0 hw1_a0 hd_a0 0 0

/-- The coefficient bounds for the `a = 0` branch, via the theorem. -/
example : 0 ≤ variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_a0)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_a0)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_a0 θ) v_main)
    ∧ variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_a0)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_a0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_a0)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_a0 θ) v_main)
      ≤ 1 :=
  MathFin.buhlmann_coefficient_bounds 2 (by norm_num) p_main w_a0 v_main
    hp_main hp1_main hw_a0 hw1_a0 hd_a0

/-- Conditional weights for the `v = 0` branch (degenerate laws). -/
private def w_v0 : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

private theorem hw_v0 : ∀ θ ξ, 0 ≤ w_v0 θ ξ := by
  intro θ ξ
  fin_cases θ <;> fin_cases ξ <;> norm_num [w_v0]

private theorem hw1_v0 : ∀ θ, ∑ ξ, w_v0 θ ξ = 1 := by
  intro θ
  fin_cases θ <;> norm_num [w_v0, Fin.sum_univ_two]

private theorem hnonneg_v0 :
    ∀ a ∈ (Finset.univ : Finset (Fin 2 × (Fin 2 → Fin 2))),
      0 ≤ p_main a.1 * ∏ i, w_v0 a.1 (a.2 i) := by
  intro a _
  obtain ⟨θ, x⟩ := a
  exact mul_nonneg (hp_main θ)
    (Finset.prod_nonneg (fun i _ => hw_v0 θ (x i)))

/-- Mixture mean for the `v = 0` branch: `μ = 20 / 3`. -/
private theorem hmu_v0 :
    (∑ θ, p_main θ * MathFin.condMean (w_v0 θ) v_main) = 20 / 3 := by
  norm_num [Fin.sum_univ_two, p_main, w_v0, v_main, MathFin.condMean]

/-- Expectation of the conditional mean for the `v = 0` branch. -/
private theorem hmean_v0 : (∫ ω, MathFin.condMean (w_v0 ω.1) v_main
    ∂(MathFin.mixtureLaw 2 p_main w_v0)) = 20 / 3 := by
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_v0 _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_v0, v_main, MathFin.condMean]
  norm_num

/-- Variance of the conditional mean for the `v = 0` branch: `a = 200 / 9`. -/
private theorem hVar_v0 : variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_v0) = 200 / 9 := by
  have hX : AEMeasurable
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_v0) :=
    (measurable_of_finite _).aemeasurable
  rw [variance_eq_integral hX, hmean_v0]
  simp only [MathFin.mixtureLaw]
  rw [MeasureTheory.Measure.integral_ofWeights _ hnonneg_v0 _]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two,
    sum_fin2_arrow, p_main, w_v0, v_main, MathFin.condMean]
  norm_num

/-- Mean conditional variance for the `v = 0` branch: `v = 0`. -/
private theorem hv_v0 :
    (∑ θ, p_main θ * MathFin.condVar (w_v0 θ) v_main) = 0 := by
  norm_num [Fin.sum_univ_two, p_main, w_v0, v_main,
    MathFin.condVar, MathFin.condMean]

/-- Bühlmann coefficient for the `v = 0` branch: `Z = 1`. -/
private theorem hZ_v0 :
    variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_v0)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_v0)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_v0 θ) v_main)
      = 1 := by
  rw [hVar_v0, hv_v0]
  norm_num

/-- Positivity side condition for the `v = 0` branch endpoints. -/
private theorem hd_v0 : 0 < variance
      (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
      (MathFin.mixtureLaw 2 p_main w_v0)
      + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_v0 θ) v_main := by
  rw [hVar_v0, hv_v0]
  norm_num

/-- The Bühlmann bound for the `v = 0` branch, via the theorem. -/
example : (∫ ω, (MathFin.condMean (w_v0 ω.1) v_main
      - ((∑ θ, p_main θ * MathFin.condMean (w_v0 θ) v_main)
        + (variance
            (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
              MathFin.condMean (w_v0 ω.1) v_main)
            (MathFin.mixtureLaw 2 p_main w_v0)
          / (variance
              (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
                MathFin.condMean (w_v0 ω.1) v_main)
              (MathFin.mixtureLaw 2 p_main w_v0)
            + ((2 : ℕ) : ℝ)⁻¹
              * ∑ θ, p_main θ * MathFin.condVar (w_v0 θ) v_main))
        * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)
          - ∑ θ, p_main θ * MathFin.condMean (w_v0 θ) v_main))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_v0))
    ≤ (∫ ω, (MathFin.condMean (w_v0 ω.1) v_main
      - (0 + 0 * (((2 : ℕ) : ℝ)⁻¹ * ∑ i, v_main (ω.2 i)))) ^ 2
      ∂(MathFin.mixtureLaw 2 p_main w_v0)) :=
  MathFin.buhlmann_mse_le 2 (by norm_num) p_main w_v0 v_main
    hp_main hp1_main hw_v0 hw1_v0 hd_v0 0 0

/-- The coefficient bounds for the `v = 0` branch, via the theorem. -/
example : 0 ≤ variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_v0)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_v0)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_v0 θ) v_main)
    ∧ variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_v0)
      / (variance
        (fun ω : Fin 2 × (Fin 2 → Fin 2) => MathFin.condMean (w_v0 ω.1) v_main)
        (MathFin.mixtureLaw 2 p_main w_v0)
        + ((2 : ℕ) : ℝ)⁻¹ * ∑ θ, p_main θ * MathFin.condVar (w_v0 θ) v_main)
      ≤ 1 :=
  MathFin.buhlmann_coefficient_bounds 2 (by norm_num) p_main w_v0 v_main
    hp_main hp1_main hw_v0 hw1_v0 hd_v0

/-- At `X = (0, 0)` the posterior mean (`95 / 18`) differs from the affine
optimum (`385 / 74`): the affine predictor is not the posterior mean. -/
example : (p_main 0 * (w_main 0 0) ^ 2 * MathFin.condMean (w_main 0) v_main
      + p_main 1 * (w_main 1 0) ^ 2 * MathFin.condMean (w_main 1) v_main)
      / (p_main 0 * (w_main 0 0) ^ 2 + p_main 1 * (w_main 1 0) ^ 2)
      = 95 / 18
    ∧ ((∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main)
      + (variance
          (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
            MathFin.condMean (w_main ω.1) v_main)
          (MathFin.mixtureLaw 2 p_main w_main)
        / (variance
            (fun ω : Fin 2 × (Fin 2 → Fin 2) =>
              MathFin.condMean (w_main ω.1) v_main)
            (MathFin.mixtureLaw 2 p_main w_main)
          + ((2 : ℕ) : ℝ)⁻¹
            * ∑ θ, p_main θ * MathFin.condVar (w_main θ) v_main))
        * (0 - ∑ θ, p_main θ * MathFin.condMean (w_main θ) v_main))
      = 385 / 74
    ∧ (95 / 18 : ℝ) ≠ 385 / 74 := by
  refine ⟨?_, ?_, by norm_num⟩
  · norm_num [p_main, w_main, v_main, MathFin.condMean, Fin.sum_univ_two]
  · rw [hmu_main, hZ_main]
    norm_num

end FiniteCredibilityOptimalityTest
