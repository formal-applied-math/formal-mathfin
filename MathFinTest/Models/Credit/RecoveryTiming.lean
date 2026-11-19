/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Recovery-timing examples

Special cases of `recoveryTiming_value_sub`: a `τ = T` atom, constant discounting, zero recovery,
default at time zero, and a non-flat curve with a nonzero timing difference. Each case applies the
endpoint and evaluates the contract values directly.
-/

open MeasureTheory MathFin.Contracts
open scoped NNReal

private theorem int_ind {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (u : ℝ≥0) :
    Integrable (defaultIndicator τ () u) Q :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_le hτ measurable_const)

private theorem int_one_sub_ind {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (u : ℝ≥0) :
    Integrable (fun ω ↦ 1 - defaultIndicator τ () u ω) Q :=
  (integrable_const (1 : ℝ)).sub (int_ind Q τ hτ u)

private theorem pw_mat {Ω : Type*} (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0) (ρ : ℝ) (ω : Ω) :
    (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T))).pathPV D
      (scenarioAt (defaultIndicator τ) ω)
      = D T * (ρ * defaultIndicator τ () T ω) := by
  simp only [Contract.pathPV, Contract.cashflows, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Payoff.eval, scenarioAt]
  ring

private theorem pw_face {Ω : Type*} (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0) (F : ℝ) (ω : Ω) :
    (Contract.pay T (Payoff.mul (Payoff.const F)
      (Payoff.sub (Payoff.const 1) (Payoff.obs () T)))).pathPV D
      (scenarioAt (defaultIndicator τ) ω)
      = D T * (F * (1 - defaultIndicator τ () T ω)) := by
  simp only [Contract.pathPV, Contract.cashflows, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Payoff.eval, scenarioAt]
  ring

private theorem dirac_mat_value {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ω₀ : Ω) (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0) (ρ : ℝ) :
    (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T))).value
      (Measure.dirac ω₀) (fun t _ ↦ D t) (defaultIndicator τ)
      = D T * (ρ * defaultIndicator τ () T ω₀) := by
  simp only [Contract.value, integral_dirac, pw_mat]

private theorem dirac_face_value {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ω₀ : Ω) (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0) (F : ℝ) :
    (Contract.pay T (Payoff.mul (Payoff.const F)
      (Payoff.sub (Payoff.const 1) (Payoff.obs () T)))).value
      (Measure.dirac ω₀) (fun t _ ↦ D t) (defaultIndicator τ)
      = D T * (F * (1 - defaultIndicator τ () T ω₀)) := by
  simp only [Contract.value, integral_dirac, pw_face]

private theorem dirac_prot_value {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ω₀ : Ω) (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0) (R : ℝ) :
    (cdsProtectionAtDefault T R).value (Measure.dirac ω₀) (fun t _ ↦ D t)
      (defaultIndicator τ)
      = (1 - R) * (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal) (τ ω₀) := by
  simp only [value_cdsProtectionAtDefault, integral_dirac]

private theorem int_prot_base {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (T : ℝ≥0) (hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t)
    (hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B) (hD : Measurable D) :
    Integrable (fun ω : Ω ↦ D (τ ω).toNNReal * defaultIndicator τ () T ω) Q := by
  obtain ⟨B, hB⟩ := hDbound
  have hBpos : 0 < B := lt_of_lt_of_le (hDpos 0 zero_le) (hB 0 zero_le)
  have hmeasD : Measurable (fun ω : Ω ↦ D (τ ω).toNNReal) :=
    hD.comp hτ.real_toNNReal
  have hNQ : Integrable (defaultIndicator τ () T) Q := int_ind Q τ hτ T
  have hbase_ae : AEStronglyMeasurable
      (fun ω : Ω ↦ D (τ ω).toNNReal * defaultIndicator τ () T ω) Q :=
    AEStronglyMeasurable.mul hmeasD.aestronglyMeasurable hNQ.aestronglyMeasurable
  have hbase_ineq : ∀ᵐ ω ∂Q,
      ‖D (τ ω).toNNReal * defaultIndicator τ () T ω‖ ≤ B := by
    refine ae_of_all _ fun ω ↦ ?_
    by_cases h : τ ω ≤ (T : ℝ)
    · have hle : (τ ω).toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 h
      have h1 : 0 < D (τ ω).toNNReal := hDpos _ hle
      have h2 : D (τ ω).toNNReal ≤ B := hB _ hle
      simp only [defaultIndicator, Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte,
        Pi.one_apply, mul_one, Real.norm_eq_abs, abs_of_pos h1]
      exact h2
    · simp only [defaultIndicator, Set.indicator, Set.mem_ofPred_eq, h, ↓reduceIte, mul_zero,
        norm_zero]
      exact hBpos.le
  exact Integrable.mono' (integrable_const B) hbase_ae hbase_ineq

private theorem int_prot {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (T : ℝ≥0) (hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t)
    (hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B) (hD : Measurable D) :
    Integrable (fun ω ↦ (cdsProtectionAtDefault T 0).pathPV D
      (scenarioAt (defaultIndicator τ) ω)) Q := by
  simpa [pathPV_cdsProtectionAtDefault] using
    int_prot_base Q τ hτ D T hDpos hDbound hD

private theorem int_scale {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (T : ℝ≥0) (ρ : ℝ) (hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t)
    (hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B) (hD : Measurable D) :
    Integrable (fun ω ↦ (Contract.scale ρ (cdsProtectionAtDefault T 0)).pathPV D
      (scenarioAt (defaultIndicator τ) ω)) Q := by
  simp only [Contract.pathPV_scale]
  exact (int_prot Q τ hτ D T hDpos hDbound hD).const_mul ρ

private theorem int_mat {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (T : ℝ≥0) (ρ : ℝ) :
    Integrable (fun ω ↦ (Contract.pay T
      (Payoff.mul (Payoff.const ρ) (Payoff.obs () T))).pathPV D
      (scenarioAt (defaultIndicator τ) ω)) Q := by
  simpa [pw_mat] using ((int_ind Q τ hτ T).const_mul ρ).const_mul (D T)

private theorem int_face {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (T : ℝ≥0) (F : ℝ) :
    Integrable (fun ω ↦ (Contract.pay T (Payoff.mul (Payoff.const F)
      (Payoff.sub (Payoff.const 1) (Payoff.obs () T)))).pathPV D
      (scenarioAt (defaultIndicator τ) ω)) Q := by
  simpa [pw_face] using ((int_one_sub_ind Q τ hτ T).const_mul F).const_mul (D T)

/-- A `τ = T` atom has no timing difference: discounting at `τ` agrees with `T`. -/
example (T : ℝ≥0) (F ρ : ℝ) (D : ℝ≥0 → ℝ) (hD : Measurable D)
    (hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t)
    (hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B) :
    ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          (Measure.dirac ()) (fun t _ ↦ D t) (defaultIndicator (fun _ : Unit ↦ (T : ℝ))))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            (Measure.dirac ()) (fun t _ ↦ D t)
            (defaultIndicator (fun _ : Unit ↦ (T : ℝ)))) = 0 := by
  have hτ : Measurable (fun _ : Unit ↦ (T : ℝ)) := measurable_const
  have hmem : (T : ℝ) ∈ Set.Iic (T : ℝ) := Set.mem_Iic.2 le_rfl
  have hInt : (∫ ω, (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal - D T)
      ((fun _ : Unit ↦ (T : ℝ)) ω) ∂Measure.dirac ()) = 0 := by
    rw [integral_dirac]
    simp
  have _ : ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          (Measure.dirac ()) (fun t _ ↦ D t) (defaultIndicator (fun _ : Unit ↦ (T : ℝ))))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            (Measure.dirac ()) (fun t _ ↦ D t)
            (defaultIndicator (fun _ : Unit ↦ (T : ℝ)))) = 0 := by
    rw [Contract.value_both _ _ _ _ _ (int_scale _ _ hτ _ _ _ hDpos hDbound hD)
      (int_face _ _ hτ _ _ _),
      Contract.value_both _ _ _ _ _ (int_mat _ _ hτ _ _ _) (int_face _ _ hτ _ _ _),
      Contract.value_scale, dirac_prot_value, dirac_mat_value, dirac_face_value]
    simp [defaultIndicator, Set.indicator]
    ring
  rw [recoveryTiming_value_sub _ _ _ hτ _ hD _ _ _ hDpos hDbound, hInt, mul_zero]

/-- Constant discounting has no timing difference, for any default time. -/
example (Ω : Type*) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ) (T : ℝ≥0) (F ρ : ℝ) (c : ℝ)
    (hc : 0 < c) (hDconst : ∀ t : ℝ≥0, D t = c) :
    ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          Q (fun t _ ↦ D t) (defaultIndicator τ))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            Q (fun t _ ↦ D t) (defaultIndicator τ)) = 0 := by
  have hD : Measurable D := by
    have hEq : D = fun _ : ℝ≥0 ↦ c := funext hDconst
    rw [hEq]
    exact measurable_const
  have hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t := fun t _ ↦ by simp [hDconst t, hc]
  have hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B :=
    ⟨c, fun t _ ↦ by simp [hDconst t]⟩
  have hInt : (∫ ω, (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal - D T)
      (τ ω) ∂Q) = 0 :=
    integral_eq_zero_of_ae (ae_of_all _ fun ω ↦ by
      by_cases h : τ ω ≤ (T : ℝ)
      · simp [Set.indicator, h, hDconst]
      · simp [Set.indicator, h])
  have _ : ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          Q (fun t _ ↦ D t) (defaultIndicator τ))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            Q (fun t _ ↦ D t) (defaultIndicator τ)) = 0 := by
    have hNQ : Integrable (defaultIndicator τ () T) Q := int_ind Q τ hτ T
    have hbaseC : Integrable
        (fun ω ↦ D (τ ω).toNNReal * defaultIndicator τ () T ω) Q :=
      (hNQ.const_mul c).congr (ae_of_all _ fun ω ↦ by simp [hDconst])
    have hprotC : Integrable (fun ω ↦ (cdsProtectionAtDefault T 0).pathPV D
        (scenarioAt (defaultIndicator τ) ω)) Q := by
      simpa [pathPV_cdsProtectionAtDefault] using hbaseC
    have hscaleC : Integrable (fun ω ↦ (Contract.scale ρ
        (cdsProtectionAtDefault T 0)).pathPV D (scenarioAt (defaultIndicator τ) ω)) Q := by
      simp only [Contract.pathPV_scale]
      exact hprotC.const_mul ρ
    have eINDc : (∫ ω, (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal) (τ ω) ∂Q)
        = ∫ ω, c * defaultIndicator τ () T ω ∂Q :=
      integral_congr_ae (ae_of_all _ fun ω ↦ by
        by_cases h : τ ω ≤ (T : ℝ)
        · simp [defaultIndicator, Set.indicator, h, hDconst]
        · simp [defaultIndicator, Set.indicator, h])
    have eProt : (Contract.scale ρ (cdsProtectionAtDefault T 0)).value Q (fun t _ ↦ D t)
        (defaultIndicator τ) = ρ * (c * ∫ ω, defaultIndicator τ () T ω ∂Q) := by
      rw [Contract.value_scale, value_cdsProtectionAtDefault, eINDc, integral_const_mul]
      ring
    have eMat : (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T))).value Q
        (fun t _ ↦ D t) (defaultIndicator τ)
        = c * (ρ * ∫ ω, defaultIndicator τ () T ω ∂Q) := by
      have g1 : (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T))).value Q
          (fun t _ ↦ D t) (defaultIndicator τ)
          = ∫ ω, c * (ρ * defaultIndicator τ () T ω) ∂Q := by
        rw [Contract.value]
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        simp [pw_mat, hDconst T]
      rw [g1, integral_const_mul, integral_const_mul]
    have hFv : (Contract.pay T (Payoff.mul (Payoff.const F)
        (Payoff.sub (Payoff.const 1) (Payoff.obs () T)))).value Q (fun t _ ↦ D t)
        (defaultIndicator τ)
        = ∫ ω, D T * (F * (1 - defaultIndicator τ () T ω)) ∂Q := by
      rw [Contract.value]
      exact integral_congr_ae (ae_of_all _ (pw_face D τ T F))
    rw [Contract.value_both _ _ _ _ _ hscaleC (int_face Q τ hτ D T F),
      Contract.value_both _ _ _ _ _ (int_mat Q τ hτ D T ρ) (int_face Q τ hτ D T F),
      eProt, eMat, hFv]
    ring
  rw [recoveryTiming_value_sub _ _ _ hτ _ hD _ _ _ hDpos hDbound, hInt, mul_zero]

/-- Zero recovery pays nothing either way, so the timing difference is zero. -/
example (Ω : Type*) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ) (hτ : Measurable τ) (D : ℝ≥0 → ℝ) (hD : Measurable D) (T : ℝ≥0)
    (F : ℝ)
    (hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t)
    (hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B) :
    ((Contract.both (Contract.scale 0 (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          Q (fun t _ ↦ D t) (defaultIndicator τ))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const 0) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            Q (fun t _ ↦ D t) (defaultIndicator τ)) = 0 := by
  have hmat0 : (Contract.pay T (Payoff.mul (Payoff.const 0) (Payoff.obs () T))).value Q
      (fun t _ ↦ D t) (defaultIndicator τ) = 0 := by
    have g : (Contract.pay T (Payoff.mul (Payoff.const 0) (Payoff.obs () T))).value Q
        (fun t _ ↦ D t) (defaultIndicator τ)
        = ∫ ω, D T * (0 * defaultIndicator τ () T ω) ∂Q := by
      rw [Contract.value]
      exact integral_congr_ae (ae_of_all _ (pw_mat D τ T 0))
    rw [g]
    exact integral_eq_zero_of_ae (ae_of_all _ fun ω ↦ by simp)
  have _ : ((Contract.both (Contract.scale 0 (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          Q (fun t _ ↦ D t) (defaultIndicator τ))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const 0) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            Q (fun t _ ↦ D t) (defaultIndicator τ)) = 0 := by
    have hscale0 : (Contract.scale 0 (cdsProtectionAtDefault T 0)).value Q
        (fun t _ ↦ D t) (defaultIndicator τ) = 0 := by
      rw [Contract.value_scale]
      exact zero_mul _
    rw [Contract.value_both _ _ _ _ _ (int_scale Q τ hτ D T 0 hDpos hDbound hD)
      (int_face Q τ hτ D T F),
      Contract.value_both _ _ _ _ _ (int_mat Q τ hτ D T 0) (int_face Q τ hτ D T F),
      hscale0, hmat0]
    ring
  rw [recoveryTiming_value_sub _ _ _ hτ _ hD _ _ _ hDpos hDbound, zero_mul]

/-- Default at time zero with `D 0 = 1` and `D T = d` gives `ρ * (1 - d)`. -/
example (T : ℝ≥0) (F ρ : ℝ) (D : ℝ≥0 → ℝ) (hD : Measurable D)
    (hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t)
    (hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B) (d : ℝ) (hD0 : D 0 = 1)
    (hDT : D T = d) :
    ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          (Measure.dirac ()) (fun t _ ↦ D t) (defaultIndicator (fun _ : Unit ↦ (0 : ℝ))))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            (Measure.dirac ()) (fun t _ ↦ D t)
            (defaultIndicator (fun _ : Unit ↦ (0 : ℝ)))) = ρ * (1 - d) := by
  have hτ : Measurable (fun _ : Unit ↦ (0 : ℝ)) := measurable_const
  have hmem0 : (0 : ℝ) ∈ Set.Iic (T : ℝ) := Set.mem_Iic.2 T.coe_nonneg
  have hInt : (∫ ω, (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal - D T)
      ((fun _ : Unit ↦ (0 : ℝ)) ω) ∂Measure.dirac ()) = 1 - d := by
    rw [integral_dirac]
    simp [hD0, hDT]
  have _ : ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          (Measure.dirac ()) (fun t _ ↦ D t) (defaultIndicator (fun _ : Unit ↦ (0 : ℝ))))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            (Measure.dirac ()) (fun t _ ↦ D t)
            (defaultIndicator (fun _ : Unit ↦ (0 : ℝ)))) = ρ * (1 - d) := by
    rw [Contract.value_both _ _ _ _ _ (int_scale _ _ hτ _ _ _ hDpos hDbound hD)
      (int_face _ _ hτ _ _ _),
      Contract.value_both _ _ _ _ _ (int_mat _ _ hτ _ _ _) (int_face _ _ hτ _ _ _),
      Contract.value_scale, dirac_prot_value, dirac_mat_value, dirac_face_value]
    simp [hD0, hDT, defaultIndicator, Set.indicator,
      T.coe_nonneg]
    ring
  rw [recoveryTiming_value_sub _ _ _ hτ _ hD _ _ _ hDpos hDbound, hInt]

/-- A non-flat curve gives a nonzero timing difference with positive probability. -/
example (T : ℝ≥0) (hT : T ≠ 0) (F ρ : ℝ) (hρ : ρ ≠ 0) (D : ℝ≥0 → ℝ)
    (hDdef : ∀ t : ℝ≥0, D t = (t : ℝ) + 1) :
    ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          (Measure.dirac ()) (fun t _ ↦ D t) (defaultIndicator (fun _ : Unit ↦ (0 : ℝ))))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            (Measure.dirac ()) (fun t _ ↦ D t)
            (defaultIndicator (fun _ : Unit ↦ (0 : ℝ)))) ≠ 0 := by
  have hτ : Measurable (fun _ : Unit ↦ (0 : ℝ)) := measurable_const
  have hD : Measurable D := by
    have hEq : D = fun t : ℝ≥0 ↦ (t : ℝ) + 1 := funext hDdef
    rw [hEq]
    exact measurable_coe_nnreal_real.add measurable_const
  have hDpos : ∀ t : ℝ≥0, t ≤ T → 0 < D t := by
    intro t _
    have hnn : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    simp only [hDdef t]
    positivity
  have hDbound : ∃ B : ℝ, ∀ t : ℝ≥0, t ≤ T → D t ≤ B :=
    ⟨(T : ℝ) + 1, fun t ht ↦ by
      simp only [hDdef t]
      exact add_le_add_left (NNReal.coe_le_coe.mpr ht) 1⟩
  have hmem0 : (0 : ℝ) ∈ Set.Iic (T : ℝ) := Set.mem_Iic.2 T.coe_nonneg
  have hInt : (∫ ω, (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal - D T)
      ((fun _ : Unit ↦ (0 : ℝ)) ω) ∂Measure.dirac ()) = 1 - (↑T + 1) := by
    rw [integral_dirac]
    simp [hDdef]
  have _ : ((Contract.both (Contract.scale ρ (cdsProtectionAtDefault T 0))
        (Contract.pay T (Payoff.mul (Payoff.const F)
          (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
          (Measure.dirac ()) (fun t _ ↦ D t) (defaultIndicator (fun _ : Unit ↦ (0 : ℝ))))
      - ((Contract.both (Contract.pay T (Payoff.mul (Payoff.const ρ) (Payoff.obs () T)))
          (Contract.pay T (Payoff.mul (Payoff.const F)
            (Payoff.sub (Payoff.const 1) (Payoff.obs () T))))).value
            (Measure.dirac ()) (fun t _ ↦ D t)
            (defaultIndicator (fun _ : Unit ↦ (0 : ℝ)))) = ρ * (1 - (↑T + 1)) := by
    rw [Contract.value_both _ _ _ _ _ (int_scale _ _ hτ _ _ _ hDpos hDbound hD)
      (int_face _ _ hτ _ _ _),
      Contract.value_both _ _ _ _ _ (int_mat _ _ hτ _ _ _) (int_face _ _ hτ _ _ _),
      Contract.value_scale, dirac_prot_value, dirac_mat_value, dirac_face_value]
    simp [hDdef, defaultIndicator, Set.indicator,
      T.coe_nonneg]
    ring
  rw [recoveryTiming_value_sub _ _ _ hτ _ hD _ _ _ hDpos hDbound, hInt]
  have hT' : (T : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hT
  have h2 : (1 : ℝ) - (↑T + 1) = -↑T := by ring
  rw [h2]
  exact mul_ne_zero hρ (neg_ne_zero.mpr hT')
