/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Two-life annuity identity checks

Concrete checks of `MathFin.lastSurvivor_annuity_eq_value` on small finite probability spaces
with explicit lifetimes. Each example applies the endpoint and computes every contract value to
an explicit rational number.

* Identical lifetimes in general form (two payments on a two-point space).
* Disjoint survival events (one-point space).
* Correlated lives where joint survival is not the product of the marginals (two-point space).
* Both lives dead at every payment date.
* Death exactly at a payment date counts as dead.
* The empty schedule (`n = 0`).
-/

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFinTest

/-- The default indicator is one when death is on or before the date. -/
private theorem defaultIndicator_of_le {Ω : Type*} [MeasurableSpace Ω] {T : Ω → ℝ}
    {s : ℝ≥0} {ω : Ω} (h : T ω ≤ (s : ℝ)) : defaultIndicator T () s ω = 1 := by
  have hm : ω ∈ {x | T x ≤ (s : ℝ)} := h
  change Set.indicator {x | T x ≤ (s : ℝ)} (1 : Ω → ℝ) ω = 1
  exact Set.indicator_of_mem hm _

/-- The default indicator is zero when death is strictly after the date. -/
private theorem defaultIndicator_of_gt {Ω : Type*} [MeasurableSpace Ω] {T : Ω → ℝ}
    {s : ℝ≥0} {ω : Ω} (h : (s : ℝ) < T ω) : defaultIndicator T () s ω = 0 := by
  have hm : ω ∉ {x | T x ≤ (s : ℝ)} := not_le.mpr h
  change Set.indicator {x | T x ≤ (s : ℝ)} (1 : Ω → ℝ) ω = 0
  exact Set.indicator_of_notMem hm _

/-- Any lifetime on a two-point space is measurable. -/
private theorem measurable_two_point (T : Fin 2 → ℝ) : Measurable T :=
  measurable_of_finite T

/-- The fair two-point probability space used below. -/
private theorem hprob_two : IsProbabilityMeasure
    (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i)) := by
  have h1 : ∀ i : Fin 2, 0 ≤ (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) i := fun _ ↦ by norm_num
  have h2 : HasSum (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) 1 := by
    have hs : Summable (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) := Summable.of_finite
    have h := hs.hasSum
    simp only [tsum_fintype, Fin.sum_univ_two] at h
    norm_num at h
    exact h
  exact HasSum.isProbabilityMeasure_sum_dirac (d := fun i : Fin 2 ↦ i) h1 h2

private theorem c_0_le_0 : (0 : ℝ) ≤ 0 := le_refl _
private theorem c_0_le_1 : (0 : ℝ) ≤ 1 := zero_le_one
private theorem c_1_le_1 : (1 : ℝ) ≤ 1 := le_refl _
private theorem c_not_1_le_0 : ¬ (1 : ℝ) ≤ 0 := by norm_num

/-- Identical lifetimes, general form: two payments on a two-point space where both lives share
the same non-constant lifetime. -/
example : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
      (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
        (.sub (.const 1) (.obs false (k : ℝ≥0))))) (1 + 1)).value
      (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
      (fun _ _ ↦ (9 / 10 : ℝ))
      (fun i ↦ defaultIndicator
        (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
          else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
    = (9 / 5 : ℝ) := by
  have hT1 : Measurable (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0) :=
    measurable_two_point _
  have hT2 : Measurable (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0) :=
    measurable_two_point _
  have := hprob_two
  have hend : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) (1 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
      = (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
          (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) (1 + 1)).value
          (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
          (fun _ _ ↦ (9 / 10 : ℝ))
          (fun i ↦ defaultIndicator
            (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
              else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
        + (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
            (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) (1 + 1)).value
            (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
            (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
                else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
        - (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
            (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
              (.sub (.const 1) (.obs false (k : ℝ≥0))))) (1 + 1)).value
            (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
            (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
                else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ()) :=
    MathFin.lastSurvivor_annuity_eq_value _ _ _ hT1 hT2 _ _ _ _
  rw [hend]
  have e1 : defaultIndicator
      (bif true then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((0 : ℕ)) : ℝ≥0) : ℝ) < (10 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e2 : defaultIndicator
      (bif true then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (1 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e3 : defaultIndicator
      (bif true then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((1 : ℕ) : ℝ≥0)
      (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((1 : ℕ)) : ℝ≥0) : ℝ) < (10 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e4 : defaultIndicator
      (bif true then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((1 : ℕ) : ℝ≥0)
      (1 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((1 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e5 : defaultIndicator
      (bif false then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((0 : ℕ)) : ℝ≥0) : ℝ) < (10 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e6 : defaultIndicator
      (bif false then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (1 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e7 : defaultIndicator
      (bif false then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((1 : ℕ) : ℝ≥0)
      (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((1 : ℕ)) : ℝ≥0) : ℝ) < (10 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e8 : defaultIndicator
      (bif false then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) () ((1 : ℕ) : ℝ≥0)
      (1 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((1 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have eL : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) (1 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_succ,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e1, e2, e3, e4, e5, e6, e7, e8, sub_zero, sub_self,
      max_def, ite_eq_left c_1_le_1, ite_eq_left c_0_le_0]
    norm_num
  have eA : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) (1 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_succ,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e1, e2, e3, e4, sub_zero, sub_self]
    norm_num
  have eB : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) (1 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_succ,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e5, e6, e7, e8, sub_zero, sub_self]
    norm_num
  have eC : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) (1 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (10 : ℝ) else 0)) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_succ,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e1, e2, e3, e4, e5, e6, e7, e8, sub_zero, sub_self,
      min_def, ite_eq_left c_1_le_1, ite_eq_left c_0_le_0]
    norm_num
  rw [eA, eB, eC]
  norm_num

/-- Disjoint survival events: one life alive, the other dead, on a one-point space. The
joint-life value vanishes while the last-survivor value equals the single-life value. -/
example : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
      (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
        (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
      (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
    = (9 / 5 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 2 ↦ (10 : ℝ)) := measurable_const
  have hT2 : Measurable (fun _ : Fin 2 ↦ (0 : ℝ)) := measurable_const
  have hend : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
          (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
          (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
        + (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
            (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
        - (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
            (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
              (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ()) :=
    MathFin.lastSurvivor_annuity_eq_value _ _ _ hT1 hT2 _ _ _ _
  rw [hend]
  have e1 : defaultIndicator
      (bif true then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ()
      ((0 : ℕ) : ℝ≥0) (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((0 : ℕ)) : ℝ≥0) : ℝ) < (10 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e2 : defaultIndicator
      (bif false then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ()
      ((0 : ℕ) : ℝ≥0) (0 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have eL : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, e2, sub_zero, sub_self,
      max_def, ite_eq_right c_not_1_le_0]
    norm_num
  have eA : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, sub_zero]
    norm_num
  have eB : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e2, sub_self]
    norm_num
  have eC : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (10 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, e2, sub_zero, sub_self,
      min_def, ite_eq_right c_not_1_le_0]
    norm_num
  rw [eA, eB, eC]
  norm_num

/-- Correlated lives on a two-point space: both survive exactly at the first point, so joint
survival (probability one half) is not the product of the marginals (one quarter). -/
example : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
      (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
        (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
      (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
      (fun _ _ ↦ (9 / 10 : ℝ))
      (fun i ↦ defaultIndicator
        (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
          else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
    = (9 / 10 : ℝ) := by
  have hT1 : Measurable (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0) :=
    measurable_two_point _
  have hT2 : Measurable (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0) :=
    measurable_two_point _
  have := hprob_two
  have hend : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
      = (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
          (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
          (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
          (fun _ _ ↦ (9 / 10 : ℝ))
          (fun i ↦ defaultIndicator
            (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
              else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
        + (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
            (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
            (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
            (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
                else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
        - (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
            (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
              (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
            (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
            (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
                else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ()) :=
    MathFin.lastSurvivor_annuity_eq_value _ _ _ hT1 hT2 _ _ _ _
  rw [hend]
  have e1 : defaultIndicator
      (bif true then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((0 : ℕ)) : ℝ≥0) : ℝ) < (8 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e2 : defaultIndicator
      (bif true then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (1 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e3 : defaultIndicator
      (bif false then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((0 : ℕ)) : ℝ≥0) : ℝ) < (9 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e4 : defaultIndicator
      (bif false then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
        else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) () ((0 : ℕ) : ℝ≥0)
      (1 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have eL : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
      = (9 / 10 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_one,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e1, e2, e3, e4, sub_zero, sub_self,
      max_def, ite_eq_left c_1_le_1, ite_eq_left c_0_le_0]
    norm_num
  have eA : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
      = (9 / 10 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_one,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e1, e2, sub_zero, sub_self]
    norm_num
  have eB : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
      = (9 / 10 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_one,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e3, e4, sub_zero, sub_self]
    norm_num
  have eC : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun j : Fin 2 ↦ if j = 0 then (8 : ℝ) else 0)
            else (fun j : Fin 2 ↦ if j = 0 then (9 : ℝ) else 0)) ())
      = (9 / 10 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      integral_sum_dirac (fun i ↦ ENNReal.ofReal_ne_top),
      tsum_fintype, Fin.sum_univ_two, Finset.sum_range_one,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num), smul_eq_mul,
      e1, e2, e3, e4, sub_zero, sub_self,
      min_def, ite_eq_left c_1_le_1, ite_eq_left c_0_le_0]
    norm_num
  rw [eA, eB, eC]
  norm_num

/-- Both lives dead at the only payment date: every value vanishes. -/
example : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
      (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
        (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
      (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
    = 0 := by
  have hT1 : Measurable (fun _ : Fin 2 ↦ (0 : ℝ)) := measurable_const
  have hT2 : Measurable (fun _ : Fin 2 ↦ (0 : ℝ)) := measurable_const
  have hend : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
          (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
          (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
        + (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
            (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
        - (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
            (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
              (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ()) :=
    MathFin.lastSurvivor_annuity_eq_value _ _ _ hT1 hT2 _ _ _ _
  rw [hend]
  have e1 : defaultIndicator
      (bif true then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ()
      ((0 : ℕ) : ℝ≥0) (0 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e2 : defaultIndicator
      (bif false then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ()
      ((0 : ℕ) : ℝ≥0) (0 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have eL : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, e2, sub_self,
      max_def, ite_eq_left c_0_le_0]
    norm_num
  have eA : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, sub_self]
    norm_num
  have eB : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e2, sub_self]
    norm_num
  have eC : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (0 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, e2, sub_self,
      min_def, ite_eq_left c_0_le_0]
    norm_num
  rw [eA, eB, eC]
  norm_num

/-- Death exactly at a payment date counts as dead: the first life dies at the date while the
second survives it, so the last-survivor value equals the second single-life value. -/
example : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
      (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
        (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
      (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
    = (9 / 5 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 2 ↦ (0 : ℝ)) := measurable_const
  have hT2 : Measurable (fun _ : Fin 2 ↦ (10 : ℝ)) := measurable_const
  have hend : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
      = (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
          (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
          (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
        + (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
            (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
        - (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
            (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
              (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ()) :=
    MathFin.lastSurvivor_annuity_eq_value _ _ _ hT1 hT2 _ _ _ _
  rw [hend]
  have e1 : defaultIndicator
      (bif true then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ()
      ((0 : ℕ) : ℝ≥0) (0 : Fin 2) = 1 := by
    apply defaultIndicator_of_le
    change (0 : ℝ) ≤ ((((0 : ℕ)) : ℝ≥0) : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have e2 : defaultIndicator
      (bif false then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ()
      ((0 : ℕ) : ℝ≥0) (0 : Fin 2) = 0 := by
    apply defaultIndicator_of_gt
    change ((((0 : ℕ)) : ℝ≥0) : ℝ) < (10 : ℝ)
    rw [NNReal.coe_natCast]
    norm_num
  have eL : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, e2, sub_zero, sub_self,
      max_def, ite_eq_left c_0_le_1]
    norm_num
  have eA : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, sub_self]
    norm_num
  have eB : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e2, sub_zero]
    norm_num
  have eC : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 1).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ)) else (fun _ : Fin 2 ↦ (10 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, integral_dirac,
      Finset.sum_range_one, e1, e2, sub_zero, sub_self,
      min_def, ite_eq_left c_0_le_1]
    norm_num
  rw [eA, eB, eC]
  norm_num

/-- The empty schedule: with no payments every value vanishes. -/
example : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
      (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
        (.sub (.const 1) (.obs false (k : ℝ≥0))))) 0).value
      (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
    = 0 := by
  have hT1 : Measurable (fun _ : Fin 2 ↦ (7 : ℝ)) := measurable_const
  have hT2 : Measurable (fun _ : Fin 2 ↦ (3 : ℝ)) := measurable_const
  have hend : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 0).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
      = (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
          (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 0).value
          (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
        + (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
            (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 0).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
        - (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
            (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
              (.sub (.const 1) (.obs false (k : ℝ≥0))))) 0).value
            (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ()) :=
    MathFin.lastSurvivor_annuity_eq_value _ _ _ hT1 hT2 _ _ _ _
  rw [hend]
  have eL : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.max (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 0).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      Finset.range_zero, Finset.sum_empty, integral_dirac]
  have eA : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs true (k : ℝ≥0)))) 0).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      Finset.range_zero, Finset.sum_empty, integral_dirac]
  have eB : (payFlows (fun k : ℕ ↦ (k : ℝ≥0))
        (fun k ↦ .mul (.const (2 : ℝ)) (.sub (.const 1) (.obs false (k : ℝ≥0)))) 0).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      Finset.range_zero, Finset.sum_empty, integral_dirac]
  have eC : (payFlows (fun k : ℕ ↦ (k : ℝ≥0)) (fun k ↦ .mul (.const (2 : ℝ))
        (.min (.sub (.const 1) (.obs true (k : ℝ≥0)))
          (.sub (.const 1) (.obs false (k : ℝ≥0))))) 0).value
        (Measure.dirac (0 : Fin 2)) (fun _ _ ↦ (9 / 10 : ℝ))
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (7 : ℝ)) else (fun _ : Fin 2 ↦ (3 : ℝ))) ())
      = 0 := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt,
      Finset.range_zero, Finset.sum_empty, integral_dirac]
  rw [eA, eB, eC]
  norm_num

end MathFinTest
