/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Reversionary annuity identity checks

Concrete checks of `MathFin.reversionary_annuity_eq_value` on small finite probability spaces
with explicit lifetimes. Each example applies the endpoint and computes every contract value to
an explicit rational number.

* Equal lifetimes pay nothing (the reversion never triggers).
* Life1 dead before the date while life2 survives pays a nonzero benefit.
* Death of life1 exactly at a payment date counts as dead (pays).
* Death of life2 at the payment date pays nothing.
* The empty schedule (`n = 0`).
* A fair two-point space where the reversion pays on exactly one point.
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

/-- Life1 dead before the date while life2 survives: the reversion pays a nonzero benefit. -/
example : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 1 ↦ (0 : ℝ)) := measurable_of_finite _
  have hT2 : Measurable (fun _ : Fin 1 ↦ (5 : ℝ)) := measurable_of_finite _
  have hep := MathFin.reversionary_annuity_eq_value (Measure.dirac (0 : Fin 1))
    (fun _ : Fin 1 ↦ (0 : ℝ)) (fun _ : Fin 1 ↦ (5 : ℝ)) hT1 hT2
    (fun _ ↦ (9 / 10 : ℝ)) (fun _ ↦ (1 : ℝ≥0)) (fun _ ↦ (2 : ℝ)) (0 + 1)
  have hS : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 0 :=
      defaultIndicator_of_gt (by change ((1 : ℝ≥0) : ℝ) < (5 : ℝ); norm_num)
    rw [e]
    norm_num
  have hJ : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e1 : defaultIndicator
        (bif true then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    have e2 : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 0 :=
      defaultIndicator_of_gt (by change ((1 : ℝ≥0) : ℝ) < (5 : ℝ); norm_num)
    rw [e1, e2]
    norm_num [min_def]
  have hR : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    calc (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
          (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
        = (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
          - (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
              (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
                (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()) := hep
      _ = (9 / 5 : ℝ) - (0 : ℝ) := by rw [hS, hJ]
      _ = (9 / 5 : ℝ) := by norm_num
  exact ⟨hR, hS, hJ⟩

/-- Equal lifetimes pay nothing: the reversion never triggers. -/
example : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
      = (0 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
      = (0 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
      = (0 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 1 ↦ (0 : ℝ)) := measurable_of_finite _
  have hT2 : Measurable (fun _ : Fin 1 ↦ (0 : ℝ)) := measurable_of_finite _
  have hep := MathFin.reversionary_annuity_eq_value (Measure.dirac (0 : Fin 1))
    (fun _ : Fin 1 ↦ (0 : ℝ)) (fun _ : Fin 1 ↦ (0 : ℝ)) hT1 hT2
    (fun _ ↦ (9 / 10 : ℝ)) (fun _ ↦ (1 : ℝ≥0)) (fun _ ↦ (2 : ℝ)) (0 + 1)
  have hS : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    rw [e]
    norm_num
  have hJ : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e1 : defaultIndicator
        (bif true then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    have e2 : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    rw [e1, e2]
    norm_num [min_def]
  have hR : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
      = (0 : ℝ) := by
    calc (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
          (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
        = (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ())
          - (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
              (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
                (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (0 : ℝ))) ()) := hep
      _ = (0 : ℝ) - (0 : ℝ) := by rw [hS, hJ]
      _ = (0 : ℝ) := by norm_num
  exact ⟨hR, hS, hJ⟩

/-- Death of life1 exactly at the payment date counts as dead: the reversion pays. -/
example : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 1 ↦ (1 : ℝ)) := measurable_of_finite _
  have hT2 : Measurable (fun _ : Fin 1 ↦ (5 : ℝ)) := measurable_of_finite _
  have hep := MathFin.reversionary_annuity_eq_value (Measure.dirac (0 : Fin 1))
    (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ : Fin 1 ↦ (5 : ℝ)) hT1 hT2
    (fun _ ↦ (9 / 10 : ℝ)) (fun _ ↦ (1 : ℝ≥0)) (fun _ ↦ (2 : ℝ)) (0 + 1)
  have hS : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 0 :=
      defaultIndicator_of_gt (by change ((1 : ℝ≥0) : ℝ) < (5 : ℝ); norm_num)
    rw [e]
    norm_num
  have hJ : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e1 : defaultIndicator
        (bif true then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (1 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    have e2 : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 0 :=
      defaultIndicator_of_gt (by change ((1 : ℝ≥0) : ℝ) < (5 : ℝ); norm_num)
    rw [e1, e2]
    norm_num [min_def]
  have hR : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (9 / 5 : ℝ) := by
    calc (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
          (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
        = (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
          - (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
              (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
                (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (1 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()) := hep
      _ = (9 / 5 : ℝ) - (0 : ℝ) := by rw [hS, hJ]
      _ = (9 / 5 : ℝ) := by norm_num
  exact ⟨hR, hS, hJ⟩

/-- Death of life2 at the payment date pays nothing. -/
example : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
      = (0 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
      = (0 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
      = (0 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 1 ↦ (0 : ℝ)) := measurable_of_finite _
  have hT2 : Measurable (fun _ : Fin 1 ↦ (1 : ℝ)) := measurable_of_finite _
  have hep := MathFin.reversionary_annuity_eq_value (Measure.dirac (0 : Fin 1))
    (fun _ : Fin 1 ↦ (0 : ℝ)) (fun _ : Fin 1 ↦ (1 : ℝ)) hT1 hT2
    (fun _ ↦ (9 / 10 : ℝ)) (fun _ ↦ (1 : ℝ≥0)) (fun _ ↦ (2 : ℝ)) (0 + 1)
  have hS : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (1 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    rw [e]
    norm_num
  have hJ : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_dirac]
    have e1 : defaultIndicator
        (bif true then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    have e2 : defaultIndicator
        (bif false then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ()
        (1 : ℝ≥0) (0 : Fin 1) = 1 :=
      defaultIndicator_of_le (by change (1 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    rw [e1, e2]
    norm_num [min_def]
  have hR : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
      = (0 : ℝ) := by
    calc (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
          (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
        = (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ())
          - (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
              (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
                (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (1 : ℝ))) ()) := hep
      _ = (0 : ℝ) - (0 : ℝ) := by rw [hS, hJ]
      _ = (0 : ℝ) := by norm_num
  exact ⟨hR, hS, hJ⟩

/-- The empty schedule pays nothing. -/
example : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) 0).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) 0).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) 0).value
        (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
  have hT1 : Measurable (fun _ : Fin 1 ↦ (0 : ℝ)) := measurable_of_finite _
  have hT2 : Measurable (fun _ : Fin 1 ↦ (5 : ℝ)) := measurable_of_finite _
  have hep := MathFin.reversionary_annuity_eq_value (Measure.dirac (0 : Fin 1))
    (fun _ : Fin 1 ↦ (0 : ℝ)) (fun _ : Fin 1 ↦ (5 : ℝ)) hT1 hT2
    (fun _ ↦ (9 / 10 : ℝ)) (fun _ ↦ (1 : ℝ≥0)) (fun _ ↦ (2 : ℝ)) 0
  have hS : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) 0).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_zero]
    simp
  have hJ : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) 0).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_zero]
    simp
  have hR : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) 0).value
      (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
      = (0 : ℝ) := by
    calc (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) 0).value
          (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
        = (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) 0).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ())
          - (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
              (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
                (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) 0).value
            (Measure.dirac (0 : Fin 1)) (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 1 ↦ (0 : ℝ)) else (fun _ ↦ (5 : ℝ))) ()) := hep
      _ = (0 : ℝ) - (0 : ℝ) := by rw [hS, hJ]
      _ = (0 : ℝ) := by norm_num
  exact ⟨hR, hS, hJ⟩

/-- Fair two-point space: the reversion pays on exactly one point, averaged. -/
example : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
            else (fun i ↦ ((i.val : ℝ) + 1))) ())
      = (9 / 10 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
            else (fun i ↦ ((i.val : ℝ) + 1))) ())
      = (9 / 10 : ℝ)
    ∧ (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
        (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
        (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
        (fun i ↦ defaultIndicator
          (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
            else (fun i ↦ ((i.val : ℝ) + 1))) ())
      = (0 : ℝ) := by
  have := hprob_two
  have hT1 : Measurable (fun _ : Fin 2 ↦ (0 : ℝ)) := measurable_of_finite _
  have hT2 : Measurable (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) := measurable_of_finite _
  have hT20 : (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) 0 = (1 : ℝ) := by
    simp only [Fin.val_zero]; norm_num
  have hT21 : (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) 1 = (2 : ℝ) := by
    simp only [Fin.val_one]; norm_num
  have hto : (ENNReal.ofReal (1 / 2)).toReal = (1 / 2 : ℝ) :=
    ENNReal.toReal_ofReal (by norm_num)
  have hep := MathFin.reversionary_annuity_eq_value
    (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
    (fun _ : Fin 2 ↦ (0 : ℝ)) (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) hT1 hT2
    (fun _ ↦ (9 / 10 : ℝ)) (fun _ ↦ (1 : ℝ≥0)) (fun _ ↦ (2 : ℝ)) (0 + 1)
  have hS : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
      (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
      (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ())
      = (9 / 10 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_sum_dirac (fun _ ↦ ENNReal.ofReal_ne_top)]
    simp only [tsum_fintype, Fin.sum_univ_two, hto, smul_eq_mul]
    have e0 : defaultIndicator
        (bif false then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ()
        (1 : ℝ≥0) (0 : Fin 2) = 1 :=
      defaultIndicator_of_le (by
        change (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) 0 ≤ ((1 : ℝ≥0) : ℝ)
        rw [hT20]; norm_num)
    have e1 : defaultIndicator
        (bif false then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ()
        (1 : ℝ≥0) (1 : Fin 2) = 0 :=
      defaultIndicator_of_gt (by
        change ((1 : ℝ≥0) : ℝ) < (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) 1
        rw [hT21]; norm_num)
    rw [e0, e1]
    norm_num
  have hJ : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
      (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ())
      = (0 : ℝ) := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [integral_sum_dirac (fun _ ↦ ENNReal.ofReal_ne_top)]
    simp only [tsum_fintype, Fin.sum_univ_two, hto, smul_eq_mul]
    have e1a : defaultIndicator
        (bif true then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ()
        (1 : ℝ≥0) (0 : Fin 2) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    have e1b : defaultIndicator
        (bif true then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ()
        (1 : ℝ≥0) (1 : Fin 2) = 1 :=
      defaultIndicator_of_le (by change (0 : ℝ) ≤ ((1 : ℝ≥0) : ℝ); norm_num)
    have e2a : defaultIndicator
        (bif false then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ()
        (1 : ℝ≥0) (0 : Fin 2) = 1 :=
      defaultIndicator_of_le (by
        change (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) 0 ≤ ((1 : ℝ≥0) : ℝ)
        rw [hT20]; norm_num)
    have e2b : defaultIndicator
        (bif false then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ()
        (1 : ℝ≥0) (1 : Fin 2) = 0 :=
      defaultIndicator_of_gt (by
        change ((1 : ℝ≥0) : ℝ) < (fun i : Fin 2 ↦ ((i.val : ℝ) + 1)) 1
        rw [hT21]; norm_num)
    rw [e1a, e1b, e2a, e2b]
    norm_num [min_def]
  have hR : (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
        (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
          (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
      (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
      (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
      (fun i ↦ defaultIndicator
        (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
          else (fun i ↦ ((i.val : ℝ) + 1))) ())
      = (9 / 10 : ℝ) := by
    calc (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
          (.mul (.obs true ((fun _ ↦ (1 : ℝ≥0)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k))))) (0 + 1)).value
          (Measure.sum (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
          (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
          (fun i ↦ defaultIndicator
            (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
              else (fun i ↦ ((i.val : ℝ) + 1))) ())
        = (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
            (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))) (0 + 1)).value
            (Measure.sum
              (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
            (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
                else (fun i ↦ ((i.val : ℝ) + 1))) ())
          - (payFlows (fun _ ↦ (1 : ℝ≥0)) (fun k ↦ .mul (.const ((fun _ ↦ (2 : ℝ)) k))
              (.min (.sub (.const 1) (.obs true ((fun _ ↦ (1 : ℝ≥0)) k)))
                (.sub (.const 1) (.obs false ((fun _ ↦ (1 : ℝ≥0)) k)))))
              (0 + 1)).value
            (Measure.sum
              (fun i : Fin 2 ↦ ENNReal.ofReal (1 / 2) • Measure.dirac i))
            (fun s _ ↦ (fun _ ↦ (9 / 10 : ℝ)) s)
            (fun i ↦ defaultIndicator
              (bif i then (fun _ : Fin 2 ↦ (0 : ℝ))
                else (fun i ↦ ((i.val : ℝ) + 1))) ()) := hep
      _ = (9 / 10 : ℝ) - (0 : ℝ) := by rw [hS, hJ]
      _ = (9 / 10 : ℝ) := by norm_num
  exact ⟨hR, hS, hJ⟩

end MathFinTest
