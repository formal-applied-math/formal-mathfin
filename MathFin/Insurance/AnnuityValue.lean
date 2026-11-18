/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Instruments.FixedIncome
public import MathFin.Insurance.Insurance
public import MathFin.Insurance.SurvivalModel
public import MathFin.Models.Credit.DefaultTime

/-!
# The life annuity-due is a contract value

A net premium is the value of a survival-contingent contract. The life annuity-due
(`lifeAnnuityDue`), which `Insurance/Insurance.lean` writes directly as the sum
`∑_{k<n} B(0, k) S(k)` of flat-rate bond prices and survival probabilities, is the value
(`Contract.value`) of the schedule of payments that pays one at each date `k < n` while the
default indicator `1{τ ≤ k}` of the lifetime `τ` is still zero (`Contracts.payFlows`,
`Contracts.defaultIndicator`), discounted on the flat-rate curve `zcb r 0`. The lifetime enters
through its survival probabilities at the dates, which are those of the force of mortality `μ`.

This is the identification of the actuarial annuity with the credit contracts of
`Models/Credit/DefaultTime.lean`: a lifetime is a default time and the annuity is a premium leg
of a credit default swap without the accrual factors (`value_cdsPremiumLeg`).

The deflator is deterministic, the flat-rate discount of the dates, and the contract is valued
under the measure `Q` of the lifetime: the statement is about the lifetime's law, with no market.

## Main results

* `lifeAnnuityDue_eq_value`: the life annuity-due is the value, on the flat-rate discount, of the
  payments of one while the default indicator is zero.
* `lastSurvivor_annuity_eq_value`: the last-survivor annuity is the sum of the single-life
  annuity values minus the joint-life value, on the same schedule.

## References

* [D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life
  Contingent Risks*][DicksonHardyWaters2013], Chapter 5 (annuities).
* [Y. Ito, *AFP Actuarial Mathematics*][ItoAFPActuarial]

## Tags

life annuity, annuity-due, survival-contingent payments, default indicator, contract value,
MSC 91G05, JEL G22
-/

@[expose] public section

namespace MathFin

open MeasureTheory MathFin.Contracts
open scoped NNReal

/-- **The life annuity-due is a contract value.** If the lifetime `τ` has the survival
probabilities of the force of mortality `μ` at the dates `k < n`, the annuity-due is the value, on
the flat-rate discount `zcb r 0`, of the contract paying one at each date `k < n` while the
default indicator `1{τ ≤ k}` is still zero. The value is under the law of `τ`; the survival
probabilities at the other dates are not used. -/
theorem lifeAnnuityDue_eq_value {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q] {τ : Ω → ℝ} (hτ : Measurable τ) (r : ℝ) (μ : ℝ → ℝ)
    (n : ℕ) (hS : ∀ k < n, SurvivalModel.survivalFunction Q τ k = survivalFromForce μ k) :
    lifeAnnuityDue r μ n =
      (payFlows (fun k ↦ (k : ℝ≥0)) (fun k ↦ (.sub (.const 1) (.obs () k) : Payoff Unit)) n).value
        Q (fun t _ ↦ zcb r 0 t) (defaultIndicator τ) := by
  have hind (k : ℕ) : Integrable (defaultIndicator τ () (k : ℝ≥0)) Q :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_le hτ measurable_const)
  have hint (k : ℕ) : Integrable (fun ω ↦ 1 - defaultIndicator τ () (k : ℝ≥0) ω) Q :=
    (integrable_const (1 : ℝ)).sub (hind k)
  rw [Contract.value]
  simp only [pathPV_payFlows, Payoff.eval, scenarioAt, lifeAnnuityDue]
  rw [integral_finsetSum _ fun k _ ↦ (hint k).const_mul _]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have h1 : ∫ ω, defaultIndicator τ () (k : ℝ≥0) ω ∂Q = Q.real {ω | τ ω ≤ ((k : ℝ≥0) : ℝ)} :=
    integral_indicator_one (measurableSet_le hτ measurable_const)
  rw [← hS k (Finset.mem_range.1 hk), integral_const_mul,
    integral_sub (integrable_const 1) (hind k), integral_const, probReal_univ, one_smul, h1,
    NNReal.coe_natCast]
  congr 1
  have halive : SurvivalModel.alive τ (k : ℝ) = {ω | τ ω ≤ (k : ℝ)}ᶜ := by
    ext ω
    simp [SurvivalModel.alive]
  rw [SurvivalModel.survivalFunction, halive, ← measureReal_def,
    probReal_compl_eq_one_sub (measurableSet_le hτ measurable_const)]

/-- **Last-survivor annuity identity.** The value of the annuity paying while either of two lives
survives is the sum of the two single-life values minus the joint-life value, for the same
payment schedule, discount and lifetimes. The identity is pointwise min/max algebra on the
survival payoffs, with no independence hypothesis. -/
theorem lastSurvivor_annuity_eq_value {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (T1 T2 : Ω → ℝ)
    (hT1 : Measurable T1) (hT2 : Measurable T2) (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0)
    (b : ℕ → ℝ) (n : ℕ) :
    (payFlows t (fun k ↦ .mul (.const (b k))
      (.max (.sub (.const 1) (.obs true (t k))) (.sub (.const 1) (.obs false (t k))))) n).value
        Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
      = (payFlows t (fun k ↦ .mul (.const (b k))
          (.sub (.const 1) (.obs true (t k)))) n).value
          Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
        + (payFlows t (fun k ↦ .mul (.const (b k))
            (.sub (.const 1) (.obs false (t k)))) n).value
            Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
        - (payFlows t (fun k ↦ .mul (.const (b k))
            (.min (.sub (.const 1) (.obs true (t k)))
              (.sub (.const 1) (.obs false (t k))))) n).value
            Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ()) := by
  have hind1 (k : ℕ) :
      Integrable (defaultIndicator (bif true then T1 else T2) () (t k)) Q :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_le hT1 measurable_const)
  have hind2 (k : ℕ) :
      Integrable (defaultIndicator (bif false then T1 else T2) () (t k)) Q :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_le hT2 measurable_const)
  have hs1 (k : ℕ) :
      Integrable (fun ω ↦ 1 - defaultIndicator (bif true then T1 else T2) () (t k) ω) Q :=
    (integrable_const (1 : ℝ)).sub (hind1 k)
  have hs2 (k : ℕ) :
      Integrable (fun ω ↦ 1 - defaultIndicator (bif false then T1 else T2) () (t k) ω) Q :=
    (integrable_const (1 : ℝ)).sub (hind2 k)
  have hmin (k : ℕ) :
      Integrable (fun ω ↦ min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
        (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) Q :=
    (hs1 k).inf (hs2 k)
  have hmax (k : ℕ) :
      Integrable (fun ω ↦ max (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
        (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) Q :=
    (hs1 k).sup (hs2 k)
  have hval (k : ℕ) :
      (∫ ω, D (t k) * (b k * max (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
        (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q)
      = (∫ ω, D (t k) * (b k * (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)) ∂Q)
        + (∫ ω, D (t k) * (b k * (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q)
        - (∫ ω, D (t k) *
          (b k * min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
            (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q) := by
    have h1 : Integrable (fun ω ↦ D (t k) *
        (b k * (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω))) Q :=
      ((hs1 k).const_mul (b k)).const_mul (D (t k))
    have h2 : Integrable (fun ω ↦ D (t k) *
        (b k * (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω))) Q :=
      ((hs2 k).const_mul (b k)).const_mul (D (t k))
    have h3 : Integrable (fun ω ↦ D (t k) *
        (b k * min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
          (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω))) Q :=
      ((hmin k).const_mul (b k)).const_mul (D (t k))
    have hsum : (∫ ω, D (t k) *
          (b k * (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)) ∂Q)
          + (∫ ω, D (t k) *
            (b k * (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q)
          - (∫ ω, D (t k) *
            (b k * min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
              (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q)
        = ∫ ω, (D (t k) * (b k * (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω))
          + D (t k) * (b k * (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω))
          - D (t k) *
            (b k * min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
              (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω))) ∂Q := by
      rw [← integral_add h1 h2]
      exact (integral_sub (h1.add h2) h3).symm
    rw [hsum]
    apply integral_congr_ae
    filter_upwards with ω
    linear_combination D (t k) * b k *
      max_add_min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
        (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)
  have eL : (payFlows t (fun k ↦ .mul (.const (b k))
      (.max (.sub (.const 1) (.obs true (t k))) (.sub (.const 1) (.obs false (t k))))) n).value
        Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
      = ∑ k ∈ Finset.range n, ∫ ω, D (t k) *
        (b k * max (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
          (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt]
    rw [integral_finsetSum _ (fun k _ ↦ ((hmax k).const_mul (b k)).const_mul (D (t k)))]
  have eA : (payFlows t (fun k ↦ .mul (.const (b k))
        (.sub (.const 1) (.obs true (t k)))) n).value
        Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
      = ∑ k ∈ Finset.range n, ∫ ω, D (t k) *
        (b k * (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)) ∂Q := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt]
    rw [integral_finsetSum _ (fun k _ ↦ ((hs1 k).const_mul (b k)).const_mul (D (t k)))]
  have eB : (payFlows t (fun k ↦ .mul (.const (b k))
        (.sub (.const 1) (.obs false (t k)))) n).value
        Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
      = ∑ k ∈ Finset.range n, ∫ ω, D (t k) *
        (b k * (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt]
    rw [integral_finsetSum _ (fun k _ ↦ ((hs2 k).const_mul (b k)).const_mul (D (t k)))]
  have eC : (payFlows t (fun k ↦ .mul (.const (b k))
        (.min (.sub (.const 1) (.obs true (t k)))
          (.sub (.const 1) (.obs false (t k))))) n).value
        Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
      = ∑ k ∈ Finset.range n, ∫ ω, D (t k) *
        (b k * min (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
          (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)) ∂Q := by
    rw [Contract.value]
    simp only [pathPV_payFlows, Payoff.eval, scenarioAt]
    rw [integral_finsetSum _ (fun k _ ↦ ((hmin k).const_mul (b k)).const_mul (D (t k)))]
  rw [eL, eA, eB, eC, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ hval k

end MathFin
