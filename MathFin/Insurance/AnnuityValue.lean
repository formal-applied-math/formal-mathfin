/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Adam Kiezun
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

The other life contracts are contracts of the same language. The `n`-year term insurance
(`termInsurance`, one paid at the end of the year of death) is the protection leg of a credit
default swap on the unit grid at recovery `0` (`cdsProtectionLeg`); the pure endowment
(`pureEndowment`) is one payment of the survival payoff at `n`. Their values on a flat-rate
discount are the discounted death probabilities and `e^{-rn} S(n)`
(`value_termInsurance`, `value_pureEndowment`), and the three are tied by
`A = 1 − d ä`: `termInsurance_add_pureEndowment_eq` for the term contracts and
`wholeLife_epv_eq` for the whole-life sums, the lifetime being any positive random variable under
`Q` and the rate `r > 0`.

This is the identification of the actuarial annuity with the credit contracts of
`Models/Credit/DefaultTime.lean`: a lifetime is a default time and the annuity is a premium leg
of a credit default swap without the accrual factors (`value_cdsPremiumLeg`).

The deflator is deterministic, the flat-rate discount of the dates, and the contract is valued
under the measure `Q` of the lifetime: the statement is about the lifetime's law, with no market.

## Main definitions

* `lifeAnnuityFlows`: the contract paying one at each date `k < n` while the lifetime has not
  ended.
* `termInsurance`: pay one at the end of the year of death, if the lifetime ends within `n` years;
  `cdsProtectionLeg` on the unit grid at recovery `0`.
* `pureEndowment`: pay one at time `n` if the insured is alive.

## Main results

* `integral_one_sub_defaultIndicator`: the survival payoff `1 − 1{τ ≤ u}` has expectation the
  survival function `S_τ(u)`.
* `value_lifeAnnuityFlows`, `value_termInsurance`, `value_pureEndowment`: the values of the three
  contracts on a deterministic discount, in terms of the survival function at integer dates.
* `lifeAnnuityDue_eq_value`: the life annuity-due is the value, on the flat-rate discount, of the
  payments of one while the default indicator is zero.
* `termInsurance_add_pureEndowment_eq`: the value of the `n`-year term insurance plus the
  `n`-year pure endowment is one minus `(1 − e^{-r})` times the value of the life annuity-due.
* `wholeLife_epv_eq`: `A = 1 − d ä` for a whole-life insurance, `d = 1 − e^{-r}`, `r > 0`, on a
  lifetime that is positive almost surely.
* `lastSurvivor_annuity_eq_value`: the last-survivor annuity is the sum of the single-life
  annuity values minus the joint-life value, on the same schedule.
* `reversionary_annuity_eq_value`: the reversionary annuity to the second life after the
  first dies is the second life's annuity value minus the joint-life value.

## References

* [D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life
  Contingent Risks*][DicksonHardyWaters2013], Chapter 4 (insurance benefits), Chapter 5
  (annuities).
* [Y. Ito, *AFP Actuarial Mathematics*][ItoAFPActuarial]

## Tags

life annuity, annuity-due, term insurance, whole life insurance, pure endowment,
survival-contingent payments, default indicator, contract value,
MSC 91G05, JEL G22
-/

@[expose] public section

namespace MathFin

open MeasureTheory MathFin.Contracts
open scoped NNReal

/-- The **survival payoff** `1 - 1{τ ≤ u}` has expectation the survival probability
`S_τ(u) = Q(τ > u)`. -/
theorem integral_one_sub_defaultIndicator {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q] {τ : Ω → ℝ} (hτ : Measurable τ) (u : ℝ≥0) :
    ∫ ω, (1 - defaultIndicator τ () u ω) ∂Q = SurvivalModel.survivalFunction Q τ u := by
  have h : ∫ ω, defaultIndicator τ () u ω ∂Q = Q.real {ω | τ ω ≤ (u : ℝ)} :=
    integral_indicator_one (measurableSet_le hτ measurable_const)
  rw [integral_sub (integrable_const 1) (integrable_defaultIndicator hτ u), integral_const,
    probReal_univ, one_smul, h, SurvivalModel.real_le_eq_one_sub_survivalFunction hτ]
  ring

/-- The **life annuity-due contract**: pay one at each date `k < n` while the default indicator
`1{τ ≤ k}` of the lifetime is still zero, that is, while the insured is alive. -/
noncomputable def lifeAnnuityFlows (n : ℕ) : Contract Unit :=
  payFlows (fun k ↦ (k : ℝ≥0)) (fun k ↦ .sub (.const 1) (.obs () (k : ℝ≥0))) n

/-- The **term insurance** contract on `n` years: pay one at the end of the year of death, if the
lifetime ends within `n` years. It is the protection leg of a credit default swap on the unit grid
at recovery `0` (`cdsProtectionLeg`). -/
noncomputable def termInsurance (n : ℕ) : Contract Unit :=
  cdsProtectionLeg (fun k ↦ (k : ℝ≥0)) 0 n

/-- The **pure endowment** contract on `n` years: pay one at time `n` if the insured is alive. -/
noncomputable def pureEndowment (n : ℕ) : Contract Unit :=
  .pay (n : ℝ≥0) (.sub (.const 1) (.obs () (n : ℝ≥0)))

section Values

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q]
  {τ : Ω → ℝ}

/-- **The value of the life annuity-due contract** on a deterministic discount `D` is
`∑_{k<n} D(k) S_τ(k)`. -/
theorem value_lifeAnnuityFlows (hτ : Measurable τ) (D : ℝ≥0 → ℝ) (n : ℕ) :
    (lifeAnnuityFlows n).value Q (fun s _ ↦ D s) (defaultIndicator τ)
      = ∑ k ∈ Finset.range n, D k * SurvivalModel.survivalFunction Q τ k := by
  rw [lifeAnnuityFlows, Contract.value_payFlows _ _ _ _ _ _ fun k _ ↦
    ((integrable_const (1 : ℝ)).sub (integrable_defaultIndicator hτ (k : ℝ≥0))).const_mul (D k)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Contract.value_pay]
  simp only [Payoff.eval, scenarioAt]
  rw [integral_const_mul, integral_one_sub_defaultIndicator Q hτ, NNReal.coe_natCast]

/-- **The value of the term insurance** on a deterministic discount `D` is the discounted
probability of death in each year, `∑_{k<n} D(k + 1) (S_τ(k) − S_τ(k + 1))`. -/
theorem value_termInsurance (hτ : Measurable τ) (D : ℝ≥0 → ℝ) (n : ℕ) :
    (termInsurance n).value Q (fun s _ ↦ D s) (defaultIndicator τ)
      = ∑ k ∈ Finset.range n, D ((k + 1 : ℕ) : ℝ≥0) *
          (SurvivalModel.survivalFunction Q τ k
            - SurvivalModel.survivalFunction Q τ (k + 1 : ℕ)) := by
  rw [termInsurance, value_cdsProtectionLeg hτ
    (S := SurvivalModel.survivalFunction Q τ) fun u ↦
      SurvivalModel.real_le_eq_one_sub_survivalFunction hτ u,
    cdsLossesGrid, sub_zero, one_mul]
  simp only [NNReal.coe_natCast]

/-- **The value of the pure endowment** on a deterministic discount `D` is `D(n) S_τ(n)`. -/
theorem value_pureEndowment (hτ : Measurable τ) (D : ℝ≥0 → ℝ) (n : ℕ) :
    (pureEndowment n).value Q (fun s _ ↦ D s) (defaultIndicator τ)
      = D n * SurvivalModel.survivalFunction Q τ n := by
  rw [pureEndowment, Contract.value_pay]
  simp only [Payoff.eval, scenarioAt]
  rw [integral_const_mul, integral_one_sub_defaultIndicator Q hτ, NNReal.coe_natCast]

/-- **The life annuity-due is a contract value.** If the lifetime `τ` has the survival
probabilities of the force of mortality `μ` at the dates `k < n`, the annuity-due is the value, on
the flat-rate discount `zcb r 0`, of the contract paying one at each date `k < n` while the
default indicator `1{τ ≤ k}` is still zero. The value is under the law of `τ`; the survival
probabilities at the other dates are not used. -/
theorem lifeAnnuityDue_eq_value (hτ : Measurable τ) (r : ℝ) (μ : ℝ → ℝ) (n : ℕ)
    (hS : ∀ k < n, SurvivalModel.survivalFunction Q τ k = survivalFromForce μ k) :
    lifeAnnuityDue r μ n =
      (payFlows (fun k ↦ (k : ℝ≥0)) (fun k ↦ (.sub (.const 1) (.obs () k) : Payoff Unit)) n).value
        Q (fun t _ ↦ zcb r 0 t) (defaultIndicator τ) :=
  Eq.trans (Finset.sum_congr rfl fun k hk ↦ by
    rw [NNReal.coe_natCast, hS k (Finset.mem_range.1 hk)])
    (value_lifeAnnuityFlows Q hτ (fun s ↦ zcb r 0 s) n).symm

/-- **Term insurance plus pure endowment on a lifetime**: on the flat-rate discount `zcb r 0`, the
value of the `n`-year term insurance plus the `n`-year pure endowment is
`1 - (1 - e^{-r}) ä`, with `ä` the value of the life annuity-due contract: the term form of
`A = 1 - d ä`. A lifetime that is positive almost surely is all it needs. -/
theorem termInsurance_add_pureEndowment_eq (hτ : Measurable τ) (hpos : ∀ᵐ ω ∂Q, 0 < τ ω)
    (r : ℝ) (n : ℕ) :
    (termInsurance n).value Q (fun s _ ↦ zcb r 0 s) (defaultIndicator τ)
      + (pureEndowment n).value Q (fun s _ ↦ zcb r 0 s) (defaultIndicator τ)
      = 1 - (1 - Real.exp (-r)) *
          (lifeAnnuityFlows n).value Q (fun s _ ↦ zcb r 0 s) (defaultIndicator τ) := by
  have hz (k : ℕ) : zcb r 0 ((k : ℝ≥0) : ℝ) = Real.exp (-r) ^ k := by
    rw [NNReal.coe_natCast, zcb_zero_natCast]
  rw [value_termInsurance Q hτ, value_pureEndowment Q hτ, value_lifeAnnuityFlows Q hτ]
  simp only [hz]
  exact term_add_endowment_eq_annuityDue (fun k ↦ SurvivalModel.survivalFunction Q τ k)
    (by simpa using SurvivalModel.survivalFunction_zero hpos) _ n

/-- **Whole-life insurance plus the life annuity-due, `A = 1 - d ä`.** For a lifetime `τ` that is
positive almost surely and a flat rate `r > 0`, the expected present value of one paid at the end
of the year of death, `A = ∑_{k ≥ 0} e^{-r(k+1)} (S_τ(k) − S_τ(k + 1))`, equals
`1 - (1 - e^{-r}) ä` with `ä = ∑_{k ≥ 0} e^{-rk} S_τ(k)` the life annuity-due. No summability is
assumed: both series are dominated by the geometric series of the discount factor `e^{-r} < 1`. -/
theorem wholeLife_epv_eq (hpos : ∀ᵐ ω ∂Q, 0 < τ ω) {r : ℝ} (hr : 0 < r) :
    ∑' k : ℕ, zcb r 0 (k + 1 : ℕ) *
        (SurvivalModel.survivalFunction Q τ k - SurvivalModel.survivalFunction Q τ (k + 1 : ℕ))
      = 1 - (1 - Real.exp (-r)) * ∑' k : ℕ, zcb r 0 k * SurvivalModel.survivalFunction Q τ k := by
  simp only [zcb_zero_natCast]
  exact wholeLife_add_endowment_eq_annuityDue (fun k ↦ SurvivalModel.survivalFunction Q τ k)
    (by simpa using SurvivalModel.survivalFunction_zero hpos)
    (SurvivalModel.survivalFunction_antitone.comp_monotone Nat.mono_cast)
    (fun k ↦ SurvivalModel.survivalFunction_nonneg k) (Real.exp_pos _)
    ((Real.exp_lt_exp.2 (neg_neg_of_pos hr)).trans_eq Real.exp_zero)

end Values

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
  have hs (i : Bool) (u : ℝ≥0) : Integrable (fun ω ↦
      1 - defaultIndicator (bif i then T1 else T2) () u ω) Q :=
    (integrable_const (1 : ℝ)).sub
      (integrable_defaultIndicator (by cases i <;> assumption) u)
  refine Contract.value_payFlows_add_sub Q _ _ t _ _ _ _ n
    (fun k _ ω ↦ ?_) (fun k _ ↦ ?_) (fun k _ ↦ ?_) (fun k _ ↦ ?_)
  · simp only [Payoff.eval, scenarioAt]
    linear_combination b k * max_add_min
      (1 - defaultIndicator (bif true then T1 else T2) () (t k) ω)
      (1 - defaultIndicator (bif false then T1 else T2) () (t k) ω)
  · exact ((hs true (t k)).const_mul (b k)).const_mul (D (t k))
  · exact ((hs false (t k)).const_mul (b k)).const_mul (D (t k))
  · exact (((hs true (t k)).inf (hs false (t k))).const_mul (b k)).const_mul (D (t k))

/-- **Reversionary annuity identity.** The value of the annuity paying life2's benefit only
after life1 has died is the life2 single-life value minus the joint-life value, for the same
payment schedule, discount and lifetimes. The payoff is life1's death indicator times life2's
survival payoff, pointwise the difference of life2's survival payoff and the joint survival
payoff on the 0/1-valued default indicators, with no independence hypothesis. -/
theorem reversionary_annuity_eq_value {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (T1 T2 : Ω → ℝ)
    (hT1 : Measurable T1) (hT2 : Measurable T2) (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0)
    (b : ℕ → ℝ) (n : ℕ) :
    (payFlows t (fun k ↦ .mul (.const (b k))
      (.mul (.obs true (t k)) (.sub (.const 1) (.obs false (t k))))) n).value
        Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
      = (payFlows t (fun k ↦ .mul (.const (b k))
          (.sub (.const 1) (.obs false (t k)))) n).value
          Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ())
        - (payFlows t (fun k ↦ .mul (.const (b k))
            (.min (.sub (.const 1) (.obs true (t k)))
              (.sub (.const 1) (.obs false (t k))))) n).value
            Q (fun s _ ↦ D s) (fun i ↦ defaultIndicator (bif i then T1 else T2) ()) := by
  have hs (i : Bool) (u : ℝ≥0) : Integrable (fun ω ↦
      1 - defaultIndicator (bif i then T1 else T2) () u ω) Q :=
    (integrable_const (1 : ℝ)).sub
      (integrable_defaultIndicator (by cases i <;> assumption) u)
  refine Contract.value_payFlows_sub Q _ _ t _ _ _ n (fun k _ ω ↦ ?_) (fun k _ ↦ ?_) (fun k _ ↦ ?_)
  · simp only [Payoff.eval, scenarioAt, Bool.cond_true, Bool.cond_false]
    rcases defaultIndicator_eq_zero_or_one T1 (t k) ω with h1 | h1 <;>
      rcases defaultIndicator_eq_zero_or_one T2 (t k) ω with h2 | h2 <;>
      simp [h1, h2]
  · exact ((hs false (t k)).const_mul (b k)).const_mul (D (t k))
  · exact (((hs true (t k)).inf (hs false (t k))).const_mul (b k)).const_mul (D (t k))

end MathFin
