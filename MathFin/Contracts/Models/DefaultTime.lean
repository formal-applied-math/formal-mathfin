/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Instruments.Credit
public import MathFin.Contracts.Pricing
public import MathFin.FixedIncome.Cox

/-!
# The credit default swap priced against a default time

`Contracts/Instruments/Credit.lean` writes the CDS on a payment grid as a contract that observes
the default indicator `N u = 1{τ ≤ u}`. Here a default time `τ : Ω → ℝ` is the model:
`defaultIndicator τ` reads `N` off it, so each leg is a finite sum of discounted values
`𝔼[N u] = Q(τ ≤ u)`. Given the survival function `S` (`Q(τ ≤ u) = 1 − S u`) the legs are worth

* the premium leg, `s` times the **grid annuity** `∑ D(tᵢ₊₁) (tᵢ₊₁ − tᵢ) S(tᵢ₊₁)`
  (`cdsAnnuityGrid`, `value_cdsPremiumLeg`);
* the protection leg, `1 − R` times the **grid losses** `∑ D(tᵢ₊₁) (S tᵢ − S tᵢ₊₁)`
  (`cdsLossesGrid`, `value_cdsProtectionLeg`);

and the protection buyer's CDS is worth their difference (`value_cdsBuyer`), zero exactly at the
**grid par spread** `(1 − R) · losses / annuity` (`value_cdsBuyer_eq_zero_iff`). These are the
discrete analogues of `Cox.cdsAnnuity`, `Cox.cdsLosses` and `Cox.cdsFairSpreadTV`.

The Cox default time of `FixedIncome/Cox.lean`, built by inverting a unit-exponential clock
through the cumulative hazard, has `S = hazardSurvival h` (`cox_cdf_timeVarying`), so under it the
CDS contract is worth the grid legs of the hazard curve (`value_cdsBuyer_coxDefaultTime`). Against
the continuous legs: with no discounting the grid losses on any grid from `0` to `T` telescope to
the default probability `1 − S(T)`, which is `Cox.cdsLosses 0 h T`
(`cdsLossesGrid_one_eq_cdsLosses`). With
discounting the grid legs approximate the continuous ones; that is not proved.

## Main definitions

* `defaultIndicator` — the process `N u = 1{τ ≤ u}` as a model.
* `cdsAnnuityGrid`, `cdsLossesGrid`, `cdsParSpreadGrid`.

## Main results

* `value_cdsPremiumLeg`, `value_cdsProtectionLeg`, `value_cdsBuyer`, `value_cdsBuyer_eq_zero_iff`.
* `value_cdsBuyer_coxDefaultTime`, `cdsLossesGrid_one_eq_cdsLosses`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The default indicator process of a default time `τ`, `N u = 1{τ ≤ u}`, as the model of the
single underlying `()`. -/
noncomputable def defaultIndicator (τ : Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ u ↦ {ω | τ ω ≤ u}.indicator 1

/-- The **grid annuity** (premium-leg kernel) of the survival function `S` on the grid `t`:
`∑ D(tᵢ₊₁) (tᵢ₊₁ − tᵢ) S(tᵢ₊₁)`. -/
noncomputable def cdsAnnuityGrid (D : ℝ≥0 → ℝ) (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, D (t (i + 1)) * (((t (i + 1) : ℝ) - t i) * S (t (i + 1)))

/-- The **grid losses** (protection-leg kernel): `∑ D(tᵢ₊₁) (S tᵢ − S tᵢ₊₁)`, the discounted
probabilities of defaulting in each period. -/
noncomputable def cdsLossesGrid (D : ℝ≥0 → ℝ) (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, D (t (i + 1)) * (S (t i) - S (t (i + 1)))

/-- The **grid par spread** `(1 − R) · losses / annuity`. -/
noncomputable def cdsParSpreadGrid (D : ℝ≥0 → ℝ) (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (R : ℝ) (n : ℕ) : ℝ :=
  (1 - R) * cdsLossesGrid D S t n / cdsAnnuityGrid D S t n

section Value

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {τ : Ω → ℝ} {S : ℝ → ℝ}

private theorem integrable_defaultIndicator (hτ : Measurable τ) (u : ℝ≥0) :
    Integrable (defaultIndicator τ () u) Q :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_le hτ measurable_const)

private theorem integrable_one_sub_defaultIndicator (hτ : Measurable τ) (u : ℝ≥0) :
    Integrable (fun ω ↦ 1 - defaultIndicator τ () u ω) Q :=
  (integrable_const (1 : ℝ)).sub (integrable_defaultIndicator hτ u)

private theorem integrable_sub_defaultIndicator (hτ : Measurable τ) (u v : ℝ≥0) :
    Integrable (fun ω ↦ defaultIndicator τ () u ω - defaultIndicator τ () v ω) Q :=
  (integrable_defaultIndicator hτ u).sub (integrable_defaultIndicator hτ v)

omit [IsProbabilityMeasure Q] in
private theorem integral_defaultIndicator (hτ : Measurable τ)
    (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u) (u : ℝ≥0) :
    ∫ ω, defaultIndicator τ () u ω ∂Q = 1 - S u := by
  rw [← hS u]
  exact integral_indicator_one (measurableSet_le hτ measurable_const)

/-- **The premium leg is `s` times the grid annuity.** Against a default time `τ` with survival
function `S` (`Q(τ ≤ u) = 1 − S u`), the premium leg of the CDS is worth `s` times
`cdsAnnuityGrid D S t n`. -/
theorem value_cdsPremiumLeg (hτ : Measurable τ) (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u)
    (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (s : ℝ) (n : ℕ) :
    (cdsPremiumLeg t s n).value Q D (defaultIndicator τ) = s * cdsAnnuityGrid D S t n := by
  simp only [Contract.value, pathPV_cdsPremiumLeg, scenarioAt, cdsAnnuityGrid, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦
    ((integrable_one_sub_defaultIndicator hτ (t (i + 1))).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, integral_sub (integrable_const 1)
    (integrable_defaultIndicator hτ _), integral_defaultIndicator hτ hS]
  simp
  ring

/-- **The protection leg is `1 − R` times the grid losses.** -/
theorem value_cdsProtectionLeg (hτ : Measurable τ)
    (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u) (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (R : ℝ)
    (n : ℕ) :
    (cdsProtectionLeg t R n).value Q D (defaultIndicator τ) = (1 - R) * cdsLossesGrid D S t n := by
  simp only [Contract.value, pathPV_cdsProtectionLeg, scenarioAt, cdsLossesGrid, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦
    ((integrable_sub_defaultIndicator hτ (t (i + 1)) (t i)).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, integral_sub (integrable_defaultIndicator hτ _)
    (integrable_defaultIndicator hτ _), integral_defaultIndicator hτ hS,
    integral_defaultIndicator hτ hS]
  ring

private theorem integrable_pathPV_cdsPremiumLeg (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (t : ℕ → ℝ≥0) (s : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ (cdsPremiumLeg t s n).pathPV D (scenarioAt (defaultIndicator τ) ω)) Q := by
  simp only [pathPV_cdsPremiumLeg]
  exact integrable_finsetSum _ fun i _ ↦
    ((integrable_one_sub_defaultIndicator hτ _).const_mul _).const_mul _

private theorem integrable_pathPV_cdsProtectionLeg (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (t : ℕ → ℝ≥0) (R : ℝ) (n : ℕ) :
    Integrable
      (fun ω ↦ (cdsProtectionLeg t R n).pathPV D (scenarioAt (defaultIndicator τ) ω)) Q := by
  simp only [pathPV_cdsProtectionLeg]
  exact integrable_finsetSum _ fun i _ ↦
    ((integrable_sub_defaultIndicator hτ _ _).const_mul _).const_mul _

/-- **The protection buyer's CDS is worth protection less premium**: `(1 − R)` times the grid
losses minus `s` times the grid annuity. -/
theorem value_cdsBuyer (hτ : Measurable τ) (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u)
    (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (s R : ℝ) (n : ℕ) :
    (cdsBuyer t s R n).value Q D (defaultIndicator τ)
      = (1 - R) * cdsLossesGrid D S t n - s * cdsAnnuityGrid D S t n := by
  have hprem : Integrable (fun ω ↦ (Contract.scale (-1) (cdsPremiumLeg t s n)).pathPV D
      (scenarioAt (defaultIndicator τ) ω)) Q := by
    simp only [Contract.pathPV_scale]
    exact (integrable_pathPV_cdsPremiumLeg hτ D t s n).const_mul _
  rw [cdsBuyer, Contract.value_both _ _ _ _ _ (integrable_pathPV_cdsProtectionLeg hτ D t R n) hprem,
    Contract.value_scale, value_cdsProtectionLeg hτ hS, value_cdsPremiumLeg hτ hS]
  ring

/-- **The buyer's CDS is worth zero exactly at the grid par spread** (nonzero annuity). -/
theorem value_cdsBuyer_eq_zero_iff (hτ : Measurable τ)
    (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u) (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (s R : ℝ)
    (n : ℕ) (hA : cdsAnnuityGrid D S t n ≠ 0) :
    (cdsBuyer t s R n).value Q D (defaultIndicator τ) = 0
      ↔ s = cdsParSpreadGrid D S t R n := by
  rw [value_cdsBuyer hτ hS, cdsParSpreadGrid, eq_div_iff hA, sub_eq_zero, eq_comm]

end Value

section Cox

open MathFin.Cox

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {h : ℝ → ℝ}

omit [IsProbabilityMeasure μ] in
/-- **The Cox default time has survival function `hazardSurvival h`**, in the form the CDS
legs consume: `μ(τ ≤ u) = 1 − S u` for every date `u ≥ 0`. -/
theorem measureReal_coxDefaultTime_le (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (u : ℝ≥0) :
    μ.real {ω | coxDefaultTime h ξ ω ≤ u} = 1 - hazardSurvival h u := by
  have hS1 : hazardSurvival h u ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (intervalIntegral.integral_nonneg u.coe_nonneg fun s _ ↦
      (hpos s).le))
  have hcdf := cox_cdf_timeVarying (μ := μ) hh hpos hdiv hξmeas hξlaw u.coe_nonneg
  refine (congrArg ENNReal.toReal hcdf).trans ?_
  rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hS1) ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (hazardSurvival_pos h u).le, ENNReal.toReal_one]

/-- **The CDS contract under the Cox default time**: the protection buyer's CDS on the grid `t`,
priced against the default time built from a unit-exponential clock `ξ` by inverting the
cumulative hazard of a continuous positive intensity `h`, is worth `(1 − R)` times the grid losses
of the hazard curve less `s` times its grid annuity. -/
theorem value_cdsBuyer_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (D : ℝ≥0 → ℝ)
    (t : ℕ → ℝ≥0) (s R : ℝ) (n : ℕ) :
    (cdsBuyer t s R n).value μ D (defaultIndicator (coxDefaultTime h ξ))
      = (1 - R) * cdsLossesGrid D (hazardSurvival h) t n
        - s * cdsAnnuityGrid D (hazardSurvival h) t n :=
  value_cdsBuyer (measurable_coxDefaultTime hh hpos hξmeas)
    (measureReal_coxDefaultTime_le hh hpos hdiv hξmeas hξlaw) D t s R n

/-- Without discounting the grid losses telescope to the default probability, whatever the grid. -/
theorem cdsLossesGrid_one (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) :
    cdsLossesGrid (fun _ ↦ 1) S t n = S (t 0) - S (t n) := by
  simpa [cdsLossesGrid] using Finset.sum_range_sub' (fun i ↦ S (t i)) n

/-- **The undiscounted grid losses are the continuous ones**: on any grid from `t 0 = 0` to `t n`,
the undiscounted grid losses of the hazard curve equal `Cox.cdsLosses 0 h (t n)`, the integral
of the default density. -/
theorem cdsLossesGrid_one_eq_cdsLosses (hh : Continuous h) (t : ℕ → ℝ≥0) (n : ℕ)
    (h0 : t 0 = 0) :
    cdsLossesGrid (fun _ ↦ 1) (hazardSurvival h) t n = cdsLosses 0 h (t n) := by
  rw [cdsLossesGrid_one, h0, NNReal.coe_zero, hazardSurvival_at_zero, cdsLosses]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  exact (defaultDensity_antideriv hh _).symm

end Cox

end MathFin.Contracts
