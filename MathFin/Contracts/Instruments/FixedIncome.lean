/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Pricing
public import MathFin.FixedIncome.MacaulayModified
public import MathFin.FixedIncome.CouponBonds
public import MathFin.FixedIncome.InterestRateSwap
public import MathFin.FixedIncome.FRA

/-!
# Bonds and swaps, as contracts

A schedule of payments is a contract: `payFlows t a n` pays the payoff `a i` at `t i` for each
`i < n`, worth `∑ D(tᵢ) · aᵢ` along a scenario (`pathPV_payFlows`); `fixedFlows t c n` is the case of
constant payoffs, `c i` at `t i`. Along every scenario its present value is `∑ D(tᵢ) cᵢ`
(`pathPV_fixedFlows`), and since it observes nothing its value in every model is that same sum
(`value_fixedFlows`). The library's
fixed-income prices are instances:

* a coupon bond discounted at a yield `y`, with integer payment times, is `bondPriceDisc`
  (`pathPV_fixedFlows_yieldDiscount`), the price the durations and convexities of
  `FixedIncome/` are taken of;
* `n` level payments on a grid of step `Δt`, discounted on the flat continuous curve `zcb r 0`,
  are `annuityValue` (`pathPV_fixedFlows_zcb`).

A swap on a deterministic discount curve `P` exchanges a fixed leg, `δK` at each payment date,
for a floating leg that pays the simple forward rate the curve implies for each accrual period,
`δ · fraForwardRate (P Tᵢ) (P Tᵢ₊₁) δ` at `Tᵢ₊₁`. The floating leg telescopes to `P(T₀) − P(Tₙ)`
(`pathPV_floatingLeg`), the fixed leg is `K` times the annuity (`pathPV_fixedLeg`), so the payer
swap is worth `payerSwapValue` (`value_payerSwap`), and it is worth zero exactly at the par rate
(`value_payerSwap_eq_zero_iff`). The floating coupons are fixed by the curve: this is the
deterministic-rates case, where a floating rate is known in advance. With one accrual period
the swap is a forward-rate agreement, worth `fraValue` (`value_payerSwap_one_eq_fraValue`).

## Main definitions

* `payFlows` — a schedule of payments; `fixedFlows` — the schedule of fixed cash flows.
* `yieldDiscount` — discounting at a yield with annual compounding.
* `floatingLeg`, `fixedLeg`, `payerSwap` — the legs of a swap on a deterministic curve.

## Main results

* `pathPV_payFlows`, `pathPV_fixedFlows`, `value_fixedFlows`, `pathPV_fixedFlows_yieldDiscount`,
  `pathPV_fixedFlows_zcb`.
* `pathPV_floatingLeg`, `pathPV_fixedLeg`, `value_payerSwap`, `value_payerSwap_eq_zero_iff`,
  `value_payerSwap_one_eq_fraValue`.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon,
*The Contract Is Not the Model: Proof-Carrying Exotic Derivatives and the
Economics of Model Risk* (working paper, 9 August 2026; Mathematical
Finance, Imperial College London), with code at
<https://github.com/thalesians/lean_contracts> (Apache-2.0). That paper in
turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A contract that pays the same along every scenario is worth that amount** in every model,
under any probability measure. -/
theorem Contract.value_eq_of_pathPV_eq {Q : Measure Ω} [IsProbabilityMeasure Q] {D : ℝ≥0 → ℝ}
    (X : ι → ℝ≥0 → Ω → ℝ) {c : Contract ι} {v : ℝ} (h : ∀ s, c.pathPV D s = v) :
    c.value Q D X = v := by
  simp [Contract.value, h]

/-- A **schedule of payments**: for each `i < n`, pay the payoff `a i` at time `t i`. -/
noncomputable def payFlows (t : ℕ → ℝ≥0) (a : ℕ → Payoff ι) : ℕ → Contract ι
  | 0 => .zero
  | n + 1 => .both (payFlows t a n) (.pay (t n) (a n))

/-- Along every scenario, a schedule of payments is worth `∑ D(tᵢ) · aᵢ`. -/
theorem pathPV_payFlows (D : ℝ≥0 → ℝ) (s : Scenario ι) (t : ℕ → ℝ≥0) (a : ℕ → Payoff ι)
    (n : ℕ) :
    (payFlows t a n).pathPV D s = ∑ i ∈ Finset.range n, D (t i) * (a i).eval s := by
  induction n with
  | zero => simp [payFlows, Contract.pathPV, Contract.cashflows]
  | succ n ih =>
    rw [payFlows, Contract.pathPV_both, ih, Finset.sum_range_succ]
    simp [Contract.pathPV, Contract.cashflows]

/-- A **schedule of fixed cash flows**: for each `i < n`, pay `c i` at time `t i`. -/
noncomputable def fixedFlows (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) : Contract ι :=
  payFlows t (fun i ↦ .const (c i)) n

/-- Along every scenario, a schedule of fixed cash flows is worth `∑ D(tᵢ) cᵢ`. -/
theorem pathPV_fixedFlows (D : ℝ≥0 → ℝ) (s : Scenario ι) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).pathPV D s = ∑ i ∈ Finset.range n, D (t i) * c i := by
  simp [fixedFlows, pathPV_payFlows, Payoff.eval]

/-- In every model, a schedule of fixed cash flows is worth `∑ D(tᵢ) cᵢ`. -/
theorem value_fixedFlows {Q : Measure Ω} [IsProbabilityMeasure Q] (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).value Q D X = ∑ i ∈ Finset.range n, D (t i) * c i :=
  Contract.value_eq_of_pathPV_eq X fun s ↦ pathPV_fixedFlows D s t c n

/-- Discounting at a yield `y` with annual compounding, `(1 + y)^{−τ}`; a discount factor for
`1 + y > 0`. -/
noncomputable def yieldDiscount (y : ℝ) : ℝ≥0 → ℝ := fun τ ↦ (1 + y) ^ (-(τ : ℝ))

/-- **A coupon bond at a yield is `bondPriceDisc`.** Discounted at the yield `y`, cash flows
`c i` at integer times `t i` are worth `∑ cᵢ / (1 + y)^{tᵢ}`. -/
theorem pathPV_fixedFlows_yieldDiscount {y : ℝ} (hy : 0 ≤ 1 + y) (s : Scenario ι) (t : ℕ → ℕ)
    (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows (fun i ↦ (t i : ℝ≥0)) c n : Contract ι).pathPV (yieldDiscount y) s
      = bondPriceDisc (Finset.range n) t c y := by
  rw [pathPV_fixedFlows, bondPriceDisc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [yieldDiscount, NNReal.coe_natCast, Real.rpow_neg hy, Real.rpow_natCast, div_eq_inv_mul]

/-- **Level payments on the flat continuous curve are `annuityValue`.** `n` payments of `c` at
`Δt, 2Δt, …, nΔt`, discounted by `zcb r 0`, are worth `∑ c e^{−r(i+1)Δt}`. -/
theorem pathPV_fixedFlows_zcb (s : Scenario ι) (n : ℕ) (c r : ℝ) (Δt : ℝ≥0) :
    (fixedFlows (fun i ↦ (i + 1 : ℝ≥0) * Δt) (fun _ ↦ c) n : Contract ι).pathPV
        (fun τ ↦ zcb r 0 τ) s = annuityValue n c r Δt := by
  rw [pathPV_fixedFlows, annuityValue]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [zcb, sub_zero, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  ring

variable (P : ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) (δ : ℝ) (n : ℕ)

/-- The **floating leg** of a swap on the deterministic discount curve `P`, with payment dates
`T 1, …, T n` and accrual `δ`: at `T (i + 1)` it pays `δ` times the simple forward rate the curve
implies for `[T i, T (i + 1)]`. -/
noncomputable def floatingLeg : Contract ι :=
  fixedFlows (fun i ↦ T (i + 1)) (fun i ↦ δ * fraForwardRate (P (T i)) (P (T (i + 1))) δ) n

/-- The **fixed leg** of a swap with fixed rate `K`: `δK` at each of `T 1, …, T n`. -/
noncomputable def fixedLeg (K : ℝ) : Contract ι := fixedFlows (fun i ↦ T (i + 1)) (fun _ ↦ δ * K) n

/-- The **payer swap**: receive the floating leg, pay the fixed leg. -/
noncomputable def payerSwap (K : ℝ) : Contract ι :=
  .both (floatingLeg P T δ n) (.scale (-1) (fixedLeg T δ n K))

variable {P T δ}

/-- **The floating leg telescopes.** Discounted on its own curve, each forward-rate coupon is
worth `P(Tᵢ) − P(Tᵢ₊₁)`, so the leg is worth `P(T₀) − P(Tₙ)`. -/
theorem pathPV_floatingLeg (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0) (s : Scenario ι) :
    (floatingLeg P T δ n : Contract ι).pathPV P s = P (T 0) - P (T n) := by
  rw [floatingLeg, pathPV_fixedFlows]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, fraForwardRate]
    field_simp [hP (n + 1)]
    ring

/-- The fixed leg is worth `K` times the annuity of its payment dates. -/
theorem pathPV_fixedLeg (K : ℝ) (s : Scenario ι) :
    (fixedLeg T δ n K : Contract ι).pathPV P s
      = K * annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n) := by
  rw [fixedLeg, pathPV_fixedFlows, annuity, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **A payer swap on a deterministic curve is worth `payerSwapValue`** in every model: the
floating leg `P(T₀) − P(Tₙ)` less `K` times the annuity. -/
theorem value_payerSwap {Q : Measure Ω} [IsProbabilityMeasure Q] (X : ι → ℝ≥0 → Ω → ℝ)
    (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0) (K : ℝ) :
    (payerSwap P T δ n K : Contract ι).value Q P X
      = payerSwapValue (P (T 0)) (P (T n)) K (annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n)) :=
  Contract.value_eq_of_pathPV_eq X fun s ↦ by
    rw [payerSwap, Contract.pathPV_both, Contract.pathPV_scale, pathPV_floatingLeg n hδ hP,
      pathPV_fixedLeg, payerSwapValue]
    ring

/-- **A forward-rate agreement is a one-period payer swap.** With one accrual period `[T₀, T₁]`
the swap's floating coupon is the simple forward rate `fraForwardRate (P T₀) (P T₁) δ` and the
fixed coupon is `δK`, both paid at `T₁`; its value in every model is `fraValue`
(`FixedIncome/FRA.lean`): `δ · P(T₁) · (F − K)`. -/
theorem value_payerSwap_one_eq_fraValue {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : ι → ℝ≥0 → Ω → ℝ) (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0) (K : ℝ) :
    (payerSwap P T δ 1 K : Contract ι).value Q P X
      = fraValue δ (P (T 1)) (fraForwardRate (P (T 0)) (P (T 1)) δ) K := by
  rw [value_payerSwap 1 X hδ hP, fraValue_forwardRate_eq_discount_difference _ _ _ _ hδ (hP 1),
    payerSwapValue, annuity]
  simp only [Finset.sum_range_one, zero_add]
  ring

/-- **A payer swap is worth zero exactly at the par swap rate.** -/
theorem value_payerSwap_eq_zero_iff {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : ι → ℝ≥0 → Ω → ℝ) (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0)
    (hA : annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n) ≠ 0) (K : ℝ) :
    (payerSwap P T δ n K : Contract ι).value Q P X = 0
      ↔ K = parSwapRate (P (T 0)) (P (T n))
        (annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n)) := by
  rw [value_payerSwap n X hδ hP]
  exact payerSwapValue_eq_zero_iff _ _ _ hA

end MathFin.Contracts
