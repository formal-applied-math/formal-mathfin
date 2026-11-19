/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Insurance.Mortality
public import MathFin.Models.Rates.ZCB
import Mathlib.Tactic.LinearCombination

/-!
# Net premium principle and the life annuity-due

The **net premium principle** sets the periodic premium `P` of an insurance
contract by equating the present value of the premiums with the present value of
the benefits:

  `P · annuityFactor = benefitPV`,

so `P = benefitPV / annuityFactor` (`net_premium_principle`, Mathlib's `eq_div_iff`).

The annuity factor of `n` payments at the start of each period is the
**annuity-due** `ä_n = ∑_{k<n} vᵏ = (1 − vⁿ)/(1 − v)` for a per-period discount
factor `v ≠ 1` (`annuityDue_closed_form`, a geometric sum). The immediate annuity of
`Models/Rates/CouponBonds.lean` (`annuityValue`) pays one period later.

A **life annuity-due** pays only while the insured is alive:
`ä = ∑_{k<n} B(0, k) · S(k)` (`lifeAnnuityDue`), with the flat-rate zero-coupon bond
price `B(0, k) = zcb r 0 k` (`Models/Rates/ZCB.lean`) and the survival probability
`S(k) = survivalFromForce μ k = exp(−∫₀ᵏ μ)` of a force of mortality `μ`
(`Insurance/Mortality.lean`). For a constant force `m`, survival is `e^{−mk}` and
discounting is `e^{−rk}`, so the life annuity-due is the annuity-certain at the
discount factor `e^{−(r + m)}`: a constant force of mortality acts as an addition to
the interest rate (`lifeAnnuityDue_const`). This is the discrete counterpart of the
risky annuity `riskyAnnuity_eq` of `Models/Credit/Cox.lean`, where a constant default
intensity adds to the rate in the same way.

`lifeAnnuityDue` is written directly as the sum `∑ B(0, k) S(k)`. That it is the
value of the payments made while a random lifetime with survival function `S` has not
ended is `lifeAnnuityDue_eq_value` (`Insurance/AnnuityValue.lean`).

## Main definitions

* `lifeAnnuityDue`: the life annuity-due of `n` unit payments at times `0, …, n − 1`, each paid
  only if the insured is alive, for a rate `r` and a force of mortality `μ`.

## Main results

* `annuityDue_closed_form`: `Σ_{k=0}^{n-1} v^k = (1 − v^n)/(1 − v)` (geometric).
* `net_premium_principle`: `P · A = B ↔ P = B / A` for `A ≠ 0`.
* `lifeAnnuityDue_const`: under a constant force of mortality `m` and `e^{-(r + m)} ≠ 1`, the life
  annuity-due is the geometric closed form at the discount factor `e^{-(r + m)}`.
* `term_add_endowment_eq_annuityDue`: finite term insurance plus survivor endowment equals
  `1 - (1 - v) * ä_n`, with `ä_n` the annuity-due survival-payment sum.
* `wholeLife_add_endowment_eq_annuityDue`: the whole-life limit of that identity,
  `A = 1 - (1 - v) * ä`, under summability and a vanishing discounted survival tail.

## References

* [D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life
  Contingent Risks*][DicksonHardyWaters2013], Chapter 5 (annuities).
* [Bowers and others, *Actuarial Mathematics*][BowersEtAl]

## Tags

net premium, equivalence principle, annuity-due, life annuity, force of mortality,
actuarial present value, MSC 91G05, JEL G22
-/

@[expose] public section

namespace MathFin

open Finset Filter Topology

/-- **Annuity-due geometric closed form**: `Σ_{k=0}^{n-1} v^k = (1 − v^n)/(1 − v)`
for `v ≠ 1`. -/
theorem annuityDue_closed_form (v : ℝ) (n : ℕ) (hv : v ≠ 1) :
    ∑ k ∈ Finset.range n, v ^ k = (1 - v ^ n) / (1 - v) := by
  have h_one_sub_ne : (1 : ℝ) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have h_v_sub_ne : v - 1 ≠ 0 := sub_ne_zero.mpr hv
  rw [geom_sum_eq hv n]
  rw [div_eq_div_iff h_v_sub_ne h_one_sub_ne]
  ring

/-- **Net premium principle**: `P · A = B ⟺ P = B / A` for `A ≠ 0` — the
defining algebra of the net premium. This is Mathlib's `eq_div_iff`
(symmetrised), cited rather than re-proved. -/
theorem net_premium_principle (P A B : ℝ) (hA : A ≠ 0) :
    P * A = B ↔ P = B / A :=
  (eq_div_iff hA).symm

/-- The **life annuity-due** of `n` unit payments at times `0, 1, …, n − 1`, each paid only if
the insured is alive: `∑_{k<n} B(0, k) · S(k)`, with the flat-rate zero-coupon bond price
`B(0, k) = zcb r 0 k` and the survival probability `S(k) = survivalFromForce μ k` of the force
of mortality `μ`. -/
noncomputable def lifeAnnuityDue (r : ℝ) (μ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, zcb r 0 k * survivalFromForce μ k

/-- **A constant force of mortality adds to the interest rate**: for a constant force `m`, the
life annuity-due is the annuity-certain `(1 − vⁿ)/(1 − v)` at the discount factor
`v = e^{−(r + m)}`, for `v ≠ 1`. Each term is `e^{−rk} · e^{−mk} = (e^{−(r + m)})ᵏ`, and the sum is
`annuityDue_closed_form`. -/
theorem lifeAnnuityDue_const {r m : ℝ} (n : ℕ) (hv : Real.exp (-(r + m)) ≠ 1) :
    lifeAnnuityDue r (fun _ ↦ m) n =
      (1 - Real.exp (-(r + m)) ^ n) / (1 - Real.exp (-(r + m))) := by
  rw [← annuityDue_closed_form _ n hv, lifeAnnuityDue]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [zcb, survivalFromForce, survivalFromIntensity, cumulativeIntensity,
    intervalIntegral.integral_const, ← Real.exp_add, ← Real.exp_nat_mul, smul_eq_mul]
  congr 1
  ring

/-- **Finite term insurance plus survivor endowment**: the death sum is the
`value_cdsProtectionLeg` unit-grid value at recovery `R = 0`, and the annuity sum is the
`lifeAnnuityDue` survival-payment schedule at dates `k` (not the arrears CDS premium leg,
which pays at `k + 1`). -/
theorem term_add_endowment_eq_annuityDue (S : ℕ → ℝ) (hS0 : S 0 = 1)
    (v : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, v ^ (k + 1) * (S k - S (k + 1))) + v ^ n * S n
      = 1 - (1 - v) * ∑ k ∈ Finset.range n, v ^ k * S k := by
  induction n with
  | zero => simp [hS0]
  | succ n IH =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ v n]
      linear_combination IH

/-- **Whole-life limit of the term insurance plus endowment identity**: the finite identity
`term_add_endowment_eq_annuityDue` passes to the limit as the term tends to infinity. The term
insurance partial sums converge to the whole-life EPV, the endowment term vanishes by the tail
hypothesis, and the life annuity-due partial sums converge to the annuity-due, giving the
whole-life identity `A = 1 - (1 - v) * ä`. -/
theorem wholeLife_add_endowment_eq_annuityDue (S : ℕ → ℝ) (hS0 : S 0 = 1)
    (v : ℝ) (_hv : 0 < v)
    (hdeath : Summable fun k => v ^ (k + 1) * (S k - S (k + 1)))
    (hann : Summable fun k => v ^ k * S k)
    (htail : Tendsto (fun n => v ^ n * S n) atTop (𝓝 0)) :
    ∑' k, v ^ (k + 1) * (S k - S (k + 1)) = 1 - (1 - v) * ∑' k, v ^ k * S k := by
  have hfin : ∀ n : ℕ, (∑ k ∈ Finset.range n, v ^ (k + 1) * (S k - S (k + 1)))
      + v ^ n * S n = 1 - (1 - v) * ∑ k ∈ Finset.range n, v ^ k * S k :=
    fun n => term_add_endowment_eq_annuityDue S hS0 v n
  have hL : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, v ^ (k + 1) * (S k - S (k + 1)))
      + v ^ n * S n) atTop (𝓝 ((∑' k, v ^ (k + 1) * (S k - S (k + 1))) + 0)) :=
    hdeath.hasSum.tendsto_sum_nat.add htail
  have hA := hann.hasSum.tendsto_sum_nat
  have hM : Tendsto (fun n : ℕ => (1 - v) * ∑ k ∈ Finset.range n, v ^ k * S k)
      atTop (𝓝 ((1 - v) * ∑' k, v ^ k * S k)) :=
    tendsto_const_nhds.mul hA
  have hR : Tendsto (fun n : ℕ => 1 - (1 - v) * ∑ k ∈ Finset.range n, v ^ k * S k)
      atTop (𝓝 (1 - (1 - v) * ∑' k, v ^ k * S k)) :=
    tendsto_const_nhds.sub hM
  have heq := tendsto_nhds_unique_of_forall hL hR hfin
  simpa using heq

end MathFin
