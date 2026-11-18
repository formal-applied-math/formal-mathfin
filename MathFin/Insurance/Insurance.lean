/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Insurance.Mortality
public import MathFin.Models.Rates.ZCB

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
* `chainFactor`: the selected chain-ladder development factor `f̂_j` of a cumulative
  triangle `C` with `n` development periods: the ratio of successive column sums over
  the rows `i < n - j` observed in both columns.
* `chainComplete`: the chain-ladder completion of `C`, defined for all cells; it agrees
  with `C` on observed cells and multiplies forward by selected factors afterwards.

## Main results

* `annuityDue_closed_form`: `Σ_{k=0}^{n-1} v^k = (1 − v^n)/(1 − v)` (geometric).
* `net_premium_principle`: `P · A = B ↔ P = B / A` for `A ≠ 0`.
* `lifeAnnuityDue_const`: under a constant force of mortality `m` and `e^{-(r + m)} ≠ 1`, the life
  annuity-due is the geometric closed form at the discount factor `e^{-(r + m)}`.
* `chainComplete_unobserved`: on unobserved cells the completion equals the last observed
  cell times the product of the selected factors over the unobserved development periods.

## References

* [D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life
  Contingent Risks*][DicksonHardyWaters2013], Chapter 5 (annuities).
* [Bowers and others, *Actuarial Mathematics*][BowersEtAl]
* [T. Mack, *Distribution-free Calculation of the Standard Error of Chain Ladder
  Reserve Estimates*][Mack1993], the chain-ladder development-factor method.

## Tags

net premium, equivalence principle, annuity-due, life annuity, force of mortality,
actuarial present value, MSC 91G05, JEL G22
-/

@[expose] public section

namespace MathFin

open Finset

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

/-- The **chain-ladder development factor** `f̂_j` of a cumulative triangle `C` with `n`
development periods: the ratio of the column-`j+1` sum to the column-`j` sum over the
rows `i < n - j` observed in both columns (`Finset.range (n - j)`). -/
noncomputable def chainFactor (n : ℕ) (C : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n - j), C i (j + 1)) / ∑ i ∈ Finset.range (n - j), C i j

/-- The **chain-ladder completion** of `C`: observed cells (`i + j ≤ n`) keep `C i j`;
each unobserved cell multiplies the previous cell in its row by the selected factor
`chainFactor n C j`. -/
noncomputable def chainComplete : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | _, C, i, 0 => C i 0
  | n, C, i, j + 1 =>
      if i + (j + 1) ≤ n then C i (j + 1)
      else chainComplete n C i j * chainFactor n C j

/-- Observed cells are preserved by the completion. -/
theorem chainComplete_eq (n : ℕ) (C : ℕ → ℕ → ℝ) (i j : ℕ) (h : i + j ≤ n) :
    chainComplete n C i j = C i j := by
  revert h
  induction j with
  | zero => intro h; rfl
  | succ j _ => intro h; simp [chainComplete, h]

/-- **Product-of-selected-factors formula**: on unobserved cells (`n < i + j`) the
completion equals the last observed cell `C i (n - i)` times the product of the
selected factors over `[n - i, j)`. -/
theorem chainComplete_unobserved (n : ℕ) (C : ℕ → ℕ → ℝ) (i j : ℕ)
    (hij : n < i + j) :
    chainComplete n C i j
      = C i (n - i) * ∏ k ∈ Finset.Ico (n - i) j, chainFactor n C k := by
  revert hij
  induction j with
  | zero =>
      intro hij
      have hni : n - i = 0 := by omega
      simp [chainComplete, hni]
  | succ j ih =>
      intro hij
      have hneg : ¬ i + (j + 1) ≤ n := by omega
      simp only [chainComplete, hneg, ↓reduceIte]
      by_cases hobs : i + j ≤ n
      · rw [chainComplete_eq n C i j hobs]
        have hji : j = n - i := by omega
        subst hji
        have hle : n - i ≤ n - i := le_refl _
        rw [Finset.prod_Ico_succ_top hle]
        rw [Finset.Ico_self, Finset.prod_empty, one_mul]
      · have hlt : n < i + j := by omega
        rw [ih hlt]
        have hle : n - i ≤ j := by omega
        rw [Finset.prod_Ico_succ_top hle]
        ring

end MathFin
