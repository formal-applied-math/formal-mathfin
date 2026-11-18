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

## Main results

* `annuityDue_closed_form`: `Σ_{k=0}^{n-1} v^k = (1 − v^n)/(1 − v)` (geometric).
* `net_premium_principle`: `P · A = B ↔ P = B / A` for `A ≠ 0`.
* `lifeAnnuityDue_const`: under a constant force of mortality `m` and `e^{-(r + m)} ≠ 1`, the life
  annuity-due is the geometric closed form at the discount factor `e^{-(r + m)}`.
* `stopLoss_succ`: on the integer lattice `S ∈ h * ℕ` a.s. with `h > 0`, stop-loss expectations
  satisfy `SL(j+1) = SL(j) - h * P(S > j * h)`.

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

open MeasureTheory

/-- **Stop-loss recurrence on the integer lattice**: if `S ≥ 0` is integrable and `S ∈ h * ℕ`
a.s. with `h > 0`, then `E[(S - (j+1) * h)⁺] = E[(S - j * h)⁺] - h * P(S > j * h)`. -/
theorem stopLoss_succ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Ω → ℝ) (hSmeas : Measurable S)
    (hSint : Integrable S μ) (hS0 : ∀ᵐ ω ∂μ, 0 ≤ S ω) (h : ℝ) (hh : 0 < h)
    (hlat : ∀ᵐ ω ∂μ, ∃ n : ℕ, S ω = n * h) (j : ℕ) :
    ∫ ω, max (S ω - (j + 1 : ℕ) * h) 0 ∂μ
      = ∫ ω, max (S ω - (j : ℝ) * h) 0 ∂μ - h * μ.real {ω | (j : ℝ) * h < S ω} := by
  have hs : MeasurableSet {ω | (j : ℝ) * h < S ω} :=
    measurableSet_lt measurable_const hSmeas
  have hc0 : (0 : ℝ) ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hh)
  have hInt : ∀ c : ℝ, 0 ≤ c → Integrable (fun ω => max (S ω - c) 0) μ := by
    intro c hc
    refine Integrable.mono' hSint ?_ ?_
    · exact ((hSmeas.sub_const c).max measurable_const).aestronglyMeasurable
    · filter_upwards [hS0] with ω hω
      have hnn : (0 : ℝ) ≤ max (S ω - c) 0 := le_max_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact max_le (by linarith) hω
  have hInt0 : Integrable (fun ω => max (S ω - (j : ℝ) * h) 0) μ := hInt _ hc0
  have hgInt : Integrable ({ω | (j : ℝ) * h < S ω}.indicator (fun _ => h)) μ :=
    (integrable_const h).indicator hs
  have hpt : ∀ᵐ ω ∂μ, max (S ω - (j + 1 : ℕ) * h) 0
      = max (S ω - (j : ℝ) * h) 0
        - {ω | (j : ℝ) * h < S ω}.indicator (fun _ => h) ω := by
    filter_upwards [hlat] with ω hω
    obtain ⟨n, hn⟩ := hω
    rw [hn]
    by_cases hmem : ω ∈ {ω | (j : ℝ) * h < S ω}
    · rw [Set.indicator_of_mem hmem]
      show max (↑n * h - (j + 1 : ℕ) * h) 0 = max (↑n * h - (j : ℝ) * h) 0 - h
      rw [Set.mem_ofPred_eq] at hmem
      rw [hn] at hmem
      have hlt : (j : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_right hmem (le_of_lt hh)
      have hjn : j < n := Nat.cast_lt.mp hlt
      have hjn1 : j + 1 ≤ n := by omega
      have hle : ((j + 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn1
      have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hh)
      have h2 : (0 : ℝ) ≤ ↑n * h - ((j + 1 : ℕ) : ℝ) * h := by linarith
      have h1 : (0 : ℝ) ≤ ↑n * h - (j : ℝ) * h := by linarith
      rw [max_eq_left h2, max_eq_left h1]
      have hcast : ((j + 1 : ℕ) : ℝ) * h = (j : ℝ) * h + h := by
        rw [Nat.cast_add, Nat.cast_one]; ring
      rw [hcast]; ring
    · rw [Set.indicator_of_notMem hmem, sub_zero]
      have hle' : S ω ≤ (j : ℝ) * h := le_of_not_gt (by simpa using hmem)
      rw [hn] at hle'
      have g2 : (n : ℝ) * h - (j : ℝ) * h ≤ 0 := by linarith
      have g1 : (n : ℝ) * h - ((j + 1 : ℕ) : ℝ) * h ≤ 0 := by
        have hcast : ((j + 1 : ℕ) : ℝ) * h = (j : ℝ) * h + h := by
          rw [Nat.cast_add, Nat.cast_one]; ring
        linarith
      rw [max_eq_right g1, max_eq_right g2]
  have htail : ∫ ω, {ω | (j : ℝ) * h < S ω}.indicator (fun _ => h) ω ∂μ
      = h * μ.real {ω | (j : ℝ) * h < S ω} := by
    rw [integral_indicator hs]
    simp only [setIntegral_const, smul_eq_mul]
    ring
  rw [integral_congr_ae hpt, integral_sub hInt0 hgInt, htail]

end MathFin
