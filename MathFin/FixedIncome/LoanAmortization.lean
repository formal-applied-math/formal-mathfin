/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.CouponBonds

/-!
# Loan amortization schedules: bullet, equal-principal and level-payment

All three schedules share the same per-period interest accrual on the outstanding
balance `B_{n-1}`,

  `I_n = B_{n-1} · i`,

and the same balance recurrence given the period's principal payment `P_n`,

  `B_n = B_{n-1} - P_n`.

They differ only in how `P_n` is chosen:

* **Bullet** (interest-only): `P_n = 0` for `n < N`, `P_N = B_0` — the whole
  principal is repaid in a single final installment. Closed form:
  `B_n = B_0` for `n < N`, `B_N = 0`.
* **Equal-principal**: `P_n = B_0 / N` every period — a constant principal
  payment. Closed form: `B_n = B_0 · (1 - n / N)`.
* **Level payment** (mortgage-style): the same payment `A` every period, its
  principal part `P_n = A - I_n` being what is left after interest, so
  `B_n = B_{n-1}·(1 + i) - A`. Priced against `annuityValue`
  (`MathFin/FixedIncome/CouponBonds.lean`), the present value of `N` payments
  `A` discounted continuously at rate `r` over periods of length `Δt`: if the
  loan's principal is that annuity's value and the period rate is
  `i = e^{rΔt} - 1`, then after `n ≤ N` payments the outstanding balance is
  the value of the `N - n` payments still to come, and the loan is paid off
  at `N`.

All three closed forms are proved here by induction on the balance recurrence,
matching the standard amortization-table identities.

## Result

* `bulletPrincipal`, `equalPrincipalPayment` — the two principal-payment
  schedules.
* `balance` — the shared balance recurrence `B_n = B_{n-1} - P_n` (as a fold).
* `interestAccrued`, `interestAccrued_succ` — `I_n = B_{n-1} · i`,
  independent of the schedule (proved on actual periods `n + 1`).
* `balance_bullet_lt`, `balance_bullet_eq` — the bullet closed form.
* `balance_equalPrincipal` — the equal-principal closed form
  `B_n = B_0 · (1 - n / N)`.
* `levelPaymentBalance`, `balance_levelPayment` — the level-payment balance,
  and that it is `balance` with principal `A - I_n`.
* `annuityValue_succ_mul_exp_sub` — one period of an annuity's value:
  `A_{m+1}·e^{rΔt} - A = A_m`.
* `levelPaymentBalance_eq_annuityValue`, `levelPaymentBalance_eq_zero` — the
  balance after `n` level payments is `annuityValue (N - n) A r Δt`, and zero
  at `N`.
-/

@[expose] public section

namespace MathFin

/-- The outstanding balance after `n` periods, given an initial balance `B₀`
and a principal-payment schedule `P : ℕ → ℝ` (period `k`'s payment is `P k`
for `k = 1, …, n`). Defined by the shared recurrence `B_n = B_{n-1} - P_n`. -/
def balance (B0 : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => B0
  | n + 1 => balance B0 P n - P (n + 1)

/-- Interest accrued in period `n ≥ 1` is the prior balance times the period
rate: `I_n = B_{n-1} · i`, for any principal schedule `P` fixed in advance. Periods are
`n = 1, …, N`; `n - 1` is ℕ-truncated subtraction, so at `n = 0` this
evaluates to `B₀ · i` (the same value as period 1) rather than being
undefined — `n = 0` is not a meaningful period, and callers should use
`interestAccrued_succ` for the proved recurrence on actual periods. -/
def interestAccrued (B0 : ℝ) (P : ℕ → ℝ) (i : ℝ) (n : ℕ) : ℝ :=
  balance B0 P (n - 1) * i

/-- The defining recurrence of `interestAccrued`, stated on `n + 1` (an
actual period `n + 1 ≥ 1`) to avoid the ℕ-truncated-subtraction pitfall at
`n = 0`: `I_{n+1} = B_n · i`. -/
@[simp] theorem interestAccrued_succ (B0 : ℝ) (P : ℕ → ℝ) (i : ℝ) (n : ℕ) :
    interestAccrued B0 P i (n + 1) = balance B0 P n * i := rfl

/-- The bullet schedule: no principal is repaid before maturity `N`, and the
entire balance is repaid in period `N`. -/
def bulletPrincipal (B0 : ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n ↦ if n = N then B0 else 0

/-- Under the bullet schedule, the balance is unchanged before maturity. -/
theorem balance_bullet_lt {B0 : ℝ} {N n : ℕ} (hn : n < N) :
    balance B0 (bulletPrincipal B0 N) n = B0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [balance, bulletPrincipal, ih (Nat.lt_of_succ_lt hn), hn.ne]

/-- Under the bullet schedule, the balance is exactly zero at maturity `N ≥ 1`
(at `N = 0` maturity is not a payment period, and the balance stays `B₀`). -/
theorem balance_bullet_eq {B0 : ℝ} {N : ℕ} (hN : 0 < N) :
    balance B0 (bulletPrincipal B0 N) N = 0 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp [balance, bulletPrincipal, balance_bullet_lt (Nat.lt_succ_self M)]

/-- The equal-principal schedule: a constant payment `B₀ / N` every period. -/
noncomputable def equalPrincipalPayment (B0 : ℝ) (N : ℕ) : ℕ → ℝ := fun _ ↦ B0 / N

/-- Closed form for the equal-principal schedule: `B_n = B₀ · (1 - n / N)`,
proved by induction on the balance recurrence. -/
theorem balance_equalPrincipal {B0 : ℝ} {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    balance B0 (equalPrincipalPayment B0 N) n = B0 * (1 - (n : ℝ) / N) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  induction n with
  | zero => simp [balance]
  | succ k ih =>
    simp only [balance, equalPrincipalPayment, ih]
    push_cast
    field_simp
    ring

/-- The level-payment balance: interest at period rate `i` accrues on the
outstanding balance, then the payment `A` is made, `B_{n+1} = B_n·(1 + i) - A`. -/
def levelPaymentBalance (B0 A i : ℝ) : ℕ → ℝ
  | 0 => B0
  | n + 1 => levelPaymentBalance B0 A i n * (1 + i) - A

/-- The level-payment schedule is the shared recurrence `balance` with the
principal part of period `n + 1`'s payment being `A` less the interest
`B_n · i` on the outstanding balance. -/
theorem balance_levelPayment (B0 A i : ℝ) (n : ℕ) :
    balance B0 (fun m ↦ A - levelPaymentBalance B0 A i (m - 1) * i) n =
      levelPaymentBalance B0 A i n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [balance, levelPaymentBalance, ih, Nat.add_sub_cancel]
    ring

/-- One period of an annuity: carrying the value of `m + 1` payments forward one
period and paying the first leaves the value of the other `m`,
`A_{m+1}·e^{rΔt} - A = A_m`. -/
theorem annuityValue_succ_mul_exp_sub (m : ℕ) (A r Δt : ℝ) :
    annuityValue (m + 1) A r Δt * Real.exp (r * Δt) - A = annuityValue m A r Δt := by
  rw [annuityValue, annuityValue, Finset.sum_range_succ', add_mul, Finset.sum_mul,
    mul_assoc A, ← Real.exp_add]
  simp only [Nat.cast_zero, zero_add, one_mul, neg_add_cancel, Real.exp_zero, mul_one,
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- **Level-payment schedule against `annuityValue`.** A loan whose principal
`B₀` is the value `annuityValue N A r Δt` of `N` level payments `A`, at period
rate `i = e^{rΔt} - 1`, has outstanding balance after `n ≤ N` payments equal to
the value of the `N - n` payments still to come. -/
theorem levelPaymentBalance_eq_annuityValue {B0 A r Δt : ℝ} {N : ℕ}
    (hB0 : annuityValue N A r Δt = B0) {n : ℕ} (hn : n ≤ N) :
    levelPaymentBalance B0 A (Real.exp (r * Δt) - 1) n = annuityValue (N - n) A r Δt := by
  induction n with
  | zero => exact hB0.symm
  | succ k ih =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hn
    rw [levelPaymentBalance, ih (Nat.le_of_succ_le hn), add_sub_cancel,
      show N - k = m + 1 by omega, show N - (k + 1) = m by omega,
      annuityValue_succ_mul_exp_sub]

/-- **A level-payment loan is paid off at maturity**: with `B₀` the value of the
`N` payments, the balance after the `N`-th is zero. -/
theorem levelPaymentBalance_eq_zero {B0 A r Δt : ℝ} {N : ℕ}
    (hB0 : annuityValue N A r Δt = B0) :
    levelPaymentBalance B0 A (Real.exp (r * Δt) - 1) N = 0 := by
  rw [levelPaymentBalance_eq_annuityValue hB0 le_rfl, Nat.sub_self, annuityValue,
    Finset.sum_range_zero]

end MathFin
