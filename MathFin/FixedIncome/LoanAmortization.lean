/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Loan amortization schedules: bullet and equal-principal recurrences

Both schedules share the same per-period interest accrual on the outstanding
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

Both closed forms are proved here by induction on the balance recurrence,
matching the standard amortization-table identities.

## Result

* `bulletPrincipal`, `equalPrincipalPayment` — the two principal-payment
  schedules.
* `balance` — the shared balance recurrence `B_n = B_{n-1} - P_n` (as a fold).
* `interestAccrued` — `I_n = B_{n-1} · i`, independent of the schedule.
* `balance_bullet_lt`, `balance_bullet_eq` — the bullet closed form.
* `balance_equalPrincipal` — the equal-principal closed form
  `B_n = B_0 · (1 - n / N)`.
-/

@[expose] public section

namespace MathFin

/-- The outstanding balance after `n` periods, given an initial balance `B₀`
and a principal-payment schedule `P : ℕ → ℝ` (period `k`'s payment is `P k`
for `k = 1, …, n`). Defined by the shared recurrence `B_n = B_{n-1} - P_n`. -/
def balance (B0 : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => B0
  | n + 1 => balance B0 P n - P (n + 1)

/-- Interest accrued in period `n` is the prior balance times the period
rate: `I_n = B_{n-1} · i`. Shared by every amortization schedule. -/
def interestAccrued (B0 : ℝ) (P : ℕ → ℝ) (i : ℝ) (n : ℕ) : ℝ :=
  balance B0 P (n - 1) * i

/-- The bullet schedule: no principal is repaid before maturity `N`, and the
entire balance is repaid in period `N`. -/
def bulletPrincipal (B0 : ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n ↦ if n = N then B0 else 0

/-- Under the bullet schedule, the balance is unchanged before maturity. -/
theorem balance_bullet_lt {B0 : ℝ} {N n : ℕ} (hn : n < N) :
    balance B0 (bulletPrincipal B0 N) n = B0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hk : k < N := Nat.lt_of_succ_lt hn
    simp only [balance, bulletPrincipal, ih hk, if_neg hn.ne, sub_zero]

/-- Under the bullet schedule, the balance is exactly zero at maturity
(assuming it was unpaid up to `N - 1`, i.e. `N ≥ 1`). -/
theorem balance_bullet_eq {B0 : ℝ} {N : ℕ} (hN : 0 < N) :
    balance B0 (bulletPrincipal B0 N) N = 0 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hprev : balance B0 (bulletPrincipal B0 (M + 1)) M = B0 :=
    balance_bullet_lt (Nat.lt_succ_self M)
  simp only [balance, bulletPrincipal, hprev]
  norm_num

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

end MathFin
