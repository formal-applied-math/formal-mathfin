/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Yield curve bootstrapping

Standard practitioner method to extract zero-coupon bond (ZCB) prices from a
sequence of coupon-bond prices at successive maturities.

Given a coupon bond paying coupon `c i` at time `T_i` for `i ∈ sprev` (the
earlier maturities) plus `c_last + F` at the new (longest) maturity `T_n`,
with observed price `P`, the new ZCB price `B_last` satisfies:

  `P = (∑_{i ∈ sprev} c i · B i) + (c_last + F) · B_last`,

so

  `B_last = (P − ∑_{i ∈ sprev} c i · B i) / (c_last + F)`,

provided `c_last + F ≠ 0`.

Applied recursively, starting from a single-period bond (where `sprev = ∅` and
`B_last = P / (c_last + F)`), this identity is how the discount curve is bootstrapped
from coupon-bond market data. For a strip of annual par bonds the recursion is closed-form
(`parBootstrap`): it reprices every bond and is the only curve that does, and a repeated coupon
makes the next factor the previous one over `1 + c` (`parBootstrap_succ_of_coupon_eq`). The
search-based recursion over general instruments is `boot` of
`Models/Rates/Bootstrapping.lean`, where
`swapBootstrap_recovers_couponBondFactor` shows that bisection on a zero-value swap
recovers the factor named by `bootstrap_solve`.

## Main definitions

* `couponBondPricingEq`: the proposition `P = (∑ i ∈ sprev, c i * B i) + (c_last + F) * B_last`,
  the price of a coupon bond with previously known maturities `sprev` and one new maturity.
* `parAnnuity`, `parBootstrap`: for annual par bonds with coupons `c n` maturing in year `n + 1`,
  the sum of the solved factors and the factor to year `n + 1` solved from the bond maturing then.
* `parBondPricingEq`: the bond with index `n` is priced at par on a curve `B`.

## Main results

* `bootstrap_solve`: from the pricing equation, recovers `B_last` as a
  closed-form ratio.
* `bootstrap_solve_first`: bootstrap base case for the first bond with empty
  previous schedule: `B_1 = P_1 / (c_1 + F)`.
* `bootstrap_solve_second`: bootstrap step for the second bond:
  `B_2 = (P_2 − c · B_1) / (c + F)`.
* `bootstrap_consistency`: the bootstrapped price, plugged back into the pricing
  equation, recovers the bond price.
* `parBootstrap_reprices`, `parBootstrap_unique`: the bootstrapped curve prices every par bond
  of the strip at par, and a curve that does so is that curve.
* `parBootstrap_succ_of_coupon_eq`: a coupon repeated in the next year gives
  `B (n + 1) = B n / (1 + c n)`.

## References

* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], Ch 9
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 4.6

## Tags

bootstrapping, zero-coupon bond, coupon bond, discount curve, yield curve construction, JEL E43,
MSC 91G30
-/

@[expose] public section

namespace MathFin

/-- Coupon-bond pricing equation expressed in terms of previously-known ZCB
prices `B : ι → ℝ` and the new ZCB `B_last`. -/
def couponBondPricingEq {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F B_last : ℝ) : Prop :=
  P = (∑ i ∈ sprev, c i * B i) + (c_last + F) * B_last

/-- **Bootstrap solve identity**: from the coupon-bond pricing equation, the
new ZCB price `B_last` is recovered as a closed-form ratio. -/
lemma bootstrap_solve {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F B_last : ℝ) (h : c_last + F ≠ 0)
    (hP : couponBondPricingEq sprev c B P c_last F B_last) :
    B_last = (P - ∑ i ∈ sprev, c i * B i) / (c_last + F) := by
  unfold couponBondPricingEq at hP
  field_simp
  linarith

/-- **First-bond bootstrap** (empty previous schedule): a single-period coupon
bond with cash flow `c_last + F` at maturity gives `B_last = P / (c_last + F)`. -/
lemma bootstrap_solve_first (P c_last F B_last : ℝ) (h : c_last + F ≠ 0)
    (hP : P = (c_last + F) * B_last) :
    B_last = P / (c_last + F) := by
  rw [hP]
  field_simp

/-- **Second-bond bootstrap step**: with one previous ZCB price `B_1` and a
two-period bond paying coupon `c` at both dates plus face `F` at the second,
`B_2 = (P − c · B_1) / (c + F)`. -/
lemma bootstrap_solve_second (P c F B_1 B_2 : ℝ) (h : c + F ≠ 0)
    (hP : P = c * B_1 + (c + F) * B_2) :
    B_2 = (P - c * B_1) / (c + F) := by
  rw [hP]
  field_simp
  ring

/-- **Recursive consistency**: the bootstrapped ZCB price, plugged back into
the pricing equation, recovers the original bond price. -/
lemma bootstrap_consistency {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F : ℝ) (h : c_last + F ≠ 0) :
    couponBondPricingEq sprev c B P c_last F
      ((P - ∑ i ∈ sprev, c i * B i) / (c_last + F)) := by
  unfold couponBondPricingEq
  field_simp
  ring

/-- The sum of the discount factors to years `1, …, n` of the par strip with coupons `c`, built
with the curve: each step adds the factor the next bond solves for. -/
noncomputable def parAnnuity (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => parAnnuity c n + (1 - c n * parAnnuity c n) / (1 + c n)

/-- **The bootstrapped discount factor** to year `n + 1` of the par strip with coupons `c`: the
bond maturing then, paying `c n` each year and `1 + c n` at the end, is priced at par on the
factors already solved. -/
noncomputable def parBootstrap (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - c n * parAnnuity c n) / (1 + c n)

/-- The bond with index `n` of the par strip with coupons `c`, on the curve `B`, is priced at par:
`1` equals its coupons discounted to years `1, …, n` plus its final payment `1 + c n` discounted
to year `n + 1` (`couponBondPricingEq`). -/
def parBondPricingEq (c B : ℕ → ℝ) (n : ℕ) : Prop :=
  couponBondPricingEq (Finset.range n) (fun _ ↦ c n) B 1 (c n) 1 (B n)

/-- The recursion for `parAnnuity` sums the bootstrapped discount factors. -/
theorem parAnnuity_eq_sum (c : ℕ → ℝ) (n : ℕ) :
    parAnnuity c n = ∑ k ∈ Finset.range n, parBootstrap c k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [parAnnuity, Finset.sum_range_succ, ← ih, parBootstrap]

/-- **The bootstrapped curve reprices every bond of the par strip** (`bootstrap_consistency`). -/
theorem parBootstrap_reprices (c : ℕ → ℝ) (hc : ∀ n, 1 + c n ≠ 0) (n : ℕ) :
    parBondPricingEq c (parBootstrap c) n := by
  have h := bootstrap_consistency (Finset.range n) (fun _ ↦ c n) (parBootstrap c) 1 (c n) 1
    (by rw [add_comm]; exact hc n)
  rwa [← Finset.mul_sum, ← parAnnuity_eq_sum, add_comm (c n) 1, ← parBootstrap] at h

/-- **The bootstrapped curve is the only one that reprices the par strip.** A curve on which every
bond is priced at par is the bootstrapped one: by induction on the maturity, each pricing equation
determines the next factor from the earlier ones (`bootstrap_solve`). -/
theorem parBootstrap_unique (c : ℕ → ℝ) (hc : ∀ n, 1 + c n ≠ 0) {B : ℕ → ℝ}
    (hB : ∀ n, parBondPricingEq c B n) (n : ℕ) : B n = parBootstrap c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [bootstrap_solve _ _ _ _ _ _ _ (by rw [add_comm]; exact hc n) (hB n), ← Finset.mul_sum,
      Finset.sum_congr rfl fun k hk ↦ ih k (Finset.mem_range.1 hk), ← parAnnuity_eq_sum,
      add_comm (c n) 1, parBootstrap]

/-- **A repeated coupon makes the curve geometric**: if the bond maturing in year `n + 2` pays the
coupon of the one maturing in year `n + 1`, the factor to year `n + 2` is the factor to year
`n + 1` over `1 + c n`. -/
theorem parBootstrap_succ_of_coupon_eq (c : ℕ → ℝ) {n : ℕ} (hn : 1 + c n ≠ 0)
    (h : c (n + 1) = c n) : parBootstrap c (n + 1) = parBootstrap c n / (1 + c n) := by
  rw [parBootstrap, parBootstrap, parAnnuity, h]
  field_simp
  ring

end MathFin
