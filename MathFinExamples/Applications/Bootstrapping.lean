/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: bootstrapping a discount curve and repricing the inputs

A worked use of the library from outside it, the way a rates desk builds a discount curve from
quoted par bonds. A strip of annual par bonds is quoted, one per maturity. This file

1. records the strip as data, with where it comes from and what the curve leaves out;
2. solves the discount factors one maturity at a time, each from the bond maturing there and the
   factors already solved (`df`);
3. proves the curve reprices every bond in the strip exactly (`df_reprices`, from
   `bootstrap_consistency`), and that it is the only curve that does (`eq_df`, from
   `bootstrap_solve`);
4. computes the curve for an illustrative strip and checks that its first three discount factors
   are below `1` and strictly decreasing, so that the one-year forward rates between them, which
   this file does not define, would be positive.

`sample_checked` is the single statement the build certifies.

## What the library supplies

* `MathFin.couponBondPricingEq`: a coupon bond's price as the sum of its discounted cash flows.
* `MathFin.bootstrap_consistency`: the solved discount factor reprices the bond.
* `MathFin.bootstrap_solve`: the pricing equation determines the new discount factor.

## What it does not

The bonds pay annual coupons on a face of `1`, are quoted at par and mature on consecutive years,
so each maturity has exactly one instrument and no interpolation is needed. Day counts, settlement
lags, accrued interest and the credit of the issuer are outside the model.

## Source

The shape of the file follows the capped-call example
(`MathFinExamples/Applications/CappedCall.lean`). The coupons below are illustrative.
-/

namespace MathFin.Examples.Bootstrapping

/-! ### The strip, as data -/

/-- A strip of annual par bonds on a face of `1`: the bond with index `n` matures in year `n + 1`,
pays the coupon `coupon n` every year until then, and is quoted at par, a price of `1`. -/
structure ParStrip where
  /-- The annual coupon of the bond maturing in year `n + 1`. -/
  coupon : ℕ → ℝ
  coupon_pos : ∀ n, 0 < coupon n
  /-- Where the coupons come from. -/
  sources : List String
  /-- What the curve does not model. -/
  unmodelled : List String

namespace ParStrip

/-- The sum of the discount factors to years `1, …, n`, built with the curve: each step adds the
factor the next bond solves for. -/
noncomputable def annuity (s : ParStrip) : ℕ → ℝ
  | 0 => 0
  | n + 1 => s.annuity n + (1 - s.coupon n * s.annuity n) / (1 + s.coupon n)

/-- **The bootstrapped discount factor** to year `n + 1`: the bond maturing then is priced at par
by its coupons, discounted on the factors already solved, and its final payment `1 + c`. -/
noncomputable def df (s : ParStrip) (n : ℕ) : ℝ :=
  (1 - s.coupon n * s.annuity n) / (1 + s.coupon n)

/-- The recursion for `annuity` sums the bootstrapped discount factors. -/
theorem annuity_eq_sum (s : ParStrip) (n : ℕ) : s.annuity n = ∑ k ∈ Finset.range n, s.df k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [annuity, Finset.sum_range_succ, ← ih, df]

/-- The price of the bond with index `n` on a curve `B`, as a pricing equation: par equals the
coupons discounted to years `1, …, n` plus the final payment discounted to year `n + 1`. -/
def PricesAtPar (s : ParStrip) (B : ℕ → ℝ) (n : ℕ) : Prop :=
  couponBondPricingEq (Finset.range n) (fun _ ↦ s.coupon n) B 1 (s.coupon n) 1 (B n)

/-- **The curve reprices every bond in the strip exactly** (`bootstrap_consistency`). -/
theorem df_reprices (s : ParStrip) (n : ℕ) : s.PricesAtPar s.df n := by
  have h := bootstrap_consistency (Finset.range n) (fun _ ↦ s.coupon n) s.df 1 (s.coupon n) 1
    (by linarith [s.coupon_pos n])
  rwa [← Finset.mul_sum, ← annuity_eq_sum, add_comm (s.coupon n) 1, ← df] at h

/-- **The curve is the only one that reprices the strip.** A curve on which every bond is priced
at par is the bootstrapped one: by induction on the maturity, each pricing equation determines
the next factor from the earlier ones (`bootstrap_solve`). -/
theorem eq_df (s : ParStrip) {B : ℕ → ℝ} (hB : ∀ n, s.PricesAtPar B n) (n : ℕ) : B n = s.df n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [bootstrap_solve _ _ _ _ _ _ _ (by linarith [s.coupon_pos n]) (hB n), ← Finset.mul_sum,
      Finset.sum_congr rfl fun k hk ↦ ih k (Finset.mem_range.1 hk), ← annuity_eq_sum,
      add_comm (s.coupon n) 1, df]

end ParStrip

/-- An illustrative strip: par bonds maturing in one, two and three years with coupons `2%`,
`2.5%` and `3%`, and `3%` for every later year. -/
noncomputable def sample : ParStrip where
  coupon n := if n = 0 then 0.02 else if n = 1 then 0.025 else 0.03
  coupon_pos n := by split_ifs <;> norm_num
  sources := ["illustrative par coupons for one-, two- and three-year bonds"]
  unmodelled :=
    ["day counts and settlement lags", "accrued interest", "the issuer's credit",
      "maturities between the annual dates"]

/-- The sample curve to three years: `50/51`, `0.951…` and `0.914…`. -/
theorem sample_df :
    sample.df 0 = 50 / 51 ∧ sample.df 1 = 1990 / 2091 ∧ sample.df 2 = 65660 / 71791 := by
  norm_num [ParStrip.df, ParStrip.annuity, sample]

/-! ### The check -/

/-- **The curve check for `sample`**, the statement this file's build certifies:
- the bootstrapped curve reprices every bond in the strip at par;
- it is the only curve that does;
- its first three discount factors are `50/51`, `1990/2091` and `65660/71791`;
- they are positive, below `1` and strictly decreasing. -/
theorem sample_checked :
    (∀ n, sample.PricesAtPar sample.df n) ∧
      (∀ B : ℕ → ℝ, (∀ n, sample.PricesAtPar B n) → B = sample.df) ∧
      (sample.df 0 = 50 / 51 ∧ sample.df 1 = 1990 / 2091 ∧ sample.df 2 = 65660 / 71791) ∧
      0 < sample.df 2 ∧ sample.df 2 < sample.df 1 ∧ sample.df 1 < sample.df 0 ∧
      sample.df 0 < 1 := by
  obtain ⟨h₀, h₁, h₂⟩ := sample_df
  refine ⟨sample.df_reprices, fun B hB ↦ funext (sample.eq_df hB), sample_df, ?_⟩
  rw [h₀, h₁, h₂]
  norm_num

end MathFin.Examples.Bootstrapping
