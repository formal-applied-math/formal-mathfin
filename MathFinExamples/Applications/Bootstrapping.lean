/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin

/-!
# Using the library: bootstrapping a discount curve and repricing the inputs

A worked use of the library from outside it, the way a rates desk builds a discount curve from
quoted par bonds. A strip of annual par bonds is quoted, one per maturity. This file

1. records the strip as data, with where it comes from and what the curve leaves out;
2. solves the discount factors one maturity at a time, each from the bond maturing there and the
   factors already solved (`df`);
3. proves the curve reprices every bond in the strip exactly (`df_reprices`, from
   `bootstrap_consistency`), and that it is the only curve that does (`eq_df`, from
   `bootstrap_solve`; both are `parBootstrap_reprices` and `parBootstrap_unique` of
   `Models/Rates/YieldCurve.lean`, applied to the strip's coupons);
4. computes the curve for an illustrative strip and checks that its first three discount factors
   are below `1` and strictly decreasing, so that the one-year forward rates between them, which
   this file does not define, would be positive, and that every later factor is the previous one
   over `1.03` (`parBootstrap_succ_of_coupon_eq`), which determines the whole curve.

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

@[expose] public section

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

/-- **The bootstrapped discount factor** to year `n + 1`: the bond maturing then is priced at par
by its coupons, discounted on the factors already solved, and its final payment `1 + c`
(`parBootstrap`). -/
noncomputable def df (s : ParStrip) : ℕ → ℝ := parBootstrap s.coupon

/-- The price of the bond with index `n` on a curve `B`, as a pricing equation: par equals the
coupons discounted to years `1, …, n` plus the final payment discounted to year `n + 1`. -/
def PricesAtPar (s : ParStrip) (B : ℕ → ℝ) (n : ℕ) : Prop :=
  parBondPricingEq s.coupon B n

/-- **The curve reprices every bond in the strip exactly** (`parBootstrap_reprices`). -/
theorem df_reprices (s : ParStrip) (n : ℕ) : s.PricesAtPar s.df n :=
  parBootstrap_reprices s.coupon (fun n ↦ by linarith [s.coupon_pos n]) n

/-- **The curve is the only one that reprices the strip** (`parBootstrap_unique`). -/
theorem eq_df (s : ParStrip) {B : ℕ → ℝ} (hB : ∀ n, s.PricesAtPar B n) (n : ℕ) : B n = s.df n :=
  parBootstrap_unique s.coupon (fun n ↦ by linarith [s.coupon_pos n]) hB n

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
  norm_num [ParStrip.df, parBootstrap, parAnnuity, sample]

/-- **The rest of the curve**: from the fourth year on the coupon is the same `3%`, so each factor
is the previous one over `1.03`. With `sample_df` this fixes the whole curve. -/
theorem sample_df_tail (n : ℕ) (hn : 2 ≤ n) : sample.df (n + 1) = sample.df n / 1.03 := by
  have hc (m : ℕ) (hm : 2 ≤ m) : sample.coupon m = 0.03 := by
    simp [sample, show m ≠ 0 by omega, show m ≠ 1 by omega]
  have := parBootstrap_succ_of_coupon_eq sample.coupon (n := n)
    (by rw [hc n hn]; norm_num) (by rw [hc n hn, hc (n + 1) (by omega)])
  rw [hc n hn] at this
  rw [show (1 : ℝ) + 0.03 = 1.03 by norm_num] at this
  exact this

/-! ### The check -/

/-- **The curve check for `sample`**, the statement this file's build certifies:
- the bootstrapped curve reprices every bond in the strip at par;
- it is the only curve that does;
- its first three discount factors are `50/51`, `1990/2091` and `65660/71791`;
- they are positive, below `1` and strictly decreasing;
- every later factor is the previous one over `1.03`. -/
theorem sample_checked :
    (∀ n, sample.PricesAtPar sample.df n) ∧
      (∀ B : ℕ → ℝ, (∀ n, sample.PricesAtPar B n) → B = sample.df) ∧
      (sample.df 0 = 50 / 51 ∧ sample.df 1 = 1990 / 2091 ∧ sample.df 2 = 65660 / 71791) ∧
      0 < sample.df 2 ∧ sample.df 2 < sample.df 1 ∧ sample.df 1 < sample.df 0 ∧
      sample.df 0 < 1 ∧ ∀ n, 2 ≤ n → sample.df (n + 1) = sample.df n / 1.03 := by
  obtain ⟨h₀, h₁, h₂⟩ := sample_df
  refine ⟨sample.df_reprices, fun B hB ↦ funext (sample.eq_df hB), sample_df, ?_, sample_df_tail⟩
  rw [h₀, h₁, h₂]
  norm_num

end MathFin.Examples.Bootstrapping
