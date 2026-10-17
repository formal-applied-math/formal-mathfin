/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.MacaulayModified

/-!
# Clean price and accrued interest, on- and between-coupon dates

A coupon bond's quoted **clean price** omits the interest that has accrued
since the last coupon date; the **dirty (invoiced) price** is what actually
changes hands. Writing `f ∈ [0, 1)` for the fraction of the current coupon
period elapsed since the last coupon date, the street-convention dirty price
is the flat-compounded present value of the remaining cashflows, carried
forward by `f` periods:

  `Dirty(y, f) = (1 + y)^f · Σ c_i / (1 + y)^{t_i}`     (`bondPriceDisc` from
  `MacaulayModified`, with `t_i` the number of *whole periods remaining* to
  each cashflow from the next coupon date),

and accrued interest on the next coupon `c₁` is the simple-interest share of
that coupon already earned,

  `Accrued(f) = f · c₁`,

with **clean price** `Clean(y, f) = Dirty(y, f) - Accrued(f)`. On a coupon
date (`f = 0`) this collapses to the ordinary `bondPriceDisc` with zero
accrued interest — the two pricing conventions agree exactly where they must.

## Result

* `dirtyPrice`, `accruedInterest`, `cleanPrice` — the three quantities.
* `cleanPrice_eq_dirty_sub_accrued`: `Clean = Dirty - Accrued` by definition.
* `dirtyPrice_on_coupon_date`: `Dirty(y, 0) = bondPriceDisc s t c y`.
* `accruedInterest_on_coupon_date`: `Accrued(0) = 0`.
* `cleanPrice_eq_dirty_on_coupon_date`: on a coupon date, clean = dirty.
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- Dirty price between coupon dates: the flat-compounded present value of
remaining cashflows, carried forward by the elapsed fraction `f` of the
current period. -/
noncomputable def dirtyPrice (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y f : ℝ) : ℝ :=
  (1 + y) ^ f * bondPriceDisc s t c y

/-- Accrued interest on the next coupon `c1`, as a simple-interest share of
the elapsed fraction `f` of the current period. -/
def accruedInterest (c1 f : ℝ) : ℝ := f * c1

/-- Clean (quoted) price: dirty price minus accrued interest. -/
noncomputable def cleanPrice (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y f c1 : ℝ) : ℝ :=
  dirtyPrice s t c y f - accruedInterest c1 f

/-- Clean price is dirty price minus accrued interest, by construction. -/
theorem cleanPrice_eq_dirty_sub_accrued (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y f c1 : ℝ) :
    cleanPrice s t c y f c1 = dirtyPrice s t c y f - accruedInterest c1 f := rfl

/-- On a coupon date (`f = 0`), the dirty price collapses to the ordinary
discrete-compounding bond price. -/
theorem dirtyPrice_on_coupon_date (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) :
    dirtyPrice s t c y 0 = bondPriceDisc s t c y := by
  unfold dirtyPrice
  rw [Real.rpow_zero, one_mul]

/-- On a coupon date, no interest has accrued. -/
theorem accruedInterest_on_coupon_date (c1 : ℝ) : accruedInterest c1 0 = 0 := by
  unfold accruedInterest; ring

/-- On a coupon date, clean price equals dirty price (equivalently, equals
the ordinary `bondPriceDisc`): the two conventions agree exactly on coupon
dates, where there is nothing left to accrue. -/
theorem cleanPrice_eq_dirty_on_coupon_date (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y c1 : ℝ) :
    cleanPrice s t c y 0 c1 = bondPriceDisc s t c y := by
  rw [cleanPrice_eq_dirty_sub_accrued, dirtyPrice_on_coupon_date,
    accruedInterest_on_coupon_date, sub_zero]

end MathFin
