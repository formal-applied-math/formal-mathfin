/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Solutions to the exercises in `docs/beginners-manual.md`

Each `example` below is one exercise of the manual, with a solution. The build checks them, so the
manual's exercises keep working as the library changes. Try them yourself before reading on.
-/

open MathFin

/-! ### Exercise 1: a tree with no arbitrage -/

example : BinomialNoArb 2 (1 / 2) 0 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### Exercise 2: its risk-neutral probability lies in `(0, 1)` -/

example : crrUpProb 2 (1 / 2) 0 ∈ Set.Ioo 0 1 :=
  crrUpProb_mem_Ioo ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### Exercise 3: and equals `1/3` -/

example : crrUpProb 2 (1 / 2) 0 = 1 / 3 := by
  norm_num [crrUpProb]

/-! ### Exercise 4: a call option in that tree -/

/-- Spot `1`, strike `1`: the call pays `1` after an up move and `0` after a down move. -/
example : binomialOptionPriceOnePeriod 2 (1 / 2) 0 (max (2 - 1) 0) (max (1 / 2 - 1) 0) = 1 / 3 := by
  norm_num [binomialOptionPriceOnePeriod, crrUpProb]

/-! ### Exercise 5: a riskless payoff is discounted, with or without no-arbitrage -/

example (u d r c : ℝ) : binomialOptionPriceOnePeriod u d r c c = Real.exp (-r) * c := by
  unfold binomialOptionPriceOnePeriod
  ring

/-! ### Exercise 6: what `crrUpProb` returns when the tree is degenerate -/

example (u r : ℝ) : crrUpProb u u r = 0 := by
  simp [crrUpProb]
