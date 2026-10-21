/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Fractional-differentiation weight recursion

López de Prado (*Advances in Financial Machine Learning*, ch. 5) builds the
fractionally-differenced series `(1-B)^d X` from a weight sequence computed by
the recursion `w_0 = 1`, `w_k = -w_{k-1}·(d-k+1)/k`, the binomial-series
coefficients of `(1-B)^d` for real exponent `d` (the series and the
differenced series are not formalized here).

This file states the recursion as `fracDiffWeight` and proves it agrees with
the closed-form alternating product `(-1)^k · ∏_{i<k} (d-i)/(i+1)` — the
real-exponent generalized binomial coefficient `(-1)^k · C(d,k)` by its
textbook definition (no identification with a Mathlib binomial coefficient is
proved) — by induction directly on the recursion. It also records the
elementary per-step magnitude ratio relating consecutive weights. The ratio
`|d-k|/(k+1)` tends to `1`; that the weights nevertheless tend to `0` for
`d > -1` is not proved here, and no decay statement is.

## Main results

* `fracDiffWeight_eq_prod`: `fracDiffWeight d k = (-1)^k * ∏ i ∈ range k, (d-i)/(i+1)`.
* `abs_fracDiffWeight_succ`: `|fracDiffWeight d (k+1)| = |fracDiffWeight d k| * |d-k| / (k+1)`,
  the per-step magnitude ratio between consecutive weights.
-/

@[expose] public section

namespace MathFin

/-- The fractional-differentiation weight recursion: `w_0 = 1`,
`w_{k+1} = -w_k · (d-k)/(k+1)` (i.e. `w_k = -w_{k-1}·(d-k+1)/k` for `k ≥ 1`). -/
noncomputable def fracDiffWeight (d : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => -fracDiffWeight d k * (d - k) / (k + 1)

@[simp] theorem fracDiffWeight_zero (d : ℝ) : fracDiffWeight d 0 = 1 := rfl

theorem fracDiffWeight_succ (d : ℝ) (k : ℕ) :
    fracDiffWeight d (k + 1) = -fracDiffWeight d k * (d - k) / (k + 1) := rfl

/-- Closed form: `w_k` is the alternating product `(-1)^k · ∏_{i<k} (d-i)/(i+1)`,
the real-exponent binomial coefficient `(-1)^k · C(d,k)`. -/
theorem fracDiffWeight_eq_prod (d : ℝ) (k : ℕ) :
    fracDiffWeight d k = (-1) ^ k * ∏ i ∈ Finset.range k, (d - i) / (i + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [fracDiffWeight_succ, ih, Finset.prod_range_succ]
    ring

/-- Per-step magnitude ratio: `|w_{k+1}| = |w_k| · |d-k| / (k+1)`. -/
theorem abs_fracDiffWeight_succ (d : ℝ) (k : ℕ) :
    |fracDiffWeight d (k + 1)| = |fracDiffWeight d k| * |d - k| / (k + 1) := by
  rw [fracDiffWeight_succ, abs_div, abs_mul, abs_neg,
    abs_of_pos (show (0 : ℝ) < (k : ℝ) + 1 by positivity)]

end MathFin
