/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Relative drawdown is scale invariant

The **relative drawdown** of an equity curve `E` at time `t` is the fraction of the running
peak lost, `1 − E t / max_{s ≤ t} E s`. The running peak is Mathlib's `partialSups E`.

`MathFin.maximumDrawdown` (`Performance/DownsideMetrics.lean`) measures the largest
*absolute* decline, and is positively homogeneous: scaling the curve by `c > 0` scales it by
`c` (`maximumDrawdown_scale`). The relative drawdown is instead *invariant* under
`E ↦ c E`: a fund ten times the size, run with the same strategy, has the same relative
drawdown at every date. This is why relative drawdown, not absolute drawdown, compares
portfolios of different sizes, or denominated in different currencies at a fixed conversion
rate.

The invariance holds for every equity curve, with no positivity hypothesis on `E`: Lean's
`x / 0 = 0` convention makes both sides `1` at a zero peak.

## Main results

* `partialSups_const_mul`: the running peak of `c E` is `c` times the running peak of `E`,
  for `c > 0` (multiplication by `c` is an order isomorphism, so it commutes with `⊔`).
* `relativeDrawdown_const_mul`: the relative drawdown of `c E` equals that of `E`.
* `maxRelativeDrawdown_const_mul`: hence so does the maximum relative drawdown up to any time.
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]

/-- Relative drawdown `1 − E t / max_{s ≤ t} E s` of an equity curve `E` at time `t`: the
fraction of the running peak lost by time `t`. -/
noncomputable def relativeDrawdown (E : ι → ℝ) (t : ι) : ℝ := 1 - E t / partialSups E t

/-- Maximum relative drawdown up to time `t`: the largest relative drawdown at any `s ≤ t`. -/
noncomputable def maxRelativeDrawdown (E : ι → ℝ) (t : ι) : ℝ :=
  partialSups (relativeDrawdown E) t

/-- The running peak is positively homogeneous: multiplication by `c > 0` is an order
isomorphism of `ℝ`, so it commutes with the finite suprema defining `partialSups`. -/
theorem partialSups_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) (t : ι) :
    partialSups (fun s ↦ c * E s) t = c * partialSups E t :=
  map_partialSups (OrderIso.mulLeft₀ c hc) E t

/-- **Relative drawdown is scale invariant**: scaling the equity curve by `c > 0` leaves the
relative drawdown unchanged at every time — unlike the absolute `maximumDrawdown`, which
scales by `c`. -/
theorem relativeDrawdown_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) :
    relativeDrawdown (fun s ↦ c * E s) = relativeDrawdown E := by
  funext t
  simp only [relativeDrawdown, partialSups_const_mul hc, mul_div_mul_left _ _ hc.ne']

/-- The maximum relative drawdown up to any time is scale invariant. -/
theorem maxRelativeDrawdown_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) :
    maxRelativeDrawdown (fun s ↦ c * E s) = maxRelativeDrawdown E := by
  unfold maxRelativeDrawdown
  rw [relativeDrawdown_const_mul hc]

end MathFin
