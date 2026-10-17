/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Fisher/Sraffa own-rate-of-interest identity

The **own rate of interest** `r` of a commodity relates its **basis** (the
convenience-adjusted real return) `b` and the inflation rate `i` through
Fisher's exact identity

  `1 + r = (1 + b)(1 + i)`,

and **Sraffa's implied own rate** recovers `b` from a spot price `S`,
forward price `F`, financing rate `m` and maturity `T`:

  `b = ((1 + m)^T · S / F)^{1/T} − 1`.

Expanding the Fisher identity gives the familiar linear approximation
`r ≈ b + i`; its error term is exactly `b · i` — the identity is an exact
equality for real numbers, so the "approximation" enters only when `b · i`
is treated as second-order-small and dropped.

## Main results

* `fisherOwnRate`: `r` defined as `(1+b)(1+i) − 1`.
* `fisher_identity`: `1 + fisherOwnRate b i = (1+b)*(1+i)`.
* `fisher_linear_approx_error`: `fisherOwnRate b i − (b + i) = b * i`, the
  exact statement underlying `r ≈ b + i` for small `b, i`.
* `sraffaOwnRate`: Sraffa's implied own rate from spot/forward/financing/time.
* `sraffaOwnRate_spec`: `(1 + sraffaOwnRate m S F T)^T = (1+m)^T · S / F`,
  the defining equation Sraffa's formula inverts.
-/

@[expose] public section

namespace MathFin

/-! ### Fisher's exact identity -/

/-- **Fisher own rate of interest**: `r = (1+b)(1+i) − 1`, exactly solving
`1 + r = (1+b)(1+i)` for the real own-rate `r` given commodity basis `b` and
inflation rate `i`. -/
noncomputable def fisherOwnRate (b i : ℝ) : ℝ := (1 + b) * (1 + i) - 1

/-- **Fisher's exact identity**: `1 + r = (1+b)(1+i)`. -/
theorem fisher_identity (b i : ℝ) :
    1 + fisherOwnRate b i = (1 + b) * (1 + i) := by
  unfold fisherOwnRate; ring

/-- **Linear approximation error**: `r − (b+i) = b·i` exactly. The usual
first-order approximation `r ≈ b + i` drops this cross term, which is
genuinely second-order small when `b, i` are both small. -/
theorem fisher_linear_approx_error (b i : ℝ) :
    fisherOwnRate b i - (b + i) = b * i := by
  unfold fisherOwnRate; ring

/-! ### Sraffa's implied own rate -/

/-- **Sraffa's implied own rate**: `b = ((1+m)^T · S/F)^{1/T} − 1`, recovered
from the financing rate `m`, spot price `S`, forward price `F` and maturity
`T` via the cost-of-carry relation `F = S·(1+m)^T / (1+b)^T`. -/
noncomputable def sraffaOwnRate (m S F T : ℝ) : ℝ :=
  ((1 + m) ^ T * (S / F)) ^ (1 / T) - 1

/-- **Sraffa's defining equation**: `(1 + b)^T = (1+m)^T · S/F`, where
`b = sraffaOwnRate m S F T`. Requires `(1+m)^T · S/F ≥ 0` (holds e.g. for
`m ≥ -1`, `S, F > 0`) and `T ≠ 0` so the `1/T`-th root inverts the `T`-th
power. -/
theorem sraffaOwnRate_spec (m S F T : ℝ) (hT : T ≠ 0)
    (hpos : 0 ≤ (1 + m) ^ T * (S / F)) :
    (1 + sraffaOwnRate m S F T) ^ T = (1 + m) ^ T * (S / F) := by
  unfold sraffaOwnRate
  have h1 : 1 + (((1 + m) ^ T * (S / F)) ^ (1 / T) - 1)
      = ((1 + m) ^ T * (S / F)) ^ (1 / T) := by ring
  rw [h1, ← Real.rpow_mul hpos, one_div, inv_mul_cancel₀ hT, Real.rpow_one]

end MathFin
