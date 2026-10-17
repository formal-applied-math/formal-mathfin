/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# FX forward via covered interest parity, and the implied forward curve

**Covered interest parity (CIP)**: with continuously-compounded domestic and
foreign rates `r_d`, `r_f` and spot `S` (domestic per unit of foreign), the
no-arbitrage forward rate for maturity `T` is

  `F(0, T) = S · exp((r_d - r_f) · T)`.

This is distinct from the already-tracked Garman–Kohlhagen *spot* option
formula (`MathFin/BlackScholes/QuantoGrounding.lean`): CIP prices the forward
*contract itself* via cash-and-carry replication in the two money markets,
with no optionality involved.

**Implied forward curve**: chaining CIP across two maturities gives the
**forward-forward factor** — the ratio `F(0,T₂)/F(0,T₁)`, i.e. the FX-swap
points between `T₁` and `T₂` — purely from the two spot-dated forwards, with
the spot rate canceling. This is *not itself* an exchange rate: the actual
`T₁`-struck forward for delivery at `T₂` is the random
`S_{T₁} · exp((r_d - r_f)·(T₂ - T₁))`, since the future spot `S_{T₁}` is
unknown today. What the factor gives is the deterministic multiplier by
which that future forward quote relates to today's two spot-dated quotes —
the curve is internally consistent, with no re-anchoring to `S` needed once
`F(0,T₁)` and `F(0,T₂)` are known:

  `F(0, T₂) / F(0, T₁) = exp((r_d - r_f) · (T₂ - T₁))`.

## Result

* `fxForward`: the CIP forward rate `S · exp((r_d - r_f) · T)`.
* `fxForward_at_zero`: `F(0, 0) = S` (the forward collapses to spot at
  immediate maturity).
* `fxForward_pos`: every CIP forward is positive whenever spot is.
* `forwardForwardFactor`: the ratio `F(0,T₂)/F(0,T₁)` — the forward-forward
  factor, independent of `S`.
* `forwardForwardFactor_eq_exp_diff`: that ratio equals
  `exp((r_d - r_f)·(T₂ - T₁))` — the curve is multiplicatively consistent.
-/

@[expose] public section

namespace MathFin

/-- Covered-interest-parity FX forward rate for maturity `T`, continuous
compounding: `F(0, T) = S · exp((r_d - r_f) · T)`. -/
noncomputable def fxForward (S r_d r_f T : ℝ) : ℝ := S * Real.exp ((r_d - r_f) * T)

/-- At zero maturity the forward collapses to the spot rate. -/
theorem fxForward_at_zero (S r_d r_f : ℝ) : fxForward S r_d r_f 0 = S := by
  unfold fxForward; simp

/-- Every CIP forward is positive whenever the spot rate is. -/
theorem fxForward_pos {S : ℝ} (hS : 0 < S) (r_d r_f T : ℝ) : 0 < fxForward S r_d r_f T :=
  mul_pos hS (Real.exp_pos _)

/-- The **forward-forward factor** between `T₁` and `T₂`: the ratio of the
two spot-dated CIP forwards. The spot rate `S` cancels, so this is exactly
the deterministic FX-swap-points factor a forward curve built from
market-quoted forwards would use, with no need to re-observe spot. It is a
unitless ratio, not an exchange rate — see the module docstring. -/
noncomputable def forwardForwardFactor (S r_d r_f T1 T2 : ℝ) : ℝ :=
  fxForward S r_d r_f T2 / fxForward S r_d r_f T1

/-- The forward-forward factor equals `exp((r_d - r_f)·(T₂ - T₁))`, with no
dependence on `S` left. This is the forward curve's self-consistency:
chaining two spot-dated forwards agrees with the direct CIP exponential over
the maturity gap. -/
theorem forwardForwardFactor_eq_exp_diff {S : ℝ} (hS : S ≠ 0) (r_d r_f T1 T2 : ℝ) :
    forwardForwardFactor S r_d r_f T1 T2 = Real.exp ((r_d - r_f) * (T2 - T1)) := by
  unfold forwardForwardFactor fxForward
  rw [mul_div_mul_left _ _ hS, ← Real.exp_sub]
  congr 1
  ring

end MathFin
