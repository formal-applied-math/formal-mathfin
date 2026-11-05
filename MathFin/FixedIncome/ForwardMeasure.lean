/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ForwardMeasure
public import MathFin.BlackScholes.Forward

/-!
# The Black–Scholes forward price under the T-forward measure

The T-forward measure `forwardMeasure Q B` (the zero-coupon bond as numéraire, bank account `B`),
its probability and the bond-numéraire change of measure `forwardMeasure_price` are in
`Foundations/ForwardMeasure.lean`. In the **constant-rate** world the density `dQ^T/dQ` is `1`
and `Q^T = Q`; this file reads the forward price off the Black–Scholes terminal.

## Main results

* `forwardMeasure_bs_expected_terminal` — the concrete Black–Scholes instance:
  `𝔼^{Q^T}[S_T] = S_0·e^{rT}`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Black–Scholes forward price under the T-forward measure**: for the
`BSCallHyp` lognormal terminal, `𝔼^{Q^T}[S_T] = S_0·e^{rT}`. Combines the
`Q^T`-expectation identity with the discounted-terminal EMM property
`discounted_terminal_eq_S0`. -/
theorem forwardMeasure_bs_expected_terminal {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, bsTerminal S_0 r σ T (Z ω) ∂(forwardMeasure Q fun _ ↦ Real.exp (r * T))
      = S_0 * Real.exp (r * T) :=
  forwardMeasure_expected_spot S_0 r T _ (discounted_terminal_eq_S0 h)

end MathFin
