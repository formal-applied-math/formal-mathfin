/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Superposition of Poisson streams: the map-form increment law

The convolution identity `poissonMeasure a ∗ poissonMeasure b =
poissonMeasure (a + b)` is **Mathlib's** — `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`,
landed 2026-05-26 (leanprover-community/mathlib4#34435), proved there by
characteristic functions. This file used to re-derive it from the point masses
(Cauchy product + binomial collapse); that proof was a duplicate of upstream and
has been replaced by consumption. What remains here is the piece Mathlib does
not carry in this form.

Mathlib's superposition statements are `HasLaw`-shaped
(`IndepFun.hasLaw_add_poissonMeasure`). The Poisson-process tower states its
increment laws as **pushforward equalities** `μ.map X = poissonMeasure a`, and
gets the measurability side conditions for free from a nonzero pushforward
rather than assuming them. `indepFun_map_add_poissonMeasure` is that adapter,
and it is the only mathematical content this file still owns.

## Main results

* `PoissonSuperposition.poissonMeasure_conv_poissonMeasure` — re-export of
  Mathlib's convolution identity, kept as the name the Poisson benchmark
  snippets reference.
* `PoissonSuperposition.indepFun_map_add_poissonMeasure` — if `X, Y` are
  independent with `Poisson(a)`, `Poisson(b)` laws *as pushforwards*, then
  `X + Y` has `Poisson(a+b)` law (the superposition theorem at increment level,
  Saporito Theorem 3.3.9, with no measurability hypotheses).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PoissonSuperposition

/-- **Poisson convolution identity** — Mathlib's
`ProbabilityTheory.poissonMeasure_conv_poissonMeasure`, re-exported under the
name the Poisson benchmark snippets reference. Not proved here: upstream has it
(via characteristic functions) and a second proof would be a duplicate. -/
theorem poissonMeasure_conv_poissonMeasure (a b : ℝ≥0) :
    poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b) :=
  _root_.ProbabilityTheory.poissonMeasure_conv_poissonMeasure a b

/-! ### Superposition at increment level -/

/-- **Superposition theorem (increment form, Saporito Theorem 3.3.9).** If
`X` and `Y` are independent `ℕ`-valued random counts with `Poisson(a)` and
`Poisson(b)` laws, their sum is `Poisson(a + b)`. No measurability hypotheses
are needed: a nonzero pushforward forces a.e.-measurability. -/
theorem indepFun_map_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {a b : ℝ≥0} {X Y : Ω → ℕ} (hXY : IndepFun X Y μ)
    (hX : μ.map X = poissonMeasure a) (hY : μ.map Y = poissonMeasure b) :
    μ.map (fun ω ↦ X ω + Y ω) = poissonMeasure (a + b) := by
  rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map₀', hX, hY, poissonMeasure_conv_poissonMeasure]
  · apply AEMeasurable.of_map_ne_zero
    simp [hX, NeZero.ne]
  · apply AEMeasurable.of_map_ne_zero
    simp [hY, NeZero.ne]
  · rw [hX]; infer_instance
  · rw [hY]; infer_instance

end PoissonSuperposition

end MathFin
