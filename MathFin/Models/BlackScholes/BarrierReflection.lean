/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The barrier reflection factor `(H/S)^{2μ}`

Every closed form for a barrier option under geometric Brownian motion carries the image
(reflection) factor `(H/S)^{2μ}` of the reflection principle, with `μ` the dimensionless drift
`(b − σ²/2)/σ²`. The binary-barrier, partial-time-barrier and Heynen–Kat two-asset formulas all
write it; this file defines it once, as `exp (2μ · log (H/S))`, so the three share one object.

## Main definitions

* `barrierReflection`: `(H/S)^{2μ}`, written as `exp (2μ · log (H/S))`.

## Main results

* `barrierReflection_eq_rpow`: for `0 < H/S` it is the real power `(H/S)^{2μ}`.
* `barrierReflection_add_one`: for `0 < H/S`, raising `μ` by one multiplies it by `(H/S)²`.

## References

* [Haug, *The Complete Guide to Option Pricing Formulas*][Haug2007], ch. 4
* [Rubinstein and Reiner (1991)][RubinsteinReiner1991]

## Tags

barrier option, reflection principle, image method, geometric Brownian motion,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- **`(H/S)^{2μ}`**, written as `exp(2μ·log(H/S))`: the reflection factor of the barrier
formulas. It agrees with the real power `(H/S)^{2μ}` when `0 < H/S`
(`barrierReflection_eq_rpow`); QuantLib's own overflow guard evaluates this factor together with
its `Φ(y)` multiplier as one logged product, not this factor alone. -/
noncomputable def barrierReflection (S H μ : ℝ) : ℝ := Real.exp (2 * μ * Real.log (H / S))

/-- For `0 < H/S` the reflection factor is the real power `(H/S)^{2μ}`. -/
lemma barrierReflection_eq_rpow {S H : ℝ} (μ : ℝ) (h : 0 < H / S) :
    barrierReflection S H μ = (H / S) ^ (2 * μ) := by
  rw [barrierReflection, Real.rpow_def_of_pos h, mul_comm]

/-- For `0 < H/S`, raising the drift `μ` by one multiplies the reflection factor by `(H/S)²`. -/
lemma barrierReflection_add_one {S H : ℝ} (μ : ℝ) (h : 0 < H / S) :
    barrierReflection S H (μ + 1) = barrierReflection S H μ * (H / S) ^ 2 := by
  rw [barrierReflection_eq_rpow _ h, barrierReflection_eq_rpow _ h, mul_add, mul_one,
    Real.rpow_add h, Real.rpow_two]

end MathFin
