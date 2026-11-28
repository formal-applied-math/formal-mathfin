/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Explicit Heston Riccati closed forms

These definitions give the principal-log candidates at complex time. The characteristic-function
theorem uses the linear flow and its time integral. Identifying that flow with these candidates
on the characteristic axis requires a further branch argument.

## Main definitions

* `hestonD`
* `hestonC`
* `affineCandidate`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston

/-- A branch-explicit square root, with a separate value at zero. -/
def principalRoot (z : Complex) : Complex :=
  if z = 0 then 0 else Complex.exp (Complex.log z / 2)

/-- Polynomial denominator before substitution of the exponential. -/
def qValue (b d e : Complex) : Complex := (b + d) - (b - d) * e

/-- Decaying exponential used in the little-Heston-trap form. -/
def decay (d t : Complex) : Complex := Complex.exp (-d * t)

/-- Denominator of the Möbius representation of the Riccati coefficient. -/
def denominator (b d t : Complex) : Complex := qValue b d (decay d t)

/-- Normalized logarithm argument. It equals one at time zero when d is nonzero. -/
def logArgument (b d t : Complex) : Complex := denominator b d t / (2 * d)

/-- Explicit D, without a quotient by b+d or by the variance coefficient. -/
def closedD (b d h t : Complex) : Complex :=
  -h * (1 - decay d t) / denominator b d t

/-- Candidate constant coefficient, evaluated with the principal complex logarithm. -/
def closedC (b d a s m t : Complex) : Complex :=
  m * t + (a / s) * ((b - d) * t - 2 * Complex.log (logArgument b d t))

/-- Quadratic vector field for the variance coefficient at characteristic frequency. -/
def rhsD (b s h z : Complex) : Complex := s / 2 * z ^ 2 - b * z - h / 2

/-- Ratio of the two root factors in the little-trap representation. -/
def trapG (b d : Complex) : Complex := (b - d) / (b + d)

/-- Actual model coefficients, not a record of assumed conclusions. -/
structure Parameters where
  /-- Mean reversion speed of the variance. -/
  kappa : Real
  /-- Long-run variance level. -/
  theta : Real
  /-- Volatility coefficient of the variance process. -/
  xi : Real
  /-- Correlation between the log-spot and variance drivers. -/
  rho : Real
  /-- Risk-free rate. -/
  r : Real
  /-- Continuous dividend yield. -/
  q : Real

/-- Mean-reversion term shifted by the correlation at the characteristic frequency. -/
def modelB (p : Parameters) (u : Real) : Complex :=
  (p.kappa : Complex) - (p.rho : Complex) * (p.xi : Complex) * Complex.I * (u : Complex)

/-- Frequency polynomial appearing in the constant Riccati forcing term. -/
def modelH (u : Real) : Complex := (u : Complex) ^ 2 + Complex.I * (u : Complex)

/-- Square of the volatility of volatility as a complex coefficient. -/
def modelS (p : Parameters) : Complex := (p.xi : Complex) ^ 2

/-- Constant variance drift, equal to the mean reversion speed times the long-run level. -/
def modelA (p : Parameters) : Complex := (p.kappa : Complex) * (p.theta : Complex)

/-- Log-spot carry multiplied by the imaginary frequency. -/
def modelM (p : Parameters) (u : Real) : Complex :=
  Complex.I * (u : Complex) * ((p.r : Complex) - (p.q : Complex))

/-- Discriminant of the characteristic-frequency Riccati polynomial. -/
def discriminant (p : Parameters) (u : Real) : Complex :=
  modelB p u ^ 2 + modelS p * modelH u

/-- Chosen square root of the characteristic-frequency discriminant. -/
def modelRoot (p : Parameters) (u : Real) : Complex := principalRoot (discriminant p u)

/-- Zero frequency is defined separately; no 0/0 convention is used there. -/
def hestonD (p : Parameters) (u t : Real) : Complex :=
  if u = 0 then 0 else closedD (modelB p u) (modelRoot p u) (modelH u) (t : Complex)

/-- Time coefficient of the complex closed form at a real characteristic frequency. -/
def hestonC (p : Parameters) (u t : Real) : Complex :=
  if u = 0 then 0 else
    closedC (modelB p u) (modelRoot p u) (modelA p) (modelS p) (modelM p u) (t : Complex)

/-- This is deliberately named a candidate, not a characteristic function. -/
def affineCandidate (p : Parameters) (u x v t : Real) : Complex :=
  Complex.exp (hestonC p u t + hestonD p u t * (v : Complex) +
    Complex.I * (u : Complex) * (x : Complex))

end MathFin.Heston
