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

Source candidate, NOT yet compiled in the authoring environment.
Complex time is used for the analytic identities. Real-time corollaries follow
by `HasDerivAt.comp_ofReal`. No stochastic interpretation is asserted here.

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

def denominator (b d t : Complex) : Complex := qValue b d (decay d t)

/-- Normalized logarithm argument. It equals one at time zero when d is nonzero. -/
def logArgument (b d t : Complex) : Complex := denominator b d t / (2 * d)

/-- Explicit D, without a quotient by b+d or by the variance coefficient. -/
def closedD (b d h t : Complex) : Complex :=
  -h * (1 - decay d t) / denominator b d t

/-- Explicit C. Its derivative is asserted only on the principal-log slit plane. -/
def closedC (b d a s m t : Complex) : Complex :=
  m * t + (a / s) * ((b - d) * t - 2 * Complex.log (logArgument b d t))

def rhsD (b s h z : Complex) : Complex := s / 2 * z ^ 2 - b * z - h / 2

def trapG (b d : Complex) : Complex := (b - d) / (b + d)

/-- Actual model coefficients, not a record of assumed conclusions. -/
structure Parameters where
  kappa : Real
  theta : Real
  xi : Real
  rho : Real
  r : Real
  q : Real

def modelB (p : Parameters) (u : Real) : Complex :=
  (p.kappa : Complex) - (p.rho : Complex) * (p.xi : Complex) * Complex.I * (u : Complex)

def modelH (u : Real) : Complex := (u : Complex) ^ 2 + Complex.I * (u : Complex)

def modelS (p : Parameters) : Complex := (p.xi : Complex) ^ 2

def modelA (p : Parameters) : Complex := (p.kappa : Complex) * (p.theta : Complex)

def modelM (p : Parameters) (u : Real) : Complex :=
  Complex.I * (u : Complex) * ((p.r : Complex) - (p.q : Complex))

def discriminant (p : Parameters) (u : Real) : Complex :=
  modelB p u ^ 2 + modelS p * modelH u

def modelRoot (p : Parameters) (u : Real) : Complex := principalRoot (discriminant p u)

/-- Zero frequency is defined separately; no 0/0 convention is used there. -/
def hestonD (p : Parameters) (u t : Real) : Complex :=
  if u = 0 then 0 else closedD (modelB p u) (modelRoot p u) (modelH u) (t : Complex)

def hestonC (p : Parameters) (u t : Real) : Complex :=
  if u = 0 then 0 else
    closedC (modelB p u) (modelRoot p u) (modelA p) (modelS p) (modelM p u) (t : Complex)

/-- This is deliberately named a candidate, not a characteristic function. -/
def affineCandidate (p : Parameters) (u x v t : Real) : Complex :=
  Complex.exp (hestonC p u t + hestonD p u t * (v : Complex) +
    Complex.I * (u : Complex) * (x : Complex))

end MathFin.Heston
