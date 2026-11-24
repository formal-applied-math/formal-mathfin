/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Generator

## Main definitions

* `logHestonGenerator`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston

def logHestonGenerator (p : Parameters) (f : Real → Real → Complex) (x v : Real) : Complex :=
  ((p.r : Complex) - (p.q : Complex) - (v : Complex) / 2) *
      deriv (fun y : Real => f y v) x +
    (p.kappa : Complex) * ((p.theta : Complex) - (v : Complex)) * deriv (f x) v +
    (v : Complex) / 2 * deriv (fun y : Real => deriv (fun z : Real => f z v) y) x +
    (p.rho : Complex) * (p.xi : Complex) * (v : Complex) *
      deriv (fun w : Real => deriv (fun y : Real => f y w) x) v +
    (p.xi : Complex) ^ 2 * (v : Complex) / 2 *
      deriv (fun w : Real => deriv (fun z : Real => f x z) w) v

end MathFin.Heston
