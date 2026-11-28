/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.Generator
public import MathFin.Models.StochVol.Heston.IntegratedTransform

/-!
# Laplace Generator

The actual backward generator equation for complex Laplace parameters in the strip.

## Main definitions

* `laplaceSpatialProfile`

## Main results

* `logHestonGenerator_laplaceSpatial`
* `hasDerivAt_globalAffineTransform`
* `globalAffineTransform_generator_pde`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston

/-- Spatial exponential-affine profile with fixed complex coefficients. -/
def laplaceSpatialProfile (C D u : Complex) (x v : Real) : Complex :=
  Complex.exp (C + u * (x : Complex) + D * (v : Complex))

theorem hasDerivAt_laplaceSpatial_x (C D u : Complex) (x v : Real) :
    HasDerivAt (fun y : Real => laplaceSpatialProfile C D u y v)
      (laplaceSpatialProfile C D u x v * u) x := by
  have hh := ((((hasDerivAt_id (x : Complex)).const_mul u).const_add C).add_const
    (D * (v : Complex))).cexp
  simpa only [laplaceSpatialProfile, id_eq, mul_one] using hh.comp_ofReal

theorem hasDerivAt_laplaceSpatial_v (C D u : Complex) (x v : Real) :
    HasDerivAt (fun z : Real => laplaceSpatialProfile C D u x z)
      (laplaceSpatialProfile C D u x v * D) v := by
  have hh := (((hasDerivAt_id (v : Complex)).const_mul D).const_add
    (C + u * (x : Complex))).cexp
  simpa only [laplaceSpatialProfile, id_eq, mul_one] using hh.comp_ofReal

theorem deriv_laplaceSpatial_x (C D u : Complex) (x v : Real) :
    deriv (fun y : Real => laplaceSpatialProfile C D u y v) x =
      laplaceSpatialProfile C D u x v * u := (hasDerivAt_laplaceSpatial_x C D u x v).deriv

theorem deriv_laplaceSpatial_v (C D u : Complex) (x v : Real) :
    deriv (fun z : Real => laplaceSpatialProfile C D u x z) v =
      laplaceSpatialProfile C D u x v * D := (hasDerivAt_laplaceSpatial_v C D u x v).deriv

theorem deriv_laplaceSpatial_xx (C D u : Complex) (x v : Real) :
    deriv (fun y : Real => deriv (fun z : Real => laplaceSpatialProfile C D u z v) y) x =
      laplaceSpatialProfile C D u x v * u ^ 2 := by
  simp_rw [deriv_laplaceSpatial_x]
  convert! ((hasDerivAt_laplaceSpatial_x C D u x v).mul_const u).deriv using 1
  ring

theorem deriv_laplaceSpatial_vv (C D u : Complex) (x v : Real) :
    deriv (fun y : Real => deriv (fun z : Real => laplaceSpatialProfile C D u x z) y) v =
      laplaceSpatialProfile C D u x v * D ^ 2 := by
  simp_rw [deriv_laplaceSpatial_v]
  convert! ((hasDerivAt_laplaceSpatial_v C D u x v).mul_const D).deriv using 1
  ring

theorem deriv_laplaceSpatial_xv (C D u : Complex) (x v : Real) :
    deriv (fun z : Real => deriv (fun y : Real => laplaceSpatialProfile C D u y z) x) v =
      laplaceSpatialProfile C D u x v * D * u := by
  simp_rw [deriv_laplaceSpatial_x]
  exact ((hasDerivAt_laplaceSpatial_v C D u x v).mul_const u).deriv

theorem logHestonGenerator_laplaceSpatial (p : Parameters) (C D u : Complex) (x v : Real) :
    logHestonGenerator p (laplaceSpatialProfile C D u) x v =
      laplaceSpatialProfile C D u x v *
        (laplaceCarry p u + modelA p * D + laplaceRhs p u D * (v : Complex)) := by
  unfold logHestonGenerator
  rw [deriv_laplaceSpatial_xx, deriv_laplaceSpatial_xv, deriv_laplaceSpatial_vv,
    deriv_laplaceSpatial_x, deriv_laplaceSpatial_v]
  unfold laplaceCarry modelA laplaceRhs laplaceA laplaceB laplaceConstant
  push_cast
  ring

theorem hasDerivAt_globalAffineTransform (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (x v t : Real) (ht : 0 ≤ t) :
    HasDerivAt (fun s : Real => globalAffineTransform p u w x v s)
      (globalAffineTransform p u w x v t * (laplaceCarry p u + modelA p * globalLaplaceD p u w t +
        laplaceRhs p u (globalLaplaceD p u w t) * (v : Complex))) t := by
  have hC := hasDerivAt_globalLaplaceC p u w hξ hρ hu hw t ht
  have hD := (hasDerivAt_globalLaplaceD p u w hξ hρ hu hw t ht).mul_const (v : Complex)
  exact ((hC.add_const (u * (x : Complex))).add hD).cexp

theorem globalAffineTransform_generator_pde (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (x v t : Real) (ht : 0 ≤ t) :
    deriv (fun s : Real => globalAffineTransform p u w x v s) t =
      logHestonGenerator p (fun y z : Real => globalAffineTransform p u w y z t) x v := by
  rw [(hasDerivAt_globalAffineTransform p u w hξ hρ hu hw x v t ht).deriv]
  change _ = logHestonGenerator p
    (laplaceSpatialProfile (globalLaplaceC p u w t) (globalLaplaceD p u w t) u) x v
  rw [logHestonGenerator_laplaceSpatial]
  rfl

end MathFin.Heston
