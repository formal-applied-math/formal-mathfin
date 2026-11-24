/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CIRRegularity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz Approximations to the CIR Diffusion Coefficient

This module defines the regularized diffusion coefficient:
  g_ε(x) = √(max x 0 + ε) - √ε

for ε > 0, and establishes its core analytic and Lipschitz properties:
1. Vanishing on the non-positive half-line: x ≤ 0 → g_ε(x) = 0.
2. Uniform non-negativity and upper bound: 0 ≤ g_ε(x) ≤ √(max x 0).
3. Uniform approximation error to √(max x 0): |g_ε(x) - √(max x 0)| ≤ √ε.
4. 1/2-Hölder (sub-linear) modulus: (g_ε(x) - g_ε(y))² ≤ |x - y|.
5. Global Lipschitz continuity on ℝ with constant 1 / (2 √ε).
6. Cross-parameter variance difference bounds:
   (g_ε(x) - g_δ(y))² ≤ 2 |x - y| + 4 (ε + δ).
7. Limiting pass-to-limit bound as δ → 0:
   (g_ε(x) - √(max y 0))² ≤ 2 |x - y| + 2 ε.

Epistemological Caveat:
This file provides strictly the analytical coefficient layer required for the
Yamada-Watanabe / Picard approximation scheme of the CIR diffusion. It does NOT
assert the existence, uniqueness, or measurability of any stochastic SDE solution.

## Main definitions

* `cirApproxDiff`

## Main results

* `lipschitzWith_cirApproxDiff`
* `cirApproxDiff_cross_sq_le`
* `cirApproxDiff_lim_sq_le`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston

open Set
open scoped Topology

/-- The regularized square-root diffusion coefficient:
`g_ε(x) = √(max x 0 + ε) - √ε`. -/
def cirApproxDiff (ε : Real) (x : Real) : Real :=
  Real.sqrt (max x 0 + ε) - Real.sqrt ε

/-- For ε > 0, if x ≤ 0 then g_ε(x) = 0. -/
theorem cirApproxDiff_of_nonpos {ε : Real} {x : Real} (hx : x ≤ 0) :
    cirApproxDiff ε x = 0 := by
  unfold cirApproxDiff
  rw [max_eq_right hx, zero_add, sub_self]

/-- Lower bound: g_ε(x) ≥ 0 for all x ∈ ℝ whenever ε ≥ 0. -/
theorem cirApproxDiff_nonneg {ε : Real} (x : Real) :
    0 ≤ cirApproxDiff ε x := by
  unfold cirApproxDiff
  have hle : ε ≤ max x 0 + ε := by
    linarith [le_max_right x 0]
  have hs : Real.sqrt ε ≤ Real.sqrt (max x 0 + ε) :=
    Real.sqrt_le_sqrt hle
  linarith

/-- Pointwise upper bound: g_ε(x) ≤ √(max x 0) for all x ∈ ℝ whenever ε ≥ 0. -/
theorem cirApproxDiff_le_sqrt_max {ε : Real} (hε : 0 ≤ ε) (x : Real) :
    cirApproxDiff ε x ≤ Real.sqrt (max x 0) := by
  unfold cirApproxDiff
  have hm : 0 ≤ max x 0 := le_max_right x 0
  have hsum : 0 ≤ max x 0 + ε := add_nonneg hm hε
  have h_sq : (Real.sqrt (max x 0 + ε) - Real.sqrt ε) ^ 2 ≤ |(max x 0 + ε) - ε| :=
    sqrt_holder_sq (max x 0 + ε) ε hsum hε
  rw [add_sub_cancel_right, abs_of_nonneg hm] at h_sq
  have hdiff_nonneg : 0 ≤ Real.sqrt (max x 0 + ε) - Real.sqrt ε := by
    have hle : ε ≤ max x 0 + ε := by linarith [hm]
    have hs := Real.sqrt_le_sqrt hle
    linarith
  nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg (max x 0)]

/-- The approximation error |g_ε(x) - √(max x 0)| is uniformly bounded by √ε. -/
theorem abs_cirApproxDiff_sub_sqrt_max_le {ε : Real} (hε : 0 ≤ ε) (x : Real) :
    |cirApproxDiff ε x - Real.sqrt (max x 0)| ≤ Real.sqrt ε := by
  rw [abs_of_nonpos (sub_nonpos.mpr (cirApproxDiff_le_sqrt_max hε x))]
  unfold cirApproxDiff
  have hs := Real.sqrt_le_sqrt (show max x 0 ≤ max x 0 + ε by linarith)
  linarith

/-- 1/2-Hölder modulus of continuity: (g_ε(x) - g_ε(y))² ≤ |x - y|. -/
theorem cirApproxDiff_holder_sq {ε : Real} (hε : 0 ≤ ε) (x y : Real) :
    (cirApproxDiff ε x - cirApproxDiff ε y) ^ 2 ≤ |x - y| := by
  unfold cirApproxDiff
  have hid : (Real.sqrt (max x 0 + ε) - Real.sqrt ε) - (Real.sqrt (max y 0 + ε) - Real.sqrt ε) =
      Real.sqrt (max x 0 + ε) - Real.sqrt (max y 0 + ε) := by ring
  rw [hid]
  have hx : 0 ≤ max x 0 + ε := add_nonneg (le_max_right x 0) hε
  have hy : 0 ≤ max y 0 + ε := add_nonneg (le_max_right y 0) hε
  have h_sq := sqrt_holder_sq (max x 0 + ε) (max y 0 + ε) hx hy
  have h_diff : (max x 0 + ε) - (max y 0 + ε) = max x 0 - max y 0 := by ring
  rw [h_diff] at h_sq
  have h_max_dist : |max x 0 - max y 0| ≤ |x - y| := by
    exact abs_max_sub_max_le_abs x y 0
  exact le_trans h_sq h_max_dist

/-- Difference bound on the right half-line x, y ≥ 0 using mean value inequality. -/
theorem abs_sqrt_add_sub_sqrt_add_le {ε : Real} (hε : 0 < ε) {u v : Real}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.sqrt (u + ε) - Real.sqrt (v + ε)| ≤ (1 / (2 * Real.sqrt ε)) * |u - v| := by
  have h := (lipschitzOnWith_sqrt_Ici hε).dist_le_mul (u + ε)
    (show u + ε ∈ Ici ε by simpa using hu)
    (v + ε) (show v + ε ∈ Ici ε by simpa using hv)
  rw [Real.coe_toNNReal] at h
  · simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using h
  · positivity

/-- Global Lipschitz continuity of g_ε with constant 1 / (2 √ε). -/
theorem lipschitzWith_cirApproxDiff {ε : Real} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (1 / (2 * Real.sqrt ε))) (cirApproxDiff ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal]
  · unfold cirApproxDiff
    have hid : (Real.sqrt (max x 0 + ε) - Real.sqrt ε) - (Real.sqrt (max y 0 + ε) - Real.sqrt ε) =
        Real.sqrt (max x 0 + ε) - Real.sqrt (max y 0 + ε) := by ring
    rw [hid]
    have hu : 0 ≤ max x 0 := le_max_right x 0
    have hv : 0 ≤ max y 0 := le_max_right y 0
    have hstep := abs_sqrt_add_sub_sqrt_add_le hε hu hv
    have hmax_dist : |max x 0 - max y 0| ≤ |x - y| := by
      exact abs_max_sub_max_le_abs x y 0
    have hpos_C : 0 ≤ 1 / (2 * Real.sqrt ε) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmax_dist hpos_C
    exact le_trans hstep hmul
  · positivity

/-- Cross-parameter variance difference bound:
`(g_ε(x) - g_δ(y))² ≤ 2 |x - y| + 4 (ε + δ)`. -/
theorem cirApproxDiff_cross_sq_le {ε δ : Real} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (x y : Real) :
    (cirApproxDiff ε x - cirApproxDiff δ y) ^ 2 ≤ 2 * |x - y| + 4 * (ε + δ) := by
  have hid : cirApproxDiff ε x - cirApproxDiff δ y =
      (cirApproxDiff ε x - cirApproxDiff ε y) +
      (cirApproxDiff ε y - Real.sqrt (max y 0)) +
      (Real.sqrt (max y 0) - cirApproxDiff δ y) := by ring
  have h_quad : (cirApproxDiff ε x - cirApproxDiff δ y) ^ 2 ≤
      2 * (cirApproxDiff ε x - cirApproxDiff ε y) ^ 2 +
      2 * ((cirApproxDiff ε y - Real.sqrt (max y 0)) +
           (Real.sqrt (max y 0) - cirApproxDiff δ y)) ^ 2 := by
    rw [hid]
    nlinarith [sq_nonneg ((cirApproxDiff ε x - cirApproxDiff ε y) -
      ((cirApproxDiff ε y - Real.sqrt (max y 0)) +
       (Real.sqrt (max y 0) - cirApproxDiff δ y)))]
  have h_inner : ((cirApproxDiff ε y - Real.sqrt (max y 0)) +
      (Real.sqrt (max y 0) - cirApproxDiff δ y)) ^ 2 ≤
      2 * (cirApproxDiff ε y - Real.sqrt (max y 0)) ^ 2 +
      2 * (Real.sqrt (max y 0) - cirApproxDiff δ y) ^ 2 := by
    nlinarith [sq_nonneg ((cirApproxDiff ε y - Real.sqrt (max y 0)) -
      (Real.sqrt (max y 0) - cirApproxDiff δ y))]
  have h_holder := cirApproxDiff_holder_sq hε x y
  have h_err_eps := abs_cirApproxDiff_sub_sqrt_max_le hε y
  have h_sq_eps : (cirApproxDiff ε y - Real.sqrt (max y 0)) ^ 2 ≤ ε := by
    have h_abs_sq : (cirApproxDiff ε y - Real.sqrt (max y 0)) ^ 2 =
        |cirApproxDiff ε y - Real.sqrt (max y 0)| ^ 2 := by
      rw [sq_abs]
    rw [h_abs_sq]
    have h0 : 0 ≤ |cirApproxDiff ε y - Real.sqrt (max y 0)| := abs_nonneg _
    have h_sq_le := (sq_le_sq₀ h0 (Real.sqrt_nonneg ε)).mpr h_err_eps
    rw [Real.sq_sqrt hε] at h_sq_le
    exact h_sq_le
  have h_err_del := abs_cirApproxDiff_sub_sqrt_max_le hδ y
  have h_sq_del : (Real.sqrt (max y 0) - cirApproxDiff δ y) ^ 2 ≤ δ := by
    have hid_del : Real.sqrt (max y 0) - cirApproxDiff δ y =
        -(cirApproxDiff δ y - Real.sqrt (max y 0)) := by ring
    rw [hid_del, neg_sq]
    have h_abs_sq : (cirApproxDiff δ y - Real.sqrt (max y 0)) ^ 2 =
        |cirApproxDiff δ y - Real.sqrt (max y 0)| ^ 2 := by
      rw [sq_abs]
    rw [h_abs_sq]
    have h0 : 0 ≤ |cirApproxDiff δ y - Real.sqrt (max y 0)| := abs_nonneg _
    have h_sq_le := (sq_le_sq₀ h0 (Real.sqrt_nonneg δ)).mpr h_err_del
    rw [Real.sq_sqrt hδ] at h_sq_le
    exact h_sq_le
  linarith

/-- Limiting bound when δ → 0:
`(g_ε(x) - √(max y 0))² ≤ 2 |x - y| + 2 ε`. -/
theorem cirApproxDiff_lim_sq_le {ε : Real} (hε : 0 ≤ ε) (x y : Real) :
    (cirApproxDiff ε x - Real.sqrt (max y 0)) ^ 2 ≤ 2 * |x - y| + 2 * ε := by
  have hid : cirApproxDiff ε x - Real.sqrt (max y 0) =
      (cirApproxDiff ε x - cirApproxDiff ε y) +
      (cirApproxDiff ε y - Real.sqrt (max y 0)) := by ring
  have h_quad : (cirApproxDiff ε x - Real.sqrt (max y 0)) ^ 2 ≤
      2 * (cirApproxDiff ε x - cirApproxDiff ε y) ^ 2 +
      2 * (cirApproxDiff ε y - Real.sqrt (max y 0)) ^ 2 := by
    rw [hid]
    nlinarith [sq_nonneg ((cirApproxDiff ε x - cirApproxDiff ε y) -
      (cirApproxDiff ε y - Real.sqrt (max y 0)))]
  have h_holder := cirApproxDiff_holder_sq hε x y
  have h_err_eps := abs_cirApproxDiff_sub_sqrt_max_le hε y
  have h_sq_eps : (cirApproxDiff ε y - Real.sqrt (max y 0)) ^ 2 ≤ ε := by
    have h_abs_sq : (cirApproxDiff ε y - Real.sqrt (max y 0)) ^ 2 =
        |cirApproxDiff ε y - Real.sqrt (max y 0)| ^ 2 := by
      rw [sq_abs]
    rw [h_abs_sq]
    have h0 : 0 ≤ |cirApproxDiff ε y - Real.sqrt (max y 0)| := abs_nonneg _
    have h_sq_le := (sq_le_sq₀ h0 (Real.sqrt_nonneg ε)).mpr h_err_eps
    rw [Real.sq_sqrt hε] at h_sq_le
    exact h_sq_le
  linarith

end MathFin.Heston
