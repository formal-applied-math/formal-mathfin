/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-! # Call price functions

The call prices `K ↦ 𝔼[(S − K)⁺]` of a nonnegative random variable `S` of mean one are convex in
the strike, lie between `(1 − K)⁺` and `1`, and tend to `0` at large strikes. These are the
single-maturity conditions of Roper, *Arbitrage free implied volatility surfaces* (2010),
Theorem 2.1, with the forward normalised to one; a function of the strike that satisfies them is
free of butterfly arbitrage. `IsNormalizedCallPrice` records them, with two consequences:
such a function is nonincreasing and tends to `1` at strike `0`
(`IsNormalizedCallPrice.of_convexOn`).

Neither direction of the correspondence with random variables is proved here.
-/

@[expose] public section

open Filter Topology Set

/-- **A convex function on a right-infinite interval that is bounded above is nonincreasing.** A
positive slope somewhere would persist, by convexity, and carry the function past its bound. -/
theorem ConvexOn.antitoneOn_Ioi_of_le {f : ℝ → ℝ} {a B : ℝ} (hf : ConvexOn ℝ (Ioi a) f)
    (hB : ∀ x ∈ Ioi a, f x ≤ B) : AntitoneOn f (Ioi a) := by
  intro x hx y hy hxy
  by_contra! hfxy
  have hxy' : x < y := hxy.lt_of_ne (by rintro rfl; exact lt_irrefl _ hfxy)
  set s := (f y - f x) / (y - x)
  have hs : 0 < s := div_pos (sub_pos.2 hfxy) (sub_pos.2 hxy')
  have hyz : y < y + (B - f y) / s + 1 := by
    linarith [div_nonneg (sub_nonneg.2 (hB y hy)) hs.le]
  have hz : y + (B - f y) / s + 1 ∈ Ioi a := lt_trans hy hyz
  have h := (le_div_iff₀ (sub_pos.2 hyz)).1 (hf.slope_mono_adjacent hx hz hxy' hyz)
  have e : s * (y + (B - f y) / s + 1 - y) = (B - f y) + s := by
    field_simp
    ring
  linarith [hB _ hz]

namespace MathFin

/-- **A normalised call price function** on positive strikes: convex and nonincreasing, between
the intrinsic value `(1 − K)⁺` and the forward `1`, with limits `1` at strike `0` and `0` at
large strikes. Convexity, the two bounds and the large-strike limit are the single-maturity
conditions of Roper's Theorem 2.1 with the forward normalised to one; the other two fields follow
from them (`IsNormalizedCallPrice.of_convexOn`). -/
structure IsNormalizedCallPrice (C : ℝ → ℝ) : Prop where
  /-- Convex in the strike: no butterfly spread has a negative price. -/
  convexOn : ConvexOn ℝ (Ioi 0) C
  /-- Nonincreasing in the strike: no call spread has a negative price. -/
  antitoneOn : AntitoneOn C (Ioi 0)
  /-- At least the intrinsic value. -/
  intrinsic_le : ∀ K ∈ Ioi (0 : ℝ), max (1 - K) 0 ≤ C K
  /-- At most the forward. -/
  le_one : ∀ K ∈ Ioi (0 : ℝ), C K ≤ 1
  /-- The price at strike `0` is the forward. -/
  tendsto_one : Tendsto C (𝓝[>] 0) (𝓝 1)
  /-- The price vanishes at large strikes. -/
  tendsto_zero : Tendsto C atTop (𝓝 0)

/-- Convexity, the two bounds and the large-strike limit make a normalised call price function:
monotonicity comes from convexity and the upper bound, the limit at strike `0` from the squeeze
`1 − K ≤ C(K) ≤ 1`. -/
theorem IsNormalizedCallPrice.of_convexOn {C : ℝ → ℝ} (hC : ConvexOn ℝ (Ioi 0) C)
    (hlow : ∀ K ∈ Ioi (0 : ℝ), max (1 - K) 0 ≤ C K) (hup : ∀ K ∈ Ioi (0 : ℝ), C K ≤ 1)
    (h0 : Tendsto C atTop (𝓝 0)) : IsNormalizedCallPrice C where
  convexOn := hC
  antitoneOn := hC.antitoneOn_Ioi_of_le hup
  intrinsic_le := hlow
  le_one := hup
  tendsto_one :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (((by fun_prop : Continuous fun K : ℝ ↦ 1 - K).tendsto' 0 1 (sub_zero 1)).mono_left
        nhdsWithin_le_nhds) tendsto_const_nhds
      (by filter_upwards [self_mem_nhdsWithin] with K hK using (le_max_left _ _).trans (hlow K hK))
      (by filter_upwards [self_mem_nhdsWithin] with K hK using hup K hK)
  tendsto_zero := h0

end MathFin
