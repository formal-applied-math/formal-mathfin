/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniqueness on the real Heston moment strip

The difference between the complex and real Riccati coefficients solves a scalar linear ODE.
Grönwall's inequality identifies the coefficients on each compact maturity interval.

## Main results

* `eq_hestonBv_of_riccati` identifies the variance coefficient.
* `eq_hestonA_of_deriv` identifies the constant coefficient.

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, Riccati equation, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.Heston

/-- On the open real moment strip the complex Riccati initial value problem selects the
real Möbius solution. The estimate only uses boundedness of its linearized coefficient
on the compact time interval in question. -/
theorem eq_hestonBv_of_riccati {κ ξ ρ u T : ℝ} (hξ : ξ ≠ 0) (hu : 0 < u) (hu' : u < 1)
    {D : ℝ → ℂ} (h₀ : D 0 = 0)
    (hD : ∀ t ∈ Set.Icc 0 T, HasDerivAt D
      (((u ^ 2 - u) / 2 : ℝ) + ((ρ * ξ * u - κ : ℝ) : ℂ) * D t +
        ((ξ ^ 2 / 2 : ℝ) : ℂ) * D t ^ 2) t) :
    ∀ t ∈ Set.Icc 0 T, D t = (hestonBv κ ξ ρ u t : ℂ) := by
  let B (t : ℝ) : ℂ := hestonBv κ ξ ρ u t
  let L (t : ℝ) : ℂ := ((ρ * ξ * u - κ : ℝ) : ℂ) + ((ξ ^ 2 / 2 : ℝ) : ℂ) * (D t + B t)
  have hb (t : ℝ) := (hasDerivAt_hestonBv κ ξ ρ u t hξ hu hu').ofReal_comp
  have hc : ContinuousOn D (Set.Icc 0 T) :=
    fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt
  have hbc : Continuous B := continuous_iff_continuousAt.mpr fun t ↦ (hb t).continuousAt
  have hl : ContinuousOn L (Set.Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul (hc.add hbc.continuousOn))
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hl.norm
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      HasDerivAt (fun s ↦ D s - B s) (L t * (D t - B t)) t := by
    apply ((hD t ht).sub (hb t)).congr_deriv
    dsimp [L, B]
    push_cast
    ring
  intro t ht
  apply sub_eq_zero.mp
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (hc.sub hbc.continuousOn)
    (fun s hs ↦ (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (by simp [B, h₀, hestonBv_at_zero])
    (fun s hs ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hK (Set.mem_image_of_mem _ ⟨hs.1, hs.2.le⟩)) (norm_nonneg _)) t ht

/-- Once the variance coefficient is identified, integrating its contribution to the
constant coefficient recovers the real logarithmic formula with the same initial value. -/
theorem eq_hestonA_of_deriv {r κ θ ξ ρ u T : ℝ} (hξ : ξ ≠ 0) (hu : 0 < u) (hu' : u < 1)
    {C : ℝ → ℂ} (h₀ : C 0 = 0)
    (hC : ∀ t ∈ Set.Icc 0 T, HasDerivAt C ((r * u + κ * θ * hestonBv κ ξ ρ u t : ℝ) : ℂ) t) :
    ∀ t ∈ Set.Icc 0 T, C t = (hestonA r κ θ ξ ρ u t : ℂ) := by
  have ha (t : ℝ) := (hasDerivAt_hestonA r κ θ ξ ρ u t hξ hu hu').ofReal_comp
  have hγ : hestonGamma κ ξ ρ u ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sq_pos_of_ne_zero hξ)
      (by nlinarith [mul_pos hu (sub_pos.mpr hu')]))
  exact eq_of_has_deriv_right_eq
    (fun t ht ↦ (hC t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t _ ↦ (ha t).hasDerivWithinAt)
    (fun t ht ↦ (hC t ht).continuousAt.continuousWithinAt)
    (fun t _ ↦ (ha t).continuousAt.continuousWithinAt)
    (by simp [h₀, hestonA_at_zero _ _ _ _ _ _ hγ])

end MathFin.Heston
