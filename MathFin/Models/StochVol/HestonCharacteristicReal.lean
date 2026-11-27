/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.StochVol.HestonCharacteristic

/-!
# The trap-form Riccati solutions at real `u` are the Möbius closed forms

`Models/StochVol/HestonCharacteristic` solves the Heston Riccati system at complex `u` in the
"little Heston trap" form, with `e^{−dτ}`. `Models/StochVol/Heston` solves it at real
`0 < u < 1` in the Möbius form with `e^{+γτ}`, `γ = hestonGamma`. This file shows that the first
extends the second: with the root `d = γ`, the trap-form `D` and `C` at the real `u` are the casts
of `hestonBv` and `hestonA`. So the real results of `Heston.lean` are the special case of the
complex ones, and the two forms are the same solution (the logarithm of the trap form differs from
that of the Möbius form by the linear term `γτ`).

## Main results

* `hestonTrapD_ofReal`: `D_trap(τ) = ↑(hestonBv κ ξ ρ u τ)` at `d = ↑γ`.
* `hestonTrapC_ofReal`: `C_trap(τ) = ↑(hestonA r κ θ ξ ρ u τ)` at `d = ↑γ`.

## References

* [Albrecher, Mayer, Schoutens, Tistaert,
  *The little Heston trap*][AlbrecherMayerSchoutensTistaert2007]
* [Heston, *A closed-form solution for options with stochastic volatility with applications to bond
  and currency options*][Heston1993]

## Tags

Heston model, stochastic volatility, affine transform, Riccati equation, characteristic function,
MSC 91G20, MSC 60J60, JEL G13
-/

@[expose] public section

namespace MathFin.Heston

/-! ### Real algebra -/

private theorem trapD_real (b γ ξ w e D : ℝ) (hξ : ξ ≠ 0) (hbp : b + γ ≠ 0) (he : e ≠ 0)
    (hD : D ≠ 0) (hDdef : D = (γ + b) * e + (γ - b)) (hw : ξ ^ 2 * w = b ^ 2 - γ ^ 2) :
    (b - γ) / ξ ^ 2 * ((1 - e⁻¹) / (1 - (b - γ) / (b + γ) * e⁻¹)) = w * (e - 1) / D := by
  have hg : 1 - (b - γ) / (b + γ) * e⁻¹ = D / ((b + γ) * e) := by
    rw [hDdef]
    first
      | (field_simp; ring)
      | field_simp
  have hw' : w = (b ^ 2 - γ ^ 2) / ξ ^ 2 :=
    (eq_div_iff (pow_ne_zero 2 hξ)).2 ((mul_comm w (ξ ^ 2)).trans hw)
  rw [hg, hw']
  first
    | (field_simp; ring)
    | field_simp

private theorem trapG_real (b γ e D : ℝ) (hbp : 0 < b + γ) (he : 0 < e)
    (hDdef : D = (γ + b) * e + (γ - b)) :
    1 - (b - γ) / (b + γ) * e⁻¹ = D / ((b + γ) * e) ∧
      1 - (b - γ) / (b + γ) = 2 * γ / (b + γ) := by
  have hbp' : b + γ ≠ 0 := hbp.ne'
  have he' : e ≠ 0 := he.ne'
  constructor
  · rw [hDdef]
    first
      | (field_simp; ring)
      | field_simp
  · field_simp
    ring

private theorem trapLog_real (b γ e D τ : ℝ) (hbp : 0 < b + γ) (hγ : 0 < γ) (hD : 0 < D)
    (he : e = Real.exp (γ * τ)) :
    Real.log (D / ((b + γ) * e)) - Real.log (2 * γ / (b + γ))
      = Real.log (D / (2 * γ)) - γ * τ := by
  have hepos : 0 < e := he ▸ Real.exp_pos _
  have hq1 : 0 < D / ((b + γ) * e) := div_pos hD (mul_pos hbp hepos)
  have hq2 : 0 < 2 * γ / (b + γ) := div_pos (by linarith) hbp
  have hq3 : 0 < D / (2 * γ) := div_pos hD (by linarith)
  rw [← Real.log_div hq1.ne' hq2.ne']
  have hratio : D / ((b + γ) * e) / (2 * γ / (b + γ)) = D / (2 * γ) / e := by
    field_simp
  rw [hratio, Real.log_div hq3.ne' hepos.ne', he, Real.log_exp]

/-! ### The bridge -/

/-- **The trap-form `D` at real `u` is the Möbius `b̂`.** On the strip `0 < u < 1`, `ξ ≠ 0`, with
the root `d = γ = hestonGamma`, `hestonTrapD` at the real `u` is the cast of `hestonBv`. -/
theorem hestonTrapD_ofReal (κ ξ ρ u τ : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    hestonTrapD κ ξ ρ (u : ℂ) (hestonGamma κ ξ ρ u : ℂ) τ = (hestonBv κ ξ ρ u τ : ℂ) := by
  obtain ⟨h1, h2⟩ := hestonGamma_abs_lt κ ξ ρ u hξ hu1 hu2
  have hDpos := hestonBvDenom_pos κ ξ ρ u τ hξ hu1 hu2
  have hγsq := hestonGamma_sq κ ξ ρ u hu1 hu2
  have hbp : 0 < κ - ρ * ξ * u + hestonGamma κ ξ ρ u := by linarith
  have hreal := trapD_real (κ - ρ * ξ * u) (hestonGamma κ ξ ρ u) ξ (u ^ 2 - u)
    (Real.exp (hestonGamma κ ξ ρ u * τ)) (hestonBvDenom κ ξ ρ u τ) hξ hbp.ne'
    (Real.exp_pos _).ne' hDpos.ne' (by simp only [hestonBvDenom]; ring)
    (by linear_combination hγsq)
  have hexp : hestonTrapE (hestonGamma κ ξ ρ u : ℂ) τ
      = (((Real.exp (hestonGamma κ ξ ρ u * τ))⁻¹ : ℝ) : ℂ) := by
    rw [hestonTrapE, neg_mul, Complex.exp_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_inv]
  have hB : hestonBv κ ξ ρ u τ = _ := hreal.symm
  rw [hB]
  simp only [hestonTrapD, hestonTrapG, hestonCoeff, hexp]
  first
    | (push_cast; ring)
    | push_cast

/-- **The trap-form `C` at real `u` is the Möbius `â`.** On the strip `0 < u < 1`, `ξ ≠ 0`, with
the root `d = γ = hestonGamma`, `hestonTrapC` at the real `u` is the cast of `hestonA`: the
logarithm of the trap form is that of the Möbius form shifted by `γτ`. -/
theorem hestonTrapC_ofReal (r κ θ ξ ρ u τ : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    hestonTrapC r κ θ ξ ρ (u : ℂ) (hestonGamma κ ξ ρ u : ℂ) τ
      = (hestonA r κ θ ξ ρ u τ : ℂ) := by
  obtain ⟨h1, h2⟩ := hestonGamma_abs_lt κ ξ ρ u hξ hu1 hu2
  have hγpos := hestonGamma_pos κ ξ ρ u hξ hu1 hu2
  have hDpos := hestonBvDenom_pos κ ξ ρ u τ hξ hu1 hu2
  have hbp : 0 < κ - ρ * ξ * u + hestonGamma κ ξ ρ u := by linarith
  have hepos := Real.exp_pos (hestonGamma κ ξ ρ u * τ)
  have hDdef : hestonBvDenom κ ξ ρ u τ
      = (hestonGamma κ ξ ρ u + (κ - ρ * ξ * u)) * Real.exp (hestonGamma κ ξ ρ u * τ)
        + (hestonGamma κ ξ ρ u - (κ - ρ * ξ * u)) := by
    simp only [hestonBvDenom]
    ring
  obtain ⟨hg1, hg2⟩ := trapG_real (κ - ρ * ξ * u) (hestonGamma κ ξ ρ u)
    (Real.exp (hestonGamma κ ξ ρ u * τ)) (hestonBvDenom κ ξ ρ u τ) hbp hepos hDdef
  have hlogr := trapLog_real (κ - ρ * ξ * u) (hestonGamma κ ξ ρ u)
    (Real.exp (hestonGamma κ ξ ρ u * τ)) (hestonBvDenom κ ξ ρ u τ) τ hbp hγpos hDpos rfl
  have hq1 : 0 < hestonBvDenom κ ξ ρ u τ
      / ((κ - ρ * ξ * u + hestonGamma κ ξ ρ u) * Real.exp (hestonGamma κ ξ ρ u * τ)) :=
    div_pos hDpos (mul_pos hbp hepos)
  have hq2 : 0 < 2 * hestonGamma κ ξ ρ u / (κ - ρ * ξ * u + hestonGamma κ ξ ρ u) :=
    div_pos (by linarith) hbp
  have hexp : hestonTrapE (hestonGamma κ ξ ρ u : ℂ) τ
      = (((Real.exp (hestonGamma κ ξ ρ u * τ))⁻¹ : ℝ) : ℂ) := by
    rw [hestonTrapE, neg_mul, Complex.exp_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_inv]
  have hgc : hestonTrapG κ ξ ρ (u : ℂ) (hestonGamma κ ξ ρ u : ℂ)
      = (((κ - ρ * ξ * u - hestonGamma κ ξ ρ u)
          / (κ - ρ * ξ * u + hestonGamma κ ξ ρ u) : ℝ) : ℂ) := by
    simp only [hestonTrapG, hestonCoeff]
    first
      | (push_cast; ring)
      | push_cast
  have h1gE : (1 : ℂ) - hestonTrapG κ ξ ρ (u : ℂ) (hestonGamma κ ξ ρ u : ℂ)
        * hestonTrapE (hestonGamma κ ξ ρ u : ℂ) τ
      = ((hestonBvDenom κ ξ ρ u τ
        / ((κ - ρ * ξ * u + hestonGamma κ ξ ρ u)
            * Real.exp (hestonGamma κ ξ ρ u * τ)) : ℝ) : ℂ) := by
    rw [← hg1, hgc, hexp]
    first
      | (push_cast; ring)
      | push_cast
  have h1g : (1 : ℂ) - hestonTrapG κ ξ ρ (u : ℂ) (hestonGamma κ ξ ρ u : ℂ)
      = ((2 * hestonGamma κ ξ ρ u / (κ - ρ * ξ * u + hestonGamma κ ξ ρ u) : ℝ) : ℂ) := by
    rw [← hg2, hgc]
    first
      | (push_cast; ring)
      | push_cast
  have hlogC : (((Real.log (hestonBvDenom κ ξ ρ u τ
        / ((κ - ρ * ξ * u + hestonGamma κ ξ ρ u) * Real.exp (hestonGamma κ ξ ρ u * τ))) : ℝ) : ℂ)
      - ((Real.log (2 * hestonGamma κ ξ ρ u / (κ - ρ * ξ * u + hestonGamma κ ξ ρ u)) : ℝ) : ℂ))
      = (((Real.log (hestonBvDenom κ ξ ρ u τ / (2 * hestonGamma κ ξ ρ u)) : ℝ) : ℂ)
        - (hestonGamma κ ξ ρ u : ℂ) * τ) := by
    rw [← Complex.ofReal_sub, hlogr]
    first
      | (push_cast; ring)
      | push_cast
  simp only [hestonTrapC]
  rw [h1gE, h1g, ← Complex.ofReal_log hq1.le, ← Complex.ofReal_log hq2.le, hlogC]
  simp only [hestonA, hestonCoeff]
  push_cast
  ring

end MathFin.Heston
