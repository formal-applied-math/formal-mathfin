/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.Comparison

/-!
# Bounded coefficients of the normalized comparison equation

The logarithmic slope of the explicit positive profile lies between its two
characteristic roots. The Riccati equation bounds its derivative. Consequently
the normalized drift and its first space/time derivatives are globally bounded.
No derivative of the unknown exercise boundary enters these bounds.

## Result

Public entry points include `rootProfile_slope_bounds`, `profile_slope_bounds`,
`profile_slope_and_deriv_bounded`, `normalizedDrift`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open scoped ContDiff

theorem rootProfile_slope_bounds {u v : ℝ} (hu : 0 < u) (hv : v < 0) (z : ℝ) :
    v < logSlope (rootProfile u v) z ∧ logSlope (rootProfile u v) z < u := by
  have huv : u - v ≠ 0 := ne_of_gt (by linarith)
  have hF : 0 < rootProfile u v z := lt_of_lt_of_le zero_lt_one (rootProfile_ge_one hu hv z)
  have hlo : deriv (rootProfile u v) z - v * rootProfile u v z = -v * Real.exp (u * z) := by
    rw [rootProfile_deriv]
    unfold rootProfile
    field_simp
    ring
  have hhi : u * rootProfile u v z - deriv (rootProfile u v) z = u * Real.exp (v * z) := by
    rw [rootProfile_deriv]
    unfold rootProfile
    field_simp
    ring
  unfold logSlope
  rw [lt_div_iff₀ hF, div_lt_iff₀ hF]
  constructor
  · have hp : 0 < -v * Real.exp (u * z) := mul_pos (neg_pos.mpr hv) (Real.exp_pos _)
    linarith
  · have hp : 0 < u * Real.exp (v * z) := by positivity
    linarith

theorem profile_slope_bounds {β ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) :
    negativeRoot β ρ < logSlope (profile β ρ) z ∧
      logSlope (profile β ρ) z < positiveRoot β ρ := by
  obtain ⟨hu, hv⟩ := roots_signs (β := β) hρ
  simpa only [profile, hρ.ne', ↓reduceIte] using rootProfile_slope_bounds hu hv z

theorem profile_slope_and_deriv_bounded {β ρ : ℝ} (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z,
      |logSlope (profile β ρ) z| ≤ B ∧ |deriv (logSlope (profile β ρ)) z| ≤ B := by
  let M := |positiveRoot β ρ| + |negativeRoot β ρ| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hm (z : ℝ) : |logSlope (profile β ρ) z| ≤ M := by
    obtain ⟨hlo, hhi⟩ := profile_slope_bounds hρ z
    apply abs_le.mpr
    dsimp [M]
    constructor
    · linarith [neg_abs_le (negativeRoot β ρ), abs_nonneg (positiveRoot β ρ)]
    · linarith [le_abs_self (positiveRoot β ρ), abs_nonneg (negativeRoot β ρ)]
  let N := |ρ| + |β| * M + M ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hm' (z : ℝ) : |deriv (logSlope (profile β ρ)) z| ≤ N := by
    rw [(logSlope_hasDeriv (profile_data hρ.le) z).deriv]
    calc
      _ ≤ |ρ| + |β| * |logSlope (profile β ρ) z| + |logSlope (profile β ρ) z| ^ 2 := by
        have h₁ := abs_add_le ρ (-(β * logSlope (profile β ρ) z))
        have h₂ := abs_add_le (ρ - β * logSlope (profile β ρ) z) (-(logSlope (profile β ρ) z ^ 2))
        simp only [← sub_eq_add_neg, abs_neg, abs_mul] at h₁
        simp only [← sub_eq_add_neg, abs_neg, abs_pow] at h₂
        linarith
      _ ≤ N := by dsimp [N]; gcongr <;> exact hm z
  refine ⟨M + N + 1, by positivity, ?_⟩
  intro z
  constructor
  · linarith [hm z]
  · linarith [hm' z]

/-- The drift `α` corrected by twice the logarithmic slope of `f`, read at `x + c * t - d`. -/
noncomputable def normalizedDrift (α c d : ℝ) (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  α + 2 * logSlope f (x + c * t - d)

theorem normalizedDrift_eq (α c d : ℝ) (f : ℝ → ℝ) (x t : ℝ) :
    normalizedDrift α c d f x t = α + 2 * deriv f (x + c * t - d) / f (x + c * t - d) := by
  unfold normalizedDrift logSlope
  ring

theorem normalizedDrift_hasDeriv_x {β ρ : ℝ} {f : ℝ → ℝ}
    (hf : ProfileData β ρ f) (α c d x t : ℝ) :
    HasDerivAt (fun y => normalizedDrift α c d f y t)
      (2 * deriv (logSlope f) (x + c * t - d)) x := by
  have hm := (logSlope_hasDeriv hf (x + c * t - d)).differentiableAt.hasDerivAt
  convert! ((hm.comp x (((hasDerivAt_id x).add_const (c * t)).sub_const d)).const_mul 2).const_add α
    using 1
  simp

theorem normalizedDrift_hasDeriv_t {β ρ : ℝ} {f : ℝ → ℝ}
    (hf : ProfileData β ρ f) (α c d x t : ℝ) :
    HasDerivAt (normalizedDrift α c d f x)
      (2 * c * deriv (logSlope f) (x + c * t - d)) t := by
  have hm := (logSlope_hasDeriv hf (x + c * t - d)).differentiableAt.hasDerivAt
  convert!
      ((hm.comp t ((((hasDerivAt_id t).const_mul c).const_add x).sub_const d)).const_mul
      2).const_add α
    using 1
  ring

/-- The coefficient and both derivatives appearing in the zero-number
hypotheses have one uniform bound on the entire space-time plane. -/
theorem normalizedDrift_bounded {β ρ : ℝ} (hρ : 0 < ρ) (α c d : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x t,
      |normalizedDrift α c d (profile β ρ) x t| ≤ C ∧
      |deriv (fun y => normalizedDrift α c d (profile β ρ) y t) x| ≤ C ∧
      |deriv (normalizedDrift α c d (profile β ρ) x) t| ≤ C := by
  obtain ⟨B, hB, hb⟩ := profile_slope_and_deriv_bounded (β := β) hρ
  refine ⟨|α| + 2 * B + 2 * |c| * B + 1, by positivity, ?_⟩
  intro x t
  obtain ⟨hm, hm'⟩ := hb (x + c * t - d)
  have hcb : 0 ≤ 2 * |c| * B := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have ha := abs_add_le α (2 * logSlope (profile β ρ) (x + c * t - d))
    norm_num only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at ha
    unfold normalizedDrift
    linarith
  · rw [(normalizedDrift_hasDeriv_x (profile_data hρ.le) α c d x t).deriv]
    norm_num only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith [abs_nonneg α]
  · rw [(normalizedDrift_hasDeriv_t (profile_data hρ.le) α c d x t).deriv]
    norm_num only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have he := mul_le_mul_of_nonneg_left hm' (show 0 ≤ 2 * |c| by positivity)
    linarith [abs_nonneg α]

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
