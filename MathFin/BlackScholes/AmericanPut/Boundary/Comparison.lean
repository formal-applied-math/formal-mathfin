/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ODEComparison

/-!
# Straight-line comparison for the dividend-paying American put

The construction in Steps 2--4 of the proposed proof. All derivatives below are
ordinary real derivatives. The profiles are explicit functions, not existence
axioms. This file does not assert the zero-number theorem or boundary convexity.

## Result

Public entry points include `straightPrice_equation`, `straightPrice_fit`, and
`straightPrice_dominates`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open scoped ContDiff

/-- The solution with value one and slope zero, written using distinct roots. -/
noncomputable def rootProfile (u v z : ℝ) : ℝ :=
  (u * Real.exp (v * z) - v * Real.exp (u * z)) / (u - v)

theorem rootProfile_smooth (u v : ℝ) : ContDiff ℝ ∞ (rootProfile u v) := by
  unfold rootProfile
  fun_prop

theorem rootProfile_hasDerivAt (u v z : ℝ) :
    HasDerivAt (rootProfile u v)
      ((u * (Real.exp (v * z) * v) - v * (Real.exp (u * z) * u)) / (u - v)) z := by
  unfold rootProfile
  simpa only [id_eq, mul_one, Pi.sub_apply] using
      (((((hasDerivAt_id z).const_mul v).exp).const_mul u).sub
    ((((hasDerivAt_id z).const_mul u).exp).const_mul v)).div_const (u - v)

theorem rootProfile_deriv (u v z : ℝ) :
    deriv (rootProfile u v) z =
      (u * (Real.exp (v * z) * v) - v * (Real.exp (u * z) * u)) / (u - v) :=
  (rootProfile_hasDerivAt u v z).deriv

theorem rootProfile_deriv2 (u v z : ℝ) :
    deriv (deriv (rootProfile u v)) z =
      (u * (Real.exp (v * z) * v * v) -
        v * (Real.exp (u * z) * u * u)) / (u - v) := by
  rw [show deriv (rootProfile u v) = fun y =>
    (u * (Real.exp (v * y) * v) - v * (Real.exp (u * y) * u)) / (u - v) from
      funext (rootProfile_deriv u v)]
  simpa only [id_eq, mul_one, Pi.sub_apply] using
      (((((((hasDerivAt_id z).const_mul v).exp).mul_const v).const_mul u).sub
    (((((hasDerivAt_id z).const_mul u).exp).mul_const u).const_mul v)).div_const
      (u - v)).deriv

theorem rootProfile_zero {u v : ℝ} (huv : u ≠ v) : rootProfile u v 0 = 1 := by
  simp [rootProfile, sub_ne_zero.mpr huv]

theorem rootProfile_deriv_zero (u v : ℝ) : deriv (rootProfile u v) 0 = 0 := by
  rw [rootProfile_deriv]
  simp [mul_comm]

/-- The exponential tangent inequality proves the global minimum at zero. -/
theorem rootProfile_ge_one {u v : ℝ} (hu : 0 < u) (hv : v < 0) (z : ℝ) :
    1 ≤ rootProfile u v z := by
  have huv : 0 < u - v := sub_pos.mpr (hv.trans hu)
  apply (le_div_iff₀ huv).mpr
  have h₁ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v * z)) hu.le
  have h₂ := mul_le_mul_of_nonpos_left (Real.add_one_le_exp (u * z)) hv.le
  nlinarith

theorem rootProfile_ode {u v β ρ : ℝ}
    (hu : u ^ 2 + β * u - ρ = 0) (hv : v ^ 2 + β * v - ρ = 0) (z : ℝ) :
    deriv (deriv (rootProfile u v)) z + β * deriv (rootProfile u v) z -
      ρ * rootProfile u v z = 0 := by
  rw [rootProfile_deriv2, rootProfile_deriv]
  unfold rootProfile
  by_cases huv : u - v = 0
  · simp [huv]
  · field_simp
    linear_combination u * Real.exp (v * z) * hv - v * Real.exp (u * z) * hu

/-- The upper branch `(-β + Real.sqrt (β ^ 2 + 4 * ρ)) / 2` of the quadratic formula for
`z ^ 2 + β * z - ρ = 0`. -/
noncomputable def positiveRoot (β ρ : ℝ) : ℝ :=
  (-β + Real.sqrt (β ^ 2 + 4 * ρ)) / 2

/-- The lower branch `(-β - Real.sqrt (β ^ 2 + 4 * ρ)) / 2` of the quadratic formula for
`z ^ 2 + β * z - ρ = 0`. -/
noncomputable def negativeRoot (β ρ : ℝ) : ℝ :=
  (-β - Real.sqrt (β ^ 2 + 4 * ρ)) / 2

theorem roots_equations {β ρ : ℝ} (hρ : 0 ≤ ρ) :
    positiveRoot β ρ ^ 2 + β * positiveRoot β ρ - ρ = 0 ∧
    negativeRoot β ρ ^ 2 + β * negativeRoot β ρ - ρ = 0 := by
  have hsq := Real.sq_sqrt (show 0 ≤ β ^ 2 + 4 * ρ by positivity)
  unfold positiveRoot negativeRoot
  constructor <;> nlinarith

theorem roots_signs {β ρ : ℝ} (hρ : 0 < ρ) :
    0 < positiveRoot β ρ ∧ negativeRoot β ρ < 0 := by
  have hsq := Real.sq_sqrt (show 0 ≤ β ^ 2 + 4 * ρ by positivity)
  have hs := Real.sqrt_nonneg (β ^ 2 + 4 * ρ)
  unfold positiveRoot negativeRoot
  constructor <;> nlinarith

theorem roots_sum_product {β ρ : ℝ} (hρ : 0 ≤ ρ) :
    positiveRoot β ρ + negativeRoot β ρ = -β ∧
      positiveRoot β ρ * negativeRoot β ρ = -ρ := by
  have hsq := Real.sq_sqrt (show 0 ≤ β ^ 2 + 4 * ρ by positivity)
  unfold positiveRoot negativeRoot
  constructor <;> nlinarith

/-- At zero killing rate the desired profile is constant, including double roots. -/
noncomputable def profile (β ρ : ℝ) : ℝ → ℝ :=
  if ρ = 0 then fun _ => 1 else rootProfile (positiveRoot β ρ) (negativeRoot β ρ)

/-- The exact ODE data needed by the comparison calculation. -/
structure ProfileData (β ρ : ℝ) (F : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ F
  equation : ∀ z, deriv (deriv F) z + β * deriv F z - ρ * F z = 0
  value : F 0 = 1
  slope : deriv F 0 = 0
  ge_one : ∀ z, 1 ≤ F z

theorem profile_data {β ρ : ℝ} (hρ : 0 ≤ ρ) : ProfileData β ρ (profile β ρ) := by
  by_cases hz : ρ = 0
  · subst ρ
    simp only [profile, ↓reduceIte]
    refine ⟨by fun_prop, ?_, rfl, by simp, fun _ => le_rfl⟩
    intro z
    simp
  · have hp : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
    obtain ⟨hu, hv⟩ := roots_signs (β := β) hp
    obtain ⟨heu, hev⟩ := roots_equations (β := β) hρ
    simp only [profile, hz, ↓reduceIte]
    exact ⟨rootProfile_smooth _ _, rootProfile_ode heu hev,
      rootProfile_zero (ne_of_gt (hv.trans hu)), rootProfile_deriv_zero _ _,
      rootProfile_ge_one hu hv⟩

namespace ProfileData

variable {β ρ : ℝ} {F : ℝ → ℝ}

theorem hasDeriv (h : ProfileData β ρ F) (z : ℝ) : HasDerivAt F (deriv F z) z :=
  (h.smooth.differentiable (by simp)).differentiableAt.hasDerivAt

theorem hasDeriv_deriv (h : ProfileData β ρ F) (z : ℝ) :
    HasDerivAt (deriv F) (deriv (deriv F) z) z :=
  (((contDiff_infty_iff_deriv.mp h.smooth).2).differentiable
    (by simp)).differentiableAt.hasDerivAt

theorem pos (h : ProfileData β ρ F) (z : ℝ) : 0 < F z := lt_of_lt_of_le zero_lt_one (h.ge_one z)

end ProfileData

/-- The straight-line comparison, with arguments `(log spot, time remaining)`. -/
noncomputable def price (f g : ℝ → ℝ) (c d x t : ℝ) : ℝ :=
  f (x + c * t - d) - Real.exp x * g (x + c * t - d)

variable {k h α c d : ℝ} {f g : ℝ → ℝ}

theorem price_hasDeriv_x (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (x t : ℝ) :
    HasDerivAt (fun y => price f g c d y t)
      (deriv f (x + c * t - d) - Real.exp x *
        (g (x + c * t - d) + deriv g (x + c * t - d))) x := by
  have hz := ((hasDerivAt_id x).add_const (c * t)).sub_const d
  have hd := ((hf.hasDeriv _).comp x hz).sub
    ((Real.hasDerivAt_exp x).mul ((hg.hasDeriv _).comp x hz))
  simp only [id_eq, mul_one, Function.comp_def] at hd
  unfold price
  convert! hd using 1
  ring

theorem price_hasDeriv_t (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (x t : ℝ) :
    HasDerivAt (price f g c d x)
      (c * (deriv f (x + c * t - d) - Real.exp x * deriv g (x + c * t - d))) t := by
  have hz := (((hasDerivAt_id t).const_mul c).const_add x).sub_const d
  have hd := ((hf.hasDeriv _).comp t hz).sub
    (((hg.hasDeriv _).comp t hz).const_mul (Real.exp x))
  simp only [id_eq, mul_one, Function.comp_def] at hd
  unfold price
  convert! hd using 1
  ring

theorem price_deriv2_x (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (x t : ℝ) :
    deriv (deriv (fun y => price f g c d y t)) x =
      deriv (deriv f) (x + c * t - d) - Real.exp x *
        (g (x + c * t - d) + 2 * deriv g (x + c * t - d) +
          deriv (deriv g) (x + c * t - d)) := by
  rw [show deriv (fun y => price f g c d y t) = fun y =>
    deriv f (y + c * t - d) - Real.exp y *
      (g (y + c * t - d) + deriv g (y + c * t - d)) from
        funext (fun y => (price_hasDeriv_x hf hg y t).deriv)]
  have hz := ((hasDerivAt_id x).add_const (c * t)).sub_const d
  have hd := ((hf.hasDeriv_deriv _).comp x hz).sub ((Real.hasDerivAt_exp x).mul
    (((hg.hasDeriv _).comp x hz).add ((hg.hasDeriv_deriv _).comp x hz)))
  simp only [id_eq, Function.comp_def, mul_one, Pi.add_apply] at hd
  convert! hd.deriv using 1
  ring

/-- Step 2: the comparison satisfies the pricing equation exactly. -/
theorem price_equation (hα : α = k - h - 1)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g) (x t : ℝ) :
    deriv (price f g c d x) t =
      deriv (deriv (fun y => price f g c d y t)) x +
        α * deriv (fun y => price f g c d y t) x - k * price f g c d x t := by
  rw [(price_hasDeriv_t hf hg x t).deriv, price_deriv2_x hf hg,
    (price_hasDeriv_x hf hg x t).deriv]
  unfold price
  linear_combination -(hf.equation (x + c * t - d)) +
    Real.exp x * hg.equation (x + c * t - d) +
    Real.exp x * g (x + c * t - d) * hα

theorem price_value_on_line (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (t : ℝ) :
    price f g c d (d - c * t) t = 1 - Real.exp (d - c * t) := by
  simp [price, hf.value, hg.value]

theorem price_smooth_fit_on_line (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (t : ℝ) :
    HasDerivAt (fun x => price f g c d x t) (-Real.exp (d - c * t)) (d - c * t) := by
  convert price_hasDeriv_x hf hg (d - c * t) t using 1
  simp [hf.slope, hg.value, hg.slope]

/-- The excess over the intrinsic expression, in line-relative coordinates. -/
noncomputable def excess (f g : ℝ → ℝ) (ℓ z : ℝ) : ℝ :=
  f z - 1 - Real.exp (ℓ + z) * (g z - 1)

theorem excess_hasDeriv (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (ℓ z : ℝ) :
    HasDerivAt (excess f g ℓ)
      (deriv f z - Real.exp (ℓ + z) * (g z - 1 + deriv g z)) z := by
  convert! ((hf.hasDeriv z).sub_const 1).sub
    ((((hasDerivAt_id z).const_add ℓ).exp).mul ((hg.hasDeriv z).sub_const 1)) using 1
  simp only [id_eq]
  ring

theorem excess_deriv2 (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (ℓ z : ℝ) :
    deriv (deriv (excess f g ℓ)) z = deriv (deriv f) z - Real.exp (ℓ + z) *
      (g z - 1 + 2 * deriv g z + deriv (deriv g) z) := by
  rw [show deriv (excess f g ℓ) = fun y =>
    deriv f y - Real.exp (ℓ + y) * (g y - 1 + deriv g y) from
      funext (fun y => (excess_hasDeriv hf hg ℓ y).deriv)]
  convert! ((hf.hasDeriv_deriv z).sub ((((hasDerivAt_id z).const_add ℓ).exp).mul
    (((hg.hasDeriv z).sub_const 1).add (hg.hasDeriv_deriv z)))).deriv using 1
  simp only [id_eq, mul_one, Pi.add_apply]
  ring

/-- Identity (8), including the sign of the dividend and line-speed terms. -/
theorem excess_equation (hα : α = k - h - 1)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g) (ℓ z : ℝ) :
    deriv (deriv (excess f g ℓ)) z + (α - c) * deriv (excess f g ℓ) z -
      k * excess f g ℓ z =
        k - h * Real.exp (ℓ + z) + c * Real.exp (ℓ + z) * (g z - 1) := by
  rw [excess_deriv2 hf hg, (excess_hasDeriv hf hg ℓ z).deriv]
  unfold excess
  linear_combination hf.equation z - Real.exp (ℓ + z) * hg.equation z +
    Real.exp (ℓ + z) * (1 - g z) * hα

theorem excess_initial (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (ℓ : ℝ) :
    excess f g ℓ 0 = 0 ∧ deriv (excess f g ℓ) 0 = 0 := by
  rw [(excess_hasDeriv hf hg ℓ 0).deriv]
  simp [excess, hf.value, hg.value, hf.slope, hg.slope]

theorem excess_forcing_nonneg (hα : α = k - h - 1)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 ≤ c) {ℓ z : ℝ} (hx : ℓ + z ≤ 0) :
    0 ≤ deriv (deriv (excess f g ℓ)) z + (α - c) * deriv (excess f g ℓ) z -
      k * excess f g ℓ z := by
  rw [excess_equation hα hf hg]
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hx) hh
  have hg₁ := hg.ge_one z
  have hp : 0 ≤ c * Real.exp (ℓ + z) * (g z - 1) := by positivity
  linarith

/-- Step 3 on BOTH sides of the line, proved using integrating factors. -/
theorem excess_nonneg (hα : α = k - h - 1)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 ≤ c)
    {ℓ z : ℝ} (hℓ : ℓ ≤ 0) (hx : ℓ + z ≤ 0) : 0 ≤ excess f g ℓ z := by
  have hfs := hf.smooth
  have hgs := hg.smooth
  have hH : ContDiff ℝ ∞ (excess f g ℓ) := by unfold excess; fun_prop
  obtain ⟨hsum, hprod⟩ := roots_sum_product (β := α - c) (hh.trans hhk)
  obtain ⟨hzero, hslope⟩ := excess_initial hf hg ℓ
  apply ode_nonneg_of_factored_forcing (u := positiveRoot (α - c) k)
    (v := negativeRoot (α - c) k) hH (min_le_left 0 z) (le_max_left 0 z)
      hzero hslope ?_ ⟨min_le_right 0 z, le_max_right 0 z⟩
  intro y hy
  have hxy : ℓ + y ≤ 0 := by
    have hm : max 0 z ≤ -ℓ := max_le (by linarith) (by linarith)
    linarith [hy.2.trans hm]
  rw [hsum, hprod]
  have hforce := excess_forcing_nonneg hα hf hg hh hhk hc hxy
  nlinarith

/-- The comparison dominates the intrinsic expression everywhere below strike. -/
theorem price_dominates_intrinsic (hα : α = k - h - 1)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 ≤ c) (hd : d ≤ 0)
    {x t : ℝ} (ht : 0 ≤ t) (hx : x ≤ 0) : 1 - Real.exp x ≤ price f g c d x t := by
  have hℓ : d - c * t ≤ 0 := by nlinarith [mul_nonneg hc ht]
  have hcoord : d - c * t + (x + c * t - d) = x := by ring
  have hH := excess_nonneg hα hf hg hh hhk hc hℓ (show
    d - c * t + (x + c * t - d) ≤ 0 by rwa [hcoord])
  dsimp [excess] at hH
  rw [hcoord] at hH
  dsimp [price]
  nlinarith

/-- Logarithmic slope; its denominator is strictly positive for these profiles. -/
noncomputable def logSlope (F : ℝ → ℝ) (z : ℝ) : ℝ := deriv F z / F z

theorem logSlope_hasDeriv {β ρ : ℝ} {F : ℝ → ℝ} (hF : ProfileData β ρ F) (z : ℝ) :
    HasDerivAt (logSlope F) (ρ - β * logSlope F z - logSlope F z ^ 2) z := by
  have hn := (hF.pos z).ne'
  convert! (hF.hasDeriv_deriv z).div (hF.hasDeriv z) hn using 1
  dsimp [logSlope]
  field_simp
  linear_combination -F z * hF.equation z

/-- Identity (16) as an actual derivative statement, not just a jet identity. -/
theorem slope_gap_crosses_up (hα : α = k - h - 1)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    {z : ℝ} (hzero : logSlope f z - logSlope g z - 1 = 0) :
    HasDerivAt (fun y => logSlope f y - logSlope g y - 1) c z := by
  convert! ((logSlope_hasDeriv hf z).sub (logSlope_hasDeriv hg z)).sub_const 1 using 1
  have hm : logSlope f z = logSlope g z + 1 := by linarith
  rw [hm, hα]
  ring

theorem slope_gap_initial (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) :
    logSlope f 0 - logSlope g 0 - 1 = -1 := by
  simp [logSlope, hf.slope, hg.slope]

/-- The ratio controlling the shape of the initial difference. -/
noncomputable def initialRatio (f g : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.exp (-z) * f z / g z

theorem initialRatio_pos (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (z : ℝ) : 0 < initialRatio f g z :=
  div_pos (mul_pos (Real.exp_pos _) (hf.pos z)) (hg.pos z)

theorem initialRatio_hasDeriv (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (z : ℝ) :
    HasDerivAt (initialRatio f g)
      (initialRatio f g z * (logSlope f z - logSlope g z - 1)) z := by
  convert! (((hasDerivAt_id z).neg.exp).mul (hf.hasDeriv z)).div
    (hg.hasDeriv z) (hg.pos z).ne' using 1
  dsimp [initialRatio, logSlope]
  field_simp [(hf.pos z).ne', (hg.pos z).ne']
  ring

/-- The positive characteristic exponent of `f` strictly dominates that of
`exp(x) * g`. For `h=0`, use `μ=0` because `g` is constant. -/
theorem positive_root_gap (hα : α = k - h - 1) (hk : 0 < k) (hc : 0 < c)
    {μ : ℝ} (hμ : 0 ≤ μ) (heq : μ ^ 2 + (α + 2 - c) * μ - h = 0) :
    μ + 1 < positiveRoot (α - c) k := by
  have heval : (μ + 1) ^ 2 + (α - c) * (μ + 1) - k = -c := by
    linear_combination heq + hα
  obtain ⟨hsum, hprod⟩ := roots_sum_product (β := α - c) hk.le
  obtain ⟨_, hv⟩ := roots_signs (β := α - c) hk
  have hfactor : (μ + 1 - positiveRoot (α - c) k) *
      (μ + 1 - negativeRoot (α - c) k) = -c := by
    calc
      _ = (μ + 1) ^ 2 - (positiveRoot (α - c) k + negativeRoot (α - c) k) *
        (μ + 1) + positiveRoot (α - c) k * negativeRoot (α - c) k := by ring
      _ = -c := by rw [hsum, hprod]; nlinarith [heval]
  by_contra hn
  have ha : 0 ≤ μ + 1 - positiveRoot (α - c) k := by linarith
  have hb : 0 ≤ μ + 1 - negativeRoot (α - c) k := by linarith
  have hp := mul_nonneg ha hb
  linarith

/-- An explicit comparison function for the physical normalized rates. -/
noncomputable def straightPrice (k h c d : ℝ) : ℝ → ℝ → ℝ :=
  price (profile (k - h - 1 - c) k) (profile (k - h - 1 + 2 - c) h) c d

/-- Step 2 with no profile existence assumptions remaining. -/
theorem straightPrice_equation {k h : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (c d x t : ℝ) :
    deriv (straightPrice k h c d x) t =
      deriv (deriv (fun y => straightPrice k h c d y t)) x +
        (k - h - 1) * deriv (fun y => straightPrice k h c d y t) x -
          k * straightPrice k h c d x t :=
  price_equation rfl (profile_data hk.le) (profile_data hh) x t

theorem straightPrice_fit {k h : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (c d t : ℝ) :
    straightPrice k h c d (d - c * t) t = 1 - Real.exp (d - c * t) ∧
    HasDerivAt (fun x => straightPrice k h c d x t)
      (-Real.exp (d - c * t)) (d - c * t) :=
  ⟨price_value_on_line (profile_data hk.le) (profile_data hh) t,
    price_smooth_fit_on_line (profile_data hk.le) (profile_data hh) t⟩

/-- The zero-dividend comparison has just one nonconstant profile. -/
theorem straightPrice_zero_dividend (k c d x t : ℝ) :
    straightPrice k 0 c d x t = profile (k - 1 - c) k (x + c * t - d) - Real.exp x := by
  simp [straightPrice, price, profile]

theorem straightPrice_dominates {k h c d x t : ℝ}
    (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 ≤ c) (hd : d ≤ 0)
    (ht : 0 ≤ t) (hx : x ≤ 0) :
    1 - Real.exp x ≤ straightPrice k h c d x t :=
  price_dominates_intrinsic rfl (profile_data (hh.trans hhk)) (profile_data hh)
    hh hhk hc hd ht hx

/-- Explicit zero-dividend milestone for the comparison construction. -/
theorem straightPrice_zero_dividend_dominates {k c d x t : ℝ}
    (hk : 0 < k) (hc : 0 ≤ c) (hd : d ≤ 0) (ht : 0 ≤ t) (hx : x ≤ 0) :
    1 - Real.exp x ≤ straightPrice k 0 c d x t :=
  straightPrice_dominates le_rfl hk.le hc hd ht hx

/-- Explicit specialization to Liu's normalized parameter range. This is a
comparison lemma, NOT yet the boundary-convexity theorem in that range. -/
theorem straightPrice_liu_range_dominates {k h c d x t : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) (hc : 0 ≤ c) (hd : d ≤ 0)
    (ht : 0 ≤ t) (hx : x ≤ 0) :
    1 - Real.exp x ≤ straightPrice k h c d x t :=
  straightPrice_dominates hh (by linarith) hc hd ht hx

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
