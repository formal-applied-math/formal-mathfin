/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.StochVol.Heston

/-!
# The Heston Riccati system at complex argument, in the "little Heston trap" branch

`Models/StochVol/Heston` solves the Heston Riccati system at real `u` (the moment transform
`E[e^{u log S_T}]` at the generator/PDE level) in the Möbius form with `e^{+γτ}`. The
characteristic function `E[e^{iω log S_T}]` is the same system at `u = iω`, a complex argument,
where the Möbius form with the principal complex logarithm is the known trap of the literature
(Albrecher et al.): the principal `log` of the denominator can jump as `τ` grows, so the formula
need not be a solution. This file solves the system at **any complex `u`** in the form of
Albrecher–Mayer–Schoutens–Tistaert (the "little Heston trap"), which keeps the logarithm in the
right half plane, and proves that this is a genuine solution.

With `b = κ − ρξu` and `d` a square root of `b² + ξ²(u − u²)`, put `g = (b − d)/(b + d)` and
`E(τ) = e^{−dτ}`. The maturity-time system (the one of `Heston.lean`)

`D' = ½(u² − u) + (ρξu − κ) D + ½ξ² D²`,  `C' = r u + κθ D`,  `D(0) = C(0) = 0`

is solved by

`D(τ) = ((b − d)/ξ²) (1 − E(τ)) / (1 − g E(τ))`,
`C(τ) = r u τ + (κθ/ξ²) [ (b − d) τ − 2 (log(1 − g E(τ)) − log(1 − g)) ]`.

**What has to be assumed, exactly.** The derivative of `D` and of `C` at a time `τ` is proved
under

* `ξ ≠ 0`;
* `d² = b² + ξ²(u − u²)` (`d` is *a* square root of the discriminant; nothing is assumed about
  which one beyond the hypotheses below);
* `b + d ≠ 0` (so that `g` is a quotient and not a junk value);
* `‖g E(τ)‖ < 1` (`hτ`). This is what keeps `1 − g E(τ)` in the right half plane, where `Complex.log`
  is holomorphic: the logarithm is then a genuine antiderivative at `τ`, not a branch accident.

For `τ ≥ 0` the last two follow from two conditions on `(b, d)`, proved here: `Re d ≥ 0` gives
`‖E(τ)‖ ≤ 1`, and `0 < Re(b · conj d)` gives `b + d ≠ 0` and `‖g‖ < 1`
(`hestonTrapG_norm_lt_one`). **That these two conditions hold for the principal square root, for all
Heston parameters and all `u = iω`, is not proved here**; they are carried as hypotheses. In
particular the existence of a root `d` with `Re d ≥ 0` and `0 < Re(b · conj d)` is not established.

At the PDE level, for complex `u` the transform `Φ(t, x, v) = exp(C(T − t) + D(T − t) v + u x)`
satisfies `∂_t Φ + L Φ = 0` for the Heston generator `L` (`hestonGenerator`, on complex-valued test
functions), at every `(t, x, v)` for which the derivative hypothesis holds at `T − t`.

**Not proved.** That `Φ(0, log S₀, v₀)` at `u = iω` is the characteristic function
`E[e^{iω log S_T}]` of a Heston process is **not** proved. It needs a Heston process (existence of
the square-root SDE, unbounded coefficients) and a two-dimensional Itô formula for a correlated
pair, neither of which the library has (`Probability/Brownian/Ito/ItoLemma2D` is the one-factor
time-dependent formula). This module is the generator/PDE level and the ODE level only.

## Main definitions

* `hestonCoeff`: `b = κ − ρξu`.
* `hestonDisc`: the discriminant `b² + ξ²(u − u²)`.
* `hestonTrapG`, `hestonTrapE`: `g = (b − d)/(b + d)` and `E(τ) = e^{−dτ}`.
* `hestonTrapD`, `hestonTrapC`: the trap-form solutions `D`, `C` above.
* `cexpAffine2`: the complex exponential-affine family `e^{A + Bx·x + Bv·v}`.
* `hestonProfileC`, `hestonTrapTransform`: the profile `e^{A(t) + u x + B(t) v}` and the explicit
  transform along `C(T − ·)`, `D(T − ·)`.

## Main results

* `hasDerivAt_hestonTrapD`, `hasDerivAt_hestonTrapC`: the two ODEs, under the hypotheses above.
* `hasDerivAt_hestonTrapD_of_nonneg`, `hasDerivAt_hestonTrapC_of_nonneg`: the same for `τ ≥ 0`
  under `Re d ≥ 0` and `0 < Re(b · conj d)`.
* `hestonTrapD_zero`, `hestonTrapC_zero`: `D(0) = C(0) = 0`, unconditionally.
* `hestonGenerator_cexpAffine2`: the Heston generator on `cexpAffine2`.
* `hestonProfileC_pde`: any solutions `A, B` of the calendar-time Riccati system give a solution of
  `∂_t Φ + L Φ = 0`.
* `hestonTrapTransform_pde`, `hestonTrapTransform_terminal`: the explicit transform solves the
  PDE and equals `e^{u x}` at `t = T`.

## References

* [Albrecher, Mayer, Schoutens, Tistaert, *The little Heston trap*][AlbrecherMayerSchoutensTistaert2007]
* [Heston, *A closed-form solution for options with stochastic volatility with applications to bond
  and currency options*][Heston1993]

## Tags

Heston model, stochastic volatility, affine transform, Riccati equation, characteristic function,
generator PDE, MSC 91G20, MSC 60J60, JEL G13
-/

@[expose] public section

namespace MathFin.Heston

/-! ### The trap-form solutions -/

/-- The mean-reversion coefficient `b = κ − ρξu` of the Heston Riccati equation at complex `u`. -/
noncomputable def hestonCoeff (κ ξ ρ : ℝ) (u : ℂ) : ℂ := κ - ρ * ξ * u

/-- The discriminant `b² + ξ²(u − u²)` of the Heston Riccati equation at complex `u`; its square
roots are the candidates for `d`. -/
noncomputable def hestonDisc (κ ξ ρ : ℝ) (u : ℂ) : ℂ :=
  hestonCoeff κ ξ ρ u ^ 2 + ξ ^ 2 * (u - u ^ 2)

/-- The ratio `g = (b − d)/(b + d)` of the little Heston trap. -/
noncomputable def hestonTrapG (κ ξ ρ : ℝ) (u d : ℂ) : ℂ :=
  (hestonCoeff κ ξ ρ u - d) / (hestonCoeff κ ξ ρ u + d)

/-- The decaying exponential `E(τ) = e^{−dτ}` of the little Heston trap (`Re d ≥ 0`). -/
noncomputable def hestonTrapE (d : ℂ) (τ : ℝ) : ℂ := Complex.exp (-d * τ)

/-- The trap-form solution `D(τ) = ((b − d)/ξ²) (1 − E(τ)) / (1 − g E(τ))` of the `D`-Riccati
equation `D' = ½(u² − u) + (ρξu − κ) D + ½ξ² D²`, `D(0) = 0`. -/
noncomputable def hestonTrapD (κ ξ ρ : ℝ) (u d : ℂ) (τ : ℝ) : ℂ :=
  (hestonCoeff κ ξ ρ u - d) / ξ ^ 2
    * ((1 - hestonTrapE d τ) / (1 - hestonTrapG κ ξ ρ u d * hestonTrapE d τ))

/-- The trap-form solution
`C(τ) = r u τ + (κθ/ξ²) [ (b − d) τ − 2 (log(1 − g E(τ)) − log(1 − g)) ]` of `C' = r u + κθ D`,
`C(0) = 0`. The two logarithms are of numbers in the right half plane exactly when
`‖g E(τ)‖ < 1` and `‖g‖ < 1`; the constant `log(1 − g)` makes `C(0) = 0` without a quotient. -/
noncomputable def hestonTrapC (r κ θ ξ ρ : ℝ) (u d : ℂ) (τ : ℝ) : ℂ :=
  r * u * τ + κ * θ / ξ ^ 2
    * ((hestonCoeff κ ξ ρ u - d) * τ
        - 2 * (Complex.log (1 - hestonTrapG κ ξ ρ u d * hestonTrapE d τ)
          - Complex.log (1 - hestonTrapG κ ξ ρ u d)))

/-- Initial datum of the `D`-flow: `D(0) = 0` (no hypothesis). -/
theorem hestonTrapD_zero (κ ξ ρ : ℝ) (u d : ℂ) : hestonTrapD κ ξ ρ u d 0 = 0 := by
  simp [hestonTrapD, hestonTrapE]

/-- Initial datum of the `C`-flow: `C(0) = 0` (no hypothesis). -/
theorem hestonTrapC_zero (r κ θ ξ ρ : ℝ) (u d : ℂ) : hestonTrapC r κ θ ξ ρ u d 0 = 0 := by
  simp [hestonTrapC, hestonTrapE]

/-! ### The hypotheses `‖g E‖ < 1` -/

private theorem one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have := Complex.re_le_norm z
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private theorem trap_ratio_norm_lt_one {b d : ℂ} (h : 0 < b.re * d.re + b.im * d.im) :
    b + d ≠ 0 ∧ ‖(b - d) / (b + d)‖ < 1 := by
  have hsq : ‖b - d‖ ^ 2 < ‖b + d‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    nlinarith
  have hlt : ‖b - d‖ < ‖b + d‖ := by
    by_contra hge
    push_neg at hge
    nlinarith [mul_nonneg (sub_nonneg.2 hge) (add_nonneg (norm_nonneg (b - d)) (norm_nonneg (b + d)))]
  have hne : b + d ≠ 0 := fun h0 => by
    have := norm_nonneg (b - d)
    rw [h0, norm_zero] at hlt
    linarith
  exact ⟨hne, by rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hne)).mpr hlt⟩

/-- **The trap ratio is a contraction.** If `0 < Re(b · conj d) = b.re d.re + b.im d.im` for
`b = κ − ρξu`, then `b + d ≠ 0` and `‖g‖ < 1`. -/
theorem hestonTrapG_norm_lt_one {κ ξ ρ : ℝ} {u d : ℂ}
    (h : 0 < (hestonCoeff κ ξ ρ u).re * d.re + (hestonCoeff κ ξ ρ u).im * d.im) :
    hestonCoeff κ ξ ρ u + d ≠ 0 ∧ ‖hestonTrapG κ ξ ρ u d‖ < 1 :=
  trap_ratio_norm_lt_one h

/-- **The trap exponential keeps `g E` a contraction.** If `‖g‖ < 1` and `Re d ≥ 0`, then
`‖g E(τ)‖ < 1` for every `τ ≥ 0`. -/
theorem norm_hestonTrapG_mul_E_lt_one {κ ξ ρ : ℝ} {u d : ℂ} {τ : ℝ}
    (hg : ‖hestonTrapG κ ξ ρ u d‖ < 1) (hre : 0 ≤ d.re) (hτ : 0 ≤ τ) :
    ‖hestonTrapG κ ξ ρ u d * hestonTrapE d τ‖ < 1 := by
  have hE : ‖hestonTrapE d τ‖ ≤ 1 := by
    rw [hestonTrapE, Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith [mul_nonneg hre hτ]
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hE (norm_nonneg _)) (by rwa [mul_one])

/-! ### The Riccati ODEs (abstract algebra, then the concrete statements) -/

/-- The `D`-ODE in abstract variables: `b = (1 + g) s / 2`, `d = (1 − g) s / 2` encode
`g = (b − d)/(b + d)` with `s = b + d`, and `w` stands for `u² − u`, tied to the discriminant by
`ξ² w = b² − d²`. -/
private theorem hasDerivAt_trapD_abstract (b d g s ξ w : ℂ) (τ : ℝ) (hξ : ξ ≠ 0)
    (hb : b = (1 + g) * s / 2) (hd : d = (1 - g) * s / 2) (hw : ξ ^ 2 * w = b ^ 2 - d ^ 2)
    (hM : 1 - g * Complex.exp (-d * τ) ≠ 0) :
    HasDerivAt (fun y : ℝ ↦
        (b - d) / ξ ^ 2 * ((1 - Complex.exp (-d * y)) / (1 - g * Complex.exp (-d * y))))
      (w / 2 + -b * ((b - d) / ξ ^ 2
          * ((1 - Complex.exp (-d * τ)) / (1 - g * Complex.exp (-d * τ))))
        + ξ ^ 2 / 2 * ((b - d) / ξ ^ 2
          * ((1 - Complex.exp (-d * τ)) / (1 - g * Complex.exp (-d * τ)))) ^ 2) τ := by
  have hE : HasDerivAt (fun y : ℝ ↦ Complex.exp (-d * (y : ℂ)))
      (Complex.exp (-d * (τ : ℂ)) * (-d * 1)) τ :=
    ((hasDerivAt_id' τ).ofReal_comp.const_mul (-d)).cexp
  have hN : HasDerivAt (fun y : ℝ ↦ 1 - Complex.exp (-d * (y : ℂ)))
      (-(Complex.exp (-d * (τ : ℂ)) * (-d * 1))) τ := hE.const_sub 1
  have hMd : HasDerivAt (fun y : ℝ ↦ 1 - g * Complex.exp (-d * (y : ℂ)))
      (-(g * (Complex.exp (-d * (τ : ℂ)) * (-d * 1)))) τ :=
    (hE.const_mul g).const_sub 1
  refine ((hN.fun_div hMd hM).const_mul ((b - d) / ξ ^ 2)).congr_deriv ?_
  have hw' : w = (b ^ 2 - d ^ 2) / ξ ^ 2 :=
    (eq_div_iff (pow_ne_zero 2 hξ)).2 ((mul_comm w (ξ ^ 2)).trans hw)
  beta_reduce
  generalize Complex.exp (-d * (τ : ℂ)) = E at hM ⊢
  subst hw' hb hd
  first
    | (field_simp; ring)
    | field_simp

/-- The `C`-ODE in abstract variables (`a = r u`, `kk = κθ`), same encoding as
`hasDerivAt_trapD_abstract`. -/
private theorem hasDerivAt_trapC_abstract (b d g s ξ a kk : ℂ) (τ : ℝ) (hξ : ξ ≠ 0)
    (hb : b = (1 + g) * s / 2) (hd : d = (1 - g) * s / 2)
    (hMs : 1 - g * Complex.exp (-d * τ) ∈ Complex.slitPlane) :
    HasDerivAt (fun y : ℝ ↦ a * y + kk / ξ ^ 2 * ((b - d) * y
        - 2 * (Complex.log (1 - g * Complex.exp (-d * y)) - Complex.log (1 - g))))
      (a + kk * ((b - d) / ξ ^ 2
        * ((1 - Complex.exp (-d * τ)) / (1 - g * Complex.exp (-d * τ))))) τ := by
  have hM : 1 - g * Complex.exp (-d * (τ : ℂ)) ≠ 0 := Complex.slitPlane_ne_zero hMs
  have hE : HasDerivAt (fun y : ℝ ↦ Complex.exp (-d * (y : ℂ)))
      (Complex.exp (-d * (τ : ℂ)) * (-d * 1)) τ :=
    ((hasDerivAt_id' τ).ofReal_comp.const_mul (-d)).cexp
  have hMd : HasDerivAt (fun y : ℝ ↦ 1 - g * Complex.exp (-d * (y : ℂ)))
      (-(g * (Complex.exp (-d * (τ : ℂ)) * (-d * 1)))) τ :=
    (hE.const_mul g).const_sub 1
  have hlog := hMd.clog_real hMs
  have hlin1 : HasDerivAt (fun y : ℝ ↦ a * (y : ℂ)) (a * 1) τ :=
    (hasDerivAt_id' τ).ofReal_comp.const_mul a
  have hlin2 : HasDerivAt (fun y : ℝ ↦ (b - d) * (y : ℂ)) ((b - d) * 1) τ :=
    (hasDerivAt_id' τ).ofReal_comp.const_mul (b - d)
  have hlg := (hlog.sub_const (Complex.log (1 - g))).const_mul 2
  refine (hlin1.fun_add ((hlin2.fun_sub hlg).const_mul (kk / ξ ^ 2))).congr_deriv ?_
  beta_reduce
  generalize Complex.exp (-d * (τ : ℂ)) = E at hM ⊢
  subst hb hd
  first
    | (field_simp; ring)
    | field_simp

/-- **The `D` Riccati ODE at complex `u`.** Let `d` be a square root of the discriminant
(`d² = b² + ξ²(u − u²)`) with `b + d ≠ 0`, and let `τ` be such that `‖g E(τ)‖ < 1`. Then the
trap-form `D` has derivative
`½(u² − u) + (ρξu − κ) D(τ) + ½ξ² D(τ)²` at `τ`, the equation of `hasDerivAt_hestonBv` with `u`
complex. -/
theorem hasDerivAt_hestonTrapD (κ ξ ρ : ℝ) (u d : ℂ) (τ : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hbd : hestonCoeff κ ξ ρ u + d ≠ 0)
    (hτ : ‖hestonTrapG κ ξ ρ u d * hestonTrapE d τ‖ < 1) :
    HasDerivAt (hestonTrapD κ ξ ρ u d)
      ((u ^ 2 - u) / 2 + (ρ * ξ * u - κ) * hestonTrapD κ ξ ρ u d τ
        + ξ ^ 2 / 2 * hestonTrapD κ ξ ρ u d τ ^ 2) τ := by
  have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
  have hMs := one_sub_mem_slitPlane_of_norm_lt_one hτ
  have hgs : hestonTrapG κ ξ ρ u d * (hestonCoeff κ ξ ρ u + d) = hestonCoeff κ ξ ρ u - d := by
    unfold hestonTrapG
    field_simp
  have hw : (ξ : ℂ) ^ 2 * (u ^ 2 - u) = hestonCoeff κ ξ ρ u ^ 2 - d ^ 2 := by
    rw [hestonDisc] at hd
    linear_combination hd
  have key := hasDerivAt_trapD_abstract (hestonCoeff κ ξ ρ u) d (hestonTrapG κ ξ ρ u d)
    (hestonCoeff κ ξ ρ u + d) (ξ : ℂ) (u ^ 2 - u) τ hξ'
    (by linear_combination (-1 / 2 : ℂ) * hgs) (by linear_combination (1 / 2 : ℂ) * hgs) hw
    (Complex.slitPlane_ne_zero hMs)
  refine key.congr_deriv ?_
  simp only [hestonCoeff, hestonTrapD, hestonTrapE, hestonTrapG]
  ring

/-- **The `C` ODE at complex `u`.** Under the hypotheses of `hasDerivAt_hestonTrapD`, the trap-form
`C` has derivative `r u + κθ D(τ)` at `τ` — the equation of `hasDerivAt_hestonA` with `u`
complex, the logarithm being a genuine antiderivative because `1 − g E(τ)` lies in the right half
plane. -/
theorem hasDerivAt_hestonTrapC (r κ θ ξ ρ : ℝ) (u d : ℂ) (τ : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hbd : hestonCoeff κ ξ ρ u + d ≠ 0)
    (hτ : ‖hestonTrapG κ ξ ρ u d * hestonTrapE d τ‖ < 1) :
    HasDerivAt (hestonTrapC r κ θ ξ ρ u d)
      (r * u + κ * θ * hestonTrapD κ ξ ρ u d τ) τ := by
  have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
  have hMs := one_sub_mem_slitPlane_of_norm_lt_one hτ
  have hgs : hestonTrapG κ ξ ρ u d * (hestonCoeff κ ξ ρ u + d) = hestonCoeff κ ξ ρ u - d := by
    unfold hestonTrapG
    field_simp
  have key := hasDerivAt_trapC_abstract (hestonCoeff κ ξ ρ u) d (hestonTrapG κ ξ ρ u d)
    (hestonCoeff κ ξ ρ u + d) (ξ : ℂ) ((r : ℂ) * u) ((κ : ℂ) * θ) τ hξ'
    (by linear_combination (-1 / 2 : ℂ) * hgs) (by linear_combination (1 / 2 : ℂ) * hgs) hMs
  refine key.congr_deriv ?_
  simp only [hestonCoeff, hestonTrapD, hestonTrapE, hestonTrapG]
  ring

/-- `hasDerivAt_hestonTrapD` for `τ ≥ 0`, from the two conditions on `(b, d)`:
`Re d ≥ 0` and `0 < Re(b · conj d)`. -/
theorem hasDerivAt_hestonTrapD_of_nonneg (κ ξ ρ : ℝ) (u d : ℂ) (τ : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hre : 0 ≤ d.re)
    (hang : 0 < (hestonCoeff κ ξ ρ u).re * d.re + (hestonCoeff κ ξ ρ u).im * d.im)
    (hτ : 0 ≤ τ) :
    HasDerivAt (hestonTrapD κ ξ ρ u d)
      ((u ^ 2 - u) / 2 + (ρ * ξ * u - κ) * hestonTrapD κ ξ ρ u d τ
        + ξ ^ 2 / 2 * hestonTrapD κ ξ ρ u d τ ^ 2) τ :=
  have h := hestonTrapG_norm_lt_one hang
  hasDerivAt_hestonTrapD κ ξ ρ u d τ hξ hd h.1 (norm_hestonTrapG_mul_E_lt_one h.2 hre hτ)

/-- `hasDerivAt_hestonTrapC` for `τ ≥ 0`, from the two conditions on `(b, d)`:
`Re d ≥ 0` and `0 < Re(b · conj d)`. -/
theorem hasDerivAt_hestonTrapC_of_nonneg (r κ θ ξ ρ : ℝ) (u d : ℂ) (τ : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hre : 0 ≤ d.re)
    (hang : 0 < (hestonCoeff κ ξ ρ u).re * d.re + (hestonCoeff κ ξ ρ u).im * d.im)
    (hτ : 0 ≤ τ) :
    HasDerivAt (hestonTrapC r κ θ ξ ρ u d)
      (r * u + κ * θ * hestonTrapD κ ξ ρ u d τ) τ :=
  have h := hestonTrapG_norm_lt_one hang
  hasDerivAt_hestonTrapC r κ θ ξ ρ u d τ hξ hd h.1 (norm_hestonTrapG_mul_E_lt_one h.2 hre hτ)

/-! ### The complex exponential-affine family and the Heston generator -/

/-- The complex exponential-affine family `(x, v) ↦ e^{A + Bx·x + Bv·v}` of a real log-spot `x` and
a real variance `v`, with complex coefficients: the complex-coefficient companion of
`expAffine2`. -/
noncomputable def cexpAffine2 (A Bx Bv : ℂ) (x v : ℝ) : ℂ := Complex.exp (A + Bx * x + Bv * v)

/-- `y ↦ e^{c + k y}` has derivative `k e^{c + k y}`, for `y` real and `c, k` complex. -/
theorem hasDerivAt_cexp_lin (c k : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp (c + k * y)) (Complex.exp (c + k * y) * k) y := by
  have h : HasDerivAt (fun y : ℝ ↦ c + k * (y : ℂ)) (k * 1) y :=
    ((hasDerivAt_id' y).ofReal_comp.const_mul k).const_add c
  exact h.cexp.congr_deriv (by simp only [mul_one])

/-- ∂_x of the complex family: `Bx · E`. -/
theorem hasDerivAt_cexpAffine2_x (A Bx Bv : ℂ) (x v : ℝ) :
    HasDerivAt (fun y : ℝ ↦ cexpAffine2 A Bx Bv y v) (Bx * cexpAffine2 A Bx Bv x v) x := by
  have h := hasDerivAt_cexp_lin (A + Bv * v) Bx x
  have e : ∀ y : ℝ, cexpAffine2 A Bx Bv y v = Complex.exp (A + Bv * v + Bx * y) := fun y ↦ by
    simp only [cexpAffine2]
    congr 1
    ring
  have hf : (fun y : ℝ ↦ cexpAffine2 A Bx Bv y v)
      = fun y : ℝ ↦ Complex.exp (A + Bv * v + Bx * y) := funext e
  rw [hf]
  refine h.congr_deriv ?_
  rw [e x]
  exact mul_comm _ _

/-- ∂_v of the complex family: `Bv · E`. -/
theorem hasDerivAt_cexpAffine2_v (A Bx Bv : ℂ) (x v : ℝ) :
    HasDerivAt (cexpAffine2 A Bx Bv x) (Bv * cexpAffine2 A Bx Bv x v) v :=
  (hasDerivAt_cexp_lin (A + Bx * x) Bv v).congr_deriv (mul_comm _ _)

/-- ∂_x of the complex family (function form). -/
theorem deriv_cexpAffine2_x (A Bx Bv : ℂ) (v : ℝ) :
    deriv (fun y : ℝ ↦ cexpAffine2 A Bx Bv y v) = fun y ↦ Bx * cexpAffine2 A Bx Bv y v :=
  funext fun y ↦ (hasDerivAt_cexpAffine2_x A Bx Bv y v).deriv

/-- ∂_v of the complex family (function form). -/
theorem deriv_cexpAffine2_v (A Bx Bv : ℂ) (x : ℝ) :
    deriv (cexpAffine2 A Bx Bv x) = fun w ↦ Bv * cexpAffine2 A Bx Bv x w :=
  funext fun w ↦ (hasDerivAt_cexpAffine2_v A Bx Bv x w).deriv

/-- ∂_xx of the complex family (function form): `Bx² · E`. -/
theorem deriv_deriv_cexpAffine2_x (A Bx Bv : ℂ) (v : ℝ) :
    deriv (deriv (fun y : ℝ ↦ cexpAffine2 A Bx Bv y v))
      = fun y ↦ Bx ^ 2 * cexpAffine2 A Bx Bv y v := by
  rw [deriv_cexpAffine2_x]
  funext y
  exact (((hasDerivAt_cexpAffine2_x A Bx Bv y v).const_mul Bx).deriv).trans (by ring)

/-- ∂_vv of the complex family (function form): `Bv² · E`. -/
theorem deriv_deriv_cexpAffine2_v (A Bx Bv : ℂ) (x : ℝ) :
    deriv (deriv (cexpAffine2 A Bx Bv x)) = fun w ↦ Bv ^ 2 * cexpAffine2 A Bx Bv x w := by
  rw [deriv_cexpAffine2_v]
  funext w
  exact (((hasDerivAt_cexpAffine2_v A Bx Bv x w).const_mul Bv).deriv).trans (by ring)

/-- The mixed derivative ∂_v∂_x of the complex family (function form): `Bx·Bv · E`. -/
theorem deriv_cexpAffine2_xv (A Bx Bv : ℂ) (x : ℝ) :
    deriv (fun w : ℝ ↦ deriv (fun y : ℝ ↦ cexpAffine2 A Bx Bv y w) x)
      = fun w ↦ Bx * Bv * cexpAffine2 A Bx Bv x w := by
  have hfun : ∀ w : ℝ, deriv (fun y : ℝ ↦ cexpAffine2 A Bx Bv y w) x
      = Bx * cexpAffine2 A Bx Bv x w :=
    fun w ↦ (hasDerivAt_cexpAffine2_x A Bx Bv x w).deriv
  simp only [hfun]
  funext w
  exact (((hasDerivAt_cexpAffine2_v A Bx Bv x w).const_mul Bx).deriv).trans (by ring)

/-- **The Heston generator on the complex family.** For complex coefficients `A, Bx, Bv`,

`L E = ((r·Bx + κθ·Bv) + (Bx²/2 + ρξ·Bx·Bv + ξ²Bv²/2 − κBv − Bx/2)·v) · E`,

the complex counterpart of `hestonGenerator_expAffine2` (`hestonGenerator` takes values in any real
normed space). -/
theorem hestonGenerator_cexpAffine2 (r κ θ ξ ρ : ℝ) (A Bx Bv : ℂ) :
    hestonGenerator r κ θ ξ ρ (cexpAffine2 A Bx Bv)
      = fun x v ↦ ((r * Bx + κ * θ * Bv)
          + (Bx ^ 2 / 2 + ρ * ξ * Bx * Bv + ξ ^ 2 / 2 * Bv ^ 2 - κ * Bv - Bx / 2) * v)
          * Complex.exp (A + Bx * x + Bv * v) := by
  funext x v
  simp only [hestonGenerator, Complex.real_smul]
  rw [deriv_deriv_cexpAffine2_x A Bx Bv v, deriv_deriv_cexpAffine2_v A Bx Bv x,
    deriv_cexpAffine2_xv A Bx Bv x, deriv_cexpAffine2_x A Bx Bv v,
    deriv_cexpAffine2_v A Bx Bv x]
  simp only [cexpAffine2]
  push_cast
  ring

/-! ### The PDE at complex `u` -/

/-- The candidate transform profile `Φ(t, x, v) = e^{A(t) + u x + B(t) v}` at complex `u`. -/
noncomputable def hestonProfileC (u : ℂ) (A B : ℝ → ℂ) (t x v : ℝ) : ℂ :=
  Complex.exp (A t + u * x + B t * v)

/-- **The PDE verification at complex `u`** (the complex counterpart of `hestonProfile_pde`, with
the Riccati hypotheses at the single time `t`). If `A, B` have, at `t`, the derivatives of the
calendar-time Heston Riccati system

`B' = u/2 − u²/2 + (κ − ρξu)B − (ξ²/2)B²`,  `A' = −r u − κθ B`,

then `∂_t Φ + L Φ = 0` at `(t, x, v)`, for `L = hestonGenerator r κ θ ξ ρ`. -/
theorem hestonProfileC_pde (r κ θ ξ ρ : ℝ) (u : ℂ) (A B : ℝ → ℂ) (t x v : ℝ)
    (hB : HasDerivAt B (u / 2 - u ^ 2 / 2 + κ * B t - ρ * ξ * u * B t - ξ ^ 2 / 2 * B t ^ 2) t)
    (hA : HasDerivAt A (-(r * u) - κ * θ * B t) t) :
    deriv (fun s ↦ hestonProfileC u A B s x v) t
      + hestonGenerator r κ θ ξ ρ (hestonProfileC u A B t) x v = 0 := by
  have hinner : HasDerivAt (fun s : ℝ ↦ A s + u * x + B s * v)
      (-(r * u) - κ * θ * B t
        + (u / 2 - u ^ 2 / 2 + κ * B t - ρ * ξ * u * B t - ξ ^ 2 / 2 * B t ^ 2) * v) t :=
    ((hA.fun_add (hasDerivAt_const t (u * (x : ℂ)))).fun_add
      (hB.mul_const (v : ℂ))).congr_deriv (by ring)
  have htime := hinner.cexp.deriv
  show deriv (fun s : ℝ ↦ Complex.exp (A s + u * x + B s * v)) t
      + hestonGenerator r κ θ ξ ρ (cexpAffine2 (A t) u (B t)) x v = 0
  rw [htime, hestonGenerator_cexpAffine2]
  ring

/-- **Calendar-time `D`-flow at complex `u`.** Under the hypotheses of `hasDerivAt_hestonTrapD` at
the maturity time `T − t`, `w ↦ D(T − w)` has derivative
`u/2 − u²/2 + (κ − ρξu) D − (ξ²/2) D²` at `t`. -/
theorem hasDerivAt_hestonTrapDCalendar (κ ξ ρ : ℝ) (u d : ℂ) (T t : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hbd : hestonCoeff κ ξ ρ u + d ≠ 0)
    (hτ : ‖hestonTrapG κ ξ ρ u d * hestonTrapE d (T - t)‖ < 1) :
    HasDerivAt (fun w : ℝ ↦ hestonTrapD κ ξ ρ u d (T - w))
      (u / 2 - u ^ 2 / 2 + κ * hestonTrapD κ ξ ρ u d (T - t)
        - ρ * ξ * u * hestonTrapD κ ξ ρ u d (T - t)
        - ξ ^ 2 / 2 * hestonTrapD κ ξ ρ u d (T - t) ^ 2) t := by
  have hts : HasDerivAt (fun w : ℝ ↦ T - w) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hcomp := (hasDerivAt_hestonTrapD κ ξ ρ u d (T - t) hξ hd hbd hτ).scomp t hts
  refine hcomp.congr_deriv ?_
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **Calendar-time `C`-flow at complex `u`.** Under the same hypotheses, `w ↦ C(T − w)` has
derivative `−r u − κθ D(T − t)` at `t`. -/
theorem hasDerivAt_hestonTrapCCalendar (r κ θ ξ ρ : ℝ) (u d : ℂ) (T t : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hbd : hestonCoeff κ ξ ρ u + d ≠ 0)
    (hτ : ‖hestonTrapG κ ξ ρ u d * hestonTrapE d (T - t)‖ < 1) :
    HasDerivAt (fun w : ℝ ↦ hestonTrapC r κ θ ξ ρ u d (T - w))
      (-(r * u) - κ * θ * hestonTrapD κ ξ ρ u d (T - t)) t := by
  have hts : HasDerivAt (fun w : ℝ ↦ T - w) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hcomp := (hasDerivAt_hestonTrapC r κ θ ξ ρ u d (T - t) hξ hd hbd hτ).scomp t hts
  refine hcomp.congr_deriv ?_
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The **explicit Heston transform at complex `u`**: `hestonProfileC` along the trap-form flows
`C(T − ·)`, `D(T − ·)`, i.e. `Φ(t, x, v) = exp(C(T − t) + D(T − t) v + u x)`. -/
noncomputable def hestonTrapTransform (r κ θ ξ ρ : ℝ) (u d : ℂ) (T t x v : ℝ) : ℂ :=
  hestonProfileC u (fun w ↦ hestonTrapC r κ θ ξ ρ u d (T - w))
    (fun w ↦ hestonTrapD κ ξ ρ u d (T - w)) t x v

/-- **The Heston PDE at complex `u`.** For `ξ ≠ 0`, a square root `d` of the discriminant with
`b + d ≠ 0`, and a time `t` at which `‖g E(T − t)‖ < 1` (for `t ≤ T` this holds under
`Re d ≥ 0` and `0 < Re(b · conj d)`, by `hestonTrapG_norm_lt_one` and
`norm_hestonTrapG_mul_E_lt_one`), the explicit transform satisfies `∂_t Φ + L Φ = 0` at
`(t, x, v)`. -/
theorem hestonTrapTransform_pde (r κ θ ξ ρ : ℝ) (u d : ℂ) (T t x v : ℝ) (hξ : ξ ≠ 0)
    (hd : d ^ 2 = hestonDisc κ ξ ρ u) (hbd : hestonCoeff κ ξ ρ u + d ≠ 0)
    (hτ : ‖hestonTrapG κ ξ ρ u d * hestonTrapE d (T - t)‖ < 1) :
    deriv (fun s ↦ hestonTrapTransform r κ θ ξ ρ u d T s x v) t
      + hestonGenerator r κ θ ξ ρ (hestonTrapTransform r κ θ ξ ρ u d T t) x v = 0 :=
  hestonProfileC_pde r κ θ ξ ρ u (fun w ↦ hestonTrapC r κ θ ξ ρ u d (T - w))
    (fun w ↦ hestonTrapD κ ξ ρ u d (T - w)) t x v
    (hasDerivAt_hestonTrapDCalendar κ ξ ρ u d T t hξ hd hbd hτ)
    (hasDerivAt_hestonTrapCCalendar r κ θ ξ ρ u d T t hξ hd hbd hτ)

/-- Terminal condition of the explicit transform: `Φ(T, x, v) = e^{u x}` (no hypothesis, since
`C(0) = D(0) = 0`). -/
theorem hestonTrapTransform_terminal (r κ θ ξ ρ : ℝ) (u d : ℂ) (T x v : ℝ) :
    hestonTrapTransform r κ θ ξ ρ u d T T x v = Complex.exp (u * x) := by
  simp [hestonTrapTransform, hestonProfileC, hestonTrapC_zero, hestonTrapD_zero]

end MathFin.Heston
