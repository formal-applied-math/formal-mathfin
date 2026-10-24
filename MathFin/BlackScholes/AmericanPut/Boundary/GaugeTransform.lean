/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonShape

/-!
# The positive-solution gauge transformation

Dividing a pricing-equation solution by the positive line profile removes the
zero-order term. Smoothness is required only locally at the point in question,
not across the exercise boundary or at expiry.

## Result

Public entry points include `deriv2_mul_at`, `shiftedProfile_hasDeriv_x`, `shiftedProfile_deriv2_x`,
`shiftedProfile_hasDeriv_t`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open scoped ContDiff

theorem deriv2_mul_at {F G : ℝ → ℝ} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G x) :
    deriv (deriv (fun y => F y * G y)) x =
      deriv (deriv F) x * G x + 2 * deriv F x * deriv G x + F x * deriv (deriv G) x := by
  have hi := iteratedDeriv_mul (n := 2) hF hG
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ] at hi
  convert! hi using 1
  ring

variable {α k c d : ℝ} {f : ℝ → ℝ}

theorem shiftedProfile_hasDeriv_x (hf : ProfileData (α - c) k f) (x t : ℝ) :
    HasDerivAt (fun y => f (y + c * t - d)) (deriv f (x + c * t - d)) x := by
  simpa only [id_eq, mul_one, Function.comp_def] using
    (hf.hasDeriv _).comp x (((hasDerivAt_id x).add_const (c * t)).sub_const d)

theorem shiftedProfile_deriv2_x (hf : ProfileData (α - c) k f) (x t : ℝ) :
    deriv (deriv (fun y => f (y + c * t - d))) x = deriv (deriv f) (x + c * t - d) := by
  rw [show deriv (fun y => f (y + c * t - d)) = fun y => deriv f (y + c * t - d) from
    funext (fun y => (shiftedProfile_hasDeriv_x hf y t).deriv)]
  simpa only [id_eq, mul_one, Function.comp_def] using
    ((hf.hasDeriv_deriv _).comp x (((hasDerivAt_id x).add_const (c * t)).sub_const d)).deriv

theorem shiftedProfile_hasDeriv_t (hf : ProfileData (α - c) k f) (x t : ℝ) :
    HasDerivAt (fun s => f (x + c * s - d)) (c * deriv f (x + c * t - d)) t := by
  convert! (hf.hasDeriv _).comp t
    ((((hasDerivAt_id t).const_mul c).const_add x).sub_const d) using 1
  simp only [id_eq]
  ring

/-- The quotient of `u` by the shifted profile, `u x t / f (x + c * t - d)`. -/
noncomputable def gauge (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (c d x t : ℝ) : ℝ :=
  u x t / f (x + c * t - d)

/-- An actual partial-derivative identity for the quotient, with NO zero-order
term. The numerator need only solve the pricing equation at this point. -/
theorem gauge_equation {u : ℝ → ℝ → ℝ} {x t : ℝ}
    (hf : ProfileData (α - c) k f)
    (hux : ContDiffAt ℝ 2 (fun y => u y t) x)
    (hut : DifferentiableAt ℝ (u x) t)
    (heq : deriv (u x) t = deriv (deriv (fun y => u y t)) x +
      α * deriv (fun y => u y t) x - k * u x t) :
    deriv (gauge u f c d x) t =
      deriv (deriv (fun y => gauge u f c d y t)) x +
        (α + 2 * deriv f (x + c * t - d) / f (x + c * t - d)) *
          deriv (fun y => gauge u f c d y t) x := by
  have hfs : ContDiff ℝ 2 f := hf.smooth.of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hFs : ContDiffAt ℝ 2 (fun y => f (y + c * t - d)) x := by fun_prop
  have hVx : ContDiffAt ℝ 2 (fun y => gauge u f c d y t) x :=
    hux.div hFs (hf.pos _).ne'
  have hVt : DifferentiableAt ℝ (gauge u f c d x) t :=
    hut.div (shiftedProfile_hasDeriv_t hf x t).differentiableAt (hf.pos _).ne'
  have hprod (y s : ℝ) : u y s = f (y + c * s - d) * gauge u f c d y s := by
    dsimp [gauge]
    field_simp [(hf.pos _).ne']
  have hprodX : (fun y => u y t) = fun y => f (y + c * t - d) * gauge u f c d y t :=
    funext (fun y => hprod y t)
  have hprodT : u x = fun s => f (x + c * s - d) * gauge u f c d x s :=
    funext (hprod x)
  have hx₁ : deriv (fun y => u y t) x =
      deriv f (x + c * t - d) * gauge u f c d x t +
        f (x + c * t - d) * deriv (fun y => gauge u f c d y t) x := by
    rw [hprodX]
    exact ((shiftedProfile_hasDeriv_x hf x t).mul
      (hVx.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hx₂ : deriv (deriv (fun y => u y t)) x =
      deriv (deriv f) (x + c * t - d) * gauge u f c d x t +
        2 * deriv f (x + c * t - d) * deriv (fun y => gauge u f c d y t) x +
          f (x + c * t - d) * deriv (deriv (fun y => gauge u f c d y t)) x := by
    rw [hprodX, deriv2_mul_at hFs hVx, (shiftedProfile_hasDeriv_x hf x t).deriv,
      shiftedProfile_deriv2_x hf]
  have ht₁ : deriv (u x) t =
      c * deriv f (x + c * t - d) * gauge u f c d x t +
        f (x + c * t - d) * deriv (gauge u f c d x) t := by
    rw [hprodT]
    exact ((shiftedProfile_hasDeriv_t hf x t).mul hVt.hasDerivAt).deriv
  rw [hx₁, hx₂, ht₁, hprod x t] at heq
  field_simp [(hf.pos (x + c * t - d)).ne']
  linear_combination heq + gauge u f c d x t * hf.equation (x + c * t - d)

/-- Subtracting a constant preserves a no-zero-order parabolic equation. -/
theorem constant_shift_equation {v : ℝ → ℝ → ℝ} {β x t ε : ℝ}
    (hvx : ContDiffAt ℝ 2 (fun y => v y t) x)
    (hvt : DifferentiableAt ℝ (v x) t)
    (heq : deriv (v x) t = deriv (deriv (fun y => v y t)) x +
      β * deriv (fun y => v y t) x) :
    deriv (fun s => v x s - ε) t =
      deriv (deriv (fun y => v y t - ε)) x + β * deriv (fun y => v y t - ε) x := by
  rw [hvt.hasDerivAt.sub_const ε |>.deriv,
    (hvx.differentiableAt (by norm_num)).hasDerivAt.sub_const ε |>.deriv]
  have h₂ : deriv (deriv (fun y => v y t - ε)) x = deriv (deriv (fun y => v y t)) x := by
    simp
  rw [h₂]
  exact heq

theorem price_joint_smooth {h : ℝ} {g : ℝ → ℝ}
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => price f g c d z.1 z.2) := by
  have hfs := hf.smooth
  have hgs := hg.smooth
  unfold price
  fun_prop

theorem normalizedDifference_contDiffAt {h : ℝ} {p : ℝ → ℝ → ℝ} {b g : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b)
    (hf : ProfileData (k - h - 1 - c) k f)
    (hg : ProfileData (k - h - 1 + 2 - c) h g)
    {x t : ℝ} (ht : 0 < t) (hx : b t < x) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => normalizedDifference p f g c d z.1 z.2) (x, t) := by
  have hps := hp.price_contDiffAt ht hx
  have hqs := (price_joint_smooth (d := d) hf hg).contDiffAt (x := (x, t))
  have hfs := hf.smooth
  have hden : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => f (z.1 + c * z.2 - d)) (x, t) := by
    fun_prop
  exact (hps.sub hqs).div hden (hf.pos _).ne'

/-- Continuity includes the initial kink; differentiability there is not needed. -/
theorem normalizedDifference_continuousOn {h : ℝ} {p : ℝ → ℝ → ℝ} {b g : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b)
    (hf : ProfileData (k - h - 1 - c) k f)
    (hg : ProfileData (k - h - 1 + 2 - c) h g) :
    ContinuousOn (fun z : ℝ × ℝ => normalizedDifference p f g c d z.1 z.2)
      {z | 0 ≤ z.2} := by
  have hfs := hf.smooth.continuous
  have hden : Continuous (fun z : ℝ × ℝ => f (z.1 + c * z.2 - d)) := by fun_prop
  exact (hp.price_continuous.sub (price_joint_smooth hf hg).continuous.continuousOn).div
    hden.continuousOn (fun z _ => (hf.pos (z.1 + c * z.2 - d)).ne')

/-- The epsilon-shift is strictly negative in a relative neighborhood of the
expiry corner. This supplies the corner-sign part of zero-count initialization,
not the still-open positive-time count itself. -/
theorem normalizedDifference_negative_near_corner {h ε : ℝ}
    {p : ℝ → ℝ → ℝ} {b g : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b)
    (hf : ProfileData (k - h - 1 - c) k f)
    (hg : ProfileData (k - h - 1 + 2 - c) h g)
    (hc : 0 ≤ c) (hd : d ≤ 0) (hε : 0 < ε) :
    ∀ᶠ z : ℝ × ℝ in nhdsWithin (0, 0) {z | 0 ≤ z.2},
      normalizedDifference p f g c d z.1 z.2 - ε < 0 := by
  have hp0 : p 0 0 = 0 := by rw [hp.initial]; norm_num [putPayoff]
  have hq0 := price_dominates_intrinsic (x := 0) (t := 0) rfl hf hg
    hp.dividend_nonneg hp.dividend_le_rate hc hd le_rfl le_rfl
  have hv0 : normalizedDifference p f g c d 0 0 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg ?_ (hf.pos _).le
    rw [hp0]
    norm_num only [Real.exp_zero, sub_self] at hq0
    linarith
  have hcont := ((normalizedDifference_continuousOn (d := d) hp hf hg) (0, 0)
    (show (0 : ℝ) ≤ 0 from le_rfl)).sub_const ε
  exact hcont.eventually (Iio_mem_nhds (show normalizedDifference p f g c d 0 0 - ε < 0 by
    linarith))

/-- Equation (12) for the ACTUAL pricing-solution difference, at each interior
point of the continuation region. No extra PDE premise or global regularity
of the payoff-extended price is needed. -/
theorem normalizedDifference_equation {h : ℝ} {p : ℝ → ℝ → ℝ} {b g : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b)
    (hf : ProfileData (k - h - 1 - c) k f)
    (hg : ProfileData (k - h - 1 + 2 - c) h g)
    {x t : ℝ} (ht : 0 < t) (hx : b t < x) :
    deriv (normalizedDifference p f g c d x) t =
      deriv (deriv (fun y => normalizedDifference p f g c d y t)) x +
        (k - h - 1 + 2 * deriv f (x + c * t - d) / f (x + c * t - d)) *
          deriv (fun y => normalizedDifference p f g c d y t) x := by
  have hps : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => p z.1 z.2) (x, t) :=
    (hp.price_contDiffAt ht hx).of_le (WithTop.coe_le_coe.mpr le_top)
  have hqs : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => price f g c d z.1 z.2) (x, t) :=
    ((price_joint_smooth hf hg).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hpx : ContDiffAt ℝ 2 (fun y => p y t) x := by
    simpa only [Function.comp_def] using
      hps.comp (f := fun y : ℝ => (y, t)) x (by fun_prop)
  have hqx : ContDiffAt ℝ 2 (fun y => price f g c d y t) x := by
    simpa only [Function.comp_def] using
      hqs.comp (f := fun y : ℝ => (y, t)) x (by fun_prop)
  have hpt : DifferentiableAt ℝ (p x) t :=
    (hps.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x, s)) t by fun_prop)).differentiableAt
      (by norm_num)
  have hqt : DifferentiableAt ℝ (price f g c d x) t :=
    (price_hasDeriv_t hf hg x t).differentiableAt
  apply gauge_equation (u := fun y s => p y s - price f g c d y s) (d := d)
    (x := x) (t := t) hf (hpx.sub hqx) (hpt.sub hqt)
  have h₂ : deriv (deriv (fun y => p y t - price f g c d y t)) x =
      deriv (deriv (fun y => p y t)) x - deriv (deriv (fun y => price f g c d y t)) x := by
    simpa [iteratedDeriv_succ] using iteratedDeriv_fun_sub (n := 2) hpx hqx
  rw [deriv_fun_sub hpt hqt, h₂,
    deriv_fun_sub (hpx.differentiableAt (by norm_num)) (hqx.differentiableAt (by norm_num))]
  have hpeq := hp.equation x t ht hx
  dsimp [dividendSpatialOperator] at hpeq
  have hqeq := price_equation (d := d) rfl hf hg x t
  linarith

theorem normalizedDifference_shifted_equation {h ε : ℝ}
    {p : ℝ → ℝ → ℝ} {b g : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b)
    (hf : ProfileData (k - h - 1 - c) k f)
    (hg : ProfileData (k - h - 1 + 2 - c) h g)
    {x t : ℝ} (ht : 0 < t) (hx : b t < x) :
    deriv (fun s => normalizedDifference p f g c d x s - ε) t =
      deriv (deriv (fun y => normalizedDifference p f g c d y t - ε)) x +
        (k - h - 1 + 2 * deriv f (x + c * t - d) / f (x + c * t - d)) *
          deriv (fun y => normalizedDifference p f g c d y t - ε) x := by
  have hs : ContDiffAt ℝ 2
      (fun z : ℝ × ℝ => normalizedDifference p f g c d z.1 z.2) (x, t) :=
    (normalizedDifference_contDiffAt hp hf hg ht hx).of_le (WithTop.coe_le_coe.mpr le_top)
  apply constant_shift_equation (v := normalizedDifference p f g c d) (ε := ε)
    (hs.comp (f := fun y : ℝ => (y, t)) x (by fun_prop))
    ((hs.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x, s)) t by fun_prop)).differentiableAt
      (by norm_num))
  exact normalizedDifference_equation hp hf hg ht hx

/-- The strictly negative moving-boundary data needed after subtracting epsilon. -/
theorem normalizedDifference_boundary_neg {h : ℝ} {p : ℝ → ℝ → ℝ} {b g : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b)
    (hf : ProfileData (k - h - 1 - c) k f)
    (hg : ProfileData (k - h - 1 + 2 - c) h g)
    (hc : 0 ≤ c) (hd : d ≤ 0) {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    normalizedDifference p f g c d (b t) t - ε < 0 := by
  have hbound := price_dominates_intrinsic rfl hf hg hp.dividend_nonneg
    hp.dividend_le_rate hc hd ht.le (hp.boundary_nonpos ht)
  have hn : p (b t) t - price f g c d (b t) t ≤ 0 := by
    rw [hp.exercise (b t) t ht le_rfl]
    linarith
  have hv : normalizedDifference p f g c d (b t) t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hn (hf.pos _).le
  linarith

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
