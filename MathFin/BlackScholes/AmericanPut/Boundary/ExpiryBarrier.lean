/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ObstacleComparison

/-!
# A shrinking-strip subsolution for the expiry estimate

This explicit quadratic in space is used only on `|x| ≤ sqrt t`.
Its strip collapses to `(0,0)`, where it is continuous relative to the strip.
No European pricing formula is required.

## Result

Public entry points include `expiryBarrier`, `expiryBarrier_hasDeriv_x`, `expiryBarrier_deriv2_x`,
`expiryBarrier_hasDeriv_t`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- The expiry barrier `(Real.sqrt t - x) ^ 2 / (16 * Real.sqrt t)`: a spatial quadratic
vanishing at `x = Real.sqrt t`. -/
noncomputable def expiryBarrier (x t : ℝ) : ℝ :=
  (Real.sqrt t - x)^2 / (16 * Real.sqrt t)

@[simp] theorem expiryBarrier_zero (x : ℝ) : expiryBarrier x 0 = 0 := by
  simp [expiryBarrier]

theorem expiryBarrier_hasDeriv_x (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y => expiryBarrier y t) ((x - Real.sqrt t) / (8 * Real.sqrt t)) x := by
  have hs := Real.sqrt_pos.mpr ht
  convert! (((hasDerivAt_const x (Real.sqrt t)).sub (hasDerivAt_id x)).pow 2).div_const
    (16 * Real.sqrt t) using 1
  dsimp
  field_simp
  ring

theorem expiryBarrier_deriv2_x (x : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (fun y => expiryBarrier y t)) x = 1 / (8 * Real.sqrt t) := by
  have he : deriv (fun y => expiryBarrier y t) = fun y => (y-Real.sqrt t)/(8*Real.sqrt t) :=
    funext (fun y => (expiryBarrier_hasDeriv_x y ht).deriv)
  rw [he]
  exact ((hasDerivAt_id x).sub_const (Real.sqrt t) |>.div_const (8*Real.sqrt t)).deriv

theorem expiryBarrier_hasDeriv_t (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (expiryBarrier x)
      ((1 - x^2/t) / (32 * Real.sqrt t)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 := Real.sq_sqrt ht.le
  have hd := Real.hasDerivAt_sqrt ht.ne'
  convert! ((hd.sub_const x).pow 2).div (hd.const_mul 16) (by positivity) using 1
  dsimp
  field_simp
  nlinarith [congrArg (fun y : ℝ => x^2*y) hs2]

theorem expiryBarrier_contDiffAt {x t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => expiryBarrier z.1 z.2) (x,t) := by
  unfold expiryBarrier
  fun_prop (disch := positivity)

theorem expiryBarrier_contDiff_x (t : ℝ) :
    ContDiff ℝ 2 (fun x => expiryBarrier x t) := by
  unfold expiryBarrier
  fun_prop

theorem expiryBarrier_bounds {x t : ℝ} (ht : 0 ≤ t)
    (hl : -Real.sqrt t ≤ x) (hr : x ≤ Real.sqrt t) :
    0 ≤ expiryBarrier x t ∧ expiryBarrier x t ≤ Real.sqrt t / 4 := by
  rcases eq_or_lt_of_le ht with he | he
  · simp [← he]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr he
  constructor
  · unfold expiryBarrier
    positivity
  · unfold expiryBarrier
    apply (div_le_iff₀ (show 0 < 16 * Real.sqrt t by positivity)).mpr
    nlinarith [sq_nonneg (Real.sqrt t + x)]

theorem expiryBarrier_ge_sqrt {x t : ℝ} (ht : 0 < t) (hx : x ≤ 0) :
    Real.sqrt t / 16 ≤ expiryBarrier x t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  unfold expiryBarrier
  apply (le_div_iff₀ (show 0 < 16*Real.sqrt t by positivity)).mpr
  nlinarith [sq_nonneg x]

theorem expiryBarrier_continuousOn (T : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => expiryBarrier z.1 z.2)
      (twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T) := by
  intro z hz
  rcases eq_or_lt_of_le hz.1 with he | he
  · have hb : ∀ᶠ w in 𝓝[twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T] z,
        0 ≤ expiryBarrier w.1 w.2 ∧ expiryBarrier w.1 w.2 ≤ Real.sqrt w.2 / 4 := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact expiryBarrier_bounds hw.1 hw.2.2.1 hw.2.2.2
    have hlim : Tendsto (fun w : ℝ × ℝ => Real.sqrt w.2 / 4)
        (𝓝[twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T] z) (𝓝 0) := by
      have hc : Continuous (fun w : ℝ × ℝ => Real.sqrt w.2 / 4) := by fun_prop
      simpa [← he] using hc.continuousAt.tendsto.mono_left
        (show 𝓝[twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T] z ≤ 𝓝 z from nhdsWithin_le_nhds)
    change Tendsto _ _ (𝓝 (expiryBarrier z.1 z.2))
    rw [← he,expiryBarrier_zero]
    exact squeeze_zero' (hb.mono (fun _ hw => hw.1)) (hb.mono (fun _ hw => hw.2)) hlim
  · exact (expiryBarrier_contDiffAt he).continuousAt.continuousWithinAt

theorem expiryBarrier_left {t : ℝ} (ht : 0 ≤ t) :
    expiryBarrier (-Real.sqrt t) t = Real.sqrt t / 4 := by
  rcases eq_or_lt_of_le ht with he | he
  · simp [← he]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr he
  unfold expiryBarrier
  field_simp
  ring

@[simp] theorem expiryBarrier_right (t : ℝ) : expiryBarrier (Real.sqrt t) t = 0 := by
  simp [expiryBarrier]

/-- The left edge is below intrinsic value for times at most one. -/
theorem expiryBarrier_left_le_payoff {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    expiryBarrier (-Real.sqrt t) t ≤ putPayoff (-Real.sqrt t) := by
  rw [expiryBarrier_left ht]
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := by nlinarith [Real.sq_sqrt ht]
  have hexp := Real.add_one_le_exp (Real.sqrt t)
  have hproduct : (1+Real.sqrt t)*Real.exp (-Real.sqrt t) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-Real.sqrt t)).le
    simpa [← Real.exp_add,add_comm] using hh
  have hexple : Real.exp (-Real.sqrt t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hbound : Real.sqrt t / 4 ≤ 1 - Real.exp (-Real.sqrt t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hexple)]
  exact hbound.trans (le_max_left _ _)

/-- For sufficiently small times the diffusion term dominates drift and
killing on the whole shrinking strip. This is an actual derivative inequality. -/
theorem expiryBarrier_subsolution {k h x t : ℝ} (hk : 0 ≤ k)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hsmall : (|k - h - 1| + k) * Real.sqrt t ≤ 1 / 4)
    (hl : -Real.sqrt t ≤ x) (hr : x ≤ Real.sqrt t) :
    deriv (expiryBarrier x) t ≤ dividendSpatialOperator k h (fun y => expiryBarrier y t) x := by
  let s := Real.sqrt t
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hs1 : s ≤ 1 := by dsimp [s]; nlinarith [Real.sq_sqrt ht.le]
  have hdxlo : -(1/4 : ℝ) ≤ (x-s)/(8*s) := by
    apply (le_div_iff₀ (show 0 < 8*s by positivity)).mpr
    dsimp [s] at *
    linarith
  have hdxhi : (x-s)/(8*s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hdrift : -|k-h-1|/4 ≤ (k-h-1)*((x-s)/(8*s)) := by
    by_cases hb : 0 ≤ k-h-1
    · rw [abs_of_nonneg hb]
      nlinarith
    · have hp := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hb) hdxhi
      have ha : 0 ≤ |k-h-1| := abs_nonneg _
      linarith
  have hdt : (1-x^2/t)/(32*s) ≤ 1/(32*s) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh : 0 ≤ x^2/t := div_nonneg (sq_nonneg x) ht.le
    linarith
  have hprice := expiryBarrier_bounds ht.le hl hr
  have hkprice : k*expiryBarrier x t ≤ k*s/4 := by nlinarith [hprice.2]
  have hkss : k*s^2 ≤ k*s := by
    have hss : 0 ≤ s-s^2 := by nlinarith
    nlinarith [mul_nonneg hk hss]
  have hgap : 1/(32*s) ≤ 1/(8*s) - |k-h-1|/4 - k*s/4 := by
    apply (div_le_iff₀ (show 0 < 32*s by positivity)).mpr
    have he : (1/(8*s) - |k-h-1|/4 - k*s/4)*(32*s) =
        4 - 8*|k-h-1| * s - 8*k*s^2 := by field_simp; ring
    rw [he]
    change (|k-h-1|+k)*s ≤ 1/4 at hsmall
    nlinarith
  unfold dividendSpatialOperator
  rw [(expiryBarrier_hasDeriv_t x ht).deriv, expiryBarrier_deriv2_x x ht,
    (expiryBarrier_hasDeriv_x x ht).deriv]
  change (1-x^2/t)/(32*s) ≤ 1/(8*s) + (k-h-1)*((x-s)/(8*s)) - k*expiryBarrier x t
  linarith

namespace DividendPutSolution

/-- The explicit shrinking-strip barrier is below the price on every
sufficiently short strip. All comparison hypotheses are discharged here. -/
theorem expiryBarrier_le_price {k h T : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (hT1 : T ≤ 1)
    (hsmall : (|k - h - 1| + k) * Real.sqrt T ≤ 1 / 4) :
    ∀ z ∈ twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T,
      expiryBarrier z.1 z.2 ≤ p z.1 z.2 := by
  have hL : Continuous (fun t : ℝ => -Real.sqrt t) := Real.continuous_sqrt.neg
  have hR : Continuous Real.sqrt := Real.continuous_sqrt
  apply hp.obstacle_comparison hL hR
    (twoSidedStrip_isCompact hL hR (fun t _ => by linarith [Real.sqrt_nonneg t]))
    (expiryBarrier_continuousOn T)
    (fun t _ _ => expiryBarrier_contDiff_x t)
    (fun _ _ ht _ _ _ => expiryBarrier_contDiffAt ht)
  · intro x t ht htT hl hr
    apply expiryBarrier_subsolution hp.rate_pos.le ht (htT.trans hT1) _ hl.le hr.le
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htT)
      (add_nonneg (abs_nonneg _) hp.rate_pos.le)).trans hsmall
  · intro x _ _
    simpa using hp.nonneg x (t := 0) le_rfl
  · intro t ht htT
    exact (expiryBarrier_left_le_payoff ht (htT.trans hT1)).trans (hp.dominates _ t ht)
  · intro t ht _
    simpa using hp.nonneg (Real.sqrt t) ht

/-- There is a genuine positive time window on which this price lower bound
holds. The small-time restriction is constructed by continuity, not assumed. -/
theorem exists_expiryBarrier_window {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T,
      expiryBarrier z.1 z.2 ≤ p z.1 z.2 := by
  have hc : Continuous (fun t : ℝ => (|k-h-1|+k)*Real.sqrt t) := by fun_prop
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), (|k-h-1|+k)*Real.sqrt t < 1/4 :=
    nhdsWithin_le_nhds (hc.continuousAt.eventually (Iio_mem_nhds (by norm_num)))
  obtain ⟨a,ha,hall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp he
  let T := min a 1 / 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hTa : T < a := by dsimp [T]; linarith [min_le_left a 1]
  have hT1 : T ≤ 1 := by dsimp [T]; linarith [min_le_right a 1]
  exact ⟨T,hT,hp.expiryBarrier_le_price hT1 (hall ⟨hT,hTa⟩).le⟩

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
