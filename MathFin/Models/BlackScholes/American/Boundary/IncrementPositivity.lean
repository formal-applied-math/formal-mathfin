/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Models.BlackScholes.American.Boundary.TimeIncrement
public import MathFin.Models.BlackScholes.American.Boundary.StrongPositivity

/-!
# Strict positivity of actual price increments

Above strike, positivity propagates directly from expiry. On a hypothetical
flat boundary tail, this supplies a positive seed and then positivity at every
interior point at each later time. Smooth fit still forces a zero derivative
at any boundary shared by the two time slices.

## Main results

* `incrementGauge_pos_above_strike`: for a `DividendPutSolution`, `δ > 0`, `x > 0` and `t > 0`,
  `incrementGauge p k h δ x t` is strictly positive.
* `incrementGauge_pos_on_flat_tail`: if `b` is constant on `[A, ∞)` with `A > 0`, then
  `incrementGauge p k h δ x t > 0` for `δ > 0`, `x > b A` and `t > A`.
* `incrementGauge_fit_of_same_boundary`: if `b (t + δ) = b t` with `0 ≤ δ` and `t > 0`, then
  `incrementGauge p k h δ` vanishes at `b t` and has zero spatial derivative there.

## Tags

time increment, strict positivity, flat tail, smooth fit, price increment, MSC 35R35, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution

open Set Comparison
open scoped Topology ContDiff

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem incrementGauge_pos_above_strike (hp : DividendPutSolution k h p b)
    {δ x t : ℝ} (hδ : 0 < δ) (hx : 0 < x) (ht : 0 < t) :
    0 < incrementGauge p k h δ x t := by
  obtain ⟨M,hM⟩ := incrementDrift_bounded (h := h) hp.rate_pos
  apply positive_later_of_positive_point (U := incrementGauge p k h δ)
    (D := fun x _ => incrementDrift k h x) (β := 0) (a := 0) (x := x) (M := M) ht hx hx
    ((hp.incrementGauge_continuousOn hδ.le).mono (fun _ hz => hz.2.1))
  · intro z s hz hs _
    exact hp.incrementGauge_contDiffAt hδ.le hs ((hp.boundary_nonpos hs).trans_lt hz)
  · intro z s hz hs _
    exact hp.incrementGauge_equation hδ.le hs ((hp.boundary_nonpos hs).trans_lt hz)
  · intro z _ _ _ _
    exact hM z
  · intro z s _ hs _
    exact hp.incrementGauge_nonneg hδ.le hs z
  · exact hp.incrementGauge_initial_pos hδ hx

theorem incrementGauge_pos_on_flat_tail (hp : DividendPutSolution k h p b)
    {δ A x t : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hflat : ∀ s, A ≤ s → b s = b A) (hx : b A < x) (ht : A < t) :
    0 < incrementGauge p k h δ x t := by
  obtain ⟨M,hM⟩ := incrementDrift_bounded (h := h) hp.rate_pos
  apply positive_later_of_positive_point (U := incrementGauge p k h δ)
    (D := fun x _ => incrementDrift k h x) (β := b A) (a := A) (x := 1) (M := M)
    ht (by linarith [hp.boundary_nonpos hA]) hx
    ((hp.incrementGauge_continuousOn hδ.le).mono (fun _ hz => hA.le.trans hz.2.1))
  · intro z s hz hs _
    exact hp.incrementGauge_contDiffAt hδ.le (hA.trans hs) (by rwa [hflat s hs.le])
  · intro z s hz hs _
    exact hp.incrementGauge_equation hδ.le (hA.trans hs) (by rwa [hflat s hs.le])
  · intro z _ _ _ _
    exact hM z
  · intro z s _ hs _
    exact hp.incrementGauge_nonneg hδ.le (hA.le.trans hs) z
  · exact hp.incrementGauge_pos_above_strike hδ (by norm_num) hA

theorem incrementGauge_fit_of_same_boundary (hp : DividendPutSolution k h p b)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (heq : b (t + δ) = b t) :
    incrementGauge p k h δ (b t) t = 0 ∧
      HasDerivAt (fun x => incrementGauge p k h δ x t) 0 (b t) := by
  have htδ := add_pos_of_pos_of_nonneg ht hδ
  have hval : timeIncrement p δ (b t) t = 0 := by
    unfold timeIncrement
    rw [hp.exercise (b t) (t+δ) htδ (by rw [heq]),hp.exercise (b t) t ht le_rfl,sub_self]
  have hd₀ := hp.price_hasDerivAt_boundary ht
  have hd₁ := hp.price_hasDerivAt_boundary htδ
  rw [heq] at hd₁
  have hf := profile_data (β := k-h-1) hp.rate_pos.le
  refine ⟨by simp [incrementGauge,hval],?_⟩
  have hnum : HasDerivAt (timeIncrement p δ · t) 0 (b t) := by
    convert! hd₁.sub hd₀ using 1
    simp
  convert! hnum.div (hf.hasDeriv (b t)) (hf.pos (b t)).ne' using 1
  rw [hval]
  simp

end MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution
