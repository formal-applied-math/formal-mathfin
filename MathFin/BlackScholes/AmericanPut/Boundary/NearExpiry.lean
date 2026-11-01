/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ExpiryBarrier

/-!
# The near-expiry ratio limit from the pricing contract

A deliberately crude square-root lower bound on the price suffices. At
`x=-sqrt(t)/64` it exceeds intrinsic value, forcing that point into the
continuation region. No boundary monotonicity or convexity is used.

## Result

Public entry points include `exists_boundary_sqrt_bound`, `boundary_below_linear_eventually`,
`boundary_ratio_tendsto_atBot`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology

namespace DividendPutSolution

/-- A quantitative, non-sharp square-root bound sufficient for tangent
intercept selection. The existence of its time window is proved. -/
theorem exists_boundary_sqrt_bound {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, 0 < t → t ≤ T → b t < -Real.sqrt t / 64 := by
  obtain ⟨T,hT,hbound⟩ := hp.exists_expiryBarrier_window
  refine ⟨T,hT,?_⟩
  intro t ht htT
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  let x := -Real.sqrt t / 64
  have hx : x ≤ 0 := by dsimp [x]; linarith
  have hxl : -Real.sqrt t ≤ x := by dsimp [x]; linarith
  have hxr : x ≤ Real.sqrt t := hx.trans hs.le
  have hprice : Real.sqrt t / 16 ≤ p x t :=
    (expiryBarrier_ge_sqrt ht hx).trans
      (hbound (x,t) ⟨ht.le,htT,hxl,hxr⟩)
  have hpayoff : 1 - Real.exp x ≤ Real.sqrt t / 64 := by
    have hexp := Real.add_one_le_exp x
    dsimp [x] at *
    linarith
  by_contra hn
  have hxb : x ≤ b t := le_of_not_gt hn
  rw [hp.exercise x t ht hxb] at hprice
  linarith

/-- Every fixed line through the origin lies in continuation
at sufficiently small positive times. -/
theorem boundary_below_linear_eventually {k h : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (hp : DividendPutSolution k h p b)
    (M : ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ), b t < -M*t := by
  obtain ⟨T,hT,hbound⟩ := hp.exists_boundary_sqrt_bound
  have hc : Continuous (fun t : ℝ => 64*M*Real.sqrt t) := by fun_prop
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 64*M*Real.sqrt t < 1 :=
    nhdsWithin_le_nhds (hc.continuousAt.eventually (Iio_mem_nhds (by norm_num)))
  filter_upwards [hsmall,nhdsWithin_le_nhds (Iio_mem_nhds hT),self_mem_nhdsWithin] with t hsm htT ht
  have htpos : 0 < t := ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hh := mul_lt_mul_of_pos_right hsm hs
  have hs2 := Real.sq_sqrt htpos.le
  have hMt : M*t < Real.sqrt t/64 := by
    nlinarith [congrArg (fun y : ℝ => M*y) hs2]
  exact (hbound t htpos htT.le).trans (by linarith)

/-- Step 1's expiry input, proved directly from the pricing-solution
contract. This is not an assumed European-price asymptotic. -/
theorem boundary_ratio_tendsto_atBot {k h : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (hp : DividendPutSolution k h p b) :
    Tendsto (fun t => b t/t) (𝓝[>] 0) atBot := by
  apply tendsto_atBot.mpr
  intro a
  filter_upwards [hp.boundary_below_linear_eventually (|a|+1),self_mem_nhdsWithin] with t hb ht
  have hratio : b t/t < -(|a|+1) := (div_lt_iff₀ (show 0 < t from ht)).mpr hb
  have ha : -(|a|+1) ≤ a := by linarith [neg_abs_le a]
  exact hratio.le.trans ha

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
