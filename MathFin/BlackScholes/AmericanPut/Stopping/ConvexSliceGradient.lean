/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Init
public import Mathlib.Analysis.Convex.Deriv

/-! # Joint continuity of the gradient of differentiable convex slices

Joint continuity of function values and differentiability of every convex
spatial slice imply joint continuity of the spatial derivatives. Fixed-endpoint
secants bound the derivative near each point.

## Main results

* `continuousAt_deriv_convex_slices`: if every positive-time slice of `f` is convex on `[0, ∞)`
  and differentiable in space on `S > 0`, and `f` is jointly continuous there, then the spatial
  derivative `(S, t) ↦ deriv (f · t) S` is jointly continuous at each `(S, t)` with `S, t > 0`.

## Tags

convex slices, gradient continuity, joint continuity, secant bounds, spatial derivative, MSC 35R35,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter
open scoped Topology

theorem continuousAt_deriv_convex_slices {f : ℝ → ℝ → ℝ}
    (hc : ∀ t, 0 < t → ConvexOn ℝ (Ici 0) (fun S => f S t))
    (hd : ∀ S t, 0 < S → 0 < t → DifferentiableAt ℝ (fun R => f R t) S)
    (hp : ∀ S t, 0 < S → 0 < t → ContinuousAt (fun z : ℝ × ℝ => f z.1 z.2) (S,t))
    {S t : ℝ} (hS : 0 < S) (ht : 0 < t) :
    ContinuousAt (fun z : ℝ × ℝ => deriv (fun R => f R z.2) z.1) (S,t) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hs := (hd S t hS ht).hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE S)
    have hpos : ∀ᶠ L in 𝓝 S, 0 < L := Ioi_mem_nhds hS
    have hnear : ∀ᶠ L in 𝓝[<] S, 0 < L ∧ L < S ∧ a < slope (fun R => f R t) S L := by
      filter_upwards [hpos.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin,hs.eventually (Ioi_mem_nhds ha)] with L hL hLS hsl
      exact ⟨hL,hLS,hsl⟩
    obtain ⟨L,hL,hLS,hsl⟩ := hnear.exists
    rw [slope_comm] at hsl
    have hm : ContinuousAt (fun z : ℝ × ℝ => (L,z.2)) (S,t) := by fun_prop
    have hfixed : ContinuousAt (fun z : ℝ × ℝ => f L z.2) (S,t) := by
      simpa only [Function.comp_def] using
        (hp L t hL ht).comp (f := fun z : ℝ × ℝ => (L,z.2)) hm
    have hsec : ContinuousAt (fun z : ℝ × ℝ => slope (fun R => f R z.2) L z.1) (S,t) := by
      simp only [slope,vsub_eq_sub,smul_eq_mul,← div_eq_inv_mul]
      exact ((hp S t hS ht).sub hfixed).div (continuousAt_fst.sub continuousAt_const)
        (sub_ne_zero.mpr hLS.ne')
    filter_upwards [hsec.preimage_mem_nhds (Ioi_mem_nhds hsl),
      continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds hLS),
      continuousAt_snd.preimage_mem_nhds (Ioi_mem_nhds ht)] with z hlow hzS hzt
    have hSz : 0 < z.1 := hL.trans hzS
    exact hlow.trans_le ((hc z.2 hzt).slope_le_deriv hL.le hSz.le hzS (hd z.1 z.2 hSz hzt))
  · intro a ha
    have hs := (hd S t hS ht).hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE S)
    have hnear : ∀ᶠ R in 𝓝[>] S, S < R ∧ slope (fun U => f U t) S R < a := by
      filter_upwards [self_mem_nhdsWithin,hs.eventually (Iio_mem_nhds ha)] with R hR hsl
      exact ⟨hR,hsl⟩
    obtain ⟨R,hSR,hsl⟩ := hnear.exists
    have hR : 0 < R := hS.trans hSR
    have hm : ContinuousAt (fun z : ℝ × ℝ => (R,z.2)) (S,t) := by fun_prop
    have hfixed : ContinuousAt (fun z : ℝ × ℝ => f R z.2) (S,t) := by
      simpa only [Function.comp_def] using
        (hp R t hR ht).comp (f := fun z : ℝ × ℝ => (R,z.2)) hm
    have hsec : ContinuousAt (fun z : ℝ × ℝ => slope (fun U => f U z.2) z.1 R) (S,t) := by
      simp only [slope,vsub_eq_sub,smul_eq_mul,← div_eq_inv_mul]
      exact (hfixed.sub (hp S t hS ht)).div (continuousAt_const.sub continuousAt_fst)
        (sub_ne_zero.mpr hSR.ne')
    filter_upwards [hsec.preimage_mem_nhds (Iio_mem_nhds hsl),
      continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds hS),
      continuousAt_fst.preimage_mem_nhds (Iio_mem_nhds hSR),
      continuousAt_snd.preimage_mem_nhds (Ioi_mem_nhds ht)] with z hu hz0 hzR hzt
    change 0 < z.1 at hz0
    exact ((hc z.2 hzt).deriv_le_slope hz0.le hR.le hzR (hd z.1 z.2 hz0 hzt)).trans_lt hu

end MathFin.BlackScholes.AmericanPut.Stopping
