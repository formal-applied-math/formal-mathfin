/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.MaturityContinuity
public import Mathlib.Analysis.Convex.Continuous

/-! # Joint spot/maturity continuity, derived from the stopping supremum 
## Result

Public entry points include `americanPutValue_uniform_spot_lipschitz`,
`americanPutValue_joint_continuousAt`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ} {K r q σ : ℝ}

theorem americanPutValue_uniform_spot_lipschitz (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) {S : ℝ} (hS : 0 < S) (T : ℝ≥0) :
    LipschitzOnWith (2*K/(S/4)).toNNReal (fun y => americanPutValue P 𝓕 W K r q σ y T)
      (ball S (S/4)) := by
  have hsub : ball S (S/2) ⊆ Ici 0 := by
    intro y hy
    have hh := (abs_lt.mp (show |y-S| < S/2 by simpa only [mem_ball,Real.dist_eq] using hy)).1
    change 0 ≤ y
    linarith
  have hc := (value_convexOn_spot (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hK hr).subset hsub (convex_ball S (S/2))
  have hl := hc.lipschitzOnWith_of_abs_le (show 0 < S/4 by positivity) (M := K) (by
    intro y hy
    have hy0 : 0 ≤ y := hsub hy
    rw [abs_of_nonneg (value_nonneg hW hK hr hy0)]
    exact value_le_strike hW hK hr hy0)
  simpa only [show S/2-S/4 = S/4 by ring] using hl

theorem americanPutValue_joint_continuousAt (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 ≤ K) (hr : 0 ≤ r) {S : ℝ} (hS : 0 < S) (T : ℝ≥0) :
    ContinuousAt (fun z : ℝ × ℝ≥0 => americanPutValue P 𝓕 W K r q σ z.1 z.2) (S,T) := by
  let L := (2*K/(S/4)).toNNReal
  have hnear : ∀ᶠ z : ℝ × ℝ≥0 in 𝓝 (S,T), z.1 ∈ ball S (S/4) :=
    continuousAt_fst (ball_mem_nhds S (by positivity))
  have hboundlim : Tendsto (fun z : ℝ × ℝ≥0 => (L : ℝ)*dist z.1 S) (𝓝 (S,T)) (𝓝 0) := by
    have hh : Continuous (fun z : ℝ × ℝ≥0 => (L : ℝ)*dist z.1 S) := by fun_prop
    simpa only [dist_self,mul_zero] using hh.tendsto (S,T)
  have herr : Tendsto (fun z : ℝ × ℝ≥0 =>
      americanPutValue P 𝓕 W K r q σ z.1 z.2-americanPutValue P 𝓕 W K r q σ S z.2)
      (𝓝 (S,T)) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hboundlim
    filter_upwards [hnear] with z hz
    have hl := (americanPutValue_uniform_spot_lipschitz (P := P) (𝓕 := 𝓕) (q := q) (σ := σ)
      hW hK hr hS z.2).dist_le_mul z.1 hz S (mem_ball_self (by positivity))
    simpa only [Real.dist_eq,Real.norm_eq_abs] using hl
  have hfixed : Tendsto (fun z : ℝ × ℝ≥0 => americanPutValue P 𝓕 W K r q σ S z.2)
      (𝓝 (S,T)) (𝓝 (americanPutValue P 𝓕 W K r q σ S T)) :=
    (americanPutValue_continuous_horizon hW hpaths hK hr hS.le).continuousAt.comp continuousAt_snd
  have hh := herr.add hfixed
  simp only [sub_add_cancel,zero_add] at hh
  convert! hh using 1

end MathFin.BlackScholes.AmericanPut.Stopping
