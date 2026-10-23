/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.DividendProblem

/-! # Pricing data without a boundary smoothness assumption

The original classical contract is unchanged. This weaker contract removes
only its positive-time boundary smoothness field. The straight comparison,
maximum principle and terminal Hopf arguments can use these data directly.

## Result

Public entry points include `ContinuousBoundaryPutSolution`,
`DividendPutSolution.toContinuousBoundaryPutSolution`, `toDividendPutSolution`, `boundary_nonpos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- Classical normalized put solution in the regime `0 ≤ h ≤ k`, `0 < k`, asking only that
the boundary be continuous: `DividendPutSolution` without its `boundary_smooth` field. -/
structure ContinuousBoundaryPutSolution (k h : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ) : Prop where
  rate_pos : 0 < k
  dividend_nonneg : 0 ≤ h
  dividend_le_rate : h ≤ k
  boundary_initial : b 0 = 0
  boundary_continuous : ContinuousOn b (Ici 0)
  price_continuous : ContinuousOn (fun z : ℝ × ℝ => p z.1 z.2) {z | 0 ≤ z.2}
  price_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (continuationRegion b)
  initial : ∀ x, p x 0 = putPayoff x
  dominates : ∀ x t, 0 ≤ t → putPayoff x ≤ p x t
  bounded : ∀ x t, 0 ≤ t → p x t ≤ 1
  exercise : ∀ x t, 0 < t → x ≤ b t → p x t = 1-Real.exp x
  continuation : ∀ x t, 0 < t → b t < x → putPayoff x < p x t
  equation : ∀ x t, 0 < t → b t < x →
    deriv (p x) t = dividendSpatialOperator k h (fun y => p y t) x
  smooth_fit : ∀ t, 0 < t → HasDerivWithinAt (fun x => p x t)
    (-Real.exp (b t)) (Ici (b t)) (b t)
  gradient_trace : ∀ t, 0 < t → Tendsto (fun x => deriv (fun y => p y t) x)
    (𝓝[>] (b t)) (𝓝 (-Real.exp (b t)))
  decay : ∀ t, 0 ≤ t → Tendsto (fun x => p x t) atTop (𝓝 0)

theorem DividendPutSolution.toContinuousBoundaryPutSolution {k h : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (hp : DividendPutSolution k h p b) :
    ContinuousBoundaryPutSolution k h p b where
  rate_pos := hp.rate_pos
  dividend_nonneg := hp.dividend_nonneg
  dividend_le_rate := hp.dividend_le_rate
  boundary_initial := hp.boundary_initial
  boundary_continuous := hp.boundary_continuous
  price_continuous := hp.price_continuous
  price_smooth := hp.price_smooth
  initial := hp.initial
  dominates := hp.dominates
  bounded := hp.bounded
  exercise := hp.exercise
  continuation := hp.continuation
  equation := hp.equation
  smooth_fit := hp.smooth_fit
  gradient_trace := hp.gradient_trace
  decay := hp.decay

instance {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} :
    Coe (DividendPutSolution k h p b) (ContinuousBoundaryPutSolution k h p b) :=
  ⟨DividendPutSolution.toContinuousBoundaryPutSolution⟩

namespace ContinuousBoundaryPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem toDividendPutSolution (hp : ContinuousBoundaryPutSolution k h p b)
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) : DividendPutSolution k h p b where
  rate_pos := hp.rate_pos
  dividend_nonneg := hp.dividend_nonneg
  dividend_le_rate := hp.dividend_le_rate
  boundary_initial := hp.boundary_initial
  boundary_continuous := hp.boundary_continuous
  boundary_smooth := hb
  price_continuous := hp.price_continuous
  price_smooth := hp.price_smooth
  initial := hp.initial
  dominates := hp.dominates
  bounded := hp.bounded
  exercise := hp.exercise
  continuation := hp.continuation
  equation := hp.equation
  smooth_fit := hp.smooth_fit
  gradient_trace := hp.gradient_trace
  decay := hp.decay

theorem boundary_nonpos (hp : ContinuousBoundaryPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    b t ≤ 0 := by
  have hv := (putPayoff_nonneg (b t)).trans (hp.dominates (b t) t ht.le)
  rw [hp.exercise (b t) t ht le_rfl] at hv
  exact Real.exp_le_one_iff.mp (by linarith)

theorem price_contDiffAt (hp : ContinuousBoundaryPutSolution k h p b)
    {x t : ℝ} (ht : 0 < t) (hx : b t < x) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (x,t) := by
  have hb : ContinuousAt b t := hp.boundary_continuous.continuousAt (Ici_mem_nhds ht)
  have hbt : ContinuousAt (fun z : ℝ × ℝ => b z.2) (x,t) := hb.comp continuousAt_snd
  have ht' : ∀ᶠ z : ℝ × ℝ in 𝓝 (x,t), 0 < z.2 :=
    continuousAt_const.eventually_lt continuousAt_snd ht
  have hx' : ∀ᶠ z : ℝ × ℝ in 𝓝 (x,t), b z.2 < z.1 :=
    hbt.eventually_lt continuousAt_fst hx
  exact hp.price_smooth.contDiffAt (ht'.and hx')

end ContinuousBoundaryPutSolution

theorem dividendPutSolution_iff_continuousBoundary_and_smooth {k h : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} :
    DividendPutSolution k h p b ↔
      ContinuousBoundaryPutSolution k h p b ∧ ContDiffOn ℝ ∞ b (Ioi 0) :=
  ⟨fun hp => ⟨hp.toContinuousBoundaryPutSolution,hp.boundary_smooth⟩,
    fun hp => hp.1.toDividendPutSolution hp.2⟩

end MathFin.BlackScholes.AmericanPut.Boundary
