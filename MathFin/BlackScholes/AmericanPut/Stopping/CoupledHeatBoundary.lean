/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.HeatBoundaryContraction

/-! # Solving the coupled boundary-input equations

A compact time cutoff makes cross-boundary propagation a strict contraction.
The two fixed-point equations give exact matching where that cutoff is one.

## Result

Public entry points include `causalBoundarySub`, `causalBoundarySub_dist`, `coupledBoundaryStep`,
`coupledBoundaryStep_contracting`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

/-- The difference `f-g` of two causal boundary inputs; vanishing on `(-∞,a]` is preserved. -/
noncomputable def causalBoundarySub {a : ℝ} (f g : CausalBoundaryData a) : CausalBoundaryData a :=
  ⟨f.1-g.1,fun t ht => by change f.1 t-g.1 t = 0; rw [f.2 t ht,g.2 t ht,sub_self]⟩

theorem causalBoundarySub_dist {a : ℝ} (f g h : CausalBoundaryData a) :
    dist (causalBoundarySub f g) (causalBoundarySub f h) = dist g h := by
  simp only [Subtype.dist_eq,causalBoundarySub,dist_eq_norm]
  rw [show (f.1-g.1)-(f.1-h.1) = -(g.1-h.1) by abel,norm_neg]

/-- One step of the coupled boundary iteration, sending `p` to
`(g₀-crossBoundaryCausal χ L p.2,g₁-crossBoundaryCausal χ L p.1)`: each component is corrected
by the cross-boundary transport of the other. -/
noncomputable def coupledBoundaryStep {a : ℝ} (χ : ℝ →ᵇ ℝ) (L : ℝ)
    (g₀ g₁ : CausalBoundaryData a) (p : CausalBoundaryData a × CausalBoundaryData a) :
    CausalBoundaryData a × CausalBoundaryData a :=
  (causalBoundarySub g₀ (crossBoundaryCausal χ L p.2),
    causalBoundarySub g₁ (crossBoundaryCausal χ L p.1))

theorem coupledBoundaryStep_contracting {a D L : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (χ : ℝ →ᵇ ℝ) (hχ : ∀ t, ‖χ t‖ ≤ 1) (hstop : ∀ t, a + D < t → χ t = 0)
    (g₀ g₁ : CausalBoundaryData a) :
    ContractingWith ⟨boundaryArrivalMass L D,boundaryArrivalMass_nonneg hL⟩
      (coupledBoundaryStep χ L g₀ g₁) := by
  refine ⟨boundaryArrivalMass_lt_one hL hD,LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  simp only [Prod.dist_eq,coupledBoundaryStep,causalBoundarySub_dist]
  apply max_le
  · exact (crossBoundaryCausal_dist hL χ hχ hstop p.2 q.2).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (boundaryArrivalMass_nonneg hL))
  · exact (crossBoundaryCausal_dist hL χ hχ hstop p.1 q.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (boundaryArrivalMass_nonneg hL))

theorem exists_coupled_boundary_inputs {a D L : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (χ : ℝ →ᵇ ℝ) (hχ : ∀ t, ‖χ t‖ ≤ 1) (hstop : ∀ t, a + D < t → χ t = 0)
    (g₀ g₁ : CausalBoundaryData a) :
    ∃ f₀ f₁ : CausalBoundaryData a,
      (∀ t, f₀.1 t+χ t*heatBoundaryExtension f₁.1 L t = g₀.1 t) ∧
      (∀ t, f₁.1 t+χ t*heatBoundaryExtension f₀.1 L t = g₁.1 t) := by
  have hc := coupledBoundaryStep_contracting hL hD χ hχ hstop g₀ g₁
  let p := hc.fixedPoint
  have hp : coupledBoundaryStep χ L g₀ g₁ p = p := hc.fixedPoint_isFixedPt
  refine ⟨p.1,p.2,?_,?_⟩
  · intro t
    have he := congrArg (fun q : CausalBoundaryData a × CausalBoundaryData a => q.1.1 t) hp
    change g₀.1 t-χ t*heatBoundaryExtension p.2.1 L t = p.1.1 t at he
    linarith
  · intro t
    have he := congrArg (fun q : CausalBoundaryData a × CausalBoundaryData a => q.2.1 t) hp
    change g₁.1 t-χ t*heatBoundaryExtension p.1.1 L t = p.2.1 t at he
    linarith

theorem exists_coupled_compact_boundary_inputs {a D L : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (χ : ℝ →ᵇ ℝ) (hχ : ∀ t, ‖χ t‖ ≤ 1) (hstop : ∀ t, a + D < t → χ t = 0)
    (hcχ : HasCompactSupport (χ : ℝ → ℝ)) (g₀ g₁ : CausalBoundaryData a)
    (hc₀ : HasCompactSupport (g₀.1 : ℝ → ℝ)) (hc₁ : HasCompactSupport (g₁.1 : ℝ → ℝ)) :
    ∃ f₀ f₁ : CausalBoundaryData a,
      HasCompactSupport (f₀.1 : ℝ → ℝ) ∧ HasCompactSupport (f₁.1 : ℝ → ℝ) ∧
      (∀ t, f₀.1 t+χ t*heatBoundaryExtension f₁.1 L t = g₀.1 t) ∧
      (∀ t, f₁.1 t+χ t*heatBoundaryExtension f₀.1 L t = g₁.1 t) := by
  obtain ⟨f₀,f₁,he₀,he₁⟩ := exists_coupled_boundary_inputs hL hD χ hχ hstop g₀ g₁
  have hf₀ : (f₀.1 : ℝ → ℝ) = fun t => g₀.1 t-χ t*heatBoundaryExtension f₁.1 L t := by
    funext t
    linarith [he₀ t]
  have hf₁ : (f₁.1 : ℝ → ℝ) = fun t => g₁.1 t-χ t*heatBoundaryExtension f₀.1 L t := by
    funext t
    linarith [he₁ t]
  refine ⟨f₀,f₁,?_,?_,he₀,he₁⟩
  · rw [hf₀]
    exact hc₀.sub hcχ.mul_right
  · rw [hf₁]
    exact hc₁.sub hcχ.mul_right

end MathFin.BlackScholes.AmericanPut.Stopping
