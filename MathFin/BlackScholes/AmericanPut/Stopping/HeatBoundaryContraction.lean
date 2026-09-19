/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.HeatBoundaryEquation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

/-! # Strict finite-time contraction of cross-boundary heat propagation

Only part of the unit-mass boundary kernel arrives within any finite time.
This strict bound is the input for solving the two coupled boundary equations.

## Result

Public entry points include `boundaryArrivalMass`, `boundaryArrivalMass_nonneg`, `boundaryArrivalMass_lt_one`, `heatBoundaryExtension_finite_bound`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

/-- The mass of the boundary kernel at depth `x` arriving within elapsed time `D`, namely
`∫ s in Ioc 0 D, heatBoundaryKernel s x`. -/
noncomputable def boundaryArrivalMass (x D : ℝ) : ℝ :=
  ∫ s in Ioc 0 D, heatBoundaryKernel s x

theorem boundaryArrivalMass_nonneg {x D : ℝ} (hx : 0 < x) :
    0 ≤ boundaryArrivalMass x D := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (heatBoundaryKernel_pos hs.1 hx).le

theorem boundaryArrivalMass_lt_one {x D : ℝ} (hx : 0 < x) (hD : 0 ≤ D) :
    boundaryArrivalMass x D < 1 := by
  have hi := heatBoundaryKernel_integrable hx
  have hit : IntegrableOn (fun s => heatBoundaryKernel s x) (Ioi D) :=
    hi.mono_set (fun _ hs => hD.trans_lt hs)
  have hp : 0 < ∫ s in Ioi D, heatBoundaryKernel s x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (heatBoundaryKernel_pos (hD.trans_lt hs) hx).le) hit).mpr
    have he : Function.support (fun s => heatBoundaryKernel s x) ∩ Ioi D = Ioi D := by
      ext s
      constructor
      · exact And.right
      · intro hs
        exact ⟨(heatBoundaryKernel_pos (hD.trans_lt hs) hx).ne',hs⟩
    rw [he]
    simp
  have he := intervalIntegral.integral_interval_add_Ioi hi hit
  rw [intervalIntegral.integral_of_le hD,heatBoundaryKernel_integral hx] at he
  dsimp [boundaryArrivalMass]
  linarith

theorem heatBoundaryExtension_finite_bound {g : ℝ → ℝ} {a D C x t : ℝ}
    (hx : 0 < x) (ht : t ≤ a+D)
    (hstart : ∀ s, s ≤ a → g s = 0) (hC : ∀ s, ‖g s‖ ≤ C) :
    ‖heatBoundaryExtension g x t‖ ≤ boundaryArrivalMass x D*C := by
  have he : (∫ s in Ioc 0 D, heatBoundaryKernel s x*g (t-s)) =
      ∫ s in Ioi 0, heatBoundaryKernel s x*g (t-s) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro s hs
    have hDs : D < s := by
      by_contra! hn
      exact hs.2 ⟨hs.1,hn⟩
    rw [hstart (t-s) (by linarith),mul_zero]
  rw [heatBoundaryExtension_eq_integral g hx t,← he]
  calc
    ‖∫ s in Ioc 0 D, heatBoundaryKernel s x*g (t-s)‖ ≤
        ∫ s in Ioc 0 D, heatBoundaryKernel s x*C := by
      apply norm_integral_le_of_norm_le
        (((heatBoundaryKernel_integrable hx).mono_set Ioc_subset_Ioi_self).mul_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul,Real.norm_of_nonneg (heatBoundaryKernel_pos hs.1 hx).le]
      exact mul_le_mul_of_nonneg_left (hC _) (heatBoundaryKernel_pos hs.1 hx).le
    _ = boundaryArrivalMass x D*C := integral_mul_const _ _

theorem heatBoundaryExtension_sub (f g : ℝ →ᵇ ℝ) (x t : ℝ) :
    heatBoundaryExtension (fun s => f s-g s) x t =
      heatBoundaryExtension f x t-heatBoundaryExtension g x t := by
  simp only [heatBoundaryExtension,mul_sub]
  rw [integral_sub
    (heatBoundaryExtension_integrable f.continuous f.norm_coe_le_norm x t)
    (heatBoundaryExtension_integrable g.continuous g.norm_coe_le_norm x t)]

/-- Bounded continuous boundary data that vanish at every time `t ≤ a`. -/
abbrev CausalBoundaryData (a : ℝ) := {g : ℝ →ᵇ ℝ // ∀ t, t ≤ a → g t = 0}

theorem isClosed_causalBoundaryData (a : ℝ) :
    IsClosed {g : ℝ →ᵇ ℝ | ∀ t, t ≤ a → g t = 0} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_eq (by fun_prop) continuous_const

instance (a : ℝ) : CompleteSpace (CausalBoundaryData a) :=
  (isClosed_causalBoundaryData a).isComplete.completeSpace_coe

instance (a : ℝ) : Inhabited (CausalBoundaryData a) := ⟨⟨0,fun _ _ => rfl⟩⟩

/-- The bounded continuous function `t ↦ χ t * heatBoundaryExtension g L t`: the half-line
extension of `g` read at depth `L`, multiplied by `χ`. -/
noncomputable def crossBoundaryMap (χ : ℝ →ᵇ ℝ) (L : ℝ) (g : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => χ t*heatBoundaryExtension g L t)
    (χ.continuous.mul ((heatBoundaryExtension_continuous g.continuous g.norm_coe_le_norm).comp
      (continuous_const.prodMk continuous_id))) (‖χ‖*‖g‖) (fun t => by
        rw [norm_mul]
        exact mul_le_mul (χ.norm_coe_le_norm t)
          (heatBoundaryExtension_bound g.norm_coe_le_norm L t) (norm_nonneg _) (norm_nonneg _))

/-- `crossBoundaryMap χ L` as a self-map of `CausalBoundaryData a`: the extension of causal data
still vanishes for `t ≤ a`. -/
noncomputable def crossBoundaryCausal {a : ℝ} (χ : ℝ →ᵇ ℝ) (L : ℝ)
    (g : CausalBoundaryData a) : CausalBoundaryData a :=
  ⟨crossBoundaryMap χ L g.1,fun t ht => by
    change χ t*heatBoundaryExtension g.1 L t = 0
    rw [heatBoundaryExtension_causal g.2 L ht,mul_zero]⟩

theorem crossBoundaryCausal_dist {a D L : ℝ} (hL : 0 < L)
    (χ : ℝ →ᵇ ℝ) (hχ : ∀ t, ‖χ t‖ ≤ 1)
    (hstop : ∀ t, a+D < t → χ t = 0) (f g : CausalBoundaryData a) :
    dist (crossBoundaryCausal χ L f) (crossBoundaryCausal χ L g) ≤
      boundaryArrivalMass L D*dist f g := by
  simp only [Subtype.dist_eq,dist_eq_norm]
  change ‖crossBoundaryMap χ L f.1-crossBoundaryMap χ L g.1‖ ≤
    boundaryArrivalMass L D*‖f.1-g.1‖
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (boundaryArrivalMass_nonneg hL) (norm_nonneg _))).mpr
  intro t
  change ‖χ t*heatBoundaryExtension f.1 L t-χ t*heatBoundaryExtension g.1 L t‖ ≤ _
  by_cases ht : t ≤ a+D
  · rw [← mul_sub,← heatBoundaryExtension_sub,norm_mul]
    calc
      ‖χ t‖*‖heatBoundaryExtension (fun s => f.1 s-g.1 s) L t‖ ≤
          ‖heatBoundaryExtension (fun s => f.1 s-g.1 s) L t‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (hχ t)
      _ ≤ boundaryArrivalMass L D*‖f.1-g.1‖ := heatBoundaryExtension_finite_bound hL ht
        (fun s hs => by rw [f.2 s hs,g.2 s hs,sub_self]) (f.1-g.1).norm_coe_le_norm
  · rw [hstop t (lt_of_not_ge ht)]
    simp only [zero_mul,sub_self,norm_zero]
    exact mul_nonneg (boundaryArrivalMass_nonneg hL) (norm_nonneg _)

theorem crossBoundaryCausal_lipschitz {a D L : ℝ} (hL : 0 < L)
    (χ : ℝ →ᵇ ℝ) (hχ : ∀ t, ‖χ t‖ ≤ 1)
    (hstop : ∀ t, a+D < t → χ t = 0) :
    LipschitzWith ⟨boundaryArrivalMass L D,boundaryArrivalMass_nonneg hL⟩
      (crossBoundaryCausal (a := a) χ L) :=
  LipschitzWith.of_dist_le_mul (crossBoundaryCausal_dist hL χ hχ hstop)

end MathFin.BlackScholes.AmericanPut.Stopping
