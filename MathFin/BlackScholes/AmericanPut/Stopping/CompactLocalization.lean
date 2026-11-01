/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.LocalPriceIto
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth price extensions around compact interior sets

A single globally C3 compactly supported function agrees with the price on a
neighborhood of a whole compact subset of continuation. This strengthens the
pointwise localization used by the local Ito calculation.

## Result

Public entry points include `exists_compact_set_localization`, `kernelContinuation`,
`kernelContinuation_isOpen`, `brownianPriceKernel_compact_localization`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter
open scoped Topology ContDiff Manifold

theorem exists_compact_set_localization {F : ℝ × ℝ → ℝ} {C U : Set (ℝ × ℝ)}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hF : ContDiffOn ℝ 3 F U) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝ˢ C] F := by
  obtain ⟨L,hL,hCL,hLU⟩ := exists_compact_between hC hU hCU
  obtain ⟨χ,hχone,hχzero,_⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℝ × ℝ) hC.isClosed hCL (n := 3)
  have hsupp : tsupport χ ⊆ L := by
    apply hL.isClosed.closure_subset_iff.mpr
    intro z hz
    by_contra hzL
    exact hz (hχzero z hzL)
  have hχcompact : HasCompactSupport χ := hL.of_isClosed_subset (isClosed_tsupport χ) hsupp
  refine ⟨fun z => χ z*F z,?_,hχcompact.mul_right,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact χ.contMDiff.contDiff.contDiffAt.mul
        (hF.contDiffAt (hU.mem_nhds (hLU (hsupp hz))))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      simp [hy]
  · filter_upwards [hχone] with z hz
    simp [hz]

/-- The set of `(t,w)` with `t < T` at which the price kernel's spatial argument
`x₀+(r-q-σ^2/2)*t+σ*w` lies strictly above the boundary value `b (σ^2/2*(T-t))`. -/
def kernelContinuation (b : ℝ → ℝ) (r q σ x₀ T : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 < T ∧ b (σ^2/2*(T-z.1)) < x₀+(r-q-σ^2/2)*z.1+σ*z.2}

theorem kernelContinuation_isOpen {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    {k h r q σ x₀ T : ℝ} (hp : Boundary.DividendPutSolution k h p b) (hσ : 0 < σ) :
    IsOpen (kernelContinuation b r q σ x₀ T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have htime : 0 < σ^2/2*(T-z.1) := mul_pos (by positivity) (sub_pos.mpr hz.1)
  have hb : ContinuousAt (fun y : ℝ × ℝ => b (σ^2/2*(T-y.1))) z :=
    Tendsto.comp (g := b) (f := fun y : ℝ × ℝ => σ^2/2*(T-y.1))
      (hp.boundary_continuous.continuousAt (Ici_mem_nhds htime))
      (show ContinuousAt (fun y : ℝ × ℝ => σ^2/2*(T-y.1)) z by fun_prop)
  exact (continuousAt_fst.eventually_lt continuousAt_const hz.1).and
    (hb.eventually_lt (by fun_prop) hz.2)

theorem brownianPriceKernel_compact_localization {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    {K r q σ x₀ T : ℝ} {C : Set (ℝ × ℝ)}
    (hp : Boundary.DividendPutSolution (Boundary.normalizedRate r σ)
        (Boundary.normalizedRate q σ) p b)
    (hσ : 0 < σ) (hC : IsCompact C) (hCU : C ⊆ kernelContinuation b r q σ x₀ T) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝ˢ C] (fun z => brownianPriceKernel p K r q σ x₀ T z.1 z.2) ∧
      ∀ z ∈ C, planeGenerator G z = 0 := by
  obtain ⟨G,hG,hcompact,heq⟩ := exists_compact_set_localization hC
    (kernelContinuation_isOpen hp hσ) hCU (fun z hz =>
      ((brownianPriceKernel_contDiffAt (K := K) hp hσ hz.1 hz.2).of_le
        (show (3 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt)
  refine ⟨G,hG,hcompact,heq,?_⟩
  intro z hzC
  have hz := heq.filter_mono (nhds_le_nhdsSet hzC)
  have htEq : (fun s => G (s,z.2)) =ᶠ[𝓝 z.1]
      (fun s => brownianPriceKernel p K r q σ x₀ T s z.2) :=
    hz.comp_tendsto (show Tendsto (fun s : ℝ => (s,z.2)) (𝓝 z.1) (𝓝 z) by
      convert! (continuous_id.prodMk continuous_const).tendsto z.1 using 1)
  have hxEq : (fun y => G (z.1,y)) =ᶠ[𝓝 z.2]
      (fun y => brownianPriceKernel p K r q σ x₀ T z.1 y) :=
    hz.comp_tendsto (show Tendsto (fun y : ℝ => (z.1,y)) (𝓝 z.2) (𝓝 z) by
      convert! (continuous_const.prodMk continuous_id).tendsto z.2 using 1)
  rw [show z = (z.1,z.2) from rfl,planeGenerator_eq_partials (hG.of_le (by norm_num)),
    htEq.deriv_eq,hxEq.deriv.deriv_eq]
  exact brownianPriceKernel_heat_equation hp hσ (hCU hzC).1 (hCU hzC).2

end MathFin.BlackScholes.AmericanPut.Stopping
