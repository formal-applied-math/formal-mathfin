/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CandidatePDE

/-!
# Compact smooth localization of the Brownian-coordinate price

At each continuation point there is a globally C3, compactly supported function
agreeing with the actual Brownian-coordinate price on a neighborhood. This
justifies availability of global smooth test functions without pretending that
the price is globally C2 across its free boundary. `CompactLocalization`
strengthens this to compact sets; `ContactMartingale` assembles stopped Ito.

## Result

Public entry points include `exists_compact_localization`, `brownianPriceKernel_localization`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Metric
open scoped Topology ContDiff

theorem exists_compact_localization {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hF : ContDiffAt ℝ ∞ F z) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧ G =ᶠ[𝓝 z] F := by
  obtain ⟨u,hu,hFu⟩ := hF.contDiffOn (m := 3)
    (WithTop.coe_le_coe.mpr le_top) (by norm_num)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hu
  let χ : ContDiffBump z := {
    rIn := ε/4
    rOut := ε/2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hsupp : tsupport χ ⊆ ball z ε := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [χ]; linarith)
  refine ⟨fun y => χ y*F y,?_,χ.hasCompactSupport.mul_right,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact χ.contDiff.contDiffAt.mul
        ((hFu.mono hball).contDiffAt (isOpen_ball.mem_nhds (hsupp hy)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with v hv
      simp [hv]
  · filter_upwards [χ.eventuallyEq_one] with y hy
    simp only [Pi.one_apply] at hy
    rw [hy,one_mul]

theorem brownianPriceKernel_localization {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    {K r q σ x₀ T t w : ℝ}
    (hp : Boundary.DividendPutSolution (Boundary.normalizedRate r σ)
        (Boundary.normalizedRate q σ) p b)
    (hσ : 0 < σ) (ht : t < T)
    (hx : b (σ ^ 2 / 2 * (T - t)) < x₀ + (r - q - σ ^ 2/2) * t + σ * w) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝 (t,w)] (fun z => brownianPriceKernel p K r q σ x₀ T z.1 z.2) :=
  exists_compact_localization (brownianPriceKernel_contDiffAt hp hσ ht hx)

end MathFin.BlackScholes.AmericanPut.Stopping
