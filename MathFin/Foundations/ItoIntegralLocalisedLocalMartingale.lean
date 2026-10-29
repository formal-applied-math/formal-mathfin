/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ExitTime
public import MathFin.Foundations.ItoIntegralLocalised

/-! # The Itô integral of an unbounded continuous adapted integrand is a local martingale

`localItoIntegral` (`ItoIntegralLocalised`) is `∫ σ dB` on `[0, T]` for a continuous adapted `σ`
that need not be bounded, built by gluing the integrals `M^N = ∫ clip N σ dB` of the clipped
integrands. This file proves it is a continuous local martingale, localised by the exit times of
`σ`.

Degenne's `IsLocalMartingale` asks the stopped processes to be càdlàg on every path, while
`localItoIntegral` is continuous only almost surely; as for the bounded integral
(`exists_continuous_localMartingale_modification`), the statement is about a representative
indistinguishable from it on `[0, T]`, frozen past `T`, zeroed off a co-null set of the null
σ-algebra, and adapted to the null-augmented Brownian filtration `augFiltration`.

The localising sequence is `τ_N = exitTime σ N`, the first time `|σ|` reaches `N`, a stopping time
of the Brownian filtration since the hit set is closed (`isStoppingTime_exitTime_of_measurable`),
increasing to `⊤` on every path. Up to `τ_N` the path of `σ` stays in `[−N, N]`
(`abs_le_of_le_exitTime`), where the integral is `M^N` (`ae_localItoIntegral_eq`); frozen at `T`
and zeroed off the same co-null set, `M^N` is a martingale (`martingale_itoLocalMod`). A process
that agrees with a right-continuous martingale up to a stopping time is, stopped there, a
martingale (`martingale_stoppedProcess_of_ae_eq`).

* `exists_continuous_localMartingale_localItoIntegral`: there is a process, indistinguishable
  from `localItoIntegral` on `[0, T]`, with every path continuous, that is a local martingale for
  the null-augmented Brownian filtration, and a martingale stopped at each exit time of `σ`.

Not here: the local martingale for the unaugmented natural filtration (the repaired
representative is not adapted to it), and `T = ∞`.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralLocalised

open MeasureTheory ProbabilityTheory Filter Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralProcessContinuousModification
  ItoLocalMartingale ItoIntegralProcessLocalMartingaleGeneral
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)

include hB hBcont in
/-- **The continuous Itô integral, frozen at `T` and zeroed off a co-null set `G` of the null
σ-algebra, is a martingale** for the null-augmented Brownian filtration. It is adapted because the
continuous Itô integral is predictable (`itoContinuousMod_isStronglyPredictable`) and `G` is a set
of the augmentation; its martingale identity is `condExp_itoLocalMod`. -/
theorem martingale_itoLocalMod {G : Set Ω} (hG : MeasurableSet[nullsAlg mΩ μ] G) (hGc : μ Gᶜ = 0)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Martingale (fun t ω ↦ itoLocalMod G T t hBmeas φ ω) (augFiltration (μ := μ) hBmeas) μ :=
  ⟨fun i ↦ (((itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ).stronglyAdapted
      (min i T)).mono (((natFiltration hBmeas).mono (min_le_left i T)).trans le_sup_left)).indicator
      (le_sup_right (b := nullsAlg mΩ μ) _ hG),
    fun _ _ hij ↦ condExp_itoLocalMod hB T hBmeas hBcont hGc φ hij⟩

variable {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω))

include hB hBcont in
/-- **The Itô integral of a continuous adapted integrand is a continuous local martingale,
localised by the exit times of the integrand.** There is a process `X`, almost surely equal to
`localItoIntegral` at every `t ≤ T`, with every path continuous, that is a local martingale for the
null-augmented Brownian filtration; stopped at `exitTime σ N`, the first time `|σ|` reaches `N`
(and zeroed where that time is `0`), it is a martingale. The proof takes for `X` the integral
frozen at `T` and zeroed off a co-null set of the null σ-algebra on which every clipped integral
`M^N` is continuous on `[0, T]` and equal to `localItoIntegral` up to each time where `σ` stays in
`[−N, N]`; up to `exitTime σ N` it is `M^N`, frozen and zeroed the same way, a martingale
(`martingale_itoLocalMod`). -/
theorem exists_continuous_localMartingale_localItoIntegral :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, X t ω = localItoIntegral (μ := μ) T hBmeas hadap hcont t ω) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧
      IsLocalMartingale X (augFiltration (μ := μ) hBmeas) μ ∧
      ∀ N : ℕ, Martingale
        (stoppedProcess (fun i ↦ {ω | ⊥ < exitTime σ N ω}.indicator (X i)) (exitTime σ N))
        (augFiltration (μ := μ) hBmeas) μ := by
  obtain ⟨G, hG, hGc, hGgood⟩ := exists_nullsAlg_of_ae (μ := μ)
    (p := fun ω ↦ (∀ N, ContinuousOn (fun t ↦ clipItoMod (μ := μ) T hBmeas hadap hcont N t ω)
        (Icc 0 T))
      ∧ ContinuousOn (fun t ↦ localItoIntegral (μ := μ) T hBmeas hadap hcont t ω) (Icc 0 T)
      ∧ ∀ N : ℕ, ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, |σ s ω| ≤ N) →
        localItoIntegral (μ := μ) T hBmeas hadap hcont t ω
          = clipItoMod (μ := μ) T hBmeas hadap hcont N t ω) <| by
    filter_upwards [ae_all_iff.2 fun N ↦ itoContinuousMod_continuousOn hB T hBmeas hBcont
        (processToLp (μ := μ) T hBmeas (clip_adapted hadap N) (clip_continuous hcont N)
          (abs_clip_le N σ)),
      ae_continuousOn_localItoIntegral hB T hBmeas hBcont hadap hcont,
      ae_localItoIntegral_eq hB T hBmeas hBcont hadap hcont] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := by rw [ae_iff]; exact hGc
  set X : ℝ≥0 → Ω → ℝ :=
    fun t ↦ G.indicator (localItoIntegral (μ := μ) T hBmeas hadap hcont (min t T))
  have hXc : ∀ ω, Continuous fun t ↦ X t ω :=
    continuous_indicator_min fun ω hω ↦ (hGgood ω hω).2.1
  have hτ : IsLocalizingSequence (augFiltration (μ := μ) hBmeas) (fun N ↦ exitTime σ N) μ :=
    isLocalizingSequence_exitTime_of_measurable
      (fun t ↦ (hadap t).measurable.mono le_sup_left le_rfl) hcont
  have hmart (N : ℕ) : Martingale
      (stoppedProcess (fun i ↦ {ω | ⊥ < exitTime σ N ω}.indicator (X i)) (exitTime σ N))
      (augFiltration (μ := μ) hBmeas) μ := by
    refine martingale_stoppedProcess_of_ae_eq (hτ.isStoppingTime N) (fun i ↦
      ((stronglyAdapted_localItoIntegral hB T hBmeas hBcont hadap hcont (min i T)).mono
        (((natFiltration hBmeas).mono (min_le_left i T)).trans le_sup_left)).indicator
        (le_sup_right (b := nullsAlg mΩ μ) _ hG))
      (fun ω ↦ (hXc ω).isCadlag.right_continuous)
      (martingale_itoLocalMod hB T hBmeas hBcont hG hGc (processToLp (μ := μ) T hBmeas
        (clip_adapted hadap N) (clip_continuous hcont N) (abs_clip_le N σ)))
      (fun ω ↦ (continuous_indicator_min (fun ω hω ↦ (hGgood ω hω).1 N) ω).isCadlag
        |>.right_continuous) ?_
    filter_upwards [hGae] with ω hω hpos u hu
    simp only [X, itoLocalMod, Set.indicator_of_mem hω]
    exact (hGgood ω hω).2.2 N _ ⟨zero_le, min_le_right u T⟩ fun s hs ↦
      abs_le_of_le_exitTime hcont hpos
        ((WithTop.coe_le_coe.2 (hs.2.trans (min_le_left u T))).trans hu)
  refine ⟨X, ?_, hXc, ⟨_, hτ, fun N ↦ ⟨hmart N,
    isStable_isCadlag X (fun ω ↦ (hXc ω).isCadlag) _ (hτ.isStoppingTime N)⟩⟩, hmart⟩
  filter_upwards [hGae] with ω hω t ht
  simp only [X, Set.indicator_of_mem hω, min_eq_left ht.2]

end ItoIntegralLocalised
end MathFin
