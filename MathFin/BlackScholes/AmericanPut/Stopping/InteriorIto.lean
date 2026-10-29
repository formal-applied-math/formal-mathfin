/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.InteriorRegion

/-!
# An Ito representation valid simultaneously up to interior stopping

Fixed-time almost-sure Ito identities cannot simply be evaluated at a random
time. A countable dense set and path continuity justify that step here, after
the drift has been proved zero on the entire interior-stopped trajectory.

## Result

Public entry points include `ae_eq_through_positive_time`,
`brownianInteriorRule_ito_representation`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem ae_eq_through_positive_time {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : ℝ≥0 → Ω → ℝ} {θ : Ω → ℝ≥0}
    (hX : ∀ ω, Continuous (fun t => X t ω)) (hY : ∀ ω, Continuous (fun t => Y t ω))
    (heq : ∀ t, ∀ᵐ ω ∂P, t < θ ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂P, 0 < θ ω → ∀ t ≤ θ ω, X t ω = Y t ω := by
  obtain ⟨D,hcount,hdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have ha : ∀ᵐ ω ∂P, ∀ t ∈ D, t < θ ω → X t ω = Y t ω :=
    (ae_ball_iff hcount).mpr (fun t _ => heq t)
  filter_upwards [ha] with ω hω hpos t ht
  have hc : IsClosed {s | X s ω = Y s ω} := isClosed_eq (hX ω) (hY ω)
  have hD : Iio (θ ω) ∩ D ⊆ {s | X s ω = Y s ω} := fun s hs => hω s hs.2 hs.1
  have hi : Iio (θ ω) ⊆ {s | X s ω = Y s ω} :=
    (hdense.open_subset_closure_inter isOpen_Iio).trans (hc.closure_subset_iff.mpr hD)
  have hm : t ∈ closure (Iio (θ ω)) := by
    rw [closure_Iio' (show (Iio (θ ω)).Nonempty from ⟨0,hpos⟩)]
    exact ht
  exact hc.closure_subset_iff.mpr hi hm

theorem brownianInteriorRule_ito_representation {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {K r q σ S : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ) (T : ℝ≥0) (n : ℕ) :
    let θ := brownianInteriorRule (K := K) (S := S) hp T n
    ∃ M : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, (∀ ω, Continuous (fun t => M t ω)) ∧
      IsLocalMartingale M brownianAugFiltration gaussianLimit ∧
      ∀ᵐ ω ∂gaussianLimit, ∀ t,
        classicalCandidate brownian K r q σ S p T (min t (θ.time ω)) ω -
          classicalCandidate brownian K r q σ S p T 0 ω =
        {ω | 0 < θ.time ω}.indicator (fun ω => M (min t (θ.time ω)) ω) ω := by
  classical
  let θ := brownianInteriorRule (K := K) (S := S) hp T n
  obtain ⟨G,hG,_,hpath⟩ := brownianInteriorRule_smooth_extension hp hK hS hσ T n
  obtain ⟨M,hMcont,hM,hIto⟩ := plane_ito_localMartingale
    isBrownianReal_brownian.toIsPreBrownianReal measurable_brownian continuous_brownian hG
  refine ⟨M,hMcont,hM,?_⟩
  have ha : ∀ᵐ ω ∂gaussianLimit, 0 < θ.time ω → ∀ t ≤ θ.time ω,
      G (t,brownian t ω)-G (0,brownian 0 ω) = M t ω := by
    apply ae_eq_through_positive_time
      (fun ω => (hG.continuous.comp
        (continuous_subtype_val.prodMk (continuous_brownian ω))).sub continuous_const) hMcont
    intro t
    filter_upwards [hIto t] with ω hω ht
    have hpos : 0 < θ.time ω := lt_of_le_of_lt zero_le ht
    have hz : (∫ s in Ioc 0 t, planeGenerator G (s,brownian s ω)
        ∂MathFin.ItoIntegralL2.timeMeasure) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun s hs => (hpath ω hpos s (hs.2.trans ht.le)).2)
    rw [hz,add_zero] at hω
    convert! hω using 1
  filter_upwards [ha] with ω hω t
  by_cases hpos : 0 < θ.time ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | 0 < θ.time ω} from hpos)]
    rw [← (hpath ω hpos _ (min_le_right t (θ.time ω))).1,
      ← (hpath ω hpos 0 zero_le).1]
    exact hω hpos _ (min_le_right t (θ.time ω))
  · have hz : θ.time ω = 0 := le_antisymm (le_of_not_gt hpos) zero_le
    rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < θ.time ω} from hpos),hz]
    simp

end MathFin.BlackScholes.AmericanPut.Stopping
