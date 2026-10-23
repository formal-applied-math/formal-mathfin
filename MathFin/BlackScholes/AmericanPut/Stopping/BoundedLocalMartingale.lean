/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PlaneIto

/-!
# Bounded local martingales and smaller filtrations

Promotion is proved by dominated convergence of localized set integrals.
No unproved upstream optional-sampling or uniform-integrability result is used.
Adaptation to the target filtration is explicit; a local property alone is
not silently treated as pointwise adaptation on exceptional null outcomes.

## Result

Public entry points include `martingale_of_setIntegral_eq_real`, `martingale_smaller_filtration`,
`locally_bounded_localMartingale_is_martingale`, `bounded_localMartingale_is_martingale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {𝓕 𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0 → Ω → ℝ}

theorem martingale_of_setIntegral_eq_real (hadapt : StronglyAdapted 𝓕 X)
    (hint : ∀ t, Integrable (X t) P)
    (heq : ∀ i j, i ≤ j → ∀ s, MeasurableSet[𝓕 i] s →
      (∫ ω in s, X i ω ∂P) = ∫ ω in s, X j ω ∂P) : Martingale X 𝓕 P := by
  refine ⟨hadapt,fun i j hij => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) (fun s hs _ => heq i j hij s hs)
    (hadapt i).aestronglyMeasurable).symm

theorem martingale_smaller_filtration (hFG : 𝓕 ≤ 𝓖) (hX : Martingale X 𝓖 P)
    (hadapt : StronglyAdapted 𝓕 X) : Martingale X 𝓕 P :=
  martingale_of_setIntegral_eq_real hadapt hX.integrable
    (fun _ _ hij _ hs => hX.setIntegral_eq hij (hFG _ _ hs))

theorem locally_bounded_localMartingale_is_martingale (hX : IsLocalMartingale X 𝓕 P)
    (hadapt : StronglyAdapted 𝓕 X)
    (hbound : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t, t ≤ T → ∀ ω, ‖X t ω‖ ≤ C) :
    Martingale X 𝓕 P := by
  obtain ⟨τ,hτ,hloc⟩ := hX
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n =>
    stoppedProcess (fun t => {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)
  have hY : ∀ n, Martingale (Y n) 𝓕 P := fun n => (hloc n).1
  have hYbound : ∀ t, ∃ C : ℝ, ∀ n ω, ‖Y n t ω‖ ≤ C := by
    intro t
    obtain ⟨C,hC⟩ := hbound t
    refine ⟨C,fun n ω => ?_⟩
    have hu : (min (t : WithTop ℝ≥0) (τ n ω)).untopA ≤ t :=
      WithTop.untopA_le (min_le_left _ _)
    exact (norm_indicator_le_norm_self _ _).trans (hC _ hu ω)
  have hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω)) := by
    intro t
    filter_upwards [hτ.tendsto_top] with ω hω
    have hlarge : ∀ᶠ n in atTop, ((t+1 : ℝ≥0) : WithTop ℝ≥0) < τ n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top (t+1)))
    have heq : (fun n => Y n t ω) =ᶠ[atTop] (fun _ => X t ω) := by
      filter_upwards [hlarge] with n hn
      have hle : (t : WithTop ℝ≥0) ≤ τ n ω :=
        (show (t : WithTop ℝ≥0) ≤
            (t+1 : ℝ≥0) by exact_mod_cast le_add_of_nonneg_right zero_le).trans hn.le
      have hpos : (⊥ : WithTop ℝ≥0) < τ n ω :=
        (show (⊥ : WithTop ℝ≥0) < (t+1 : ℝ≥0) by
          change (0 : WithTop ℝ≥0) < _
          exact_mod_cast (show (0 : ℝ≥0) < t+1 by positivity)).trans hn
      exact (stoppedProcess_eq_of_le hle).trans
        (indicator_of_mem (show ω ∈ {ω | ⊥ < τ n ω} from hpos) _)
    exact tendsto_const_nhds.congr' heq.symm
  have hint : ∀ t, Integrable (X t) P := by
    intro t
    obtain ⟨C,hC⟩ := hbound t
    exact (integrable_const C).mono' ((hadapt t).mono (𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall (hC t le_rfl))
  apply martingale_of_setIntegral_eq_real hadapt hint
  intro i j hij s hs
  have hconv (t : ℝ≥0) : Tendsto (fun n => ∫ ω in s, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in s, X t ω ∂P)) := by
    obtain ⟨C,hC⟩ := hYbound t
    exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hY n).integrable t).aestronglyMeasurable.restrict) (integrable_const C)
      (fun n => Eventually.of_forall (hC n)) (ae_restrict_of_ae (hlim t))
  have hi := hconv i
  have heq : (fun n => ∫ ω in s, Y n i ω ∂P) = (fun n => ∫ ω in s, Y n j ω ∂P) :=
    funext (fun n => (hY n).setIntegral_eq hij hs)
  rw [heq] at hi
  exact tendsto_nhds_unique hi (hconv j)

theorem bounded_localMartingale_is_martingale (hX : IsLocalMartingale X 𝓕 P)
    (hadapt : StronglyAdapted 𝓕 X) {C : ℝ}
    (hbound : ∀ t ω, ‖X t ω‖ ≤ C) : Martingale X 𝓕 P :=
  locally_bounded_localMartingale_is_martingale hX hadapt
    (fun _ => ⟨C,fun t _ ω => hbound t ω⟩)

end MathFin.BlackScholes.AmericanPut.Stopping
