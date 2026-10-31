/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# A martingale up to a horizon, frozen at the horizon

A process `S` that is a martingale only up to a horizon `T` (adapted and integrable on
`{t ≤ T}`, `S s = E[S t | 𝓕 s]` for `s ≤ t ≤ T`) is a martingale once it is frozen at `T`:
`t ↦ S (min t T)` is a martingale for the same filtration, and every martingale of that form
arises so (`martingale_min_iff`). Past the horizon the frozen process is constant, and the
constant `S T` is `𝓕 T ⊆ 𝓕 s`-measurable, so it is its own conditional expectation.

This is the vocabulary of the horizon-`T` equivalent martingale measures, discrete
(`MathFin.IsEMM`) and continuous (`MathFin.ContinuousMarket.IsEMM`): the hypothesis there is the
frozen martingale, and the three consequences read off it (adaptedness, integrability and the
martingale identity before the horizon) are the forward direction of `martingale_min_iff`. On
`ℕ` the identity need only be given one step at a time (`martingale_min_of_condExp_succ`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section LinearOrder

variable {ι : Type*} [LinearOrder ι] {𝓕 : Filtration ι m0} {S : ι → Ω → E} {T : ι}

/-- **A martingale up to `T`, frozen at `T`, is a martingale; and conversely.** `t ↦ S (min t T)`
is a `μ`-martingale for `𝓕` iff `S` is adapted and integrable on `{t ≤ T}` and satisfies the
martingale identity `S s = E[S t | 𝓕 s]` for `s ≤ t ≤ T`. -/
theorem martingale_min_iff [IsFiniteMeasure μ] :
    Martingale (fun t ↦ S (min t T)) 𝓕 μ ↔
      (∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) ∧ (∀ t ≤ T, Integrable (S t) μ) ∧
        ∀ ⦃s t⦄, s ≤ t → t ≤ T → S s =ᵐ[μ] μ[S t | 𝓕 s] := by
  refine ⟨fun h ↦ ⟨fun t ht ↦ by simpa only [min_eq_left ht] using h.1 t,
    fun t ht ↦ by simpa only [min_eq_left ht] using h.integrable t,
    fun s t hst ht ↦ by
      simpa only [min_eq_left ht, min_eq_left (hst.trans ht)] using
        (h.condExp_ae_eq hst).symm⟩, fun ⟨hadapt, hint, hmart⟩ ↦
    ⟨fun s ↦ (hadapt _ (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _)),
      fun i j hij ↦ ?_⟩⟩
  show μ[S (min j T) | 𝓕 i] =ᵐ[μ] S (min i T)
  rcases le_or_gt j T with hj | hj
  · simpa only [min_eq_left hj, min_eq_left (hij.trans hj)] using (hmart hij hj).symm
  rw [min_eq_right hj.le]
  rcases le_or_gt i T with hi | hi
  · simpa only [min_eq_left hi, min_eq_right hj.le] using (hmart hi le_rfl).symm
  · rw [min_eq_right hi.le]
    exact .of_eq (condExp_of_stronglyMeasurable (𝓕.le i)
      ((hadapt T le_rfl).mono (𝓕.mono hi.le)) (hint T le_rfl))

end LinearOrder

/-- **The one-step form on `ℕ`.** A process that is adapted and integrable up to `T` and satisfies
the one-step martingale identity `S t = E[S (t+1) | 𝓕 t]` for `t < T` is a martingale once frozen
at `T`. -/
theorem martingale_min_of_condExp_succ [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0}
    {S : ℕ → Ω → E} {T : ℕ} (hadapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t))
    (hint : ∀ t ≤ T, Integrable (S t) μ) (hmart : ∀ t < T, S t =ᵐ[μ] μ[S (t + 1) | 𝓕 t]) :
    Martingale (fun n ↦ S (min n T)) 𝓕 μ := by
  refine martingale_of_condExp_sub_eq_zero_nat
    (fun n ↦ (hadapt _ (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _)))
    (fun n ↦ hint _ (min_le_right _ _)) fun n ↦ ?_
  show μ[S (min (n + 1) T) - S (min n T) | 𝓕 n] =ᵐ[μ] 0
  rcases lt_or_ge n T with hn | hn
  · rw [min_eq_left hn.le, min_eq_left (Nat.succ_le_of_lt hn)]
    filter_upwards [condExp_sub (hint (n + 1) hn) (hint n hn.le) (𝓕 n), hmart n hn]
      with ω h_sub h_mart
    rw [Pi.zero_apply, h_sub, Pi.sub_apply,
      condExp_of_stronglyMeasurable (𝓕.le n) (hadapt n hn.le) (hint n hn.le), ← h_mart, sub_self]
  · simp [min_eq_right hn, min_eq_right (hn.trans n.le_succ)]

end MathFin
