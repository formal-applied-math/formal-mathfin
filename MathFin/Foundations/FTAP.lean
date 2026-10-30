/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.MartingaleTransform
public import MathFin.Foundations.NoArbitrageCore

/-!
# FTAP (Theorem 2.6.7), forward (⇒) direction: EMM ⇒ no arbitrage

The one forward direction of the library's FTAP: existence of an equivalent martingale
measure precludes arbitrage, via the martingale-transform argument, on a general probability
space and up to a finite horizon `T`. The hypotheses are the horizon-`T` ones (adapted,
integrable, one-step martingale for `t < T`), so the finite-Ω market of `FTAPDiscrete.lean`
and the one-period market of `FTAPOnePeriodVector.lean` (a two-step filtration with
`𝓕 0 = ⊥`) are instances: their `noArbitrage_of_isEMM` call this theorem. The backward
directions are proved in the narrower settings: on a finite full-support space over a finite
horizon (`FTAPDiscrete.lean`), for one period on a general space (`FTAPOnePeriodVector.lean`,
with the scalar `FTAPOnePeriod.lean` its `F = ℝ` case), and for one-period finite-state
markets (`FTAPMultiState.lean`, whose two-state case is `FTAPTwoState.lean`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale
measure precludes arbitrage.

Given a discounted-price process `S` adapted and `Q`-integrable up to the horizon `T`, an
equivalent probability measure `Q ≪≫ P` under which `S` is a martingale up to `T`
(`S t = E_Q[S (t+1) | 𝓕 t]` for `t < T`), and a predictable strategy `φ` bounded up to `T`,
the discounted P&L `V_T = ∑_{t<T} φ_{t+1}(ω) · (S_{t+1} − S_t)` cannot be `P`-a.s.
nonnegative and strictly positive on a `P`-non-null set. A process that is a martingale for
all times (`Martingale S 𝓕 Q`) satisfies the hypotheses at every horizon.

Proof: stop `S`, `φ` and `𝓕` at the horizon, which turns `S` into a genuine martingale and
`φ` into a bounded predictable process, and apply `martingaleTransform_isMartingale`. -/
theorem emm_implies_no_arbitrage
    {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
    {T : ℕ} {𝓕 : Filtration ℕ m0} {S : ℕ → Ω → ℝ}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hS_adapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t))
    (hS_int : ∀ t ≤ T, Integrable (S t) Q)
    (hS_mart : ∀ t < T, S t =ᵐ[Q] Q[S (t + 1) | 𝓕 t])
    (φ : ℕ → Ω → ℝ)
    (hφ_pred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, |φ n ω| ≤ K)
    (hV_nonneg : ∀ᵐ ω ∂P,
      0 ≤ ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)) :
    P {ω | 0 < ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)} = 0 := by
  -- stop the filtration, the price and the strategy at the horizon
  obtain ⟨𝓖, h𝓖⟩ : ∃ 𝓖 : Filtration ℕ m0, ∀ n, 𝓖 n = 𝓕 (min n T) :=
    ⟨{ seq := fun n ↦ 𝓕 (min n T)
       mono' := fun _ _ h ↦ 𝓕.mono (min_le_min_right T h)
       le' := fun n ↦ 𝓕.le _ }, fun _ ↦ rfl⟩
  let S' : ℕ → Ω → ℝ := fun n ↦ S (min n T)
  let φ' : ℕ → Ω → ℝ := fun n ω ↦ if n ≤ T then φ n ω else 0
  have hS' : Martingale S' 𝓖 Q := by
    refine martingale_of_condExp_sub_eq_zero_nat
      (fun n ↦ by rw [h𝓖]; exact hS_adapt _ (min_le_right _ _))
      (fun n ↦ hS_int _ (min_le_right _ _)) fun n ↦ ?_
    show Q[S (min (n + 1) T) - S (min n T) | 𝓖 n] =ᵐ[Q] 0
    rw [h𝓖]
    rcases lt_or_ge n T with hn | hn
    · rw [min_eq_left hn.le, min_eq_left hn]
      have h_now : Q[S n | 𝓕 n] = S n :=
        condExp_of_stronglyMeasurable (𝓕.le n) (hS_adapt n hn.le) (hS_int n hn.le)
      filter_upwards [condExp_sub (hS_int (n + 1) hn) (hS_int n hn.le) (𝓕 n), hS_mart n hn]
        with ω h_sub h_mart
      rw [Pi.zero_apply, h_sub, Pi.sub_apply, h_now, ← h_mart, sub_self]
    · rw [min_eq_right hn, min_eq_right (hn.trans (Nat.le_succ n)), sub_self, condExp_zero]
  have hφ'_pred : StronglyAdapted 𝓖 (fun n ↦ φ' (n + 1)) := fun n ↦ by
    show StronglyMeasurable[𝓖 n] (φ' (n + 1))
    rcases lt_or_ge n T with hn | hn
    · have h : φ' (n + 1) = φ (n + 1) := funext fun ω ↦ if_pos hn
      rw [h, h𝓖, min_eq_left hn.le]
      exact hφ_pred n hn
    · have h : φ' (n + 1) = 0 := funext fun ω ↦ if_neg (by omega)
      rw [h]
      exact stronglyMeasurable_zero
  obtain ⟨K, hK⟩ := hφ_bdd
  have hsum (ω : Ω) : martingaleTransform φ' S' T ω
      = ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω) := by
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have htT : t + 1 ≤ T := Finset.mem_range.mp ht
    simp only [φ', S', if_pos htT, min_eq_left htT, min_eq_left (t.le_succ.trans htT)]
  have hV_mart : Martingale (martingaleTransform φ' S') 𝓖 Q :=
    martingaleTransform_isMartingale hS' hφ'_pred
      ⟨max K 0, Filter.Eventually.of_forall fun ω n ↦ by
        simp only [φ']
        split_ifs with h
        · exact (hK n h ω).trans (le_max_left _ _)
        · simp⟩
  have hnull : Q {ω | 0 < martingaleTransform φ' S' T ω} = 0 :=
    martingale_nonneg_terminal_ae_zero hV_mart (martingaleTransform_zero _ _)
      (by filter_upwards [hQP.ae_le hV_nonneg] with ω h; rw [Pi.zero_apply, hsum]; exact h)
  simp only [hsum] at hnull
  exact hPQ hnull

end MathFin
