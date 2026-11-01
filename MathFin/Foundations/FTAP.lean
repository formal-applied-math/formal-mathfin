/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.EquivMeasure
public import MathFin.Foundations.MartingaleFrozen
public import MathFin.Foundations.MartingaleTransform
public import MathFin.Foundations.NoArbitrageCore

/-!
# FTAP (Theorem 2.6.7), forward (⇒) direction: EMM ⇒ no arbitrage

The discrete-time market and the one forward direction of the library's FTAP: existence of an
equivalent martingale measure precludes arbitrage, via the martingale-transform argument, on a
general probability space and up to a finite horizon `T`.

* `IsEMM 𝓕 P S T Q` — `Q` is an equivalent martingale measure for the `F`-valued discounted price
  `S` up to the horizon `T`: `Q ≈ P` and `S` frozen at `T` is a `Q`-martingale for `𝓕`. This is the
  shape of `ContinuousMarket.IsEMM`, with `ℕ` for `ℝ≥0`; its three consequences before the
  horizon are `IsEMM.adapted`, `.integrable` and `.condExp_eq` (`martingale_min_iff`), and the way
  to build one from the one-step martingale identity is `IsEMM.of_condExp_succ`.
* `NoArbitrage 𝓕 P S T` — no predictable strategy, bounded up to `T`, turns zero initial wealth
  into a `P`-a.s. nonnegative gain that is not `P`-a.s. zero. The price and the holdings are valued
  in a real inner-product space `F` (several assets), the gains are `⟪φ_{t+1}, S_{t+1} − S_t⟫`
  (`martingaleTransform φ S T`); the scalar market is `F = ℝ`.
* `IsEMM.noArbitrage` — the forward theorem: `IsEMM` ⇒ `NoArbitrage`.

The finite-Ω market of `FTAPDiscrete.lean` and the one-period market of
`FTAPOnePeriodVector.lean` (a two-step filtration with `𝓕 0 = ⊥`) are instances: their forward
directions call this theorem. So does the continuous-time one,
`ContinuousMarket.isEMM_noArbitrageSimple`, through `ContinuousMarket.IsEMM.sampled`. The backward
directions are proved in the narrower settings: on a finite full-support space over a finite
horizon (`FTAPDiscrete.lean`), for one period on a general space (`FTAPOnePeriodVector.lean`,
with the scalar `FTAPOnePeriod.lean` its `F = ℝ` case), and for one-period finite-state
markets (`FTAPMultiState.lean`, whose two-state case is `FTAPTwoState.lean`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Equivalent martingale measure for the finite horizon `T`.** `Q` is a probability measure
mutually absolutely continuous with `P`, and the price `S` frozen at the horizon, `n ↦ S (min n T)`,
is a `Q`-martingale for `𝓕`: the honest finite-horizon object, since `S` need not be a
`Q`-martingale past `T`. A `Q`-martingale on all of `ℕ` is an EMM at every horizon. At `T = 1`
with `𝓕 0 = ⊥` this is the one-period notion for `S 1 − S 0` (`isEMM_one_iff_onePeriod`). -/
structure IsEMM (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ)
    (Q : Measure Ω) : Prop extends IsEquivProbMeasure P Q where
  martingale : Martingale (fun n ↦ S (min n T)) 𝓕 Q

/-- **No arbitrage** up to the horizon `T`: no predictable strategy `φ` (`φ (t+1)` is
`𝓕 t`-measurable for `t < T`), bounded up to `T`, turns zero initial wealth into a `P`-a.s.
nonnegative gain `martingaleTransform φ S T` without making it `P`-a.s. zero. -/
def NoArbitrage (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ) : Prop :=
  ∀ φ : ℕ → Ω → F, (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) →
    (∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) →
    0 ≤ᵐ[P] martingaleTransform φ S T → martingaleTransform φ S T =ᵐ[P] 0

namespace IsEMM

variable {𝓕 : Filtration ℕ m0} {P Q : Measure Ω} {S : ℕ → Ω → F} {T : ℕ}

/-- **The way an EMM is built**: an equivalent probability measure under which the price is
adapted and integrable up to `T` and satisfies the one-step martingale identity
`S t = E_Q[S (t+1) | 𝓕 t]` for `t < T` (`martingale_min_of_condExp_succ`). -/
theorem of_condExp_succ (hQ : IsEquivProbMeasure P Q)
    (hadapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) (hint : ∀ t ≤ T, Integrable (S t) Q)
    (hmart : ∀ t < T, S t =ᵐ[Q] Q[S (t + 1) | 𝓕 t]) : IsEMM 𝓕 P S T Q :=
  haveI := hQ.isProb
  ⟨hQ, martingale_min_of_condExp_succ hadapt hint hmart⟩

/-- Before the horizon the price is `𝓕`-adapted. -/
theorem adapted (h : IsEMM 𝓕 P S T Q) {t : ℕ} (ht : t ≤ T) : StronglyMeasurable[𝓕 t] (S t) :=
  haveI := h.isProb
  (martingale_min_iff.mp h.martingale).1 t ht

/-- Before the horizon the price is `Q`-integrable. -/
theorem integrable (h : IsEMM 𝓕 P S T Q) {t : ℕ} (ht : t ≤ T) : Integrable (S t) Q :=
  haveI := h.isProb
  (martingale_min_iff.mp h.martingale).2.1 t ht

/-- **The martingale property before the horizon**: `Q[S t | 𝓕 s] = S s` for `s ≤ t ≤ T`. -/
theorem condExp_eq (h : IsEMM 𝓕 P S T Q) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    Q[S t | 𝓕 s] =ᵐ[Q] S s :=
  haveI := h.isProb
  ((martingale_min_iff.mp h.martingale).2.2 hst ht).symm

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale measure
precludes arbitrage.

Given an equivalent martingale measure `Q ≈ P` for the discounted price `S` up to the horizon `T`
and a predictable strategy `φ` bounded up to `T`, the discounted P&L
`V_T = ∑_{t<T} ⟪φ_{t+1}(ω), S_{t+1}(ω) − S_t(ω)⟫` (`martingaleTransform φ S T`; for a scalar price,
`F = ℝ`, the product `φ_{t+1} · (S_{t+1} − S_t)`) cannot be `P`-a.s. nonnegative without being
`P`-a.s. zero. The price and the holdings are valued in a real inner-product space `F` (several
assets); the scalar theorem is the case `F = ℝ`.

Proof: the transform of the frozen price by the strategy, cut off at the horizon, is a bounded
predictable transform of a martingale, so a martingale (`martingaleTransform_isMartingale`) started
at `0`; a `Q`-a.s. nonnegative terminal value of such a martingale vanishes
(`martingale_nonneg_terminal_ae_zero`), and `P ≪ Q` carries the null set over. -/
theorem noArbitrage (h : IsEMM 𝓕 P S T Q) : NoArbitrage 𝓕 P S T := by
  haveI := h.isProb
  intro φ hφ_pred hφ_bdd hV_nonneg
  obtain ⟨K, hK⟩ := hφ_bdd
  -- cut the strategy off at the horizon, where the frozen price stops moving
  let φ' : ℕ → Ω → F := fun n ω ↦ if n ≤ T then φ n ω else 0
  have hsum : martingaleTransform φ' (fun n ↦ S (min n T)) T = martingaleTransform φ S T := by
    funext ω
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have htT : t + 1 ≤ T := Finset.mem_range.mp ht
    simp only [φ', if_pos htT, min_eq_left htT, min_eq_left (t.le_succ.trans htT)]
  have hV_mart : Martingale (martingaleTransform φ' fun n ↦ S (min n T)) 𝓕 Q :=
    martingaleTransform_isMartingale h.martingale
      (fun n ↦ by
        rcases lt_or_ge n T with hn | hn
        · simpa only [φ', if_pos (Nat.succ_le_of_lt hn)] using hφ_pred n hn
        · simp only [φ', if_neg (by omega : ¬ n + 1 ≤ T)]
          exact stronglyMeasurable_zero)
      ⟨max K 0, Filter.Eventually.of_forall fun ω n ↦ by
        simp only [φ']
        split_ifs with hn
        · exact (hK n hn ω).trans (le_max_left _ _)
        · simp⟩
  refine ae_eq_zero_of_nonneg_of_null_pos hV_nonneg ?_
  rw [← hsum]
  exact h.ac' (martingale_nonneg_terminal_ae_zero hV_mart (martingaleTransform_zero _ _)
    (by rw [hsum]; exact h.ac.ae_le hV_nonneg))

end IsEMM

end MathFin
