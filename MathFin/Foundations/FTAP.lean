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
* `IsCompleteMarket 𝓕 P S T` — every bounded `𝓕 T`-claim is replicated, `P`-a.s., by a bounded
  predictable strategy from some initial wealth: `H = x + martingaleTransform φ S T`.
* `IsEMM.measure_eq_of_isCompleteMarket` — the second FTAP's easy direction: in a complete market
  two equivalent martingale measures agree on `𝓕 T`. The converse, on a finite space, is
  `ftap_two` (`FTAPComplete.lean`).

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

/-- **Complete market** up to the horizon `T`: every bounded `𝓕 T`-measurable claim `H` is
replicated, `P`-a.s., by a bounded predictable strategy `φ` from some initial wealth `x`:
`H = x + martingaleTransform φ S T`, the terminal value of the self-financing portfolio holding
`φ_{t+1}` over `(t, t+1]`. The same strategy class as `NoArbitrage`. -/
def IsCompleteMarket (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ) : Prop :=
  ∀ H : Ω → ℝ, StronglyMeasurable[𝓕 T] H → (∃ C : ℝ, ∀ ω, |H ω| ≤ C) →
    ∃ (x : ℝ) (φ : ℕ → Ω → F), (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) ∧
      (∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) ∧ H =ᵐ[P] fun ω ↦ x + martingaleTransform φ S T ω

namespace IsEMM

variable {𝓕 : Filtration ℕ m0} {P Q : Measure Ω} {S : ℕ → Ω → F} {T : ℕ}

/-- **The way an EMM is built**: an equivalent probability measure under which the price is
adapted and integrable up to `T` and satisfies the one-step martingale identity
`S t = E_Q[S (t+1) | 𝓕 t]` for `t < T` (`martingale_min_of_condExp_succ`). -/
theorem of_condExp_succ (hQ : IsEquivProbMeasure P Q)
    (hadapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) (hint : ∀ t ≤ T, Integrable (S t) Q)
    (hmart : ∀ t < T, S t =ᵐ[Q] Q[S (t + 1) | 𝓕 t]) : IsEMM 𝓕 P S T Q :=
  have := hQ.isProb
  ⟨hQ, martingale_min_of_condExp_succ hadapt hint hmart⟩

/-- Before the horizon the price is `𝓕`-adapted. -/
theorem adapted (h : IsEMM 𝓕 P S T Q) {t : ℕ} (ht : t ≤ T) : StronglyMeasurable[𝓕 t] (S t) :=
  have := h.isProb
  (martingale_min_iff.mp h.martingale).1 t ht

/-- Before the horizon the price is `Q`-integrable. -/
theorem integrable (h : IsEMM 𝓕 P S T Q) {t : ℕ} (ht : t ≤ T) : Integrable (S t) Q :=
  have := h.isProb
  (martingale_min_iff.mp h.martingale).2.1 t ht

/-- **The martingale property before the horizon**: `Q[S t | 𝓕 s] = S s` for `s ≤ t ≤ T`. -/
theorem condExp_eq (h : IsEMM 𝓕 P S T Q) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    Q[S t | 𝓕 s] =ᵐ[Q] S s :=
  have := h.isProb
  ((martingale_min_iff.mp h.martingale).2.2 hst ht).symm

/-- **The gains of a bounded predictable strategy are a `Q`-martingale started at `0`.** The
transform of the frozen price by the strategy cut off at the horizon (where the frozen price stops
moving) is a bounded predictable transform of a martingale, hence a martingale
(`martingaleTransform_isMartingale`), and at time `T` it is `martingaleTransform φ S T`. -/
theorem exists_martingale_gains (h : IsEMM 𝓕 P S T Q) {φ : ℕ → Ω → F}
    (hφ_pred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) :
    ∃ V : ℕ → Ω → ℝ, Martingale V 𝓕 Q ∧ V 0 = 0 ∧ V T = martingaleTransform φ S T := by
  have := h.isProb
  obtain ⟨K, hK⟩ := hφ_bdd
  let φ' : ℕ → Ω → F := fun n ω ↦ if n ≤ T then φ n ω else 0
  have hsum : martingaleTransform φ' (fun n ↦ S (min n T)) T = martingaleTransform φ S T := by
    funext ω
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have htT : t + 1 ≤ T := Finset.mem_range.mp ht
    simp only [φ', ite_eq_left htT, min_eq_left htT, min_eq_left (t.le_succ.trans htT)]
  exact ⟨_, martingaleTransform_isMartingale h.martingale
      (fun n ↦ by
        rcases lt_or_ge n T with hn | hn
        · simpa only [φ', ite_eq_left (Nat.succ_le_of_lt hn)] using hφ_pred n hn
        · simp only [φ', ite_eq_right (by omega : ¬ n + 1 ≤ T)]
          exact stronglyMeasurable_zero)
      ⟨max K 0, Filter.Eventually.of_forall fun ω n ↦ by
        simp only [φ']
        split_ifs with hn
        · exact (hK n hn ω).trans (le_max_left _ _)
        · simp⟩,
    martingaleTransform_zero _ _, hsum⟩

/-- **Fair game**: the gains of a bounded predictable strategy have `Q`-mean zero. -/
theorem integral_martingaleTransform (h : IsEMM 𝓕 P S T Q) {φ : ℕ → Ω → F}
    (hφ_pred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) :
    ∫ ω, martingaleTransform φ S T ω ∂Q = 0 := by
  have := h.isProb
  obtain ⟨V, hV, hV0, hVT⟩ := h.exists_martingale_gains hφ_pred hφ_bdd
  simpa [← hVT, hV0] using (hV.setIntegral_eq (Nat.zero_le T) MeasurableSet.univ).symm

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale measure
precludes arbitrage.

Given an equivalent martingale measure `Q ≈ P` for the discounted price `S` up to the horizon `T`
and a predictable strategy `φ` bounded up to `T`, the discounted P&L
`V_T = ∑_{t<T} ⟪φ_{t+1}(ω), S_{t+1}(ω) − S_t(ω)⟫` (`martingaleTransform φ S T`; for a scalar price,
`F = ℝ`, the product `φ_{t+1} · (S_{t+1} − S_t)`) cannot be `P`-a.s. nonnegative without being
`P`-a.s. zero. The price and the holdings are valued in a real inner-product space `F` (several
assets); the scalar theorem is the case `F = ℝ`.

Proof: the gains are a `Q`-martingale started at `0` (`exists_martingale_gains`); a `Q`-a.s.
nonnegative terminal value of such a martingale vanishes (`martingale_nonneg_terminal_ae_zero`),
and `P ≪ Q` carries the null set over. -/
theorem noArbitrage (h : IsEMM 𝓕 P S T Q) : NoArbitrage 𝓕 P S T := by
  have := h.isProb
  intro φ hφ_pred hφ_bdd hV_nonneg
  obtain ⟨V, hV, hV0, hVT⟩ := h.exists_martingale_gains hφ_pred hφ_bdd
  refine ae_eq_zero_of_nonneg_of_null_pos hV_nonneg ?_
  rw [← hVT]
  exact h.ac' (martingale_nonneg_terminal_ae_zero hV hV0 (by rw [hVT]; exact h.ac.ae_le hV_nonneg))

/-- **Replication prices the claim**: if a bounded predictable strategy replicates the indicator of
`A` from initial wealth `x`, `P`-a.s., then every equivalent martingale measure gives `A` the
probability `x`. -/
theorem measureReal_eq_of_replicates (h : IsEMM 𝓕 P S T Q) {A : Set Ω} (hA : MeasurableSet A)
    {x : ℝ} {φ : ℕ → Ω → F} (hφ_pred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K)
    (hrep : A.indicator (1 : Ω → ℝ) =ᵐ[P] fun ω ↦ x + martingaleTransform φ S T ω) :
    Q.real A = x := by
  have := h.isProb
  obtain ⟨V, hV, -, hVT⟩ := h.exists_martingale_gains hφ_pred hφ_bdd
  have hint : Integrable (martingaleTransform φ S T) Q := hVT ▸ hV.integrable T
  rw [← integral_indicator_one hA, integral_congr_ae (h.ac.ae_le hrep),
    integral_add (integrable_const x) hint, integral_const,
    h.integral_martingaleTransform hφ_pred hφ_bdd]
  simp

/-- **Second FTAP, `complete ⇒ unique`**: in a complete market any two equivalent martingale
measures agree on `𝓕 T`. Replicate the indicator of the event; both measures give it the
initial wealth of the replicating strategy (`measureReal_eq_of_replicates`). -/
theorem measure_eq_of_isCompleteMarket {Q₁ Q₂ : Measure Ω} (hc : IsCompleteMarket 𝓕 P S T)
    (h₁ : IsEMM 𝓕 P S T Q₁) (h₂ : IsEMM 𝓕 P S T Q₂) {A : Set Ω} (hA : MeasurableSet[𝓕 T] A) :
    Q₁ A = Q₂ A := by
  have := h₁.isProb
  have := h₂.isProb
  obtain ⟨x, φ, hpred, hbdd, hrep⟩ := hc (A.indicator 1) (stronglyMeasurable_const.indicator hA)
    ⟨1, fun ω ↦ by by_cases hω : ω ∈ A <;> simp [hω]⟩
  have hA' : MeasurableSet A := 𝓕.le T A hA
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    ((h₁.measureReal_eq_of_replicates hA' hpred hbdd hrep).trans
      (h₂.measureReal_eq_of_replicates hA' hpred hbdd hrep).symm)

end IsEMM

end MathFin
