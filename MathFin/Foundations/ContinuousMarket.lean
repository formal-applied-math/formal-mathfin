/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAP
public import MathFin.Foundations.NoArbitrageCore

/-!
# Continuous-time market vocabulary: `IsEMM`, simple strategies, no-arbitrage

A **model-agnostic** frame for the continuous-time first fundamental theorem of asset
pricing (FTAP), parametric over a finite-dimensional real inner-product-space-valued
discounted price process `S : ℝ≥0 → Ω → F`. The Black–Scholes model (`ContinuousFTAP.lean`)
instantiates it at `F = ℝ`; a multi-asset model would instantiate at `F = Fin n → ℝ`.

* `IsEMM S T Q` — `Q` is an equivalent martingale measure for `S` up to the horizon `T`:
  `Q ≈ P` (mutual absolute continuity) and `S` is a `Q`-martingale w.r.t. the filtration `𝓕` on
  `{t ≤ T}`, i.e. the process stopped at `T` is a `Q`-martingale. This matches the discrete
  `MathFin.IsEMM` (`FTAPDiscrete.lean`), which also takes a horizon `T`, and it is what an
  equivalent measure obtained by a density change on `𝓕_T` can be: the Girsanov/Esscher measure
  makes the discounted Black–Scholes price a martingale on `[0, T]` and no further
  (`bs_discounted_isEMM`). A martingale on all of `ℝ≥0` is an EMM at every horizon.
* `SimpleStrategy 𝓕 F` — a piecewise-constant, predictable, bounded trading strategy:
  finitely many trading dates `time : Fin (N+1) → ℝ≥0` and `𝓕`-measurable bounded holdings
  `hold : Fin N → Ω → F` between consecutive dates.
* `SimpleStrategy.gains` — the discounted terminal gains of a simple strategy against `S`.
* `NoArbitrageSimple S T` — no simple strategy trading up to `T` has gains that are `P`-a.s.
  nonnegative and strictly positive on a `P`-non-null set.
* `martingale_stopped_of_setIntegral_eq` — the way an `IsEMM` is built: adaptedness, integrability
  and the set-integral martingale identity on `[0, T]` give the stopped martingale.
* `isEMM_noArbitrageSimple` — the forward theorem. A simple strategy sampled at its own dates is
  a discrete predictable strategy, and the discrete forward theorem `emm_implies_no_arbitrage`
  (vector-valued, `FTAP.lean`) applies to the sampled price.
* `increment_integrable`, `increment_integral_zero` — a bounded predictable weight against a
  `Q`-martingale increment is `Q`-integrable with zero `Q`-mean. Public because the
  pricing-measure argument of `PricingMeasureL2Density` is built out of exactly these, summed
  over a simple process's bands.

## Scope: meaning-1 (operational) vs. meaning-2 (Delbaen–Schachermayer) FTAP

This file builds **meaning 1**: an EMM for a *given* process, restricted to the honest,
economically transparent class of *simple* (piecewise-constant) strategies. It deliberately
does **not** build meaning 2, the Delbaen–Schachermayer theorem (`NFLVR ⟺ ∃ EMM` for a
general locally-bounded semimartingale, admissible strategies over a continuum of trading
times, and the general stochastic integral `∫ φ dS`). Absent by design:

* general **admissible** strategies (not just piecewise-constant) and the general stochastic
  integral `∫ φ dS` against a semimartingale;
* **NFLVR** (no free lunch with vanishing risk) and its distinction from plain no-arbitrage;
* the **converse** direction `NoArbitrageSimple S T → ∃ Q, IsEMM S T Q`, and closedness of the
  set of claims super-replicable from zero wealth (the Kreps–Yan / Hahn–Banach core DS needs).

`IsEMM` here is stated *on a process* `S`, exactly the object Delbaen–Schachermayer's theorem
would produce — so this frame is a strict sub-object of the DS one, and extending it to
meaning 2 is additive (new strategy class + new theorem), not a rewrite.

One such extension already exists. `Foundations/MarketCompleteness` states replication,
superreplication duality and uniqueness of the pricing measure over the **Itô-integrable
predictable** integrands rather than `SimpleStrategy`. That widening is forced by the
mathematics, not chosen: the hedge martingale representation returns is a general predictable
process, and a general `L²` claim is not the terminal value of any piecewise-constant holding,
so a completeness statement over `SimpleStrategy` would have no witnesses. `SimpleStrategy`
remains the right class *here*, where the whole point is that the forward no-arbitrage
conclusion needs no stochastic integration at all — a finite sum of predictable increments. The
two classes coexist; neither file changes the other, and `IsEMM` is shared.
-/

@[expose] public section

namespace MathFin.ContinuousMarket

open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Q` is an **equivalent martingale measure (EMM) up to the horizon `T`** for the discounted
price process `S`: `Q` is a probability measure mutually absolutely continuous with `P`
(`Q ≈ P`), and `S` is a `Q`-martingale w.r.t. the filtration `𝓕` on `{t ≤ T}` — stated as the
process `t ↦ S (min t T)` stopped at the horizon being a `Q`-martingale. A `Q`-martingale on all
of `ℝ≥0` is an EMM for every `T`. -/
structure IsEMM (S : ℝ≥0 → Ω → F) (T : ℝ≥0) (Q : Measure Ω) : Prop where
  isProb : IsProbabilityMeasure Q
  ac : Q ≪ P
  ac' : P ≪ Q
  martingale : Martingale (fun t ↦ S (min t T)) 𝓕 Q

/-- **The way an EMM's martingale is built.** A process that is `𝓕`-adapted and `Q`-integrable on
`{t ≤ T}` and satisfies the set-integral martingale identity there is a martingale once stopped at
`T`: past the horizon the stopped process is frozen, and `S T` is `𝓕 T ⊆ 𝓕 s`-measurable. -/
theorem martingale_stopped_of_setIntegral_eq {Q : Measure Ω} [IsFiniteMeasure Q]
    {S : ℝ≥0 → Ω → F} {T : ℝ≥0} (hadapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t))
    (hint : ∀ t ≤ T, Integrable (S t) Q)
    (hset : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T → ∀ ⦃A : Set Ω⦄, MeasurableSet[𝓕 s] A →
      ∫ ω in A, S t ω ∂Q = ∫ ω in A, S s ω ∂Q) :
    Martingale (fun t ↦ S (min t T)) 𝓕 Q := by
  have hadapt' (s : ℝ≥0) : StronglyMeasurable[𝓕 s] (S (min s T)) :=
    (hadapt _ (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _))
  refine ⟨hadapt', fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hint _ (min_le_right _ _))
    (fun A _ _ ↦ (hint _ (min_le_right _ _)).integrableOn) (fun A hA _ ↦ ?_)
    (hadapt' s).aestronglyMeasurable).symm
  by_cases hsT : s ≤ T
  · rw [min_eq_left hsT]
    exact (hset (le_min hst hsT) (min_le_right _ _) hA).symm
  · rw [min_eq_right (not_le.mp hsT).le, min_eq_right ((not_le.mp hsT).le.trans hst)]

/-- A **simple strategy**: finitely many trading dates `time 0 ≤ time 1 ≤ ⋯ ≤ time N`, with
piecewise-constant, `𝓕`-predictable, bounded holdings `hold i` held over `(time i, time i+1]`.
Does not depend on any measure — it is a purely path-space/filtration object. -/
structure SimpleStrategy (𝓕 : Filtration ℝ≥0 mΩ) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  /-- The number of trading intervals. -/
  N : ℕ
  /-- The `N + 1` trading dates `time 0 ≤ time 1 ≤ ⋯ ≤ time N`. -/
  time : Fin (N + 1) → ℝ≥0
  /-- The trading dates are nondecreasing. -/
  mono : Monotone time
  /-- The holding `hold i` carried over the `i`-th interval `(time i, time i+1]`. -/
  hold : Fin N → Ω → F
  /-- Predictability: each holding is `𝓕`-strongly-measurable at the start of its interval. -/
  meas : ∀ i : Fin N, StronglyMeasurable[𝓕 (time i.castSucc)] (hold i)
  /-- The holdings are uniformly bounded (in `ω` and `i`). -/
  bdd : ∃ K : ℝ, ∀ (i : Fin N) ω, ‖hold i ω‖ ≤ K

/-- The **discounted terminal gains** of a simple strategy `ψ` against the price process `S`:
`∑ᵢ ⟪hold i, S(time i+1) − S(time i)⟫`. -/
noncomputable def SimpleStrategy.gains (ψ : SimpleStrategy 𝓕 F)
    (S : ℝ≥0 → Ω → F) (ω : Ω) : ℝ :=
  ∑ i : Fin ψ.N, ⟪ψ.hold i ω, S (ψ.time i.succ) ω - S (ψ.time i.castSucc) ω⟫_ℝ

/-- **No simple-strategy arbitrage up to `T`**: no simple strategy trading on `[0, T]` (its last
date is `≤ T`) has gains against `S` that are `P`-a.s. nonnegative and strictly positive on a
`P`-non-null set. -/
def NoArbitrageSimple (S : ℝ≥0 → Ω → F) (T : ℝ≥0) : Prop :=
  ∀ ψ : SimpleStrategy 𝓕 F, ψ.time (Fin.last ψ.N) ≤ T → (0 ≤ᵐ[P] fun ω ↦ ψ.gains S ω) →
    P {ω | 0 < ψ.gains S ω} = 0

/-- The discrete `ℕ`-filtration `n ↦ 𝓕 (t n)` obtained by **sampling** a continuous-time
filtration `𝓕` along a monotone schedule `t : ℕ → ℝ≥0`. -/
def sampledFiltration (𝓕 : Filtration ℝ≥0 mΩ) {t : ℕ → ℝ≥0} (ht : Monotone t) :
    Filtration ℕ mΩ where
  seq n := 𝓕 (t n)
  mono' _ _ hij := 𝓕.mono (ht hij)
  le' n := 𝓕.le (t n)

omit [FiniteDimensional ℝ F] in
/-- **A `Q`-martingale sampled along a monotone schedule is a discrete `Q`-martingale.**
Sampling `S` at the increasing times `t 0 ≤ t 1 ≤ ⋯` gives a martingale w.r.t. the sampled
filtration `sampledFiltration 𝓕 ht`: adaptedness and the tower property both restrict along
`t`. A general, standalone structural lemma (the discrete-time trace of a continuous-time
martingale), benchmarked as `gir-martingale-reindex`. It is the sampling bridge of the forward
theorem `isEMM_noArbitrageSimple` below and of `IsEMM.sampled` (`FTAPDiscrete.lean`). -/
theorem martingale_comp_monotone {Q : Measure Ω} {S : ℝ≥0 → Ω → F}
    (hS : Martingale S 𝓕 Q) {t : ℕ → ℝ≥0} (ht : Monotone t) :
    Martingale (fun n ↦ S (t n)) (sampledFiltration 𝓕 ht) Q :=
  ⟨fun n ↦ hS.1 (t n), fun i j hij ↦ hS.2 (t i) (t j) (ht hij)⟩

/-- **A predictable-weighted increment `⟪φ, S t − S s⟫` is `Q`-integrable** when `φ` is bounded
and `S` is a `Q`-martingale (so `S t`, `S s` are integrable): Cauchy–Schwarz bounds the inner
product by `K · ‖S t − S s‖`, which is integrable. -/
theorem increment_integrable {Q : Measure Ω}
    {S : ℝ≥0 → Ω → F} (hS : Martingale S 𝓕 Q) {φ : Ω → F} {s t : ℝ≥0}
    (hφ : StronglyMeasurable[𝓕 s] φ) {K : ℝ} (hφb : ∀ ω, ‖φ ω‖ ≤ K) :
    Integrable (fun ω ↦ ⟪φ ω, S t ω - S s ω⟫_ℝ) Q := by
  have hΔ : Integrable (fun ω ↦ S t ω - S s ω) Q := (hS.integrable t).sub (hS.integrable s)
  refine Integrable.mono' (hΔ.norm.const_mul K)
    (((hφ.mono (𝓕.le s)).aestronglyMeasurable).inner hΔ.aestronglyMeasurable) ?_
  filter_upwards with ω
  calc ‖⟪φ ω, S t ω - S s ω⟫_ℝ‖ ≤ ‖φ ω‖ * ‖S t ω - S s ω‖ := norm_inner_le_norm _ _
    _ ≤ K * ‖S t ω - S s ω‖ := mul_le_mul_of_nonneg_right (hφb ω) (norm_nonneg _)

/-- **A predictable-weighted martingale increment has zero `Q`-integral.** For a `Q`-martingale
`S`, a `𝓕 s`-measurable bounded weight `φ`, and `s ≤ t`, the increment gain `⟪φ, S t − S s⟫`
integrates to `0`: pull `φ` out of `Q[· | 𝓕 s]` and use `Q[S t − S s | 𝓕 s] = 0`. -/
theorem increment_integral_zero {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S : ℝ≥0 → Ω → F} (hS : Martingale S 𝓕 Q) {φ : Ω → F} {s t : ℝ≥0} (hst : s ≤ t)
    (hφ : StronglyMeasurable[𝓕 s] φ) {K : ℝ} (hφb : ∀ ω, ‖φ ω‖ ≤ K) :
    ∫ ω, ⟪φ ω, S t ω - S s ω⟫_ℝ ∂Q = 0 := by
  have hm : 𝓕 s ≤ mΩ := 𝓕.le s
  have hΔ : Integrable (fun ω ↦ S t ω - S s ω) Q := (hS.integrable t).sub (hS.integrable s)
  -- `Q[S t − S s | 𝓕 s] = 0`.
  have hcond0 : Q[fun ω ↦ S t ω - S s ω | 𝓕 s] =ᵐ[Q] 0 := by
    have hsub : Q[fun ω ↦ S t ω - S s ω | 𝓕 s] =ᵐ[Q] Q[S t | 𝓕 s] - Q[S s | 𝓕 s] :=
      condExp_sub (hS.integrable t) (hS.integrable s) _
    have h1 : Q[S t | 𝓕 s] =ᵐ[Q] S s := hS.2 s t hst
    have h2 : Q[S s | 𝓕 s] = S s := condExp_of_stronglyMeasurable hm (hS.1 s) (hS.integrable s)
    filter_upwards [hsub, h1] with ω hω h1ω
    rw [hω, Pi.zero_apply, Pi.sub_apply, h1ω, h2, sub_self]
  -- Pull out `φ` and collapse.
  calc ∫ ω, ⟪φ ω, S t ω - S s ω⟫_ℝ ∂Q
      = ∫ ω, (Q[fun ω ↦ ⟪φ ω, S t ω - S s ω⟫_ℝ | 𝓕 s]) ω ∂Q := (integral_condExp hm).symm
    _ = ∫ ω, ⟪φ ω, (Q[fun ω ↦ S t ω - S s ω | 𝓕 s]) ω⟫_ℝ ∂Q :=
        integral_congr_ae (condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hφ
          (increment_integrable hS hφ hφb) hΔ)
    _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hcond0] with ω hω
        rw [hω]; simp

namespace IsEMM

variable {S : ℝ≥0 → Ω → F} {T : ℝ≥0} {Q : Measure Ω}

/-- **A martingale on all of `ℝ≥0` is an EMM at every horizon**, when its measure is an equivalent
probability measure. -/
theorem of_martingale [IsProbabilityMeasure Q] (hS : Martingale S 𝓕 Q) (hQP : Q ≪ P)
    (hPQ : P ≪ Q) (T : ℝ≥0) : IsEMM (P := P) (𝓕 := 𝓕) S T Q :=
  ⟨inferInstance, hQP, hPQ, martingale_stopped_of_setIntegral_eq (fun t _ ↦ hS.1 t)
    (fun t _ ↦ hS.integrable t) fun _ _ hst _ _ hA ↦ (hS.setIntegral_eq hst hA).symm⟩

omit [FiniteDimensional ℝ F] in
/-- Before the horizon the price is `𝓕`-adapted. -/
theorem adapted (h : IsEMM (P := P) (𝓕 := 𝓕) S T Q) {t : ℝ≥0} (ht : t ≤ T) :
    StronglyMeasurable[𝓕 t] (S t) := by
  simpa only [min_eq_left ht] using h.martingale.1 t

/-- Before the horizon the price is `Q`-integrable. -/
theorem integrable (h : IsEMM (P := P) (𝓕 := 𝓕) S T Q) {t : ℝ≥0} (ht : t ≤ T) :
    Integrable (S t) Q := by
  simpa only [min_eq_left ht] using h.martingale.integrable t

omit [FiniteDimensional ℝ F] in
/-- **The martingale property before the horizon**: `Q[S t | 𝓕 s] = S s` for `s ≤ t ≤ T`. -/
theorem condExp_eq (h : IsEMM (P := P) (𝓕 := 𝓕) S T Q) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : t ≤ T) : Q[S t | 𝓕 s] =ᵐ[Q] S s := by
  simpa only [min_eq_left ht, min_eq_left (hst.trans ht)] using h.martingale.condExp_ae_eq hst

end IsEMM

/-- **Forward continuous first FTAP: an equivalent martingale measure precludes simple-strategy
arbitrage.** If `Q` is an EMM for the discounted price `S` up to `T`, then no simple strategy
trading on `[0, T]` has gains that are `P`-a.s. nonnegative and strictly positive on a
`P`-non-null set.

The proof is the discrete forward theorem. A simple strategy `ψ` is a discrete predictable
strategy for the price sampled at its own trading dates (the schedule `n ↦ time (min n N)`, a
monotone schedule inside `[0, T]`): the sampled price is a `Q`-martingale for the sampled
filtration (`martingale_comp_monotone`), the holding `hold i` is predictable for it, and the
gains `ψ.gains S` are the martingale transform of the sampled price by the holdings. So
`emm_implies_no_arbitrage` (`FTAP.lean`) applies, and the continuous theorem has no argument of
its own. -/
theorem isEMM_noArbitrageSimple {S : ℝ≥0 → Ω → F} {T : ℝ≥0} {Q : Measure Ω}
    (h : IsEMM (P := P) (𝓕 := 𝓕) S T Q) : NoArbitrageSimple (P := P) (𝓕 := 𝓕) S T := by
  intro ψ hψT hnonneg
  haveI := h.isProb
  obtain ⟨K, hK⟩ := ψ.bdd
  -- the sampling schedule: the trading dates, held at the last one
  let t : ℕ → ℝ≥0 := fun n ↦ ψ.time ⟨min n ψ.N, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have ht : Monotone t := fun a b hab ↦ ψ.mono (Fin.mk_le_mk.mpr (min_le_min_right _ hab))
  have htT (n : ℕ) : t n ≤ T := (ψ.mono (Fin.le_last _)).trans hψT
  -- the holding in force over the `n`-th step, `0` outside the trading window
  let φ : ℕ → Ω → F := fun n ω ↦
    if hn : 0 < n ∧ n ≤ ψ.N then ψ.hold ⟨n - 1, by omega⟩ ω else 0
  have hφ (i : Fin ψ.N) : φ (i + 1) = ψ.hold i := by
    funext ω
    simp only [φ]
    rw [dif_pos ⟨by omega, i.2⟩]
    rfl
  have ht_castSucc (i : Fin ψ.N) : t i = ψ.time i.castSucc :=
    congrArg ψ.time (Fin.ext (min_eq_left i.2.le))
  have ht_succ (i : Fin ψ.N) : t (i + 1) = ψ.time i.succ :=
    congrArg ψ.time (Fin.ext (min_eq_left i.2))
  have hgain : martingaleTransform φ (fun n ↦ S (t n)) ψ.N = ψ.gains S := by
    funext ω
    unfold martingaleTransform SimpleStrategy.gains
    rw [← Fin.sum_univ_eq_sum_range
      (fun k ↦ ⟪φ (k + 1) ω, S (t (k + 1)) ω - S (t k) ω⟫_ℝ) ψ.N]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hφ, ht_succ, ht_castSucc]
  have hmain := emm_implies_no_arbitrage (T := ψ.N) (𝓕 := sampledFiltration 𝓕 ht)
    (S := fun n ↦ S (t n)) h.ac h.ac' (fun n _ ↦ h.adapted (htT n)) (fun n _ ↦ h.integrable (htT n))
    (fun n _ ↦ (h.condExp_eq (ht n.le_succ) (htT _)).symm) φ
    (fun n hn ↦ by
      have hn' : (⟨n, hn⟩ : Fin ψ.N) + 1 = n + 1 := rfl
      rw [← hn', hφ]
      change StronglyMeasurable[𝓕 (t n)] _
      rw [ht_castSucc ⟨n, hn⟩]
      exact ψ.meas ⟨n, hn⟩)
    ⟨max K 0, fun n _ ω ↦ by
      simp only [φ]
      split_ifs
      · exact (hK _ ω).trans (le_max_left _ _)
      · simp⟩
    (by simpa only [hgain] using hnonneg)
  simpa only [hgain] using hmain

end MathFin.ContinuousMarket
