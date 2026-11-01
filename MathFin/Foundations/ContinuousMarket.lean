/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.EquivMeasure
public import MathFin.Foundations.FTAP
public import MathFin.Foundations.MartingaleFrozen
public import MathFin.Foundations.MartingaleSetIntegral
public import MathFin.Foundations.NoArbitrageCore

/-!
# Continuous-time market vocabulary: `IsEMM`, simple strategies, no-arbitrage

A **model-agnostic** frame for the continuous-time first fundamental theorem of asset
pricing (FTAP), parametric over a finite-dimensional real inner-product-space-valued
discounted price process `S : ℝ≥0 → Ω → F`. The Black–Scholes model (`ContinuousFTAP.lean`)
instantiates it at `F = ℝ`; a multi-asset model would instantiate at `F = Fin n → ℝ`.

* `IsEMM 𝓕 P S T Q` — `Q` is an equivalent martingale measure for `S` up to the horizon `T`:
  `Q ≈ P` (mutual absolute continuity) and `S` is a `Q`-martingale w.r.t. the filtration `𝓕` on
  `{t ≤ T}`, i.e. the process stopped at `T` is a `Q`-martingale. This is the discrete
  `MathFin.IsEMM` (`FTAP.lean`) with `ℝ≥0` for `ℕ`, and `IsEMM.sampled` restricts it to one; it is what an
  equivalent measure obtained by a density change on `𝓕_T` can be: the Girsanov/Esscher measure
  makes the discounted Black–Scholes price a martingale on `[0, T]` and no further
  (`bs_discounted_isEMM`). A martingale on all of `ℝ≥0` is an EMM at every horizon.
* `SimpleStrategy 𝓕 F` — a piecewise-constant, predictable, bounded trading strategy:
  finitely many trading dates `time : Fin (N+1) → ℝ≥0` and `𝓕`-measurable bounded holdings
  `hold : Fin N → Ω → F` between consecutive dates.
* `SimpleStrategy.gains` — the discounted terminal gains of a simple strategy against `S`.
* `NoArbitrageSimple 𝓕 P S T` — no simple strategy trading up to `T` has gains that are `P`-a.s.
  nonnegative and strictly positive on a `P`-non-null set.
* `martingale_stopped_of_setIntegral_eq` — the way an `IsEMM` is built: adaptedness, integrability
  and the set-integral martingale identity on `[0, T]` give the stopped martingale.
* `SimpleStrategy.schedule`, `SimpleStrategy.toDiscrete` — the strategy's trading dates as a
  monotone schedule `ℕ → ℝ≥0`, and its holdings as a discrete predictable strategy for the price
  sampled along it; `SimpleStrategy.gains_eq_martingaleTransform` says the gains are the
  martingale transform of the sampled price by it.
* `IsEMM.sampled` — a continuous-time EMM, sampled along a monotone schedule inside `[0, T]`, is a
  discrete-time `MathFin.IsEMM`.
* `isEMM_noArbitrageSimple` — the forward theorem: `IsEMM.sampled` along the strategy's schedule,
  then the discrete forward theorem `MathFin.IsEMM.noArbitrage` (vector-valued, `FTAP.lean`).

## Scope: meaning-1 (operational) vs. meaning-2 (Delbaen–Schachermayer) FTAP

This file builds **meaning 1**: an EMM for a *given* process, restricted to the honest,
economically transparent class of *simple* (piecewise-constant) strategies. It deliberately
does **not** build meaning 2, the Delbaen–Schachermayer theorem (`NFLVR ⟺ ∃ EMM` for a
general locally-bounded semimartingale, admissible strategies over a continuum of trading
times, and the general stochastic integral `∫ φ dS`). Absent by design:

* general **admissible** strategies (not just piecewise-constant) and the general stochastic
  integral `∫ φ dS` against a semimartingale;
* **NFLVR** (no free lunch with vanishing risk) and its distinction from plain no-arbitrage;
* the **converse** direction `NoArbitrageSimple 𝓕 P S T → ∃ Q, IsEMM 𝓕 P S T Q`, and closedness
  of the set of claims super-replicable from zero wealth (the Kreps–Yan / Hahn–Banach core DS needs).

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
structure IsEMM (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (S : ℝ≥0 → Ω → F) (T : ℝ≥0)
    (Q : Measure Ω) : Prop extends IsEquivProbMeasure P Q where
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
  refine martingale_of_setIntegral_eq
    (fun s ↦ (hadapt _ (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _)))
    (fun s ↦ hint _ (min_le_right _ _)) fun s t hst A hA ↦ ?_
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
def NoArbitrageSimple (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (S : ℝ≥0 → Ω → F) (T : ℝ≥0) :
    Prop :=
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

namespace SimpleStrategy

variable (ψ : SimpleStrategy 𝓕 F)

/-- The **sampling schedule** of a simple strategy: its trading dates `time 0 ≤ ⋯ ≤ time N`,
held at the last one. -/
def schedule (n : ℕ) : ℝ≥0 := ψ.time ⟨min n ψ.N, Nat.lt_succ_of_le (min_le_right _ _)⟩

omit [FiniteDimensional ℝ F] in
theorem monotone_schedule : Monotone ψ.schedule := fun _ _ hab ↦
  ψ.mono (Fin.mk_le_mk.mpr (min_le_min_right _ hab))

omit [FiniteDimensional ℝ F] in
/-- A strategy trading up to `T` has its whole schedule inside `[0, T]`. -/
theorem schedule_le {T : ℝ≥0} (hψT : ψ.time (Fin.last ψ.N) ≤ T) (n : ℕ) : ψ.schedule n ≤ T :=
  (ψ.mono (Fin.le_last _)).trans hψT

omit [FiniteDimensional ℝ F] in
theorem schedule_castSucc (i : Fin ψ.N) : ψ.schedule i = ψ.time i.castSucc :=
  congrArg ψ.time (Fin.ext (min_eq_left i.2.le))

omit [FiniteDimensional ℝ F] in
theorem schedule_succ (i : Fin ψ.N) : ψ.schedule (i + 1) = ψ.time i.succ :=
  congrArg ψ.time (Fin.ext (min_eq_left i.2))

/-- The simple strategy as a **discrete** one: the holding in force over the `n`-th step of the
schedule, `0` outside the trading window. -/
def toDiscrete : ℕ → Ω → F := fun n ω ↦
  if hn : 0 < n ∧ n ≤ ψ.N then ψ.hold ⟨n - 1, by omega⟩ ω else 0

omit [FiniteDimensional ℝ F] in
theorem toDiscrete_succ (i : Fin ψ.N) : ψ.toDiscrete (i + 1) = ψ.hold i := by
  funext ω
  simp only [toDiscrete]
  rw [dif_pos ⟨by omega, i.2⟩]
  rfl

omit [FiniteDimensional ℝ F] in
/-- The discrete strategy is predictable for the filtration sampled along the schedule. -/
theorem toDiscrete_predictable :
    ∀ t < ψ.N, StronglyMeasurable[sampledFiltration 𝓕 ψ.monotone_schedule t]
      (ψ.toDiscrete (t + 1)) := fun n hn ↦ by
  rw [show n + 1 = ((⟨n, hn⟩ : Fin ψ.N) : ℕ) + 1 from rfl, toDiscrete_succ]
  change StronglyMeasurable[𝓕 (ψ.schedule n)] _
  rw [schedule_castSucc ψ ⟨n, hn⟩]
  exact ψ.meas ⟨n, hn⟩

omit [FiniteDimensional ℝ F] in
/-- The discrete strategy is bounded. -/
theorem toDiscrete_bdd : ∃ K : ℝ, ∀ n ≤ ψ.N, ∀ ω, ‖ψ.toDiscrete n ω‖ ≤ K := by
  obtain ⟨K, hK⟩ := ψ.bdd
  refine ⟨max K 0, fun n _ ω ↦ ?_⟩
  simp only [toDiscrete]
  split_ifs
  · exact (hK _ ω).trans (le_max_left _ _)
  · simp

omit [FiniteDimensional ℝ F] in
/-- **The gains of a simple strategy are the martingale transform**, by its discrete holdings, of
the price sampled along its schedule. -/
theorem gains_eq_martingaleTransform (S : ℝ≥0 → Ω → F) :
    ψ.gains S = martingaleTransform ψ.toDiscrete (fun n ↦ S (ψ.schedule n)) ψ.N := by
  funext ω
  unfold martingaleTransform SimpleStrategy.gains
  rw [← Fin.sum_univ_eq_sum_range
    (fun k ↦ ⟪ψ.toDiscrete (k + 1) ω, S (ψ.schedule (k + 1)) ω - S (ψ.schedule k) ω⟫_ℝ) ψ.N]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [toDiscrete_succ, schedule_succ, schedule_castSucc]

end SimpleStrategy

namespace IsEMM

variable {S : ℝ≥0 → Ω → F} {T : ℝ≥0} {Q : Measure Ω}

/-- **A martingale on all of `ℝ≥0` is an EMM at every horizon**, when its measure is an equivalent
probability measure. -/
theorem of_martingale [IsProbabilityMeasure Q] (hS : Martingale S 𝓕 Q) (hQP : Q ≪ P)
    (hPQ : P ≪ Q) (T : ℝ≥0) : IsEMM 𝓕 P S T Q :=
  ⟨⟨inferInstance, hQP, hPQ⟩, martingale_stopped_of_setIntegral_eq (fun t _ ↦ hS.1 t)
    (fun t _ ↦ hS.integrable t) fun _ _ hst _ _ hA ↦ (hS.setIntegral_eq hst hA).symm⟩

/-- Before the horizon the price is `𝓕`-adapted. -/
theorem adapted (h : IsEMM 𝓕 P S T Q) {t : ℝ≥0} (ht : t ≤ T) :
    StronglyMeasurable[𝓕 t] (S t) :=
  haveI := h.isProb
  (martingale_min_iff.mp h.martingale).1 t ht

/-- Before the horizon the price is `Q`-integrable. -/
theorem integrable (h : IsEMM 𝓕 P S T Q) {t : ℝ≥0} (ht : t ≤ T) : Integrable (S t) Q :=
  haveI := h.isProb
  (martingale_min_iff.mp h.martingale).2.1 t ht

/-- **The martingale property before the horizon**: `Q[S t | 𝓕 s] = S s` for `s ≤ t ≤ T`. -/
theorem condExp_eq (h : IsEMM 𝓕 P S T Q) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : t ≤ T) : Q[S t | 𝓕 s] =ᵐ[Q] S s :=
  haveI := h.isProb
  ((martingale_min_iff.mp h.martingale).2.2 hst ht).symm

/-- **A continuous-time EMM, sampled, is a discrete-time EMM.** If `Q` is an equivalent
martingale measure up to `T` for the discounted price `S` in continuous time, then along
any monotone schedule `t 0 ≤ t 1 ≤ ⋯` whose first `T' + 1` dates lie in `[0, T]` it is an
equivalent martingale measure, at the discrete horizon `T'`, for the sampled price `n ↦ S (t n)`
and the sampled filtration `n ↦ 𝓕 (t n)`. General Ω; the sampled martingale is built from the
three consequences of `IsEMM` before the horizon (`martingale_min_iff`). -/
theorem sampled (h : IsEMM 𝓕 P S T Q) {t : ℕ → ℝ≥0} (ht : Monotone t) (T' : ℕ)
    (hT' : t T' ≤ T) :
    MathFin.IsEMM (sampledFiltration 𝓕 ht) P (fun n ↦ S (t n)) T' Q :=
  haveI := h.isProb
  ⟨h.toIsEquivProbMeasure, martingale_min_iff.mpr
    ⟨fun n hn ↦ h.adapted (t := t n) ((ht hn).trans hT'),
      fun n hn ↦ h.integrable (t := t n) ((ht hn).trans hT'),
      fun m n hmn hnT' ↦ (h.condExp_eq (s := t m) (t := t n) (ht hmn) ((ht hnT').trans hT')).symm⟩⟩

end IsEMM

/-- **Forward continuous first FTAP: an equivalent martingale measure precludes simple-strategy
arbitrage.** If `Q` is an EMM for the discounted price `S` up to `T`, then no simple strategy
trading on `[0, T]` has gains that are `P`-a.s. nonnegative and strictly positive on a
`P`-non-null set.

The proof is the discrete forward theorem. A simple strategy `ψ` is a discrete predictable
strategy (`toDiscrete`) for the price sampled at its own trading dates (`schedule`, a monotone
schedule inside `[0, T]`): the sampled price is a discrete EMM (`IsEMM.sampled`) and the gains
`ψ.gains S` are the martingale transform of the sampled price by the holdings
(`gains_eq_martingaleTransform`). So `MathFin.IsEMM.noArbitrage` (`FTAP.lean`) applies, and the
continuous theorem has no argument of its own. -/
theorem isEMM_noArbitrageSimple {S : ℝ≥0 → Ω → F} {T : ℝ≥0} {Q : Measure Ω}
    (h : IsEMM 𝓕 P S T Q) : NoArbitrageSimple 𝓕 P S T := fun ψ hψT hnonneg ↦ by
  rw [ψ.gains_eq_martingaleTransform] at hnonneg ⊢
  have hzero := (h.sampled ψ.monotone_schedule ψ.N (ψ.schedule_le hψT _)).noArbitrage
    ψ.toDiscrete ψ.toDiscrete_predictable ψ.toDiscrete_bdd hnonneg
  exact measure_mono_null (fun ω hω ↦ ne_of_gt hω) (ae_iff.mp hzero)

end MathFin.ContinuousMarket
