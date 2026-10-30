/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianTransition
public import MathFin.BlackScholes.AmericanPut.Stopping.GridBellman

/-! # Markov representation of the physical-grid Bellman recursion

The recursion is deterministic Gaussian integration in the current log spot, along any monotone
schedule. Its identification with conditional expectation is stated once, for any filtration and
measure in which the log state is `IsGaussianMarkov`; the raw and usual Brownian filtrations and the
delayed grid are instances. No classical pricing solution is assumed.

## Result

Public entry points include `brownianGridMarkovAux`, `brownianGridMarkovAux_bound`,
`bellmanAux_eq_brownianGridMarkovAux`, `brownianGridPrice_eq_gridAmericanPutValue`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- Backward recursion in the log-spot variable `x` along a schedule `s`: stage `0` at index `i` is
`Z i`, and stage `n+1` is the max of `Z i x` with the `brownianHeatFlow` of stage `n` at index
`i+1`, run over the step from `s i` to `s (i+1)`. -/
noncomputable def brownianGridMarkovAux (Z : ℕ → ℝ → ℝ) (s : ℕ → ℝ≥0) (β σ : ℝ) :
    ℕ → ℕ → ℝ → ℝ
  | 0, i => Z i
  | n+1, i => fun x => max (Z i x)
      (brownianHeatFlow (brownianGridMarkovAux Z s β σ n (i+1))
        (σ^2*((s (i+1) : ℝ)-(s i : ℝ))).toNNReal
        (x+β*((s (i+1) : ℝ)-(s i : ℝ))))

theorem brownianGridMarkovAux_bound {Z : ℕ → ℝ → ℝ} {C : ℝ}
    (hb : ∀ i x, ‖Z i x‖ ≤ C) (s : ℕ → ℝ≥0) (β σ : ℝ) (n i : ℕ) (x : ℝ) :
    ‖brownianGridMarkovAux Z s β σ n i x‖ ≤ C := by
  induction n generalizing i x with
  | zero => exact hb i x
  | succ n ih =>
    have hheat := brownianHeatFlow_bound (ih (i+1))
      (σ^2*((s (i+1) : ℝ)-(s i : ℝ))).toNNReal (x+β*((s (i+1) : ℝ)-(s i : ℝ)))
    rw [Real.norm_eq_abs,abs_le] at hheat ⊢
    have hz := hb i x
    rw [Real.norm_eq_abs,abs_le] at hz
    exact ⟨hz.1.trans (le_max_left _ _),max_le hz.2 hheat.2⟩

theorem brownianGridMarkovAux_continuous {Z : ℕ → ℝ → ℝ} {C : ℝ}
    (hc : ∀ i, Continuous (Z i)) (hb : ∀ i x, ‖Z i x‖ ≤ C)
    (s : ℕ → ℝ≥0) (β σ : ℝ) (n i : ℕ) :
    Continuous (brownianGridMarkovAux Z s β σ n i) := by
  induction n generalizing i with
  | zero => exact hc i
  | succ n ih =>
    exact (hc i).max ((brownianHeatFlow_continuous (ih (i+1))
      (brownianGridMarkovAux_bound hb s β σ n (i+1))).comp
      (continuous_const.prodMk (continuous_id.add continuous_const)))

/-- The recursion only sees the increments of its schedule, so a delay does not change it. -/
theorem brownianGridMarkovAux_add_left (Z : ℕ → ℝ → ℝ) (u : ℝ≥0) {s' s : ℕ → ℝ≥0}
    (hs : ∀ j, s' j = u+s j) (β σ : ℝ) (n i : ℕ) :
    brownianGridMarkovAux Z s' β σ n i = brownianGridMarkovAux Z s β σ n i := by
  obtain rfl : s' = fun j => u+s j := funext hs
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [brownianGridMarkovAux,ih,NNReal.coe_add,add_sub_add_left_eq_sub]

/-- **The Bellman recursion on a sampled filtration is Gaussian integration in the log state.**
For any monotone schedule `s` and any log state `L` that is `IsGaussianMarkov` in `𝓕` under `P`,
the `bellmanAux` of the rewards `Z j (L (s j))` on the sampled filtration `𝓕 (s j)` is
`brownianGridMarkovAux Z s β σ n i` evaluated at `L (s i)`. -/
theorem bellmanAux_eq_brownianGridMarkovAux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {s : ℕ → ℝ≥0} (hs : Monotone s) {β σ : ℝ}
    {L : ℝ≥0 → Ω → ℝ} (hL : IsGaussianMarkov P 𝓕 β σ L) {Z : ℕ → ℝ → ℝ} {C : ℝ}
    (hc : ∀ i, Continuous (Z i)) (hb : ∀ i x, ‖Z i x‖ ≤ C) (n i : ℕ) :
    bellmanAux P (ContinuousMarket.sampledFiltration 𝓕 hs) (fun j ω => Z j (L (s j) ω)) n i
      =ᵐ[P] fun ω => brownianGridMarkovAux Z s β σ n i (L (s i) ω) := by
  induction n generalizing i with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hcond := condExp_congr_ae (m := ContinuousMarket.sampledFiltration 𝓕 hs i) (ih (i+1))
    have ht := hL (brownianGridMarkovAux_continuous hc hb s β σ n (i+1))
      (brownianGridMarkovAux_bound hb s β σ n (i+1)) (hs (Nat.le_succ i))
    filter_upwards [hcond,ht] with ω hω htω
    change max _ _ = max _ _
    rw [hω]
    exact congrArg (max _) htω

/-- The put payoff at log spot `x`, discounted to time zero: `exp (-r*t)*max (K-exp x) 0`. -/
noncomputable def discountedLogPayoff (K r : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (-r*(t : ℝ))*max (K-Real.exp x) 0

theorem discountedLogPayoff_continuous (K r : ℝ) (t : ℝ≥0) :
    Continuous (discountedLogPayoff K r t) := by
  unfold discountedLogPayoff
  fun_prop

theorem discountedLogPayoff_bound {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (t : ℝ≥0) (x : ℝ) : ‖discountedLogPayoff K r t x‖ ≤ K := by
  have he : Real.exp (-r*(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [t.coe_nonneg])
  have hp : 0 ≤ max (K-Real.exp x) 0 := le_max_right _ _
  have hpK : max (K-Real.exp x) 0 ≤ K := max_le (sub_le_self _ (Real.exp_pos x).le) hK
  rw [discountedLogPayoff,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hp)]
  exact (mul_le_mul_of_nonneg_right he hp).trans (by simpa using hpK)

theorem gridReward_eq_discountedLogPayoff (K r q σ x : ℝ) (T δ : ℝ≥0) :
    gridReward brownian K r q σ (Real.exp x) T δ =
      fun i ω => discountedLogPayoff K r (cappedGridTime T δ i)
        (brownianLogState (r-q-σ^2/2) σ x (cappedGridTime T δ i) ω) := by
  funext i ω
  simp only [gridReward,putRewardAt,putReward,MathFin.gbmValue,discountedLogPayoff,
    brownianLogState,cappedGridTime,Real.exp_add,mul_assoc]

/-- Deterministic Gaussian recursion for the actual capped-grid put value. -/
noncomputable def brownianGridPrice (K r q σ : ℝ) (T δ : ℝ≥0) (x : ℝ) : ℝ :=
  brownianGridMarkovAux (fun i => discountedLogPayoff K r (cappedGridTime T δ i))
    (cappedGridTime T δ) (r-q-σ^2/2) σ ⌈T/δ⌉₊ 0 x

theorem brownianGridPrice_continuous {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (q σ : ℝ) (T δ : ℝ≥0) : Continuous (brownianGridPrice K r q σ T δ) :=
  brownianGridMarkovAux_continuous (fun _ => discountedLogPayoff_continuous K r _)
    (fun _ x => discountedLogPayoff_bound hK hr _ x) _ (r-q-σ^2/2) σ _ _

/-- **The Gaussian recursion prices the grid put in any filtration where the log state is Gaussian
Markov.** Raw and usual Brownian filtrations are the two instances; `P` and `𝓕` are free. -/
theorem brownianGridPrice_eq_gridAmericanPutValue [MeasurableSpace (ℝ≥0 → ℝ)]
    {P : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace (ℝ≥0 → ℝ)›}
    (hW : Measurable (Function.uncurry brownian)) (ha : Adapted 𝓕 brownian)
    (hz : ∀ᵐ ω ∂P, brownian 0 ω = 0)
    (hL : ∀ β σ x, IsGaussianMarkov P 𝓕 β σ (brownianLogState β σ x))
    {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) (x : ℝ) :
    brownianGridPrice K r q σ T δ x = gridAmericanPutValue P 𝓕 brownian K r q σ (Real.exp x) T δ := by
  rw [gridValue_eq_bellman hW ha hK hr (Real.exp_pos x).le hδ]
  have he : bellmanAux P (cappedGridFiltration 𝓕 T δ)
      (fun j ω => discountedLogPayoff K r (cappedGridTime T δ j)
        (brownianLogState (r-q-σ^2/2) σ x (cappedGridTime T δ j) ω)) ⌈T/δ⌉₊ 0 =ᵐ[P]
      fun ω => brownianGridMarkovAux (fun i => discountedLogPayoff K r (cappedGridTime T δ i))
        (cappedGridTime T δ) (r-q-σ^2/2) σ ⌈T/δ⌉₊ 0
        (brownianLogState (r-q-σ^2/2) σ x (cappedGridTime T δ 0) ω) :=
    bellmanAux_eq_brownianGridMarkovAux (cappedGridTime_mono T δ) (hL (r-q-σ^2/2) σ x)
      (fun i => discountedLogPayoff_continuous K r (cappedGridTime T δ i))
      (fun i y => discountedLogPayoff_bound hK hr (cappedGridTime T δ i) y) ⌈T/δ⌉₊ 0
  rw [gridReward_eq_discountedLogPayoff]
  simp only [finiteBellman,Nat.sub_zero,min_eq_left (Nat.zero_le _)]
  rw [integral_congr_ae he]
  have he0 : (fun ω => brownianGridMarkovAux
      (fun i => discountedLogPayoff K r (cappedGridTime T δ i))
      (cappedGridTime T δ) (r-q-σ^2/2) σ ⌈T/δ⌉₊ 0
      (brownianLogState (r-q-σ^2/2) σ x (cappedGridTime T δ 0) ω)) =ᵐ[P]
      fun _ => brownianGridPrice K r q σ T δ x := by
    filter_upwards [hz] with ω hω
    simp [cappedGridTime,brownianLogState,hω,brownianGridPrice]
  rw [integral_congr_ae he0]
  simp

theorem brownianGridPrice_eq_gridValue {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) (x : ℝ) :
    brownianGridPrice K r q σ T δ x =
      gridAmericanPutValue gaussianLimit brownianFiltration brownian K r q σ (Real.exp x) T δ :=
  brownianGridPrice_eq_gridAmericanPutValue measurable_brownian_uncurry brownian_adapted
    isBrownianReal_brownian.eval_zero_ae_eq_zero brownianLogState_isGaussianMarkov hK hr T hδ x

theorem brownianGridPrice_tendsto {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => brownianGridPrice K r q σ T (gridStep n) x) atTop
      (𝓝 (brownianAmericanPut K r q σ (Real.exp x) T)) := by
  have he : (fun n => brownianGridPrice K r q σ T (gridStep n) x) =
      fun n => gridAmericanPutValue gaussianLimit brownianFiltration brownian
        K r q σ (Real.exp x) T (gridStep n) :=
    funext (fun n => brownianGridPrice_eq_gridValue hK hr T (gridStep_pos n) x)
  rw [he]
  exact gridValue_tendsto_americanValue measurable_brownian_uncurry continuous_brownian hK hr
      (Real.exp_pos x).le

end MathFin.BlackScholes.AmericanPut.Stopping
