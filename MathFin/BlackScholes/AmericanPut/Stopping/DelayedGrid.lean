/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.SampledRules
public import MathFin.BlackScholes.AmericanPut.Stopping.UsualGridMarkov

/-! # Optimal finite-grid exercise after a deterministic waiting time 
## Result

Public entry points include `delayedGridTime`, `delayedGridTime_mono`, `delayedGridFiltration`,
`delayedBellmanAux_eq_markov`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The `i`-th capped grid time delayed by a waiting time: `u+cappedGridTime T δ i`. -/
def delayedGridTime (u T δ : ℝ≥0) (i : ℕ) : ℝ≥0 := u+cappedGridTime T δ i

theorem delayedGridTime_mono (u T δ : ℝ≥0) : Monotone (delayedGridTime u T δ) :=
  fun _ _ hij => add_le_add le_rfl (cappedGridTime_mono T δ hij)

/-- The Brownian filtration sampled along the delayed grid times. -/
noncomputable def delayedGridFiltration (u T δ : ℝ≥0) :=
  ContinuousMarket.sampledFiltration brownianFiltration (delayedGridTime_mono u T δ)

theorem delayedBellmanAux_eq_markov {Z : ℕ → ℝ → ℝ} {C : ℝ}
    (hc : ∀ i, Continuous (Z i)) (hb : ∀ i x, ‖Z i x‖ ≤ C)
    (u T δ : ℝ≥0) (β σ x : ℝ) (n i : ℕ) :
    bellmanAux gaussianLimit (delayedGridFiltration u T δ)
      (fun j ω => Z j (brownianLogState β σ x (delayedGridTime u T δ j) ω)) n i =ᵐ[gaussianLimit]
      fun ω => brownianGridMarkovAux Z T δ β σ n i
        (brownianLogState β σ x (delayedGridTime u T δ i) ω) := by
  induction n generalizing i with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hcond := condExp_congr_ae (m := delayedGridFiltration u T δ i) (ih (i+1))
    have ht := brownianLogState_condExp_transition
      (brownianGridMarkovAux_continuous hc hb T δ β σ n (i+1))
      (brownianGridMarkovAux_bound hb T δ β σ n (i+1))
      (delayedGridTime_mono u T δ (Nat.le_succ i)) β σ x
    have hdt : (delayedGridTime u T δ (i+1) : ℝ)-(delayedGridTime u T δ i : ℝ) =
        (cappedGridTime T δ (i+1) : ℝ)-(cappedGridTime T δ i : ℝ) := by
      simp only [delayedGridTime,NNReal.coe_add]
      ring
    rw [hdt] at ht
    filter_upwards [hcond,ht] with ω hω htω
    change max _ _ = max _ _
    rw [hω]
    exact congrArg (max _) htω

/-- The discounted put reward from spot `Real.exp x`, exercised at the deterministic time
`delayedGridTime u T δ i`. -/
noncomputable def delayedGridReward (K r q σ x : ℝ) (u T δ : ℝ≥0) (i : ℕ) : (ℝ≥0 → ℝ) → ℝ :=
  putReward brownian K r q σ (Real.exp x) (fun _ => delayedGridTime u T δ i)

theorem delayedGridReward_adapted (K r q σ x : ℝ) (u T δ : ℝ≥0) :
    Adapted (delayedGridFiltration u T δ) (delayedGridReward K r q σ x u T δ) := by
  intro i
  have hw := brownian_adapted (delayedGridTime u T δ i)
  unfold delayedGridReward putReward MathFin.gbmValue
  dsimp only
  fun_prop

theorem delayedGridReward_integrable {K r q σ x : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (u T δ : ℝ≥0) (i : ℕ) : Integrable (delayedGridReward K r q σ x u T δ i) gaussianLimit :=
  putReward_integrable measurable_brownian_uncurry gaussianLimit hK hr (Real.exp_pos x).le
      measurable_const

theorem delayedGridReward_eq (K r q σ x : ℝ) (u T δ : ℝ≥0) :
    delayedGridReward K r q σ x u T δ = fun i ω => Real.exp (-r*(u : ℝ))*
      discountedLogPayoff K r (cappedGridTime T δ i)
        (brownianLogState (r-q-σ^2/2) σ x (delayedGridTime u T δ i) ω) := by
  funext i ω
  unfold delayedGridReward putReward discountedLogPayoff MathFin.gbmValue brownianLogState
  dsimp only
  have he : Real.exp (-r*(delayedGridTime u T δ i : ℝ)) =
      Real.exp (-r*(u : ℝ))*Real.exp (-r*(cappedGridTime T δ i : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [delayedGridTime,NNReal.coe_add]
    ring
  rw [he]
  simp only [Real.exp_add,mul_assoc]

theorem delayedGrid_bellman_eq {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (u T δ : ℝ≥0) (x : ℝ) :
    finiteBellman gaussianLimit (delayedGridFiltration u T δ)
      (delayedGridReward K r q σ x u T δ) ⌈T/δ⌉₊ 0 =ᵐ[gaussianLimit]
      fun ω => Real.exp (-r*(u : ℝ))*brownianGridPrice K r q σ T δ
        (brownianLogState (r-q-σ^2/2) σ x u ω) := by
  rw [delayedGridReward_eq]
  simp only [finiteBellman,Nat.sub_zero,min_eq_left (Nat.zero_le _)]
  have hm := bellmanAux_const_mul (P := gaussianLimit) (𝓕 := delayedGridFiltration u T δ)
    (fun i ω => discountedLogPayoff K r (cappedGridTime T δ i)
      (brownianLogState (r-q-σ^2/2) σ x (delayedGridTime u T δ i) ω))
    (Real.exp_pos (-r*(u : ℝ))).le ⌈T/δ⌉₊ 0
  have he := delayedBellmanAux_eq_markov
    (fun i => discountedLogPayoff_continuous K r (cappedGridTime T δ i))
    (fun i y => discountedLogPayoff_bound hK hr (cappedGridTime T δ i) y)
    u T δ (r-q-σ^2/2) σ x ⌈T/δ⌉₊ 0
  filter_upwards [hm,he] with ω hmω heω
  rw [hmω,heω]
  simp [brownianGridPrice,delayedGridTime,cappedGridTime]

theorem delayedGridPrice_le_american {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (u T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) (x : ℝ) :
    (∫ ω, Real.exp (-r*(u : ℝ))*brownianGridPrice K r q σ T δ
      (brownianLogState (r-q-σ^2/2) σ x u ω) ∂gaussianLimit) ≤
      brownianAmericanPut K r q σ (Real.exp x) (u+T) := by
  let η := finiteBellmanRule (P := gaussianLimit) (delayedGridReward_adapted K r q σ x u T δ) ⌈T/δ⌉₊
  have hsT : delayedGridTime u T δ ⌈T/δ⌉₊ = u+T := by
    have hh : T ≤ (⌈T/δ⌉₊ : ℝ≥0)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ))
    simp only [delayedGridTime,cappedGridTime,min_eq_right hh]
  let hη := η.toSampledRule
  have hv := expectedReward_le_value (P := gaussianLimit) (q := q) (σ := σ)
    measurable_brownian_uncurry hK hr (Real.exp_pos x).le hη
  have hi := finiteBellmanContact_expected_payoff (P := gaussianLimit)
    (delayedGridReward_adapted K r q σ x u T δ) (delayedGridReward_integrable hK hr u T δ) ⌈T/δ⌉₊
  have he := integral_congr_ae (delayedGrid_bellman_eq (q := q) (σ := σ) hK hr u T δ x)
  rw [← he,← hi]
  convert! hv using 1
  rw [hsT]
  rfl

end MathFin.BlackScholes.AmericanPut.Stopping
