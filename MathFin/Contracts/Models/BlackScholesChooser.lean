/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.BlackScholesAsian
public import MathFin.Contracts.Parity
public import MathFin.BlackScholes.ChooserComposition
public import MathFin.Bridges.BSCallHypFromBrownian

/-!
# The chooser option priced along the Black–Scholes path

`chooser K r T t₁` is the call at `(K, T)` plus the put at `t₁` struck at `K e^{−r(T−t₁)}`
(`Contracts/Instruments/Options.lean`), two single cash flows at two different dates. Pricing it
needs the underlying at both, so the model is `BlackScholes.pathAssets`, the geometric Brownian
path of a pre-Brownian motion, with the discount `D u = e^{−ru}`.

Nothing new is proved about Black–Scholes. Each leg is a discounted European payoff at a single
date, whose spot there is `bsTerminal` of the standardised Brownian value; `bs_call_formula` and
`bs_put_formula` price them and `chooserPrice_expanded` identifies the sum with the closed form
`chooserPrice`.

## Main results

* `BlackScholes.value_chooser` — `chooser K r T t₁` is worth `chooserPrice S₀ K r σ T t₁`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- At a positive date `u` the geometric Brownian path is `bsTerminal` of the standardised
Brownian value `B_u / √u`: the `√u` cancels (`bsTerminal_via_brownian`). -/
theorem pathAssets_eq_bsTerminal (B : ℝ≥0 → Ω → ℝ) {u : ℝ≥0} (hu : 0 < (u : ℝ)) (S_0 r σ : ℝ)
    (ω : Ω) :
    pathAssets S_0 r σ B () u ω = bsTerminal S_0 r σ u (B u ω / Real.sqrt u) := by
  simpa [pathAssets] using (bsTerminal_via_brownian B (S_0 := S_0) (r := r) (σ := σ) hu ω).symm

/-- **The chooser's Black–Scholes value** is the closed form `chooserPrice`: for a pre-Brownian
motion `B` under a probability measure `μ`, positive spot, strike and volatility and positive
dates `t₁`, `T`, the replicating portfolio `chooser K r T t₁` with the discount `e^{−ru}` is
worth `bsV K r σ S₀ T + bsP (K e^{−r(T−t₁)}) r σ S₀ t₁`. No ordering of `t₁` and `T` is needed for
the identity; the contract is a chooser when `t₁ ≤ T`. -/
theorem value_chooser {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T t₁ : ℝ≥0} (hT : 0 < (T : ℝ)) (ht₁ : 0 < (t₁ : ℝ))
    {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) :
    (chooser K r T t₁).value μ (fun u ↦ Real.exp (-r * u)) (pathAssets S_0 r σ B)
      = chooserPrice S_0 K r σ T t₁ := by
  have hyp {u : ℝ≥0} (hu : 0 < (u : ℝ)) {K : ℝ} (hK : 0 < K) :
      BSCallHyp μ S_0 K r σ u (fun ω ↦ B u ω / Real.sqrt u) := by
    simpa using BSCallHyp.of_isPreBrownian μ B hB hS₀ hK hσ hu
  have hX {u : ℝ≥0} (hu : 0 < (u : ℝ)) : Integrable (fun ω ↦
      Real.exp (-r * u) * pathAssets S_0 r σ B () u ω) μ := by
    simp only [pathAssets_eq_bsTerminal B hu]
    exact (integrable_bsTerminal (hyp hu hK).Z_law S_0 r σ u).const_mul _
  have hKd : 0 < K * Real.exp (-(r * ((T : ℝ) - t₁))) := mul_pos hK (Real.exp_pos _)
  rw [chooser, Contract.value_both _ _ _ _ _ (integrable_europeanCall_pathPV (hX hT))
      (integrable_europeanPut_pathPV (hX ht₁)), europeanCall, europeanPut, Contract.value_pay,
    Contract.value_pay]
  simp only [europeanCallPayoff, Payoff.eval, scenarioAt, pathAssets_eq_bsTerminal B hT,
    pathAssets_eq_bsTerminal B ht₁]
  rw [bs_call_formula (hyp hT hK), bs_put_formula (hyp ht₁ hKd), chooserPrice_expanded]
  simp only [neg_mul]
