/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.Binomial
public import MathFin.Contracts.Models.BlackScholes
public import MathFin.Binomial.CRRClosedForm

/-!
# One contract in two models: the tree's value converges to the Black–Scholes value

`europeanCall K T` is one term. Priced in the `n`-step Cox–Ross–Rubinstein tree over `[0, T]`
(`Contracts/Models/Binomial.lean`) it has one value for each `n`; priced in the Black–Scholes
model (`Contracts/Models/BlackScholes.lean`) it has another. This file proves the first converges
to the second.

The tree has step `T / n` (`crrStep`), per-step rate `r T / n` (`crrPerStepRate`), up and down
factors `e^{±σ √(T/n)}` (`crrUp`, `crrDown`), and flips that go up with probability
`crrProb r σ T n`. That probability is in `[0, 1]` for every `n` once `|r| √T < σ`
(`binomialNoArb_crr`, `crrProb_mem_Icc`), which is the one hypothesis added to the
Black–Scholes ones.

Nothing about the limit is proved here. Each tree value is the tree price
(`Binomial.value_europeanCall`), and the tree prices converge to the Black–Scholes closed form
(`binomialPrice_call_tendsto_bs_closed`, proved in `Binomial/CRRCharFun.lean` and
`Binomial/CRRClosedForm.lean`). That closed form is the Black–Scholes value of the same
contract (`BlackScholes.value_europeanCall`). This file only composes the three.

## Main results

* `tendsto_binomial_value_europeanCall` — the call's value in the `n`-step CRR tree tends to its
  Black–Scholes value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The tree's value of a European call converges to its Black–Scholes value.** The contract
`europeanCall K T` priced in the `n`-step CRR tree over `[0, T]` tends, as `n → ∞`, to the same
contract priced in the Black–Scholes model, provided the volatility dominates the drift over the
horizon (`|r| √T < σ`), which makes every tree with `n ≥ 1` arbitrage-free. -/
theorem tendsto_binomial_value_europeanCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S₀ K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (hbs : BSCallHyp Q S₀ K r σ T Z)
    (hrT : |r| * Real.sqrt T < σ) :
    Tendsto (fun n : ℕ ↦ (europeanCall K T).value
        (coinFlipMeasure (crrProb r σ T n).toNNReal (Real.toNNReal_le_one.mpr
          (crrProb_mem_Icc (fun _ hn ↦ binomialNoArb_crr hbs.T_pos hrT hn) n).2))
        (Binomial.discount (crrPerStepRate r T n) (crrStep T n))
        (Binomial.assets S₀ (crrUp σ T n) (crrDown σ T n) (crrStep T n))) atTop
      (𝓝 ((europeanCall K T).value Q (fun _ ↦ Real.exp (-r * T))
        (BlackScholes.assets S₀ r σ T Z))) := by
  have hna (n : ℕ) (hn : 0 < n) := binomialNoArb_crr hbs.T_pos hrT hn
  have hTN (n : ℕ) : (T : ℝ) / crrStep T n = n := div_div_cancel₀ hbs.T_pos.ne'
  rw [BlackScholes.value_europeanCall hbs, neg_mul]
  exact (binomialPrice_call_tendsto_bs_closed hbs.σ_pos hbs.T_pos hbs.S_0_pos hbs.K_pos hna).congr
    fun n ↦ (Binomial.value_europeanCall _
      (Real.coe_toNNReal _ (crrProb_mem_Icc hna n).1).symm S₀ K (hTN n)).symm

end MathFin.Contracts
