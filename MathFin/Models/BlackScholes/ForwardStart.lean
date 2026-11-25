/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.BSCallHypFromBrownian
public import MathFin.Models.BlackScholes.BlackScholesChooser
public import MathFin.Models.BlackScholes.Forward
public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.PDE
public import MathFin.Probability.Analysis.IndepFreezing

/-!
# The forward-start call in the Black–Scholes market

A forward-start call sets its strike at a future reset date `t₁` as a fixed multiple `α` of the
asset price then observed, and pays `max (S_T − α S_{t₁}) 0` at the maturity `T`
(`forwardStartCall`, the first payoff in the language whose strike is an observation).
Under the risk-neutral
dynamics the ratio `S_T / S_{t₁}` is a function of the Brownian increment `B_T − B_{t₁}`, which is
independent of everything known at `t₁`, so the price factorizes (`condExp_mul_of_indep`): the
discounted price at `t₁` freezes at its mean, and the payoff of the ratio keeps the law of a
unit-spot asset over the remaining time `τ = T − t₁`. The frozen leg contributes the martingale
mean `e^{−rt₁} 𝔼[S_{t₁}] = S₀` (`discounted_terminal_eq_S0`), the ratio leg the Black–Scholes call
price on a unit spot, `bsV α r σ 1 τ` (`integral_bsCall_payoff_eq_bsV`). The closed form
`S₀ · bsV α r σ 1 (T − t₁)` is Rubinstein's at zero dividend yield: the general formula's factor
`e^{−qt₁}` is absent because this market's asset pays no dividends.

## Main results

* `value_forwardStartCall`: on the risk-neutral geometric Brownian path of a filtered
  pre-Brownian motion, the forward-start call's value is `S₀ · bsV α r σ 1 (T − t₁)`.
* `price_forwardStartCall_constGirsanovMeasure`: in the Black–Scholes market, under the Girsanov
  pricing measure of the market price of risk, the forward-start call has that same price,
  whatever the physical drift.

## References

* [M. Rubinstein, *Pay now, choose later*][Rubinstein1991PayNow] (the Risk column's volume and
  issue follow the issue trail; its page numbers could not be verified from this machine)
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 26 §5 (11th ed.)
* [QuantLib, `ql/pricingengines/forward/forwardengine.hpp`][QuantLibForwardEngine] (the reference
  implementation; at zero dividend yield it reaches the closed form above)
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII],
  3.3.2; 3.3.4

## Tags

forward-start option, delayed strike, Black–Scholes market, independent increments, geometric
Brownian motion, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The forward-start call's Black–Scholes value.** For a filtered pre-Brownian motion `B`
under a probability measure `Q`, the value of `forwardStartCall α t₁ T` on the risk-neutral asset
`pathAssets S₀ r σ B` at the discount `e^{−rT}` is `S₀ · bsV α r σ 1 (T − t₁)`: the payoff
factorizes as the price at `t₁` against the ratio `S_T/S_{t₁}`, the increment `B_T − B_{t₁}` is
independent of `𝓕 t₁` (so the expectation of the product splits, `condExp_mul_of_indep`), the
frozen leg has mean `e^{−rt₁}𝔼[S_{t₁}] = S₀` (`discounted_terminal_eq_S0`), and the ratio leg is
`bsV` on a unit spot (`integral_bsCall_payoff_eq_bsV`). Rubinstein's formula at zero dividend
yield; the general formula's `e^{−qt₁}` factor is absent because this asset pays no dividends. -/
theorem value_forwardStartCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredPreBrownian B 𝓕 Q)
    {S_0 r α σ : ℝ} {t₁ T : ℝ≥0} (hS₀ : 0 < S_0) (hα : 0 < α) (hσ : 0 < σ)
    (ht₁ : 0 < (t₁ : ℝ)) (hτ : (t₁ : ℝ) < (T : ℝ)) :
    (forwardStartCall α t₁ T).value Q (fun _ _ ↦ Real.exp (-(r * (T : ℝ))))
        (pathAssets S_0 r σ B)
      = S_0 * bsV α r σ 1 ((T : ℝ) - (t₁ : ℝ)) := by
  have hT : 0 < (T : ℝ) := lt_trans ht₁ hτ
  have ht₁T : t₁ ≤ T := by exact_mod_cast hτ.le
  have hposT : ∀ ω, 0 ≤ pathAssets S_0 r σ B () T ω := by
    intro ω
    unfold pathAssets
    exact mul_nonneg hS₀.le (Real.exp_pos _).le
  have hpos₁ : ∀ ω, 0 ≤ pathAssets S_0 r σ B () t₁ ω := by
    intro ω
    unfold pathAssets
    exact mul_nonneg hS₀.le (Real.exp_pos _).le
  -- the law of the standardized increment `(B_T − B_{t₁})/√τ`
  have hZlaw : HasLaw (fun ω ↦ (B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ)))
      (gaussianReal 0 1) Q := by
    have hB' : IsPreBrownianReal B Q := hB.toIsPreBrownianReal
    have hshift := scaled_isPreBrownian_eval_law
      (fun t ω ↦ B (t₁ + t) ω - B t₁ ω) (hB'.shift t₁)
      (T := (T : ℝ) - (t₁ : ℝ)) (sub_pos.2 hτ)
    have hcoe : t₁ + Real.toNNReal ((T : ℝ) - (t₁ : ℝ)) = T := by
      apply NNReal.eq
      push_cast
      rw [Real.coe_toNNReal _ (sub_nonneg.2 (by exact_mod_cast hτ.le))]
      ring
    have hfun : (fun ω ↦ (fun t ω ↦ B (t₁ + t) ω - B t₁ ω)
          (Real.toNNReal ((T : ℝ) - (t₁ : ℝ))) ω / Real.sqrt ((T : ℝ) - (t₁ : ℝ)))
        = fun ω ↦ (B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ)) := by
      funext ω
      simp only []
      rw [hcoe]
    rw [hfun] at hshift
    exact hshift
  -- the two legs' Black-Scholes hypotheses
  have hZ₁ : BSCallHyp Q S_0 1 r σ (t₁ : ℝ) (fun ω ↦ B t₁ ω / Real.sqrt (t₁ : ℝ)) := by
    simpa using BSCallHyp.of_isPreBrownian Q B hB.toIsPreBrownianReal hS₀ one_pos hσ ht₁
  have hZT : BSCallHyp Q S_0 1 r σ (T : ℝ) (fun ω ↦ B T ω / Real.sqrt (T : ℝ)) := by
    simpa using BSCallHyp.of_isPreBrownian Q B hB.toIsPreBrownianReal hS₀ one_pos hσ hT
  have hZ₂ : BSCallHyp Q 1 α r σ ((T : ℝ) - (t₁ : ℝ))
      (fun ω ↦ (B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) :=
    ⟨one_pos, hα, hσ, sub_pos.2 hτ, hZlaw⟩
  -- integrability of the two legs
  have hint₁ : Integrable (fun ω ↦ pathAssets S_0 r σ B () t₁ ω) Q := by
    rw [funext fun ω ↦ pathAssets_eq_bsTerminal B ht₁ S_0 r σ ω]
    exact integrable_bsTerminal hZ₁.Z_law S_0 r σ (t₁ : ℝ)
  have hintT : Integrable (fun ω ↦ pathAssets S_0 r σ B () T ω) Q := by
    rw [funext fun ω ↦ pathAssets_eq_bsTerminal B hT S_0 r σ ω]
    exact integrable_bsTerminal hZT.Z_law S_0 r σ (T : ℝ)
  have hYi : Integrable
      (fun ω ↦ max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
        ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0) Q :=
    ((integrable_bsTerminal hZlaw 1 r σ ((T : ℝ) - (t₁ : ℝ))).sub'
      (integrable_const α)).pos_part
  -- the frozen leg is strongly measurable for `𝓕 t₁`
  have hXm : StronglyMeasurable[𝓕 t₁]
      (fun ω ↦ Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) := by
    simp only [pathAssets]
    have hm : Measurable[𝓕 t₁] (B t₁) :=
      StronglyMeasurable.measurable (hB.stronglyAdapted t₁)
    exact Measurable.stronglyMeasurable (Measurable.const_mul
      (Measurable.const_mul (Measurable.exp (Measurable.const_add
        (Measurable.const_mul hm σ) ((r - σ ^ 2 / 2) * (t₁ : ℝ)))) S_0)
      (Real.exp (-(r * (T : ℝ)))))
  -- the ratio leg is measurable for the σ-algebra of the increment
  have hYm : StronglyMeasurable[MeasurableSpace.comap (B T - B t₁) inferInstance]
      (fun ω ↦ max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
        ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0) := by
    have hcont : Continuous fun y : ℝ ↦ max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
        (y / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 := by
      unfold bsTerminal
      fun_prop
    exact hcont.stronglyMeasurable.comp_measurable (comap_measurable _)
  -- the increment's σ-algebra is inside the ambient one
  have hmeasΔ : Measurable (B T - B t₁) :=
    ((hB.stronglyAdapted T).measurable.mono (𝓕.le T) le_rfl).sub
      ((hB.stronglyAdapted t₁).measurable.mono (𝓕.le t₁) le_rfl)
  -- the pointwise factorization of the discounted payoff
  have hfactor : ∀ ω, Real.exp (-(r * (T : ℝ))) *
      max (pathAssets S_0 r σ B () T ω - α * pathAssets S_0 r σ B () t₁ ω) 0
      = (Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
        max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 := by
    intro ω
    have hratio : pathAssets S_0 r σ B () T ω = pathAssets S_0 r σ B () t₁ ω *
        Real.exp ((r - σ ^ 2 / 2) * ((T : ℝ) - (t₁ : ℝ)) + σ * (B T ω - B t₁ ω)) := by
      unfold pathAssets
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hbs : Real.exp ((r - σ ^ 2 / 2) * ((T : ℝ) - (t₁ : ℝ)) + σ * (B T ω - B t₁ ω))
        = bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) := by
      unfold bsTerminal
      rw [one_mul]
      congr 1
      have hne : Real.sqrt ((T : ℝ) - (t₁ : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.2 hτ)).ne'
      field_simp
    rw [hratio, hbs, mul_comm α (pathAssets S_0 r σ B () t₁ ω), ← mul_sub]
    by_cases hle : bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
        ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) ≤ α
    · have hle' : bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α ≤ 0 := sub_nonpos.2 hle
      rw [max_eq_right ((mul_nonpos_iff).2 (Or.inl ⟨hpos₁ ω, hle'⟩)), max_eq_right hle']
      ring
    · have hlt : 0 ≤ bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α :=
        sub_nonneg.2 (le_of_lt (not_le.mp hle))
      rw [max_eq_left (mul_nonneg (hpos₁ ω) hlt), max_eq_left hlt]
      ring
  -- the product is integrable
  have hint : Integrable (fun ω ↦ (Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
      max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
        ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0) Q := by
    have hbound : ∀ ω, ‖(Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
        max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0‖
        ≤ Real.exp (-(r * (T : ℝ))) *
          (pathAssets S_0 r σ B () T ω + α * pathAssets S_0 r σ B () t₁ ω) := by
      intro ω
      have hnn : 0 ≤ (Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
          max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
            ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 :=
        mul_nonneg (mul_nonneg (Real.exp_pos _).le (hpos₁ ω)) (le_max_right _ _)
      rw [Real.norm_of_nonneg hnn, ← hfactor ω]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hαp : 0 ≤ α * pathAssets S_0 r σ B () t₁ ω :=
        mul_nonneg hα.le (hpos₁ ω)
      refine max_le ?_ (by linarith [hposT ω, hαp])
      linarith [hposT ω, hαp]
    refine Integrable.mono' ((hintT.add (hint₁.const_mul α)).const_mul _) ?_
      (ae_of_all _ hbound)
    exact ((hXm.mono (𝓕.le t₁)).mul (hYm.mono hmeasΔ.comap_le)).aestronglyMeasurable
  -- the expectation of the product splits
  have hsplit : ∫ ω, (Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
      max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
        ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 ∂Q
      = (∫ ω, Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω ∂Q) *
        (∫ ω, max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 ∂Q) := by
    have hmul := condExp_mul_of_indep (𝓕.le t₁) hmeasΔ.comap_le (hB.indep t₁ T ht₁T) hXm hYm
      (hint₁.const_mul _) hYi
    have hmul' : Q[fun ω ↦ (Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
        max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
          ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 | 𝓕 t₁]
        =ᵐ[Q] fun ω ↦ (Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω) *
          (∫ ω, max (bsTerminal 1 r σ ((T : ℝ) - (t₁ : ℝ))
            ((B T ω - B t₁ ω) / Real.sqrt ((T : ℝ) - (t₁ : ℝ))) - α) 0 ∂Q) := hmul
    rw [← integral_condExp (𝓕.le t₁), integral_congr_ae hmul', integral_mul_const]
  -- the frozen leg's mean is the spot
  have hEX : ∫ ω, Real.exp (-(r * (T : ℝ))) * pathAssets S_0 r σ B () t₁ ω ∂Q
      = S_0 * Real.exp (-(r * ((T : ℝ) - (t₁ : ℝ)))) := by
    rw [integral_const_mul, integral_congr_ae
      (ae_of_all _ fun ω ↦ by rw [pathAssets_eq_bsTerminal B ht₁ S_0 r σ ω])]
    have hd := discounted_terminal_eq_S0 hZ₁
    rw [integral_const_mul] at hd
    have hexp : Real.exp (-(r * (T : ℝ)))
        = Real.exp (-(r * (t₁ : ℝ))) * Real.exp (-(r * ((T : ℝ) - (t₁ : ℝ)))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    linear_combination Real.exp (-(r * ((T : ℝ) - (t₁ : ℝ)))) * hd
  -- the ratio leg is `bsV` on a unit spot
  have hEY := integral_bsCall_payoff_eq_bsV hZ₂
  rw [integral_const_mul] at hEY
  rw [forwardStartCall, Contract.value_pay]
  simp only [Payoff.eval, scenarioAt]
  rw [integral_congr_ae (ae_of_all _ hfactor), hsplit, hEX, mul_assoc, ← neg_mul, hEY]

/-- **The forward-start call in the Black–Scholes market** is worth Rubinstein's closed form
`S₀ · bsV α r σ 1 (T − t₁)` under the Girsanov pricing measure of the market price of risk
`θ = (m − r)/σ` at any horizon `H` covering the maturity, whatever the physical drift `m`: the
price is the contract's value on the physical asset (`price_market`), which under `Q` reads the
asset as the risk-neutral path (`value_physical_eq_riskNeutral`), and that value is
`value_forwardStartCall`. The hypotheses mirror `price_europeanCall_constGirsanovMeasure` (positive
spot, strike multiple and volatility), with the reset date `t₁` strictly between now and the
maturity `T`. -/
theorem price_forwardStartCall_constGirsanovMeasure {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))
    {S_0 m r σ α : ℝ} {t₁ T H : ℝ≥0} (hT₁H : t₁ ≤ H) (hTH : T ≤ H) (hS₀ : 0 < S_0)
    (hα : 0 < α) (hσ : 0 < σ) (ht₁ : 0 < (t₁ : ℝ)) (hτ : (t₁ : ℝ) < (T : ℝ)) :
    (market μ hWmeas S_0 m r σ).price (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (forwardStartCall α t₁ T)
      = S_0 * bsV α r σ 1 ((T : ℝ) - (t₁ : ℝ)) := by
  have hQ : IsProbabilityMeasure (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) :=
    constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hfix : (forwardStartCall α t₁ T).FixedDated := by
    simp [forwardStartCall, Contract.FixedDated]
  have hval : (forwardStartCall α t₁ T).value
      (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) (fun t _ ↦ Real.exp (-r * t))
      (pathAssets S_0 r σ (constBtheta (μ := μ) hWmeas ((m - r) / σ) H))
      = (forwardStartCall α t₁ T).value
          (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
          (fun _ _ ↦ Real.exp (-(r * (T : ℝ))))
          (pathAssets S_0 r σ (constBtheta (μ := μ) hWmeas ((m - r) / σ) H)) := by
    unfold Contract.value
    refine integral_congr_ae (.of_forall fun ω ↦ (forwardStartCall α t₁ T).pathPV_congr hfix
      (fun t ht ↦ ?_) fun _ _ ↦ rfl)
    obtain rfl : t = T := by simpa [forwardStartCall, Contract.dates] using ht
    show Real.exp (-r * (t : ℝ)) = Real.exp (-(r * (t : ℝ)))
    rw [neg_mul]
  rw [price_market, value_physical_eq_riskNeutral hW hWmeas hσ.ne' H _ hfix fun p hp ↦ by
    simp only [forwardStartCall, Contract.obsList, Payoff.obsList, List.append_nil,
      List.nil_append, List.mem_append, List.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption, hval]
  exact value_forwardStartCall (isFilteredPreBrownian_constBtheta hW hWmeas ((m - r) / σ) H)
    hS₀ hα hσ ht₁ hτ

end MathFin.Contracts.BlackScholes
