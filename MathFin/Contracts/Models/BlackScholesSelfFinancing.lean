/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.BlackScholesHedge
public import MathFin.Foundations.ItoProductRule

/-!
# The Black–Scholes delta hedge is self-financing

`BlackScholesHedge` states the replication theorem in discounted terms:
`e^{−rt} C(t, S_t) = C(0, S₀) + ∫₀ᵗ Δ σ e^{−rs} S_s dB_s`. This file turns it into the statement
that the stock-and-bank portfolio finances itself. With the undiscounted value
`V_t = C(t, S_t)`, the delta `Δ_t = Φ(d₁(S_t, T − t))` and the bank position
`ψ_t = V_t − Δ_t S_t`, almost surely, for all `t ≤ T'` at once (`T' < T`),

  `V_t = V₀ + (∫₀ᵗ Δ_s r S_s ds + ∫₀ᵗ Δ_s σ S_s dB_s) + ∫₀ᵗ r ψ_s ds`,

with `V₀ = (europeanCall K T).value` (`europeanCall_selfFinancing`). The bracket is the gain
`∫ Δ dS` of holding `Δ` shares, `dS = r S dt + σ S dB`; the last term is the interest on the bank
position. The stochastic integral is the library's `predItoIntegral`.

The proof is the product rule with the finite-variation factor `e^{rt}`, applied to the discounted
value, which is the Itô process `localItoProcess` of the delta-hedge integrand (capped in time so
that its paths are continuous, `timeCap`): Itô's formula for `f(t, x) = e^{rt} x`
(`ito_formula_adapted_unbounded_process`, the product rule with a deterministic factor) gives
`V_t = V₀ + ∫₀ᵗ r V_s ds + ∫₀ᵗ e^{rs} H_s dB_s`, where `H` is the discounted integrand
`Δ σ e^{−rs} S_s`, and `r V = Δ r S + r ψ` splits the drift.

Not here: the self-financing property as a trading-strategy structure, the identity up to `t = T`,
and the integral `∫ Δ dS` as an integral against the semimartingale `S`: the gain is written as
its drift integral plus the Brownian integral of `Δ σ S`.

## Main definitions

* `hedgeDelta`, `hedgeValue`, `hedgeBank`: the delta `Φ(d₁)`, the value `C(t, S_t)` and the bank
  position `C − Δ S` along the Black–Scholes path.

## Main results

* `BlackScholes.europeanCall_selfFinancing`: the self-financing equation above.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], §4.5

## Tags

self-financing strategy, delta hedging, replication, product rule, Itô formula, European call,
MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralLocalised ItoFormulaAdapted AdaptedDrift
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The delta `Φ(d₁(S_s, T − s))` of the call along the Black–Scholes path. -/
noncomputable def hedgeDelta (K r σ S_0 T : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Phi (bsd1 (pathAssets S_0 r σ B () s ω) K r σ (T - s))

/-- The call value `C(s, S_s) = bsV K r σ S_s (T − s)` along the Black–Scholes path. -/
noncomputable def hedgeValue (K r σ S_0 T : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  bsV K r σ (pathAssets S_0 r σ B () s ω) (T - s)

/-- The bank position `ψ_s = C(s, S_s) − Δ_s S_s` of the delta hedge. -/
noncomputable def hedgeBank (K r σ S_0 T : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  hedgeValue K r σ S_0 T B s ω - hedgeDelta K r σ S_0 T B s ω * pathAssets S_0 r σ B () s ω

private theorem aux_mul {e e' σ S Φ : ℝ} (h : e * e' = 1) :
    Φ * (σ * S) = e * (σ * (e' * S) * Φ) := by
  linear_combination (-(σ * S * Φ)) * h

/-- The delta times the diffusion `σ S` of the stock is `e^{rs}` times the discounted hedge
integrand. -/
private theorem delta_mul_diffusion (K r σ S_0 T : ℝ) (s x : ℝ) :
    Phi (bsd1 (gbmValue S_0 r σ s x) K r σ (T - s)) * (σ * gbmValue S_0 r σ s x)
      = Real.exp (r * s) * deltaHedgeIntegrand K r σ S_0 T s x := by
  unfold deltaHedgeIntegrand
  exact aux_mul (by rw [← Real.exp_add]; simp)

/-- The delta times the stock is `e^{rs}` times the discounted hedge integrand over `σ`. -/
private theorem delta_mul_stock (K r σ S_0 T : ℝ) (hσ : σ ≠ 0) (s x : ℝ) :
    Phi (bsd1 (gbmValue S_0 r σ s x) K r σ (T - s)) * gbmValue S_0 r σ s x
      = Real.exp (r * s) * deltaHedgeIntegrand K r σ S_0 T s x / σ := by
  rw [eq_div_iff hσ]
  have h := delta_mul_diffusion K r σ S_0 T s x
  linear_combination h

/-- The undiscounted hedge gain integrand `Δ σ S` is predictable. -/
theorem hedgeGain_isStronglyPredictable {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (K r σ S_0 T : ℝ) :
    IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) ω ↦
      hedgeDelta K r σ S_0 T B s ω * (σ * pathAssets S_0 r σ B () s ω) := by
  refine isStronglyPredictable_comp_path hBmeas hBcont
    (h := fun s x ↦ Phi (bsd1 (gbmValue S_0 r σ s x) K r σ (T - s)) * (σ * gbmValue S_0 r σ s x))
    ?_
  have hPhi : Measurable Phi := continuous_Phi.measurable
  unfold bsd1 gbmValue
  fun_prop

/-- **The Black–Scholes delta hedge is self-financing.** Let `B` be a Brownian motion with
continuous paths, `T' < T`, and `K, σ, S₀ > 0`. With the call value `V_t = C(t, S_t)`
(`hedgeValue`), the delta `Δ_t = Φ(d₁)` (`hedgeDelta`) and the bank position
`ψ_t = V_t − Δ_t S_t` (`hedgeBank`), almost surely, for all `t ≤ T'` at once,

  `V_t = V₀ + (∫₀ᵗ Δ_s · r S_s ds + ∫₀ᵗ Δ_s · σ S_s dB_s) + ∫₀ᵗ r ψ_s ds`,

where `V₀` is the value of `europeanCall K T`, and the Brownian integral is `predItoIntegral` of
the predictable integrand `Δ σ S`. The bracket is the gain `∫ Δ dS` of `dS = r S dt + σ S dB`.
Stated on `[0, T']` for `T' < T`. -/
theorem europeanCall_selfFinancing {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {T : ℝ≥0} (hT : 0 < (T : ℝ))
    {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (T' : ℝ≥0) (hT' : T' < T) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T',
      hedgeValue K r σ S_0 T B t ω
        = (europeanCall K T).value μ (fun u ↦ Real.exp (-r * u)) (pathAssets S_0 r σ B)
          + ((∫ s in Ioc 0 t, hedgeDelta K r σ S_0 T B s ω * (r * pathAssets S_0 r σ B () s ω)
                ∂timeMeasure)
              + predItoIntegral (μ := μ) T' hBmeas
                (hedgeGain_isStronglyPredictable hBmeas hBcont K r σ S_0 T) t ω)
          + ∫ s in Ioc 0 t, r * hedgeBank K r σ S_0 T B s ω ∂timeMeasure := by
  have hT'' : (T' : ℝ) < T := NNReal.coe_lt_coe.2 hT'
  obtain ⟨ψ, hψc, hψT, hψid⟩ : ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t, ψ t < T) ∧
      ∀ t ≤ (T' : ℝ), ψ t = t :=
    ⟨timeCap (T' : ℝ) T, (contDiff_timeCap 1).continuous, timeCap_lt hT'',
      fun t ht ↦ timeCap_of_le hT'' ht⟩
  obtain ⟨H', hH'⟩ : ∃ H' : ℝ≥0 → Ω → ℝ, ∀ s ω,
      H' s ω = deltaHedgeIntegrand K r σ S_0 T (ψ s) (B s ω) := ⟨_, fun _ _ ↦ rfl⟩
  have hcomp : Continuous fun p : ℝ × ℝ ↦ deltaHedgeIntegrand K r σ S_0 T (ψ p.1) p.2 :=
    continuous_deltaHedgeIntegrand_comp hK hσ hS₀ hψc hψT
  have hHa : ∀ t : ℝ≥0, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (H' t) := by
    intro t
    have hg : Continuous fun x : ℝ ↦ deltaHedgeIntegrand K r σ S_0 T (ψ t) x :=
      hcomp.comp (Continuous.prodMk continuous_const continuous_id)
    have : H' t = fun ω ↦ deltaHedgeIntegrand K r σ S_0 T (ψ t) (B t ω) := funext (hH' t)
    rw [this]
    exact hg.comp_stronglyMeasurable (stronglyAdapted_natFiltration hBmeas t)
  have hHc : ∀ ω, Continuous fun s : ℝ≥0 ↦ H' s ω := by
    intro ω
    have : (fun s : ℝ≥0 ↦ H' s ω) = fun s ↦ deltaHedgeIntegrand K r σ S_0 T (ψ s) (B s ω) :=
      funext fun s ↦ hH' s ω
    rw [this]
    exact hcomp.comp (NNReal.continuous_coe.prodMk (hBcont ω))
  have hpredH' := isStronglyPredictable_of_bdd_adapted_cont hBmeas hHa hHc
  have hHeq (ω : Ω) (s : ℝ≥0) (hs : s ∈ Icc (0 : ℝ≥0) T') :
      deltaHedgeIntegrand K r σ S_0 T s (B s ω) = H' s ω := by
    rw [hH' s ω, hψid s (NNReal.coe_le_coe.2 hs.2)]
  have hexp (s : ℝ≥0) : Real.exp (r * s) * Real.exp (-(r * s)) = 1 := by
    rw [← Real.exp_add]; simp
  have hecont : Continuous fun s : ℝ≥0 ↦ Real.exp (r * s) := by fun_prop
  -- the discounted value as an Itô process
  obtain ⟨X', hX'⟩ : ∃ X' : ℝ≥0 → Ω → ℝ, X' = localItoProcess (μ := μ) T' hBmeas hHa hHc
      (bsV K r σ S_0 T) (fun _ _ ↦ (0 : ℝ)) := ⟨_, rfl⟩
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X' t ω) (Icc 0 T') := by
    subst hX'
    exact ae_continuousOn_localItoProcess hB T' hBmeas hBcont hHa hHc (b := fun _ _ ↦ (0 : ℝ))
      (fun _ ↦ continuous_const) _
  have hrep := bs_delta_hedge_replication hB hBmeas hBcont hK hσ hS₀ T' hT''
  have hcongr := ae_predItoIntegral_congr hB T' hBmeas hBcont
    (deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S_0 T)
    (ae_of_all _ fun ω ↦ (hHc ω).continuousOn.congr fun s hs ↦ hHeq ω s hs) hpredH'
    (ae_of_all _ fun ω ↦ (hHc ω).continuousOn) (ae_of_all _ fun ω s hs ↦ hHeq ω s hs)
  have hLI := ae_predItoIntegral_eq_localItoIntegral hB T' hBmeas hBcont hHa hHc
  have hXeq : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T',
      X' t ω = Real.exp (-(r * t)) * hedgeValue K r σ S_0 T B t ω := by
    subst hX'
    filter_upwards [hrep, hcongr, hLI] with ω h1 h2 h3 t ht
    have h1' : Real.exp (-(r * t)) * hedgeValue K r σ S_0 T B t ω = bsV K r σ S_0 T
        + predItoIntegral (μ := μ) T' hBmeas
          (deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S_0 T) t ω := h1 t ht
    have hd : driftPath (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) t ω = 0 := by simp [driftPath]
    unfold localItoProcess
    rw [hd, ← h3 t ht, h1', h2 t ht]
    ring
  -- Itô's formula for `f(t, x) = e^{rt} x` along the discounted value
  have hpt : IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦
      Real.exp (r * s) :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun _ ↦ stronglyMeasurable_const)
      fun _ _ ↦ hecont.continuousWithinAt
  have hpE : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ Real.exp (r * s) * H' s ω :=
    hpt.mul hpredH'
  have hct : Continuous fun p : ℝ × ℝ ↦ r * Real.exp (r * p.1) * p.2 := by fun_prop
  have hcx : Continuous fun p : ℝ × ℝ ↦ Real.exp (r * p.1) := by fun_prop
  have hf_t (t x : ℝ) : HasDerivAt (fun s ↦ Real.exp (r * s) * x) (r * Real.exp (r * t) * x) t := by
    convert (((hasDerivAt_id' t).const_mul r).exp).mul_const x using 1
    ring
  have hf_x (t x : ℝ) : HasDerivAt (fun u ↦ Real.exp (r * t) * u) (Real.exp (r * t)) x := by
    convert (hasDerivAt_id' x).const_mul (Real.exp (r * t)) using 1
    ring
  have hf_xx (t x : ℝ) : HasDerivAt (fun _ : ℝ ↦ Real.exp (r * t)) 0 x := hasDerivAt_const x _
  have hIto : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T',
      Real.exp (r * t) * X' t ω = Real.exp (r * 0) * bsV K r σ S_0 T
        + ∫ s in Ioc 0 t, (r * Real.exp (r * s) * X' s ω + Real.exp (r * s) * 0
            + 1 / 2 * (0 * H' s ω ^ 2)) ∂timeMeasure
        + predItoIntegral (μ := μ) T' hBmeas hpE t ω := by
    subst hX'
    have h := ito_formula_adapted_unbounded_process hB T' hBmeas hBcont hHa hHc
      (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
      (bsV K r σ S_0 T) (f := fun t x ↦ Real.exp (r * t) * x)
      (f_t := fun t x ↦ r * Real.exp (r * t) * x) (f_x := fun t _ ↦ Real.exp (r * t))
      (f_xx := fun _ _ ↦ 0) hf_t hf_x hf_xx hct hcx continuous_const
    filter_upwards [h] with ω hω t ht
    exact hω t ht
  -- the integrand of the stochastic term is the hedge gain
  have hGE (ω : Ω) (s : ℝ≥0) (hs : s ∈ Icc (0 : ℝ≥0) T') :
      hedgeDelta K r σ S_0 T B s ω * (σ * pathAssets S_0 r σ B () s ω)
        = Real.exp (r * s) * H' s ω := by
    rw [← hHeq ω s hs]
    exact delta_mul_diffusion K r σ S_0 T s (B s ω)
  have hPG := ae_predItoIntegral_congr hB T' hBmeas hBcont hpE
    (ae_of_all _ fun ω ↦ (hecont.mul (hHc ω)).continuousOn)
    (hedgeGain_isStronglyPredictable hBmeas hBcont K r σ S_0 T)
    (ae_of_all _ fun ω ↦ (hecont.mul (hHc ω)).continuousOn.congr fun s hs ↦ hGE ω s hs)
    (ae_of_all _ fun ω s hs ↦ (hGE ω s hs).symm)
  have hDS (ω : Ω) (s : ℝ≥0) (hs : s ∈ Icc (0 : ℝ≥0) T') :
      hedgeDelta K r σ S_0 T B s ω * pathAssets S_0 r σ B () s ω
        = Real.exp (r * s) * H' s ω / σ := by
    rw [← hHeq ω s hs]
    exact delta_mul_stock K r σ S_0 T hσ.ne' s (B s ω)
  rw [value_europeanCall_pathAssets hB hT hS₀ hK hσ]
  filter_upwards [hXc, hXeq, hIto, hPG] with ω hc hX hI hP t ht
  have hsub : Icc (0 : ℝ≥0) t ⊆ Icc 0 T' := Icc_subset_Icc_right ht.2
  have cDS : ContinuousOn (fun s : ℝ≥0 ↦ hedgeDelta K r σ S_0 T B s ω
      * pathAssets S_0 r σ B () s ω) (Icc 0 T') :=
    ((hecont.mul (hHc ω)).div_const σ).continuousOn.congr fun s hs ↦ hDS ω s hs
  have cV : ContinuousOn (fun s : ℝ≥0 ↦ hedgeValue K r σ S_0 T B s ω) (Icc 0 T') :=
    (hecont.continuousOn.mul hc).congr fun s hs ↦ by
      show hedgeValue K r σ S_0 T B s ω = Real.exp (r * s) * X' s ω
      rw [hX s hs]
      linear_combination (-(hedgeValue K r σ S_0 T B s ω)) * hexp s
  have cr : ContinuousOn (fun _ : ℝ≥0 ↦ r) (Icc 0 T') := continuousOn_const
  have hi1 : IntegrableOn (fun s : ℝ≥0 ↦ hedgeDelta K r σ S_0 T B s ω
      * (r * pathAssets S_0 r σ B () s ω)) (Ioc 0 t) timeMeasure :=
    integrableOn_Ioc_of_continuousOn
      (((cr.mul cDS).congr fun s _ ↦ mul_left_comm _ _ _).mono hsub)
  have hi2 : IntegrableOn (fun s : ℝ≥0 ↦ r * hedgeBank K r σ S_0 T B s ω) (Ioc 0 t)
      timeMeasure :=
    integrableOn_Ioc_of_continuousOn
      (((cr.mul (cV.sub cDS)).congr fun s _ ↦ rfl).mono hsub)
  have hsplit : ∫ s in Ioc 0 t, (hedgeDelta K r σ S_0 T B s ω * (r * pathAssets S_0 r σ B () s ω)
        + r * hedgeBank K r σ S_0 T B s ω) ∂timeMeasure
      = ∫ s in Ioc 0 t, r * hedgeValue K r σ S_0 T B s ω ∂timeMeasure :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ by simp only [hedgeBank]; ring
  rw [integral_add hi1 hi2] at hsplit
  have hdrift : ∫ s in Ioc 0 t, (r * Real.exp (r * s) * X' s ω + Real.exp (r * s) * 0
        + 1 / 2 * (0 * H' s ω ^ 2)) ∂timeMeasure
      = ∫ s in Ioc 0 t, r * hedgeValue K r σ S_0 T B s ω ∂timeMeasure :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
      simp only [hX s ⟨zero_le, hs.2.trans ht.2⟩]
      linear_combination (r * hedgeValue K r σ S_0 T B s ω) * hexp s
  have e1 := hI t ht
  rw [hX t ht, hdrift, hP t ht] at e1
  simp only [mul_zero, Real.exp_zero, one_mul] at e1
  have e2 : Real.exp (r * t) * (Real.exp (-(r * t)) * hedgeValue K r σ S_0 T B t ω)
      = hedgeValue K r σ S_0 T B t ω := by
    linear_combination (hedgeValue K r σ S_0 T B t ω) * hexp t
  linarith [e1, e2, hsplit]

end MathFin.Contracts.BlackScholes
