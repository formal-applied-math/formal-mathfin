/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PlaneIto
public import MathFin.BlackScholes.AmericanPut.Boundary.DividendProblem

/-!
# Zero-drift smooth Ito localizations of the classical price

Every continuation point admits a compact C3 localization whose Brownian
generator is zero nearby and whose compensated Brownian evaluation is a
genuine local martingale. Compact-region assembly and transfer to the raw
filtration are proved subsequently in `InteriorIto` and `ContactMartingale`.

## Result

Public entry points include `brownianPriceKernel_localization_zero_drift`, `local_price_ito`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped Topology NNReal

theorem brownianPriceKernel_localization_zero_drift {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    {K r q σ x₀ T t w : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hσ : 0 < σ) (ht : t < T)
    (hx : b (σ ^ 2 / 2 * (T - t)) < x₀ + (r - q - σ ^ 2 / 2) * t + σ * w) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝 (t,w)] (fun z => brownianPriceKernel p K r q σ x₀ T z.1 z.2) ∧
      ∀ᶠ z in 𝓝 (t,w), planeGenerator G z = 0 := by
  obtain ⟨G,hG,hcompact,heq⟩ := brownianPriceKernel_localization (K := K) hp hσ ht hx
  refine ⟨G,hG,hcompact,heq,?_⟩
  have htime : 0 < σ^2/2*(T-t) := mul_pos (by positivity) (sub_pos.mpr ht)
  have hb : ContinuousAt (fun z : ℝ × ℝ => b (σ^2/2*(T-z.1))) (t,w) :=
    Tendsto.comp (g := b) (f := fun z : ℝ × ℝ => σ^2/2*(T-z.1))
      (hp.boundary_continuous.continuousAt (Ici_mem_nhds htime))
      (show ContinuousAt (fun z : ℝ × ℝ => σ^2/2*(T-z.1)) (t,w) by fun_prop)
  have hleft : ∀ᶠ z : ℝ × ℝ in 𝓝 (t,w), z.1 < T :=
    continuousAt_fst.eventually_lt continuousAt_const ht
  have hright : ∀ᶠ z : ℝ × ℝ in 𝓝 (t,w),
      b (σ^2/2*(T-z.1)) < x₀+(r-q-σ^2/2)*z.1+σ*z.2 :=
    hb.eventually_lt (by fun_prop) hx
  filter_upwards [heq.eventuallyEq_nhds,hleft,hright] with z hz hzt hzx
  have htEq : (fun s => G (s,z.2)) =ᶠ[𝓝 z.1]
      (fun s => brownianPriceKernel p K r q σ x₀ T s z.2) :=
    hz.comp_tendsto (show Tendsto (fun s : ℝ => (s,z.2)) (𝓝 z.1) (𝓝 z) by
      convert! (continuous_id.prodMk continuous_const).tendsto z.1 using 1)
  have hxEq : (fun y => G (z.1,y)) =ᶠ[𝓝 z.2]
      (fun y => brownianPriceKernel p K r q σ x₀ T z.1 y) :=
    hz.comp_tendsto (show Tendsto (fun y : ℝ => (z.1,y)) (𝓝 z.2) (𝓝 z) by
      convert! (continuous_const.prodMk continuous_id).tendsto z.2 using 1)
  rw [show z = (z.1,z.2) from rfl,planeGenerator_eq_partials hG,htEq.deriv_eq,hxEq.deriv.deriv_eq]
  exact brownianPriceKernel_heat_equation hp hσ hzt hzx

theorem local_price_ito {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ℝ}
    (hW : IsPreBrownianReal W P) (hmeas : ∀ s, Measurable (W s))
    (hpaths : ∀ ω, Continuous (fun s => W s ω))
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {K r q σ x₀ T t w : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hσ : 0 < σ) (ht : t < T)
    (hx : b (σ ^ 2 / 2 * (T - t)) < x₀ + (r - q - σ ^ 2 / 2) * t + σ * w) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝 (t,w)] (fun z => brownianPriceKernel p K r q σ x₀ T z.1 z.2) ∧
      (∀ᶠ z in 𝓝 (t,w), planeGenerator G z = 0) ∧
      ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (fun s => M s ω)) ∧
        IsLocalMartingale M
            (MathFin.ItoIntegralProcessLocalMartingaleGeneral.augFiltration (μ := P) hmeas) P ∧
        ∀ s : ℝ≥0, (fun ω => G (s,W s ω)-G (0,W 0 ω)) =ᵐ[P]
          (fun ω => M s ω + ∫ u in Set.Ioc 0 s,
            planeGenerator G (u,W u ω) ∂MathFin.ItoIntegralL2.timeMeasure) := by
  obtain ⟨G,hG,hcompact,heq,hzero⟩ :=
      brownianPriceKernel_localization_zero_drift (K := K) hp hσ ht hx
  exact ⟨G,hG,hcompact,heq,hzero,
    plane_ito_localMartingale hW hmeas hpaths (hG.of_le (by norm_num))⟩

end MathFin.BlackScholes.AmericanPut.Stopping
