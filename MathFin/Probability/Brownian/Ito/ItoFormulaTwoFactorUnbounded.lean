/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaTwoFactorLocal

/-! # Itô's formula for `f(t, X_t, Y_t)` with unbounded coefficients, as an identity of processes

Let `B` be a Brownian motion with continuous paths, and `σ`, `τ`, `b`, `c` adapted to its natural
filtration with every path continuous, not bounded. With `M^σ = ∫ σ dB`, `M^τ = ∫ τ dB`
(`localItoIntegral`), `X = x₀ + ∫ b ds + M^σ` and `Y = y₀ + ∫ c ds + M^τ` (`localItoProcess`, both
driven by the *same* `B`), and `f(t, x, y)` with jointly continuous partials `f_t`, `f_x`, `f_y`,
`f_xx`, `f_xy = ∂_y f_x`, `f_yy`, almost surely, at every `t ∈ [0, T]` at once,

`f(t, X_t, Y_t) = f(0, x₀, y₀) + ∫₀ᵗ ito2Drift (s, X_s, Y_s) ds + (∫ (f_x σ + f_y τ)(·, X, Y) dB)_t`

(`ito_formula_adapted_two_factor_process`), where `ito2Drift` is
`f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²` and the stochastic integral is
`predItoIntegral` of the predictable integrand `f_x(s, X_s, Y_s) σ_s + f_y(s, X_s, Y_s) τ_s`. The
cross term `f_xy σ τ` is the quadratic covariation `d⟨X, Y⟩ = σ τ dt` of the two martingale
parts, derived and not assumed. This is the statement of `ito_formula_adapted_unbounded_process`
for two processes, with every hypothesis of that theorem carried over: nothing is assumed bounded,
neither `f` and its partials, nor `σ`, `τ`, `b`, `c`.

The proof is the proof of the one-factor theorem. On the event that the four coefficients stay in
`[−N, N]` up to `T` they equal their clippings, the processes are almost surely the Itô processes
of the clipped coefficients (`ae_localItoProcess_eq`), and the formula with bounded coefficients
and unbounded partials of `f` (`ito_formula_adapted_two_factor_local_le`) gives the convergence in
probability of the Riemann–Stieltjes sums at each `t ≤ T`
(`ito_formula_adapted_two_factor_unbounded_le`). The sums converge also to the two integrals
`predItoIntegral` (`tendstoInMeasure_riemannStieltjes_localItoIntegral`), which gives the identity
at each time; both sides have continuous paths, so it holds at all times at once.

The one-factor theorem `ito_formula_adapted_unbounded_process` has the same hypotheses on `σ`,
`b` and `f`; it is not restated here as a corollary, since the duplicate statement would be the
parallel copy the library avoids.

Not here: a random starting point, `T = ∞`, a vector Brownian driver (neither this library nor
BrownianMotion at the pinned version defines a multi-dimensional Brownian motion: two *independent*
Brownian motions are not covered, so `d⟨X, Y⟩ = 0` for processes driven by independent motions is
not a corollary), and the local-martingale statement of `exists_localMartingale_ito_formula`
for two factors.

## Main results

* `ito_formula_adapted_two_factor_process`: for `X`, `Y` as above and `f` with jointly continuous
  partials, almost surely, for all `t ∈ [0, T]`,
  `f(t, X_t, Y_t) = f(0, x₀, y₀) + ∫₀ᵗ ito2Drift ds + (∫ (f_x σ + f_y τ)(·, X, Y) dB)_t`.
* `ito_formula_adapted_two_factor_unbounded_le`: for `t ≤ T` the Riemann–Stieltjes sums of
  `f_x(·, X, Y)` against `M^σ` plus those of `f_y(·, X, Y)` against `M^τ` converge in measure to
  `f(t, X_t, Y_t) − f(0, x₀, y₀) − ∫₀ᵗ ito2Drift ds`.
* `continuous_uncurry_three_of_continuous_partials`: a function with jointly continuous partials
  `g_t`, `g_x`, `g_y` is jointly continuous.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 7.5.2 (shared-driver case).
* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.3.6
* [Revuz and Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], Theorem IV.3.3

## Tags

Itô formula, Itô lemma, two-dimensional Itô formula, quadratic covariation, unbounded
coefficients, clipping, localisation, identity of processes, MSC 60H05, MSC 60H10
-/

@[expose] public section

namespace MathFin

/-- **A function with jointly continuous partials is jointly continuous**, in three variables:
`g(t, x, y) = g(0, 0, 0) + ∫₀ᵗ g_t(s, 0, 0) ds + ∫₀ˣ g_x(t, u, 0) du + ∫₀ʸ g_y(t, x, v) dv`, and
parametric integrals of a continuous integrand are continuous. -/
theorem continuous_uncurry_three_of_continuous_partials {g g_t g_x g_y : ℝ → ℝ → ℝ → ℝ}
    (hg_t : ∀ t x y, HasDerivAt (fun s ↦ g s x y) (g_t t x y) t)
    (hg_x : ∀ t x y, HasDerivAt (fun u ↦ g t u y) (g_x t x y) x)
    (hg_y : ∀ t x y, HasDerivAt (fun v ↦ g t x v) (g_y t x y) y)
    (hg_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ g_t p.1 p.2.1 p.2.2)
    (hg_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ g_x p.1 p.2.1 p.2.2)
    (hg_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ g_y p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2 := by
  have h (t x y : ℝ) : g t x y = g 0 0 0 + (∫ s in (0 : ℝ)..t, g_t s 0 0)
      + (∫ u in (0 : ℝ)..x, g_x t u 0) + ∫ v in (0 : ℝ)..y, g_y t x v := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hg_t s 0 0)
        ((hg_t_cont.comp (continuous_id.prodMk
          (continuous_const.prodMk continuous_const))).intervalIntegrable 0 t),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hg_x t u 0)
        ((hg_x_cont.comp (continuous_const.prodMk
          (continuous_id.prodMk continuous_const))).intervalIntegrable 0 x),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ ↦ hg_y t x v)
        ((hg_y_cont.comp (continuous_const.prodMk
          (continuous_const.prodMk continuous_id))).intervalIntegrable 0 y)]
    ring
  rw [show (fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) = fun p ↦ g 0 0 0
      + (∫ s in (0 : ℝ)..p.1, g_t s 0 0) + (∫ u in (0 : ℝ)..p.2.1, g_x p.1 u 0)
      + ∫ v in (0 : ℝ)..p.2.2, g_y p.1 p.2.1 v from funext fun p ↦ h p.1 p.2.1 p.2.2]
  exact ((continuous_const.add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ × ℝ × ℝ) s ↦ g_t s 0 0)
      (hg_t_cont.comp (continuous_snd.prodMk (continuous_const.prodMk continuous_const)))
      continuous_fst)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ × ℝ) u ↦ g_x p.1 u 0)
      (hg_x_cont.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_const)))
      continuous_snd.fst)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ × ℝ) v ↦ g_y p.1 p.2.1 v)
      (hg_y_cont.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk continuous_snd)))
      continuous_snd.snd)

namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift ItoIntegralLocalised LocalisationInMeasure
open scoped NNReal ENNReal

/-- **The drift of `f(t, X_t, Y_t)` is continuous** along paths continuous on `[0, T]`, for
coefficients continuous on `[0, T]` and jointly continuous partials. -/
theorem continuousOn_ito2Drift {T : ℝ≥0} {x y b c σ τ : ℝ≥0 → ℝ}
    {f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
    (hf_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2)
    (hf_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2)
    (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2)
    (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hb : ContinuousOn b (Icc 0 T)) (hc : ContinuousOn c (Icc 0 T))
    (hσ : ContinuousOn σ (Icc 0 T)) (hτ : ContinuousOn τ (Icc 0 T)) :
    ContinuousOn (fun s : ℝ≥0 ↦
      ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s) (c s) (σ s) (τ s) s (x s) (y s)) (Icc 0 T) := by
  unfold ito2Drift
  exact (((((continuousOn_comp_time_pair hf_t_cont hx hy).add
    ((continuousOn_comp_time_pair hf_x_cont hx hy).mul hb)).add
    ((continuousOn_comp_time_pair hf_y_cont hx hy).mul hc)).add
    (continuousOn_const.mul ((continuousOn_comp_time_pair hf_xx_cont hx hy).mul
      (hσ.pow 2)))).add
    ((continuousOn_comp_time_pair hf_xy_cont hx hy).mul (hσ.mul hτ))).add
    (continuousOn_const.mul ((continuousOn_comp_time_pair hf_yy_cont hx hy).mul (hτ.pow 2)))

/-- **The Itô integral is the same for integrands that are equal as functions**: `predItoIntegral`
does not depend on the proof of predictability, only on the integrand. -/
theorem predItoIntegral_congr {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {θ θ' : ℝ≥0 → Ω → ℝ} (h : θ = θ')
    (hp : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hp' : IsStronglyPredictable (natFiltration hBmeas) θ') (t : ℝ≥0) (ω : Ω) :
    predItoIntegral (μ := μ) T hBmeas hp t ω = predItoIntegral (μ := μ) T hBmeas hp' t ω := by
  subst h
  rfl

section Unbounded

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ τ : ℝ≥0 → Ω → ℝ}
  (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
  (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
  (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω)
  {b c : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω)
  (hc_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (c t))
  (hc_cont : ∀ ω, Continuous fun s ↦ c s ω) (x₀ y₀ : ℝ)

include hB hBcont hσa hσc hτa hτc hb_adap hb_cont hc_adap hc_cont in
/-- **A jointly continuous function of the time and of two Itô processes with unbounded
coefficients is predictable.** -/
theorem comp_time_localItoProcess_pair_isStronglyPredictable {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) :
    IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦
      g s (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω)
        (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω) :=
  hg.comp_stronglyMeasurable (StronglyMeasurable.prodMk (isStronglyPredictable_time hBmeas)
    (StronglyMeasurable.prodMk
      (isStronglyPredictable_localItoProcess hB T hBmeas hBcont hσa hσc hb_adap hb_cont x₀)
      (isStronglyPredictable_localItoProcess hB T hBmeas hBcont hτa hτc hc_adap hc_cont y₀)))

variable {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
  (hf_t : ∀ t x y, HasDerivAt (fun s ↦ f s x y) (f_t t x y) t)
  (hf_x : ∀ t x y, HasDerivAt (fun u ↦ f t u y) (f_x t x y) x)
  (hf_y : ∀ t x y, HasDerivAt (fun v ↦ f t x v) (f_y t x y) y)
  (hf_xx : ∀ t x y, HasDerivAt (fun u ↦ f_x t u y) (f_xx t x y) x)
  (hf_xy : ∀ t x y, HasDerivAt (fun v ↦ f_x t x v) (f_xy t x y) y)
  (hf_yy : ∀ t x y, HasDerivAt (fun v ↦ f_y t x v) (f_yy t x y) y)
  (hf_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2)
  (hf_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2)
  (hf_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2)
  (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2)
  (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2)
  (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2)

include hB hBcont hσa hσc hτa hτc hb_adap hb_cont hc_adap hc_cont hf_x_cont hf_y_cont in
/-- **The integrand `f_x(s, X_s, Y_s) σ_s + f_y(s, X_s, Y_s) τ_s` of the two-factor Itô formula is
predictable.** -/
theorem itoIntegrand2_isStronglyPredictable :
    IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦
      f_x s (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω)
          (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω) * σ s ω
        + f_y s (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω)
          (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω) * τ s ω :=
  ((comp_time_localItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc
    hb_adap hb_cont hc_adap hc_cont x₀ y₀ hf_x_cont).mul
      (isStronglyPredictable_of_bdd_adapted_cont hBmeas hσa hσc)).add
    ((comp_time_localItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc
      hb_adap hb_cont hc_adap hc_cont x₀ y₀ hf_y_cont).mul
      (isStronglyPredictable_of_bdd_adapted_cont hBmeas hτa hτc))

include hB hBcont hb_adap hb_cont hc_adap hc_cont hf_t hf_x hf_y hf_xx hf_xy hf_yy hf_t_cont
  hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont in
/-- **Itô's formula for `f(t, X_t, Y_t)` along two Itô processes with unbounded coefficients, in
probability.** Let `B` be a Brownian motion with every path continuous, `σ`, `τ`, `b`, `c` adapted
to its natural filtration with every path continuous, `M^σ = ∫ σ dB`, `M^τ = ∫ τ dB`
(`localItoIntegral`), `X = x₀ + ∫ b ds + M^σ`, `Y = y₀ + ∫ c ds + M^τ` (`localItoProcess`), and
`f(t, x, y)` with jointly continuous partials `f_t`, `f_x`, `f_y`, `f_xx`, `f_xy = ∂_y f_x`,
`f_yy`. For `t ≤ T` the left-point Riemann–Stieltjes sums
`∑ f_x(sₖ, Xₖ, Yₖ) ΔM^σ_k + ∑ f_y(sₖ, Xₖ, Yₖ) ΔM^τ_k` on the uniform partitions of `[0, t]`
converge in probability to

`f(t, X_t, Y_t) − f(0, x₀, y₀) − ∫₀ᵗ (f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²)
  (s, X_s, Y_s) ds`

(`ito2Drift`). No bound on `σ`, `τ`, `b`, `c`, `f` or the partials of `f` is assumed. -/
theorem ito_formula_adapted_two_factor_unbounded_le {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦
        ∑ k ∈ Finset.range n,
          f_x (unifPart t n k)
            (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b (unifPart t n k) ω)
            (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c (unifPart t n k) ω)
          * (localItoIntegral (μ := μ) T hBmeas hσa hσc (unifPart t n (k + 1)) ω
            - localItoIntegral (μ := μ) T hBmeas hσa hσc (unifPart t n k) ω)
        + ∑ k ∈ Finset.range n,
          f_y (unifPart t n k)
            (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b (unifPart t n k) ω)
            (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c (unifPart t n k) ω)
          * (localItoIntegral (μ := μ) T hBmeas hτa hτc (unifPart t n (k + 1)) ω
            - localItoIntegral (μ := μ) T hBmeas hτa hτc (unifPart t n k) ω)) atTop
      fun ω ↦
        f t (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b t ω)
          (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c t ω) - f 0 x₀ y₀
        - ∫ s in Ioc 0 t, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
            (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω)
            (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω) ∂timeMeasure := by
  have hAσ := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hσa hσc
  have hAτ := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hτa hτc
  have hAb := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hb_adap hb_cont
  have hAc := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hc_adap hc_cont
  refine tendstoInMeasure_of_ae_eqOn
    (A := fun N : ℕ ↦ (({ω | ∀ s ∈ Icc 0 T, |σ s ω| ≤ N} ∩ {ω | ∀ s ∈ Icc 0 T, |τ s ω| ≤ N})
      ∩ {ω | ∀ s ∈ Icc 0 T, |b s ω| ≤ N}) ∩ {ω | ∀ s ∈ Icc 0 T, |c s ω| ≤ N})
    (tendsto_measure_compl_inter (tendsto_measure_compl_inter
      (tendsto_measure_compl_inter hAσ hAτ) hAb) hAc)
    (fun N ↦ ito_formula_adapted_two_factor_local_le hB T hBmeas hBcont (clip_adapted hσa N)
      (clip_continuous hσc N) (abs_clip_le N σ) (clip_adapted hτa N) (clip_continuous hτc N)
      (abs_clip_le N τ) (clip_adapted hb_adap N) (clip_continuous hb_cont N) (abs_clip_le N b)
      (clip_adapted hc_adap N) (clip_continuous hc_cont N) (abs_clip_le N c) x₀ y₀ hf_t hf_x hf_y
      hf_xx hf_xy hf_yy hf_t_cont hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont ht)
    (fun N n ↦ ?_) fun N ↦ ?_
  · filter_upwards [ae_localItoProcess_eq hB T hBmeas hBcont hσa hσc x₀ (b := b),
      ae_localItoProcess_eq hB T hBmeas hBcont hτa hτc y₀ (b := c),
      ae_localItoIntegral_eq hB T hBmeas hBcont hσa hσc,
      ae_localItoIntegral_eq hB T hBmeas hBcont hτa hτc] with ω hX hY hMσ hMτ hω
    have hσ := hω.1.1.1
    have hτ := hω.1.1.2
    have hbb := hω.1.2
    have hcc := hω.2
    congr 1
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.1 hk
      have h1 : unifPart t n k ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk'.le).trans ht⟩
      have h2 : unifPart t n (k + 1) ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk').trans ht⟩
      rw [hX N hσ hbb _ h1, hY N hτ hcc _ h1,
        hMσ N _ h1 fun r hr ↦ hσ r ⟨hr.1, hr.2.trans h1.2⟩,
        hMσ N _ h2 fun r hr ↦ hσ r ⟨hr.1, hr.2.trans h2.2⟩]
      rfl
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.1 hk
      have h1 : unifPart t n k ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk'.le).trans ht⟩
      have h2 : unifPart t n (k + 1) ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk').trans ht⟩
      rw [hX N hσ hbb _ h1, hY N hτ hcc _ h1,
        hMτ N _ h1 fun r hr ↦ hτ r ⟨hr.1, hr.2.trans h1.2⟩,
        hMτ N _ h2 fun r hr ↦ hτ r ⟨hr.1, hr.2.trans h2.2⟩]
      rfl
  · filter_upwards [ae_localItoProcess_eq hB T hBmeas hBcont hσa hσc x₀ (b := b),
      ae_localItoProcess_eq hB T hBmeas hBcont hτa hτc y₀ (b := c)] with ω hX hY hω
    have hσ := hω.1.1.1
    have hτ := hω.1.1.2
    have hbb := hω.1.2
    have hcc := hω.2
    rw [hX N hσ hbb t ⟨zero_le, ht⟩, hY N hτ hcc t ⟨zero_le, ht⟩]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have hs' : s ∈ Icc 0 T := ⟨zero_le, hs.2.trans ht⟩
    simp only [hX N hσ hbb s hs', hY N hτ hcc s hs', clip_eq_self (hσ s hs'),
      clip_eq_self (hτ s hs'), clip_eq_self (hbb s hs'), clip_eq_self (hcc s hs')]

include hB hBcont hb_adap hb_cont hc_adap hc_cont hf_t hf_x hf_y hf_xx hf_xy hf_yy hf_t_cont
  hf_xx_cont hf_xy_cont hf_yy_cont hf_x_cont hf_y_cont in
/-- **Itô's formula for `f(t, X_t, Y_t)` as an identity of processes.** Let `B` be a Brownian
motion with every path continuous, `σ`, `τ`, `b`, `c` adapted to its natural filtration with every
path continuous, `X = x₀ + ∫ b ds + ∫ σ dB` and `Y = y₀ + ∫ c ds + ∫ τ dB` (`localItoProcess`, one
Brownian motion), and `f(t, x, y)` with jointly continuous partials `f_t`, `f_x`, `f_y`, `f_xx`,
`f_xy = ∂_y f_x`, `f_yy`. Almost surely, for every `t ∈ [0, T]` at once,

`f(t, X_t, Y_t) = f(0, x₀, y₀)
  + ∫₀ᵗ (f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²)(s, X_s, Y_s) ds
  + (∫ (f_x σ + f_y τ)(·, X, Y) dB)_t`,

the stochastic integral being `predItoIntegral` of the predictable integrand
`f_x(s, X_s, Y_s) σ_s + f_y(s, X_s, Y_s) τ_s`, whose paths are almost surely continuous. The term
`f_xy σ τ` is the quadratic covariation `d⟨X, Y⟩ = σ τ dt` of the two martingale parts (both are
integrals against the same `B`). No bound on `σ`, `τ`, `b`, `c`, `f` or its partials is
assumed. -/
theorem ito_formula_adapted_two_factor_process :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      f t (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b t ω)
          (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c t ω) = f 0 x₀ y₀
        + ∫ s in Ioc 0 t, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
            (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω)
            (localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω) ∂timeMeasure
        + predItoIntegral (μ := μ) T hBmeas
            (itoIntegrand2_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc hb_adap
              hb_cont hc_adap hc_cont x₀ y₀ hf_x_cont hf_y_cont) t ω := by
  set X := localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b
  set Y := localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c
  have hXc := ae_continuousOn_localItoProcess hB T hBmeas hBcont hσa hσc hb_cont x₀
  have hYc := ae_continuousOn_localItoProcess hB T hBmeas hBcont hτa hτc hc_cont y₀
  have hXY : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T)
      ∧ ContinuousOn (fun t ↦ Y t ω) (Icc 0 T) := by
    filter_upwards [hXc, hYc] with ω h1 h2 using ⟨h1, h2⟩
  have hwx : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (X s ω) (Y s ω)) (Icc 0 T) :=
    hXY.mono fun ω h ↦ continuousOn_comp_time_pair hf_x_cont h.1 h.2
  have hwy : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_y s (X s ω) (Y s ω)) (Icc 0 T) :=
    hXY.mono fun ω h ↦ continuousOn_comp_time_pair hf_y_cont h.1 h.2
  have hpx := comp_time_localItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa
    hτc hb_adap hb_cont hc_adap hc_cont x₀ y₀ hf_x_cont
  have hpy := comp_time_localItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa
    hτc hb_adap hb_cont hc_adap hc_cont x₀ y₀ hf_y_cont
  have hθ₁ : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ f_x s (X s ω) (Y s ω) * σ s ω :=
    hpx.mul (isStronglyPredictable_of_bdd_adapted_cont hBmeas hσa hσc)
  have hθ₂ : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ f_y s (X s ω) (Y s ω) * τ s ω :=
    hpy.mul (isStronglyPredictable_of_bdd_adapted_cont hBmeas hτa hτc)
  have hθ := itoIntegrand2_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc hb_adap
    hb_cont hc_adap hc_cont x₀ y₀ hf_x_cont hf_y_cont
  have hc₁ : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (X s ω) (Y s ω) * σ s ω) (Icc 0 T) :=
    hwx.mono fun ω h ↦ h.mul (hσc ω).continuousOn
  have hc₂ : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_y s (X s ω) (Y s ω) * τ s ω) (Icc 0 T) :=
    hwy.mono fun ω h ↦ h.mul (hτc ω).continuousOn
  have hc₃ : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (X s ω) (Y s ω) * σ s ω
      + f_y s (X s ω) (Y s ω) * τ s ω) (Icc 0 T) :=
    (hc₁.and hc₂).mono fun ω h ↦ h.1.add h.2
  have hsplit := ae_predItoIntegral_add hB T hBmeas hBcont hθ₁ hθ₂ hθ hc₁ hc₂ hc₃
    (Eventually.of_forall fun ω s _ ↦ rfl)
  -- at each time, the stochastic integral is the limit in probability of the Riemann sums
  have hfix (t : ℝ≥0) (ht : t ∈ Icc 0 T) :
      predItoIntegral (μ := μ) T hBmeas hθ t =ᵐ[μ] fun ω ↦ f t (X t ω) (Y t ω) - f 0 x₀ y₀
        - ∫ s in Ioc 0 t, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
            (X s ω) (Y s ω) ∂timeMeasure :=
    ((show predItoIntegral (μ := μ) T hBmeas hθ t =ᵐ[μ] fun ω ↦ predItoIntegral (μ := μ) T hBmeas
        hθ₁ t ω + predItoIntegral (μ := μ) T hBmeas hθ₂ t ω from
      hsplit.mono fun ω h ↦ h t ht).trans
      (tendstoInMeasure_ae_unique
        ((tendstoInMeasure_riemannStieltjes_localItoIntegral hB T hBmeas hBcont hσa hσc hpx hwx
          ht.2).add
          (tendstoInMeasure_riemannStieltjes_localItoIntegral hB T hBmeas hBcont hτa hτc hpy hwy
            ht.2))
        (ito_formula_adapted_two_factor_unbounded_le hB T hBmeas hBcont hσa hσc hτa hτc hb_adap
          hb_cont hc_adap hc_cont x₀ y₀ hf_t hf_x hf_y hf_xx hf_xy hf_yy hf_t_cont hf_x_cont
          hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont ht.2)))
  have hfc := continuous_uncurry_three_of_continuous_partials hf_t hf_x hf_y hf_t_cont hf_x_cont
    hf_y_cont
  have hRc : ∀ᵐ ω ∂μ, ContinuousOn (fun t : ℝ≥0 ↦ f t (X t ω) (Y t ω) - f 0 x₀ y₀
      - ∫ s in Ioc 0 t, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
          (X s ω) (Y s ω) ∂timeMeasure) (Icc 0 T) := by
    filter_upwards [hXY] with ω hω
    exact ((continuousOn_comp_time_pair hfc hω.1 hω.2).sub continuousOn_const).sub
      (continuousOn_driftPath (ω := ω) (T := T)
        (b := fun (s : ℝ≥0) (ω : Ω) ↦ ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω)
          (σ s ω) (τ s ω) s (X s ω) (Y s ω))
        (continuousOn_ito2Drift hf_t_cont hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont
          hω.1 hω.2 (hb_cont ω).continuousOn (hc_cont ω).continuousOn (hσc ω).continuousOn
          (hτc ω).continuousOn))
  filter_upwards [ae_forall_eq_of_continuousOn
    (ae_continuousOn_predItoIntegral hB T hBmeas hBcont hθ hc₃) hRc hfix] with ω h t ht
  linarith [h t ht]

end Unbounded

end ItoFormulaAdapted

end MathFin
