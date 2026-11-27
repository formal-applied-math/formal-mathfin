/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaTwoFactor
public import MathFin.Probability.Brownian.Ito.ItoFormulaTwoFactorCutoff

/-! # The two-factor Itô formula for `f` with unbounded partials

`ito_formula_adapted_two_factor_against` (`ItoFormulaTwoFactor`) needs bounded partials. This file
removes that assumption, for bounded coefficients, by the space cutoff of `ItoFormulaCutoff` in
three variables (`ItoFormulaTwoFactorCutoff`), exactly as `ito_formula_adapted_td_local` does for
`f(t, x)`.

Let `B` be a Brownian motion with continuous paths, `σ`, `τ`, `b`, `c` bounded, adapted to its
natural filtration, with every path continuous, `X = x₀ + ∫ b ds + σ●B` and
`Y = y₀ + ∫ c ds + τ●B` (`adaptedItoProcess`, horizon `T`, one Brownian motion), and `f(t, x, y)`
with jointly continuous partials `f_t`, `f_x`, `f_y`, `f_xx`, `f_xy = ∂_y f_x`, `f_yy`. The sums
`∑ f_x(tₖ, Xₖ, Yₖ) ΔM^σ_k + ∑ f_y(tₖ, Xₖ, Yₖ) ΔM^τ_k` along the uniform partitions of `[0, T]`
converge in probability to
`f(T, X_T, Y_T) − f(0, x₀, y₀) − ∫₀ᵀ ito2Drift (s, X_s, Y_s) ds`
(`ito_formula_adapted_two_factor_local`), and the same on `[0, t]` for each `t ≤ T`
(`ito_formula_adapted_two_factor_local_le`).

On the event that `X` and `Y` stay in `[−N, N]` on `[0, T]` the cutoff of `f` is inert, so the
sums and the limit are those of the cut-off function, which has bounded partials; the events
exhaust `Ω` in probability (`tendsto_measure_compl_abs_le`), and convergence in measure is local
(`tendstoInMeasure_of_eqOn`).

Not here: unbounded coefficients (`ItoFormulaTwoFactorUnbounded`).

## Main results

* `ito_formula_adapted_two_factor_local`: for bounded coefficients and `f` with jointly continuous
  partials, no bound on the partials, the Riemann–Stieltjes sums of `f_x(·, X, Y)` against `M^σ`
  plus those of `f_y(·, X, Y)` against `M^τ` converge in measure to
  `f(T, X_T, Y_T) − f(0, x₀, y₀) − ∫₀ᵀ ito2Drift ds`.
* `ito_formula_adapted_two_factor_local_le`: the same on `[0, t]` for every `t ≤ T`.
* `continuousOn_comp_time_pair`: a function of the time and of two paths continuous on `[0, T]`,
  jointly continuous in its three arguments, is continuous on `[0, T]`.
* `tendsto_measure_compl_inter`: the complements of two exhausting families of events exhaust.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.3.6
* [Revuz and Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], Theorem IV.3.3

## Tags

Itô formula, Itô lemma, two-dimensional Itô formula, localisation, cutoff, Itô process,
MSC 60H05, MSC 60H10
-/

@[expose] public section

namespace MathFin

namespace LocalisationInMeasure

open MeasureTheory Filter Topology

/-- **Two exhausting families of events have an exhausting intersection**: if the complements of
`A N` and of `B N` have measure tending to `0`, so do the complements of `A N ∩ B N`. -/
theorem tendsto_measure_compl_inter {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : ℕ → Set Ω} (hA : Tendsto (fun N ↦ μ (A N)ᶜ) atTop (𝓝 0))
    (hB : Tendsto (fun N ↦ μ (B N)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ μ (A N ∩ B N)ᶜ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hA.add hB)
    (fun _ ↦ bot_le) fun N ↦ (measure_mono (compl_inter _ _).le).trans (measure_union_le _ _)

end LocalisationInMeasure

namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralBrownian
  QuadraticVariationL2 ItoIntegralProcessContinuousModification AdaptedDrift
  AdaptedRiemannStieltjes AdaptedQuadraticVariation ItoIntegralAgainstMartingale SummitC
  LocalisationInMeasure
open scoped NNReal ENNReal

/-- **A function of the time and of two paths**, jointly continuous in its three arguments, along
two paths continuous on `[0, T]` is continuous on `[0, T]`. -/
theorem continuousOn_comp_time_pair {T : ℝ≥0} {x y : ℝ≥0 → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) (hx : ContinuousOn x (Icc 0 T))
    (hy : ContinuousOn y (Icc 0 T)) :
    ContinuousOn (fun s : ℝ≥0 ↦ g s (x s) (y s)) (Icc 0 T) :=
  hg.comp_continuousOn (NNReal.continuous_coe.continuousOn.prodMk (hx.prodMk hy))

section Local

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ τ : ℝ≥0 → Ω → ℝ}
  (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω) {Cσ : ℝ} (hσb : ∀ t ω, |σ t ω| ≤ Cσ)
  (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
  (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω) {Cτ : ℝ} (hτb : ∀ t ω, |τ t ω| ≤ Cτ)
  {b c : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb)
  (hc_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (c t))
  (hc_cont : ∀ ω, Continuous fun s ↦ c s ω) {Cc : ℝ} (hc_bdd : ∀ s ω, |c s ω| ≤ Cc)
  (x₀ y₀ : ℝ)
  {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
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

include hB hBcont hσa hσc hσb hτa hτc hτb hb_adap hb_cont hb_bdd hc_adap hc_cont hc_bdd hf_t hf_x
  hf_y hf_xx hf_xy hf_yy hf_t_cont hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont in
/-- **Itô's formula for `f(t, X_t, Y_t)` along two Itô processes driven by one Brownian motion,
with no bound on the partials of `f`.** Let `B` be a Brownian motion with every path continuous,
`σ`, `τ`, `b`, `c` bounded, adapted to its natural filtration, with every path continuous,
`X = x₀ + ∫ b ds + M^σ` and `Y = y₀ + ∫ c ds + M^τ` (`adaptedItoProcess`, horizon `T`, with
`M^σ = σ●B`, `M^τ = τ●B`), and `f(t, x, y)` with jointly continuous partials `f_t`, `f_x`, `f_y`,
`f_xx`, `f_xy = ∂_y f_x`, `f_yy`. The left-point Riemann–Stieltjes sums
`∑ f_x(tₖ, Xₖ, Yₖ) ΔM^σ_k + ∑ f_y(tₖ, Xₖ, Yₖ) ΔM^τ_k` on the uniform partitions of `[0, T]`
converge in probability to

`f(T, X_T, Y_T) − f(0, x₀, y₀) − ∫₀ᵀ (f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²)
  (s, X_s, Y_s) ds`

(`ito2Drift`). No bound on `f` or its partials is assumed. -/
theorem ito_formula_adapted_two_factor_local :
    TendstoInMeasure μ (fun n ω ↦
        ∑ k ∈ Finset.range n,
          f_x (unifPart T n k)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b
              (unifPart T n k) ω)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c
              (unifPart T n k) ω)
          * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb)
              (unifPart T n (k + 1)) ω
            - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb)
              (unifPart T n k) ω)
        + ∑ k ∈ Finset.range n,
          f_y (unifPart T n k)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b
              (unifPart T n k) ω)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c
              (unifPart T n k) ω)
          * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb)
              (unifPart T n (k + 1)) ω
            - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb)
              (unifPart T n k) ω)) atTop
      fun ω ↦
        f T (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b T ω)
          (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c T ω)
        - f 0 x₀ y₀
        - ∫ s in Ioc 0 T, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b s ω)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c s ω)
            ∂timeMeasure := by
  set φσ := processToLp (μ := μ) T hBmeas hσa hσc hσb
  set φτ := processToLp (μ := μ) T hBmeas hτa hτc hτb
  set X := adaptedItoProcess T hBmeas φσ x₀ b
  set Y := adaptedItoProcess T hBmeas φτ y₀ c
  have hXp : IsStronglyPredictable (natFiltration hBmeas) X :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φσ hb_adap hb_cont hb_bdd x₀
  have hYp : IsStronglyPredictable (natFiltration hBmeas) Y :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φτ hc_adap hc_cont hc_bdd y₀
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φσ hb_cont hb_bdd x₀
  have hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φτ hc_cont hc_bdd y₀
  have hXYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T)
      ∧ ContinuousOn (fun t ↦ Y t ω) (Icc 0 T) := by
    filter_upwards [hXc, hYc] with ω h1 h2 using ⟨h1, h2⟩
  have hAX := tendsto_measure_compl_abs_le (T := T)
    (fun t ↦ ((hXp.stronglyAdapted t).mono ((natFiltration hBmeas).le t)).measurable) hXc
  have hAY := tendsto_measure_compl_abs_le (T := T)
    (fun t ↦ ((hYp.stronglyAdapted t).mono ((natFiltration hBmeas).le t)).measurable) hYc
  obtain ⟨S⟩ := smoothTrunc_exists
  -- the cutoff level `L N ≥ N, T`, so that on `[0, T] × [−N, N]²` the cutoff is inert
  set L : ℕ → ℕ := fun N ↦ N + ⌈(T : ℝ)⌉₊
  have hLN (N : ℕ) : (N : ℝ) ≤ L N := by simp [L]
  have hLT (N : ℕ) {s : ℝ≥0} (hs : s ≤ T) : |(s : ℝ)| ≤ L N := by
    rw [abs_of_nonneg s.coe_nonneg]
    calc (s : ℝ) ≤ T := hs
      _ ≤ ⌈(T : ℝ)⌉₊ := Nat.le_ceil _
      _ ≤ L N := by simp [L]
  choose Ct hCt using fun N ↦ fTruncT3_bdd (f_t := f_t) S (L N) hf_t_cont
  choose Cx hCx using fun N ↦ fTruncX3_bdd (f_x := f_x) S (L N) hf_x_cont
  choose Cy hCy using fun N ↦ fTruncY3_bdd (f_y := f_y) S (L N) hf_y_cont
  choose Cxx hCxx using fun N ↦ fTruncXX3_bdd (f_x := f_x) (f_xx := f_xx) S (L N) hf_x_cont
    hf_xx_cont
  choose Cxy hCxy using fun N ↦ fTruncXY3_bdd (f_xy := f_xy) S (L N) hf_xy_cont
  choose Cyy hCyy using fun N ↦ fTruncYY3_bdd (f_y := f_y) (f_yy := f_yy) S (L N) hf_y_cont
    hf_yy_cont
  have hxc (N : ℕ) := fTruncX3_continuous (f_x := f_x) S (L N) hf_x_cont
  have hyc (N : ℕ) := fTruncY3_continuous (f_y := f_y) S (L N) hf_y_cont
  refine tendstoInMeasure_of_eqOn
    (A := fun N : ℕ ↦ {ω | ∀ t ∈ Icc 0 T, |X t ω| ≤ N} ∩ {ω | ∀ t ∈ Icc 0 T, |Y t ω| ≤ N})
    (tendsto_measure_compl_inter hAX hAY)
    (fun N ↦ (tendstoInMeasure_riemannStieltjes hB T hBmeas φσ
        (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φσ ht)
        (comp_time_adaptedItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont φσ φτ hb_adap
          hb_cont hb_bdd hc_adap hc_cont hc_bdd x₀ y₀ (hxc N))
        (hXYc.mono fun ω h ↦ continuousOn_comp_time_pair (hxc N) h.1 h.2)
        fun s ω ↦ hCx N s (X s ω) (Y s ω)).add
      (tendstoInMeasure_riemannStieltjes hB T hBmeas φτ
        (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φτ ht)
        (comp_time_adaptedItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont φσ φτ hb_adap
          hb_cont hb_bdd hc_adap hc_cont hc_bdd x₀ y₀ (hyc N))
        (hXYc.mono fun ω h ↦ continuousOn_comp_time_pair (hyc N) h.1 h.2)
        fun s ω ↦ hCy N s (X s ω) (Y s ω)))
    (fun N n ω hω ↦ ?_) fun N ↦ ?_
  · -- the sums agree where the cutoff is inert
    congr 1
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : unifPart T n k ≤ T := unifPart_le_T (Finset.mem_range.1 hk).le
      rw [fTruncX3_eq_of S (hLT N hk') ((hω.1 _ ⟨zero_le, hk'⟩).trans (hLN N))
        ((hω.2 _ ⟨zero_le, hk'⟩).trans (hLN N))]
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : unifPart T n k ≤ T := unifPart_le_T (Finset.mem_range.1 hk).le
      rw [fTruncY3_eq_of S (hLT N hk') ((hω.1 _ ⟨zero_le, hk'⟩).trans (hLN N))
        ((hω.2 _ ⟨zero_le, hk'⟩).trans (hLN N))]
  · filter_upwards [ito_formula_adapted_two_factor_against hB T hBmeas hBcont hσa hσc hσb hτa hτc
      hτb hb_adap hb_cont hb_bdd hc_adap hc_cont hc_bdd x₀ y₀ (fTrunc3_hasDerivAt_t hf_t S (L N))
      (fTrunc3_hasDerivAt_x hf_x S (L N)) (fTrunc3_hasDerivAt_y hf_y S (L N))
      (fTrunc3_hasDerivAt_xx hf_xx S (L N)) (fTrunc3_hasDerivAt_xy hf_xy S (L N))
      (fTrunc3_hasDerivAt_yy hf_yy S (L N)) (fTruncT3_continuous S (L N) hf_t_cont) (hxc N)
      (hyc N) (fTruncXX3_continuous S (L N) hf_x_cont hf_xx_cont)
      (fTruncXY3_continuous S (L N) hf_xy_cont)
      (fTruncYY3_continuous S (L N) hf_y_cont hf_yy_cont) (hCt N) (hCx N) (hCy N) (hCxx N)
      (hCxy N) (hCyy N),
    adaptedItoProcess_zero hB T hBmeas hBcont φσ x₀ (b := b),
    adaptedItoProcess_zero hB T hBmeas hBcont φτ y₀ (b := c)] with ω hk h0x h0y hω
    have hx₀ : |x₀| ≤ L N := by
      rw [← show X 0 ω = x₀ from h0x]
      exact (hω.1 0 ⟨le_rfl, zero_le⟩).trans (hLN N)
    have hy₀ : |y₀| ≤ L N := by
      rw [← show Y 0 ω = y₀ from h0y]
      exact (hω.2 0 ⟨le_rfl, zero_le⟩).trans (hLN N)
    have hXT : |X T ω| ≤ L N := (hω.1 T ⟨zero_le, le_rfl⟩).trans (hLN N)
    have hYT : |Y T ω| ≤ L N := (hω.2 T ⟨zero_le, le_rfl⟩).trans (hLN N)
    have hint : ∫ s in Ioc 0 T, ito2Drift (fTruncT3 f_t S (L N)) (fTruncX3 f_x S (L N))
          (fTruncY3 f_y S (L N)) (fTruncXX3 f_x f_xx S (L N)) (fTruncXY3 f_xy S (L N))
          (fTruncYY3 f_y f_yy S (L N)) (b s ω) (c s ω) (σ s ω) (τ s ω) s (X s ω) (Y s ω)
          ∂timeMeasure
        = ∫ s in Ioc 0 T, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
          (X s ω) (Y s ω) ∂timeMeasure := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
      have hsT := hLT N hs.2
      have hXs := (hω.1 s (Ioc_subset_Icc_self hs)).trans (hLN N)
      have hYs := (hω.2 s (Ioc_subset_Icc_self hs)).trans (hLN N)
      simp only [ito2Drift, fTruncT3_eq_of S hsT hXs hYs, fTruncX3_eq_of S hsT hXs hYs,
        fTruncY3_eq_of S hsT hXs hYs, fTruncXX3_eq_of S hsT hXs hYs,
        fTruncXY3_eq_of S hsT hXs hYs, fTruncYY3_eq_of S hsT hXs hYs]
    rw [fTrunc3_eq_of S (hLT N le_rfl) hXT hYT, fTrunc3_eq_of S (s := 0) (by simp) hx₀ hy₀,
      hint] at hk
    linarith

include hB hBcont hσa hσc hσb hτa hτc hτb hb_adap hb_cont hb_bdd hc_adap hc_cont hc_bdd hf_t hf_x
  hf_y hf_xx hf_xy hf_yy hf_t_cont hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont in
/-- **Itô's formula for `f(t, X_t, Y_t)` at every time `t ≤ T`**, for the processes built at
horizon `T`: the Riemann–Stieltjes sums on the uniform partitions of `[0, t]` converge in
probability to `f(t, X_t, Y_t) − f(0, x₀, y₀) − ∫₀ᵗ ito2Drift (s, X_s, Y_s) ds`. The martingale
parts built at horizons `t` and `T` agree on `[0, t]` almost surely
(`ae_itoContinuousMod_eq_of_le`). -/
theorem ito_formula_adapted_two_factor_local_le {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦
        ∑ k ∈ Finset.range n,
          f_x (unifPart t n k)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b
              (unifPart t n k) ω)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c
              (unifPart t n k) ω)
          * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb)
              (unifPart t n (k + 1)) ω
            - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb)
              (unifPart t n k) ω)
        + ∑ k ∈ Finset.range n,
          f_y (unifPart t n k)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b
              (unifPart t n k) ω)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c
              (unifPart t n k) ω)
          * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb)
              (unifPart t n (k + 1)) ω
            - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb)
              (unifPart t n k) ω)) atTop
      fun ω ↦
        f t (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b t ω)
          (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c t ω)
        - f 0 x₀ y₀
        - ∫ s in Ioc 0 t, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b s ω)
            (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c s ω)
            ∂timeMeasure := by
  have hMσ := ae_itoContinuousMod_eq_of_le hB T hBmeas hBcont hσa hσc hσb ht
  have hMτ := ae_itoContinuousMod_eq_of_le hB T hBmeas hBcont hτa hτc hτb ht
  refine (ito_formula_adapted_two_factor_local hB t hBmeas hBcont hσa hσc hσb hτa hτc hτb hb_adap
    hb_cont hb_bdd hc_adap hc_cont hc_bdd x₀ y₀ hf_t hf_x hf_y hf_xx hf_xy hf_yy hf_t_cont
    hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont).congr (fun n ↦ ?_) ?_
  · filter_upwards [hMσ, hMτ] with ω hσ hτ
    congr 1
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.1 hk
      rw [adaptedItoProcess_eq_of_eqOn hσ ⟨zero_le, unifPart_le_T hk'.le⟩,
        adaptedItoProcess_eq_of_eqOn hτ ⟨zero_le, unifPart_le_T hk'.le⟩,
        hσ _ ⟨zero_le, unifPart_le_T hk'⟩, hσ _ ⟨zero_le, unifPart_le_T hk'.le⟩]
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.1 hk
      rw [adaptedItoProcess_eq_of_eqOn hσ ⟨zero_le, unifPart_le_T hk'.le⟩,
        adaptedItoProcess_eq_of_eqOn hτ ⟨zero_le, unifPart_le_T hk'.le⟩,
        hτ _ ⟨zero_le, unifPart_le_T hk'⟩, hτ _ ⟨zero_le, unifPart_le_T hk'.le⟩]
  · filter_upwards [hMσ, hMτ] with ω hσ hτ
    rw [adaptedItoProcess_eq_of_eqOn hσ ⟨zero_le, le_rfl⟩,
      adaptedItoProcess_eq_of_eqOn hτ ⟨zero_le, le_rfl⟩]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    rw [adaptedItoProcess_eq_of_eqOn hσ (Ioc_subset_Icc_self hs),
      adaptedItoProcess_eq_of_eqOn hτ (Ioc_subset_Icc_self hs)]

end Local

end ItoFormulaAdapted

end MathFin
