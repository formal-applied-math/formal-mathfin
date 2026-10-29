/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdaptedUnbounded
public import MathFin.Foundations.ItoIntegralLocalisedPredictable

/-! # Itô's formula as an identity of processes

Let `B` be a Brownian motion with continuous paths, `σ`, `b` adapted to its natural filtration
with every path continuous, not bounded, and `X = x₀ + ∫ b ds + ∫ σ dB` (`localItoProcess`). For
`f(t, x)` with jointly continuous partials `f_t`, `f_x`, `f_xx`, almost surely, at every
`t ∈ [0, T]` at once,

`f(t, X_t) = f(0, x₀) + ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds + (∫ f_x(·, X) σ dB)_t`

(`ito_formula_adapted_unbounded_process`), where the stochastic integral is `predItoIntegral` of
the integrand `f_x(s, X_s) σ_s`, a process in `t`. That integrand is predictable but has
continuous paths only almost surely, which is why it is the integral of
`ItoIntegralLocalisedPredictable`. The stochastic term is a continuous local martingale for the
null-augmented Brownian filtration, so `f(t, X_t)` minus its drift integral has a version that is
one (`exists_localMartingale_ito_formula`). A `C²` function `f(x)` is the case `f_t = 0`
(`ito_formula_adapted_unbounded_C2_process`).

The proof. At each `t ≤ T` the Riemann–Stieltjes sums of `f_x(·, X)` against `M = ∫ σ dB` converge
in probability to `f(t, X_t) − f(0, x₀) − ∫₀ᵗ …` (`ito_formula_adapted_unbounded_le`) and to
`(∫ f_x(·, X) σ dB)_t` (`tendstoInMeasure_riemannStieltjes_localItoIntegral`), so the two agree
almost surely. Both sides have paths continuous on `[0, T]` almost surely: `f` is jointly
continuous (`continuous_uncurry_of_continuous_partials`), and the drift integral is continuous in
its upper limit (`continuousOn_driftPath`). Processes with continuous paths that agree at each
time agree at all times (`ae_forall_eq_of_continuousOn`).

Along the way: the level of a continuous path is left-continuous in time
(`eventually_pathLevel_eq`), so `localItoIntegral` is predictable
(`isStronglyPredictable_localItoIntegral`), and so is `X`.

Not here: a random starting point, `T = ∞`, and Itô's formula for a continuous semimartingale not
built from `B`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

/-! ### Joint continuity from continuous partials -/

/-- **A function with jointly continuous partials is jointly continuous**:
`g(t, x) = g(0, 0) + ∫₀ᵗ g_t(s, 0) ds + ∫₀ˣ g_x(t, u) du`, and parametric integrals of a
continuous integrand are continuous. -/
theorem continuous_uncurry_of_continuous_partials {g g_t g_x : ℝ → ℝ → ℝ}
    (hg_t : ∀ t x, HasDerivAt (fun s ↦ g s x) (g_t t x) t)
    (hg_x : ∀ t x, HasDerivAt (fun u ↦ g t u) (g_x t x) x)
    (hg_t_cont : Continuous fun p : ℝ × ℝ ↦ g_t p.1 p.2)
    (hg_x_cont : Continuous fun p : ℝ × ℝ ↦ g_x p.1 p.2) :
    Continuous fun p : ℝ × ℝ ↦ g p.1 p.2 := by
  have h (t x : ℝ) :
      g t x = g 0 0 + (∫ s in (0 : ℝ)..t, g_t s 0) + ∫ u in (0 : ℝ)..x, g_x t u := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hg_t s 0)
        ((hg_t_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 t),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hg_x t u)
        ((hg_x_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 x)]
    ring
  rw [show (fun p : ℝ × ℝ ↦ g p.1 p.2) = fun p ↦ g 0 0 + (∫ s in (0 : ℝ)..p.1, g_t s 0)
      + ∫ u in (0 : ℝ)..p.2, g_x p.1 u from funext fun p ↦ h p.1 p.2]
  exact (continuous_const.add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (f := fun _ s ↦ g_t s 0)
      (hg_t_cont.comp (continuous_snd.prodMk continuous_const)) continuous_fst)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) u ↦ g_x p.1 u)
      (hg_x_cont.comp (continuous_fst.fst.prodMk continuous_snd))
      continuous_snd)

namespace ItoIntegralLocalised

open ItoIntegralL2 ItoIntegralBrownian ItoIntegralProcessContinuousModification
  LocalisationInMeasure

/-! ### The integral is predictable -/

/-- **The level of a continuous path is left-continuous in time**: just before `t` it is the level
at `t`. If the level at `t` is `k + 1`, the path exceeds `k` at some time `r ≤ t`; before `t` and
after `r`, or near `r = t` by continuity, it still does. -/
theorem eventually_pathLevel_eq {x : ℝ≥0 → ℝ} (hx : Continuous x) (t : ℝ≥0) :
    ∀ᶠ s in 𝓝[<] t, pathLevel s x = pathLevel t x := by
  have hmono (s : ℝ≥0) (hst : s ≤ t) : pathLevel s x ≤ pathLevel t x :=
    pathLevel_le fun r hr ↦ abs_le_pathLevel hx.continuousOn r ⟨hr.1, hr.2.trans hst⟩
  rcases Nat.eq_zero_or_pos (pathLevel t x) with h0 | hpos
  · exact eventually_nhdsWithin_of_forall fun s hs ↦ by have := hmono s (le_of_lt hs); omega
  obtain ⟨k, hk⟩ : ∃ k, pathLevel t x = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hnot : ∃ r ∈ Icc 0 t, (k : ℝ) < |x r| := by
    by_contra! h
    have := pathLevel_le h
    omega
  obtain ⟨r, hr, hrk⟩ := hnot
  have hev : ∀ᶠ s in 𝓝[<] t, ∃ r' ∈ Icc 0 s, (k : ℝ) < |x r'| := by
    rcases hr.2.lt_or_eq with hrt | rfl
    · filter_upwards [Ioo_mem_nhdsLT hrt] with s hs using ⟨r, ⟨hr.1, hs.1.le⟩, hrk⟩
    · filter_upwards [nhdsWithin_le_nhds
        ((continuous_abs.comp hx).continuousAt.eventually (lt_mem_nhds hrk))] with s hs
        using ⟨s, ⟨zero_le, le_rfl⟩, hs⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s ⟨r', hr', hr'k⟩ hs
  refine le_antisymm (hmono s (le_of_lt hs)) ?_
  by_contra hlt
  have h1 := abs_le_pathLevel hx.continuousOn r' hr'
  have h2 : (pathLevel s x : ℝ) ≤ k := Nat.cast_le.2 (by omega)
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω))

include hB hBcont in
/-- **The Itô integral of a continuous adapted integrand is predictable.** The level
`t ↦ pathLevel t σ` is adapted and left-continuous (`eventually_pathLevel_eq`), hence predictable,
and each clipped integral is predictable (`itoContinuousMod_isStronglyPredictable`); the integral
reads the clipped integral at the level. -/
theorem isStronglyPredictable_localItoIntegral :
    IsStronglyPredictable (natFiltration hBmeas)
      (localItoIntegral (μ := μ) T hBmeas hadap hcont) := by
  have hL : IsStronglyPredictable (natFiltration hBmeas)
      fun t ω ↦ pathLevel t fun s ↦ σ s ω :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous
      (fun t ↦ (measurable_pathLevel
        (fun s hs ↦ ((hadap s).mono ((natFiltration hBmeas).mono hs.2)).measurable)
        fun ω ↦ (hcont ω).continuousOn).stronglyMeasurable)
      fun ω a ↦ tendsto_const_nhds.congr'
        ((eventually_pathLevel_eq (hcont ω) a).mono fun _ h ↦ h.symm)
  exact (measurable_apply_countable (mΩ := (natFiltration hBmeas).predictable)
    (f := fun N p ↦ clipItoMod (μ := μ) T hBmeas hadap hcont N p.1 p.2)
    (fun _ ↦ (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont _).measurable)
    hL.measurable).stronglyMeasurable

end ItoIntegralLocalised

namespace ItoFormulaAdapted

open ItoIntegralL2 ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift ItoIntegralLocalised LocalisationInMeasure ItoIntegralProcessLocalMartingaleGeneral

/-! ### The drift of an unbounded rate -/

/-- **The drift integral is continuous in its upper limit** along a path of the rate continuous on
`[0, T]`: there it is the drift path of a bounded continuous rate (`continuous_driftPath`). -/
theorem continuousOn_driftPath {Ω : Type*} {b : ℝ≥0 → Ω → ℝ} {ω : Ω} {T : ℝ≥0}
    (hb : ContinuousOn (fun s ↦ b s ω) (Icc 0 T)) :
    ContinuousOn (fun t ↦ driftPath b t ω) (Icc 0 T) := by
  obtain ⟨N, hN⟩ := exists_nat_abs_le_Icc hb
  set c : ℝ≥0 → Unit → ℝ := fun s _ ↦ clampM N (b (min s T) ω)
  have hc (u : Unit) : Continuous fun s ↦ c s u :=
    (continuous_clampM N).comp (hb.comp_continuous (continuous_id.min continuous_const)
      fun s ↦ ⟨zero_le, min_le_right s T⟩)
  refine (continuous_driftPath hc (fun s _ ↦ clampM_abs_le (Nat.cast_nonneg N) _)
    ()).continuousOn.congr fun t ht ↦ setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
  have hs' : s ≤ T := hs.2.trans ht.2
  simp only [c, min_eq_left hs', clampM_eq_self (hN s ⟨zero_le, hs'⟩)]

/-- **Every drift path of a continuous rate is continuous**, bounded or not. -/
theorem continuous_driftPath_of_continuous {Ω : Type*} {b : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hb : Continuous fun s ↦ b s ω) : Continuous fun t ↦ driftPath b t ω :=
  continuous_iff_continuousAt.2 fun t ↦ (continuousOn_driftPath (T := t + 1)
    hb.continuousOn).continuousAt (mem_of_superset (Iio_mem_nhds (lt_add_one t))
      fun _ hs ↦ ⟨zero_le, le_of_lt hs⟩)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (x₀ : ℝ)

omit [IsProbabilityMeasure μ] in
include hb_adap hb_cont in
/-- **The drift path of a continuous adapted rate is predictable**, bounded or not: at each time
it is the limit of the drift paths of the clipped rates, which are adapted
(`stronglyMeasurable_driftPath`), and its paths are continuous. -/
theorem driftPath_isStronglyPredictable_of_continuous :
    IsStronglyPredictable (natFiltration hBmeas) (driftPath b) := by
  refine StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun t ↦ ?_)
    fun ω _ ↦ (continuous_driftPath_of_continuous (hb_cont ω)).continuousWithinAt
  have hm (N : ℕ) : StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (driftPath (clip N b) t) := stronglyMeasurable_driftPath hBmeas
    (clip_adapted hb_adap N) (clip_continuous hb_cont N) (abs_clip_le N b) t
  letI : MeasurableSpace Ω := natFiltration hBmeas t
  refine stronglyMeasurable_of_tendsto atTop hm
    (tendsto_pi_nhds.2 fun ω ↦ tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop (pathLevel t fun s ↦ b s ω)] with N hN
  exact driftPath_congr fun s hs ↦ (clip_eq_self
    ((abs_le_pathLevel (hb_cont ω).continuousOn s ⟨zero_le, hs.2⟩).trans (Nat.cast_le.2 hN))).symm

include hB hBcont hb_adap hb_cont in
/-- The Itô process with unbounded coefficients is predictable. -/
theorem isStronglyPredictable_localItoProcess :
    IsStronglyPredictable (natFiltration hBmeas)
      (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b) :=
  StronglyMeasurable.add (stronglyMeasurable_const.add
      (driftPath_isStronglyPredictable_of_continuous hBmeas hb_adap hb_cont))
    (isStronglyPredictable_localItoIntegral hB T hBmeas hBcont hadap hcont)

include hB hBcont hb_cont in
/-- Almost every path of the Itô process with unbounded coefficients is continuous on `[0, T]`. -/
theorem ae_continuousOn_localItoProcess :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω)
      (Icc 0 T) :=
  (ae_continuousOn_localItoIntegral hB T hBmeas hBcont hadap hcont).mono fun ω h ↦
    (continuous_const.add (continuous_driftPath_of_continuous (hb_cont ω))).continuousOn.add h

include hB hBcont hb_adap hb_cont in
/-- A jointly continuous function of the time and of the Itô process is predictable. -/
theorem comp_time_localItoProcess_isStronglyPredictable {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ g s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) := by
  have ht : IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ) :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun _ ↦ stronglyMeasurable_const)
      fun _ _ ↦ NNReal.continuous_coe.continuousWithinAt
  exact hg.comp_stronglyMeasurable (StronglyMeasurable.prodMk ht
    (isStronglyPredictable_localItoProcess hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀))

include hB hBcont hb_adap hb_cont in
/-- **The integrand `f_x(s, X_s) σ_s` of Itô's formula is predictable.** -/
theorem itoIntegrand_isStronglyPredictable {f_x : ℝ → ℝ → ℝ}
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ f_x s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * σ s ω :=
  (comp_time_localItoProcess_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont
    x₀ hf_x_cont).mul (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont)

/-! ### The formula -/

variable {f f_t f_x f_xx : ℝ → ℝ → ℝ}
  (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
  (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
  (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
  (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
  (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
  (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)

include hB hBcont hb_adap hb_cont hf_t hf_x hf_xx hf_t_cont hf_xx_cont in
/-- **Itô's formula as an identity of processes.** Let `B` be a Brownian motion with every path
continuous, `σ` and `b` adapted to the natural filtration of `B` with every path continuous,
`X = x₀ + ∫ b ds + ∫ σ dB` (`localItoProcess`), and `f(t, x)` with jointly continuous partials
`f_t`, `f_x`, `f_xx`. Almost surely, for every `t ∈ [0, T]` at once,

`f(t, X_t) = f(0, x₀) + ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds + (∫ f_x(·, X) σ dB)_t`,

the stochastic integral being `predItoIntegral` of the predictable integrand `f_x(s, X_s) σ_s`,
whose paths are almost surely continuous. No bound on `σ`, `b`, `f` or its partials is
assumed. -/
theorem ito_formula_adapted_unbounded_process :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      f t (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω) = f 0 x₀
        + ∫ (s : ℝ≥0) in Ioc 0 t, (f_t s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
            + f_x s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * b s ω
            + 1 / 2 * (f_xx s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure
        + predItoIntegral (μ := μ) T hBmeas (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont
            hadap hcont hb_adap hb_cont x₀ hf_x_cont) t ω := by
  set X := localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b
  have hX := ae_continuousOn_localItoProcess hB T hBmeas hBcont hadap hcont hb_cont x₀
  have hcomp {g : ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) {ω : Ω}
      (hω : ContinuousOn (fun t ↦ X t ω) (Icc 0 T)) :
      ContinuousOn (fun s : ℝ≥0 ↦ g s (X s ω)) (Icc 0 T) :=
    hg.comp_continuousOn (NNReal.continuous_coe.continuousOn.prodMk hω)
  have hwc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (X s ω)) (Icc 0 T) :=
    hX.mono fun ω h ↦ hcomp hf_x_cont h
  have hθ := itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀
    hf_x_cont
  have hθc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (X s ω) * σ s ω) (Icc 0 T) :=
    hwc.mono fun ω h ↦ h.mul (hcont ω).continuousOn
  have hfix (t : ℝ≥0) (ht : t ∈ Icc 0 T) :
      predItoIntegral (μ := μ) T hBmeas hθ t =ᵐ[μ] fun ω ↦ f t (X t ω) - f 0 x₀
        - ∫ (s : ℝ≥0) in Ioc 0 t, (f_t s (X s ω) + f_x s (X s ω) * b s ω
            + 1 / 2 * (f_xx s (X s ω) * σ s ω ^ 2)) ∂timeMeasure :=
    tendstoInMeasure_ae_unique (tendstoInMeasure_riemannStieltjes_localItoIntegral hB T hBmeas
        hBcont hadap hcont (comp_time_localItoProcess_isStronglyPredictable hB T hBmeas hBcont
          hadap hcont hb_adap hb_cont x₀ hf_x_cont) hwc ht.2)
      (ito_formula_adapted_unbounded_le hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀ hf_t
        hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont ht.2)
  have hfc := continuous_uncurry_of_continuous_partials hf_t hf_x hf_t_cont hf_x_cont
  have hRc : ∀ᵐ ω ∂μ, ContinuousOn (fun t : ℝ≥0 ↦ f t (X t ω) - f 0 x₀
      - ∫ (s : ℝ≥0) in Ioc 0 t, (f_t s (X s ω) + f_x s (X s ω) * b s ω
          + 1 / 2 * (f_xx s (X s ω) * σ s ω ^ 2)) ∂timeMeasure) (Icc 0 T) := by
    filter_upwards [hX] with ω hω
    exact ((hcomp hfc hω).sub continuousOn_const).sub
      (continuousOn_driftPath (ω := ω) (b := fun (s : ℝ≥0) ω ↦ f_t s (X s ω) + f_x s (X s ω) * b s ω
        + 1 / 2 * (f_xx s (X s ω) * σ s ω ^ 2))
        (((hcomp hf_t_cont hω).add ((hcomp hf_x_cont hω).mul (hb_cont ω).continuousOn)).add
          (continuousOn_const.mul ((hcomp hf_xx_cont hω).mul
            ((hcont ω).continuousOn.pow 2)))))
  filter_upwards [ae_forall_eq_of_continuousOn
    (ae_continuousOn_predItoIntegral hB T hBmeas hBcont hθ hθc) hRc hfix] with ω h t ht
  linarith [h t ht]

include hB hBcont hb_adap hb_cont hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont in
/-- **`f(t, X_t)` minus its drift integral is a continuous local martingale.** For `X` and `f` as
in `ito_formula_adapted_unbounded_process`, there is a process `Y` with every path continuous, a
local martingale for the null-augmented Brownian filtration, that is almost surely, at every
`t ∈ [0, T]`, `f(t, X_t) − f(0, x₀) − ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`: a version of the
stochastic term `∫ f_x(·, X) σ dB` (`exists_continuous_localMartingale_predItoIntegral`). -/
theorem exists_localMartingale_ito_formula :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
        Y t ω = f t (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω) - f 0 x₀
          - ∫ (s : ℝ≥0) in Ioc 0 t, (f_t s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
              + f_x s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * b s ω
              + 1 / 2 * (f_xx s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
                * σ s ω ^ 2)) ∂timeMeasure) ∧
      (∀ ω, Continuous fun t ↦ Y t ω) ∧
      IsLocalMartingale Y (augFiltration (μ := μ) hBmeas) μ := by
  have hθc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s
      (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * σ s ω) (Icc 0 T) :=
    (ae_continuousOn_localItoProcess hB T hBmeas hBcont hadap hcont hb_cont x₀).mono fun ω h ↦
      (hf_x_cont.comp_continuousOn (NNReal.continuous_coe.continuousOn.prodMk h)).mul
        (hcont ω).continuousOn
  obtain ⟨Y, hY, hYc, hYm⟩ := exists_continuous_localMartingale_predItoIntegral hB T hBmeas hBcont
    (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀
      hf_x_cont) hθc
  refine ⟨Y, ?_, hYc, hYm⟩
  filter_upwards [hY, ito_formula_adapted_unbounded_process hB T hBmeas hBcont hadap hcont
    hb_adap hb_cont x₀ hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont] with ω h1 h2 t ht
  rw [h1 t ht, h2 t ht]
  ring

include hB hBcont hb_adap hb_cont in
/-- **Itô's formula for a `C²` function, as an identity of processes.** For `X` as in
`ito_formula_adapted_unbounded_process` and `f` twice differentiable with `f''` continuous, almost
surely, for every `t ∈ [0, T]` at once,
`f(X_t) = f(x₀) + ∫₀ᵗ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds + (∫ f'(X) σ dB)_t`. The case `f_t = 0`
of `ito_formula_adapted_unbounded_process`. -/
theorem ito_formula_adapted_unbounded_C2_process {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      f (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω) = f x₀
        + ∫ (s : ℝ≥0) in Ioc 0 t,
            (f' (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * b s ω
              + 1 / 2 * (f'' (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
                * σ s ω ^ 2)) ∂timeMeasure
        + predItoIntegral (μ := μ) T hBmeas (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont
            hadap hcont hb_adap hb_cont x₀ (f_x := fun _ x ↦ f' x)
            ((Differentiable.continuous fun x ↦ (hf' x).differentiableAt).comp continuous_snd))
            t ω := by
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  filter_upwards [ito_formula_adapted_unbounded_process hB T hBmeas hBcont hadap hcont hb_adap
    hb_cont x₀ (f := fun _ x ↦ f x) (f_t := fun _ _ ↦ 0) (fun t x ↦ hasDerivAt_const t (f x))
    (fun _ x ↦ hf x) (fun _ x ↦ hf' x) continuous_const (hf'c.comp continuous_snd)
    (hf''.comp continuous_snd)] with ω h t ht
  simpa only [zero_add] using h t ht

end ItoFormulaAdapted
end MathFin
