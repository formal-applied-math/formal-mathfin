/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralCrossHorizon
public import MathFin.Foundations.ItoIntegralProcessContinuousModification
public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
public import MathFin.Foundations.LocalisationInMeasure

/-! # The Itô integral of an unbounded continuous adapted integrand

The `L²` Itô integral `∫ σ dB` of the library is built for bounded integrands (`processToLp`,
`itoContinuousMod`). An adapted `σ` with continuous paths need not be bounded, nor `∫₀ᵀ σ² ds`
integrable, yet every path of `σ` is bounded on `[0, T]`. This file builds `∫ σ dB` for such `σ`
by localisation in the sample space, without stopping times.

Clip `σ` to `[−N, N]` (`clip`, through `clampM`). The clipped integrand is bounded, adapted and
path-continuous, so it has the continuous Itô integral `M^N` (`clipItoMod`). On the event that the
path of `σ` stays in `[−N, N]` up to `T`, the integrands `clip n σ` and `clip N σ` (`n ≤ N`) are
the same, and so are their left-point Riemann sums `∑ σ(tₖ)(B_{tₖ₊₁} − B_{tₖ})`. Those sums converge
in measure to `M^n_t` and `M^N_t` (`tendstoInMeasure_riemannσ_itoContinuousMod`), and limits in
measure are local (`ae_eq_of_tendstoInMeasure_of_eqOn`), so `M^n = M^N` almost surely on the event,
at each time and then, by continuity, on all of `[0, T]` (`ae_clipItoMod_eq`). Every path of `σ`
is bounded on `[0, T]` by some integer, the least being `pathLevel`, and `localItoIntegral` reads
`M^N` at that level. The level reads the whole path on `[0, T]`, so `localItoIntegral t` is not
shown adapted; it is the integral on `[0, T]` only.

* `tendstoInMeasure_riemannσ_localItoIntegral`: for `t ≤ T` the Riemann sums of `σ` on `[0, t]`
  converge in probability to `localItoIntegral t`. This characterises the integral: it is the
  Itô integral as the limit in probability of its Riemann sums (Revuz–Yor IV.2.13).
* `ae_continuousOn_localItoIntegral`: almost every path is continuous on `[0, T]`.
* `ae_localItoIntegral_eq_itoContinuousMod`: for bounded `σ` it is the `L²` construction.

Not here: the local-martingale property of `localItoIntegral`.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralLocalised

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralBrownian
  QuadraticVariationL2 ItoIntegralProcessContinuousModification ItoIntegralRiemannBridge
  LocalisationInMeasure
open scoped NNReal ENNReal

/-! ### Clipping -/

theorem continuous_clampM (M : ℝ) : Continuous (clampM M) := by
  unfold clampM
  fun_prop

/-- The process `σ` clipped to `[−N, N]`. -/
noncomputable def clip {Ω : Type*} (N : ℕ) (σ : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ clampM N (σ t ω)

theorem abs_clip_le {Ω : Type*} (N : ℕ) (σ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    |clip N σ t ω| ≤ N :=
  clampM_abs_le (Nat.cast_nonneg N) _

theorem clip_eq_self {Ω : Type*} {N : ℕ} {σ : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω}
    (h : |σ t ω| ≤ N) : clip N σ t ω = σ t ω :=
  clampM_eq_self h

theorem clip_continuous {Ω : Type*} {σ : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t ↦ σ t ω)
    (N : ℕ) (ω : Ω) : Continuous fun t ↦ clip N σ t ω :=
  (continuous_clampM N).comp (hcont ω)

theorem clip_adapted {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {σ : ℝ≥0 → Ω → ℝ} (hadap : ∀ t, StronglyMeasurable[𝓕 t] (σ t)) (N : ℕ) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] (clip N σ t) :=
  (continuous_clampM N).comp_stronglyMeasurable (hadap t)

/-- The least integer bounding the path `x` on `[0, T]`; `0` when there is none. -/
noncomputable def pathLevel (T : ℝ≥0) (x : ℝ≥0 → ℝ) : ℕ :=
  sInf {N : ℕ | ∀ t ∈ Icc 0 T, |x t| ≤ N}

/-- A path continuous on `[0, T]` is bounded there by its level (`exists_nat_abs_le_Icc`). -/
theorem abs_le_pathLevel {T : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, |x t| ≤ pathLevel T x :=
  Nat.sInf_mem (exists_nat_abs_le_Icc hx)

theorem pathLevel_le {T : ℝ≥0} {x : ℝ≥0 → ℝ} {N : ℕ} (h : ∀ t ∈ Icc 0 T, |x t| ≤ N) :
    pathLevel T x ≤ N :=
  Nat.sInf_le h

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω))

/-! ### Bounded integrands at intermediate times -/

include hB hBcont in
/-- **For a bounded integrand the Riemann sums on `[0, t]` converge in measure to the continuous
Itô integral at `t`**, built at any horizon `T ≥ t`: the sums converge to the `L²` integral at
horizon `t` (`tendstoInMeasure_riemannσ`), which is the integral at horizon `T` read at time `t`
(`itoProcessCLM_consist`), and `itoContinuousMod` is a modification of it. -/
theorem tendstoInMeasure_riemannσ_itoContinuousMod {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)
    {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ↦ riemannσ (B := B) σ t n) atTop
      (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) t) := by
  have h := (itoContinuousMod_modification hB T hBmeas hBcont
    (processToLp (μ := μ) T hBmeas hadap hcont hbdd) ht).symm
  rw [itoProcessCLM_consist hB hBmeas le_rfl ht hadap hcont hbdd, itoProcessCLM_terminal_eq] at h
  exact (tendstoInMeasure_riemannσ hB hBmeas hadap hcont hbdd t).congr_right h

/-! ### The clipped integrals -/

/-- The continuous Itô integral of the integrand clipped to `[−N, N]`. -/
noncomputable def clipItoMod (N : ℕ) : ℝ≥0 → Ω → ℝ :=
  itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas (clip_adapted hadap N)
    (clip_continuous hcont N) (abs_clip_le N σ))

include hB hBcont in
/-- **The clipped integrals agree where the clipping is inactive.** For `n ≤ N`, almost surely on
the event that `σ` stays in `[−n, n]` up to `T`, `M^n` and `M^N` are the same path on `[0, T]`. -/
theorem ae_clipItoMod_eq {n N : ℕ} (hnN : n ≤ N) :
    ∀ᵐ ω ∂μ, (∀ t ∈ Icc 0 T, |σ t ω| ≤ n) →
      ∀ t ∈ Icc 0 T, clipItoMod (μ := μ) T hBmeas hadap hcont n t ω
        = clipItoMod (μ := μ) T hBmeas hadap hcont N t ω := by
  refine ae_forall_eq_of_continuousOn (A := {ω | ∀ t ∈ Icc 0 T, |σ t ω| ≤ n})
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _)
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _) fun t ht ↦ ?_
  refine ae_eq_of_tendstoInMeasure_of_eqOn
    (tendstoInMeasure_riemannσ_itoContinuousMod hB T hBmeas hBcont (clip_adapted hadap n)
      (clip_continuous hcont n) (abs_clip_le n σ) ht.2)
    (tendstoInMeasure_riemannσ_itoContinuousMod hB T hBmeas hBcont (clip_adapted hadap N)
      (clip_continuous hcont N) (abs_clip_le N σ) ht.2) fun m ω hω ↦ ?_
  refine riemannσ_congr (fun s hs ↦ ?_) m
  have hs' := hω s ⟨zero_le, hs.2.trans ht.2⟩
  rw [clip_eq_self hs', clip_eq_self (hs'.trans (Nat.cast_le.2 hnN))]

/-! ### The integral -/

/-- **The Itô integral of a continuous adapted integrand**, possibly unbounded: on each path, the
continuous Itô integral of `σ` clipped at the least integer bounding that path on `[0, T]`. It is
the integral on `[0, T]` only; past `T` its value carries no meaning. -/
noncomputable def localItoIntegral (t : ℝ≥0) (ω : Ω) : ℝ :=
  clipItoMod (μ := μ) T hBmeas hadap hcont (pathLevel T fun s ↦ σ s ω) t ω

include hB hBcont in
/-- Almost surely, wherever `σ` stays in `[−N, N]` up to `T`, the integral is `M^N` on `[0, T]`. -/
theorem ae_localItoIntegral_eq :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, (∀ t ∈ Icc 0 T, |σ t ω| ≤ N) →
      ∀ t ∈ Icc 0 T, localItoIntegral (μ := μ) T hBmeas hadap hcont t ω
        = clipItoMod (μ := μ) T hBmeas hadap hcont N t ω := by
  have h (n N : ℕ) : ∀ᵐ ω ∂μ, n ≤ N → (∀ t ∈ Icc 0 T, |σ t ω| ≤ n) →
      ∀ t ∈ Icc 0 T, clipItoMod (μ := μ) T hBmeas hadap hcont n t ω
        = clipItoMod (μ := μ) T hBmeas hadap hcont N t ω := by
    rcases le_or_gt n N with hnN | hNn
    · filter_upwards [ae_clipItoMod_eq hB T hBmeas hBcont hadap hcont hnN] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h ↦ absurd h hNn.not_ge
  filter_upwards [ae_all_iff.2 fun n ↦ ae_all_iff.2 (h n)] with ω hω N hN t ht
  exact hω _ N (pathLevel_le hN) (abs_le_pathLevel (hcont ω).continuousOn) t ht

include hB hBcont in
/-- **Almost every path of the integral is continuous on `[0, T]`.** -/
theorem ae_continuousOn_localItoIntegral :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ localItoIntegral (μ := μ) T hBmeas hadap hcont t ω)
      (Icc 0 T) := by
  filter_upwards [ae_localItoIntegral_eq hB T hBmeas hBcont hadap hcont,
    ae_all_iff.2 fun N ↦ itoContinuousMod_continuousOn hB T hBmeas hBcont
      (processToLp (μ := μ) T hBmeas (clip_adapted hadap N) (clip_continuous hcont N)
        (abs_clip_le N σ))] with ω hω hc
  exact (hc (pathLevel T fun s ↦ σ s ω)).congr fun t ht ↦
    hω _ (abs_le_pathLevel (hcont ω).continuousOn) t ht

include hB hBcont in
/-- **The integral is the limit in probability of its Riemann sums.** For `t ≤ T` the left-point
Riemann–Itô sums `∑ σ(tₖ)(B_{tₖ₊₁} − B_{tₖ})` on the uniform partitions of `[0, t]` converge in
probability to `localItoIntegral t`. On the event that `σ` stays in `[−N, N]` up to `T` the sums
are those of the clipped integrand, which converge to `M^N_t`, and the events exhaust `Ω` in
probability (`tendsto_measure_compl_abs_le`). -/
theorem tendstoInMeasure_riemannσ_localItoIntegral {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ↦ riemannσ (B := B) σ t n) atTop
      (localItoIntegral (μ := μ) T hBmeas hadap hcont t) := by
  refine tendstoInMeasure_of_eqOn (A := fun N : ℕ ↦ {ω | ∀ s ∈ Icc 0 T, |σ s ω| ≤ N})
    (tendsto_measure_compl_abs_le
      (fun s ↦ ((hadap s).mono ((natFiltration hBmeas).le s)).measurable)
      (Eventually.of_forall fun ω ↦ (hcont ω).continuousOn))
    (fun N ↦ tendstoInMeasure_riemannσ_itoContinuousMod hB T hBmeas hBcont (clip_adapted hadap N)
      (clip_continuous hcont N) (abs_clip_le N σ) ht)
    (fun N m ω hω ↦ riemannσ_congr (fun s hs ↦ (clip_eq_self (hω s ⟨zero_le, hs.2.trans ht⟩)).symm)
      m) fun N ↦ ?_
  filter_upwards [ae_localItoIntegral_eq hB T hBmeas hBcont hadap hcont] with ω hω hN
    using hω N hN t ⟨zero_le, ht⟩

include hB hBcont in
/-- **For a bounded integrand the integral is the `L²` Itô integral**: almost surely the same path
on `[0, T]` as `itoContinuousMod`, both being limits in probability of the same Riemann sums. -/
theorem ae_localItoIntegral_eq_itoContinuousMod {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, localItoIntegral (μ := μ) T hBmeas hadap hcont t ω
      = itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) t ω := by
  filter_upwards [ae_forall_eq_of_continuousOn (A := univ)
    (ae_continuousOn_localItoIntegral hB T hBmeas hBcont hadap hcont)
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _) fun t ht ↦
      (tendstoInMeasure_ae_unique
        (tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont hadap hcont ht.2)
        (tendstoInMeasure_riemannσ_itoContinuousMod hB T hBmeas hBcont hadap hcont hbdd ht.2)).mono
        fun _ h _ ↦ h] with ω hω
  exact hω (mem_univ ω)

end ItoIntegralLocalised
end MathFin
