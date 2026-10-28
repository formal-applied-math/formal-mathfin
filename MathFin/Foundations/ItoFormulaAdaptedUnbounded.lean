/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdaptedTD
public import MathFin.Foundations.ItoIntegralLocalised

/-! # Itô's formula along an Itô process with unbounded adapted coefficients

Let `B` be a Brownian motion with continuous paths, and `σ`, `b` adapted to its natural
filtration with every path continuous, but not bounded. The Itô integral `M = ∫ σ dB` is
`localItoIntegral`, the limit in probability of its Riemann sums, and `X = x₀ + ∫ b ds + M` is
`localItoProcess`. For `t ≤ T` and `f(t, x)` with jointly continuous partials `f_t`, `f_x`, `f_xx`,
the left-point Riemann–Stieltjes sums `∑ f_x(tₖ, X_{tₖ})(M_{tₖ₊₁} − M_{tₖ})` on the uniform
partitions of `[0, t]` converge in probability to

`f(t, X_t) − f(0, x₀) − ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`

(`ito_formula_adapted_unbounded_le`, and `ito_formula_adapted_unbounded_C2_le` for `f(x)`).

The proof is one more localisation in the sample space. On the event that `σ` and `b` stay in
`[−N, N]` up to `T`, they equal their clippings `clip N σ`, `clip N b`, which are bounded; there
`X` is almost surely the Itô process of the clipped coefficients (`ae_localItoProcess_eq`), whose
formula is `ito_formula_adapted_td_local_le`, and its Riemann sums and limit are those of `X`. The
events exhaust `Ω` in probability (`tendsto_measure_compl_abs_le`), and convergence in measure is
local (`tendstoInMeasure_of_ae_eqOn`).

Not here: the formula as an identity of processes, and a random starting point.
-/

@[expose] public section

namespace MathFin
namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift ItoIntegralLocalised LocalisationInMeasure
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (x₀ : ℝ)

/-- **The Itô process `X = x₀ + ∫ b ds + ∫ σ dB` with unbounded coefficients**, the stochastic
integral being `localItoIntegral`. -/
noncomputable def localItoProcess (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ + driftPath b t ω + localItoIntegral (μ := μ) T hBmeas hadap hcont t ω

include hB hBcont in
/-- Almost surely, wherever `σ` and `b` stay in `[−N, N]` up to `T`, the process is on `[0, T]`
the Itô process of the coefficients clipped to `[−N, N]`. -/
theorem ae_localItoProcess_eq :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, (∀ s ∈ Icc 0 T, |σ s ω| ≤ N) → (∀ s ∈ Icc 0 T, |b s ω| ≤ N) →
      ∀ s ∈ Icc 0 T, localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω
        = adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas (clip_adapted hadap N)
            (clip_continuous hcont N) (abs_clip_le N σ)) x₀ (clip N b) s ω := by
  filter_upwards [ae_localItoIntegral_eq hB T hBmeas hBcont hadap hcont] with ω hω N hσ hb s hs
  rw [localItoProcess, adaptedItoProcess, hω N s hs fun r hr ↦ hσ r ⟨hr.1, hr.2.trans hs.2⟩,
    driftPath_congr fun r hr ↦ (clip_eq_self (hb r ⟨zero_le, hr.2.trans hs.2⟩)).symm]
  rfl

variable {f f_t f_x f_xx : ℝ → ℝ → ℝ}
  (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
  (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
  (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
  (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
  (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
  (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)

include hB hBcont hb_adap hb_cont hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont in
/-- **Itô's formula along an Itô process with unbounded adapted coefficients.** Let `B` be a
Brownian motion with every path continuous, `σ` and `b` adapted to the natural filtration of `B`
with every path continuous, `M = ∫ σ dB` (`localItoIntegral`), `X = x₀ + ∫ b ds + M`
(`localItoProcess`), and `f(t, x)` with jointly continuous partials `f_t`, `f_x`, `f_xx`. For
`t ≤ T` the left-point Riemann–Stieltjes sums of `f_x(s, X_s)` against `M` on the uniform
partitions of `[0, t]` converge in probability to

`f(t, X_t) − f(0, x₀) − ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`.

No bound on `σ`, `b`, `f` or the partials of `f` is assumed. -/
theorem ito_formula_adapted_unbounded_le {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f_x (unifPart t n k)
          (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b (unifPart t n k) ω)
        * (localItoIntegral (μ := μ) T hBmeas hadap hcont (unifPart t n (k + 1)) ω
          - localItoIntegral (μ := μ) T hBmeas hadap hcont (unifPart t n k) ω)) atTop
      fun ω ↦ f t (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω) - f 0 x₀
        - ∫ s in Ioc 0 t, (f_t s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
            + f_x s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * b s ω
            + 1 / 2 * (f_xx s (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  have hAσ := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hadap hcont
  have hAb := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hb_adap hb_cont
  refine tendstoInMeasure_of_ae_eqOn
    (A := fun N : ℕ ↦ {ω | ∀ s ∈ Icc 0 T, |σ s ω| ≤ N} ∩ {ω | ∀ s ∈ Icc 0 T, |b s ω| ≤ N})
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hAσ.add hAb)
      (fun _ ↦ bot_le) fun N ↦ (measure_mono (compl_inter _ _).le).trans (measure_union_le _ _))
    (fun N ↦ ito_formula_adapted_td_local_le hB T hBmeas hBcont (clip_adapted hadap N)
      (clip_continuous hcont N) (abs_clip_le N σ) (clip_adapted hb_adap N)
      (clip_continuous hb_cont N) (abs_clip_le N b) x₀ hf_t hf_x hf_xx hf_t_cont hf_x_cont
      hf_xx_cont ht) (fun N n ↦ ?_) fun N ↦ ?_
  · filter_upwards [ae_localItoProcess_eq hB T hBmeas hBcont hadap hcont x₀,
      ae_localItoIntegral_eq hB T hBmeas hBcont hadap hcont] with ω hX hM hω
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    have h1 : unifPart t n k ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk'.le).trans ht⟩
    have h2 : unifPart t n (k + 1) ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk').trans ht⟩
    rw [hX N hω.1 hω.2 _ h1, hM N _ h1 fun r hr ↦ hω.1 r ⟨hr.1, hr.2.trans h1.2⟩,
      hM N _ h2 fun r hr ↦ hω.1 r ⟨hr.1, hr.2.trans h2.2⟩]
    rfl
  · filter_upwards [ae_localItoProcess_eq hB T hBmeas hBcont hadap hcont x₀] with ω hX hω
    rw [hX N hω.1 hω.2 t ⟨zero_le, ht⟩]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have hs' : s ∈ Icc 0 T := ⟨zero_le, hs.2.trans ht⟩
    simp only [hX N hω.1 hω.2 s hs', clip_eq_self (hω.1 s hs'), clip_eq_self (hω.2 s hs')]

include hB hBcont hb_adap hb_cont in
/-- **Itô's formula for a `C²` function, with unbounded adapted coefficients.** For `X` as in
`ito_formula_adapted_unbounded_le`, `f` twice differentiable with `f''` continuous, and `t ≤ T`,
the left-point Riemann–Stieltjes sums of `f'(X)` against `M` on the uniform partitions of
`[0, t]` converge in probability to `f(X_t) − f(x₀) − ∫₀ᵗ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`. -/
theorem ito_formula_adapted_unbounded_C2_le {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f' (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b (unifPart t n k) ω)
        * (localItoIntegral (μ := μ) T hBmeas hadap hcont (unifPart t n (k + 1)) ω
          - localItoIntegral (μ := μ) T hBmeas hadap hcont (unifPart t n k) ω)) atTop
      fun ω ↦ f (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω) - f x₀
        - ∫ s in Ioc 0 t, (f' (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) * b s ω
            + 1 / 2 * (f'' (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  refine (ito_formula_adapted_unbounded_le hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀
    (f := fun _ x ↦ f x) (f_t := fun _ _ ↦ 0) (fun t x ↦ hasDerivAt_const t (f x))
    (fun _ x ↦ hf x) (fun _ x ↦ hf' x) continuous_const (hf'c.comp continuous_snd)
    (hf''.comp continuous_snd) ht).congr_right (Eventually.of_forall fun ω ↦ ?_)
  simp only [zero_add]

end ItoFormulaAdapted
end MathFin
