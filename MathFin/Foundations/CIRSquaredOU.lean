/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.WienerIntegralL2
public import MathFin.Foundations.WienerIntegralGaussian

/-!
# The CIR squared-OU construction at the mean-dynamics level

The CIR variance process constructed explicitly as `V t := (X₁ t)² + (X₂ t)²`, where
each `Xᵢ` is an explicit Ornstein–Uhlenbeck fluctuation built **without any SDE
solver** from the library's stochastic integral for deterministic integrands:

`Xᵢ t := e^{−(k/2)·t} · (x_{i0} + s · ∫₀ᵗ e^{(k/2)u} dBᵢ_u)`.

With `v₀ := x_{10}² + x_{20}²` and `θ := 2s²/k` (so `2kθ = (2s)²`, the
Feller-borderline parametrization of `dV = k(θ − V) dt + 2s√V dW`), the headline is
the CIR mean dynamics `𝔼[V t] = θ·(1 − e^{−kt}) + v₀·e^{−kt}` (`cirVariance_mean`).

Honest scope, recorded as content: existence is landed at the level the current
substrate supports — explicit per-`t` Gaussian random variables with exact laws and
moments (`ouProcess_hasLaw`, `ouProcess_integral`, `ouProcess_integral_sq`), not
path-level processes. The bounded-coefficient Itô-drift engines do not apply to this
construction for four independent reasons: the OU drift `−(k/2)·X_u` has linear
growth (unbounded, so outside every `|β| ≤ Db` hypothesis); the deterministic-drift
decomposition's residual is mean-reverting rather than a martingale, so no
`hMeq`-pinning can hold; the exponential integrand is not globally bounded; and no
path-continuous modification of the `L²` Itô integral is constructed in the library.
The E-level headline needs only that `B₁`, `B₂` are each pre-Brownian — independence
of the pair is *not* used (expectations add regardless); the full law of `V` (via the
Lévy characterization of the normalized square root) would need it and is future work.

## Result

Public API (all in namespace `MathFin.CIRSquaredOU`):

* `ouKernel`, `ouKernelLp`, `ouKernel_integral_sq`, `ouKernelLp_integral_sq`,
  `ouWienerLaw`, `ouWiener_integral`, `ouWiener_integral_sq` — the deterministic
  kernel, its `L²`-closed-form norm, and the exact Gaussian law/isometry of the
  fluctuation core;
* `ouProcess`, `ouProcess_hasLaw`, `ouProcess_integral`, `ouProcess_integral_sq`,
  `ouDrift_integral`, `ouProcess_drift_shape` — the explicit OU construction with
  law, mean, second moment and drift decomposition;
* `cirTheta`, `cirTheta_borderline`, `cirVariance`, `cirVariance_nonneg`,
  `cirVariance_mean` — the CIR variance process, its pathwise nonnegativity, and the
  headline mean dynamics.

Supporting lemmas (`expMul_key`, `ouWiener_memLp`, `ouWiener_integrable`,
`ouWiener_sq_integrable`, `ouProcess_sq_expansion`, `ouProcess_sq_integrable`) are
`private`.
-/

@[expose] public section

namespace MathFin.CIRSquaredOU

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal
open MathFin WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The exponential bookkeeping (private) -/

/-- The key exponential identity: `e^{−kt}·(e^{kt} − 1)/k = (1 − e^{−kt})/k` —
the decay of the fluctuation's prefactor against the isometry's growth. -/
private lemma expMul_key {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    Real.exp (-(k * t)) * ((Real.exp (k * t) - 1) / k)
      = (1 - Real.exp (-(k * t))) / k := by
  have h1 : Real.exp (-(k * t)) * Real.exp (k * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc Real.exp (-(k * t)) * ((Real.exp (k * t) - 1) / k)
      = (Real.exp (-(k * t)) * Real.exp (k * t) - Real.exp (-(k * t))) / k := by
          field_simp
    _ = (1 - Real.exp (-(k * t))) / k := by rw [h1]

/-! ### The OU kernel and its Wiener integral -/

/-- **The OU kernel** `u ↦ e^{(k/2)·u}` — the deterministic integrand of the
fluctuation `s·e^{−(k/2)t}·∫₀ᵗ e^{(k/2)u} dB_u`. -/
noncomputable def ouKernel (k u : ℝ) : ℝ := Real.exp ((k / 2) * u)

/-- The kernel is continuous (an exponential of an affine map). -/
lemma ouKernel_continuous (k : ℝ) : Continuous (ouKernel k) := by
  unfold ouKernel; fun_prop

/-- **The kernel is in `L²((0, t])`**: on the support `u ≤ t` and `k > 0`, so
`e^{(k/2)u} ≤ e^{(k/2)t}` — bounded, hence `L^∞ ⊆ L²` on the finite interval
(the `hwKernel_memLp` idiom). -/
lemma ouKernel_memLp {k : ℝ} (hk : 0 < k) (t : ℝ≥0) :
    MemLp (ouKernel k) 2 (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
  refine (memLp_top_of_bound (by unfold ouKernel; fun_prop) (Real.exp (k / 2 * (t : ℝ)))
      ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro u hu
  rw [ouKernel, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 (by positivity))

/-- **The kernel as an `L²((0, t])` element** — the argument of
`wienerIntegralLp B hB t`, the stack's Wiener integral of a deterministic integrand
(`WienerIntegralL2.wienerIntegralLp`). -/
noncomputable def ouKernelLp {k : ℝ} (hk : 0 < k) (t : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) :=
  (ouKernel_memLp hk t).toLp _

/-- **The kernel's `L²`-norm squared in closed form**:
`∫₀ᵗ (e^{(k/2)u})² du = ∫₀ᵗ e^{ku} du = (e^{kt} − 1)/k` by the FTC with
antiderivative `e^{ku}/k` (the `hwIntegral_exp_pos_const` idiom, `Θ = 1`). -/
lemma ouKernel_integral_sq {k : ℝ} (hk : k ≠ 0) (t : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (ouKernel k u) ^ 2 ∂volume
      = (Real.exp (k * (t : ℝ)) - 1) / k := by
  have hsq : ∀ u : ℝ, (ouKernel k u) ^ 2 = Real.exp (k * u) := by
    intro u
    rw [ouKernel, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [integral_congr_ae (ae_of_all _ hsq),
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  have hF : ∀ u ∈ Set.uIcc (0 : ℝ) (t : ℝ),
      HasDerivAt (fun u : ℝ => Real.exp (k * u) / k) (Real.exp (k * u)) u := by
    intro u _
    have hk' : HasDerivAt (fun u : ℝ => k * u) k u := by
      simpa using (hasDerivAt_id u).const_mul k
    have h := (hk'.exp).div_const k
    have hval : (Real.exp (k * u) * k) / k = Real.exp (k * u) := by
      field_simp
    rw [hval] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- The `L²`-element version of the norm-squared identity (the representative is
a.e. the honest kernel — the `hwKernelLp_integral_sq` idiom). -/
lemma ouKernelLp_integral_sq {k : ℝ} (hk : 0 < k) (t : ℝ≥0) :
    (∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (ouKernelLp hk t u) ^ 2 ∂volume)
      = (Real.exp (k * (t : ℝ)) - 1) / k := by
  rw [show (∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (ouKernelLp hk t u) ^ 2 ∂volume)
        = ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), (ouKernel k u) ^ 2 ∂volume by
      refine integral_congr_ae ?_
      filter_upwards [(ouKernel_memLp hk t).coeFn_toLp] with u hu
      rw [ouKernelLp, hu]]
  exact ouKernel_integral_sq hk.ne' t

/-- **The exact law of the OU fluctuation core**: `∫₀ᵗ e^{(k/2)u} dB_u` is centered
Gaussian with variance `(e^{kt} − 1)/k` (`wienerIntegralLp_hasLaw_gaussian` + the
norm identity — the `hwKernelWienerLaw` idiom). -/
lemma ouWienerLaw (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k) (t : ℝ≥0) :
    HasLaw (fun ω ↦ wienerIntegralLp B hB t (ouKernelLp hk t) ω)
      (gaussianReal 0 (((Real.exp (k * (t : ℝ)) - 1) / k).toNNReal)) μ := by
  have h0 := wienerIntegralLp_hasLaw_gaussian hB t (ouKernelLp hk t)
  rw [ouKernelLp_integral_sq hk t] at h0
  exact h0

/-- **The fluctuation core is centered**: `𝔼[∫₀ᵗ e^{(k/2)u} dB_u] = 0` (the Gaussian
law transported through `HasLaw.integral_eq` + `integral_id_gaussianReal`). -/
lemma ouWiener_integral (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k) (t : ℝ≥0) :
    ∫ ω, wienerIntegralLp B hB t (ouKernelLp hk t) ω ∂μ = 0 := by
  rw [(ouWienerLaw hB hk t).integral_eq, integral_id_gaussianReal]

/-- **The isometry in closed form**: `𝔼[(∫₀ᵗ e^{(k/2)u} dB_u)²] = (e^{kt} − 1)/k`
(`wienerIntegralLp_integral_sq`, the Itô isometry for deterministic integrands,
+ the kernel norm identity). -/
lemma ouWiener_integral_sq (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (t : ℝ≥0) :
    ∫ ω, (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2 ∂μ
      = (Real.exp (k * (t : ℝ)) - 1) / k := by
  have h1 := wienerIntegralLp_integral_sq hB t (ouKernelLp hk t)
  rw [ouKernelLp_integral_sq hk t] at h1
  exact h1

/-! ### Integrability of the core (private plumbing) -/

omit [IsProbabilityMeasure μ] in
/-- The core is in `L²(μ)` — it *is* an `Lp` element. -/
private lemma ouWiener_memLp (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (t : ℝ≥0) :
    MemLp (fun ω ↦ wienerIntegralLp B hB t (ouKernelLp hk t) ω) 2 μ :=
  Lp.memLp _

/-- The core is integrable (`L² ⊆ L¹` on a probability space). -/
private lemma ouWiener_integrable (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (t : ℝ≥0) :
    Integrable (fun ω ↦ wienerIntegralLp B hB t (ouKernelLp hk t) ω) μ :=
  memLp_one_iff_integrable.mp
    ((ouWiener_memLp hB hk t).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- The core's square is integrable (`L²` ⇒ `I² ∈ L¹` on a probability space). -/
private lemma ouWiener_sq_integrable (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (t : ℝ≥0) :
    Integrable (fun ω ↦ (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2) μ := by
  have h := (ouWiener_memLp hB hk t).integrable_norm_pow' (p := 2)
  exact Integrable.congr h (ae_of_all μ fun ω ↦ by simp [Real.norm_eq_abs, sq_abs])

/-! ### The OU process -/

/-- **The OU fluctuation process** (explicit solution, no SDE solver):
`X_t = e^{−(k/2)t}·(x₀ + s·∫₀ᵗ e^{(k/2)u} dB_u)` — the dispatch's literal shape,
with the stochastic integral instantiated as the stack's Wiener integral
`wienerIntegralLp B hB t (ouKernelLp hk t)`. Per `t` this is a random variable with
an exact Gaussian law (`ouProcess_hasLaw` below); the path-level reading
(continuity/adaptedness) is blocked at this pin (see the module header, wall 4). -/
noncomputable def ouProcess (hB : IsPreBrownianReal B μ) (k s x0 : ℝ)
    (hk : 0 < k) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(k / 2 * (t : ℝ))) * (x0
    + s * wienerIntegralLp B hB t (ouKernelLp hk t) ω)

/-- **The OU law**: `X_t ~ N(x₀·e^{−(k/2)t}, (s²/k)·(1 − e^{−kt}))` — the affine
image of the centered core (the `hwIntegratedRate_hasLaw_gaussian` idiom). This is
the honest landing of "OU existence, explicitly": the exact per-`t` law, from which
every E-level statement below follows. -/
theorem ouProcess_hasLaw (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) :
    HasLaw (ouProcess hB k s x0 hk t)
      (gaussianReal (x0 * Real.exp (-(k / 2 * (t : ℝ))))
        ((s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ))))).toNNReal)) μ := by
  have hkt : (0 : ℝ) ≤ k * (t : ℝ) := mul_nonneg hk.le (NNReal.coe_nonneg t)
  have hV : (0 : ℝ) ≤ (Real.exp (k * (t : ℝ)) - 1) / k :=
    div_nonneg (sub_nonneg_of_le (Real.one_le_exp_iff.mpr hkt)) hk.le
  have hVR : (0 : ℝ) ≤ s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ)))) := by
    refine mul_nonneg (div_nonneg (sq_nonneg s) hk.le) ?_
    exact sub_nonneg_of_le (Real.exp_le_one_iff.mpr (by nlinarith [hkt]))
  have hW := ouWienerLaw hB hk t
  have hShift := gaussianReal_const_add (gaussianReal_const_mul hW
    (s * Real.exp (-(k / 2 * (t : ℝ))))) (x0 * Real.exp (-(k / 2 * (t : ℝ))))
  have hfun : ∀ ω : Ω, ouProcess hB k s x0 hk t ω
      = x0 * Real.exp (-(k / 2 * (t : ℝ)))
        + s * Real.exp (-(k / 2 * (t : ℝ)))
          * wienerIntegralLp B hB t (ouKernelLp hk t) ω := by
    intro ω
    simp only [ouProcess]
    ring
  have hmean : s * Real.exp (-(k / 2 * (t : ℝ))) * 0
      + x0 * Real.exp (-(k / 2 * (t : ℝ)))
      = x0 * Real.exp (-(k / 2 * (t : ℝ))) := by ring
  have hvar : NNReal.mk ((s * Real.exp (-(k / 2 * (t : ℝ)))) ^ 2)
      (sq_nonneg (s * Real.exp (-(k / 2 * (t : ℝ)))))
      * (((Real.exp (k * (t : ℝ)) - 1) / k).toNNReal)
      = (s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ))))).toNNReal := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hV,
      Real.coe_toNNReal _ hVR]
    have hm : (s * Real.exp (-(k / 2 * (t : ℝ)))) ^ 2
        = s ^ 2 * Real.exp (-(k * (t : ℝ))) := by
      rw [mul_pow]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc (s * Real.exp (-(k / 2 * (t : ℝ)))) ^ 2
          * ((Real.exp (k * (t : ℝ)) - 1) / k)
        = s ^ 2 * (Real.exp (-(k * (t : ℝ)))
            * ((Real.exp (k * (t : ℝ)) - 1) / k)) := by rw [hm]; ring
      _ = s ^ 2 * ((1 - Real.exp (-(k * (t : ℝ)))) / k) :=
          by rw [expMul_key hk.ne' (t : ℝ)]
      _ = s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ)))) := by ring
  refine ⟨hShift.aemeasurable.congr (ae_of_all μ fun ω ↦ (hfun ω).symm), ?_⟩
  rw [Measure.map_congr (ae_of_all μ hfun), hShift.map_eq, hmean, hvar]

/-- **The OU mean**: `𝔼[X_t] = x₀·e^{−(k/2)t}` — the deterministic drift survives
the centered fluctuation untouched. -/
theorem ouProcess_integral (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) :
    ∫ ω, ouProcess hB k s x0 hk t ω ∂μ = x0 * Real.exp (-(k / 2 * (t : ℝ))) := by
  have hsplit : ∀ ω : Ω, ouProcess hB k s x0 hk t ω
      = Real.exp (-(k / 2 * (t : ℝ))) * x0
        + Real.exp (-(k / 2 * (t : ℝ))) * s
          * wienerIntegralLp B hB t (ouKernelLp hk t) ω := by
    intro ω
    simp only [ouProcess]
    ring
  have hA : ∫ ω : Ω, Real.exp (-(k / 2 * (t : ℝ))) * x0 ∂μ
      = x0 * Real.exp (-(k / 2 * (t : ℝ))) := by
    simp
    ring
  have hBterm : ∫ ω : Ω, Real.exp (-(k / 2 * (t : ℝ))) * s
      * wienerIntegralLp B hB t (ouKernelLp hk t) ω ∂μ
      = Real.exp (-(k / 2 * (t : ℝ))) * s
        * ∫ ω : Ω, wienerIntegralLp B hB t (ouKernelLp hk t) ω ∂μ
    := integral_const_mul _ (fun ω : Ω ↦ wienerIntegralLp B hB t (ouKernelLp hk t) ω)
  rw [integral_congr_ae (ae_of_all μ hsplit),
    integral_add (integrable_const _) ((ouWiener_integrable hB hk t).const_mul _),
    hA, hBterm, ouWiener_integral, mul_zero, add_zero]

omit [IsProbabilityMeasure μ] in
/-- **The pointwise square expansion** (private plumbing for the second moment):
`(e^{−(k/2)t}(x₀ + sI_ω))² = e^{−kt}(x₀² + 2x₀s·I_ω + s²·I_ω²)`. -/
private lemma ouProcess_sq_expansion (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) : ∀ ω : Ω,
    (ouProcess hB k s x0 hk t ω) ^ 2
      = Real.exp (-(k * (t : ℝ))) * x0 ^ 2
        + Real.exp (-(k * (t : ℝ))) * (2 * x0 * s)
          * wienerIntegralLp B hB t (ouKernelLp hk t) ω
        + Real.exp (-(k * (t : ℝ))) * s ^ 2
          * (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2 := by
  intro ω
  simp only [ouProcess]
  have h2 : Real.exp (-(k / 2 * (t : ℝ))) * Real.exp (-(k / 2 * (t : ℝ)))
      = Real.exp (-(k * (t : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (Real.exp (-(k / 2 * (t : ℝ)))
        * (x0 + s * wienerIntegralLp B hB t (ouKernelLp hk t) ω)) ^ 2
      = (Real.exp (-(k / 2 * (t : ℝ)))) ^ 2
          * (x0 + s * wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2 := by ring
    _ = Real.exp (-(k * (t : ℝ)))
          * (x0 ^ 2 + 2 * x0 * s * wienerIntegralLp B hB t (ouKernelLp hk t) ω
            + s ^ 2 * (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2) := by
          rw [pow_two, h2]
          ring
    _ = Real.exp (-(k * (t : ℝ))) * x0 ^ 2
          + Real.exp (-(k * (t : ℝ))) * (2 * x0 * s)
            * wienerIntegralLp B hB t (ouKernelLp hk t) ω
          + Real.exp (-(k * (t : ℝ))) * s ^ 2
            * (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2 := by ring

/-- The OU square is integrable (const + `L¹` core + `L¹` core², per the expansion). -/
private lemma ouProcess_sq_integrable (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ (ouProcess hB k s x0 hk t ω) ^ 2) μ :=
  ((integrable_const _).add
    ((ouWiener_integrable hB hk t).const_mul _)).add
    ((ouWiener_sq_integrable hB hk t).const_mul _) |>.congr
      (ae_of_all μ fun ω ↦ (ouProcess_sq_expansion hB hk s x0 t ω).symm)

/-- **The OU second moment** (the component engine of the headline):
`𝔼[X_t²] = x₀²·e^{−kt} + (s²/k)·(1 − e^{−kt})` — deterministic decay plus the
isometry term `s²·e^{−kt}·(e^{kt} − 1)/k`. -/
theorem ouProcess_integral_sq (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) :
    ∫ ω, (ouProcess hB k s x0 hk t ω) ^ 2 ∂μ
      = x0 ^ 2 * Real.exp (-(k * (t : ℝ)))
        + s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ)))) := by
  have hA : ∫ ω : Ω, Real.exp (-(k * (t : ℝ))) * x0 ^ 2 ∂μ
      = Real.exp (-(k * (t : ℝ))) * x0 ^ 2 := by
    simp
  have hBterm : ∫ ω : Ω, Real.exp (-(k * (t : ℝ))) * (2 * x0 * s)
      * wienerIntegralLp B hB t (ouKernelLp hk t) ω ∂μ
      = Real.exp (-(k * (t : ℝ))) * (2 * x0 * s)
        * ∫ ω : Ω, wienerIntegralLp B hB t (ouKernelLp hk t) ω ∂μ
    := integral_const_mul _ (fun ω : Ω ↦ wienerIntegralLp B hB t (ouKernelLp hk t) ω)
  have hCterm : ∫ ω : Ω, Real.exp (-(k * (t : ℝ))) * s ^ 2
      * (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2 ∂μ
      = Real.exp (-(k * (t : ℝ))) * s ^ 2
        * ∫ ω : Ω, (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2 ∂μ
    := integral_const_mul _ (fun ω : Ω ↦ (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2)
  have hfin : Real.exp (-(k * (t : ℝ))) * s ^ 2
      * ((Real.exp (k * (t : ℝ)) - 1) / k)
      = s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ)))) := by
    calc Real.exp (-(k * (t : ℝ))) * s ^ 2
          * ((Real.exp (k * (t : ℝ)) - 1) / k)
        = s ^ 2 * (Real.exp (-(k * (t : ℝ)))
            * ((Real.exp (k * (t : ℝ)) - 1) / k)) := by ring
      _ = s ^ 2 * ((1 - Real.exp (-(k * (t : ℝ)))) / k) := by
          rw [expMul_key hk.ne' (t : ℝ)]
      _ = s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ)))) := by ring
  have hI1 : Integrable (fun ω : Ω ↦ Real.exp (-(k * (t : ℝ))) * x0 ^ 2
      + Real.exp (-(k * (t : ℝ))) * (2 * x0 * s)
        * wienerIntegralLp B hB t (ouKernelLp hk t) ω) μ :=
    (integrable_const _).add ((ouWiener_integrable hB hk t).const_mul _)
  have hI2 : Integrable (fun ω : Ω ↦ Real.exp (-(k * (t : ℝ))) * s ^ 2
      * (wienerIntegralLp B hB t (ouKernelLp hk t) ω) ^ 2) μ :=
    (ouWiener_sq_integrable hB hk t).const_mul _
  rw [integral_congr_ae (ae_of_all μ (ouProcess_sq_expansion hB hk s x0 t)),
    integral_add hI1 hI2, integral_add (integrable_const _)
      ((ouWiener_integrable hB hk t).const_mul _),
    hA, hBterm, ouWiener_integral, mul_zero, add_zero, hCterm,
    ouWiener_integral_sq, hfin]
  ring

/-! ### The drift decomposition (the dispatch's requested shape) -/

/-- **The deterministic drift integral** (the `b` of the dispatch's shape):
`∫₀ᵗ −(k/2)·x₀·e^{−(k/2)u} du = x₀·(e^{−(k/2)t} − 1)` — FTC with antiderivative
`x₀·e^{−(k/2)u}`. -/
theorem ouDrift_integral {k : ℝ} (x0 t : ℝ) :
    ∫ u in (0 : ℝ)..t, -(k / 2) * x0 * Real.exp (-(k / 2 * u))
      = x0 * (Real.exp (-(k / 2 * t)) - 1) := by
  have hexp : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => Real.exp (-(k / 2 * u)))
        (Real.exp (-(k / 2 * u)) * -(k / 2)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => k / 2 * u) (k / 2) u := by
      simpa using (hasDerivAt_id u).const_mul (k / 2)
    simpa using h1.neg.exp
  have hF : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => x0 * Real.exp (-(k / 2 * u)))
        (-(k / 2) * x0 * Real.exp (-(k / 2 * u))) u := by
    intro u hu
    have h := (hexp u hu).const_mul x0
    have hval : x0 * (Real.exp (-(k / 2 * u)) * -(k / 2))
        = -(k / 2) * x0 * Real.exp (-(k / 2 * u)) := by ring
    rw [hval] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

omit [IsProbabilityMeasure μ] in
/-- **The drift+fluctuation decomposition** (the dispatch's shape, as a pointwise
identity — honest scope: the fluctuation term is *not* an Itô-integral process, see
the module header, wall 2): `X_t = x₀ + ∫₀ᵗ b + s·e^{−(k/2)t}·∫₀ᵗ e^{(k/2)u} dB_u`
with `b_u = −(k/2)·x₀·e^{−(k/2)u}`, combined via `ouDrift_integral`. -/
theorem ouProcess_drift_shape (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) (ω : Ω) :
    ouProcess hB k s x0 hk t ω
      = x0 + (∫ u in (0 : ℝ)..(t : ℝ), -(k / 2) * x0 * Real.exp (-(k / 2 * u)))
        + s * Real.exp (-(k / 2 * (t : ℝ)))
          * wienerIntegralLp B hB t (ouKernelLp hk t) ω := by
  rw [ouDrift_integral x0 (t : ℝ)]
  simp only [ouProcess]
  ring

/-! ### The CIR variance process and the headline -/

variable {B1 B2 : ℝ≥0 → Ω → ℝ}

/-- **The CIR long-run variance** `θ := 2s²/k` — the Feller-borderline
parametrization of `dV = k(θ − V) dt + 2s√V dW`. -/
noncomputable def cirTheta (s k : ℝ) : ℝ := 2 * s ^ 2 / k

/-- **The borderline identity**: `2kθ = (2s)²` — the diffusion coefficient `2s√V`
squares to exactly `2kθ·V` at the boundary where the squared-OU construction
represents the CIR dimension. Guard `k ≠ 0` (at `k = 0` the identity is false:
Lean's `x/0 = 0` makes the left side vanish). -/
theorem cirTheta_borderline (s k : ℝ) (hk : k ≠ 0) :
    2 * k * cirTheta s k = (2 * s) ^ 2 := by
  rw [cirTheta]
  field_simp

/-- **The CIR variance process** (the 2D squared-OU construction):
`V_t := (X₁_t)² + (X₂_t)²` with `Xᵢ` the OU fluctuation driven by `Bᵢ`
from initial value `x_{i0}`. -/
noncomputable def cirVariance (hB1 : IsPreBrownianReal B1 μ)
    (hB2 : IsPreBrownianReal B2 μ) (k s x10 x20 : ℝ) (hk : 0 < k)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  (ouProcess hB1 k s x10 hk t ω) ^ 2 + (ouProcess hB2 k s x20 hk t ω) ^ 2

omit [IsProbabilityMeasure μ] in
/-- **Pathwise nonnegativity**: `V_t(ω) ≥ 0` for every `(t, ω)` — the defining
property a square-root diffusion needs, holding pathwise by construction. -/
theorem cirVariance_nonneg (hB1 : IsPreBrownianReal B1 μ)
    (hB2 : IsPreBrownianReal B2 μ) (k s x10 x20 : ℝ) (hk : 0 < k)
    (t : ℝ≥0) (ω : Ω) :
    0 ≤ cirVariance hB1 hB2 k s x10 x20 hk t ω :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The CIR mean dynamics** (the headline):
`𝔼[V_t] = θ·(1 − e^{−kt}) + v₀·e^{−kt}` with `θ = 2s²/k` and
`v₀ = x_{10}² + x_{20}²` — mean reversion towards `θ` at rate `k`, from initial
variance `v₀`. Route: the component second moments `ouProcess_integral_sq`
(per component, `x₀²·e^{−kt} + (s²/k)(1 − e^{−kt})`), summed. Independence of
`B₁, B₂` is not used — expectations add regardless (module header, independence
note). -/
theorem cirVariance_mean (hB1 : IsPreBrownianReal B1 μ)
    (hB2 : IsPreBrownianReal B2 μ) {k : ℝ} (hk : 0 < k) (s x10 x20 : ℝ)
    (t : ℝ≥0) :
    ∫ ω, cirVariance hB1 hB2 k s x10 x20 hk t ω ∂μ
      = cirTheta s k * (1 - Real.exp (-(k * (t : ℝ))))
        + (x10 ^ 2 + x20 ^ 2) * Real.exp (-(k * (t : ℝ))) := by
  have hI1 := ouProcess_sq_integrable hB1 hk s x10 t
  have hI2 := ouProcess_sq_integrable hB2 hk s x20 t
  simp only [cirVariance]
  rw [integral_add hI1 hI2,
    ouProcess_integral_sq hB1 hk s x10 t,
    ouProcess_integral_sq hB2 hk s x20 t, cirTheta]
  ring


end MathFin.CIRSquaredOU
