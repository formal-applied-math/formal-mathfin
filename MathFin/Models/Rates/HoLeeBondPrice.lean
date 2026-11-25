/-
Copyright (c) 2026 WorldianAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WorldianAI
-/
module

public import MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian
public import MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment
public import MathFin.Models.Rates.VasicekZeroMeanReversionLimit

/-!
# The Ho–Lee zero-coupon bond price

The Ho–Lee short rate `dr_t = θ(t) dt + σ dB_t` is the member of the Gaussian short-rate family
with no mean reversion (`κ = 0`, the case that `Models/Rates/HullWhiteCalibration.lean` excludes
with `0 < κ`). Integrating it over `[0, T]` and swapping the time order sends the diffusion
kernel `1` to the **integrated kernel**

  `g(u) = ∫_u^T 1 ds = T − u`,

so `∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ g(u) dB_u`, with deterministic mean `M(T) = ∫₀ᵀ (r₀ + ∫₀ˢ θ) ds`.
As in the Vasicek and Hull–White files, the integrated rate is carried in this Wiener
representation (the time-order swap is the modelling bridge). The bond price is then a Gaussian
Laplace transform, the instance `f = g` of `integral_exp_neg_add_mul_wienerIntegralLp`, and the
variance of the diffusion part is `∫₀ᵀ (T − u)² du = T³/3`. The affine loading is `B(T) = T`, the
`κ → 0` limit of Vasicek's `(1 − e^{−κT})/κ`.

## Main definitions

* `integratedKernel`, `integratedKernelLp`: the kernel `g(u) = T − u` and its `L²((0, T])` element.
* `integratedMean`: the deterministic mean `∫₀ᵀ (r₀ + ∫₀ˢ θ) ds` of the integrated rate.
* `bondRate`: the integrated Ho–Lee short rate in its Wiener representation.
* `bondA`: the affine coefficient `A(T) = exp(−∫₀ᵀ θ(s)(T − s) ds + σ²T³/6)`.

## Main results

* `integral_integratedKernel_sq`: `∫₀ᵀ (T − u)² du = T³/3`.
* `integratedMean_eq`: for continuous `θ`, `∫₀ᵀ (r₀ + ∫₀ˢ θ) ds = r₀·T + ∫₀ᵀ θ(s)(T − s) ds`.
* `bondPrice_eq`: `𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²T³/6)`.
* `bondPrice_affine`: the affine form `P(0, T) = A(T)·exp(−T·r₀)`, with `B(T) = T`.
* `bondA_const`, `bondPrice_zero_drift`: the constant-drift coefficient
  `A(T) = exp(−θ·T²/2 + σ²T³/6)`, and at zero drift the price is the driftless price
  `brownianBondPrice_eq` of `Models/Rates/VasicekZeroMeanReversionLimit.lean`.
* `tendsto_vasicekBondPrice_hoLee`: the Vasicek closed form at long-run level `θ/κ` tends to the
  constant-drift Ho–Lee price as `κ → 0⁺` — Ho–Lee is the vanishing-mean-reversion limit at the
  level rescaling that lets the drift survive.

## References

* [T. Ho and S.-B. Lee, *Term structure movements and pricing interest rate contingent
  claims*][HoLee1986]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.3.1

## Tags

Ho–Lee model, affine term structure, zero-coupon bond price, integrated short rate,
Wiener integral, Gaussian Laplace transform, MSC 91G30, MSC 60H05, JEL E43
-/

@[expose] public section

namespace MathFin.HoLee

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The integrated kernel -/

/-- The **integrated Ho–Lee kernel** `g(u) = T − u = ∫_u^T 1 ds`, the deterministic integrand
whose Wiener integral is the diffusion part of the integrated short rate. -/
noncomputable def integratedKernel (T : ℝ) : ℝ → ℝ :=
  fun u ↦ T - u

/-- The integrated kernel is in `L²((0, T])`: on the support it lies in `[0, T]`. -/
lemma integratedKernel_memLp (T : ℝ≥0) :
    MemLp (integratedKernel T) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  refine (memLp_top_of_bound (by unfold integratedKernel; fun_prop) (T : ℝ) ?_).mono_exponent
    le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro s hs
  rw [integratedKernel, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
  linarith [hs.1]

/-- The integrated kernel as an element of `L²((0, T])`. -/
noncomputable def integratedKernelLp (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (integratedKernel_memLp T).toLp _

/-- The variance integral: `∫₀ᵀ (T − u)² du = T³/3`. -/
lemma integral_integratedKernel_sq (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (integratedKernel (T : ℝ) u) ^ 2 ∂volume
      = (T : ℝ) ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le T.coe_nonneg]
  simp only [integratedKernel]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ 2) (T : ℝ)]
  simp [integral_pow]
  norm_num

/-- `∫₀ᵀ g² = T³/3` for the `L²` representative of the kernel (a.e. equal to the honest kernel). -/
lemma integratedKernelLp_integral_sq (T : ℝ≥0) :
    (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (integratedKernelLp T u) ^ 2 ∂volume)
      = (T : ℝ) ^ 3 / 3 := by
  rw [← integral_integratedKernel_sq T]
  refine integral_congr_ae ?_
  filter_upwards [(integratedKernel_memLp T).coeFn_toLp] with u hu
  rw [integratedKernelLp, hu]

/-! ### The deterministic mean -/

/-- The deterministic mean of the integrated Ho–Lee rate: `∫₀ᵗ α(s) ds` with
`α(s) = r₀ + ∫₀ˢ θ`, the solution of `α' = θ`, `α(0) = r₀`. For non-integrable `θ` the integrals
are junk; the statements below assume `θ` continuous. -/
noncomputable def integratedMean (θ : ℝ → ℝ) (r₀ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (r₀ + ∫ u in (0 : ℝ)..s, θ u)

/-- **Mean of the integrated Ho–Lee rate in kernel form**:
`∫₀ᵗ (r₀ + ∫₀ˢ θ) ds = r₀·t + ∫₀ᵗ θ(s)·(t − s) ds`, by integration by parts. -/
lemma integratedMean_eq {θ : ℝ → ℝ} (hθ : Continuous θ) (r₀ t : ℝ) :
    integratedMean θ r₀ t = r₀ * t + ∫ s in (0 : ℝ)..t, θ s * (t - s) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun s : ℝ ↦ ∫ u in (0 : ℝ)..s, θ u) (θ x) x := fun x ↦
    intervalIntegral.integral_hasDerivAt_right (hθ.intervalIntegrable 0 x)
      (hθ.stronglyMeasurableAtFilter _ _) hθ.continuousAt
  have hc : Continuous (fun s : ℝ ↦ ∫ u in (0 : ℝ)..s, θ u) :=
    intervalIntegral.continuous_primitive (fun a b ↦ hθ.intervalIntegrable a b) 0
  have hparts : ∫ s in (0 : ℝ)..t, (∫ u in (0 : ℝ)..s, θ u)
      = (∫ u in (0 : ℝ)..t, θ u) * t - ∫ s in (0 : ℝ)..t, θ s * s := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := t)
      (u := fun s : ℝ ↦ ∫ u in (0 : ℝ)..s, θ u) (v := fun s : ℝ ↦ s)
      (u' := θ) (v' := fun _ ↦ (1 : ℝ)) (fun x _ ↦ hd x) (fun x _ ↦ hasDerivAt_id x)
      (hθ.intervalIntegrable 0 t) (by simp)
    simpa using h
  have hsplit : ∫ s in (0 : ℝ)..t, θ s * (t - s)
      = t * (∫ u in (0 : ℝ)..t, θ u) - ∫ s in (0 : ℝ)..t, θ s * s := by
    have e : ∀ s : ℝ, θ s * (t - s) = t * θ s - θ s * s := fun s ↦ by ring
    simp_rw [e]
    have h1 : IntervalIntegrable (fun s : ℝ ↦ t * θ s) volume 0 t :=
      (continuous_const.mul hθ).intervalIntegrable 0 t
    have h2 : IntervalIntegrable (fun s : ℝ ↦ θ s * s) volume 0 t :=
      (hθ.mul continuous_id).intervalIntegrable 0 t
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  unfold integratedMean
  rw [intervalIntegral.integral_add (by simp) (hc.intervalIntegrable 0 t), hparts, hsplit]
  simp
  ring

/-! ### The integrated short rate and the bond price -/

/-- The **integrated Ho–Lee short rate** in its Wiener representation:
`∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ (T − u) dB_u`. -/
noncomputable def bondRate (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (σ r₀ : ℝ) (T : ℝ≥0)
    (ω : Ω) : ℝ :=
  integratedMean θ r₀ (T : ℝ) + σ * (wienerIntegralLp B hB T (integratedKernelLp T) ω)

/-- **The Ho–Lee bond price** as the exponential-Gaussian moment:
`P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²·T³/6)`. It is the instance `m = M(T)`, `c = σ`,
`f = g` of `integral_exp_neg_add_mul_wienerIntegralLp`, with `∫₀ᵀ g² = T³/3`. -/
theorem bondPrice_eq (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (σ r₀ : ℝ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(bondRate hB θ σ r₀ T ω)) ∂μ
      = Real.exp (-(integratedMean θ r₀ (T : ℝ)) + σ ^ 2 * ((T : ℝ) ^ 3 / 3) / 2) :=
  (integral_exp_neg_add_mul_wienerIntegralLp hB T (integratedMean θ r₀ (T : ℝ)) σ
    (integratedKernelLp T)).trans <| by rw [integratedKernelLp_integral_sq T]

/-- The Ho–Lee affine coefficient `A(T) = exp(−∫₀ᵀ θ(s)·(T − s) ds + σ²·T³/6)`: the
`θ`-forcing integral and half the variance `σ²T³/3`. -/
noncomputable def bondA (θ : ℝ → ℝ) (σ t : ℝ) : ℝ :=
  Real.exp (-(∫ s in (0 : ℝ)..t, θ s * (t - s)) + σ ^ 2 * t ^ 3 / 6)

/-- **The Ho–Lee affine term structure**: `P(0, T) = A(T)·exp(−B(T)·r₀)` with the linear
loading `B(T) = T`, and `A` independent of `r₀`. -/
theorem bondPrice_affine (hB : IsPreBrownianReal B μ) {θ : ℝ → ℝ} (hθ : Continuous θ)
    (σ r₀ : ℝ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(bondRate hB θ σ r₀ T ω)) ∂μ
      = bondA θ σ (T : ℝ) * Real.exp (-((T : ℝ) * r₀)) := by
  rw [bondPrice_eq hB θ σ r₀ T, bondA, integratedMean_eq hθ r₀ (T : ℝ), ← Real.exp_add]
  congr 1
  ring

/-! ### The constant drift, the zero-drift price, and the vanishing-mean-reversion bridge -/

/-- The drift loading of a constant Ho–Lee drift: `∫₀ᵀ θ·(T − s) ds = θ·T²/2`, by the
reflection substitution `s ↦ T − s` and the elementary `∫ x = (b² − a²)/2`. -/
lemma integral_const_driftLoading (θ T : ℝ) :
    ∫ s in (0 : ℝ)..T, θ * (T - s) = θ * T ^ 2 / 2 := by
  open intervalIntegral in
  rw [integral_comp_sub_left (f := fun y : ℝ ↦ θ * y), intervalIntegral.integral_const_mul,
    integral_id]
  simp
  ring

/-- **Constant drift, in closed form**: the affine coefficient of the constant-drift Ho–Lee
model is `A(T) = exp(−θ·T²/2 + σ²T³/6)` — the level term `θ·T²/2` plus half the variance
`σ²T³/3`. -/
lemma bondA_const (θ σ T : ℝ) :
    bondA (fun _ ↦ θ) σ T = Real.exp (-(θ * T ^ 2 / 2) + σ ^ 2 * T ^ 3 / 6) := by
  rw [bondA, integral_const_driftLoading]

/-- **Zero drift is the driftless model.** At `θ ≡ 0` the mean reduces to `r₀·T` and the
Ho–Lee price is the driftless Gaussian price `brownianBondPrice_eq` of
`Models/Rates/VasicekZeroMeanReversionLimit.lean`, `exp(−r₀·T + σ²T³/6)`: the kernel `T − u`
and its variance are shared, and the drift never enters either. -/
theorem bondPrice_zero_drift (hB : IsPreBrownianReal B μ) (σ r₀ : ℝ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(bondRate hB (fun _ ↦ 0) σ r₀ T ω)) ∂μ
      = ∫ ω, Real.exp (-(brownianIntegratedRate hB r₀ σ T ω)) ∂μ := by
  rw [bondPrice_eq hB (fun _ ↦ 0) σ r₀ T, brownianBondPrice_eq]
  congr 1
  have hm : integratedMean (fun _ : ℝ ↦ (0 : ℝ)) r₀ (T : ℝ) = r₀ * (T : ℝ) := by
    simp [integratedMean]
    ring
  rw [hm]
  ring

/-- **Ho–Lee is the vanishing-mean-reversion limit at rescaled level.** The Vasicek closed
form `exp(−M(T) + σ²V(T)/2)` (`vasicekBondPrice_eq`, for each `κ > 0` the `μ`-expectation of
`exp(−∫r)`) at long-run level `θ/κ` — the level that makes the drift `κ·(θ/κ − r) → θ` survive
vanishing mean reversion — tends as `κ → 0⁺` to the constant-drift Ho–Lee price
`bondA (fun _ ↦ θ) σ T·exp(−T·r₀)`: the mean splits as `M = r₀·B(T) + θ·(T − B(T))/κ`, whose
second loading converges to `T²/2`. At level `0` instead, the limit is the driftless price
(`tendsto_vasicekBondPrice_brownianBondPrice`): the level, not the limit, carries the drift.
A limit of the closed forms; no convergence of the random variables is claimed. -/
theorem tendsto_vasicekBondPrice_hoLee (r₀ θ σ T : ℝ) :
    Tendsto (fun κ ↦ Real.exp (-(vasicekIntegratedMean r₀ (θ / κ) κ T)
        + σ ^ 2 * vasicekBondV κ T / 2))
      (𝓝[>] 0) (𝓝 (bondA (fun _ ↦ θ) σ T * Real.exp (-(T * r₀)))) := by
  rw [bondA_const, ← Real.exp_add]
  have hB := (tendsto_vasicekBondB_zero_meanReversion T).mono_left (nhdsGT_le_nhdsNE 0)
  have hmean := ((tendsto_const_nhds (x := r₀)).mul hB).add
    ((tendsto_const_nhds (x := θ)).mul
      (tendsto_vasicekBondB_secondOrder_zero_meanReversion T))
  have h := (hmean.neg.add
    (((tendsto_const_nhds (x := σ ^ 2)).mul
      (tendsto_vasicekBondV_zero_meanReversion T)).div_const 2)).rexp
  convert h using 3
  · simp only [vasicekIntegratedMean]
    ring
  · ring

end MathFin.HoLee
