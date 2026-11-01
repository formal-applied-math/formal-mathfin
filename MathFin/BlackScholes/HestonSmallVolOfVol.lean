/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.BlackScholes.Heston
public import MathFin.FixedIncome.Vasicek
public import MathFin.FixedIncome.AffineTermStructurePDE

/-!
# The Heston transform at vanishing vol-of-vol

The Riccati closed forms of `BlackScholes/Heston.lean` (`hestonBv`, `hestonA`) carry the
vol-of-vol `ξ` in two places that break at `ξ = 0`: the prefactor `2κθ/ξ²` of the `A`-flow,
multiplying the bracket `((γ + κ − ρξu)/2)τ − log(D(τ)/(2γ))` whose two terms each tend to
`κτ`. Each piece alone diverges like `κ²θτ/ξ²`; their difference is `O(ξ²)`. This is the
cancellation behind QuantLib's `AnalyticHestonEngine::chF` small-`σ` Taylor branch (taken
for `σ ≤ 1e-6`), which `COSHestonEngine`, `AnalyticPTDHestonEngine` and `HestonRNDCalculator`
lack. This file proves the limit those engines should reach.

At `ξ = 0` the variance follows the deterministic ODE `dv = κ(θ − v)dt`, whose solution is
`vasicekDeterministic v₀ θ κ` (`FixedIncome/Vasicek`), and the transform tends to the
Black–Scholes real moment with total variance
`W = ∫₀^τ v(s) ds = v₀B(τ) + θ(τ − B(τ))`, `B(τ) = (1 − e^{−κτ})/κ` — `vasicekIntegratedMean`
and `vasicekBondB` from `FixedIncome/VasicekBondPrice` (with `hasDerivAt_vasicekBondB` from
`FixedIncome/AffineTermStructurePDE`), reused here as plain closed forms.

The `A`-limit is proved without expanding the cancellation: for `ξ ≠ 0`,
`â(τ) = ∫₀^τ (ru + κθ·b̂(s)) ds` (FTC on `hasDerivAt_hestonA`); `b̂` is jointly continuous in
`(ξ, s)` across `ξ = 0` once `κ > 0`, so the parametric integral is continuous in `ξ`.

Results (`κ > 0`, `0 < u < 1`; limits are `ξ → 0`, `ξ ≠ 0`):

* `tendsto_hestonBv_smallVolOfVol`: `b̂(τ) → ((u² − u)/2)·B(τ)` (here a genuine
  continuity statement, `hestonBv_zero_volOfVol`).
* `hestonA_zero_volOfVol`: Lean's own value at `ξ = 0` is `ruτ` (`2κθ/0 = 0`) — **not** the
  limit; the closed form is discontinuous there, the formal shape of the missing branch.
* `tendsto_hestonA_smallVolOfVol`: `â(τ) → ruτ + θ·((u² − u)/2)·(τ − B(τ))`.
* `integral_vasicekDeterministic`: `∫₀^τ vasicekDeterministic v₀ θ κ = vasicekIntegratedMean`.
* `tendsto_hestonProfile_smallVolOfVol_blackScholes`: the transform profile tends to
  `mgf id (gaussianReal (x + r(T − t) − W/2) W) u`, the lognormal log-spot moment.

**Scope.** This is the real-moment transform `u ∈ (0, 1)` at the Riccati level, as in
`Heston.lean`. Not covered: the characteristic function at complex argument `iu` (QuantLib's
`chF`), the Fourier-inversion price, and the identification of the profile with
`E[e^{u log S_T}]` for a Heston process (`Heston.lean` does not prove it either). The
algebra is the same under `u ↦ iz`: QuantLib's `D = √((κ − iρσz)² + (z² + iz)σ²)` is
`hestonGamma` at `u = iz`.
-/

@[expose] public section

open Filter Topology ProbabilityTheory
open scoped NNReal

namespace MathFin

/-! ### The `ξ = 0` variance path: integrated deterministic variance -/

/-- **The limit's variance is the integrated deterministic variance path.** At `ξ = 0` the
variance obeys the ODE `dv = κ(θ − v)dt`, solved by `vasicekDeterministic v₀ θ κ`
(`vasicekDeterministic_solves_ODE`), and
`∫₀^τ v(s) ds = v₀·B(τ) + θ·(τ − B(τ)) = vasicekIntegratedMean v₀ θ κ τ`. -/
theorem integral_vasicekDeterministic {κ : ℝ} (hκ : κ ≠ 0) (v₀ θ τ : ℝ) :
    ∫ s in (0 : ℝ)..τ, vasicekDeterministic v₀ θ κ s = vasicekIntegratedMean v₀ θ κ τ := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) τ,
      HasDerivAt (vasicekIntegratedMean v₀ θ κ) (vasicekDeterministic v₀ θ κ s) s := by
    intro s _
    have h : HasDerivAt (fun s => v₀ * vasicekBondB κ s + θ * (s - vasicekBondB κ s))
        (v₀ * (1 - κ * vasicekBondB κ s) + θ * (1 - (1 - κ * vasicekBondB κ s))) s :=
      ((hasDerivAt_vasicekBondB hκ s).const_mul v₀).fun_add
        (((hasDerivAt_id' s).fun_sub (hasDerivAt_vasicekBondB hκ s)).const_mul θ)
    convert h using 1
    · rfl
    · simp only [vasicekDeterministic, vasicekBondB]
      field_simp
      ring
  have hcont : Continuous (vasicekDeterministic v₀ θ κ) := by
    unfold vasicekDeterministic
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp [vasicekIntegratedMean, vasicekBondB]

/-- The integrated deterministic variance is nonnegative (`κ > 0`, `v₀, θ, τ ≥ 0`):
`0 ≤ B(τ) ≤ τ`. -/
theorem vasicekIntegratedMean_nonneg {κ v₀ θ τ : ℝ} (hκ : 0 < κ) (hv : 0 ≤ v₀) (hθ : 0 ≤ θ)
    (hτ : 0 ≤ τ) : 0 ≤ vasicekIntegratedMean v₀ θ κ τ := by
  have hB0 : 0 ≤ vasicekBondB κ τ := by
    rw [vasicekBondB]
    refine div_nonneg ?_ hκ.le
    have : Real.exp (-(κ * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hBτ : vasicekBondB κ τ ≤ τ := by
    rw [vasicekBondB, div_le_iff₀ hκ]
    have := Real.add_one_le_exp (-(κ * τ))
    nlinarith
  rw [vasicekIntegratedMean]
  have := mul_nonneg hv hB0
  have := mul_nonneg hθ (sub_nonneg.mpr hBτ)
  linarith

end MathFin

namespace MathFin.Heston

/-- At zero vol-of-vol the Heston root is the mean-reversion speed: `γ = √(κ²) = κ`. -/
theorem hestonGamma_zero_volOfVol {κ : ℝ} (hκ : 0 < κ) (ρ u : ℝ) :
    hestonGamma κ 0 ρ u = κ := by
  simp only [hestonGamma, mul_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
  exact Real.sqrt_sq hκ.le

/-- The shared Möbius denominator is positive for **every** vol-of-vol `ξ`, the degenerate
`ξ = 0` included, once `κ > 0`: at `ξ = 0` it is `2κe^{κτ}`, and for `ξ ≠ 0` this is
`hestonBvDenom_pos`. -/
theorem hestonBvDenom_pos_of_kappa_pos {κ u : ℝ} (hκ : 0 < κ) (hu1 : 0 < u) (hu2 : u < 1)
    (ξ ρ τ : ℝ) : 0 < hestonBvDenom κ ξ ρ u τ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [hestonBvDenom, hestonGamma_zero_volOfVol hκ]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, sub_self]
    have := Real.exp_pos (κ * τ)
    positivity
  · exact hestonBvDenom_pos κ ξ ρ u τ hξ hu1 hu2

/-- **The `Bv`-flow is jointly continuous in (vol-of-vol, maturity)**, across `ξ = 0`:
square root, exponential and a quotient whose denominator never vanishes. -/
theorem continuous_hestonBv_volOfVol {κ u : ℝ} (hκ : 0 < κ) (hu1 : 0 < u) (hu2 : u < 1)
    (ρ : ℝ) : Continuous (fun p : ℝ × ℝ => hestonBv κ p.1 ρ u p.2) := by
  simp only [hestonBv]
  refine Continuous.div ?_ ?_ fun p => (hestonBvDenom_pos_of_kappa_pos hκ hu1 hu2 p.1 ρ p.2).ne'
  · simp only [hestonGamma]
    fun_prop
  · simp only [hestonBvDenom, hestonGamma]
    fun_prop

/-- The `Bv`-flow at zero vol-of-vol: `b̂(τ) = ((u² − u)/2)·B(τ)` with
`B(τ) = (1 − e^{−κτ})/κ` (`vasicekBondB`). -/
theorem hestonBv_zero_volOfVol {κ : ℝ} (hκ : 0 < κ) (ρ u τ : ℝ) :
    hestonBv κ 0 ρ u τ = (u ^ 2 - u) / 2 * vasicekBondB κ τ := by
  rw [hestonBv, hestonBvDenom, hestonGamma_zero_volOfVol hκ, vasicekBondB, Real.exp_neg]
  simp only [mul_zero, zero_mul, sub_zero, add_zero, sub_self]
  have he : Real.exp (κ * τ) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- **Small vol-of-vol limit of the `Bv`-flow**: `b̂ → ((u² − u)/2)·(1 − e^{−κτ})/κ` as
`ξ → 0`. No catastrophic cancellation here — `b̂` is continuous in `ξ` at `0`. -/
theorem tendsto_hestonBv_smallVolOfVol {κ u : ℝ} (hκ : 0 < κ) (hu1 : 0 < u) (hu2 : u < 1)
    (ρ τ : ℝ) :
    Tendsto (fun ξ => hestonBv κ ξ ρ u τ) (𝓝 0) (𝓝 ((u ^ 2 - u) / 2 * vasicekBondB κ τ)) := by
  rw [← hestonBv_zero_volOfVol hκ ρ u τ]
  exact ((continuous_hestonBv_volOfVol hκ hu1 hu2 ρ).comp
    (Continuous.prodMk_left τ)).tendsto 0

/-! ### The `A`-flow: the `κθ/ξ²` prefactor and the integral route around it -/

/-- **Lean's literal value of the `A`-flow at `ξ = 0` drops the `κθ` term**: the prefactor
`2κθ/ξ²` is `2κθ/0 = 0` under Lean's division convention, leaving only `ruτ`. This is *not*
the `ξ → 0` limit (`tendsto_hestonA_smallVolOfVol`): the closed form `hestonA` is
discontinuous at `ξ = 0`, which is the formal shape of the missing small-`ξ` branch. -/
theorem hestonA_zero_volOfVol (r κ θ ρ u τ : ℝ) : hestonA r κ θ 0 ρ u τ = r * u * τ := by
  simp [hestonA]

/-- **The `A`-flow as an integral of the `Bv`-flow** (`ξ ≠ 0`):
`â(τ) = ∫₀^τ (ru + κθ·b̂(s)) ds` — the fundamental theorem of calculus on
`hasDerivAt_hestonA` with `â(0) = 0`. This form carries no `1/ξ²` and is the route to the
`ξ → 0` limit. -/
theorem hestonA_eq_integral {κ ξ u : ℝ} (r θ ρ : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1)
    (τ : ℝ) :
    hestonA r κ θ ξ ρ u τ = ∫ s in (0 : ℝ)..τ, (r * u + κ * θ * hestonBv κ ξ ρ u s) := by
  have hcont : Continuous (fun s => r * u + κ * θ * hestonBv κ ξ ρ u s) :=
    continuous_const.add (continuous_const.mul (continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_hestonBv κ ξ ρ u s hξ hu1 hu2).continuousAt))
  have hγ : hestonGamma κ ξ ρ u ≠ 0 := by
    have h := hestonBvDenom_pos κ ξ ρ u 0 hξ hu1 hu2
    simp only [hestonBvDenom, mul_zero, Real.exp_zero, mul_one] at h
    intro h0
    rw [h0] at h
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_hestonA r κ θ ξ ρ u s hξ hu1 hu2) (hcont.intervalIntegrable _ _),
    hestonA_at_zero r κ θ ξ ρ u hγ, sub_zero]

/-- The integral of the limiting `A`-integrand, in closed form:
`∫₀^τ (ru + κθ·((u² − u)/2)·B(s)) ds = ruτ + θ·((u² − u)/2)·(τ − B(τ))`
(using `κ·B(s) = 1 − e^{−κs}` and `∫₀^τ e^{−κs} ds = B(τ)`). -/
theorem integral_hestonA_integrand_zero_volOfVol {κ : ℝ} (hκ : κ ≠ 0) (r θ u τ : ℝ) :
    ∫ s in (0 : ℝ)..τ, (r * u + κ * θ * ((u ^ 2 - u) / 2 * vasicekBondB κ s))
      = r * u * τ + θ * ((u ^ 2 - u) / 2) * (τ - vasicekBondB κ τ) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) τ,
      HasDerivAt (fun s => r * u * s + θ * ((u ^ 2 - u) / 2) * (s - vasicekBondB κ s))
        (r * u + κ * θ * ((u ^ 2 - u) / 2 * vasicekBondB κ s)) s := by
    intro s _
    have h : HasDerivAt (fun s => r * u * s + θ * ((u ^ 2 - u) / 2) * (s - vasicekBondB κ s))
        (r * u * 1 + θ * ((u ^ 2 - u) / 2) * (1 - (1 - κ * vasicekBondB κ s))) s :=
      ((hasDerivAt_id' s).const_mul (r * u)).fun_add
        (((hasDerivAt_id' s).fun_sub (hasDerivAt_vasicekBondB hκ s)).const_mul
          (θ * ((u ^ 2 - u) / 2)))
    convert h using 1
    ring
  have hcont : Continuous (fun s => r * u + κ * θ * ((u ^ 2 - u) / 2 * vasicekBondB κ s)) := by
    simp only [vasicekBondB]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp [vasicekBondB]

/-- **Small vol-of-vol limit of the `A`-flow** (the derived-limit core). As `ξ → 0`
(`ξ ≠ 0`),

`â(τ) → ruτ + θ·((u² − u)/2)·(τ − (1 − e^{−κτ})/κ)`.

In the closed form `hestonA` the bracket `((γ + κ − ρξu)/2)τ − log(D(τ)/(2γ))` is a
difference of two terms that each tend to `κτ`, multiplied by `2κθ/ξ²` — each piece
alone diverges like `κ²θτ/ξ²`. The proof never touches that cancellation: it rewrites
`â` as `∫₀^τ (ru + κθ·b̂)` (`hestonA_eq_integral`) and passes the limit through the
integral by joint continuity of `b̂` (`continuous_hestonBv_volOfVol`). -/
theorem tendsto_hestonA_smallVolOfVol {κ u : ℝ} (hκ : 0 < κ) (hu1 : 0 < u) (hu2 : u < 1)
    (r θ ρ τ : ℝ) :
    Tendsto (fun ξ => hestonA r κ θ ξ ρ u τ) (𝓝[≠] 0)
      (𝓝 (r * u * τ + θ * ((u ^ 2 - u) / 2) * (τ - vasicekBondB κ τ))) := by
  set F : ℝ → ℝ := fun ξ => ∫ s in (0 : ℝ)..τ, (r * u + κ * θ * hestonBv κ ξ ρ u s) with hFdef
  have hF : Continuous F := by
    have hc : Continuous (fun p : ℝ × ℝ => r * u + κ * θ * hestonBv κ p.1 ρ u p.2) :=
      continuous_const.add (continuous_const.mul (continuous_hestonBv_volOfVol hκ hu1 hu2 ρ))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun ξ s => r * u + κ * θ * hestonBv κ ξ ρ u s) hc 0 τ
  have hF0 : F 0 = r * u * τ + θ * ((u ^ 2 - u) / 2) * (τ - vasicekBondB κ τ) := by
    simp only [hFdef, hestonBv_zero_volOfVol hκ]
    exact integral_hestonA_integrand_zero_volOfVol hκ.ne' r θ u τ
  have hlim : Tendsto F (𝓝[≠] 0) (𝓝 (F 0)) := (hF.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [hF0] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  exact (hestonA_eq_integral r θ ρ hξ hu1 hu2 τ).symm

/-! ### The transform limit and the Black–Scholes identification -/

/-- **Small vol-of-vol limit of the Heston transform profile.** As `ξ → 0` (`ξ ≠ 0`),

`Φ_ξ(t, x, v) = e^{â(T−t) + u·x + b̂(T−t)·v} → exp(ux + ru(T − t) + ((u² − u)/2)·W)`,

`W = vasicekIntegratedMean v θ κ (T − t) = ∫₀^{T−t} (θ + (v − θ)e^{−κs}) ds` — the integrated
deterministic variance (`integral_vasicekDeterministic`). -/
theorem tendsto_hestonProfile_smallVolOfVol {κ u : ℝ} (hκ : 0 < κ) (hu1 : 0 < u) (hu2 : u < 1)
    (r θ ρ T t x v : ℝ) :
    Tendsto (fun ξ => hestonProfile u (fun w => hestonA r κ θ ξ ρ u (T - w))
        (fun w => hestonBv κ ξ ρ u (T - w)) t x v) (𝓝[≠] 0)
      (𝓝 (Real.exp (u * x + r * u * (T - t)
        + (u ^ 2 - u) / 2 * vasicekIntegratedMean v θ κ (T - t)))) := by
  have hA := tendsto_hestonA_smallVolOfVol hκ hu1 hu2 r θ ρ (T - t)
  have hB := (tendsto_hestonBv_smallVolOfVol hκ hu1 hu2 ρ (T - t)).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [hestonProfile]
  refine (Real.continuous_exp.tendsto _).comp ?_
  convert (hA.add_const (u * x)).add (hB.mul_const v) using 2
  rw [vasicekIntegratedMean]
  ring

/-- The Black–Scholes (lognormal) real moment: if `log S_T ~ N(x + rτ − W/2, W)` then
`E[e^{u log S_T}] = exp(ux + ruτ + ((u² − u)/2)·W)`. -/
theorem mgf_gaussianReal_logSpot (x r τ u : ℝ) (W : ℝ≥0) :
    mgf id (gaussianReal (x + r * τ - W / 2) W) u
      = Real.exp (u * x + r * u * τ + (u ^ 2 - u) / 2 * W) := by
  simp only [mgf_id_gaussianReal]
  congr 1
  ring

/-- **Headline: the Heston transform tends to the Black–Scholes moment with the integrated
variance.** For `κ > 0`, `0 < u < 1`, `v, θ ≥ 0`, `t ≤ T`, as the vol-of-vol `ξ → 0`
(`ξ ≠ 0`) the Heston transform profile (`hestonProfile` built from the Riccati closed forms
`hestonA`, `hestonBv`) converges to `E[e^{u·X}]` for the Gaussian
`X ~ N(x + r(T − t) − W/2, W)` — the log-spot law of Black–Scholes with total variance
`W = ∫₀^{T−t} v(s) ds`, `v(s) = θ + (v − θ)e^{−κs}` the `ξ = 0` variance path. -/
theorem tendsto_hestonProfile_smallVolOfVol_blackScholes {κ u : ℝ} (hκ : 0 < κ) (hu1 : 0 < u)
    (hu2 : u < 1) (r θ ρ T t x v : ℝ) (hv : 0 ≤ v) (hθ : 0 ≤ θ) (htT : t ≤ T) :
    Tendsto (fun ξ => hestonProfile u (fun w => hestonA r κ θ ξ ρ u (T - w))
        (fun w => hestonBv κ ξ ρ u (T - w)) t x v) (𝓝[≠] 0)
      (𝓝 (mgf id (gaussianReal (x + r * (T - t) - (vasicekIntegratedMean v θ κ (T - t)).toNNReal / 2)
        (vasicekIntegratedMean v θ κ (T - t)).toNNReal) u)) := by
  rw [mgf_gaussianReal_logSpot, Real.coe_toNNReal _
    (vasicekIntegratedMean_nonneg hκ hv hθ (sub_nonneg.mpr htT))]
  exact tendsto_hestonProfile_smallVolOfVol hκ hu1 hu2 r θ ρ T t x v

end MathFin.Heston
