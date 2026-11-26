/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Jumps.JumpDiffusionMerton
public import MathFin.Models.Jumps.JumpDiffusionBrownian
public import MathFin.Probability.Laws.Esscher
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The Esscher transform of a jump-diffusion

The Esscher transform with parameter `θ` reweights a law by `e^{θy}` and renormalizes it
(`Probability/Laws/Esscher.lean`, on Mathlib's `Measure.tilted`). Here it acts on the log-return law
over `τ` of a jump-diffusion with drift `b`, volatility coefficient `σ`, jump rate `Λ` and jump
law `ν` (`jumpDiffusionIncrementLaw`), whose Laplace exponent is `κ` (`jumpDiffusionExponent`).

* `jumpDiffusionIncrementLaw_tilted`: when the moment-generating function of `ν` is finite near
  `θ`, the tilted law is again a jump-diffusion log-return law. The drift becomes `b + θσ²`, `σ`
  is unchanged, the rate becomes `Λ·m(θ)` with `m(θ) = ∫ e^{θx} dν` (`jumpMoment`), and the jump
  law is tilted the same way. The proof compares moment-generating functions near `0`
  (`measure_eq_of_mgf_id_eventuallyEq`): both laws have the moment-generating function
  `u ↦ e^{(κ(u + θ) − κ(θ))τ}` there, since `κ(u + θ) − κ(θ)` is the Laplace exponent of the tilted
  characteristics (`jumpDiffusionExponent_tilted`). Jump laws whose moment-generating function is
  finite only on an interval, such as Kou's double-exponential jumps, are covered.
* `smul_tilted_eq_withDensity`: the transform multiplies the Lévy measure `Λν` by `e^{θx}`, the
  unnormalized transform of the Esscher layer (`ofReal_integral_exp_smul_tilted`).
* `compensated_tilted_iff`: the tilted characteristics are at their compensated drift exactly
  when `κ(θ + 1) − κ(θ) = r`, the Esscher condition: the criterion `κ(1) = r`
  (`compensated_iff_exponent_one`) for the tilted Laplace exponent `u ↦ κ(u + θ) − κ(θ)`.
* `existsUnique_esscher`: with a Gaussian part (`σ ≠ 0`) and every exponential moment of `ν`, the
  Esscher condition has exactly one solution, the Esscher parameter.
* `existsUnique_esscher_of_steep`: with a Gaussian part and a positive jump rate, a jump law with
  exponential moments on an interval `(α, β)`, `1 < β − α`, that blow up at both ends (Kou's
  double-exponential jumps) has exactly one Esscher parameter in `(α, β − 1)`.
* `integral_call_tilted_eq_jumpDiffusionCallPrice`: the call integrated against the tilted law is
  the call price function of the tilted characteristics, so results about price functions apply.
* `integral_call_tilted_eq_merton`: at an Esscher parameter it is Merton's formula for the tilted
  jump law (`jumpDiffusionCallPrice_eq_merton`).
* `integral_call_tilted_eq_mertonCallPrice`: tilting keeps Merton's lognormal jumps lognormal
  (`mertonJump_tilted`), so in Merton's model the same integral is Merton's 1976 series with a
  shifted jump mean.
* `integral_call_tilted_zero_eq_bsV`: with no jumps the log-return law is Gaussian, and its
  Esscher transform is the Gaussian tilt that also gives the static Girsanov theorem
  (`gaussianReal_tilted_const_mul`, behind `gaussianReal_withDensity_esscher`). The Esscher
  parameter is `θ = (r − b − σ²/2)/σ²` (`jumpDiffusionExponent_zero_esscher`), and the price is the
  Black–Scholes formula.

The statements are about the law at one date, not about the process under a changed measure. The
Esscher law is equivalent to the physical law (Mathlib's `tilted_absolutelyContinuous` and
`absolutelyContinuous_tilted`), but with nontrivial jumps it is not the only compensated law
equivalent to it: for `σ ≠ 0`, when the physical drift is not already compensated, the Merton
measure's law is another, and the two price some call differently (`exists_call_esscher_ne_merton`,
under its moment conditions). Without a Gaussian part (`σ = 0`) the existence of an Esscher
parameter is not proved.

## Main definitions

* `jumpMoment`: the exponential moment `m(θ) = ∫ e^{θx} dν` of a jump law, as a nonnegative
  real (`0` where the integral is infinite).

## Main results

* `jumpDiffusionIncrementLaw_tilted`: for `θ` in the interior of the exponentially integrable
  set of `ν`, the Esscher transform of the log-return law is the log-return law with drift
  `b + θσ²`, rate `Λ m(θ)` and jump law `ν.tilted (θ * ·)`.
* `smul_tilted_eq_withDensity`: tilting multiplies the Lévy measure by `e^{θx}`.
* `compensated_tilted_iff`: the tilted characteristics are at their compensated drift iff
  `κ(θ + 1) − κ(θ) = r`, with `κ` the Laplace exponent.
* `existsUnique_esscher`: for `σ ≠ 0` and a jump law with every exponential moment, exactly one
  `θ` satisfies `κ(1 + θ) − κ(θ) = r`.
* `existsUnique_esscher_of_steep`: for `σ ≠ 0`, `Λ > 0` and a jump law whose exponential moments
  are finite on `(α, β)`, `1 < β − α`, and tend to `+∞` at both ends, exactly one
  `θ ∈ (α, β − 1)` satisfies `κ(1 + θ) − κ(θ) = r`.
* `existsUnique_mem_Ioo_eq_of_strictMonoOn`: a continuous strictly increasing real function on
  `(a, b)` tending to `-∞` at `a` and `+∞` at `b` takes each value exactly once there.
* `integral_call_tilted_eq_jumpDiffusionCallPrice`: the discounted call integrated against the
  tilted law is the call price function of the tilted characteristics.
* `integral_call_tilted_eq_merton`: at an Esscher parameter, it is the Poisson mixture of
  Black–Scholes prices over jumps of law `ν.tilted (θ * ·)`.
* `integral_call_tilted_eq_mertonCallPrice`: with Merton's log-jumps `N(log(1 + k) − δ²/2, δ²)`
  and `σ > 0`, at an Esscher parameter it is `mertonCallPrice` with jump mean
  `(1 + k) e^{θδ²} − 1` and expected jump count `Λ m(θ) τ` (`mertonJump_tilted`).
* `jumpDiffusionExponent_zero_esscher`, `integral_call_tilted_zero_eq_bsV`: without jumps
  `θ = (r − b − σ²/2)/σ²` solves the Esscher equation, and the call integrated against the tilted
  law is the Black–Scholes price.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [Gerber and Shiu, *Option pricing by Esscher transforms*][GerberShiu1994]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

Esscher transform, exponential tilting, jump-diffusion, equivalent martingale measure,
Laplace exponent, MSC 91G20, MSC 60G51, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The exponential moment `m(θ) = ∫ e^{θx} dν` of a jump law, as a nonnegative real (the Bochner
integral, so `0` where the moment is infinite). -/
noncomputable def jumpMoment (ν : Measure ℝ) (θ : ℝ) : ℝ≥0 :=
  .mk (∫ x, rexp (θ * x) ∂ν) (integral_nonneg fun _ ↦ (Real.exp_pos _).le)

@[simp] lemma coe_jumpMoment (ν : Measure ℝ) (θ : ℝ) :
    (jumpMoment ν θ : ℝ) = ∫ x, rexp (θ * x) ∂ν :=
  rfl

/-- **The Laplace exponent of the tilted characteristics.** For the characteristics
`(b + θσ², σ, Λ·m(θ), ν.tilted (θ * ·))`, which `jumpDiffusionIncrementLaw_tilted` shows are those
of the tilted law, `jumpDiffusionExponent` at every `u` is `κ(u + θ) − κ(θ)`. It is their Laplace
exponent at `u` where `∫ e^{(u + θ)x} dν < ∞`. -/
lemma jumpDiffusionExponent_tilted (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} [NeZero ν] {θ : ℝ}
    (hθ : Integrable (fun x ↦ rexp (θ * x)) ν) (u : ℝ) :
    jumpDiffusionExponent (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·)) u
      = jumpDiffusionExponent b σ Λ ν (u + θ) - jumpDiffusionExponent b σ Λ ν θ := by
  have hm : (∫ x, rexp (θ * x) ∂ν) ≠ 0 := (integral_exp_pos hθ).ne'
  simp only [jumpDiffusionExponent, integral_exp_mul_tilted_const_mul, NNReal.coe_mul,
    coe_jumpMoment]
  field_simp
  ring

open Filter Topology in
/-- **The Esscher transform of a jump-diffusion log-return law.** When the moment-generating
function of the jump law is finite near `θ` (`θ` in the interior of `integrableExpSet id ν`),
tilting the log-return law over `τ` by `e^{θy}` gives the log-return law with drift `b + θσ²`, the
same volatility coefficient, the rate `Λ·m(θ)` and the tilted jump law `ν.tilted (θ * ·)`. Both
laws have the moment-generating function `u ↦ e^{(κ(u + θ) − κ(θ))τ}` near `0`, which determines
them (`measure_eq_of_mgf_id_eventuallyEq`). -/
theorem jumpDiffusionIncrementLaw_tilted (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {θ : ℝ} (hθ : θ ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    (jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·)
      = jumpDiffusionIncrementLaw (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·)) τ := by
  have hθν : Integrable (fun x ↦ rexp (θ * x)) ν := interior_subset (s := integrableExpSet id ν) hθ
  have : IsProbabilityMeasure (ν.tilted (θ * ·)) := isProbabilityMeasure_tilted hθν
  -- near `0`, the jump law has the exponential moments of the orders `u + θ`
  have hU := eventually_integrable_exp_add_mul hθ
  refine Eq.symm (measure_eq_of_mgf_id_eventuallyEq
    (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw _ _ _
      (zero_mem_interior_integrableExpSet_tilted hθ) τ) (hU.mono fun u hu ↦ ?_))
  rw [mgf_id_jumpDiffusionIncrementLaw _ _ _ (integrable_exp_mul_tilted_const_mul hθν hu),
    jumpDiffusionExponent_tilted b σ Λ hθν u, mgf_id_tilted_const_mul,
    mgf_id_jumpDiffusionIncrementLaw b σ Λ hu, mgf_id_jumpDiffusionIncrementLaw b σ Λ hθν,
    ← Real.exp_sub, sub_mul]

/-- **The Esscher transform multiplies the Lévy measure by `e^{θx}`**: the tilted
characteristics have the Lévy measure `Λm(θ)·ν_θ = e^{θx}·Λν`, where `m(θ) = ∫ e^{θx} dν`. It is
`Λ` times the unnormalized transform `m(θ)·ν_θ = e^{θx}·ν` (`ofReal_integral_exp_smul_tilted`). -/
lemma smul_tilted_eq_withDensity (Λ : ℝ≥0) {ν : Measure ℝ} {θ : ℝ}
    (hθ : Integrable (fun x ↦ rexp (θ * x)) ν) :
    (Λ * jumpMoment ν θ) • ν.tilted (θ * ·)
      = Λ • ν.withDensity fun x ↦ ENNReal.ofReal (rexp (θ * x)) := by
  rw [mul_smul, ENNReal.smul_def (jumpMoment ν θ), ← ENNReal.ofReal_coe_nnreal, coe_jumpMoment,
    ofReal_integral_exp_smul_tilted hθ]

/-- **The Esscher condition.** The tilted characteristics are at their compensated drift,
`b + θσ² = r − σ²/2 − Λm(θ)(∫ eˣ d(ν tilted) − 1)`, exactly when `κ(θ + 1) − κ(θ) = r`: the
criterion `κ(1) = r` (`compensated_iff_exponent_one`) for their Laplace exponent
`u ↦ κ(u + θ) − κ(θ)` (`jumpDiffusionExponent_tilted`). -/
lemma compensated_tilted_iff (b σ r : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} [NeZero ν] {θ : ℝ}
    (hθ : Integrable (fun x ↦ rexp (θ * x)) ν) :
    b + θ * σ ^ 2 = r - σ ^ 2 / 2
        - (Λ * jumpMoment ν θ : ℝ≥0) * (∫ x, rexp x ∂(ν.tilted (θ * ·)) - 1)
      ↔ jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r := by
  rw [compensated_iff_exponent_one, jumpDiffusionExponent_tilted b σ Λ hθ 1]

/-! ### The Esscher parameter -/

/-- **The Esscher map written out**: `κ(1 + θ) − κ(θ) = b + σ²/2 + σ²θ + Λ(m(1 + θ) − m(θ))`, with
`m(θ) = ∫ e^{θx} dν`. -/
lemma jumpDiffusionExponent_one_add_sub (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (θ : ℝ) :
    jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ
      = b + σ ^ 2 / 2 + σ ^ 2 * θ + Λ * (∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν) := by
  simp only [jumpDiffusionExponent]
  ring

/-- The jump part of the Esscher map, `θ ↦ ∫ e^{(1 + θ)x} dν − ∫ e^{θx} dν = ∫ e^{θx}(eˣ − 1) dν`,
is nondecreasing where both moments are finite: for `θ ≤ θ'` the difference of integrands
`(e^{θ'x} − e^{θx})(eˣ − 1)` is nonnegative, both factors having the sign of `x`. -/
lemma monotoneOn_integral_exp_one_add_sub {ν : Measure ℝ} :
    MonotoneOn (fun θ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν)
      {θ | Integrable (fun x ↦ rexp (θ * x)) ν ∧ Integrable (fun x ↦ rexp ((1 + θ) * x)) ν} := by
  rintro θ ⟨hθ0, hθ1⟩ θ' ⟨hθ'0, hθ'1⟩ hθ
  change ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν
      ≤ ∫ x, rexp ((1 + θ') * x) ∂ν - ∫ x, rexp (θ' * x) ∂ν
  rw [← integral_sub hθ1 hθ0, ← integral_sub hθ'1 hθ'0]
  refine integral_mono (hθ1.sub hθ0) (hθ'1.sub hθ'0) fun x ↦ ?_
  change rexp ((1 + θ) * x) - rexp (θ * x) ≤ rexp ((1 + θ') * x) - rexp (θ' * x)
  have key : 0 ≤ (rexp (θ' * x) - rexp (θ * x)) * (rexp x - 1) := by
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hθ hx)))
        (sub_nonneg.2 (Real.one_le_exp hx))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hθ hx)))
        (sub_nonpos.2 (Real.exp_le_one_iff.2 hx))
  rw [add_mul, add_mul, one_mul, Real.exp_add, Real.exp_add]
  linarith

/-- With every exponential moment, the jump part of the Esscher map is nondecreasing
(`monotoneOn_integral_exp_one_add_sub`). -/
lemma monotone_integral_exp_one_add_sub {ν : Measure ℝ}
    (hν : ∀ u, Integrable (fun x ↦ rexp (u * x)) ν) :
    Monotone fun θ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν :=
  fun _ _ h ↦ monotoneOn_integral_exp_one_add_sub ⟨hν _, hν _⟩ ⟨hν _, hν _⟩ h

open Filter Topology Set in
/-- A continuous strictly increasing real function on `(a, b)` that tends to `-∞` at `a` and to
`+∞` at `b` takes every value exactly once on `(a, b)`: the intermediate value theorem
(`ContinuousOn.surjOn_of_tendsto`) and injectivity. -/
theorem existsUnique_mem_Ioo_eq_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Ioo a b)) (hmono : StrictMonoOn f (Ioo a b))
    (hbot : Tendsto f (𝓝[>] a) atBot) (htop : Tendsto f (𝓝[<] b) atTop) (r : ℝ) :
    ∃! x, x ∈ Ioo a b ∧ f x = r := by
  obtain ⟨x, hx, hxr⟩ := hf.surjOn_of_tendsto (nonempty_Ioo.2 hab)
    ((tendsto_comp_coe_Ioo_atBot hab).2 hbot) ((tendsto_comp_coe_Ioo_atTop hab).2 htop)
    (mem_univ r)
  exact ⟨x, ⟨hx, hxr⟩, fun y ⟨hy, hyr⟩ ↦ hmono.injOn hy hx (hyr.trans hxr.symm)⟩

open Filter in
/-- **The Esscher parameter exists and is unique** when there is a Gaussian part, `σ ≠ 0`, and the
jump law has every exponential moment: exactly one `θ` satisfies `κ(θ + 1) − κ(θ) = r`. The map
`θ ↦ κ(1 + θ) − κ(θ)` is the strictly increasing line `b + σ²/2 + σ²θ` plus `Λ` times a
nondecreasing jump part (`monotone_integral_exp_one_add_sub`). It is continuous
(`continuous_jumpDiffusionExponent`) and unbounded in both directions, so it takes the value `r`
(`Continuous.surjective`) exactly once. -/
theorem existsUnique_esscher (b σ r : ℝ) (hσ : σ ≠ 0) (Λ : ℝ≥0) {ν : Measure ℝ}
    (hν : ∀ u, Integrable (fun x ↦ rexp (u * x)) ν) :
    ∃! θ, jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r := by
  have hσ2 : 0 < σ ^ 2 := sq_pos_iff.2 hσ
  obtain ⟨g, hg, hF⟩ : ∃ g : ℝ → ℝ, Monotone g ∧ ∀ θ, jumpDiffusionExponent b σ Λ ν (1 + θ)
      - jumpDiffusionExponent b σ Λ ν θ = b + σ ^ 2 / 2 + σ ^ 2 * θ + Λ * g θ :=
    ⟨_, monotone_integral_exp_one_add_sub hν, jumpDiffusionExponent_one_add_sub b σ Λ ν⟩
  have hκ := continuous_jumpDiffusionExponent b σ Λ hν
  have hκ1 : Continuous fun θ ↦ jumpDiffusionExponent b σ Λ ν (1 + θ) :=
    hκ.comp (continuous_const.add continuous_id)
  have hcont : Continuous fun θ ↦ b + σ ^ 2 / 2 + σ ^ 2 * θ + Λ * g θ := (hκ1.sub hκ).congr hF
  have hmono : StrictMono fun θ ↦ b + σ ^ 2 / 2 + σ ^ 2 * θ + Λ * g θ :=
    ((strictMono_mul_left_of_pos hσ2).const_add _).add_monotone (hg.const_mul Λ.coe_nonneg)
  have htop : Tendsto (fun θ ↦ b + σ ^ 2 / 2 + σ ^ 2 * θ + Λ * g θ) atTop atTop :=
    tendsto_atTop_add_right_of_le' _ (Λ * g 0)
      (tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hσ2))
      ((eventually_ge_atTop 0).mono fun θ hθ ↦ mul_le_mul_of_nonneg_left (hg hθ) Λ.coe_nonneg)
  have hbot : Tendsto (fun θ ↦ b + σ ^ 2 / 2 + σ ^ 2 * θ + Λ * g θ) atBot atBot :=
    tendsto_atBot_add_right_of_ge' _ (Λ * g 0)
      (tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atBot hσ2))
      ((eventually_le_atBot 0).mono fun θ hθ ↦ mul_le_mul_of_nonneg_left (hg hθ) Λ.coe_nonneg)
  obtain ⟨θ, hθ⟩ := hcont.surjective htop hbot r
  exact ⟨θ, (hF θ).trans hθ, fun θ' h ↦ hmono.injective (((hF θ').symm.trans h).trans hθ.symm)⟩

open Filter Topology Set in
/-- **The Esscher parameter for jump laws with exponential moments on an interval.** With a
Gaussian part, `σ ≠ 0`, and a positive jump rate, suppose `ν` has the exponential moments
`∫ e^{ux} dν < ∞` for `u ∈ (α, β)`, with `1 < β − α`, and that the moment map is steep:
it tends to `+∞` at both ends of the interval. This covers Kou's double-exponential jumps.
Then exactly one `θ ∈ (α, β − 1)` satisfies `κ(1 + θ) − κ(θ) = r`. On `(α, β − 1)` both
`θ` and `1 + θ` lie in `(α, β)`, where the moment map is continuous (Mathlib's
`continuousOn_mgf`); the Esscher map is the strictly increasing line `b + σ²/2 + σ²θ` plus `Λ`
times a nondecreasing jump part (`monotoneOn_integral_exp_one_add_sub`). At `β − 1` the moment
of order `1 + θ` blows up while that of order `θ` stays bounded, so the map tends to `+∞`; at
`α` the moment of order `θ` blows up while that of order `1 + θ` stays bounded, so it tends to
`−∞`. The intermediate value theorem
(`existsUnique_mem_Ioo_eq_of_strictMonoOn`) gives the unique parameter. Uniqueness is within
`(α, β − 1)` only, the interval where both moments are known to be finite. -/
theorem existsUnique_esscher_of_steep (b σ r : ℝ) (hσ : σ ≠ 0) {Λ : ℝ≥0} (hΛ : 0 < Λ)
    {ν : Measure ℝ} {α β : ℝ} (hαβ : 1 < β - α)
    (hI : ∀ u ∈ Ioo α β, Integrable (fun x ↦ rexp (u * x)) ν)
    (hα : Tendsto (fun u ↦ ∫ x, rexp (u * x) ∂ν) (𝓝[>] α) atTop)
    (hβ : Tendsto (fun u ↦ ∫ x, rexp (u * x) ∂ν) (𝓝[<] β) atTop) :
    ∃! θ, θ ∈ Ioo α (β - 1) ∧
      jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r := by
  have hσ2 : 0 < σ ^ 2 := sq_pos_iff.2 hσ
  have hΛ' : (0 : ℝ) < Λ := NNReal.coe_pos.2 hΛ
  have hlt : α < β - 1 := by linarith
  have hm : ContinuousOn (fun u ↦ ∫ x, rexp (u * x) ∂ν) (Ioo α β) :=
    (continuousOn_mgf (X := id) (μ := ν)).mono
      (isOpen_Ioo.subset_interior_iff.2 fun u hu ↦ hI u hu)
  have hD (θ : ℝ) (hθ : θ ∈ Ioo α (β - 1)) : θ ∈ Ioo α β ∧ 1 + θ ∈ Ioo α β :=
    ⟨⟨hθ.1, by linarith [hθ.2]⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have hlin : Continuous fun θ : ℝ ↦ b + σ ^ 2 / 2 + σ ^ 2 * θ := by fun_prop
  let f : ℝ → ℝ := fun θ ↦ b + σ ^ 2 / 2 + σ ^ 2 * θ
    + Λ * (∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν)
  simp only [jumpDiffusionExponent_one_add_sub b σ Λ ν]
  refine existsUnique_mem_Ioo_eq_of_strictMonoOn hlt (f := f) ?_ ?_ ?_ ?_ r
  · have h1 : ContinuousOn (fun θ : ℝ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν) (Ioo α (β - 1)) :=
      hm.comp (continuousOn_const.add continuousOn_id) fun θ hθ ↦ (hD θ hθ).2
    exact hlin.continuousOn.add
      (continuousOn_const.mul (h1.sub (hm.mono fun θ hθ ↦ (hD θ hθ).1)))
  · intro θ hθ θ' hθ' hθθ'
    have hg : ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν
        ≤ ∫ x, rexp ((1 + θ') * x) ∂ν - ∫ x, rexp (θ' * x) ∂ν :=
      monotoneOn_integral_exp_one_add_sub ⟨hI _ (hD θ hθ).1, hI _ (hD θ hθ).2⟩
        ⟨hI _ (hD θ' hθ').1, hI _ (hD θ' hθ').2⟩ hθθ'.le
    have := mul_le_mul_of_nonneg_left hg hΛ'.le
    have := mul_lt_mul_of_pos_left hθθ' hσ2
    simp only [f]
    linarith
  · -- at `α`, the moment of order `θ` blows up and that of order `1 + θ` stays bounded
    have h1c : ContinuousAt (fun θ : ℝ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν) α :=
      ContinuousAt.comp (f := fun θ : ℝ ↦ 1 + θ)
        (hm.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩))
        (continuous_const.add continuous_id).continuousAt
    have hg : Tendsto (fun θ : ℝ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν)
        (𝓝[>] α) atBot :=
      Tendsto.congr (fun θ ↦ (sub_eq_add_neg _ _).symm)
        ((h1c.tendsto.mono_left nhdsWithin_le_nhds).add_atBot
          (tendsto_neg_atTop_atBot.comp hα))
    exact ((hlin.tendsto α).mono_left nhdsWithin_le_nhds).add_atBot (hg.const_mul_atBot hΛ')
  · -- at `β - 1`, the moment of order `1 + θ` blows up and that of order `θ` stays bounded
    have hshift : Tendsto (fun θ : ℝ ↦ 1 + θ) (𝓝[<] (β - 1)) (𝓝[<] β) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun θ hθ ↦ ?_⟩
      · have : Tendsto (fun θ : ℝ ↦ 1 + θ) (𝓝 (β - 1)) (𝓝 (1 + (β - 1))) :=
          (continuous_const.add continuous_id).tendsto _
        rw [add_sub_cancel] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact (by linarith [show θ < β - 1 from hθ] : 1 + θ < β)
    have h2 : ContinuousAt (fun u ↦ ∫ x, rexp (u * x) ∂ν) (β - 1) :=
      hm.continuousAt (isOpen_Ioo.mem_nhds ⟨hlt, by linarith⟩)
    have hg : Tendsto (fun θ : ℝ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν)
        (𝓝[<] (β - 1)) atTop :=
      Tendsto.congr (fun θ ↦ (sub_eq_add_neg _ _).symm)
        ((hβ.comp hshift).atTop_add (h2.tendsto.mono_left nhdsWithin_le_nhds).neg)
    exact ((hlin.tendsto (β - 1)).mono_left nhdsWithin_le_nhds).add_atTop
      (hg.const_mul_atTop hΛ')

/-- **The Esscher price is a price function of the tilted characteristics.** When the
moment-generating function of the jump law is finite near `θ`, the discounted call payoff integrated
against the Esscher-tilted log-return law is the call price function `jumpDiffusionCallPrice` of
the characteristics `(b + θσ², σ, Λ·m(θ), ν.tilted (θ * ·))` (`jumpDiffusionIncrementLaw_tilted`),
so results about price functions apply to it, such as Merton's formula at the compensated drift. -/
lemma integral_call_tilted_eq_jumpDiffusionCallPrice (S K r b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {θ : ℝ} (hθ : θ ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·))
      = jumpDiffusionCallPrice S K r (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·))
          τ := by
  rw [jumpDiffusionIncrementLaw_tilted b σ Λ hθ τ, jumpDiffusionCallPrice]

/-- **Esscher pricing of the call.** When the moment-generating function of the jump law is finite
near `θ` and at `1 + θ`, at an Esscher parameter, `κ(θ + 1) − κ(θ) = r`, the discounted call payoff
integrated against the Esscher-tilted log-return law is Merton's formula for the tilted
characteristics: the `Poisson(Λm(θ)τ)` mixture of Black–Scholes prices over jumps of law
`ν.tilted (θ * ·)` (`integral_call_tilted_eq_jumpDiffusionCallPrice`,
`jumpDiffusionCallPrice_eq_merton`). -/
theorem integral_call_tilted_eq_merton {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hθν : θ ∈ interior (integrableExpSet id ν)) (h1 : Integrable (fun x ↦ rexp ((1 + θ) * x)) ν)
    (hθ : jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·))
      = ∫ n, ∫ j, bsV K r σ (S * rexp (-((Λ * jumpMoment ν θ : ℝ≥0) * τ
          * (∫ x, rexp x ∂(ν.tilted (θ * ·)) - 1)) + ∑ i ∈ Finset.range n, j i)) τ
          ∂(Measure.infinitePi fun _ : ℕ ↦ ν.tilted (θ * ·))
          ∂(poissonMeasure (Λ * jumpMoment ν θ * τ)) := by
  have hθ' : Integrable (fun x ↦ rexp (θ * x)) ν := interior_subset (s := integrableExpSet id ν) hθν
  have : IsProbabilityMeasure (ν.tilted (θ * ·)) := isProbabilityMeasure_tilted hθ'
  rw [integral_call_tilted_eq_jumpDiffusionCallPrice S K r b σ Λ hθν τ]
  exact jumpDiffusionCallPrice_eq_merton hS hK hσ
    (by simpa only [one_mul] using integrable_exp_mul_tilted_const_mul hθ' h1)
    ((compensated_tilted_iff b σ r Λ hθ').2 hθ) hτ

/-- **Tilting keeps Merton's jumps lognormal**: Merton's log-jump law `N(log(1 + k) − δ²/2, δ²)`
tilted by `e^{θx}` is Merton's log-jump law with the jump mean `(1 + k)e^{θδ²} − 1`
(`gaussianReal_tilted_const_mul`). -/
lemma mertonJump_tilted {k : ℝ} (hk : -1 < k) (δ θ : ℝ) :
    (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal).tilted (θ * ·)
      = gaussianReal (Real.log (1 + ((1 + k) * rexp (θ * δ ^ 2) - 1)) - δ ^ 2 / 2)
          (δ ^ 2).toNNReal := by
  rw [gaussianReal_tilted_const_mul, Real.coe_toNNReal _ (sq_nonneg δ), add_sub_cancel,
    Real.log_mul (show (0 : ℝ) < 1 + k by linarith).ne' (Real.exp_pos _).ne', Real.log_exp]
  congr 1
  ring

/-- **Esscher pricing in Merton's model.** With Merton's log-jumps `N(log(1 + k) − δ²/2, δ²)`, at
an Esscher parameter the call integrated against the tilted log-return law is Merton's 1976 series
with the jump mean `k' = (1 + k)e^{θδ²} − 1` and the expected jump count `Λm(θ)τ`: the tilted jumps
are Merton's with jump mean `k'` (`mertonJump_tilted`), and
`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice` applies. -/
theorem integral_call_tilted_eq_mertonCallPrice {S K r b σ k δ : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hσ : 0 < σ) (hk : -1 < k) {Λ : ℝ≥0} {θ : ℝ}
    (hθ : jumpDiffusionExponent b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) (1 + θ)
      - jumpDiffusionExponent b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) θ = r)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ Λ
          (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ).tilted (θ * ·))
      = mertonCallPrice S K r σ τ ((1 + k) * rexp (θ * δ ^ 2) - 1) δ
          (Λ * jumpMoment (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) θ
            * τ) := by
  have hν (u : ℝ) : Integrable (fun x ↦ rexp (u * x))
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) :=
    integrable_exp_mul_gaussianReal u
  have hk' : -1 < (1 + k) * rexp (θ * δ ^ 2) - 1 := by
    linarith [mul_pos (show (0 : ℝ) < 1 + k by linarith) (Real.exp_pos (θ * δ ^ 2))]
  -- the Esscher condition is the compensated drift of the tilted Merton model
  have hb := (compensated_tilted_iff b σ r Λ (hν θ)).2 hθ
  rw [mertonJump_tilted hk δ θ, integral_exp_mertonJump hk' δ] at hb
  rw [integral_call_tilted_eq_jumpDiffusionCallPrice S K r b σ Λ (by simp) τ,
    mertonJump_tilted hk δ θ]
  exact jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice hS hK hσ hk'
    (by linear_combination hb) hτ

/-- **With no jumps the Esscher transform shifts the drift**: the log-return law `N(bτ, σ²τ)`
tilted by `e^{θy}` is `N((b + θσ²)τ, σ²τ)`, the log-return law with drift `b + θσ²`. It is the
Gaussian tilt of the static Girsanov theorem (`gaussianReal_tilted_const_mul`); no moment of the
jump law is needed. -/
lemma jumpDiffusionIncrementLaw_zero_tilted (b σ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ : ℝ) (τ : ℝ≥0) :
    (jumpDiffusionIncrementLaw b σ 0 ν τ).tilted (θ * ·)
      = jumpDiffusionIncrementLaw (b + θ * σ ^ 2) σ 0 ν τ := by
  rw [jumpDiffusionIncrementLaw_zero, jumpDiffusionIncrementLaw_zero,
    gaussianReal_tilted_const_mul]
  congr 1
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  ring

/-- **Without jumps the Esscher parameter is explicit.** At jump rate `0`, `κ(θ) = bθ + σ²θ²/2`, so
`κ(θ + 1) − κ(θ) = b + σ²/2 + σ²θ`, and `θ = (r − b − σ²/2)/σ²` satisfies the Esscher condition
`κ(θ + 1) − κ(θ) = r`. -/
lemma jumpDiffusionExponent_zero_esscher (b σ r : ℝ) (hσ : σ ≠ 0) (ν : Measure ℝ) :
    jumpDiffusionExponent b σ 0 ν (1 + (r - b - σ ^ 2 / 2) / σ ^ 2)
      - jumpDiffusionExponent b σ 0 ν ((r - b - σ ^ 2 / 2) / σ ^ 2) = r := by
  have h0 : ((0 : ℝ≥0) : ℝ) = 0 := rfl
  simp only [jumpDiffusionExponent, h0, zero_mul, add_zero]
  linear_combination div_mul_cancel₀ (r - b - σ ^ 2 / 2) (pow_ne_zero 2 hσ)

/-- **With no jumps, Esscher pricing is Black–Scholes pricing.** For any drift `b`, the Esscher
parameter `θ = (r − b − σ²/2)/σ²` (`jumpDiffusionExponent_zero_esscher`) moves the log-return law
`N(bτ, σ²τ)` to the risk-neutral `N((r − σ²/2)τ, σ²τ)` (`jumpDiffusionIncrementLaw_zero_tilted`),
and the discounted call integrated against it is the Black–Scholes price `C_BS(S, τ)`
(`jumpDiffusionCallPrice_zero`), for `S, K, σ, τ > 0`. -/
theorem integral_call_tilted_zero_eq_bsV {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ 0 ν τ).tilted ((r - b - σ ^ 2 / 2) / σ ^ 2 * ·))
      = bsV K r σ S τ := by
  have hθ : b + (r - b - σ ^ 2 / 2) / σ ^ 2 * σ ^ 2 = r - σ ^ 2 / 2 := by
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hσ.ne')]
    ring
  rw [jumpDiffusionIncrementLaw_zero_tilted, hθ]
  exact jumpDiffusionCallPrice_zero hS hK hσ ν hτ

end MathFin
