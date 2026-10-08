/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.JumpDiffusionMerton
public import MathFin.BlackScholes.JumpDiffusionBrownian
public import MathFin.Foundations.Esscher

/-!
# The Esscher transform of a jump-diffusion

The Esscher transform with parameter `θ` reweights a law by `e^{θy}` and renormalizes it
(`Foundations/Esscher.lean`, on Mathlib's `Measure.tilted`). Here it acts on the log-return law
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
* `compensated_tilted_iff`: the tilted characteristics are at their compensated drift exactly
  when `κ(θ + 1) − κ(θ) = r`, the Esscher condition: the criterion `κ(1) = r`
  (`compensated_iff_exponent_one`) for the tilted Laplace exponent `u ↦ κ(u + θ) − κ(θ)`.
* `existsUnique_esscher`: with a Gaussian part (`σ ≠ 0`) and every exponential moment of `ν`, the
  Esscher condition has exactly one solution, the Esscher parameter.
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

The statements are about the law at one date, not about the process under a changed measure. With
jumps (`Λ > 0`) the market is in general incomplete (not formalized here), and the Esscher law is
then one pricing law among others. Without a Gaussian part (`σ = 0`) the existence of an Esscher
parameter is not proved.
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
  have hint : ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun y ↦ rexp (u * y))
      (jumpDiffusionIncrementLaw (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·)) τ) :=
    hU.mono fun u hu ↦ integrable_exp_mul_jumpDiffusionIncrementLaw _ _ _
      (integrable_exp_mul_tilted_const_mul hθν hu) τ
  refine Eq.symm (measure_eq_of_mgf_id_eventuallyEq (mem_interior_iff_mem_nhds.2 hint)
    (hU.mono fun u hu ↦ ?_))
  rw [mgf_id_jumpDiffusionIncrementLaw _ _ _ (integrable_exp_mul_tilted_const_mul hθν hu),
    jumpDiffusionExponent_tilted b σ Λ hθν u, mgf_id_tilted_const_mul,
    mgf_id_jumpDiffusionIncrementLaw b σ Λ hu, mgf_id_jumpDiffusionIncrementLaw b σ Λ hθν,
    ← Real.exp_sub, sub_mul]

/-- **The Esscher transform multiplies the Lévy measure by `e^{θx}`**: the tilted
characteristics have the Lévy measure `Λm(θ)·ν_θ = e^{θx}·Λν`, where `m(θ) = ∫ e^{θx} dν`. -/
lemma smul_tilted_eq_withDensity (Λ : ℝ≥0) {ν : Measure ℝ} [NeZero ν] {θ : ℝ}
    (hθ : Integrable (fun x ↦ rexp (θ * x)) ν) :
    (Λ * jumpMoment ν θ) • ν.tilted (θ * ·)
      = Λ • ν.withDensity fun x ↦ ENNReal.ofReal (rexp (θ * x)) := by
  have hm : 0 < ∫ x, rexp (θ * x) ∂ν := integral_exp_pos hθ
  rw [mul_smul, Measure.tilted, ENNReal.smul_def (jumpMoment ν θ),
    ← withDensity_smul' _ _ ENNReal.coe_ne_top]
  refine congrArg (Λ • ·) (congrArg ν.withDensity (funext fun x ↦ ?_))
  rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal, coe_jumpMoment,
    ← ENNReal.ofReal_mul hm.le, mul_div_cancel₀ _ hm.ne']

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
is nondecreasing: for `θ ≤ θ'` the difference of integrands `(e^{θ'x} − e^{θx})(eˣ − 1)` is
nonnegative, both factors having the sign of `x`. -/
lemma monotone_integral_exp_one_add_sub {ν : Measure ℝ}
    (hν : ∀ u, Integrable (fun x ↦ rexp (u * x)) ν) :
    Monotone fun θ ↦ ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν := by
  intro θ θ' hθ
  show ∫ x, rexp ((1 + θ) * x) ∂ν - ∫ x, rexp (θ * x) ∂ν
      ≤ ∫ x, rexp ((1 + θ') * x) ∂ν - ∫ x, rexp (θ' * x) ∂ν
  rw [← integral_sub (hν _) (hν _), ← integral_sub (hν _) (hν _)]
  refine integral_mono ((hν _).sub (hν _)) ((hν _).sub (hν _)) fun x ↦ ?_
  show rexp ((1 + θ) * x) - rexp (θ * x) ≤ rexp ((1 + θ') * x) - rexp (θ' * x)
  have key : 0 ≤ (rexp (θ' * x) - rexp (θ * x)) * (rexp x - 1) := by
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hθ hx)))
        (sub_nonneg.2 (Real.one_le_exp hx))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hθ hx)))
        (sub_nonpos.2 (Real.exp_le_one_iff.2 hx))
  rw [add_mul, add_mul, one_mul, Real.exp_add, Real.exp_add]
  linarith

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
