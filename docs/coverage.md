# Formalization Status

This project distinguishes two claims:

1. **Backend verification coverage:** active Lean code checks successfully.
2. **Faithful theorem formalization:** the checked statement closely matches the course theorem AND the proof is a real derivation, not a structural projection from an axiomatized conclusion.

The first claim is useful engineering evidence. The second is the academic claim. Do not collapse them.

## Status Vocabulary

- `full`: a faithful formal **derivation** of the textbook theorem from its hypotheses. The hypotheses must be encoded honestly (not the conclusion in disguise) and the proof must do real work — `ring`/`simp`/`rfl` on a structure-projection target does NOT qualify.
- `library_wrapper`: the active code directly invokes a named Lean library theorem whose statement matches the benchmark theorem. The library does the real work.
- `reduced_core`: the active code is honest but narrower than the textbook theorem. This includes:
  - Algebraic / analytic / distributional core checks (e.g., a constant-θ MGF identity behind Wald's exponential).
  - Lean specifications where the textbook conclusion is encoded as a structure field and the proof reads it off via projection. The structure pins down the textbook STATEMENT but does not derive the conclusion.
- `placeholder`: active prover code verifies but does not yet encode a meaningful formal statement of the textbook theorem.

For delivery claims, count only:

```text
full + library_wrapper
```

Report `reduced_core` and `placeholder` separately. **Spec-with-axiomatized-conclusion is `reduced_core`, not `full`.**

## Current Audit

### The law of the price, as a measure (2026-10-08)

Four entries added, all `full`: `mf-price-law-change-of-variables`, `mf-jump-diffusion-price-law`,
`mf-black-scholes-price-law` and `mf-merton-price-law`. Corpus 513 → 517. Files:
`BlackScholes/JumpDiffusionDensity.lean` and `BlackScholes/JumpDiffusionDigital.lean`.

- The change of variables. For `f ≥ 0` and `S > 0`, the image of `f(y) dy` under `y ↦ Seʸ` is
  `f(log(K/S))/K dK` on `(0, ∞)` (`map_mul_exp_withDensity`, from Mathlib's
  `lintegral_image_eq_lintegral_abs_deriv_mul`; `y ↦ Seʸ` is a bijection of `ℝ` onto `(0, ∞)`
  with derivative `Seʸ`).
- The jump-diffusion price. With `σ ≠ 0` the price `Seʸ` has the law `f(log(K/S))/K dK` on
  `(0, ∞)` (`jumpDiffusionIncrementLaw_map_mul_exp`). The density of the price that the second
  strike derivative of the call reads off, strike by strike, is the density of the law of the price.
- Black–Scholes. Without jumps, at the drift `r − σ²/2`, the price has the law
  `lognormalTerminalPDF(K) dK` on `(0, ∞)` and the formula integrates to one
  (`jumpDiffusionIncrementLaw_zero_map_mul_exp`, `lintegral_lognormalTerminalPDF`). These are the
  two facts `BreedenLitzenberger.lean` states it does not prove.
- Merton. With Gaussian log-jumps and any drift, the price has the law `mertonTerminalPDF(K) dK` on
  `(0, ∞)` and the mixture integrates to one (`jumpDiffusionIncrementLaw_gaussian_map_mul_exp`,
  `lintegral_mertonTerminalPDF`).

Each identification of densities is pointwise on `(0, ∞)` (the earlier sections), and two
`withDensity` measures agree when their densities agree almost everywhere (Mathlib's
`withDensity_congr_ae`); integrating to one is the mass of the image of a probability measure.

Safe wording: "the price `Seʸ` of a jump-diffusion with a Gaussian part has the density
`f(log(K/S))/K` on `(0, ∞)`; without jumps this is the lognormal density `lognormalTerminalPDF`, and
with Gaussian log-jumps it is Merton's Poisson mixture `mertonTerminalPDF`, each a probability
density". Not covered: moments of the price computed from these densities (the library computes
them from the log-return law, `mgf_id_jumpDiffusionIncrementLaw`).

### Kinks: the call price is differentiable in the strike exactly where the law has no atom (2026-10-08)

Four entries added, all `full`: `mf-call-strike-differentiable-iff-no-atom`,
`mf-jump-diffusion-call-differentiable-iff`, `mf-jump-diffusion-call-kink` and
`mf-cash-digital-strike`. Corpus 509 → 513. `BlackScholes/CallSpreadDigital.lean`,
`BlackScholes/JumpDiffusionDensity.lean`, `BlackScholes/JumpDiffusionDigital.lean` and
`BlackScholes/StrikeGreeks.lean` gain the results.

- The left spread. For a measurable, integrable `X` under a finite measure, the call spread just
  below the strike, `(C(K − h) − C(K))/h`, tends to `μ{X ≥ K}` as `h ↓ 0`
  (`tendsto_call_spread_left`, dominated convergence as for `tendsto_call_spread`). So the left
  strike derivative is `−μ{X ≥ K}` and the right one `−μ{X > K}`.
- Differentiability iff no atom. The call price `C(k) = ∫ (X − k)⁺ dμ` is differentiable at `K` iff
  `μ{X = K} = 0` (`differentiableAt_integral_call_iff`): a derivative makes the two one-sided
  slopes equal (Mathlib's `HasDerivAt.tendsto_slope_zero_right` and `tendsto_slope_zero_left`),
  and they differ by the mass of the atom.
- The jump-diffusion call. For `S, K > 0` and a finite forward, the call price function is
  differentiable at `K` iff the log-return law has no atom at `log(K/S)`
  (`differentiableAt_jumpDiffusionCallPrice_strike_iff`). Without a Gaussian part the law has an
  atom at `bτ` of mass at least `e^{−Λτ}`, the probability of no jump
  (`ofReal_exp_le_jumpDiffusionIncrementLaw_singleton`: given the jumps the law is a point mass,
  Mathlib's `gaussianReal_zero_var`). So with `σ = 0` the call price has a kink at the strike
  `Se^{bτ}` (`not_differentiableAt_jumpDiffusionCallPrice_strike`).
- The Black–Scholes digital in the strike. `∂_K (e^{−rτ}Φ(d₂)) = −e^{−rτ}ϕ(d₂)/(Kσ√τ)`
  (`hasDerivAt_bsCashDigital_K`), the strike Greek missing from `DigitalGreeks`. The second strike
  derivative of the call, `hasDerivAt_deriv_bsV_K`, is now this lemma negated, and Merton's
  digital series is the Poisson mixture of `bsCashDigital` (section below).

Safe wording: "the call price is differentiable in the strike exactly where the law of the
underlying has no atom, its one-sided strike derivatives being minus the digitals of `X > K` and
`X ≥ K`; a jump-diffusion without a Gaussian part has an atom at the no-jump outcome, so its call
price has a kink at the strike `Se^{bτ}`". Not covered:
- the other atoms of a law with `σ = 0` (at `bτ` plus the atoms of the convolution powers of `ν`);
- the size of the kink as a statement about the jump-diffusion call price (it follows from the
  general one-sided limits, applied to `Seʸ`).

### Merton's digital and Merton's density: the strike derivatives of Merton's series (2026-10-08)

Three entries added, all `full`: `mf-merton-strike-derivatives`, `mf-jump-diffusion-merton-digital`
and `mf-jump-diffusion-merton-density`. Corpus 506 → 509. New file
`BlackScholes/MertonStrikeGreeks.lean`; `BlackScholes/JumpDiffusionDigital.lean` gains the
identifications.

- The series in the strike. Merton's call series `C(K) = ∑ₙ wₙ C_BS(S·cₙ, K, σₙ)` is
  differentiated term by term in the strike, as the Merton Greeks differentiate it in the spot
  (`hasDerivAt_tsum_of_isPreconnected`). For `S, σ, T, K > 0` and `k > −1`:
  `∂C/∂K = −mertonDigitalPrice`, with `mertonDigitalPrice = ∑ₙ wₙ e^{−rT}Φ(d₂ⁿ)`
  (`hasDerivAt_mertonCallPrice_strike`, each term by `hasDerivAt_bsV_K`), the Poisson mixture of
  the Black–Scholes digitals `bsCashDigital`; and `∂²C/∂K² = e^{−rT}·mertonTerminalPDF`, with
  `mertonTerminalPDF = ∑ₙ wₙ·lognormalTerminalPDF(S·cₙ, r, σₙ, T, K)`
  (`hasDerivAt_mertonDigitalPrice_strike`, `hasDerivAt_deriv_mertonCallPrice_strike`, each term
  by `hasDerivAt_bsCashDigital_K`). The derivative bounds are `wₙe^{−rT}` and, on `(K/2, ∞)`,
  `wₙe^{−rT}/((K/2)σ√T)`; the Poisson weights sum to one (Mathlib's `hasSum_one_poissonMeasure`).
- Merton's digital. For `σ > 0`, `k > −1`, `S, K > 0` and `τ > 0`, with Gaussian log-jumps
  `N(log(1 + k) − δ²/2, δ²)` at the compensated drift `b = r − σ²/2 − Λk`, the jump-diffusion
  digital price is `mertonDigitalPrice` at the expected
  jump count `Λτ` (`jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice`). The digital price
  is minus the strike derivative of the call price, and near `K` the call price is Merton's series
  (`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`); `HasDerivAt.unique` compares the two
  derivatives.
- Merton's density. With the same jumps and any drift `b`, the density of the price at `K`,
  `f(log(K/S))/K`, is `mertonTerminalPDF` at the parameter `r = b + σ²/2 + Λk`
  (`jumpDiffusionDensity_gaussian_div_eq_mertonTerminalPDF`): the strike derivative of the digital
  price discounted at `r` is `−e^{−rτ}f(log(K/S))/K`, and near `K` that digital price is Merton's
  digital series. At the compensated drift `r` is the interest rate; `r` enters the series only
  through `d₂`, which is why every drift is covered.

Neither identification integrates a payoff against a Gaussian or convolves Gaussians: both are read
off Merton's call series. The only Gaussian computation in the chain is the Gaussian smoothing
behind that series, which the library had derived from the general jump-diffusion.

Safe wording: "Merton's call series has strike derivative minus the Poisson mixture of
Black–Scholes digitals and second strike derivative the discounted Poisson mixture of lognormal
density formulas; with Gaussian log-jumps `N(log(1 + k) − δ²/2, δ²)` (`k > −1`) and `σ > 0`, these
mixtures at maturity `τ` and expected jump count `Λτ` are the digital price (at the compensated
drift) and the density of the price (at every drift) of the jump-diffusion". Not covered:
- the put's strike derivatives and the put digital;
- strike derivatives for jump laws other than Gaussian, beyond the general
  `breedenLitzenberger_jumpDiffusion`.

### The density of a jump-diffusion log-return; Breeden–Litzenberger with jumps (2026-10-08)

Three entries added, all `full`: `mf-jump-diffusion-density`, `mf-breeden-litzenberger-jump-diffusion`
and `mf-black-scholes-lognormal-density`. Corpus 503 → 506. New file
`BlackScholes/JumpDiffusionDensity.lean`, which holds the facts about the law; the option prices
are in `BlackScholes/JumpDiffusionDigital.lean`. The no-atom lemma of the digital rung moved to the
density file, where it is a corollary of the density, and `mf-jump-diffusion-digital-strike-derivative`
now states it.

- The law is a Gaussian mixture. Given the jump count `n` and the jump sizes `j`, the log-return
  is `N(bτ + ∑_{i<n} jᵢ, σ²τ)` (Mathlib's `gaussianReal_map_const_mul` and
  `gaussianReal_map_const_add`). So the law is the mixture of these Gaussian laws over
  `Poisson(Λτ) ⊗ ν^ℕ` (`jumpDiffusionIncrementLaw_apply`, for every `σ`).
- The density. For `σ ≠ 0` and `τ > 0` the law is `f(y) dy`, with `f` the mixture of the normal
  densities (`jumpDiffusionDensity`, `jumpDiffusionIncrementLaw_eq_withDensity`, by Tonelli). `f`
  is continuous by dominated convergence, since a normal density is at most `1/√(2πv)`
  (`continuous_jumpDiffusionDensity`). The jump law is arbitrary and needs no moment condition; for
  lognormal jumps `f` is Merton's (1976) Poisson mixture of normal densities. So the law has no
  atoms (`nullSingletonClass_jumpDiffusionIncrementLaw`, from Mathlib's
  `nullSingletonClass_withDensity`).
- The tail of a law with a density. For any law `f(y) dy` with `f ≥ 0` integrable, `x ↦ P(Y > x)`
  has derivative `−f(a)` at every `a` where `f` is continuous
  (`hasDerivAt_measureReal_Ioi_withDensity`, from Mathlib's
  `intervalIntegral.integral_hasDerivAt_right`).
- Breeden–Litzenberger with jumps. For `S > 0` and `K > 0` the digital price has strike derivative
  `−e^{−rτ}f(log(K/S))/K` (`hasDerivAt_jumpDiffusionDigitalPrice_strike`). So `f(log(K/S))/K` is
  the derivative at `K` of the distribution function of the price `Seʸ`. With a finite forward the
  strike derivative of the call is `−D` at every strike, so
  `∂²C/∂K² = e^{−rτ}f(log(K/S))/K` (`breedenLitzenberger_jumpDiffusion`).
- The lognormal density, read off. Without jumps, at the drift `r − σ²/2` and with `σ > 0`, the call
  price function is `bsV` near `K` (`jumpDiffusionCallPrice_zero`), so its second strike
  derivative is also `e^{−rτ}·lognormalTerminalPDF` (`breedenLitzenberger`). The two derivatives
  are equal (`HasDerivAt.unique`), so `f(log(K/S))/K = lognormalTerminalPDF`
  (`jumpDiffusionDensity_div_eq_lognormalTerminalPDF`). The formula of `BreedenLitzenberger.lean`
  is therefore the density of the price, which `breedenLitzenberger` alone does not show.

Safe wording: "with a Gaussian part, the log-return law of a jump-diffusion has a continuous
density, the mixture over the jumps of normal densities, for any jump law; the strike derivative of
the digital price is minus the discounted density of the price, and with a finite forward the
second strike derivative of the call price is the discounted density of the price
(Breeden–Litzenberger with jumps); without jumps, at the drift `r − σ²/2`, that density is the
lognormal density of `breedenLitzenberger`". Not covered:
- smoothness of the density beyond continuity;
- `σ = 0`, where the law has an atom at `bτ` (the no-jump event; not formalized);

### Digital options: minus the strike derivative of the call (2026-10-08)

Three entries added, all `full`: `mf-call-strike-derivative`,
`mf-jump-diffusion-digital-strike-derivative` and `mf-jump-diffusion-digital-black-scholes`. Corpus
500 → 503. New file `BlackScholes/JumpDiffusionDigital.lean`; `BlackScholes/CallSpreadDigital.lean`
gains the general strike derivative.

- The strike derivative in general. Where a measurable, integrable `X` has no atom at `K`, the
  undiscounted call price `C(k) = ∫ (X − k)⁺ dμ` is differentiable at `K`, and
  `C'(K) = −μ{X > K}` (`hasDerivAt_integral_call`, by Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_lip`). At an atom only the right derivative is claimed
  here (`tendsto_call_spread`); the left one and the kink came later (kink section above).
- No atoms with a Gaussian part. For `σ ≠ 0` and `τ > 0` the jump-diffusion log-return law has no
  atoms (`nullSingletonClass_jumpDiffusionIncrementLaw`). Since the density rung (above) this is a
  corollary of the density; the first proof used that, given the jumps, the log-return is affine
  in the standard normal sample with slope `σ√τ`.
- The jump-diffusion digital. With a finite forward the call price function is therefore
  differentiable in the strike at every `K`, and `∂C/∂K = −D`
  (`hasDerivAt_jumpDiffusionCallPrice_strike`). Here `D = e^{−rτ}P(Se^Y > K)` is the price of the
  cash-or-nothing digital (`jumpDiffusionDigitalPrice`).
- Black–Scholes from the strike derivative. Without jumps, `D = e^{−rτ}Φ(d₂)`
  (`jumpDiffusionDigitalPrice_zero`). The function has two derivatives at `K`, `−D` and
  `−e^{−rτ}Φ(d₂)` (from `hasDerivAt_bsV_K`), and they are equal. `bs_cash_or_nothing_formula`
  computes the same value as a Gaussian integral, and the two derivations agree.

Safe wording: "where the law of the underlying has no atom at the strike, minus the strike
derivative of the call price is the digital price; a jump-diffusion with a Gaussian part has no
atoms, so with a finite forward its digital price is minus the strike derivative of its call price
at every strike; without jumps this gives the Black–Scholes digital `e^{−rτ}Φ(d₂)`". Merton's
series for the jump-diffusion digital came later (Merton section above).

### Incompleteness at one date: call prices determine the law, the law determines the characteristics (2026-10-08)

Four entries added, all `full`: `mf-call-spread-digital`, `mf-call-prices-determine-law`,
`mf-jump-diffusion-identifiability` and `mf-jump-diffusion-incompleteness`. Corpus 496 → 500.
Files: `BlackScholes/CallSpreadDigital.lean`, `BlackScholes/JumpDiffusionIdentifiability.lean` and
`BlackScholes/JumpDiffusionIncompleteness.lean`. The local uniqueness lemma of
`Foundations/Esscher.lean` now holds for finite measures, not only probability laws, and the same
file has the unnormalized Esscher transform `(∫ e^f dμ)·μ.tilted f = e^f·μ`
(`ofReal_integral_exp_smul_tilted`).

- Call spreads and the digital. For a measurable, integrable `X` under a finite measure, the
  bull-call spread `(C(K) − C(K + h))/h` tends to `μ{X > K}` as `h ↓ 0` (`tendsto_call_spread`).
  The spread payoff is at most `1` in absolute value, because the call payoff is `1`-Lipschitz in
  the strike (Mathlib's `abs_max_sub_max_le_abs`), and tends pointwise to the digital payoff. So
  call prices at every strike `K > 0` determine the law of a log-return with a finite forward
  (`measure_eq_of_integral_call_eq`): the first-order Breeden–Litzenberger, for any law with a
  finite forward. The second-order form is `breedenLitzenberger_jumpDiffusion` for jump-diffusions
  with a Gaussian part (density rung, above) and `breedenLitzenberger` for Black–Scholes.
- The law determines the drift, the Gaussian variance and the Lévy measure. Wherever
  `∫ e^{ux} dν < ∞`, `κ(u) = bu + σ²u²/2 + ∫ (e^{ux} − 1) Π(dx)`, with `Π` the Lévy measure `Λν`
  restricted off `0` (`jumpDiffusionExponent_eq_levy`). For jump laws whose moment-generating
  functions are finite near `0`, two log-return laws at one date `τ > 0` are equal iff their drifts
  agree, their Gaussian variances `σ²` agree and their Lévy measures agree off `0`
  (`jumpDiffusionIncrementLaw_eq_iff`). The sign of `σ`, the rate and the jump law are not
  determined separately. Second differences of `κ` are the moment-generating function of the
  finite measure `σ²s²·δ₀ + 2(cosh(sx) − 1)·Λν` (`secondDifferenceMeasure`), so the local
  uniqueness of the Esscher layer identifies that measure. Its atom at `0` gives `σ²`, and off `0`
  dividing by the kernel gives `Π`. This is the Lévy–Khintchine uniqueness for compound-Poisson
  jumps with exponential moments near `0`.
- A change of drift gives an equivalent law. For `σ ≠ 0` and `τ > 0`, log-return laws that differ
  only in the drift are equivalent (`jumpDiffusionIncrementLaw_absolutelyContinuous`): on the
  canonical model a change of drift is a move of the standard normal sample, and the moved
  Gaussian `N(m, 1)` is the Esscher tilt of `N(0, 1)` (`gaussianReal_tilted_const_mul`), equivalent
  to it. This is static Girsanov on the Gaussian factor (`Foundations/GaussianGirsanov.lean`).
- Incompleteness at one date. The Esscher transform multiplies the Lévy measure by `e^{θx}`
  (`smul_tilted_eq_withDensity`). Suppose `σ ≠ 0`, the jumps are nontrivial (`Λ > 0`, `ν` not the
  point mass at `0`), the jump law's moment-generating function is finite near `0` and near `θ`
  with finite exponential moments `∫ eˣ dν` and `∫ e^{(1+θ)x} dν`, and the physical drift is off the
  compensated one. Then the Esscher law and the Merton measure's law (the same `σ`, `Λ`, `ν` and
  the compensated drift) are both equivalent to the physical law and both have the forward
  `∫ eʸ = e^{rτ}`, yet at some strike their call prices differ (`exists_call_esscher_ne_merton`).
  Equal prices at every strike would make the two laws equal, hence their Lévy measures, but
  `θ ≠ 0` and `e^{θx} ≠ 1` off `0`.

Safe wording: "call prices at every strike determine the law of the log-return; the law at one
date of a jump-diffusion determines its drift, its Gaussian variance and its Lévy measure off `0`
(for jump laws with exponential moments near `0`); and with
`σ ≠ 0`, nontrivial jumps and a physical drift off the compensated one, the Esscher law and the
Merton measure's law are two compensated laws, both equivalent to the physical law at one date,
that price some call differently". Not covered:
- the Lévy–Khintchine uniqueness without moment conditions (by characteristic functions);
- the process-level changes of measure (equivalent martingale measures for the price process)
  behind the two laws; for `σ = 0` the Merton law need not be equivalent to the physical one (the
  physical law has an atom at `bτ`, which a change of drift moves);
- the set of all arbitrage-free call prices, or superreplication bounds.

### The Esscher transform: one tilt for static Girsanov and the jumps, one MGF identification shared with Brownian motion (2026-10-08)

Six entries added, all `full`: `mf-jump-diffusion-esscher-transform`,
`mf-jump-diffusion-esscher-pricing`, `mf-jump-diffusion-esscher-parameter`,
`mf-merton-esscher-pricing`, `mf-black-scholes-esscher-pricing` and `gir-gaussian-esscher-tilt`.
Corpus 490 → 496. The tilt lives in `Foundations/Esscher.lean`, the jump-diffusion results in
`BlackScholes/JumpDiffusionEsscher.lean`.

- One tilt. The Esscher transform with parameter `θ` of a law `μ` on `ℝ` is Mathlib's
  `μ.tilted (θ * ·)`. Its exponential moments are ratios of those of `μ`
  (`integral_exp_mul_tilted_const_mul`, Mathlib's `integral_exp_tilted` at linear exponents).
  A law is determined by its moment-generating function on a neighbourhood of `0`, when that
  function is finite there (`measure_eq_of_mgf_id_eventuallyEq`). The proof is the identity
  theorem on a vertical strip for Mathlib's complex moment-generating function, then the
  characteristic function on the imaginary axis. `measure_eq_of_mgf_id_eq` is the case of every
  exponential moment. A Gaussian law has its mean shifted: `N(m, v)` tilted is `N(m + θv, v)`
  (`gaussianReal_tilted_const_mul`).
- One file, three users. The static Girsanov change of measure
  `gaussianReal_withDensity_esscher` (behind `BSCallHyp.exists_of_physical`) is the case `N(0, 1)`
  of the Gaussian tilt; its pdf proof `gaussian_esscher_pdf`, used nowhere else, is removed. The
  exponential-martingale characterization of Brownian motion (`ExpMartingaleQBrownian`)
  identifies the Gaussian increment law with `measure_eq_of_mgf_id_eq` instead of its own copy of
  the complex-MGF argument. The jump layer is the third user.
- The jump-diffusion law. When the moment-generating function of the jump law `ν` is finite near
  `θ`, the tilted log-return law over `τ` is the jump-diffusion law with drift `b + θσ²`, the same
  `σ`, rate `Λ·∫e^{θx}dν` and the tilted jump law (`jumpDiffusionIncrementLaw_tilted`). Near
  `0`, both laws have the moment-generating function `u ↦ e^{(κ(u + θ) − κ(θ))τ}`
  (`jumpDiffusionExponent_tilted`). This covers jump laws whose moment-generating function is
  finite only on an interval, such as Kou's double-exponential jumps.
- Esscher pricing. The tilted characteristics are at their compensated drift exactly when
  `κ(θ + 1) − κ(θ) = r` (`compensated_tilted_iff`): the criterion `κ(1) = r`
  (`compensated_iff_exponent_one`, shared with the discounted-price martingale criterion) for the
  tilted Laplace exponent. The call against the tilted law is the call price function of the
  tilted characteristics (`integral_call_tilted_eq_jumpDiffusionCallPrice`). So at such a `θ`,
  with the moment at `1 + θ` finite, it is Merton's formula for the tilted jump law
  (`integral_call_tilted_eq_merton`). Tilting keeps Merton's jumps lognormal with the jump mean
  `(1 + k)e^{θδ²} − 1` (`mertonJump_tilted`), so in Merton's model it is Merton's 1976 series
  (`integral_call_tilted_eq_mertonCallPrice`).
- The Esscher parameter exists and is unique when `σ ≠ 0` and the jump law has every exponential
  moment (`existsUnique_esscher`). `θ ↦ κ(1 + θ) − κ(θ)` is the line `b + σ²/2 + σ²θ` plus `Λ`
  times the jump part `∫ e^{θx}(eˣ − 1) dν`, which is nondecreasing because
  `(e^{θ'x} − e^{θx})(eˣ − 1) ≥ 0` for `θ ≤ θ'`. So the map is strictly increasing, continuous
  (Mathlib's `continuous_mgf`) and unbounded both ways, and `Continuous.surjective` applies.
  Without jumps the parameter is `θ = (r − b − σ²/2)/σ²` (`jumpDiffusionExponent_zero_esscher`).
  The tilt there gives the risk-neutral law and the Black–Scholes price for every drift
  (`integral_call_tilted_zero_eq_bsV`, through `jumpDiffusionIncrementLaw_zero_tilted`).

Safe wording: "where the jump law's moment-generating function is finite near `θ`, the Esscher
transform of the log-return law at one date is again a jump-diffusion law, and at an Esscher
parameter with a finite moment of order `1 + θ` the call against it is Merton's formula for the
tilted jumps". The Esscher law is equivalent to the physical law at one date, but with
nontrivial jumps and `σ ≠ 0` it is not the only compensated law that is: when the physical drift is
not already compensated, the Merton measure's law is another, and the two price some call
differently (`exists_call_esscher_ne_merton`, section above, under its moment conditions); without
jumps the model is Black–Scholes. Not covered:
- the existence of an Esscher parameter without a Gaussian part (`σ = 0`), or when the jump law's
  moment-generating function is finite only on an interval;
- the Esscher measure on the process, a change of measure on `Ω` under which `X` is again a
  jump-diffusion;
- optimality properties of the Esscher measure.

### The Laplace exponent: the moment-generating function, exponential martingales, power claims (2026-10-08)

Four entries added, all `full`: `mf-jump-diffusion-scaling`, `mf-jump-diffusion-levy-exponent`,
`mf-jump-diffusion-exponential-martingales` and `mf-jump-diffusion-power-claim-every-date`.
Corpus 486 → 490. They live in `BlackScholes/JumpDiffusionProcess.lean` (the moment-generating
function) and `BlackScholes/JumpDiffusionExponent.lean` (scaling, martingales, power claims).

- The moment-generating function, at every `θ` with `∫ e^{θx} dν < ∞`:
  `∫ e^{θy} dμ_τ(y) = e^{κ(θ)τ}` with the Laplace exponent
  `κ(θ) = bθ + σ²θ²/2 + Λ(∫ e^{θx} dν − 1)` (`jumpDiffusionExponent`,
  `integral_exp_const_mul_jumpDiffusionIncrementLaw`). On the canonical model it is the Gaussian
  moment-generating function times the compound-Poisson one, by independence
  (`JumpDiffusionHyp.mgf_logReturn`: Mathlib's `mgf_gaussianReal` and `IndepFun.mgf_add'`, and
  `compoundPoisson_mgf_of_indepFun` from `Actuarial/CompoundPoissonMGF.lean`). In Mathlib's terms
  `κ(θ)τ` is the cumulant generating function (`cgf_id_jumpDiffusionIncrementLaw`). The moment at
  `1`, which the discounted-price criterion uses, is now its corollary; it was derived from the
  pricing identity `discounted_terminal`.
- Scaling, `jumpDiffusionIncrementLaw_map_const_mul`: `θ` times a jump-diffusion log-return over
  `τ` is one with drift `θb`, volatility coefficient `θσ`, the same rate, and the jump law pushed
  forward by `x ↦ θx`. This is an identity of laws, with no integrability hypothesis. On the
  canonical model the drift and the Gaussian coefficient scale inside the log-return, and the
  jumps change only the jump law (`jumpDiffusionMeasure_map_jumps`, from Mathlib's
  `Measure.map_prod_map` and `Measure.infinitePi_map_pi`). On the process, `θX` is a
  `JumpDiffusionProcess` (`JumpDiffusionProcess.const_mul`).
- The exponential martingales `e^{θX_t − κ(θ)t}` (`JumpDiffusionProcess.martingale_exp_const_mul_sub`)
  are the discounted-price criterion `martingale_iff` applied to `θX` at the rate `κ(θ)`. The
  criterion itself reads `κ(1) = r` (`JumpDiffusionProcess.martingale_iff_exponent_one`). For
  `b = 0`, `σ = 1` and no jumps `κ(θ) = θ²/2`, the exponent of Wald's martingales; both families
  rest on `martingale_exp_sub_of_indep_increments`.
- Power claims at each date before maturity, `JumpDiffusionProcess.condExp_rpow`: for `S₀ > 0`,
  `∫ e^{px} dν < ∞` and `t ≤ T`, `𝔼[e^{−r(T−t)}S_T^p | 𝓕_t] = S_t^p e^{(κ(p) − r)(T − t)}`, almost
  surely. It goes through `condExp_comp`, as the put and the call do.

Safe wording: "where the jump law has the exponential moment of order `θ`, the log-return over `τ`
has moment-generating function `e^{κ(θ)τ}`, and `e^{θX_t − κ(θ)t}` is a martingale". "Price" for
the power claim holds only when `P` is a martingale measure for the discounted price
(`κ(1) = r`), and then it is an arbitrage-free price. With jumps it is in general not the
only one, which is not formalized for the process; at one date, compensated laws are already not
unique (`exists_call_esscher_ne_merton`). Not covered: `θ` with
`∫ e^{θx} dν = ∞`; the Esscher change of measure on the process (the transform of the law at
one date is in the section above); the convolution semigroup `μ_s ∗ μ_t = μ_{s+t}`; the existence of the process with
jumps.

### One conditional freezing lemma; European payoffs at every date (2026-10-08)

Two entries added, both `full`: `ce-conditional-freezing-lemma` and
`mf-jump-diffusion-payoff-every-date`. Corpus 484 → 486.

- The conditional freezing lemma (Shreve's independence lemma), `condExp_comp_prodMk_of_indep`
  (`Foundations/IndepFreezing.lean`): for `X` measurable for a σ-algebra `𝒢` and `Y` independent
  of `𝒢`, `𝔼[g(X, Y) | 𝒢] = G(X)` with `G(x) = ∫ g(x, y) d(law Y)(y)`, for `g` strongly measurable
  with `g(X, Y)` integrable. On each event of `𝒢` the joint law of `(X, Y)` is a product
  (`map_restrict_prodMk_of_indep`), so Fubini gives the same integral over every such event. It
  replaces the bounded, real-valued case (`AmericanPut/Stopping/IndependentKernel.lean`, deleted):
  the American put's Brownian transitions and the jump-diffusion prices now use the same lemma.
- European payoffs at every date, `JumpDiffusionProcess.condExp_comp`:
  `𝔼[f(X_T) | 𝓕_t] = ∫ f(X_t + y) dμ_{T−t}(y)` for measurable `f` with `f(X_T)` integrable, with
  `μ_{T−t}` the log-return law over the remaining time. The put (for `S₀ ≥ 0`, any strike) and the
  call (for `∫ eˣ dν < ∞`, any `S₀` and `K`) are instances. The call no longer goes through
  put–call parity, the put no longer needs `K ≥ 0`, and the call no longer needs `S₀, K ≥ 0`.
- Coherence: put–call parity of the price functions comes from the payoff identity
  `max_sub_max_neg` of the finite-state parity (`Foundations/NoArbitrageDerivations.lean`). The
  canonical model's count–size independence comes from Mathlib's
  `indepFun_iff_hasLaw_prodMk_prod`; the repo's measure-preserving pull-back lemma is deleted.
  `[IsProbabilityMeasure P]` is derived from the process (`JumpDiffusionProcess.isProbabilityMeasure`)
  on six statements, and the log-return is a named function (`jumpDiffusionLogReturn`).

Safe wording: "given the information at `t`, a European payoff at `T` is the payoff averaged over
the remaining log-return, started from the current state; the step is Shreve's independence lemma,
proved for integrable payoffs". Not covered: path-dependent payoffs and random times (the strong
Markov property); the existence of the process with jumps.

### Coherence bridges: Brownian motion without jumps; Merton's model exists (2026-10-08)

Four entries added, all `full`: `mf-jump-diffusion-brownian-no-jumps`, `mf-bs-formulas-every-date`,
`gir-risk-neutral-drift-unique` and `mf-merton-model-exists`. Corpus 480 → 484.

- With rate `0` the jump-diffusion log-return is `N(bτ, σ²τ)` (`jumpDiffusionIncrementLaw_zero`),
  so for a filtered pre-Brownian motion `B` the log-price `bt + σB_t` is a `JumpDiffusionProcess`
  (`IsFilteredPreBrownian.jumpDiffusionProcess`, `BlackScholes/JumpDiffusionBrownian.lean`). The
  Brownian motion constructed on path space for the American-put development
  (`brownian_filtered`) makes the structure satisfiable without jumps
  (`jumpDiffusionProcess_brownian`).
- The process-level jump results then specialize to the Black–Scholes model driven by a Brownian
  motion: the discounted price is a martingale if and only if `b = r − σ²/2`
  (`IsFilteredPreBrownian.martingale_discounted_iff`, whose "if" direction is
  `discountedGBM_isMartingale` of `gir-continuous-ftap`), and the conditional values of the call
  and the put before maturity are the Black–Scholes formulas at the current price and the
  remaining maturity (`IsFilteredPreBrownian.condExp_call_eq_bsV`,
  `IsFilteredPreBrownian.condExp_put_eq_bsPut`).
- A `JumpDiffusionHyp` model whose first log-jump is `N(log(1 + k) − δ²/2, δ²)` is a Merton model
  (`JumpDiffusionHyp.toMertonHyp`), and the canonical model with that jump law gives a `MertonHyp`
  (`mertonHyp_canonical`), so the Merton entries' hypotheses can be met.

Safe wording: "Brownian motion with drift is a jump-diffusion process without jumps, so the
jump-diffusion process results contain the Black–Scholes model at every date before maturity, and
Merton's model exists". Not covered: a jump-diffusion process with jumps (`Λ > 0`); `MertonHyp` as
an instance of `JumpDiffusionHyp` (its jumps are only a.e.-measurable).

### Gaussian smoothing; Merton's 1976 series from the general route, at every date (2026-10-08)

Three entries added, all `full`: `mf-bs-gaussian-smoothing`, `mf-merton-from-general-jump-law` and
`mf-jump-diffusion-merton-1976-every-date`. Corpus 477 → 480.

- Gaussian smoothing of the Black–Scholes price (`BlackScholes/GaussianSmoothing.lean`): for
  `G ∼ N(m, v)`, `𝔼[C_BS(Se^G; σ)] = C_BS(Se^{m + v/2}; √(σ² + v/T))`
  (`integral_bsV_mul_exp_gaussianReal`, with the volatility characterised by `σ'²T = σ²T + v` in
  `integral_bsV_mul_exp_gaussianReal_of_sq`). The proof reads the average as a call through the
  mixing formula and adds the Gaussian log-shocks.
- Merton's series from the general route (`BlackScholes/JumpDiffusionMerton.lean`): with
  log-jumps `N(log(1 + k) − δ²/2, δ²)` and the compensator `kΛ`, the general-law formula and
  Gaussian smoothing give `mertonCallPrice` (`JumpDiffusionHyp.call_eq_mertonCallPrice`). The two
  Merton towers now reach the same series. `MertonHyp` is still not an instance of
  `JumpDiffusionHyp` (its jumps are only a.e.-measurable), so `merton_call_formula` keeps its own
  proof.
- Merton's 1976 formula at every date: with Gaussian jumps at the compensated drift
  `b = r − σ²/2 − Λk`, the call price function is `mertonCallPrice` at the expected jump count
  `Λτ` (`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`), and for `t < T` the conditional
  call value given `𝓕_t` is `mertonCallPrice` at `S_t`, `T − t` and `Λ(T − t)`
  (`JumpDiffusionProcess.condExp_call_eq_mertonCallPrice`). The put follows from the two
  put–call parities: `jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice` and
  `JumpDiffusionProcess.condExp_put_eq_mertonPutPrice` give `mertonPutPrice`.

Safe wording: "averaging a Black–Scholes call over a lognormal spot factor is a Black–Scholes call
at the shifted spot and the enlarged volatility; with lognormal jumps the general jump-diffusion
formula is Merton's 1976 series, and in a log-price process with independent jump-diffusion
increments, at the compensated drift `b = r − σ²/2 − Λk`, it is the conditional value of the call
and the put at every date before maturity". Not covered: the existence of the process with jumps;
`MertonHyp` as an instance of `JumpDiffusionHyp`.

### Prices at every date; Merton's formula and the implied-volatility lift at every date (2026-10-08)

Five entries added, all `full`: `mf-jump-diffusion-price-parity`,
`mf-jump-diffusion-put-intermediate-date`, `mf-jump-diffusion-call-intermediate-date`,
`mf-jump-diffusion-merton-intermediate-date` and `mf-jump-diffusion-implied-vol-every-date`.
Corpus 472 → 477.

- The price functions (`BlackScholes/JumpDiffusionOptionPrices.lean`): `jumpDiffusionPutPrice` and
  `jumpDiffusionCallPrice` are the discounted expected payoffs `e^{−rτ}(K − Se^Y)⁺` and
  `e^{−rτ}(Se^Y − K)⁺` against the log-return law over `τ`. They satisfy put–call parity
  `C = P + S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ} − Ke^{−rτ}` (`jumpDiffusionCallPrice_eq`), which
  is `C = P + S − Ke^{−rτ}` at the compensated drift (`jumpDiffusionCallPrice_eq_of_compensated`).
- Prices at an intermediate date, for any drift: given `𝓕_t`, the discounted put and call payoffs
  at `T` have conditional expectations `P(S_t, T − t)` and `C(S_t, T − t)`
  (`JumpDiffusionProcess.condExp_put`, `JumpDiffusionProcess.condExp_call`). Both are instances
  of `JumpDiffusionProcess.condExp_comp`, the conditional freezing lemma applied to the process
  (see the 484 → 486 section): `X_t` is known at `t`, and the increment is independent of `𝓕_t`.
  At the compensated drift `P` is a martingale measure, so these are arbitrage-free prices, the
  ones under `P`. With jumps they are in general not the only ones, which is not formalized for
  the process; at one date, compensated laws are already not unique
  (`exists_call_esscher_ne_merton`). At any other drift they are only
  `P`-conditional expectations.
- Merton's formula at every date: at the compensated drift the call price function is the call of
  the canonical model with expected jump count `Λτ` (`jumpDiffusionCallPrice_eq_canonical`), so it
  is the
  `Poisson(Λτ)` mixture of Black–Scholes prices averaged over `ν^ℕ`
  (`jumpDiffusionCallPrice_eq_merton`). For `t < T`, `𝔼[e^{−r(T−t)}(S_T − K)⁺ | 𝓕_t]` is that
  formula at `S_t` and `T − t` (`JumpDiffusionProcess.condExp_call_eq_merton`).
- The implied-volatility lift at every date: with `Λ > 0` and a jump law other than `δ₀`, the
  price function has a unique Black–Scholes implied volatility, above `σ`
  (`jumpDiffusionCallPrice_impliedVol_gt`, from `JumpDiffusionHyp.impliedVol_gt` on the canonical
  model). So for `t < T`, almost surely, the conditional call value has a unique implied
  volatility at `S_t` and `T − t`, above `σ` (`JumpDiffusionProcess.condExp_call_impliedVol_gt`).

Safe wording: "for a log-price process with independent jump-diffusion increments, the
conditional value of a European put or call at any date is its price function at the current
spot and the remaining maturity; at the compensated drift the call's is Merton's formula for the
jump law, and once jumps occur and move the price its implied volatility is almost surely above
`σ` at each date before maturity and each positive strike". Not covered: the existence of such a
process with jumps, its path regularity, and a measurable choice of the implied volatility as a
random variable (the statement holds path by path, almost surely, with a null set that may depend
on the strike and the dates).

### The jump-diffusion model exists; its price process (2026-10-08)

Five entries added, all `full`: `mf-jump-diffusion-model-exists`,
`mf-jump-diffusion-call-law-invariance`, `mf-jump-diffusion-log-return-mgf`,
`mf-jump-diffusion-discounted-price-martingale` and `mart-exp-indep-increments`. Corpus 467 → 472.

- The model exists, `jumpDiffusionHyp_canonical` (`BlackScholes/JumpDiffusionCanonical.lean`):
  for every expected jump count `Λ` and every jump law `ν`, the coordinates of `ℝ × ℕ × (ℕ → ℝ)`
  under `N(0, 1) ⊗ Poisson(Λ) ⊗ ν^ℕ` satisfy `JumpDiffusionHyp`, with jumps of law `ν`.
  `JumpDiffusionHyp` can therefore be discharged for any `Λ` and `ν`; the remaining hypotheses on
  the model are `∫ eˣ dν < ∞` (`integrable_exp_canonical_jump`) and, for the implied-volatility
  result, `Λ > 0` and `ν ≠ δ₀`. `MertonHyp` was witnessed later (`mertonHyp_canonical`).
- The call depends only on `Λ` and the jump law, `JumpDiffusionHyp.call_eq_integral_infinitePi`:
  on any model with `𝔼[e^{J₀}] < ∞`, for `S₀, K, σ, T > 0`, it is
  `∫ n, ∫ x, C_BS(S₀e^{−κ + ∑_{i<n} xᵢ}) dν^ℕ dPoisson(Λ)`, with `ν` the law of `J₀`.
- The price process, `BlackScholes/JumpDiffusionProcess.lean`: a log-price `X` on `[0, ∞)`,
  adapted, started at `0`, with increments independent of the past and distributed as a
  jump-diffusion log-return over the elapsed time (`JumpDiffusionProcess`). The log-return's
  exponential moment is `e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))τ}`
  (`integral_exp_jumpDiffusionIncrementLaw`), and the discounted price `e^{−rt}S₀e^{X_t}` is a
  martingale if and only if `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` (`JumpDiffusionProcess.martingale_iff`).
  The engine is `Foundations/ExpMartingaleIndepIncrements.martingale_exp_sub_of_indep_increments`:
  `e^{X_t − ψ(t)}` is a martingale when the increments are independent of the past with
  `𝔼[e^{X_t − X_s}] = e^{ψ(t) − ψ(s)}`.

Safe wording: "the compound-Poisson jump-diffusion model exists for every expected jump count and
jump law, its call price depends only on the expected jump count and the jump law, and a log-price process with
independent jump-diffusion increments has a martingale discounted price exactly at the compensated
drift". Not covered: the existence of such a process (a Lévy process up to path regularity;
constructing it needs a Kolmogorov extension or a construction from a Brownian motion and a
compound Poisson process) and its path regularity. Prices at intermediate dates came in the next
phase.

### Jumps lift the implied volatility (2026-10-08)

Six entries added, all `full`: `mf-bs-call-strictly-convex-in-spot`,
`mf-bs-call-tends-to-spot-high-vol`, `mf-implied-vol-exists-above-reference`,
`mf-jump-diffusion-call-strict-bounds`, `mf-jump-diffusion-implied-vol-above-sigma` and
`mf-compound-poisson-implied-vol-above-sigma`. Corpus 461 → 467.

- Strict bounds, `bsV_lt_jumpDiffusion_call` and `jumpDiffusion_call_lt`: a compensated jump part
  `Y` (`𝔼[e^Y] = 1`) that is not almost surely `0` puts the call strictly between `C_BS(S₀; σ)`
  and `S₀`. The lower bound is Jensen's inequality made strict
  (`Foundations/AffineMinorant.lt_integral_of_affine_lt`): the Black–Scholes price is strictly
  convex in the spot (`bsV_spot_strictConvexOn`, from positive gamma), so it lies strictly above
  its tangent away from `S₀` (`bsV_spot_tangent_lt`).
- The Black–Scholes side, in `BlackScholes/ImpliedVolatility.lean`: the call tends to the spot as
  `σ → ∞` (`tendsto_bsV_sigma_atTop`), so a price strictly between the Black–Scholes price at
  some `σ₀ > 0` and the spot has a unique positive implied volatility, and it is above `σ₀`
  (`exists_impliedVol_gt_of_bsV_lt`).
- Together, `jumpDiffusion_impliedVol_gt`: the jump-diffusion call has a unique Black–Scholes
  implied volatility, and it exceeds `σ`, at every positive strike and maturity, for any
  compensated jump part that is not almost surely `0`. For the compound-Poisson model at the
  compensator, `JumpDiffusionHyp.impliedVol_gt` needs, beyond `𝔼[e^J] < ∞`, only a positive
  expected jump count and a jump law that is not the point mass at `0`; under these the jump part
  is not almost surely `0` (`JumpDiffusionHyp.not_jumpPart_ae_eq_zero`).

Safe wording: "for a compensated jump-diffusion whose jump part is not almost surely zero, with
any jump law, the call has a unique Black–Scholes implied volatility, and it is strictly above the
diffusion volatility, at every strike and maturity". Not covered: how the implied volatility
varies with the strike (the shape of the smile); the `σ → 0` limit of the Black–Scholes price,
and with it implied-volatility existence across the whole no-arbitrage range; the put's implied
volatility (parity holds for the price functions, `jumpDiffusionCallPrice_eq_of_compensated`, but
the put's implied volatility is not stated).

### Jump-diffusions with an arbitrary jump law (2026-10-07)

Four entries added, all `full`: `mf-jump-diffusion-mixing-formula`,
`mf-jump-diffusion-call-dominates-bs`, `mf-jump-diffusion-compensator` and
`mf-merton-general-jump-law`. Corpus 457 → 461.

`BlackScholes/JumpDiffusionMixing.lean` drops the Gaussian jump law of `MertonModel`:

- the mixing formula, `jumpDiffusion_call_eq_integral_bsV`: for `Z ∼ N(0, 1)` and a jump part `Y`
  independent of `Z` with `𝔼[e^Y] < ∞`,
  `𝔼[e^{−rT}(S₀e^{(r−σ²/2)T + σ√T·Z + Y} − K)⁺] = 𝔼[C_BS(S₀e^Y)]`. With `Y` frozen at `y` the
  terminal price is a Black–Scholes terminal price at the spot `S₀e^y`, so the freezing lemma
  reduces the call to `bs_call_formula`.
- jump risk is never free, `bsV_le_jumpDiffusion_call` and `jumpDiffusion_call_le`: if
  `𝔼[e^Y] = 1`, the call lies between `C_BS(S₀)` and `S₀`, whatever the law of `Y`. The lower
  bound is Jensen's inequality for the Black–Scholes price, which is convex in the spot. Merton's
  lognormal case, `bsV_le_mertonCallPrice`, had needed a second (volatility) channel.
- the compensator, `JumpDiffusionHyp.discounted_terminal` and `discounted_terminal_eq_iff`: for
  the compound-Poisson jump part `−κ + ∑_{i<N} Jᵢ`, with i.i.d. `Jᵢ` of any law with
  `𝔼[e^J] < ∞`, `𝔼[e^{−rT}S_T] = S₀e^{−κ + Λ(𝔼[e^J] − 1)}`. This equals `S₀` exactly when
  `κ = Λ(𝔼[e^J] − 1)`.
- Merton's formula for a general jump law, `JumpDiffusionHyp.call_eq_integral_bsV` and
  `call_poisson_mixture`: the call is `𝔼[C_BS(S₀e^{−κ + ∑_{i<N} Jᵢ})]`, and with the count
  integrated out, `∫ n, 𝔼[C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})] ∂Poisson(Λ)`.

The model assumes the count independent of the diffusion sample and the jump sizes, and the
diffusion sample independent of the sizes. `Foundations/IndepFreezing.indepFun_prodMk_of_indepFun_prodMk`
re-associates this to "the diffusion sample is independent of the count and the sizes", so each
model-level statement is the single-jump-part theorem at `Y = −κ + ∑_{i<N} Jᵢ`. Integrating out a
countable variable is one lemma, `integral_comp_of_hasLaw_of_countable`, which the Merton prices,
the compound-Poisson MGF and the general-law formula all use (`Foundations/PoissonMaxima` still
conditions on its count by hand).

Safe wording: "the mixing formula, Black–Scholes and spot bounds for a compensated jump-diffusion
call, the compound-Poisson compensator, and Merton's Poisson-mixture formula for i.i.d. jumps of
any law with a finite exponential moment, at maturity". Not covered: closed forms for specific
non-Gaussian jump laws (Kou's double-exponential model needs its own integrals), the put and
put–call parity, the price process, and Lévy processes beyond compound Poisson. `MertonModel` is
not derived from this file: a `MertonHyp` is not a `JumpDiffusionHyp` as stated, because its jumps
are only a.e.-measurable.

### The Merton Greeks (2026-10-07)

Five entries added, all `full`: `mf-merton-delta`, `mf-merton-gamma`, `mf-merton-vega`,
`mf-merton-call-convex-in-spot` and `mf-merton-call-increasing-in-vol`. Corpus 452 → 457. These
are the statements issue #129 asks for.

`BlackScholes/MertonGreeks.lean` differentiates the Poisson series of Black–Scholes prices
`C(S) = ∑ₙ wₙ C_BS(S·cₙ, σₙ)` term by term (`hasDerivAt_tsum_of_isPreconnected`), with
`wₙ = e^{−Λ}Λⁿ/n!`, `cₙ = e^{−kΛ}(1 + k)ⁿ` and `σₙ = √(σ² + nδ²/T)`. For `K, σ, T > 0`, `k > −1`
and `S > 0`:

- delta: `∂C/∂S = ∑ₙ wₙ cₙ Φ(d₁ⁿ)`, with `0 < Δ < 1` (`hasDerivAt_mertonCallPrice_spot`,
  `mertonDelta_pos`, `mertonDelta_lt_one`). The upper bound is the compensation identity
  `∑ₙ wₙcₙ = 1` together with `Φ < 1`.
- gamma, stated for the price as the derivative of `deriv C`: `∑ₙ wₙ cₙ ϕ(d₁ⁿ)/(S σₙ √T) > 0`
  (`hasDerivAt_deriv_mertonCallPrice_spot`, `mertonGamma_pos`).
- vega: `∂C/∂σ = ∑ₙ wₙ S cₙ ϕ(d₁ⁿ) √T · σ/σₙ > 0` (`hasDerivAt_mertonCallPrice_sigma`,
  `mertonVega_pos`).
- shape: on `(0, ∞)` the price strictly increases and is strictly convex in `S`, and strictly
  increases in `σ` (`mertonCallPrice_strictMonoOn_spot`, `mertonCallPrice_strictConvexOn_spot`,
  `mertonCallPrice_strictMonoOn_sigma`).

Each term's derivative is dominated by `wₙcₙ` (delta), by `wₙcₙ/((S/2)σ√T)` near `S` (gamma,
since `ϕ ≤ 1` and `σₙ ≥ σ`), or by `wₙ S cₙ √T` (vega). These bounds are summable because the
weights `wₙcₙ` sum to one.

Safe wording: "the Merton call's delta, gamma and vega as Poisson mixtures of Black–Scholes Greeks,
with their signs and the shape of the price they imply". The Greeks are stated for
`mertonCallPrice`, which `merton_call_formula` identifies with the model's expectation at each
spot. Not covered: the put Greeks, theta and rho, and sensitivities to the jump parameters `k`,
`δ`, `Λ`.

### Merton's formula derived from the jump-diffusion (2026-10-07)

Five entries added, all `full`: `mf-merton-call-formula`, `mf-merton-put-formula`,
`mf-merton-discounted-terminal`, `mf-compound-poisson-mgf-random-count` and `ce-freezing-lemma`.
Corpus 447 → 452.

`mertonCallPrice` was a definition: the Poisson mixture `∫ n, C_BS(spot_n, vol_n) ∂Poisson(Λ)`.
`BlackScholes/MertonModel.lean` proves it is the price of the model. Under `MertonHyp`, a standard
normal `Z`, a jump count `N ∼ Poisson(Λ)` and i.i.d. log-jumps `Jᵢ ∼ N(log(1+k) − δ²/2, δ²)`,
mutually independent, the terminal price
`S_T = S₀ exp((r − σ²/2)T − kΛ + σ√T·Z + ∑_{i<N} Jᵢ)` has
`𝔼[e^{−rT}(S_T − K)⁺] = mertonCallPrice` (`merton_call_formula`), the put analogue
(`merton_put_formula`) and `𝔼[e^{−rT}S_T] = S₀` (`merton_discounted_terminal`). With `n` jumps the
total log-shock is a sum of independent Gaussians, so `S_T` is a Black–Scholes terminal price at
`mertonSpot n` and `mertonVol n` (`mertonTerminal_eq_bsTerminal`, `MertonHyp.hasLaw_mertonStd`);
the jump count is then integrated out by the freezing lemma.

The freezing lemma is `Foundations/IndepFreezing.integral_comp_prodMk_of_indepFun`:
`𝔼[g(X, Y)] = ∫ x, 𝔼[g(x, Y)] d(law X)` for independent `X`, `Y`, from Mathlib's
`IndepFun.map_prod_eq_prod_map_map` and `integral_prod`. Its second consumer closes a gap
`Actuarial/CompoundPoissonMGF.lean` used to declare: `compoundPoisson_mgf_of_indepFun` computes
`𝔼[exp(t·∑_{i<N} Xᵢ)] = exp(λ(M_X(t) − 1))` for a claim count that is a random variable
independent of the claims, where `mf-compound-poisson-mgf` integrated against the Poisson weights.

Safe wording: "Merton's 1976 option prices derived from the terminal law of the jump-diffusion".
Not covered: the price process `(S_t)` (a Brownian motion plus a compound-Poisson process) and the
martingale property of `e^{−rt}S_t` at intermediate dates; the conditional form of the freezing
lemma; closed forms for jump laws other than lognormal (the Poisson mixture for any law is
`mf-merton-general-jump-law`).

### Itô's formula for adapted coefficients (2026-10-05)

One entry added, `sc-ito-formula-adapted` (`full`). Corpus 446 → 447.

For `X_t = x₀ + ∫₀ᵗ b ds + ∫₀ᵗ σ dB` with `σ`, `b` bounded, adapted to the natural filtration of
`B` and with every path continuous, and `f ∈ C²` with `f'`, `f''` bounded,
`f(X_T) − f(x₀) = ∫₀ᵀ f'(X)σ dB + ∫₀ᵀ (f'(X) b + ½ f''(X) σ²) ds` almost surely
(`ItoFormulaAdapted.ito_formula_adapted`). This is the first Itô formula in the library for a
process that is not a function of `(t, B_t)`.

Safe wording: "Itô's formula at a fixed time for an Itô process with bounded adapted continuous
coefficients and `f` with bounded first and second derivatives". Not covered: unbounded `f'` or
`f''` (so not `exp` or `x²`), unbounded coefficients, time-dependent `f`, a random start, every
`t ≤ T` at once, a Brownian motion continuous only almost surely.

### The SVI tail condition (2026-10-05)

One entry added, `mf-svi-butterfly-free-sign-formula` (`full`). Corpus 445 → 446.

The strike-convexity certificate left out the large-strike behaviour. For raw SVI with `b ≥ 0`
and positive variance, `d₊(k) → −∞` as `k → ∞` exactly when the right wing slope `b(1+ρ)` is below
`2` (`tendsto_blackPlus_atBot_iff`), and the smiled call tends to `0` at large strikes exactly
when it is (`tendsto_bsSmile_zero_iff`). The call is also between `(1 − K)⁺` and `1`, tends to `1`
at strike `0`, and is nonincreasing once it is convex. So the strike-convexity formula with the
one further atom `2 − b(1+ρ) > 0` holds exactly when `σ ≥ 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is
positive and the smiled call is a normalised call price function (`IsNormalizedCallPrice`,
`butterflyFreeFormula_iff_isNormalizedCallPrice`). In the terms of Gatheral–Jacquier's Lemma 2.2
that is convexity of the call together with `d₊ → −∞` (`butterflyFreeFormula_iff`); convexity is
Durrleman's `g ≥ 0` for `σ > 0`, and at `σ = 0` only the convexity statement is proved.

The general pieces are in `BlackScholes/CallPriceFunction.lean` (the structure, and that a convex
function bounded above on a right-infinite interval is nonincreasing) and
`Foundations/NormalTail.lean` (the Mills bound).

Not proved: that a normalised call price function is the call price of a nonnegative random
variable of mean one, the last step of Roper's Theorem 2.1.

### A polynomial-sign certificate for raw SVI (2026-10-04)

New benchmark file `benchmarks/svi_certificate.json`, three entries, all `full`. Corpus 442 → 445.
The development is Robert Martin's
[ButterflyFreeSVI](https://github.com/robertmartin8/ButterflyFreeSVI), ported to
`MathFin/BlackScholes/SVI/` (42 modules) with statements unchanged; it answers #174.

| Benchmark ID | Mathematical conclusion | Lean declaration |
|---|---|---|
| `mf-svi-durrleman-sign-formula` | For `σ > 0`: a fixed finite Boolean combination of signs of polynomials in `(a, b, ρ, m, σ)` holds exactly when `b ≥ 0`, `ρ² ≤ 1`, the variance is positive everywhere and Durrleman's `g ≥ 0` everywhere. | `MathFin.SVI.fullCertificateFormula_iff` |
| `mf-svi-call-convex-iff-durrleman` | For `σ > 0` and positive variance: the Black–Scholes call with the SVI volatility substituted strike by strike is convex in strike iff `g ≥ 0` everywhere. | `MathFin.SVI.bsSmile_convex_iff` |
| `mf-svi-strike-convexity-sign-formula` | For `σ ≥ 0`: a fixed finite sign formula holds exactly when `b ≥ 0`, `ρ² ≤ 1`, the variance is positive everywhere and that call is convex in strike. | `MathFin.SVI.extendedCertificateFormula_iff_bsSmile_convex` |

The route: rationalise `g` to a polynomial of degree at most ten on `(0, ∞)`; nonnegativity there
is two endpoint signs and no positive critical point with a negative value; four Tarski queries
count those; each query is a signature of a Hermite matrix, by Hermite's trace-form identity,
proved here for any nonzero polynomial with no squarefreeness assumed.

What is not covered:
- No tail condition in these three entries: they characterise the Durrleman / strike-convexity
  domain. The tail condition is `mf-svi-butterfly-free-sign-formula`, above.
- Slices with zero variance at some log-strike are excluded.
- The formula is defined structurally and never expanded; its size is not stated.
- Nothing about calendar-spread arbitrage or surfaces.

### Riemann–Stieltjes sums against an Itô integral (2026-10-04)

One entry added, `sc-riemann-stieltjes-against-ito` (`full`). Corpus 441 → 442.

For `M = φ●B` and a bounded predictable weight `w` whose paths are almost surely continuous on
`[0, T]`, the sums `∑ₖ w(tₖ)(M_{tₖ₊₁} − M_{tₖ})` along the uniform partition of `[0, T]` converge
in mean square to `∫ w dM`, and `∫ w dM` is the Itô integral against `B` of a class equal to `φ·w`
almost everywhere (`Foundations/AdaptedRiemannStieltjes.lean`). This is the martingale part of the
first-order term of the planned adapted Itô formula, with `w = f'(X)`.

The route goes through `L²(⟨M⟩)` and does not freeze the driver. Each sum is the integral against
`M` of the left-endpoint step process of `w`. The step processes converge to `w` in `L²(⟨M⟩)` by
dominated convergence, and the isometry against `M` carries that to the integrals. So `φ` needs no
path regularity. Two lemmas of the adapted Riemann bridge, the step process's bound and its
convergence along a continuous path, were extracted so that both proofs share them.

Scope. Only uniform partitions and bounded weights are covered, and `M` is an `L²` class at each
time. The same change relaxes `sc-thm-7.4.5-adapted` and
`tendsto_weighted_qv_process_of_ae_continuous` once more, to weights whose paths are almost surely
continuous on `[0, T]` only: the library proves `itoContinuousMod` continuous on `[0, T]`, not
beyond.

### Quadratic variation of an Itô process with adapted coefficients (2026-10-03)

One entry added, `sc-thm-7.4.5-adapted` (`full`). Corpus 440 → 441.

`sc-thm-7.4.5` proves Theorem 7.4.5 for constant `σ`. The new entry proves it for `σ` bounded,
adapted to the natural Brownian filtration and continuous in time: for `X = X₀ + A + σ●B` with a
drift path `A` Lipschitz in time with one constant for every path, the squared-increment sums of `X`
along the uniform partition of `[0, T]` converge in `L¹` to `∫₀ᵀ σ_s² ds`. The weighted form,
`∑ₖ w(tₖ)(ΔXₖ)² → ∫₀ᵀ w σ² ds` for a bounded adapted weight whose paths are almost surely
continuous on `[0, T]`, is re-exported alongside. It has the shape of the second-order term of the planned adapted
Itô formula, and since 2026-10-04 its weight hypothesis is the one that formula's weight `f''(X)`
meets: adapted, with paths almost surely continuous on `[0, T]`. These are steps B1 and B2 of that
formula
(`docs/specs/2026-07-05-adapted-ito-formula-design.md`).

The proof splits `(ΔXₖ)²` around the frozen increment `σ(tₖ)ΔBₖ`. The freezing defects
`Dₖ = ΔMₖ − σ(tₖ)ΔBₖ` of `M = σ●B` are orthogonal Itô integrals whose sum is the error of the frozen
Riemann–Itô sum, so `∑ₖ ‖Dₖ‖² → 0` (`Foundations/AdaptedStochasticIntegralFreezing.lean`). What the
defects leave is the weighted quadratic variation of `B` with weight `w σ²`, which the tower already
had (`tendsto_weighted_qv_process`).

Scope. The convergence is in `L¹`, where `sc-thm-7.4.5` has `L²`: an `L²` bound on the freezing part
would need fourth moments of `σ●B`, which the tower does not have. Only uniform partitions are
covered, and the drift rate must be bounded. The drift is not assumed measurable; the integrals are
Bochner integrals, so the statement has content when its increments are. `X` need only agree with
`X₀ + A + σ●B` almost surely at each time of `[0, T]`.

### The integral against an Itô integral is a stochastic integral, in BrownianMotion's sense (2026-10-02)

One entry added, `sc-ito-is-stochastic-integral` (`full`). Corpus 439 → 440.

BrownianMotion's `StochasticIntegral.lean` characterises a stochastic integral axiomatically:
Riemann–Stieltjes values on elementary processes, linearity, indistinguishability and dominated
convergence (`IsRiemannStieltjesExtension`), plus agreement with every other such extension on the
common domain (`IsStochasticIntegral`). `Foundations/StochasticIntegralCharacterisation.lean` proves
that the integral against `M = φ●B` is one, for `M` stopped at `T` and the natural Brownian
filtration. BrownianMotion does not instantiate the predicate anywhere at the pin.

The domain is the processes indistinguishable from a predictable process square-integrable against
the bracket. That is forced rather than chosen: the predicate asks for a domain closed under
indistinguishability, and a process indistinguishable from a predictable one need not be
predictable, or even jointly measurable, whatever the filtration. The uniqueness clause is the
substantive part. An extension in the upstream sense is not assumed `L²`-continuous, so
`itoIntegralAgainst_unique` does not reach it; the proof is a monotone-class argument from
dominated convergence, through a Dynkin argument over the predictable rectangles, and it uses
nothing about `M`. Dominated convergence in `L^p`, which Mathlib at the pin has only for `p = 1`,
is proved on the way for every `p < ∞` and every measure
(`tendsto_eLpNorm_sub_of_dominated_convergence`).

Scope. The integrator is an Itô integral against a Brownian motion, not a general semimartingale.
As in the upstream `SIntegral`, the integral is the terminal value; the process `t ↦ ∫₀ᵗ` is not
part of the statement. The driver and the domain are `L²` objects: the localised domain
(`∫ X² d⟨M⟩ < ∞` almost surely) is not covered, and no maximality of the domain is claimed. `itoIntegralAgainst_unique`, uniqueness among continuous linear maps on
`L²(⟨M⟩)`, stays as a separate theorem with a different hypothesis.

### Quantitative risk management: quantiles, VaR for every law, ES for every integrable loss (2026-10-01)

New benchmark file `benchmarks/quantitative_risk_management.json`, drawn from McNeil, Frey and
Embrechts, *Quantitative Risk Management* (2015) and its exercise book (Hofert, Frey and McNeil,
2020). Every entry carries `formalization_status: full`.

The base layer is `Foundations/Quantile.lean`, the generalized inverse of a CDF, which Mathlib
does not have. Value-at-risk (`RiskMeasures/ValueAtRisk.lean`) is defined for every law, atoms included. The
expected-shortfall theorems hold for every integrable loss. The library's earlier Gaussian closed forms, which take a quantile
parameter `z`, are now theorems about the law at `z = Φ⁻¹(α)` (`qrm-gaussian-var-is-var`,
`qrm-gaussian-es`).

What is not covered:
- Sklar's theorem is proved for continuous margins only.
- The Clayton tail-dependence limit is a statement about the copula function; the Clayton
  measure is not constructed.
- Fisher–Tippett–Gnedenko and Pickands–Balkema–de Haan are not formalized. The extreme-value
  entries prove domain-of-attraction memberships by computation, max-stability, and the exact
  Poisson–GPD maximum law.
- The Basel IRB limit assumes the one-factor Gaussian threshold model with pairwise independent
  idiosyncratic terms.

| Benchmark ID | Mathematical conclusion | Lean module and declaration | Faithfulness |
|---|---|---|---|
| `qrm-quantile-transform` | For every probability measure μ on ℝ, its quantile function (the generalized inverse p ↦ inf{x | p ≤ F(x)} of the CDF) has law μ under the uniform law on (0, 1). | `MathFin/Foundations/Quantile.lean`, `MathFin.hasLaw_quantile` | `full` |
| `qrm-quantile-galois` | For p ∈ (0, 1) and any measure μ on ℝ, quantile μ p ≤ x ↔ p ≤ F_μ(x): the generalized inverse of the CDF is its lower adjoint, with no continuity or strict-monotonicity assumption. | `MathFin/Foundations/Quantile.lean`, `MathFin.quantile_le_iff` | `full` |
| `qrm-probability-integral-transform` | If X has law μ and the CDF F of μ is continuous, then F(X) is uniformly distributed on (0, 1). | `MathFin/Foundations/Quantile.lean`, `MathFin.hasLaw_cdf` | `full` |
| `qrm-quantile-equivariance` | For a probability measure μ, a monotone lower-semicontinuous h (e.g. continuous increasing) and p ∈ (0, 1): the p-quantile of the image law μ∘h⁻¹ is h(quantile μ p). | `MathFin/Foundations/Quantile.lean`, `MathFin.quantile_map` | `full` |
| `qrm-gaussian-quantile` | For p ∈ (0, 1), the p-quantile of N(m, v) is m + √v · Φ⁻¹(p), where Φ⁻¹ is the standard normal quantile function. | `MathFin/Foundations/NormalQuantile.lean`, `MathFin.quantile_gaussianReal` | `full` |
| `qrm-var-comonotone-additive` | For a loss factor Z and monotone lower-semicontinuous f, g, VaR_α(f(Z) + g(Z)) = VaR_α(f(Z)) + VaR_α(g(Z)) for every α ∈ (0, 1) (comonotone additivity in its common-factor form). | `MathFin/RiskMeasures/ValueAtRisk.lean`, `MathFin.valueAtRisk_add_of_comonotone` | `full` |
| `qrm-var-additive-linear-dependence` | For an a.e.-measurable loss X, α ∈ (0, 1), a ≥ 0 and b ∈ ℝ: VaR_α(X + (aX + b)) = VaR_α(X) + VaR_α(aX + b). | `MathFin/RiskMeasures/ValueAtRisk.lean`, `MathFin.valueAtRisk_add_affine` | `full` |
| `qrm-gaussian-var-is-var` | For a loss X ~ N(m, v) and α ∈ (0, 1), VaR_α(X) = gaussianVaR m √v (Φ⁻¹(α)) = m + √v·Φ⁻¹(α): the library's quantile-parametrized Gaussian closed form is the value-at-risk of the law. | `MathFin/RiskMeasures/GaussianValueAtRisk.lean`, `MathFin.valueAtRisk_of_hasLaw_gaussianReal` | `full` |
| `qrm-rockafellar-uryasev` | For an integrable loss X and α ∈ (0, 1), expected shortfall ES_α(X) = (1−α)⁻¹∫_α^1 VaR_u(X) du is the least value of c ↦ c + (1−α)⁻¹E[(X − c)⁺], and that value is attained (the minimizer c = VaR_α(X) is `rockafellarUryasev_valueAtRisk`). No continuity of the law is assumed. | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.isLeast_rockafellarUryasev` | `full` |
| `qrm-es-subadditive` | For integrable losses X, Y on one probability space and α ∈ (0, 1): ES_α(X + Y) ≤ ES_α(X) + ES_α(Y). | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.expectedShortfall_add_le` | `full` |
| `qrm-es-coherent` | For α ∈ (0, 1), X ↦ ES_α(X) satisfies the four coherence axioms (monotonicity, translation invariance, positive homogeneity, subadditivity) on the integrable losses of any probability space. | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.expectedShortfall_isCoherentRiskMeasure` | `full` |
| `qrm-es-acerbi-tasche` | For an integrable loss X, α ∈ (0, 1) and q = VaR_α(X): ES_α(X) = (1−α)⁻¹(E[X·1{X > q}] + q·(1 − α − P(X > q))), the correction term accounting for an atom at q. | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.expectedShortfall_eq_acerbiTasche` | `full` |
| `qrm-es-dual-representation` | For an integrable loss X and α ∈ (0, 1), ES_α(X) is the greatest value of E[D·X] over densities D with 0 ≤ D ≤ (1−α)⁻¹ a.s. and E[D] = 1; the maximum is attained. | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.isGreatest_integral_mul_expectedShortfall` | `full` |
| `qrm-es-monotone-level` | For an integrable loss X and 0 < α ≤ β < 1, ES_α(X) ≤ ES_β(X). | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.expectedShortfall_mono_level` | `full` |
| `qrm-es-adeh-representation` | On a finite probability space, X ↦ ES_α(−X) satisfies the ADEH axioms (IsCoherentRisk), so ES_α(−X) is the least upper bound of the expected losses ∑ qᵢ(−Xᵢ) over its representing probability vectors. | `MathFin/RiskMeasures/ExpectedShortfall.lean`, `MathFin.expectedShortfall_isLUB_representingSet` | `full` |
| `qrm-gaussian-es` | For a loss X ~ N(m, v) with v > 0 and α ∈ (0, 1): ES_α(X) = gaussianCVaR m √v (Φ⁻¹(α)) α = m + √v·ϕ(Φ⁻¹(α))/(1 − α). | `MathFin/RiskMeasures/GaussianExpectedShortfall.lean`, `MathFin.expectedShortfall_of_hasLaw_gaussianReal` | `full` |
| `qrm-var-bisection` | For any loss X, α ∈ (0, 1) and a bracket with P(X ≤ lo) < α ≤ P(X ≤ hi), bisection on x ↦ P(X ≤ x) against α converges to VaR_α(X) (with error at most (hi − lo)/2^(n+1) after n steps, abs_bisectMid_sub_valueAtRisk_le). | `MathFin/RiskMeasures/ValueAtRiskBisection.lean`, `MathFin.tendsto_bisectMid_valueAtRisk` | `full` |
| `qrm-var-superadditive-bernoulli` | For d independent Bernoulli(p) losses Y₁,…,Y_d (values in {0,1}, p ∈ (0,1)) and α ∈ (0, 1): ∑ VaR_α(Yᵢ) < VaR_α(∑ Yᵢ) if and only if (1 − p)^d < α ≤ 1 − p. So VaR is superadditive for such losses whenever d ≥ 2 and α lies in that range. | `MathFin/RiskMeasures/VaRSuperadditivity.lean`, `MathFin.valueAtRisk_sum_bernoulli_superadditive_iff` | `full` |
| `qrm-var-superadditive-pareto` | For independent L₁, L₂ with Pareto law F(x) = 1 − x^(−1/2) on [1, ∞) and every α ∈ (0, 1): VaR_α(L₁) + VaR_α(L₂) < VaR_α(L₁ + L₂). | `MathFin/RiskMeasures/VaRSuperadditivity.lean`, `MathFin.valueAtRisk_add_gt_of_paretoHalf` | `full` |
| `qrm-var-gaussian-subadditive-iff` | For a jointly Gaussian pair (X₁, X₂) whose covariance is strictly below √Var X₁·√Var X₂ and α ∈ (0, 1): VaR_α(X₁ + X₂) ≤ VaR_α(X₁) + VaR_α(X₂) if and only if α ≥ 1/2. | `MathFin/RiskMeasures/VaRSuperadditivity.lean`, `MathFin.valueAtRisk_add_le_iff_of_hasGaussianLaw` | `full` |
| `qrm-es-exponential` | For X ~ Exp(r) (r > 0) and α ∈ (0, 1): ES_α(X) = (1 − log(1 − α))/r (the VaR is `valueAtRisk_of_hasLaw_expMeasure`: −log(1 − α)/r). | `MathFin/RiskMeasures/RiskClosedForms.lean`, `MathFin.expectedShortfall_of_hasLaw_expMeasure` | `full` |
| `qrm-es-var-ratio-exponential` | For X ~ Exp(r), ES_α(X)/VaR_α(X) → 1 as α → 1⁻ (light tail). | `MathFin/RiskMeasures/RiskClosedForms.lean`, `MathFin.tendsto_expectedShortfall_div_valueAtRisk_expMeasure` | `full` |
| `qrm-es-lomax` | For X with Lomax law F(x) = 1 − (κ/(κ + x))^θ, θ > 1, κ > 0 and α ∈ (0, 1): ES_α(X) = κ(θ/(θ − 1)·(1 − α)^(−1/θ) − 1). | `MathFin/RiskMeasures/RiskClosedForms.lean`, `MathFin.expectedShortfall_of_hasLaw_lomaxMeasure` | `full` |
| `qrm-es-var-ratio-pareto` | For X with Lomax law (θ > 1, κ > 0), ES_α(X)/VaR_α(X) → θ/(θ − 1) as α → 1⁻: the heavy tail is visible in the shortfall-to-quantile ratio. | `MathFin/RiskMeasures/RiskClosedForms.lean`, `MathFin.tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure` | `full` |
| `qrm-median-shortfall` | For a loss with continuous CDF and α ∈ (0, 1), the median of the conditional law of X given X > VaR_α(X) equals VaR_{(1+α)/2}(X). | `MathFin/RiskMeasures/RiskClosedForms.lean`, `MathFin.medianShortfall_eq_valueAtRisk` | `full` |
| `qrm-var-elicitable` | For α ∈ (0, 1), the pinball loss (𝟙{y ≤ x} − α)(x − y) strictly elicits the α-quantile on the probability measures with finite mean whose α-quantile is unique (CDF > α right after it): the quantile is the unique minimizer of the expected score. | `MathFin/RiskMeasures/Elicitability.lean`, `MathFin.strictlyElicits_pinballLoss` | `full` |
| `qrm-es-not-elicitable` | For every α ∈ (0, 1), no scoring function with finite expected score under every law in the class elicits ES_α on the probability measures with finite mean: δ₀ and ((1+α)/2)δ₋₁ + ((1−α)/2)δ₁ both have ES_α = 0 while their mixture (1−α)δ₀ + α·(second law) has ES_α = α/2, so the level set is not convex. | `MathFin/RiskMeasures/Elicitability.lean`, `MathFin.not_isElicitable_expectedShortfall_integrable` | `full` |
| `qrm-frechet-lower-not-copula` | For an index type with at least three elements, no copula (probability measure on ℝ^ι with uniform coordinates) has distribution function u ↦ max(∑ uᵢ − (d − 1), 0) on [0, 1]^ι. | `MathFin/Foundations/Copula.lean`, `MathFin.not_exists_isCopula_frechetLower` | `full` |
| `qrm-frechet-hoeffding-lower` | For every copula C on ℝ^ι and u ∈ [0, 1]^ι: ∑ uᵢ − (d − 1) ≤ C(U ≤ u). | `MathFin/Foundations/Copula.lean`, `MathFin.IsCopula.sum_sub_le_measureReal_Iic` | `full` |
| `qrm-sklar-existence-copula` | For a random vector X whose marginal CDFs are continuous, the joint law of the probability-integral transforms (F₁(X₁), …, F_d(X_d)) is a copula (probability measure with uniform coordinates). | `MathFin/Foundations/Sklar.lean`, `MathFin.isCopula_copulaOf` | `full` |
| `qrm-sklar-representation` | For a random vector X with continuous marginal CDFs F_i: P(X ≤ x) = C(F₁(x₁), …, F_d(x_d)) for all x, where C is the copula of X (continuous-margins case of Sklar's theorem). | `MathFin/Foundations/Sklar.lean`, `MathFin.measureReal_le_eq_copulaOf` | `full` |
| `qrm-sklar-uniqueness` | For a random vector X with continuous marginal CDFs, any copula C with P(X ≤ x) = C(F₁(x₁), …, F_d(x_d)) for all x equals the copula of X. | `MathFin/Foundations/Sklar.lean`, `MathFin.eq_copulaOf_of_measureReal_le` | `full` |
| `qrm-copula-invariance` | For a random vector X and strictly increasing T₁, …, T_d, the joint law of the probability-integral transforms of (T₁(X₁), …, T_d(X_d)) (copulaOf, a copula when the margins are continuous) equals that of X. | `MathFin/Foundations/Sklar.lean`, `MathFin.copulaOf_comp_strictMono` | `full` |
| `qrm-fgm-copula` | The function uv + θuv(1 − u)(1 − v) is the distribution function on [0, 1]² of some bivariate copula if and only if |θ| ≤ 1. | `MathFin/Foundations/CopulaFamilies.lean`, `MathFin.exists_isCopula_fgm_iff` | `full` |
| `qrm-fgm-spearman` | For |θ| ≤ 1, Spearman's rho (12E[U₀U₁] − 3) of the FGM copula is θ/3, so the family only reaches rank correlations in [−1/3, 1/3]. | `MathFin/Foundations/CopulaFamilies.lean`, `MathFin.spearmanRho_fgmCopula` | `full` |
| `qrm-clayton-tail-dependence` | For θ > 0 the Clayton copula function C_θ(u, u) = (2u^(−θ) − 1)^(−1/θ) satisfies C_θ(u, u)/u → 2^(−1/θ) as u → 0⁺ (lower tail dependence coefficient), proved at the level of the copula function. | `MathFin/Foundations/CopulaFamilies.lean`, `MathFin.tendsto_claytonCopulaFun_diag_div` | `full` |
| `qrm-hoeffding-covariance` | For square-integrable X, Y: cov(X, Y) = ∫∫ (P(X ≤ s, Y ≤ t) − P(X ≤ s)P(Y ≤ t)) ds dt. | `MathFin/Foundations/HoeffdingCovariance.lean`, `MathFin.covariance_eq_integral_cdf` | `full` |
| `qrm-covariance-ordering` | For two square-integrable pairs with the same marginal laws whose joint distribution functions are pointwise ordered, their covariances are ordered the same way. | `MathFin/Foundations/HoeffdingCovariance.lean`, `MathFin.covariance_le_covariance_of_cdf_le` | `full` |
| `qrm-default-correlation-bound` | For events A, B: cov(1_A, 1_B) ≤ min(P(A), P(B)) − P(A)P(B) (the comonotone Fréchet bound for default indicators). | `MathFin/Foundations/HoeffdingCovariance.lean`, `MathFin.covariance_indicator_one_le` | `full` |
| `qrm-marshall-olkin-survival` | For independent exponential T₁, T₂, T₃ with rates λ₁, λ₂, λ₃ and Xⱼ = min(Tⱼ, T₃): P(X₁ > s, X₂ > t) = exp(−λ₁s − λ₂t − λ₃ max(s, t)) for s, t ≥ 0. | `MathFin/Foundations/MarshallOlkin.lean`, `MathFin.marshallOlkin_survival` | `full` |
| `qrm-marshall-olkin-ftd` | In the Marshall–Olkin model with all three rates positive, the first-to-default spread −log P(min(X₁, X₂) > t)/t (equal to λ₁ + λ₂ + λ₃, `marshallOlkin_firstToDefault_spread`) is strictly below the sum of the single-name spreads (λ₁ + λ₃) + (λ₂ + λ₃). | `MathFin/Foundations/MarshallOlkin.lean`, `MathFin.marshallOlkin_firstToDefault_spread_lt` | `full` |
| `qrm-correlation-fallacy` | There exist random variables Z, Y, both N(0, 1), with cov(Z, Y) = 0 that are not independent, not jointly Gaussian, and whose sum is not Gaussian (Y = V·Z with an independent random sign V). | `MathFin/Foundations/CorrelationFallacies.lean`, `MathFin.exists_gaussian_uncorrelated_not_indepFun` | `full` |
| `qrm-evt-poisson-approximation` | For a nonnegative F, thresholds uₙ and h > 0: F(uₙ)ⁿ → h if and only if n(1 − F(uₙ)) → −log h. | `MathFin/Foundations/ExtremeValue.lean`, `MathFin.tendsto_pow_iff_tendsto_nat_mul_tail` | `full` |
| `qrm-gev-max-stable` | For every shape ξ, x and n ≥ 1: H_ξ(cₙx + dₙ)ⁿ = H_ξ(x) with the explicit normalizations gevNormScale ξ n and gevNormLoc ξ n. | `MathFin/Foundations/ExtremeValue.lean`, `MathFin.gevCDF_max_stable` | `full` |
| `qrm-exponential-gumbel-mda` | For r > 0 the exponential CDF lies in MDA(H₀) (witnessed by cₙ = 1/r, dₙ = log n/r): F(x/r + log n/r)ⁿ → exp(−e^(−x)). | `MathFin/Foundations/ExtremeValue.lean`, `MathFin.cdf_expMeasure_inMDA` | `full` |
| `qrm-gpd-mda` | For β > 0 and every ξ ∈ ℝ, the generalized Pareto distribution function G_{ξ,β} lies in MDA(H_ξ). | `MathFin/Foundations/GeneralizedPareto.lean`, `MathFin.gpdCDF_inMDA` | `full` |
| `qrm-gpd-mean-excess` | For the GPD law with ξ < 1, β > 0 and a threshold u ≥ 0 in the support: E[X − u | X > u] = (β + ξu)/(1 − ξ), linear in u. | `MathFin/Foundations/GeneralizedPareto.lean`, `MathFin.integral_sub_cond_gpdMeasure` | `full` |
| `qrm-poisson-gpd-gev` | For N ~ Poisson(λ) independent of iid GPD(ξ, β) losses Yᵢ (ξ ≠ 0), and x ≥ 0: P(max_{i<N} Yᵢ ≤ x) = H_ξ((x − μ)/σ) with σ = βλ^ξ, μ = β(λ^ξ − 1)/ξ. | `MathFin/Foundations/PoissonMaxima.lean`, `MathFin.measureReal_poisson_max_gpd` | `full` |
| `qrm-quantile-convergence` | If Xₙ → Y almost surely and the α-quantile of Y is unique (F_Y(x) > α for every x above it), then the α-quantiles of the laws of Xₙ converge to the α-quantile of the law of Y. | `MathFin/Foundations/QuantileConvergence.lean`, `MathFin.tendsto_quantile_of_tendsto_ae` | `full` |
| `qrm-bernoulli-mixture-moments` | For defaults Yᵢ = 1{Uᵢ ≤ Q} with Q ∈ [0, 1], Uᵢ iid uniform and independent of Q: the probability that every obligor in a set s defaults is E[Q^|s|]. | `MathFin/RiskMeasures/BernoulliMixture.lean`, `MathFin.measureReal_iInter_default_eq_integral_pow` | `full` |
| `qrm-default-correlation` | In the exchangeable Bernoulli mixture, the default correlation of two distinct obligors equals Var(Q)/(E[Q](1 − E[Q])) (hence is nonnegative, defaultCorrelation_nonneg). | `MathFin/RiskMeasures/BernoulliMixture.lean`, `MathFin.defaultCorrelation_eq` | `full` |
| `qrm-one-factor-pd` | For independent N(0, 1) factor F and idiosyncratic ε, π ∈ (0, 1) and ρ ∈ [0, 1]: P(√ρ F + √(1 − ρ) ε ≤ Φ⁻¹(π)) = π. | `MathFin/RiskMeasures/BernoulliMixture.lean`, `MathFin.oneFactor_measureReal_default` | `full` |
| `qrm-large-portfolio-lln` | In the one-factor Gaussian threshold model with pairwise independent N(0, 1) idiosyncratic terms (any factor F, any π, ρ < 1), the default fraction of the first m obligors converges almost surely to p(F) = Φ((Φ⁻¹(π) − √ρ F)/√(1 − ρ)). | `MathFin/RiskMeasures/VasicekIRB.lean`, `MathFin.tendsto_oneFactorLossFraction_ae` | `full` |
| `qrm-basel-irb-formula` | In the one-factor Gaussian threshold model (standard normal factor, pairwise independent standard normal idiosyncratic terms, α ∈ (0, 1), ρ < 1), VaR_α of the default fraction of the first m obligors converges as m → ∞ to Φ((Φ⁻¹(π) + √ρ·Φ⁻¹(α))/√(1 − ρ)) (asrfQuantile), the worst-case default rate at the core of the Basel IRB formula. Loss given default, expected-loss subtraction and the maturity adjustment are not modelled. | `MathFin/RiskMeasures/VasicekIRB.lean`, `MathFin.tendsto_valueAtRisk_oneFactorLossFraction` | `full` |
| `qrm-equicorrelation-psd` | For d ≥ 2, the matrix with ones on the diagonal and ρ off it is positive semidefinite if and only if −1/(d − 1) ≤ ρ ≤ 1. | `MathFin/Portfolio/Equicorrelation.lean`, `MathFin.posSemidef_equicorrelationMatrix_iff` | `full` |
| `qrm-var-optimal-is-markowitz` | For a Gaussian random vector X, α ∈ (1/2, 1) and a set S of weights with a common expected portfolio loss, w₀ minimizes VaR_α(∑ wᵢXᵢ) over S if and only if it minimizes the portfolio variance wᵀΣw over S. | `MathFin/Bridges/GaussianRiskMarkowitz.lean`, `MathFin.isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN` | `full` |
| `qrm-es-optimal-is-markowitz` | For a Gaussian random vector X, α ∈ (1/2, 1) and a set S of weights with a common expected portfolio loss, w₀ minimizes ES_α(∑ wᵢXᵢ) over S if and only if it minimizes the portfolio variance over S. | `MathFin/Bridges/GaussianRiskMarkowitz.lean`, `MathFin.isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN` | `full` |
| `qrm-var-subadditive-gaussian-portfolios` | For a Gaussian random vector X, α ∈ [1/2, 1) and weight vectors w, w': VaR_α(⟨w, X⟩ + ⟨w', X⟩) ≤ VaR_α(⟨w, X⟩) + VaR_α(⟨w', X⟩). | `MathFin/Bridges/GaussianRiskMarkowitz.lean`, `MathFin.valueAtRisk_portfolio_add_le` | `full` |
| `qrm-systematic-floor` | For a covariance kernel with variance v ≥ 0 and common covariance ρv (ρ ≤ 1) and fully invested weights, the portfolio variance is at least ρv (the identity Var(w) = v((1 − ρ)·HHI(w) + ρ) is `portfolioVarN_equicorrelated_of_sum_eq_one`). | `MathFin/Bridges/EquicorrelationConcentration.lean`, `MathFin.mul_le_portfolioVarN_equicorrelated` | `full` |
| `qrm-square-root-of-time` | For a geometric Brownian motion S_t = S₀exp((μ − σ²/2)t + σB_t) driven by a pre-Brownian motion and σ ≥ 0: the h-period log-loss −log(S_{t+h}/S_t) has VaR_α = −(μ − σ²/2)h + σ√h·Φ⁻¹(α), so the volatility term scales with √h. | `MathFin/Bridges/SquareRootOfTime.lean`, `MathFin.valueAtRisk_gbm_loss` | `full` |
| `qrm-expectile-exists-unique` | For an integrable loss Y and α ∈ (0, 1) there is exactly one e with α·E[(Y − e)⁺] = (1 − α)·E[(e − Y)⁺] (the α-expectile). | `MathFin/RiskMeasures/Expectile.lean`, `MathFin.existsUnique_expectileGap_eq_zero` | `full` |
| `qrm-expectile-monotone` | For an integrable loss Y and 0 < α ≤ β < 1, the α-expectile is at most the β-expectile. | `MathFin/RiskMeasures/Expectile.lean`, `MathFin.expectile_mono` | `full` |
| `qrm-covariance-cauchy-schwarz` | For square-integrable X, Y on a probability space: cov(X, Y) ≤ √Var X · √Var Y. | `MathFin/RiskMeasures/StandardDeviationPrinciple.lean`, `MathFin.covariance_le_sqrt_mul_sqrt` | `full` |
| `qrm-sd-principle-subadditive` | For k ≥ 0 and square-integrable X, Y: E[X + Y] + k·sd(X + Y) ≤ (E[X] + k·sd(X)) + (E[Y] + k·sd(Y)). | `MathFin/RiskMeasures/StandardDeviationPrinciple.lean`, `MathFin.stdDevPrinciple_add_le` | `full` |
| `qrm-sd-principle-not-monotone` | For k ≥ 0 and a loss B ≤ 0 equal to −1 with probability q > 0 and 0 otherwise, if q(1 + k²) < k² then E[B] + k·sd(B) > 0 = the principle's value at the zero loss, although B ≤ 0. | `MathFin/RiskMeasures/StandardDeviationPrinciple.lean`, `MathFin.stdDevPrinciple_not_monotone` | `full` |

Verification:
- The default `lake build` passed, including the curated `AxiomAudit.lean`, which gained 17
  headline guards, and the regenerated `AxiomAuditGen.lean` (450 guards).
- `lake lint` passed.
- The ledger reports 438 fresh, 0 stale and 0 missing entries; all 65 new entries were verified
  through the daemon.
- `pytest` passed 57/57.
- A three-agent values review (2026-10-01, `docs/values-review.md`) found ten prose overclaims,
  all corrected before verification.

### A price with a drift, and the integral against it (2026-09-29)

One entry added, `sc-ito-integral-against-drifted-price` (`full`). Corpus 373 → 374.

`Foundations/PricePathDrift.lean` adds `S = S₀ + ∫b ds + (σ●B)` next to the driftless
`MarketCompletenessInPrice.pricePath`, which is unchanged, so nothing downstream of it moves.
The drift is `driftContinuousMod`, the pathwise object the Girsanov track built. No second
time-integral is constructed. `∫ψ dS` is `gainsDrift`, the drift integral of `ψb` plus
`itoIntegralAgainstCLM`.

`gainsDrift_eq_setIntegral`, the entry, proves the gains are a.e. `∫₀ᵀ ψ(s,ω) b(s,ω) ds + ∫ψ dM`.
The Itô half holds by definition. The work is on the drift half: `driftContinuousMod_eq_setIntegral`
identifies the limit object for an `L²` integrand, and `ae_slice_of_ae_trim` moves the
`trim`-a.e. identity `toLp (ψb) = ψb` onto a.e. path. Predictability makes the set measurable,
which is what lets the two a.e. quantifiers swap. `pricePathDrift_eq_setIntegral` is the same
identification for the price itself.

`b = 0` recovers the driftless objects a.e. (`pricePathDrift_zero_drift`,
`gainsDrift_zero_drift`), not definitionally. `driftContinuousMod 0` is a `limUnder` along a chosen
approximating sequence, and nothing makes that sequence vanish pointwise.
`memLp_mul_zero_drift` shows the side condition holds for every holding at `b = 0`, so
`gainsDrift_zero_drift` discharges it rather than assuming it.

Scope. `ψb ∈ L²(trim)` is a hypothesis. Square-integrability against the bracket does not imply
it, and `L²` is more than a pathwise integral needs. It is what `driftContinuousMod`'s domain
asks for. The drift term also reads `ψ` where the bracket does not: a holding in `L²(σ²·trim)` is
determined only where `σ ≠ 0`, while `∫ψb ds` reads it wherever `b ≠ 0`. On `{σ = 0, b ≠ 0}` the
gains depend on the representative, not only on the class. That is the set where a drift can be
collected without risk. For a discounted price, no arbitrage forces `b = σλ` and then it is
null; nothing here assumes it.
With `b ≠ 0`, `S` is not a martingale under `μ`, and neither completeness in the drifted price
nor a pricing-measure statement is claimed.

### Library wrappers: the upstream theorems are axiom-pinned (2026-09-25)

No statement or proof changed. The 18 `library_wrapper` entries re-export a Mathlib or
BrownianMotion theorem and count as delivered, but both axiom audits skipped names declared
outside `MathFin/`. BrownianMotion has `sorry`s at the pin (314f04a, and the same eight below
at 0d5b6eb, the 2026-10-02 bump), and two wrapper
snippets import modules that contain one. `cm-thm-4.3.7` imports LocalMartingale, whose import
closure has six sorried declarations: `isStable_submartingale` (LocalMartingale),
`Submartingale.stoppedValue_min_ae_le_condExp` (OptionalSampling), and
`Submartingale.uniformIntegrable_stoppedValue`, `Martingale.ae_tendsto_limitProcess` and both
`Martingale.condExp_limitProcess_ae_eq` lemmas (UniformIntegrable). `cm-thm-4.3.9` imports
DoobLp, which has two: `integral_iSup_le_norm_rpow_le` and `integral_iSup_norm_rpow_le`. The
other wrapper snippets reach no sorried BrownianMotion module. Importing a module with a `sorry`
does not make a theorem depend on it; `#print axioms` settles that.

The 29 upstream constants that wrapper proofs cite are now listed in `UPSTREAM_CITATIONS`
(`tools/verify/axiom_audit_gen.py`) and pinned in `MathFin/AxiomAuditGen.lean`. In build.yml
run 36151826318, 24 matched the standard three axioms and five reported fewer. None depends on
`sorryAx`:

| Entry | Upstream theorem | Axioms |
|---|---|---|
| `cm-thm-4.3.7` | `MeasureTheory.Martingale.stoppedProcess_indicator` (BrownianMotion) | the standard three |
| `cm-thm-4.3.9` | `ProbabilityTheory.maximal_ineq_nonneg` (BrownianMotion) | the standard three |
| `bm-thm-5.1.5` | `ProbabilityTheory.IsPreBrownianReal.isMartingale` (BrownianMotion) | the standard three |
| `bm-thm-5.3.2` | `ProbabilityTheory.IsPreBrownianReal.memHolder_mk` (BrownianMotion) | the standard three |

The other 25 come from Mathlib or Lean core. Twenty use the standard three; `min_eq_left` uses
only `propext`, and `Eq.symm`, `LT.lt.ne'`, `Pi.add_apply` and `inferInstance` use none.

Five scope notes described BrownianMotion as it was at an older pin. Four cited that pin
(51807683), `cm-thm-4.3.7` and `cm-thm-4.3.9` cited `#print axioms` checks made there, and
`bm-thm-5.1.5` said "Axioms-clean." They now cite the guards and the current names (`IsPreBrownian`
became `IsPreBrownianReal`). `bm-prop-5.1.2` now cites Mathlib, where
`IsGaussianProcess.isPreBrownianReal_of_covariance` has moved. Reading the five against their
statements turned up four older imprecisions, now fixed:

- `bm-thm-5.1.5` holds for any filtration carrying `IsFilteredPreBrownian`. The natural
  filtration is one of them, but the entry does not instantiate it.
- `bm-thm-5.3.2`'s almost-sure path claim needs `IsBrownianReal.mk_ae_forall_eq`, not only
  `mk_ae_eq`.
- `cm-thm-4.3.7`'s indicator form agrees with M<sub>t∧τ</sub> on {τ > 0}.
- `cm-thm-4.3.9`'s description now states the sharp form the Lean proves.

A follow-up brought the Lean docstrings of four of these snippets (`bm-thm-5.3.2`,
`bm-prop-5.1.2`, `cm-thm-4.3.7`, `cm-thm-4.3.9`) in line with their scope notes. It also fixed
`bm-thm-5.3.2`'s description, which allowed β = 0, and `sc-thm-7.1.1`, whose description said
f ∈ C². That theorem assumes f′, f″ and f‴ exist and are bounded, and the description now says
so. Its scope now uses the current names. It notes that `ito_formula_unrestricted` proves the
localization to C³ in local-martingale form, and it cites `ito_formula_L2_bddDeriv_mk` for the
path-continuity hypothesis.

`test_library_wrapper_citations_are_pinned` keeps the list in step with the corpus. Every wrapper
entry needs a row, each listed name must still appear in its proof, and each must be pinned. The
test cannot see a name that a row leaves out; that is still a review item.

### Girsanov: independent increments, proved (2026-09-25)

The first of the two gaps named in the next section, joint independence of the increments, is
closed in Lean; the second, path continuity, is not. `isQBrownianMotion_of_expMartingale` now
concludes, for the process `Y` under `Q` on `[0, T]`:

1. `Y_0 = 0` almost surely;
2. `Y_t − Y_s ~ N(0, t − s)` for `s ≤ t ≤ T`;
3. `HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q`: for any `t₀ ≤ ⋯ ≤ tₙ` in `[0, T]`, the
   increments are jointly independent (Mathlib's definition).

Together these fix every finite-dimensional law of `Y` on `[0, T]` to that of a Brownian motion.
That implication is not itself proved here; on the whole time axis `ℝ≥0` it is Mathlib's
`HasIndepIncrements.isPreBrownianReal_of_hasLaw`. Neither path continuity nor independence of the
increments from `𝓕_s` is stated.

The proof extends the two-increment argument to `n` increments. By induction on `n`, the joint MGF
of the increments over `t₀ ≤ ⋯ ≤ tₙ` is the product of the Gaussian ones: the increments before
the last are `𝓕_{t_{n−1}}`-measurable and factor out of the conditional expectation given
`𝓕_{t_{n−1}}`, which is deterministic on the last increment. So every linear combination of the
increments is Gaussian with the diagonal variance, and `iIndepFun_iff_charFun_pi` turns that into
joint independence (`increments_iIndepFun_of_expMartingale`). `HasIndepIncrements.of_nat` reduces
the general statement to the first `N` increments of a monotone sequence
(`hasIndepIncrements_of_expMartingale`). The pairwise lemmas `increments_indepFun_of_expMartingale`
and `Btheta_increments_indepFun`, and the two-increment code they used, are removed: pairwise
independence is `iIndepFun.indepFun` of the joint statement. One lemma,
`map_eq_gaussianReal_of_mgf`, replaces three copies of the MGF-to-law argument.

The four Girsanov entries get the stronger conclusion through that one theorem. `gir-const-theta-qbm`,
`gir-simple-adapted`, `gir-thm-9.1.8` and `gir-thm-9.1.8-predictable` now state `HasIndepIncrements`
in place of the pairwise property, and their names, descriptions and scope notes say so. They stay
`full`, revising the criterion recorded in the next section, whose Brownian conclusion included
path continuity. Each derives from primitives zero start, `N(0, t − s)` increments and
`HasIndepIncrements` on `[0, T]`, which fix the finite-dimensional laws of a Brownian motion. That
is the level at which these entries assume Brownian motion for `B` itself (`IsPreBrownianReal` or
`IsFilteredPreBrownian`), and `bm-prop-5.1.2` counts `IsPreBrownianReal` as a Brownian motion
modulo continuity. Each description says that path continuity is not stated. `sc-thm-9.1.8`, the
general case under Novikov's condition, stays `reduced_core`.

Seven structure entries encoded "independent increments" the same pairwise way, and each now uses
`HasIndepIncrements`: the definitions `bm-def-5.1.1` (Brownian motion) and `cv-poisson-def`
(Poisson process), whose scope notes call them faithful encodings; the specifications
`bm-thm-5.1.7`, `bm-cor-5.3.4` and `bm-thm-5.3.5`, which assume the Brownian axioms;
`sc-thm-9.1.1`, whose assumed conclusion is Gaussian independent increments; and `sc-thm-9.1.8`,
which has both. The two definitions also move from the index `ℝ` to `ℝ≥0`: indexed by `ℝ`, the
Brownian increment law constrained negative times as well. The specifications keep the index `ℝ`,
over which their conclusions are stated. `pp-prop-3.3.6` keeps its pairwise hypothesis, which is
what its proof uses; assuming less makes its theorem stronger, not weaker.

### Girsanov: what the increment statements prove (2026-09-25)

*Partly superseded the same day by the section above: joint independence is now proved, path
continuity is still not stated, and the status question at the end of this section is settled
there.*

No statement or proof changed. Four `full` entries described their conclusion as "`B^θ` is a
`Q`-Brownian motion", two of them "in full". Each proves three properties of the drift-corrected
process under `Q`, on `[0, T]`:

1. `B^θ_0 = 0` almost surely;
2. `B^θ_t − B^θ_s ~ N(0, t − s)` for `s ≤ t ≤ T`;
3. `B^θ_t − B^θ_s` and `B^θ_v − B^θ_u` are independent for `s ≤ t ≤ u ≤ v ≤ T`.

The third is independence of two increments at a time. A Brownian motion also has jointly
independent increments, which fix its finite-dimensional law, and continuous paths. Neither is
stated. All four entries read the three properties off `isQBrownianMotion_of_expMartingale`
(`Foundations/ExpMartingaleQBrownian.lean`), whose conclusion has the same form.

| Benchmark ID | θ | Lean declaration |
|---|---|---|
| `gir-const-theta-qbm` | constant | `Btheta_isQBrownianMotion` |
| `gir-simple-adapted` | bounded, piecewise-constant adapted | `Btheta_simple_isQBrownianMotion` |
| `gir-thm-9.1.8` | bounded, continuous adapted | `Btheta_isQBrownianMotion_adapted` |
| `gir-thm-9.1.8-predictable` | bounded, predictable | `Btheta_isQBrownianMotion_predictable_of_bdd` |

Their names, descriptions, scope notes and snippet docstrings now state the three properties, and
so do the docstrings of the five Lean modules involved. The two Theorem 9.1.8 entries say in
`description` that the textbook conclusion is not derived in full. The same wording in the scope
of `gir-const-theta-marginal` and in the description and scope of `sc-thm-9.1.8` was corrected
with them, as were the notes further down this file. The declaration names still say
`isQBrownianMotion`; renaming them changes the API and is left for a separate decision.

The four entries stay `full` for now. By the vocabulary above, the two Theorem 9.1.8 entries are
narrower than the textbook theorem, whose conclusion is a Brownian motion, so they meet the
`reduced_core` definition unless the gap is closed in Lean. The hypothesis `IsExpQMartingale`
already fixes the conditional MGF of `Y_t − Y_s` given all of `𝓕_s`, so the missing step is to
show that a deterministic conditional MGF makes the increment independent of `𝓕_s`. Joint
independence of the increments over any partition then follows by induction, since the earlier
increments are `𝓕_s`-measurable.

### Higher derivatives are stated for the price (2026-09-18)

No entries were added. Twenty `full` entries now state a stronger theorem:

- the Greeks: the put, Black-76, Bachelier, digital and BS-Merton gammas, vanna, volga,
  charm, and both speeds;
- the call and put second strike derivatives, and Breeden–Litzenberger;
- the two bond second-order entries, the zero-coupon duration and convexity, and the
  Almgren–Chriss Euler–Lagrange equation;
- the gamma conjunct of `sc-bs-pde`.

Each used to differentiate an explicit lower-order formula, for example `∂_S Φ(d₁)`
rather than `∂²V/∂S²`. Its description named the higher derivative through a composition
with another result. The zero-coupon pair was weaker still: each stated a cancellation,
`(c·B)/B = c`, and was described as a derivative. Now each states the derivative of the
price itself: `HasDerivAt (deriv V) …`, `s ↦ deriv (V s) y` for a mixed partial, or
`deriv` inside the ratio. One congruence lemma, `hasDerivAt_deriv_of_eventually` in
`Foundations/DerivOfDeriv.lean`, carries each formula-level result over. It applies because
the formula is the lower derivative on a neighbourhood of the point.

Charm now also assumes `K > 0` and `S > 0`, which its delta needs. Almgren–Chriss no
longer assumes `sinh(κT) ≠ 0`, which no derivative ever used.

Most formula lemmas are now private. `hasDerivAt_bsV_SS`, shared across three files, is
renamed `hasDerivAt_Phi_bsd1_S` for what it states. The names `breedenLitzenberger`,
`almgrenChrissPath_satisfies_EL` and `bondPortfolio_immunization_second_order` now label
the genuine theorems.

`bsV_strike_convexOn` and `bsV_spot_convexOn` use the new lemmas in place of four private
transport helpers. `lognormalTerminalPDF_nonneg_via_strike_convexity` now takes its sign
from the strike convexity it is named for. Before, its convexity step was an unused
`have`, so the `docs/open-problems.md` entry calling that route "already proved" was not
true until now.

The native default `lake build` passed (9215 jobs), including `AxiomAuditGen.lean` with
333 guards. Each changed snippet elaborated with no errors, warnings or `sorry`: the
twenty restated entries and `sc-bs-pde-feynman-kac`, whose module changed. `pytest`
passed 52/52 in the verify container. The change restaled 94 ledger rows, and
`ledger-sweep.yml` (`scope: stale`) re-verifies them on runners.

### Implied volatility by bisection: convergence (2026-09-18)

The new entry below carries `formalization_status: full`. The bisection
iteration is a (noncomputable) definition in the library, not an assumed
sequence, and the entry proves an explicit rate, not only a limit. The generic
method lives in `MathFin/Foundations/Bisection.lean`. Its convergence theorem
takes the limit point as an input, in the form bisection uses: `σ ∈ [lo, hi]` is
the threshold of `f` against the target, `f x < C ↔ x < σ` on the bracket. It
assumes neither continuity nor strictness. A strictly increasing `f` with
`f σ = C` satisfies it, and then `σ` is the root. For the Black–Scholes call
price,
`bsV_continuousOn_sigma` and the intermediate value theorem supply the root;
`bsV_strictMonoOn_sigma` makes it the threshold and the only positive implied
volatility.

| Benchmark ID | Mathematical conclusion | Lean module and declaration | Faithfulness |
|---|---|---|---|
| `mf-impliedvol-bisection` | For `K, S, T > 0`, any `r`, and a bracket `0 < σ_lo < σ_hi` with `bsV(σ_lo) < C_obs < bsV(σ_hi)`: an implied volatility `σ ∈ (σ_lo, σ_hi)` exists and is the only positive one; after `n` halvings (`n = 0` is the midpoint of `[σ_lo, σ_hi]`) the bisection estimate is within `(σ_hi − σ_lo)/2ⁿ⁺¹` of `σ`, and the estimates converge to `σ` | `MathFin/BlackScholes/BisectionIV.lean`, `MathFin.impliedVol_bisection_converges` (generic core: `MathFin/Foundations/Bisection.lean`) | `full` |

`mf-impliedvol-bracket`'s description used to call its lemma "the
bisection-method correctness statement". The lemma proves only that the bracket
contains exactly one root, so the description now says that and points here
for convergence. Its proof now consumes Mathlib's `intermediate_value_Ioo` for
existence and uses strict monotonicity only for uniqueness; the statement is
unchanged. The textbook bisection theorem for a merely continuous `f` with a
sign change (convergence to *some* root) is not formalized.

The native default `lake build` passed, including `AxiomAuditGen.lean` (now
333 guards), and `lake lint` passed. Both bisection entries re-verified through
the daemon; the ledger reports 373 fresh, 0 stale, and 0 missing entries. The
arithmetic is exact over `ℝ`: no floating-point error analysis or stopping rule
is claimed.

### American put option boundary: geometric contribution (#175)

The two new entries below carry `formalization_status: full`. Their hypotheses
are only `K > 0`, `r > 0`, `σ > 0`, and `0 ≤ q ≤ r`. They concern the
actual stopping boundary on the constructed completed usual Brownian
filtration, not an assumed pricing-equation solution. Their time domain is
`Set.Ioi 0`. See [the declaration and definition map](american-put-boundary.md)
for the model, proof, and source provenance.

| Benchmark ID | Mathematical conclusion | Lean module and declaration | Faithfulness |
|---|---|---|---|
| `mf-american-put-log-boundary-convex` | `log(B(τ)/K)` is convex in positive time-to-expiry | `MathFin/BlackScholes/AmericanPut/Stopping/PhysicalBoundaryConvexity.lean`, `MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualLogBoundary_convexOn` | `full` |
| `mf-american-put-stock-boundary-strict-convex` | `B(τ)` is strictly convex in positive time-to-expiry | Same module, `MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualStockBoundary_strictConvexOn` | `full` |

The native default `lake build` passed, including `AxiomAuditGen.lean` and
the curated audit. Both new benchmark statements passed native verification;
the ledger reports 372 fresh, 0 stale, and 0 missing entries. These checks
support the formal statements, not independent mathematical peer review. No `C²`
boundary regularity, classical curvature, strict log-convexity, or `q > r`
result is claimed by these entries. The dated baseline below records the
prior corpus audit, not a verification of this addition.

> **Live status (2026-09-18):** corpus
> **373**, **342 full + 18 wrappers = 360/373 delivery-ready**, 13 reduced cores, 0 placeholders.
> Ledger 373 fresh / 0 stale / 0 missing; `lake build MathFin` and `lake lint` green, `pytest`
> 59/59, `AxiomAuditGen` at 333 guards (243 curated). **Implied volatility by bisection** (above)
> is the newest round; the **American put exercise-boundary geometry** and the **Glosten–Milgrom
> spread** below precede it; the bracket
> compensator, the conditional bracket, the unconditional one, the **contracts tower**, the
> **Itô chain rule**, and its coherence pass follow.
>
> **2026-09-01 — adverse selection alone sets the spread (369 → 370).** A new section
> `MathFin/Execution/` opens with Glosten–Milgrom (1985). `Execution.spread_pos_of_model` proves
> `∫ V ∂μ[|buy] > ∫ V ∂μ[|sell]` from the trader mix — the informed event independent of the
> value, an informed trader buying exactly when the value is high, an uninformed trader tossing a
> coin. Corpus entry `mf-glosten-milgrom-spread-positive`.
>
> **The trade probabilities are derived, not posited.** `P(buy | V_H) = (1+p)/2` and
> `P(buy | V_L) = (1−p)/2` follow from the four primitives — the prior, the informed event
> independent of the value, informed traders trading on the value, uninformed traders tossing a
> coin — which is what makes this `full` rather than a restatement. They are stated additively
> (`2 · μ[B|H] = 1 + p`, `2 · μ[B|Hᶜ] + p = 1`) so that no step forms a difference in a type where
> subtraction truncates; the textbook form does follow from the additive one, so this buys the
> proofs, not the statements. The quotes are honest Bochner integrals: with the payoff written as
> a constant plus an indicator, integrability is one line and the asset cancels, leaving
> `(V_H − V_L)` times the gap between the posteriors.
>
> **The seam is the load-bearing part.** `cond_toReal_eq` is Bayes pushed through `.toReal` once
> and generically; it is what identifies the model's `μ[H | B]` with the real function `postBuy`
> the closed form is about, and the buy and sell sides are then the same lemma applied twice with
> the likelihoods swapped. Without it the measure-theoretic half and the real-analysis half are
> true statements about unrelated objects. `toReal` sends `∞ ↦ 0` and `x/0 ↦ 0`, so every
> conversion carries its `≠ ∞` side condition.
>
> **`0 < θ < 1` is a hypothesis issue #107's acceptance criterion omits, and the prior's two
> endpoints fail differently.** With `p < 1` a degenerate prior leaves nothing to be adversely
> selected: the posteriors coincide, the spread is exactly `0`, and `ask − bid > 0` is false. A
> degenerate prior with `p = 1` is worse, in two ways both machine-checked here: one trade event
> is null, and `quote_eq_zero_of_null` shows `cond` then returns the *zero measure*, whose
> integral is `0` — not a bad price but no price; and `spread_junk_at_corner` evaluates the closed
> form at `θ = 1, p = 1`, where it returns the **entire** `V_H − V_L`, the largest spread there
> could be, at the one point where the true spread is `0`, because `0/0 = 0`. Nothing errors in
> either case. `p = 1` on its own is admitted, not excluded — `spread_pos_of_model` derives
> `p ≤ 1` rather than assuming it, and at `p = 1` with `0 < θ < 1` both trade events still carry
> positive mass. It is the prior's endpoints that go. The derivation demands the hypothesis
> independently: the two trade probabilities need `μ H ≠ 0` and `μ Hᶜ ≠ 0`, so their hypotheses
> cannot be jointly satisfied without it. Two further hypotheses proved unnecessary and were
> removed rather than shipped:
> `p ≤ 1` is forced by `μ (H ∩ I) ≤ μ H`, and `μ H ≠ 0` in `postSell_eq` is forced by the trade
> probability itself.
>
> **The hypotheses are satisfiable, and that is a theorem.** A conjunction of measure-theoretic
> constraints proves nothing if no model meets it — the same failure this round is about, one
> level up. `MathFin/Execution/GlostenMilgromModel.lean` exhibits a six-point space (value high or
> low × informed or not × the uninformed trader's coin) discharging every hypothesis, symbolically
> in `θ` and `p`, so `spread_pos_witness` states the conclusion with no measure-theoretic
> hypothesis in front of it.
>
> **Not claimed, and this is the important half.** The competitive market maker is *not*
> formalized: `ask = E[V | buy]` and `bid = E[V | sell]` are posited by the shape of the
> conclusion, and Glosten–Milgrom's derivation of them from zero expected profit under competition
> is the assumed part. The sell event is modelled as `Bᶜ`, so there is no no-trade outcome — under
> the standard extension that admits one, `E[V | Bᶜ]` is not the bid. Nothing dynamic: no sequence
> of trades, no convergence of quotes to the true value. The model is two-valued and one-period,
> as in the paper's opening section.
>
> **2026-08-28 — the bracket is adapted, and it compensates `M²` (368 → 369).**
> `BracketCompensator.condExp_sq_sub_bracket` proves
> `𝔼[M_b² − ⟨M⟩_b | 𝓕_a] =ᵐ M_a² − ⟨M⟩_a` for `M = φ●B` on `[0,T]` — the property that makes
> `⟨M⟩` *the* compensator of `M²` rather than a formula with a suggestive name. Corpus entry
> `sc-bracket-compensator`.
>
> **The blocker it had to clear.** The 2026-08-27 entry below explicitly declined to claim the
> bracket adapted, because `⇑φ` is strongly measurable for the *predictable* σ-algebra, which
> mixes every `𝓕_s`. What is true is a **trace** statement: intersected with a band `(a,b] × Ω`,
> every predictable set is `Borel(ℝ≥0) ⊗ 𝓕_b`-measurable — on a generator `(c,d] × F` the *left*
> endpoint decides, either `c ≤ b` and `F ∈ 𝓕_c ⊆ 𝓕_b`, or `c > b` and the intersection is empty.
> Clamping the squared representative to the band makes it product-measurable at `b`; integrating
> the time variable out leaves an honestly `𝓕_b`-measurable function of `ω`
> (`measurable_bracketRep`, `bracketProcess_adapted`). With `⟨M⟩_a` adapted it splits off a
> conditional expectation, and the conditional bracket identity rearranges into the compensator
> statement.
>
> **Still not claimed.** No pathwise quadratic variation: nothing takes a limit of sums along
> partitions, so `⟨M⟩` is `∫φ²`, not `[M]`. And no bundled `Martingale` structure for
> `t ↦ M_t² − ⟨M⟩_t`: the `Lp`-valued `M` supplies only a.e. adaptedness, which `Martingale` does
> not accept. This is also not Doob–Meyer — existence and uniqueness of a compensator for a
> general submartingale is untouched. Also landed this round: `bracketRep_bandGen`, which
> evaluates the pathwise bracket of a band generator as `Z²·(d−c)` and so retires the one
> "true by inspection, not formalised" caveat the previous round shipped.
>
> **2026-08-27 — the bracket is conditional (367 → 368).**
> `PointwiseBracket.condExp_band_second_moment` proves
> `𝔼[(M_b − M_a)² | 𝓕_a] =ᵐ 𝔼[⟨M⟩_b − ⟨M⟩_a | 𝓕_a]` for `M = φ●B` on `[0,T]` and `a ≤ b ≤ T`,
> the refinement the 2026-08-24 entry below left open. The bracket increment is `bracketRep`,
> the ω-wise `∫_a^b φ_u(ω)² du` of the class's own predictable representative — nonnegative,
> band-additive (`bracketRep_add`), monotone. Corpus entry `sc-bracket-conditional`.
>
> **What it does not claim, stated where the claim is made.** `bracketRep` is **not** asserted
> adapted: predictability of the representative does not give progressive measurability at this
> pin, so the bracket is delivered through its increments' *conditional expectations*, not as an
> adapted increasing process — which is also why the right-hand side is `𝔼[⟨M⟩_b − ⟨M⟩_a | 𝓕_a]`
> rather than `⟨M⟩_b − ⟨M⟩_a` (that is the classical statement, the increment being
> `𝓕_b`-measurable). No pathwise quadratic variation is constructed: nothing in the file takes a
> limit of sums along partitions.
>
> **The route, because it replaced the planned one.** The design of record (2026-08-25, part 1)
> was pair identity → density of the post-`a` generators → ε-extension, roughly 800 lines. It was
> dropped: the identity *is* the Itô isometry localised. A conditional-expectation identity is an
> identity of `𝓕_a`-set integrals; on such a set `𝟙_F` is a bounded `𝓕_a`-measurable factor, so
> `itoIntegralCLM_T_smulAdapted` folds it back inside the integral, `𝟙_F² = 𝟙_F` costs nothing,
> and both set-integrals meet at `∫_{(a,b]×F} φ² d trim_T` — one side by the isometry, the other
> by Tonelli through the trim. About 200 lines, no density argument and no ε. The band generators
> and conditional Brownian kernels from part 1 stay: they state the classical facts the general
> theorem abstracts, and reach coefficients it cannot (integrable rather than bounded).
>
> **2026-08-24 — the bracket earns its name (#200; corpus unchanged at 367).**
> `ItoIntegralAgainstMartingale.norm_sq_increment_eq_bracket` proves the unconditional second
> moment `𝔼[(M_b − M_a)²] = ⟨M⟩((a,b] × Ω)` for `M = φ●B` — the defining property quadratic
> variation is for, at the level of expectations, so the `d⟨M⟩ = φ²·trim_T` reading of
> `bracketMeasure` is no longer only motivation. The conditional refinement
> (`𝔼[(M_b−M_a)² | 𝓕_a] = 𝔼[⟨M⟩_b − ⟨M⟩_a | 𝓕_a]`) was the next rung on this seam and landed
> 2026-08-27 (entry above); an *adapted* bracket process, and any pathwise quadratic variation,
> stay unclaimed. Supporting change:
> `itoIntegralCLM_T_bandRestrict` (`∫ 𝟙_{(a,b]}·φ dB = M_b − M_a`) extracted from
> `itoIntegralAgainst_elementary`, which now consumes it.
>
> **FIXED — the CRR→BS convergence theorems were vacuous as stated
> (found 2026-08-19, fixed 2026-08-20).** All three carried
> `hna : ∀ n, BinomialNoArb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)`,
> and no `(r, σ, T)` satisfies it: at `n = 0`, `crrStep T 0 = T / 0 = 0` (Lean
> division by zero), so `u = d = Real.exp 0 = 1` and `BinomialNoArb 1 1 0`
> demands `Real.exp 0 < 1`. Every theorem carrying it was vacuously true.
> Machine-checked: `¬ ∀ n, BinomialNoArb …` is provable for arbitrary `r σ T`.
>
> The hypothesis is now `∀ n, 0 < n → …`, which is all the limit ever consumed —
> both identity steps in the proof were already established eventually-in-`n`,
> and the only place needing `n = 0` was the `0 ≤ p ≤ 1` bound, which survives
> the degenerate step on its own (`crrProb_zero`). Restricting a hypothesis is
> not by itself evidence it can be met, so `MathFin.binomialNoArb_crr`
> (`MathFin/Binomial/CRRConvergence.lean`) proves it can: whenever
> `|r|·√T < σ`, every step with `n ≥ 1` is arbitrage-free, since
> `√(T/n) ≤ √T` bounds all of them at once. Both restrictions are necessary —
> `n = 0` is degenerate, and for a fixed `n` a large enough `|r|` pushes
> `e^{rΔt}` outside `[d, u]`. Affected
> `binomialPrice_call_tendsto_bs_closed`, `binomialPrice_call_tendsto_bs`,
> `tendsto_integral_put`, the entry `mf-crr-bs-call-convergence` (which keeps
> its `full` tier — the proof was always a real derivation; it is the statement
> that asserted nothing) and the README landmark row.
>
> Worth recording *why* nothing caught it: the proof never exploited the
> vacuity, so every gate passed honestly. The axiom audit, kernel replay, ledger
> freshness, the `sorry` scan, `lake build`, `lake lint` and even the
> prose-vs-statement gate are all satisfied by a vacuous statement — the last
> one compares prose against a statement that is itself empty. Soundness gates
> ask whether the proof is valid, and it was. Nothing asked whether the
> hypothesis was inhabited. It surfaced only because the Palomar submission
> (`docs/palomar.md`) forced the statement to be restated for an outside
> auditor in Mathlib alone.
>
> **2026-08-17 — the contracts tower: a reified payoff language, closed to Black–Scholes (358 →
> 367).** Five new modules under `MathFin/Contracts/`, nine entries `mf-contract-*`. `Core.lean`
> reifies a payoff as data — `Payoff ι` / `Contract ι` inductives over a **typed** underlying
> index `ι` (`ι = Unit` for the single-asset instances below), not the inline lambda every other
> payoff in the library is written as. `Adapted.lean` proves the reification pays for itself:
> `Payoff.measurable_eval_of_obsTimes_le` is the adaptedness hypothesis a `Payoff` will need to
> be a legitimate stochastic-integral integrand — `𝓕 u`-measurability follows from every
> observation time in `obsTimes` (a syntactic, sufficient-not-necessary over-approximation)
> being `≤ u`; **it still has no consumer**, since `Pricing.lean` integrates against a fixed
> measure, never a filtration. Its a.e.-measurable sibling `Payoff.aemeasurable_eval` does have
> one as of 2026-08-19: `CappedCall.lean`'s `integrable_europeanCall_pathPV` calls it directly,
> needing exactly the `AEMeasurable` strength `BSCallHyp` supplies rather than the `Measurable`
> its own unconditional sibling `Payoff.measurable_eval` proves — that one stays consumed only
> internally, by `aemeasurable_eval` on measurable representatives, not by `CappedCall.lean`.
> `Pricing.lean` integrates `pathPV` against a measure into `Contract.value`, proves it linear
> (`value_scale` unconditional, `value_both` needing both integrability hypotheses —
> `integral_add` is false without them), and proves `value_deliverAsset` /
> `value_process_martingale` from `Martingale.condExp_ae_eq` and `martingale_condExp` alone —
> deliberately **no** `IsEMM` hypothesis anywhere in the file, since neither theorem touches the
> mutual-absolute-continuity content (`ac`/`ac'`) that turns a martingale measure into an
> *equivalent* one. `BlackScholes.lean` and `CappedCall.lean` close the loop: `value_pay_eq`
> reduces `Contract.value` on any single-cashflow contract to exactly the payoff integral, so
> `value_europeanCall`/`value_europeanPut`/`value_digitalCall` reach `bs_call_formula` /
> `bs_put_formula` / `bs_cash_or_nothing_formula` by one `rw` each, and `value_cappedCall` reaches
> the bull-spread difference by **composing** `value_europeanCall` twice through
> `Contract.value_both`/`value_scale` — no third integral. `cappedCall_payoff_eq` is a separate
> theorem (`mf-contract-capped-call`) transporting the existing pointwise identity
> `cappedCall_eq_bull_spread` onto the composed contract's `pathPV`; it, not the definition's
> name, is what earns `cappedCall` its name, and the corpus keeps the payoff and value claims as
> two entries (`mf-contract-capped-call` / `mf-contract-capped-call-value`) rather than one that
> would silently attach the pricing result to whichever entry a reader opens first.
>
> **The honest ceiling, stated once for the whole tower.** `Payoff` is a finite inductive walked
> by `List`-valued `obsTimes`, so every instance here is a payoff kernel over a **finite**
> observation grid — no continuously-monitored barrier is expressible. Rung (c) (the
> `BlackScholes.lean`/`CappedCall.lean` reductions) is **single-asset**, `ι = Unit`, under the
> `BSCallHyp` hypothesis bundle each closed form already needed; nothing here prices under a
> model that is not separately assumed. The martingale rung (`value_deliverAsset`,
> `value_process_martingale`) is the **value process**, not the hedge: it does not identify
> `Contract.value` with the initial wealth of a replicating strategy (that primitive,
> `MarketCompletenessInPrice.exists_replicating_strategy_in_price`, landed on `main` the day
> before this round and is the natural next rung, deferred). And none of it is a term-sheet
> formalisation — no calendar, business-day convention, disruption, corporate action or issuer
> credit exists at any instantiation, and no entry's `description` or `formalization_scope`
> claims one. Consulted as a source, not a template: Bilokon, *The Contract Is Not the Model*
> (working paper, 2026); see `docs/sources.md` for what was taken and what was not. All nine
> entries axioms-clean, `full`. Net: corpus 358 → **367**, **327 full → 336 full** + 18 = 354/367
> delivery-ready, 13 reduced, 0 placeholders.
>
> **2026-08-17 — coherence pass over the chain-rule tower (corpus unchanged at 358).** No new
> entries; the round is about what the previous one asserted rather than proved.
>
> * **The uniqueness clause now says what it should.** The band identity is summed over a whole
>   simple process (`itoIntegralAgainst_simpleProcess`), so
>   `itoIntegralAgainst_unique_of_riemannStieltjes` takes agreement with the *written-out* sums
>   `∑ₚ V(p)·(M_{p.2} − M_{p.1})` — a hypothesis naming no stochastic integral — rather than
>   agreement with the object being characterised. Closes #195.
> * **A theorem that may have been vacuous is now known not to be.** `Martingale` requires
>   adaptedness pointwise; `pricePath`, built from `Lp` classes, supplies only its a.e. version,
>   so `PricingMeasureL2Density`'s martingale hypothesis had **no exhibited witness**. The
>   statements are now carried on an abstract adapted `S` agreeing a.e. with the price — the form
>   `ContinuousMarket.IsEMM` already used, for the same reason — and
>   `exists_density_price_martingale` supplies the witness via `pricePathCondExp`, the price
>   rebuilt from `μ[· | 𝓕_t]`. This is the price-side counterpart of `pricesGainsAtZero_self`.
>   Nothing in the gate stack could see this: the theorem was true, axiom-clean and green.
> * **A duplicated proof removed and a definition deduplicated.**
>   `ItoIntegralL2.uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero` states the band decomposition for
>   *any* measure charging the time origin nothing — generalised over the `MeasurableSpace` too,
>   which is the part that lets a trimmed measure reuse it. `elemIntegrand` became the primitive
>   and `rectTerm` its `rfl`-equal instance. Closes #197.
> * **A hypothesis deleted and one weakened.** `hDmeas : Measurable ⇑D` was derivable
>   (`Lp.stronglyMeasurable`) and was carried through five theorems and out into the corpus;
>   `hD` is now a.e. rather than pointwise. `lake lint` then found `bracketMeasure_mulLI`'s
>   `[IsProbabilityMeasure μ]` unused.
> * **`d⟨ψ●M⟩ = ψ² d⟨M⟩`** (`bracketMeasure_mulLI`): the construction is closed under itself.
> * **Prose corrected.** `bracketMeasure` is *defined* as `φ²·trim_T`; the repo constructs no
>   quadratic variation, so the identification with `d⟨M⟩` is motivation, and the docstrings and
>   `leaps.md` now say so. Earning the name is #200; #199 and #201 carry the other deferrals.
>
> **2026-08-16 — the chain rule, the integral against a price, and the pricing measure
> (353 → 358).** For a predictable `L²` driver `φ` and `M = φ●B`, the integrands
> square-integrable against `M` are the bracket-weighted `L²(φ²·trim_T)`, and
> `ItoIntegralAgainstMartingale.itoIntegralAgainstCLM` is `itoIntegralCLM_T` precomposed with
> multiplication by `φ`. Both factors are isometries, so `‖∫ψ dM‖ = ‖ψ‖_{L²(⟨M⟩)}` — the Itô
> isometry against `M`, and the reason the weighted space is the right domain. Five entries:
> `sc-ito-chain-rule` (`∫ψ dM = ∫ψφ dB`), `sc-ito-integral-band`
> (`∫ Z·1_{(a,b]} dM = Z·(M_b − M_a)`, the Riemann–Stieltjes agreement that identifies the
> construction), `sc-simple-dense-bracket` (simple processes dense in the weighted `L²`),
> `gir-replication-in-price`, `gir-pricing-measure-density`.
>
> **What changed for the pricing measure.** `gir-pricing-measure-unique` (2026-08-07) assumed
> `PricesGainsAtZero`. `gir-pricing-measure-density` **derives** it: for `S = S₀ + (σ●B)` with
> `σ ≠ 0` a.e., a probability measure `Q = D·μ` with `D ∈ L²(μ)` under which `S` is a
> martingale prices the traded gains at zero, hence agrees with `μ` on all of `𝓕ᴮ_T`. The
> functional `ψ ↦ 𝔼_Q[∫ψ dS]` is an inner product against the density composed with an
> isometry, so continuity is `innerSL`'s; it vanishes on a band because that integral is a
> bounded predictable weight against a `Q`-martingale increment, then on simple processes by
> linearity and the `Lp` band decomposition, then everywhere by density.
>
> **Scope, stated plainly, and unchanged where it was already honest.** Square-integrability of
> the density is not removable by this argument — it is exactly what buys continuity. The price
> is **driftless** by construction; a drift term is additive and is what the HJM bond dynamics
> need. `σ ≠ 0` a.e. is required (only that — no uniform lower bound; the weighted norm
> rescales). Only `complete ⟹ unique` is delivered, the Jacod–Yor converse being untouched, and
> the agreement `Q = μ` is **on `𝓕ᴮ_T`**, saying nothing off that σ-algebra. The single-band
> identity does **not** come with a stated summed version over a general simple process: what
> exists is the `Lp` decomposition `simpleAssemblyOfMeasure_eq_sum_bands` it would follow from,
> and `itoIntegralAgainst_unique` correspondingly takes agreement on simple processes rather
> than on written-out sums. Degenne's axiomatic `IsStochasticIntegral` characterisation is the
> right frame for that uniqueness clause but exists only on `v4.33.0-rc1`, so instantiating it
> waits for a stable pin. *(2026-10-02: both have moved. The summed identity landed as
> `itoIntegralAgainst_simpleProcess`, and the integral is now an instance of
> `IsStochasticIntegral`, `sc-ito-is-stochastic-integral` above
> ([#196](https://github.com/formal-applied-math/formal-mathfin/issues/196)).)*
>
> **Superseded status (2026-08-07):** corpus
> **353**, **322 full + 18 wrappers = 340/353 delivery-ready**, 13 reduced cores, 0 placeholders.
> Ledger 353 fresh / 0 stale / 0 missing; `lake build` and `lake lint` green with no `#guard_msgs`
> failure. The round covered martingale representation + market completeness, then the localized Itô
> formula naming its integrand, then the description-semantics fix below; the last two entries are
> the downside-performance-metrics work of
> [#173](https://github.com/formal-applied-math/formal-mathfin/pull/173) and the von Neumann–Morgenstern
> lotteries of [#178](https://github.com/formal-applied-math/formal-mathfin/pull/178).
> `itoIntegralCLM_T` was already a `LinearIsometry` from the predictable `L²(dt⊗dμ)` integrands into
> `L²(μ)`. `MathFin/Foundations/MartingaleRepresentation.lean` identifies its image exactly:
> `itoIntegralCLM_T_surjective_onto_centered` says the Itô integrals together with the constants
> exhaust `lpMeas ℝ ℝ 𝓕ᴮ_T 2 μ`, and `itoIsometryEquiv` bundles the isometry as an equivalence onto
> the centered part. The route is orthogonal decomposition against the (closed, because isometric)
> range, plus totality of the step-integrand Doléans exponentials
> (`WienerExponentialTotality.eq_zero_of_orthogonal_stepDoleans`,
> `DoleansStepRepresentation.stepDoleans_sub_one_mem_range`), settled on the dyadic cylinder
> σ-algebras of `BrownianCylinderGeneration`, whose supremum is the natural filtration
> (`iSup_cylinderFiltration_eq_natFiltration`). No Malliavin calculus and no adapted-integrand Itô
> formula. Centering, `𝔼[∫₀ᵀ φ dB] = 0`, is proved a floor down as
> `ItoIntegralProcessGeneral.integral_itoIntegralCLM_T`, not assumed.
> **`gir-thm-9.3.4` flips `reduced_core → full`** (14 → 13 reduced cores): it had been a `Prop`
> structure whose conclusion was a bundled field read off by projection, and it now re-exports
> `martingale_representation`, the process form the entry states.
> Three new entries. `gir-mrt-range-surjective` is the submodule form above.
> `gir-market-completeness` (`MathFin/Foundations/MarketCompleteness.lean`,
> `exists_replicating_strategy`) is the finance reading: every `L²` `𝓕ᴮ_T`-claim is the terminal
> wealth `𝔼_μ[H] + ∫₀ᵀ φ dB` of a strategy, with a *unique* hedge. `gir-pricing-measure-unique`
> (`measure_eq_of_pricesGainsAtZero`) is uniqueness of the pricing measure on the Brownian
> filtration, for measures that price the traded gains at zero.
>
> **Scope of the uniqueness result, stated plainly.** `gir-pricing-measure-unique` is **not** the
> unconditional second FTAP, and it does **not** follow from `IsEMM` alone. The textbook argument
> needs the replicating wealth to be a stochastic integral against the price `S`, hence a martingale
> under every EMM; the wealth process martingale representation builds is an integral against `B`,
> and `S` and `B` share only a filtration. That fair-game step is therefore a named hypothesis,
> `PricesGainsAtZero Q`: every terminal Itô integral is `Q`-integrable with zero `Q`-mean. What is
> hypothesised is step (i) of the textbook proof; what is proved is step (ii). The hypothesis is
> guarded by two proved facts rather than asserted: `pricesGainsAtZero_self` (`μ` satisfies it, so
> nothing here is vacuous) and `pricesGainsAtZero_of_gains_martingale` (it follows from the textbook
> gains-martingale condition). The corollary `emm_unique_of_complete` consumes only the `isProb` and
> `ac` fields of `IsEMM`; its `martingale` field rides along unused, kept so the statement stays in
> the vocabulary a reader looks it up under. Only `complete ⟹ unique` is delivered — the converse
> needs the Jacod–Yor extreme-point characterisation and is out of scope.
> The companion `superReplication_eq_emm_price` is the continuous-time superreplication duality, and
> its "EMM price" is `𝔼_μ[H]`. It does **not** close
> [#39](https://github.com/formal-applied-math/formal-mathfin/issues/39): `Foundations/SuperhedgingDuality`
> is a finite-state one-period matrix model whose Farkas gate is untouched. The two equalities hold
> for structurally different reasons, separation there and martingale representation here, and
> neither implies the other. The hedging strategy class is the Itô-integrable predictable integrands,
> wider than `ContinuousMarket.SimpleStrategy`; the widening is forced, since a general `L²` claim is
> not the terminal value of any piecewise-constant holding. `ContinuousMarket` itself is untouched
> apart from a scope paragraph. All four entries axioms-clean.
>
> **The localized Itô formula now names its integrand**
> ([#183](https://github.com/formal-applied-math/formal-mathfin/issues/183), closed 2026-08-07; no corpus
> entries added, five strengthened). The chain
> `ito_formula_td_L2_bddDeriv → cutoff_bddDeriv → ito_formula_td_localized → ito_formula_itoProcess →
> ito_formula_gbm`/`ito_formula_expBrownian → discountedGBM_eq_itoIntegral` was a run of bare
> existentials, so no consumer could identify the diffusion coefficient — the library could not say
> "the delta is `σŜ`". Every link now carries `gfx =ᵐ [the integrand]`, ending at `gfx =ᵐ [σ·Ŝ(·)]`
> for the discounted GBM, and `sc-thm-7.1.2`, `sc-ito-formula-localized`, `sc-ito-formula-gbm`,
> `sc-discounted-gbm-ito` and `sc-ito-formula-ito-process` state it. **This closed a fidelity gap, not
> just a convenience one:** all five entries' `description` and docstring already wrote the integral as
> `∫₀ᵀ f_x(s,B_s) dB_s` / `∫₀ᵀ σŜ(s) dB_s` while the Lean said only `∃ gfx` — the prose was ahead of
> the statement. The identification argument is a general `Lp` fact
> (`ae_eq_of_tendsto_Lp_of_tendsto`: an `L²` limit agrees a.e. with a pointwise limit of a.e.
> representatives, via subsequence a.e. convergence) applied to the observation that each cutoff's
> chain-rule integrand is *eventually constant* at `f_x(·, B)` at every point. `L²` membership of
> `f_x(·, B_·)` comes out of the identification rather than being a prerequisite. The forgetful wrapper
> `ito_formula_td_L2_bddDeriv`, whose only job was to drop the conjunct
> `ito_formula_td_L2_bddDeriv_explicit` already carried — the mechanism that created the gap — is
> merged away: the two are one theorem under the shorter name.
>
> **The audit that followed** (2026-08-07, corpus unchanged). Two overstatements in one day stopped
> being a one-off, so the class was swept repo-wide. `sc-thm-7.1.1` had the identical defect one tower
> over — description writing `∫₀ᵗ f'(B_s) dB_s` over an `∃ gf'` — now fixed through
> `itoIntegralCLM_T_of_bdd_cont → ito_formula_L2_bddDeriv → _mk`. Four descriptions corrected where
> they claimed the textbook theorem and the entry delivers less (`cm-thm-4.3.10` no `L^p` convergence,
> `sc-thm-8.2.5` uniqueness not existence, `sc-thm-7.4.5` constant `σ`, `sc-thm-9.2.1` the Feynman–Kac
> identification not PDE uniqueness). The README's landmark row for `ito_formula_unrestricted` was
> rendering a local-martingale theorem as an integral identity. And
> `ae_fst_mem_Ioc_trimMeasure_T` existed six times across five files; five retired. The mechanical
> slice is now gated (`test_prose_does_not_outrun_statement`, negative-controlled against the three
> conjuncts it exists to protect); the judgment slice is a standing first pass in the values-review
> protocol and in `CLAUDE.md`.
>
> **`description` now has one job** (2026-08-07, closing that open item). All 36 textbook-framed
> descriptions were read against their statements and **15 — 42% — claimed more than the Lean
> proved**. Beyond the five already corrected: a sign error (`mart-prop-2.5.5` wrote `(X_n−a)⁻`
> where the theorem proves the submartingale `(X_N−a)⁺`); a stale description contradicting its own
> status (`gir-thm-9.1.8` said "Kept reduced_core" on a `full` entry); a multivariate claim delivered
> only in 1-D (`dist-thm-B.1.2-affine`); `[B,B]_t = t` where the theorem proves the L¹-mean
> `E[Σ(ΔB)²] → t` (`sc-thm-6.1.1`); plus local-vs-global Hölder, one of two tower equalities,
> unclaimed continuity of a stopped process, and two Poisson entries stating increment laws for a
> pair where the prose said "process" and "family".
>
> The rule is now: **`description` states the theorem as this entry proves it**; where an entry
> delivers less than the source theorem it is named after, the description says so. The structural
> cause was an asymmetry — `formalization_scope`, the honest per-entry disclosure, exists on every
> entry and was **not** exported, while `description` was. The claim shipped and the disclosure
> stayed home. `tools/verify/hf_dataset.py` now publishes both.
>
> **Record correction (2026-08-04, drafter attribution — no theorem changed):** corpus
> **348**, **316 full + 18 wrappers = 334/348 delivery-ready**, 14 reduced cores, 0
> placeholders — all unchanged; this touched `metadata.provenance` only, and the ledger
> stayed 348 fresh because the input-hash covers snippet + imports + pins, not metadata.
> `mf-performance-gain_to_pain` and `mf-performance-upside_capture` recorded
> `statement_source: magistral-autoform`. They landed **2026-07-31**; Magistral left the
> drafter on **2026-07-27** (foundry `17ac296`), so they cannot have been drafted by it.
> The name was baked in at ENQUEUE rather than written by the stage that ran — the defect
> `assemble.py::sanitize_provenance` exists to stop, added after these had already merged.
> Both are scrubbed to the drafter-agnostic `autoform` via that same function, so their
> `formalization_scope` prose now reads "autoformalized statement" rather than
> "magistral-drafted statement". `mf-fixedincome-swap` (#66) and
> `mf-insurance-premium-principles` (#85) landed 2026-07-18, genuinely in the Magistral
> era, and **keep** their attribution — the correction is not a rename.
> `formalization.yaml` had a second fault of the same family: it derived the drafter from
> provenance correctly and then attached it to the TOTAL, crediting one drafter with all
> four entries. It now tallies per drafter ("Magistral (2) and an unnamed drafter (2)"),
> with `test_the_disclosure_does_not_generalize_one_drafter_to_every_entry` asserting the
> property. Full rationale in [`values-review.md`](values-review.md).
>
> **Prior (2026-07-31, speed greeks + caplet/floorlet parity — closes #8, #27):** corpus
> **348**, **316 full + 18 wrappers = 334/348 delivery-ready**, 14 reduced cores, 0 placeholders.
> Three entries finishing two contributions that had been open since June (#36, #38, mertunsall)
> and had gone stale against the pin bump.
> `mf-bs-speed` (`BlackScholes/HigherGreeks`): **speed** `∂³V/∂S³ = ∂Γ/∂S =
> -ϕ(d₁)(d₁ + σ√τ)/(S²σ²τ)`. Placed beside vanna/volga/charm rather than in the PDE file —
> gamma *is* the quotient `ϕ(d₁)/(S σ √τ)` (`hasDerivAt_bsV_SS`), so speed is one quotient rule
> away, with `ϕ'(d₁) = -d₁ϕ(d₁)` supplying the numerator derivative. The contribution also
> corrected the formula in issue #8, which was algebraically wrong.
> `mf-black76-speed` (`Futures/Black76Greeks`): the discount factor is `F`-independent, so the
> Black-76 speed is a bare-term `const_mul` of the `r = 0` BS speed, with `e^{-rT}` live in both
> the function and the value — matching the sibling greeks, so the `r` binder is load-bearing.
> `mf-caplet-floorlet-parity` (`Futures/Black76`): `V^caplet - V^floorlet = α·(F - K)`, derived by
> *applying* `swaption_payer_receiver_parity` rather than re-running the same `Phi`-symmetry
> argument — `blackCaplet_eq_blackPayerSwaption` records that a caplet is the payer swaption's
> formula with the accrual factor where the annuity sits. The caplet and floorlet price
> definitions carry no benchmark entry of their own: price-equals-definition closes by `rfl`, so
> they are exercised through the parity identity and the ledger instead, and the
> definitional-`rfl` allowlist stays empty. Axioms-clean.
>
> **Prior (2026-07-31, forward-rate agreement — closes #67):** corpus **345**,
> **313 full + 18 wrappers = 331/345 delivery-ready**, 14 reduced cores, 0 placeholders.
> `mf-fixedincome-fra` (`FixedIncome/FRA`, closes #67; the first outside contribution to the
> corpus): the simple forward rate `F = (P(0,T₁)/P(0,T₂) - 1)/δ`, FRA value
> `V = δ·P(0,T₂)·(F-K)`, its expanded discount-factor identity, and the fair-rate equivalence
> `V = 0 ↔ K = F`. The generic discount-factor algebra is stated once and instantiated on the
> existing `zcb` curve; `P(0,T₂) ≠ 0` is *derived* from `zcb_pos` rather than assumed, leaving
> `δ ≠ 0` as the only hypothesis — the natural-generality discipline applied without prompting.
> The proof structurally consumes `MathFin.zcb`; it does not encode the conclusion in a `let`
> binding or close a benchmark with `rfl`.
>
> **Prior (2026-07-31, gain-to-pain + upside capture — closes #161, #162):** corpus
> **344**, **312 full + 18 wrappers = 330/344 delivery-ready**, 14 reduced cores, 0 placeholders.
> `mf-performance-gain_to_pain` and `mf-performance-upside_capture`
> (`Performance/RatiosExtended`): the two realised-path ratios join the four moment ratios
> already in that module. `gainToPain` is written on Mathlib's positive/negative parts
> (`r⁺`, `r⁻`) rather than open-coded `max _ 0`, which buys `posPart_sub_negPart` and hence
> `one_le_gainToPain_iff` — the ratio clears 1 exactly when the period was profitable, the
> statement that makes the definition worth having. `upCapture_smul` is degree-one
> homogeneity in the portfolio leg.
>
> Both landed as **one** refined change consolidating four duplicate autoform PRs
> (#163/#165 for #161, #164/#167 for #162 — the pipeline drafted each target twice). Each
> draft carried a **spurious division guard** (`0 < ∑ r⁻`, `∑ b ≠ 0`) that neither issue
> asked for and neither proof needs: in Lean `x / 0 = 0`, so nonnegativity and homogeneity
> both hold unconditionally. The guards are dropped, so the merged statements are strictly
> *stronger* than the drafted ones. Each draft also created a new one-lemma module instead of
> the `RatiosExtended` module both issues named; consolidated. Axioms-clean.
>
> **Prior (2026-07-18, in-out barrier parity — closes #53):** corpus
> **342**, **310 full + 18 wrappers = 328/342 delivery-ready**, 14 reduced cores, 0 placeholders.
> `mf-barrier-inout-parity` (`BlackScholes/BarrierParity`, closes #53): knock-in / knock-out
> **in-out parity** `V_in + V_out = V_vanilla` — the barrier-hit event `A` and its complement
> partition every path, so the discounted expected payoffs add to the vanilla price (pure
> linearity of expectation; no barrier density, in the register of `chooser_integral_decomp`).
> The proof lifts the pathwise payoff split `barrier_payoff_partition`
> (`𝟙_A·f + 𝟙_{Aᶜ}·f = f`, `Set.indicator_self_add_compl`) through `integral_indicator` +
> `integral_add_compl`. New def `discountedValue D Q g = D·E_Q[g]` — the present-value functional
> the pricing files had only ever written inline, now named so the three barrier values
> (`knockInValue` / `knockOutValue` / `vanillaValue`) are thin specialisations and parity reads as
> an identity about *values*. Axioms-clean. Provenance: the target the autoform pipeline repeatedly
> failed to draft (depth-gate, then a hallucinated `MathFin.zcb`); authored by hand as the
> bottleneck-locating control.
>
> **Prior (2026-07-18, second refined autoform PR — loaded premium principles):** corpus
> **341**, **309 full + 18 wrappers = 327/341 delivery-ready**, 14 reduced cores, 0 placeholders.
> `mf-insurance-premium-principles` (`Actuarial/ActuarialInsurance`, closes #85; the second
> autoform-pipeline PR — the generalization run's output, Leanstral-drafted and -proved,
> human-refined at review): the three classical **loaded premium principles** — expected-value
> `(1+θ)·μ`, variance `μ + α·σ²`, standard-deviation `μ + β·σ` — each with its own named
> nonnegative-loading bound (`expectedValuePremium_ge_mean` via `le_mul_of_one_le_left`,
> `variancePremium_ge_mean` / `stdDevPremium_ge_mean` via one-term `mul_nonneg` certificates), and
> the bundle `premium_ge_mean` assembled from them. The loadings sit on top of the net premium of
> `Actuarial/Insurance.lean` (prose seam; the net-premium algebra there is Mathlib's `eq_div_iff`
> consumed directly, same certificate family as the swap par identity). Refinery diff vs the draft:
> signature-bound def arguments + docstrings (the `docBlame` red), the never-used coupling
> hypothesis `hσ_eq : σ = √σ²` dropped, the unused `Insurance` import dropped, per-principle lemmas
> extracted so the bundle is a `⟨…, …, …⟩` of certificates rather than three `nlinarith` calls.
>
> **Prior (2026-07-18, first refined autoform PR — the vanilla swap par identity):** corpus
> **340**, **308 full + 18 wrappers = 326/340 delivery-ready**, 14 reduced cores, 0 placeholders.
> `mf-fixedincome-swap` (`FixedIncome/InterestRateSwap`, closes #66; the first autoform-pipeline PR
> to land — Leanstral-drafted and -proved, human-refined at review): the **par identity**
> `payerSwapValue P₀ Pₙ K A = 0 ↔ K = parSwapRate P₀ Pₙ A`, proved abstractly for any nonzero
> annuity (`payerSwapValue_eq_zero_iff`, a two-rewrite `sub_eq_zero`/`eq_div_iff` certificate) and
> instantiated on the `zcb` curve (`payerSwapValue_zcb_eq_zero_iff`) where positivity is discharged
> by `zcb_pos` + `annuity_pos` — assumed nowhere. New defs `annuity` (`A = δ·∑ P(0,Tᵢ)` — the
> numéraire slot `blackPayerSwaption` consumes), `payerSwapValue`, `parSwapRate`. The refinery diff
> vs the drafted statement: derivable positivity hypothesis dropped, member-witness binders replaced
> by `s.Nonempty`, flat-curve specialization demoted from theorem to corollary, snake_case def names
> and missing docstrings fixed (the classes the pipeline now gates itself).
>
> **Prior (2026-07-18, jump calculus — the Itô–Lévy integral CLM):** corpus **339**,
> **307 full + 18 wrappers = 325/339 delivery-ready**, 14 reduced cores, 0 placeholders. The
> **jump/Lévy axis** now carries the compensated-Poisson (Itô–Lévy) stochastic integral all the way
> to a continuous linear operator and its `L²` isometry — **`cgarryZA/LevyStochCalc`'s (Apache-2.0,
> cited) axiom #6 in full generality** (`sc-levy-integral-clm-isometry`,
> `Foundations/PoissonCompensatedIntegralOperator`). The integral `H ↦ ∫ H dÑ` is built on marked
> simple integrands (`levySimpleModule`, a `Finsupp` submodule of adapted bounded space-time-box
> coefficients), shown an isometry there (`assembly_isometry`, summing the overlapping-box bilinear
> pairing `sc-levy-bilinear-pairing`: `𝔼[(φa·Ñ(boxa))(φb·Ñ(boxb))] = 𝔼[φa·φb]·ν̂(boxa∩boxb)`), then
> extended by continuity (`LinearMap.extendOfNorm`) to its whole `L²(dP⊗dν̂)` closure —
> `itoLevyIntegralL2 : levyClosure N →L[ℝ] L²(P)` with `‖itoLevyIntegralL2 H‖ = ‖H‖`. **Design win**:
> defining the target *as* `topologicalClosure(range emb)` makes the density hypothesis a soft
> `IsInducing.subtypeVal.dense_iff` fact — no from-scratch marked-predictable `σ`-algebra (the route
> the continuous Itô CLM needed a bespoke trimmed measure for). The simple-integrand rungs
> `sc-levy-isometry-compensated-simple` (the grid double sum
> `𝔼[(∑ⱼ∑ₗ φⱼₗ·Ñ((tⱼ,tⱼ₊₁]×Aₗ))²] = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)`,
> `Foundations/PoissonCompensatedIntegralL2`) and `sc-levy-isometry-normform` (norm form
> `𝔼[(∫ H dÑ)²] = ‖H‖²_{L²(dP⊗dt⊗dν)}`) proved axiom #6 at the simple level via the single
> independent-scattering PRM field `indep_of_disjoint_region` (with the diagonal Poisson second
> moment `𝔼[Ñ(B)²]=ν̂(B)`, a Mathlib gap-fill via the pmf index-shift `(n+1)·c_r(n+1)=r·c_r(n)`); the
> integral CLM **closes their declared dense-extension follow-up**. **Honest scope**: all four
> `sc-levy-*` entries are axiom-clean `full`; PRM *existence* (LevyStochCalc's axiom #2 — Mathlib has
> no PRM substrate) remains a declared, deferred Summit.
>
> **Prior (2026-07-16, multi-asset matrix Riccati):** the two matrix-Riccati `full` entries
> `mf-mm-matrix-riccati` / `mf-mm-matrix-value` (`Foundations/MatrixMarketMakingRiccati`, BEGV
> Proposition 2): the spectral-reduction closed form `a(t) = U·diag(riccatiCoeff(λᵢ))·Uᴴ` solving
> `a'(t) = a(t)·a(t) − Â·Â` and its market-making instantiation `A' = 2·A·D₊·A − (γ/2)·Σ`; the
> `B`/`C` coefficients, general-`d` value verification, and optimal-control substrate remain deferred.
>
> **Prior (2026-07-16, single-asset market-making Riccati):** corpus **333**,
> **301 full + 18 wrappers = 319/333 delivery-ready**, 14 reduced cores, 0 placeholders. Three new
> `full` entries open optimal **market making** (`Foundations/MarketMakingRiccati`) — the single-asset
> (`d = 1`) closed-form approximation of Bergault–Evangelista–Guéant–Vieira (arXiv:1810.04383): the
> Riccati coefficient `mf-mm-riccati` (`a(t) = Â·tanh(Â(T−t))` solves `a' = a² − Â²`; the `tanh`
> derivative is derived locally, Mathlib carrying none at this pin), the value-function verification
> `mf-mm-value-function` (the quadratic ansatz `θ̌ = −Aq² − Bq − C` solves the **approximate**
> quadratic-Hamiltonian Hamilton–Jacobi equation given the Riccati/linear ODE system — Prop. 1 at
> `d = 1`, the `B`/`C` coefficients certified by the `ring` closure), and the closed-form quotes
> `mf-mm-quotes` (constant half-spread + inventory-linear skew, instantiated at the Model-A
> `quoteConstA` and Model-B `quoteConstB` constants). **Honest scope** (mirroring `mf-almgren-chriss-EL`):
> we verify the closed-form solution of the *approximate* HJ equation only; the stochastic
> optimal-control substrate (existence of the true value function, the verification theorem linking
> `θ` to optimal quotes), the approximation-to-truth (numerical in the paper), the multi-asset
> matrix-Riccati case, and the `T → ∞` ergodic limit are out of scope / deferred follow-ups.
>
> **Prior (2026-07-12, continuous first-FTAP frame):** corpus **330**,
> **298 full + 18 wrappers = 316/330 delivery-ready**, 14 reduced cores, 0 placeholders. Four new
> `full` entries land the model-agnostic continuous-market EMM frame (`Foundations/ContinuousMarket`):
> the general forward FTAP `gir-continuous-emm-forward` (`isEMM_noArbitrageSimple` — an equivalent
> martingale measure precludes arbitrage against **simple** piecewise-constant predictable bounded
> strategies, proved directly via the bilinear conditional-expectation pull-out
> `condExp_bilin_of_stronglyMeasurable_left` with `innerSL ℝ` and a vanishing primitive
> `ae_zero_of_nonneg_of_integral_zero` **shared with the discrete FTAP**); its `F = ℝ` instance
> `gir-discounted-gbm-emm` (`discountedGBM_isEMM`, **Q = P**: the discounted GBM is already a
> full-horizon `P`-martingale, so `P` is its own EMM); the corollary `gir-discounted-gbm-no-arbitrage`;
> and the standalone foundational lemma `gir-martingale-reindex` (a `Q`-martingale sampled along a
> monotone schedule is a discrete `Q`-martingale). **Honest scope:** meaning-1 (simple strategies).
> The physical-measure Girsanov EMM `Q ≠ P` is intrinsically bounded-horizon (`Q = withDensity Z_T`
> is a martingale measure only on `[0,T]`), so a horizon-aware EMM is tracked as follow-up; general
> admissible strategies / NFLVR / the converse (Delbaen–Schachermayer) are the deferred meaning-2.
>
> **Prior (2026-07-11, survival-model foundation):** corpus **326**,
> **294 full + 18 wrappers = 312/326 delivery-ready**, 14 reduced cores, 0 placeholders. Two new
> `full` entries open the life-contingencies foundation (issue #112): the survival-ratio keystone
> `mf-survival-ccdf-ratio` (`tpₓ = S_X(x+t)/S_X(x)` for `t ≥ 0` — the conditional-probability
> definition of `survive`, built on Mathlib's conditional measure `cond`, collapses to the ratio)
> and `mf-survival-ccdf-zero` (`S_X(0) = 1`), in `Actuarial/SurvivalModel`. **Provenance:** the
> design and proofs are our own, in this library's Mathlib idiom; Yosuke Ito's Isabelle/HOL AFP
> entry *Actuarial Mathematics* (`Survival_Model`, BSD) was consulted as a source for the classical
> result set and is cited, with the author's kind permission. The disclosure is mechanical —
> `metadata.provenance.source == afp-actuarial-mathematics`, counted in `formalization.yaml`.
>
> **Prior (2026-07-11, finance-breadth sprint):** corpus **324**,
> **292 full + 18 wrappers = 310/324 delivery-ready**, 14 reduced cores, 0 placeholders. Five new
> `full` finance entries land and one `reduced_core` flips to `full`, so `mathematical_finance`
> is now **224/225 full**: (1) the **n-date geometric-Asian** option — driver law
> `mf-asian-geom-n-driver` (`(1/n)∑ B_{τᵢ} ~ N(0, (1/n²)∑∑min(τᵢ,τⱼ))`) and closed-form price
> `mf-asian-geom-n-price` (reduction to one effective BS driver), `BlackScholes/AsianGeometricN`;
> (2) **binomial barrier/lookback** via the reflection principle — the counting identity
> `mf-barrier-reflection-count` and the running-maximum law `mf-barrier-maximal-distribution`
> (`#{max ≥ a} = 2·#{end > a} + #{end = a}`), consuming the previously-stranded
> `reflectionPrincipleEquiv_below`, `Binomial/BarrierReflection`; (3) the **Girsanov-grounded quanto
> forward** `mf-quanto-forward-grounded` — the `−ρ σ_S σ_FX` drift adjustment *derived* from a
> joint-Gaussian FX model + change of measure rather than posited, `BlackScholes/QuantoGrounding`;
> and (4) the **compound-Poisson aggregate-loss MGF** `mf-compound-poisson-mgf` (`reduced_core → full`),
> the n-claim iid-sum MGF composed with the Poisson pgf, `Actuarial/CompoundPoissonMGF`. Honestly
> deferred: the fully general **2D Itô formula** `sc-thm-7.5.2` stays `reduced_core` — its
> continuous-time covariation form is a summit-scale build, not a breadth item.

> **Prior (2026-07-10, bounded-PREDICTABLE Girsanov — Rung 1):** corpus **319**,
> **286 full + 18 wrappers = 304/319 delivery-ready**, 15 reduced cores, 0 placeholders. New `full`
> entry `gir-thm-9.1.8-predictable` (`girsanov_predictable_qbm`,
> `Foundations/GirsanovPredictableTheta.Btheta_isQBrownianMotion_predictable_of_bdd`) **strengthens**
> the continuous-adapted `gir-thm-9.1.8` to a bounded **predictable** `θ` — the honest domain of the Itô
> `L²` integral, dropping the path-continuity assumption. `B^θ_u = B_u + driftContinuousMod θ̂ u` (the
> genuinely-`𝓕`-adapted modification of `∫₀ᵘθ ds`) starts at `0`, has `N(0,t−s)` increments, and has
> any two non-overlapping increments independent under
> `Q = μ.withDensity(exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds))`. **Still spine-free**, over a Route-B marshalled
> density approximation: `θ` is approximated in `L²` by clamped dense simple processes marshalled into
> single-partition `(s,c)` form (so `isExpQMartingale_BthetaSimple` applies per `n`); the stochastic
> integral, drift, AND quadratic variation each converge in `μ`-measure (via the drift-modification
> tower's `L²`-slice energy identity), fused through a common a.e.-subsequence (`exists_subseq_tendsto_ae₂`)
> into the same set-integral engine `tendsto_setIntegral_of_subseq_ae_of_sq_bound` plus a generic
> Fatou-`L²` limit (`memLp_two_of_subseq_ae_of_sq_bound`), with the partition-generic uniform L⁴/L²
> moment bounds of `GirsanovSimpleDoleansMoments`. Axioms-clean, `lake build` green (8860 jobs), gates +
> ledger fresh. Girsanov ladder: constant → simple-adapted → continuous-adapted → **predictable (Rung 1)**;
> only the strictly more general `L²`/progressive-`θ` under Novikov (unbounded, Rung 2) remains
> `reduced_core`, at `sc-thm-9.1.8`.
>
> **Prior (2026-07-09, continuous-adapted Girsanov closes `gir-thm-9.1.8`):** corpus **318**,
> **285 full + 18 wrappers = 303/318 delivery-ready**, 15 reduced cores, 0 placeholders. `gir-thm-9.1.8`
> flips `reduced_core → full`: `girsanov_adapted_continuous_qbm`
> (`Foundations/GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted`) derives zero start, Gaussian
> `𝒩(0,t−s)` increments, and independence of any two non-overlapping increments under `Q` for a
> bounded (`|θ| ≤ C`), `𝓕`-adapted, path-continuous `θ`, under `Q = μ.withDensity(exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds))`
> with `B^θ_u = B_u + ∫₀ᵘθ ds`. **Spine-free:** rather than a continuous Doléans stochastic exponential
> proved to be a martingale (a Novikov crux), the simple-θ exponential-martingale identity
> `isExpQMartingale_BthetaSimple` (uniform-partition approximants `c⁽ⁿ⁾_i = θ(tᵢ)`) is passed to the
> limit — the stochastic exponent `Wⁿ = ∑θ(tᵢ)ΔBᵢ → ∫θ dB` in `L²`, the drift parts converge everywhere,
> and the **mixed-time** set-integral limit `∫_A exp(a·Yⁿ−½)·Zⁿ_T → ∫_A exp(a·Y−½)·Z_T` goes through the
> a.e.-subsequence engine `tendsto_setIntegral_of_subseq_ae_of_sq_bound` with a route-A L⁴/AM-GM uniform
> `L²` bound, then `isQBrownianMotion_of_expMartingale` reads off the three properties (no adapted-integrand
> Itô formula). Axioms-clean, `lake build` green, gates + ledger fresh. This is the culmination of the
> Girsanov Track-α arc (constant → simple → continuous adapted). **Only the strictly more general
> `L²`/progressive-`θ` under Novikov (unbounded) remains `reduced_core`, at `sc-thm-9.1.8`.**
>
> **Prior (2026-07-08, geometric-Asian lognormality + the Wiener-indicator identity):** corpus
> **318**, **284 full + 18 wrappers = 302/318 delivery-ready**, 16 reduced cores, 0 placeholders. One new
> `full` entry plus a reusable foundational brick, both axioms-clean (`lake build` green, gates + ledger
> fresh). `mf-asian-geom-driver-gaussian` (`BlackScholes/AsianGeometric.asianGeom_driver_hasLaw`): the
> two-date geometric-Asian **log-driver** `(B_s + B_t)/2` — the Gaussian part of `log √(S_s·S_t)` under GBM —
> is Gaussian `N(0, (3s+t)/4)`, the variance the Brownian covariance sum `(s + 2·min(s,t) + t)/4`. This turns
> the geometric average into a priceable lognormal, complementing the AM-GM payoff bound
> `mf-asian-geom-le-arith-two`. The enabling brick is `Foundations/WienerIntegralIndicator.wienerIntegralLp_stepIndicator`
> (`∫ 𝟙_{(s,t]} dB = B_t − B_s`, from `LinearMap.extendOfNorm_eq` on the single-basis coefficient), which lets
> a sum of Brownian values be read as a single Wiener integral of a deterministic step kernel — the same route
> the Vasicek bond price takes for the *integrated* rate; here the kernel is a sum of indicators. The law then
> comes from `wienerIntegralLp_hasLaw_gaussian`, its variance the kernel `L²`-norm evaluated on the Ω-side
> through `integral_mul_eval` (`∫ B_u·B_v = min(u,v)`) and zero start `B_0 = 0` a.s. Honest scope: two dates
> (matching the AM-GM entry); the n-date extension is the Finset covariance sum `(1/n²)∑∑min(tᵢ,tⱼ)`, unblocked
> by the same crux. This closes the geometric-Asian item flagged open by the 2026-07-07 note below.
>
> **Live status (2026-07-07, finance breadth — the Vasicek affine bond price + the T-forward measure):**
> corpus **317**, **283 full + 18 wrappers = 301/317 delivery-ready**, 16 reduced cores, 0 placeholders.
> Two new `full` fixed-income entries, both consuming machinery already load-bearing (no new frontier;
> `lake build` 8852 green, all 19 gates + ledger 317 fresh, both axioms-clean).
> (1) `mf-vasicek-bond-price` (`FixedIncome/VasicekBondPrice.vasicekBondPrice_affine`): the Vasicek
> zero-coupon bond price `P(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)]` as the Gaussian Laplace transform of the integrated
> short rate, collapsing to the **affine term structure** `P(0,T) = A(T)·exp(−B(T)·r₀)`, `B(T) = (1−e^{−κT})/κ`.
> The integrated rate `∫₀ᵀ r_s ds = M(T) + σ∫₀ᵀ g dB` is carried in its Wiener representation (integrated OU
> kernel `g(u) = (1−e^{−κ(T−u)})/κ`; the deterministic time-order swap is the modelling bridge, cited — parity
> with the OU-solution model of `mf-vasicek-sde-terminal-gaussian`), its Gaussian law `N(M, σ²V)` from
> `wienerIntegralLp_hasLaw_gaussian` + the FTC variance integral `∫₀ᵀ g² = V(T)`, and the price factors
> `exp(−M)·𝔼[exp(−σ∫g dB)] = exp(−M + σ²V/2)` by the centred Gaussian MGF `integral_exp_mul_gaussianReal_zero`
> at `−σ`. Second deterministic-integrand-Wiener consumer in FixedIncome. (2) `mf-forward-measure-spot`
> (`FixedIncome/ForwardMeasure.forwardMeasure_bs_expected_terminal`): the **T-forward measure** `Q^T`
> (zero-coupon bond as numéraire) with `𝔼^{Q^T}[S_T] = S_0·e^{rT} = S_0/P(0,T) = F(0,T)` — the forward price —
> as a `changeOfNumeraire` instance (bond slots `N_T = P(T,T) = 1`, `N_0 = P(0,T) = e^{−rT}`), the natural next
> numéraire instance after the stock and `S²`-numéraires. Honest scope: under the constant-rate ZCB the density
> `dQ^T/dQ = 1` so `Q^T = Q` coincides with the risk-neutral measure; the construction carries verbatim to a
> stochastic short rate. CVaR's Rockafellar–Uryasev variational theorem + the coherence quartet were found
> **already complete** (`RockafellarUryasev`, `CoherentAxioms`); the geometric-Asian *closed-form price*
> (only the AM-GM inequality bound exists) remains a genuine open item (needs the BM joint-Gaussian covariance).
>
> **Prior (2026-07-03, SDE existence made pathwise — the E-fixed point as a sample-path process,
> #19 → existence bridge):** corpus **312** (unchanged — a Foundations-level formalization advance, not a
> new benchmark entry). The strong solution, previously banked only as the abstract `L²`-fixed point
> `picardSolution ∈ E`, is now realized as a genuine **pathwise** process:
> `Foundations/SDEPathwise.sde_pathwise_decomposition` slices the fixed-point equation `X = Φ(X)` (which
> holds in `E`) into the sample-path identity
> `X_t(ω) = η(ω) + driftContinuousMod(b∘X)_t(ω) + itoContinuousMod(σ∘X)_t(ω)` for a.e. `(t, ω)`. The
> enabling crux is `Foundations/DriftProcessModification.driftProcessAssembled_coeFn`: the abstract
> `extendOfNorm` drift operator's `coeFn` equals the honest pointwise-`limUnder` process
> `driftContinuousMod` a.e. It is proved (not, as on the Itô side, true by construction) via two
> convergences of `driftSimpleProcessLp Vₙ` — CLM-continuity to the operator and a.e. to the pathwise limit
> (`driftContinuousMod_tendsto`, a **direct Chebyshev** maximal bound — no martingale — plus
> Borel–Cantelli, the drift analog of `itoContinuousMod_tendsto`) — unique in measure on the finite trim
> space, the a.e. convergence lifted from per-slice to the trim measure through the predictable-measurable
> convergence set. All axiom-clean (`[propext, Classical.choice, Quot.sound]`, pinned in `AxiomAudit`).
> **The drift term is now the honest single Lebesgue integral** (#33, this session):
> `DriftProcessModification.driftContinuousMod_eq_setIntegral` proves `driftContinuousMod g t ω =
> ∫₀ᵗ ⇑g(s,ω) ds` a.e. for every `t ≤ T` — the elementary drifts `∫₀ᵗ Vₙ ds` converge to
> `driftContinuousMod`, and the ω-slice energies `Dₙ(ω) = ∫₀ᵀ(⇑Vₙ − ⇑g)² ds` decay in `L¹(μ)`
> (`= ‖simpleAssembly_T Vₙ − g‖²`), so a subsequence has `Dₙₖ(ω) → 0` a.e., whence the interval
> Cauchy–Schwarz `|∫₀ᵗ(⇑Vₙₖ − ⇑g)| ≤ √(T·Dₙₖ(ω)) → 0` matches the two limits.
> `SDEPathwise.sde_pathwise_drift_eq_setIntegral` specializes it to `b∘X`, so the strong solution's drift
> term is the recognizable SDE integral `∫₀ᵗ b(X_s(ω)) ds`, not merely an abstract limit. All axiom-clean.
> `sc-thm-8.2.5`'s existence half stays the conditional-`c < 1` `E` result; this bridge makes that
> solution's sample paths — and now its drift integral — explicit.
>
> **Prior (2026-07-03, SDE strong-solution uniqueness — the L²-energy Grönwall keystone, #19):**
> corpus **312**, **278 full + 18 wrappers = 296/312 delivery-ready**, 16 reduced cores, 0 placeholders.
> **The uniqueness half of Theorem 8.2.5 is now a genuinely _derived_ theorem, not an assumed field.**
> `Foundations/SDEUniqueness.IsL2SolutionPair.uniqueness` (entry `sc-thm-8.2.5`, flipped
> **`reduced_core` → `full`**) proves two `L²` strong solutions of `dX = μ(X)dt + σ(X)dB` sharing the
> driver agree a.s. at every time, via the classical `L²`-energy argument: `E t = 𝔼[(Xₜ−Yₜ)²]` satisfies
> `E t ≤ (2·Cdrift·t + 2·Cdiff)·∫₀ᵗ E`, and `gronwall_zero_of_le_const_mul_integral` (a reusable integral
> Grönwall, built from Mathlib's differential form via the FTC primitive `G t = ∫₀ᵗ E`) forces `E ≡ 0`.
> The **drift** energy bound is _derived_ from Lipschitz `μ` (`drift_energy_le`: Cauchy–Schwarz in time +
> Tonelli), the **diffusion** from the Itô isometry. **Honest scope:** (i) this is the _uniqueness_ half —
> existence stays the separately-banked conditional-`L²` Picard result (`sde-picard-existence-uniqueness`);
> (ii) the diffusion enters through an operator `Iσ` whose _sole_ assumed property is the Itô isometry
> energy bound (the `isometry` field of `IsL2SolutionPair`) — a genuine, proven property of the Itô
> integral (`itoProcessCLM_norm_sq`), not the conclusion in disguise; (iii) a non-vacuity guard (the zero
> solution) certifies the `IsL2SolutionPair` field set is satisfiable. This **replaces** the prior
> `reduced_core` encoding, whose `uniqueness` was an assumed structural field read off by projection.
>
> **Prior (2026-07-03, the change of numéraire — the IV↔I seam):** corpus
> **312**, **277 full + 18 wrappers = 295/312 delivery-ready**, 17 reduced cores, 0 placeholders.
> **The library now has a general change-of-numéraire theorem plus both of its seam directions.**
> (1) `Foundations/Numeraire.changeOfNumeraire` (entry `mf-change-of-numeraire`, **`full`**) proves price
> is numéraire-invariant: with `Q^N = Q.withDensity((N_T·B₀)/(N₀·B_T))`, every terminal claim `X`
> satisfies `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]` — a pure measure-transport identity plus cancellation
> of `N_T`, needing **no integrability hypothesis**. The backbone is **consumed**, not orphaned:
> `StockNumeraire.stockNumeraireMeasure_eq_numeraireMeasure` exhibits the BS stock numéraire as the
> instance `B_T = e^{rT}`, `B₀ = 1`, `N = S`, and `ExchangeOption.exchangeOption_numeraire_price` (entry
> `mf-exchange-numeraire`, **`full`**) exhibits Margrabe's `S²`-numéraire valuation as the instance
> `X =` exchange payoff, `N = S²`. (2) `Performance/KellyNumeraire.kellyNumeraire_isRiskNeutral` (entry
> `mf-kelly-numeraire-emm`, **`full`**) delivers the martingale half of the *numéraire-portfolio ⟹ EMM*
> direction: deflated by the growth-optimal (Kelly) wealth, the physical weights give the bet zero
> expected return (`q₊·b + q₋·(−1) = 0`). The closed forms `q₊ = 1/(b+1)`, `q₋ = b/(b+1)`, their
> `p`-independence (the Kelly first-order condition) and their summing to `1` are not in the entry's
> statement, so `q` is not shown to be a probability measure. **Honest
> scope:** the portfolio⟹EMM direction is the **discrete, two-outcome** market — the elementary shadow of
> the **continuous** Long/Platen benchmark theorem (deflated prices are `P`-martingales, EMM density
> `∝ 1/N*`), which still needs a state-price-density / market model absent from the Itô tower. Garman's
> normal form is post-integration closed-form algebra (no measure), so it is not a `numeraireMeasure`
> instance and none was fabricated.
>
> **Prior (2026-07-02, SDE existence — the Picard fixed point, #44):** corpus
> **309**, **274 full + 18 wrappers = 292/309 delivery-ready**, 17 reduced cores, 0 placeholders.
> **The strong solution of `dX = b(X)dt + σ(X)dB` is now constructed as a Picard fixed point.**
> `Foundations/SDEExistence.picardMap_exists_unique_fixedPoint` (entry `sde-picard-existence-uniqueness`,
> **`full`**) builds the Picard iterate `Φ(X) = η + ∫₀ᵗ b(X)ds + ∫₀ᵗ σ(X)dB` as a self-map of the
> predictable `L²` space `E = Lp 2 (trimMeasure_T T)` — its diffusion term the *actual* Itô integral
> assembled in the tower — proves the a priori contraction estimate `‖Φ X − Φ Y‖ ≤ (T·L_b + √T·L_σ)‖X − Y‖`
> (drift operator norm `T` × Cauchy–Schwarz, Itô operator norm `√T` × the isometry), and obtains existence
> **and** uniqueness of the fixed point via Banach's theorem. **Honest scope:** the `L²`/`E` formulation,
> conditional on the small-horizon contraction constant `< 1`. The abstract-operator benchmark
> `sc-thm-8.2.5` (ℝ-time, `intervalIntegral` drift, opaque `Iσ`) stays **`reduced_core`** pending the
> `ℝ≥0`↔`ℝ`-time translation + a Bielecki all-`T` extension.
>
> **Prior (2026-06-30, Phase 2 — Girsanov: the EMM as an explicit change of measure):** corpus
> **308**, **273 full + 18 wrappers = 291/308 delivery-ready**, 17 reduced cores, 0 placeholders.
> **The Black–Scholes risk-neutral measure is now constructed as a Girsanov density change**, not taken
> as given. `Foundations/Girsanov.bs_discounted_isQMartingale` (entry `gir-bs-emm-girsanov`, **`full`**)
> tilts the physical measure by `Q = withDensity(exp(−θX_T − ½θ²T))` (constant market price of risk
> `θ = (μ−r)/σ`) and proves the discounted stock is a `Q`-martingale on `[0,T]` — retiring the Wald
> shortcut of `discountedGBM_isMartingale`, which took `Q = P` from the start. It stands on a reusable
> **Bayes change-of-measure engine** `Foundations/ChangeOfMeasure.changeOfMeasure_setIntegral_eq` (entry
> `gir-change-of-measure-engine`, **`full`**): if `Z` and `Z·D` are both `P`-martingales then `D` is a
> `Q`-martingale on `[0,T]` — no stochastic calculus, only conditional expectations (a Bayes pull-out and
> a martingale set-integral). The one new estimate is the mixed-time integrability of `D_u·Z_T`, via
> AM–GM (`exp(σX_u)exp(−θX_T) ≤ exp(2σX_u)+exp(−2θX_T)`, each Gaussian-MGF-integrable). This partially
> wires the architecture doc's Girsanov seam (I↔II, the martingale side; see `mathematical-architecture.md`).
> **The distributional side, for constant `θ` (2026-07-05):**
> `Foundations/GirsanovConstantTheta.Btheta_isQBrownianMotion` proves the drift-corrected
> `B^θ_t = X_t + θ t` has zero start, Gaussian increments
> `B^θ_t − B^θ_s ~ N(0, t−s)`, **and** independence of any two non-overlapping increments (corpus
> `gir-const-theta-qbm`, `full`; the marginal law is `gir-const-theta-marginal`, `full`). All three
> properties are now read off in **one** application of the process-agnostic exponential
> characterization `Foundations/ExpMartingaleQBrownian.isQBrownianMotion_of_expMartingale` (2026-07-06):
> the const-θ exponential martingale `exp(a·B^θ − ½a²·)` (`expBtheta_isQMartingale`, from the Bayes
> engine + two Wald exponentials) is packaged as `IsExpQMartingale`, and the characterization derives
> the marginal law, the increment law, and independence — the same reusable module now scheduled to
> power the simple-/continuous-θ cases (Route α). The increment *independence*, previously flagged as
> a Mathlib gap ("conditional-MGF ⟹ independence" is absent — only the reverse `condExp_indep_eq`
> exists), is reached WITHOUT that lemma: via Mathlib's `indepFun_iff_charFun_prod`, the joint
> characteristic function at `w = (w₁, w₂)` is the charFun-at-`1` of the Gaussian law of the linear
> combination `w₁·I₁ + w₂·I₂` (from the joint-MGF factorisation — a
> `condExp_mul_of_stronglyMeasurable_left` pull-out), so it factors into the two marginal Gaussian
> characteristic functions (`charFun_gaussianReal`) — no adapted-integrand Itô formula.
>
> **Simple (piecewise-constant) adapted θ — now `full` (2026-07-06):** `gir-simple-adapted`
> (`Foundations/GirsanovSimpleTheta.Btheta_simple_isQBrownianMotion`) proves `B^θ_t = X_t + ∑_i c_i
> (s_{i+1}∧t − s_i∧t)` has the same three properties under `Q = P.withDensity(E^{−c}_T)` for bounded
> `𝓕_{s i}`-measurable multipliers — the general bounded-**adapted**-θ Girsanov for the simple case,
> strictly beyond constant θ, via one application of `isQBrownianMotion_of_expMartingale` (no charFun
> chain re-derived). The two simple-θ-specific ingredients: the spine `simple_spine_ae`
> (`E^{−c}·exp(a·B^θ − ½a²·) =ᵐ E^{a−c}`) and the mixed-time integrability
> `integrable_expBthetaSimple_mul_density` (an `L²` Hölder: `Z_T² = E^{−2c}_T·exp(∑ c_i²Δτ_i)` with
> `∑ c_i²Δτ_i ≤ K²T`).
>
> **Continuous adapted θ — now `full` (2026-07-09):** `gir-thm-9.1.8`
> (`Foundations/GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted`) closes the bounded adapted
> **continuous** case by exactly the `L²`-approximation route anticipated here: the simple-θ identity
> `isExpQMartingale_BthetaSimple` (on the uniform-partition approximants `c⁽ⁿ⁾_i = θ(tᵢ)`) passed to the
> limit through the a.e.-subsequence set-integral engine `tendsto_setIntegral_of_subseq_ae_of_sq_bound`
> (route-A L⁴/AM-GM uniform `L²` bound on the mixed-time product `exp(a·Yⁿ−½)·Zⁿ_T`), then one
> application of `isQBrownianMotion_of_expMartingale` — no adapted-integrand Itô formula, no continuous
> stochastic-exponential-is-a-martingale (Novikov) crux. **Open (still `reduced_core`):** only the
> strictly more general `L²`/**progressive**-`θ` under Novikov (unbounded, merely progressively
> measurable), at `sc-thm-9.1.8`.

> **Prior round (2026-06-29, Phase 1 — the convex-duality unification: pricing = risk):** corpus
> **306**, **271 full + 18 wrappers = 289/306 delivery-ready**, 17 reduced cores, 0 placeholders.
> **The FTAP (pricing) and the coherent-risk representation (risk) are now proved to be the same
> Hahn–Banach theorem.** A shared cone-separation root lives in `Foundations/ConvexDuality.lean` — the
> cone↔simplex separation `exists_pos_separating_of_cone_disjoint_simplex` + the point↔cone companion
> `exists_separating_of_not_mem_cone`, sharing two atoms (`functional_eq_sum_single`,
> `functional_nonneg_on_cone`). Four new `full` corpus entries stand on it: `mf-convex-duality-root`
> (the root); the FTAP kernel `exists_pos_dual_of_disjoint_stdSimplex` **re-derived in place** from it
> (signature byte-identical → no consumer churn); `mf-coherent-risk-representation`
> (`RiskMeasures/AcceptanceSet.coherentRisk_isLUB`, the finite-state ADEH representation stated as an
> `IsLUB`, acceptance-set closedness *derived* from the four axioms, not assumed);
> `mf-worstcase-risk-representation` (`RiskMeasures/WorstCaseRisk.worstCase_isLUB`, a concrete instance
> — worst-case loss = sup over the whole probability simplex); and `mf-superhedging-emm-bound`
> (`Foundations/SuperhedgingDuality.emm_le_superReplication`, every equivalent martingale measure
> prices a claim ≤ its super-replication cost). This realizes the architecture doc's #1 seam (I↔IV;
> see `mathematical-architecture.md`). **Open:** the superhedging strong-duality *equality*
> (`superhedge = sup_{EMM}`), blocked on a finite-dimensional Farkas / polyhedral-cone closedness
> absent from Mathlib at this pin; the Gaussian CVaR robust form.

> **Prior round (2026-06-29, Summit C in Degenne's `IsLocalMartingale` typeclass — the wrapper
> completed):** corpus **302**, **267 full + 18 wrappers = 285/302 delivery-ready**, 17 reduced
> cores, 0 placeholders. **The unrestricted-`C³` residual `M` is now a genuine `IsLocalMartingale`**
> (`Foundations/ItoFormulaUnrestrictedLocMart.lean`, entry
> `sc-ito-formula-unrestricted-islocalmartingale`, **`full`**): the one ingredient beyond the
> explicit form — adaptedness of `M` (`residual_stronglyMeasurable`), i.e. of the drift primitive
> `D_t = ∫₀ᵗ drift` (`driftPrimitive_stronglyMeasurable`, time-clamp + Carathéodory +
> `StronglyMeasurable.integral_prod_right`) — discharged; then
> `StronglyAdapted.stoppedProcess_indicator` + the all-time agreement assemble
> `Locally (Martingale ∧ cadlag)` with the exit-time localizer `σ_N`.
> **Itô's formula now holds for a general `C³` `f` with NO growth/boundedness hypothesis**
> (`Foundations/ItoFormulaUnrestricted.lean`, entry `sc-ito-formula-unrestricted-local`, **`full`**):
> the residual `M_t = f(t,B_t) − f(0,B_0) − ∫₀ᵗ(f_t+½f_xx)ds` is a continuous local martingale in
> **explicit form** — a localizing sequence `σ_N = min(τ_N, N) ↑ ⊤` (exit times capped in time) plus
> per-`N` continuous true martingales agreeing with `M` on `{t ≤ σ_N}`. The engine is the double
> cutoff `f(φₙ·,φₙ·)` (time *and* space), whose globally-bounded derivatives let
> `ito_formula_td_process` apply; the all-time agreement is `indistinguishable_on_stochInterval`. The
> Degenne-`IsLocalMartingale`-typeclass packaging remains as drift-integral-adaptedness plumbing.
> **The time-dependent Itô formula now holds as a process identity for every `t ≤ T`
> simultaneously** (`Foundations/ItoFormulaProcess.lean`, entry `sc-ito-formula-td-process`,
> **`full`**): `f(t,B_t) − f(0,B_0) =ᵐ (itoProcessL2Inf t F) + ∫₀ᵗ (f_t + ½f_xx)(s,B_s) ds`, the
> stochastic term the genuine Itô-integral **process** `(f_x(·,B) ● B)_t` — a continuous `L²`
> martingale admitting an everywhere-continuous **local-martingale** modification on the
> null-augmented Brownian filtration. So the compensated process `f(t,B_t)−f(0,B_0)−∫₀ᵗ drift` is
> (a modification of) a continuous local martingale: *Itô's lemma as a semimartingale
> decomposition*. This makes the `[0,∞)` continuous-local-martingale tower load-bearing as an
> Itô-**formula** consumer for the first time, and is the prerequisite for the unrestricted-`C²`
> (stopping-time localization) Itô formula. The construction is entirely inside the Itô tower —
> **no Markov property, no PDE**: the terminal formula's witness is now canonical
> (`ito_formula_td_L2_bddDeriv` exposes `gfx =ᵐ [f_x(·,B)]`), zero-extended to a `[0,∞)`
> integrand `F` (`exists_fullHorizon_extension`) and matched to each horizon via the existing
> consistency `itoProcessL2Inf_eq_itoProcessCLM`. Earlier (corpus 298): **the Itô
> formula decomposes `f(X)` for a general `C³` exp-growth `f` against a constant-coefficient Itô
> process** `X_t = X₀ + b·t + σ B_t` (`Foundations/ItoFormulaItoProcess.lean`,
> `sc-ito-formula-ito-process`, **`full`**),
> `f(X_T) − f(X₀) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ (f'(X)·b + ½f''(X)·σ²) ds`, `gfx =ᵐ [σ·f'(X_·)]`. Earlier:
> **Geometric Brownian motion is decomposed by the genuine continuous
> Itô integral** (`Foundations/ItoFormulaGBM.lean`, entries `sc-ito-formula-gbm` and
> `sc-discounted-gbm-ito`, both **`full`**) — the **first pricing-ward consumer of the analytic
> Itô tower**, which until now had *none* (GBM/BS pricing ran via separate algebraic towers and
> the Wald exponential). `ito_formula_gbm` gives `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ m·Ŝ ds` with `gfx =ᵐ [σ·Ŝ(·)]`
> for the GBM value `Ŝ(t)=S₀ exp((m−σ²/2)t+σ B_t)`, the stochastic term the *real* Itô integral.
> The route is the classic one — **localization in time**: the GBM value is `t`-exponential (fails
> the localized formula's `t`-uniform growth), so the localized formula is applied to the
> time-localized exponent `S₀ exp((m−σ²/2)·φₙ(t)+σx)` (`φₙ` = smooth cutoff, `n=⌈T⌉₊`), the
> identity on `[0,T]` yet globally bounded; there `φₙ=id`, `φₙ'=1`, so the localization drift
> `(m−σ²/2)·Ŝ` and the Itô correction `½σ²·Ŝ` collapse to `m·Ŝ`. Setting `m=0`
> (`discountedGBM_eq_itoIntegral`) makes the drift vanish — the Itô-integral content of the
> discounted-GBM martingale (`discountedGBM_isMartingale`, there via the Wald exponential).
> Axioms-clean `[propext, Classical.choice, Quot.sound]`. Earlier:
> **The time-dependent Itô formula reaches at-most-exponential growth**
> (`Foundations/ItoFormulaLocalized.lean`, entry `sc-ito-formula-localized`, **`full`**):
> `ito_formula_td_localized` lifts the bounded-derivative `ito_formula_td_L2_bddDeriv` to `f`
> with `|f_• t x| ≤ C·exp(λ|x|)`, so it reaches the Black–Scholes/GBM value function
> `f(t,x)=S₀ exp((r−σ²/2)t+σx)` — the named out-of-scope gap of 7.1.1/7.1.2. An L²-cutoff
> localization *consumes* the bounded engine: smooth truncation `φₙ` (a `ContDiffBump`
> antiderivative), the cutoff `fₙ=f(t,φₙ(x))` through `cutoff_bddDeriv`, then `n→∞` — boundary
> and drift converge in `L²(μ)` (Brownian marginals have every exponential moment,
> `BrownianExpMoment`; the drift dominator is the new base stone `pathIntegral_expGrowth_memLp`),
> so `aₙ=itoIntegralCLM_T gfxₙ` is Cauchy, the Itô **isometry** transfers Cauchy-ness to the
> integrands, completeness gives the witness, CLM **continuity** identifies the limit, and an
> a.e.-identification pass names it (`gfx =ᵐ [f_x(·,B_·)]`).
> Axioms-clean `[propext, Classical.choice, Quot.sound]`. Earlier:
> **The unbounded-horizon Itô integral is a continuous local martingale on
> the whole half-line `ℝ≥0`** (`Foundations/ItoIntegralProcessLocalMartingaleInfinite.lean`,
> entry `sc-ito-infinite-local-martingale`, **`full`**): an everywhere-continuous
> representative modifying the process at *every* `t`. The per-horizon `[0,T=n]` continuous
> local martingales are **glued** — horizon consistency (`itoProcessL2Inf_eq_itoProcessCLM`,
> resting on a hand-built `[0,T]` clamp of Degenne's `SimpleProcess`) makes each a
> modification of the *same* unbounded-horizon process and
> `indistinguishable_of_modification_on` agrees them on overlaps — into one path continuous
> on all of `ℝ≥0`; with **no horizon clamp**, the martingale property is the *global*
> `itoProcessL2Inf_isMartingale` through `condExp_sup_nulls`. This crowns the
> pathwise-regularity layer (2026-06-26): the
> L²-valued process `(φ●B)_t` has a **continuous modification on `[0,T]`**
> (`Foundations/ItoIntegralProcessContinuousModification.lean`, entry
> `sc-ito-general-continuous-modification`, **`full`**) — the first sample-path result for the
> *general* integrand, via Degenne's continuous-time Doob maximal inequality + Borel–Cantelli
> on a fast subsequence — upgraded to a genuine **continuous local martingale**
> (`Foundations/ItoIntegralProcessLocalMartingaleGeneral.lean`, entry
> `sc-ito-general-local-martingale`, **`full`**): the everywhere-continuous representative,
> adapted to the **null-augmented** Brownian filtration `𝓕ᴮ ⊔ 𝓝`, meets Degenne's
> `IsLocalMartingale` interface. The measure-theoretic core is `condExp_sup_nulls`
> (cond-expectation invariance under the null augmentation, its σ-algebra crux consuming
> Mathlib's `eventuallyMeasurableSpace`); both are axioms-clean and non-redundant with
> Degenne's sorry-backed general càdlàg modification. Earlier this day: the **d-asset**
> one-period FTAP `ftap_one_period_vector`
> (`Foundations/FTAPOnePeriodVector.lean`, entry `mf-ftap-one-period-vector`, **`full`**)
> is the unrestricted Föllmer–Schied 1.6 for a discounted excess return valued in any
> **finite-dimensional** inner-product space `F` (the `ℝᵈ` market is `F = EuclideanSpace ℝ
> (Fin d)`) — **no non-redundancy hypothesis**. The explicit **Esscher / minimal-divergence**
> EMM minimises the convex softplus potential `θ ↦ ∫ log(1 + exp⟪θ,Y⟫)`; it is constant
> along the **gains kernel** `N = {θ : ⟪θ,Y⟫ = 0 a.e.}` and coercive on `Nᗮ`, so a
> minimiser on `Nᗮ` is automatically global (redundant directions are absorbed, dropping
> the earlier non-redundancy assumption), and its first-order condition (differentiation
> under the integral) hands back the strictly-positive bounded density `σ⟪θ₀,Y⟫`. No
> Hahn–Banach, no L⁰-closedness, no measurable selection — those remain only for the
> general-Ω **multi-period** DMW. General-Ω one-period **Fundamental Theorem of Asset Pricing**
> (Föllmer–Schied 1.55 / one-period Dalang–Morton–Willinger): `ftap_one_period`
> — for a scalar `L⁰` excess return on an **arbitrary** probability space, no
> arbitrage ⟺ ∃ equivalent martingale measure `Q ~ P` with `Y` integrable and
> `E_Q[Y] = 0` (`Foundations/FTAPOnePeriod.lean`, entry
> `mf-ftap-one-period-general`), backward via a bounded-density reduction to `L¹`,
> the scalar no-arbitrage dichotomy, and a two-region balancing `withDensity` —
> no Hahn–Banach, no Kreps–Yan. This is the genuine measure-theoretic step beyond
> the finite-Ω **Harrison–Pliska** `ftap_discrete` (no arbitrage ⟺ ∃ EMM,
> multi-period, finite Ω, scalar discounted asset; `Foundations/FTAPDiscrete.lean`,
> entry `mf-ftap-discrete-complete`), itself backward via a global geometric
> Hahn–Banach separation of the attainable-gains subspace from the standard simplex
> (the reusable kernel `Foundations/ConvexSeparation.lean`) and forward via
> martingale-transform telescoping; plus the single-period multi-state biconditional
> `hasEMM_multi_iff_not_hasArbitrage` (entry `mf-ftap-single-period-complete`).
> Open follow-on: the general-Ω **multi-period** DMW (L⁰-closedness + measurable
> selection, absent from the pin) — the d-asset one-period case is now closed in full
> (`ftap_one_period_vector`, redundant assets included).
> Since B3: **D1** (the **bilinear Itô isometry** — the `[0,T]` Itô CLM bundled as
> a `LinearIsometry`, so it preserves the L²-inner product by polarization:
> `𝔼[(∫φ dB)(∫ψ dB)] = ⟪φ, ψ⟫`, the diagonal recovering the isometry;
> `Foundations/ItoIntegralCovariation.lean`, entry
> `sc-ito-covariation-bilinear-isometry`). Earlier on the Itô tower: **B2**
> (unbounded-horizon `[0,∞)` σ-finite Itô integral CLM
> `itoIntegralL2`, `Foundations/ItoIntegralL2Dense.lean`, entry
> `sc-ito-infinite-horizon-isometry`) and **B3** (the elementary Itô integral as
> a continuous **local martingale** — pathwise continuity + Degenne's
> `Martingale.IsLocalMartingale`, `Foundations/ItoIntegralProcessLocalMartingale.lean`,
> entry `sc-ito-simple-process-local-martingale`). The figures further below are
> the historical 2026-05-20 audit record, kept as provenance.
>
> **Summit B / B1b round (2026-06-12).** The **general-integrand** Itô integral
> `(φ●B)_t = ∫₀ᵗ φ dB` for a general predictable `φ ∈ L2Predictable[0,T]`, as a
> continuous L² martingale on `[0,T]` (`Foundations/ItoIntegralProcessGeneral.lean`).
> It extends B1a (simple integrands) by density along the *same* `simpleAssembly_T`
> embedding that builds the terminal CLM `itoIntegralCLM_T`, so the bridge to B1a
> is definitional (`extendOfNorm_eq`). The key identity
> `(φ●B)_t = E[∫₀ᵀ φ dB | 𝓕_t]` (the `condExpL2` projection of the terminal
> integral) yields the L² martingale property (condExp tower), a.e.-adaptedness,
> the Itô contraction `‖(φ●B)_t‖ ≤ ‖φ‖`, the terminal isometry `‖(φ●B)_T‖ = ‖φ‖`,
> and L²-continuity (uniform approximation via the t-free contraction). 3 new
> `full` entries: `sc-ito-general-martingale` / `-terminal-isometry` /
> `-l2-continuity`. **Honest scope:** finite-horizon `[0,T]`, L² sense.
>
> **Isometry round (2026-06-12).** The explicit per-t isometry
> `E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds` — deferred at B1b — is now **proved**
> (`itoProcessCLM_norm_sq`, `Foundations/ItoIntegralProcessIsometry.lean`, entry
> `sc-ito-general-time-isometry`): the band-restricted simple-process isometry
> (B1a's per-endpoint-`∧t`-truncated rectangle double sum = the joint-overlap-`∩(0,t]`
> double sum, equal by a pure-ℝ interval-length identity) transfers to all predictable
> `φ` by `DenseRange.equalizer` — both `‖(φ●B)_t‖²` and `∫_{(0,t]}φ²` (`= ‖truncCLM φ‖²`,
> the band-truncation CLM) are continuous and agree on the dense simple processes. The
> generic `lp_two_norm_sq` was de-privatised in `ItoIntegralL2` and reused (no
> duplication). Net: corpus 280 → **281**, 245 → **246 full**; lake build 8724 jobs
> green, axioms-clean. (B2 — the infinite-horizon `[0,∞)` σ-finite extension —
landed 2026-06-13: `itoIntegralL2` / `itoIntegralL2_norm` in
`Foundations/ItoIntegralL2Dense.lean`, corpus entry `sc-ito-infinite-horizon-isometry`.)

Refresh with:

```bash
python3 -m tools.verify.coverage_report
```

Coverage as of 2026-06-22 (extended mathematical-finance pass: put greeks, higher-order BS greeks including charm, Bachelier greeks, digital greeks, BS-Merton with dividends, Garman-Kohlhagen FX, Black-76 greeks; second pass: Bachelier γ/θ, asset-or-nothing γ, BS-Merton δ/γ/vega, American options in binomial tree; third pass: CRR drift-quotient limit closing the analytic content of CRR-to-BS; fifth pass: cash-or-nothing digital gamma closing the previously deferred quotient-rule item; sixth pass: full digital ρ/vega/θ matrix for cash and asset variants — 6 theorems closing the remaining digital Greek gap; seventh pass: Black-76 ρ and θ closing the futures-options Greek set; eighth pass: CRR drift limit n-form `n·(2p_n−1)·σ·√(T/n) → (r−σ²/2)T` closing the previously deferred substitution work; ninth pass: Phase 5 broader mathematical-finance — fixed-income ZCB pricing/yield/duration/convexity, two-asset Markowitz portfolio theory with completing-the-square factorization, CAPM beta + portfolio linearity — 12 theorems extending the project beyond derivatives pricing into fixed income and portfolio theory; tenth pass: Phase 6 quant-risk + N-asset portfolio + bond immunization — Gaussian VaR/CVaR closed forms with affine/scaling identities, bond portfolio rate sensitivity + Redington-style first-order immunization, N-asset Markowitz variance via Finset double sum with diagonal/iid/PSD/two-asset specializations — 15 theorems; eleventh pass: Phase 7 performance / coherent risk / fixed-income depth / static bounds / two-fund separation — Sharpe (√T scaling + scale invariance) + Kelly criterion, gaussian VaR/CVaR coherent risk-measure axioms (translation, homogeneity, monotonicity, gaussian subadditivity via joint-stdev triangle inequality), annuity geometric-series closed form + forward/spot consistency + coupon-bond YTM monotonicity, Phi ≤ 1 + BS call/put price upper bounds + box-spread arbitrage identity, capital market line equation + Sharpe invariance + two-fund decomposition — 23 theorems extending the project into performance measurement, axiomatic risk, and multi-fund portfolio theory; twelfth pass: Phase 8 extended performance / second-order immunization / Asian option inequality — Sortino/Treynor/Information ratios + tracking-error decomposition, second-derivative bond rate sensitivity ∂²P/∂r² = C_P·P + Redington second-order convexity-matching immunization, two-element and equal-weight n-element AM-GM with two-date geometric ≤ arithmetic Asian payoff bound — 13 theorems; **thirteenth pass: Phase 9 credit-risk + strike Greeks + multi-period Kelly** — reduced-form credit spread under constant hazard with survival monotonicity, BS strike-direction derivatives (∂_K bsV, ∂_K bsP, ∂²_K bsV) via magic-identity collapse + put-call parity, multi-period Kelly criterion with myopia + fraction sign analysis — 14 theorems):
**267 / 284 delivery-ready** (249 full + 18 library wrappers), 17 reduced cores, 0 placeholders.

> **2026-08-07 — vNM expected-utility round (#178).** Added one `full` benchmark entry
> covering the mixture algebra of finite-outcome lotteries, affinity of expected utility
> in the mixture, the von Neumann–Morgenstern axioms verified for the expected-utility
> preference (completeness, transitivity, independence, Archimedean continuity with the
> indifference weight exhibited), and invariance of the preference under positive affine
> rescaling of the utility. Soundness direction only — the representation theorem
> (axioms ⟹ ∃u) is deliberately out of scope and the module doc records it.

> **2026-08-02 — downside-performance round (#73).** Added one `full` benchmark entry
> covering finite-state Omega nonnegativity and its threshold identity, maximum-drawdown
> nonnegativity and nonnegative scaling on finite price paths, and positive-scaling
> invariance of the Calmar ratio. The corrected drawdown theorem deliberately assumes
> `0 ≤ c`; negative scaling reverses peak-to-trough order and is not claimed.

> **Poisson cluster + Itô-QV upgrade round (2026-06-05).** Four reduced cores
> earned `full` by replacing statement-level specs with genuine derivations,
> each backed by a new `Foundations/` module: `pp-thm-3.3.9` (superposition —
> the Poisson convolution identity `Poisson(a) ∗ Poisson(b) = Poisson(a+b)`,
> absent from Mathlib, proved by singleton-ext + binomial collapse;
> `PoissonSuperposition.lean`), `pp-thm-3.3.10` (thinning — the
> binomial-marking factorisation into `Poisson(pr) ×ₘ Poisson((1−p)r)`, so the
> thinned marginals AND the independence of the streams are derived;
> `PoissonThinning.lean`), `pp-thm-3.3.5` (marginal law re-earned via the
> interarrival-construction route this file had flagged: Erlang arrival law
> composed with the new Gamma-CDF difference identity
> `∫₀ᵗ γ_k − ∫₀ᵗ γ_{k+1} = e^{−rt}(rt)ᵏ/k!`; `PoissonCounting.lean`), and
> `sc-thm-7.4.5` (QV of an Itô process in the constant-σ/Lipschitz-drift
> regime — drift contributes nothing, with explicit `1/n` L² rates;
> `ItoProcessQV.lean`; the previous spec was degenerate — its "stochastic
> piece" was a Lebesgue integral of σ). `pp-prop-3.3.6` stays `reduced_core`
> honestly but its core is now derived, not assumed: the FIRST interarrival
> is proved exponential from the counting axioms and the memoryless survival
> factorisation is proved from independent increments
> (`PoissonInterarrival.lean`); the full-sequence iid claim still needs the
> strong Markov property (upstream-gated). Net: **225 full + 18 wrappers =
> 243 / 261 delivery-ready, 18 reduced cores.**

> **Finance layer over the Poisson/QV track (2026-06-06).** Six new `full`
> entries make the freshly-derived foundations load-bearing in the pricing
> layer: `mf-variance-swap-drift-immunity` (realized variance of GBM
> log-returns → `σ²T` in **L²** for ANY drift — the variance-swap fair
> strike is a QV functional, immune to the physical-vs-risk-neutral drift;
> strengthens the phase-34 expectation-level limit;
> `VarianceSwapDriftImmunity.lean`, first pricing consumer of
> `ItoProcessQV`), `mf-first-to-default-spread` (FtD basket spread = Σ
> single-name hazards under independence — `ExpMin.minimum_survival`
> bridged into the `Credit.lean` vocabulary; `FirstToDefault.lean`),
> `dist-poisson-pgf` (the Poisson pgf `E[x^N] = e^{r(x−1)}` for every real
> `x`, absent from Mathlib; `PoissonPgf.lean`), and the Merton (1976)
> jump-diffusion trio (`mf-merton-call-series`,
> `mf-merton-spot-recombination`, `mf-merton-put-call-parity`): the price
> is *defined* as the expectation over the Poisson jump count, so the
> textbook series, the compensation identity `E[spot_N] = S₀` (the pgf at
> `1+k`), and parity `C − P = S₀ − Ke^{−rT}` are theorems — and every
> series term is separately proved equal to a discounted conditional
> expected payoff (`bs_call_formula` on `(ℝ, gaussianReal 0 1)`).
> Terminal-mixture-law scope, exactly parallel to `BSCallHyp`: the
> compound-Poisson jump *SDE* is upstream-gated and not claimed
> (`MertonJumpDiffusion.lean`). Net: **231 full + 18 wrappers = 249 / 267
> delivery-ready, 18 reduced cores** (corpus 261 → 267).

> **Merton dominance + classic display; Markov path law (2026-06-06, second
> round).** Two new `full` entries deepen the Merton layer:
> `mf-merton-dominance` — *jump risk is never free*,
> `C_BS(S₀,σ) ≤ C_Merton(S₀,σ,k,δ,Λ)` for every `Λ`, `δ`, `k > −1`, proved
> by pricing the two jump channels separately: per-term vol-monotonicity
> (`bsV_strictMonoOn_sigma`, vega) lowers the jump vol to `δ = 0`, and there
> a Jensen floor comes from the new spot-direction convexity
> `bsV_spot_convexOn` (gamma ≥ 0 second-derivative test, the S-direction
> dual of `bsV_strike_convexOn`; `SpotConvexity.lean`) whose supporting
> tangent at `S₀` has its linear term integrate to zero by the compensation
> identity `integral_mertonSpot` (`MertonDominance.lean`). And
> `mf-merton-classic-display` — the textbook `Λ′ = Λ(1+k)` form, driven by
> the rate-shift invariance
> `bsV K r σ (S·e^{cτ}) τ = e^{cτ}·bsV K (r+c) σ S τ`
> (`bsV_spot_exp_rate_shift`) at `c_n = r_n − r` plus Poisson-weight
> absorption (`MertonClassicDisplay.lean`). One reduced core earned `full`:
> `mc-thm-1.1.2` (path distribution of a Markov chain) — the chain's law is
> now *constructed* via the pin's Ionescu–Tulcea trajectory kernels
> (`Kernel.trajMeasure`) from kernels that read only the last history
> coordinate, and `P(X₀=i₀,…,Xₙ=iₙ) = init(i₀)·∏ P(iₖ,iₖ₊₁)` is derived by
> induction through the comp-product recursion of the marginals, replacing
> the prior definitional `rfl` (`Foundations/MarkovPathMeasure.lean`; the
> converse characterization is not claimed). The same `Kernel.traj` re-cost
> found the other five Markov reduced cores still honestly gated: recurrence
> needs renewal theory / fundamental-matrix algebra, convergence needs
> Perron–Frobenius, the ergodic theorem needs both, stationarity-uniqueness
> needs recurrence, and the strong Markov property needs stopping-time
> kernels — none in the pin. Net: **234 full + 18 wrappers = 252 / 269
> delivery-ready, 17 reduced cores** (corpus 267 → 269).

> **Values-gates round (2026-06-06, evening).** The honesty conventions this
> file documents became *mechanically enforced*: `tests/test_values.py` adds
> (1) a forbidden-text scan over `MathFin/` sources (no
> sorry/admit/native_decide/polyrith/`?`-suggestion tactics/hammer/loogle/
> leansearch outside comments), (2) a **definitional-`rfl` tripwire** — no
> `full` entry may cite a theorem whose proof is bare `rfl`/`unfold; rfl`
> (the reduced_core pattern in disguise), (3) blueprint-spine ⊆ curated
> audit, (4) byte-freshness of the new GENERATED exhaustive audit
> `MathFin/AxiomAuditGen.lean`, which `#guard_msgs`-pins every
> proof-position MathFin constant cited by the corpus (222 names vs the
> curated file's headliners). CI (`build.yml`) now runs pytest + `ledger
> status` before the Lean build, so these gates and ledger freshness are
> push-enforced, not session discipline. First-run catches: the tripwire
> demoted `mf-kelly-n-periods-linearity` `full`→`reduced_core` (its cited
> lemma states `T·kellyGrowth = T·(unfolded formula)` by `rfl`; the genuine
> multi-period iid model is not formalized — same class as the 2026-05-29
> newton-raphson demotion, now pinned in `EXPECTED_REDUCED_CORE_THEOREMS`),
> and the blueprint-coverage check found seven spine headliners unguarded
> (including `bs_identity`), now pinned in the curated audit. Net: **233
> full + 18 wrappers = 251 / 269 delivery-ready, 18 reduced cores.**

> **Summit A′ round (2026-06-07).** Two reduced cores earned `full`, each by
> replacing the named gap with the actual mathematics. (1)
> `mf-kelly-n-periods-linearity` — repairing the previous round's
> definitional-`rfl` demotion: the n-period iid model is now real measure
> theory (`Performance/Kelly.lean`): one period's wealth multiplier is the
> two-point law `kellyReturnMeasure p b f`, n periods are its n-fold
> `Measure.pi`, and `E[∑ log Rᵢ] = n·kellyGrowth p b f` is *computed* via
> linearity of expectation through the product measure's coordinate
> evaluations. (2) `sc-thm-7.1.2` — the **time-dependent Itô formula**
> (Summit A′): `f(T,B_T) − f(0,B₀) = ∫₀ᵀ f_x(s,B_s) dB_s +
> ∫₀ᵀ (f_t + ½f_xx)(s,B_s) ds` a.e., the classical `df = f_x dB +
> (f_t + ½f_xx) dt`, with the stochastic integral the genuine
> `itoIntegralCLM_T`. The three Summit-A limit arguments redone with
> `(t,x)`-dependence: `WeightedQuadraticVariation` generalized to bounded
> **adapted weight processes** (the fluctuation engine never cared the
> weight was `g(B_s)`; `tendsto_riemann_L2_process` exported standalone for
> the drift term), the 2D Itô–Taylor remainder vanishing at `O(1/n)`
> (`ItoFormulaTDRemainder.lean` — time/cross/space split bounded by
> `C_tt Δt² + C_tx|ΔB|Δt + C_xxx|ΔB|³`), and the time-dependent Riemann↔CLM
> bridge (`ItoIntegralRiemannBridgeTD.lean`). Assembly in
> `Foundations/ItoFormulaTD.lean`; `f_t`'s joint continuity is *derived*
> from its bounded partials (jointly Lipschitz), not assumed; unbounded
> coefficients stay the named gap, as in 7.1.1. All four new headliners
> axiom-pinned in the curated audit and the spine node
> `thm:ito-formula-td-l2` added. Net: **235 full + 18 wrappers = 253 / 269
> delivery-ready, 16 reduced cores.**

> **Deferred-cleanup round (2026-06-09).** Executed the round-5 values-review
> follow-up catalogue. (1) **Corpus faithfulness** — `sc-thm-8.2.5` (SDE
> existence/uniqueness) encoded its diffusion as a Lebesgue `∫σ ds`, leaving the
> Brownian driver `B` dead (a random-IC ODE, not an SDE); fixed to an opaque
> adapted stochastic-integral process `IσX` (= `∫₀ᵗ σ dB`), mirroring
> `sc-thm-7.5.2`'s opaque Itô-integral fields. Stays `reduced_core`, now faithful.
> *(Round-6 correction, 2026-06-09: that rewrite's uniqueness clause quantified a free
> per-candidate integral `IσY`, which made the spec **uninhabitable** — any process
> discharges the solution premise by taking its own residual as "integral". Repaired
> with an opaque integral-operator encoding `Iσ : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ` consumed
> as `Iσ X` / `Iσ Y`, the uniqueness conclusion scoped to `0 ≤ t`, a `: Prop`
> ascription, and an in-snippet inhabitant `example` guarding non-vacuity.)*
> (2) **Orphan wiring** — three documented-but-unwired Foundations bridges became
> `full` corpus entries: `mf-ftap-multi-state-forward` (Phase 42 forward FTAP, EMM
> ⟹ no-arbitrage in arbitrary finite state + assets), `mf-pricing-kernel-butterfly`
> (Phase 53 FTAP state-price butterfly no-arbitrage), `mf-variance-swap-equivalence`
> (Phase 45 log-payoff strike = realised-variance QV limit). The literal
> anti-wrapper re-export `varianceSwap_equivalence` (subsumed by the genuine
> two-functional theorem) was removed. `StochasticInterval` was reflected on and
> **kept** — it is the Degenne #440 upstream-PR body, anchored by two AxiomAudit
> entries and named as the `ElementaryPredictableSet` gap in the deferred
> Itô-CLM coherence record. (3) **Blueprint** — the keystone
> `bsV_satisfies_bs_pde_via_feynmanKac` and the kernel heat equation
> `feynmanU_heat_equation` are now `@[blueprint]` spine nodes (with curated
> AxiomAudit guards); the regenerated spine shows the FK tower linking into the
> existing `bsCall` node. Net: **239 full + 18 wrappers = 257 / 273
> delivery-ready, 16 reduced cores** (corpus 270 → 273). lake build 8708 jobs,
> axiom-clean; ledger 273/273 fresh; gate tests green.

> **2026-06-09 — values round 6 (whole-repo, 8-lens panel).** Three blockers found and fixed:
> `sc-thm-8.2.5`'s round-5 rewrite was **uninhabitable** (free per-candidate `IσY`; repaired with
> the opaque integral-operator encoding + conclusion scoped to `0 ≤ t` + an in-snippet inhabitant
> guard — refutation and inhabitant both daemon-checked); Vasicek's claimed-but-absent limit
> theorem (added for real: `vasicekDeterministic_tendsto_mean`); RatiosExtended's claimed-but-
> absent variance expansion (de-claimed). Corpus honesty: `mf-compound-poisson-mgf` demoted to
> `reduced_core` (exp-algebra core only); `mf-credit-spread-time-avg-hazard` now exports the
> definitional identity *and* the substantive FTC recovery; André's reflection principle wired as
> the new `full` entry `mf-reflection-principle-counting`. PricingKernel recomposed so its FTAP
> lineage and `statePricePricing` consumption are definitional. Net: corpus 273 → **274**,
> **239 full + 18 wrappers = 257 / 274 delivery-ready**, 17 reduced. lake build 8708 jobs green,
> ledger 274/274 fresh, 19 gate tests green. Full findings ledger: `docs/values-review.md`.

> **Feynman–Kac → Black–Scholes-PDE keystone round (2026-06-08).** The new
> `full` entry `sc-bs-pde-feynman-kac` (`bsV_satisfies_bs_pde_via_feynmanKac`)
> re-derives the Black–Scholes PDE `−∂_τV + ½σ²S²∂_SSV + rS∂_SV − rV = 0` from
> the Feynman–Kac representation — through the heat kernel's joint
> Fréchet-differentiability (`hasFDerivAt_heatKernel`) and a parametric
> differentiate-under-the-integral skeleton, *not* from Itô — closing the
> long-standing two-tower gap between the deep heat-kernel/Itô foundations and
> the pricing layer (the orphaned `feynmanU` heat flow is now load-bearing for
> pricing; `Foundations/FeynmanKacHeatEquation.lean` +
> `BlackScholes/PDEFromFeynmanKac.lean`). In the same pass the Feynman–Kac scope
> note on `sc-thm-9.2.1` was de-staled: its "~300–500 lines left as upstream
> work" claim was false — that infrastructure is now built and consumed by the
> keystone. Net: **236 full + 18 wrappers = 254 / 270 delivery-ready, 16 reduced
> cores** (corpus 269 → 270).

> **Duplication + status audit (2026-06-03).** A five-reviewer sweep of all 216
> then-`full` entries asked two questions: does any MathFin module re-derive
> content already in pinned Mathlib / Degenne's BrownianMotion package, and is
> any `full` really a wrapper? The foundations tower came back clean — the
> package at pin `fa590b1` has **no** sorry-free L²-adapted stochastic integral
> (it stops at the elementary simple-process integral), no strong-type Doob L^p
> (weak-type only — same as Mathlib, whose own docstring defers the L^p version),
> no Wald/X²−t martingales, no Itô formula; our Wiener-vs-Itô division and the
> BrownianMartingale division-of-labor header were re-verified accurate. The
> Portfolio/Performance/Risk/FixedIncome slice had zero findings (geometric
> series, Cauchy–Schwarz etc. are consumed from Mathlib, never re-proved).
> Verified findings, all applied: `full`→`library_wrapper`:
> `ce-prop-2.1.11-jensen` (Mathlib's `ConvexOn.map_condExp_le_of_finiteDimensional`
> proves textbook Jensen from bare convexity; our explicit-subgradient derivation
> was strictly weaker — `Foundations/CondExpJensen.lean` deleted, benchmark now
> wraps Mathlib), `mf-carr-madan-log` (was a `Real.log_div` alias; alias lemma
> deleted), `cv-prob-space` (`measure_univ`/`measure_empty`).
> `full`→`reduced_core`: `pp-thm-3.3.5` and `mc-thm-1.1.2` (THEOREM-named entries
> whose conclusion is a projected structure field / definitional `rfl`; definition
> entries `bm-def-5.1.1`/`cv-poisson-def`/`mc-def-1.1.1` keep the documented
> definitional-`full` convention). Coherence fix: `am_gm_two` now specializes
> Mathlib's `Real.geom_mean_le_arith_mean2_weighted` instead of re-proving it;
> documented-distinction cross-references added for the Carr–Madan second-order
> remainder (the `n = 1` case of Mathlib's `taylor_integral_remainder`, kept in
> explicit-`HasDerivAt` form) and the StandardNormal MGF (pdf-form vs Mathlib's
> measure-form `mgf_gaussianReal`). New guardrail:
> `test_expected_reduced_cores_stay_reduced_core`. Upstream opportunity recorded
> in `docs/bridges.md` (our L² martingale convergence could discharge the
> package's sorry'd `SquareIntegrable` targets).

> **Honesty re-audit (2026-05-29).** A dedicated benchmark-`formalization_status`
> sweep (four adversarial reviewers over all 11 files / 251 theorems, every
> finding source-verified) reclassified **13 over-credited entries**, dropping
> delivery-ready from 235→222. The pattern was the same one found in the Itô
> stack: a benchmark named after a deep theorem but proving only an algebraic
> shadow / a conclusion read off a hypothesis / an unfaithful library wrapper.
> Reclassified `full`→`reduced_core`: `mf-tangent-portfolio-foc` (FOC by `ring`,
> no calculus), `mf-american-supermartingale` + `mf-american-intrinsic-bound`
> (`le_max` on the Bellman def, not the measure-theoretic supermartingale),
> `mf-kmv-merton-pd` (only the ≤1 bound proved), `mf-markowitz-n-psd`
> (conclusion-in-hypothesis), `mf-newton-raphson-fixed-at-root` (definitional
> unfold), `mart-thm-2.3.6` (wraps the bounded-time submartingale *inequality*,
> not the UI optional-stopping *equality*). `full`→`library_wrapper`:
> `bm-thm-5.1.5` (one-line Degenne re-export). `library_wrapper`→`reduced_core`:
> the 5 `markov_chains` entries whose `library_wrapper` credit rested on a
> since-removed second backend while the active Lean code is a structural
> specification (matching how `poisson_processes` already tiers its structural
> entries). See `docs/deep-review-2026-05-29.md`.
>
> **Upgrade-properly round (2026-05-29).** Rather than only relabel down, two of
> those entries were *earned back to `full`* by re-pointing the benchmark at the
> genuine derivation that **already existed** in the library (the benchmark had
> been wrapping the shallow algebraic lemma instead): `mf-tangent-portfolio-foc`
> now wraps `sharpeSqTwo_critical_iff_crossProduct_FOC` (the Sharpe FOC as a
> genuine `HasDerivAt` critical-point characterisation), and `mf-kmv-merton-pd`
> now wraps `kmvPD_eq_one_sub_survival_probability` (KMV PD = the actual
> risk-neutral default probability `1 − Q(V_T>F)`, via `riskNeutralProb_S_T_gt_K`).
> Both re-pointed snippets were compile-verified. Balancing this, the algebraic
> shadow `mf-kmv-survival-Phi-d2` (the normal-CDF symmetry `1 − Φ(−x) = Φ(x)`,
> previously `full`) was demoted to `reduced_core`. Net: 222→223 delivery-ready,
> but now backed by the genuine theorems. The remaining reduced_core entries are
> either inherently one-line facts (no deeper theorem exists) or gated on
> machinery not yet in Lean — relabeling *those* up would re-introduce the
> overclaim.

> **Summit A — continuous-time Itô formula (2026-06-02).** Promoted `sc-thm-7.1.1`
> (Itô's Formula) `reduced_core`→`full`: the bounded-derivative continuous-time L² Itô
> formula `f(B_T)−f(B_0) = itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds` is now *derived* from
> foundational primitives, with the stochastic integral the genuine continuous Itô integral
> `itoIntegralCLM_T gf'` (the L²-limit of the Riemann–Itô sums). The proof chain (Summit A):
> `tendsto_weighted_qv` (weighted quadratic variation) + `tendsto_ito_remainder` (vanishing
> Itô–Taylor remainder) + `itoIntegralCLM_T_of_bdd_cont` (Riemann↔CLM bridge), assembled in
> `ito_formula_L2_bddDeriv`. Scope: `f ∈ C³` with bounded `f′,f″,f‴` — a faithful but
> strictly C³-bounded specialization of the C² textbook statement (the gap to unrestricted
> C² is Summit C localization, not yet formalized). All four Summit-A theorems are
> `#print axioms`-clean (AxiomAudit-pinned). `coverage_report`: `stochastic_calculus.json`
> 4→5 full, 7→6 reduced.

> **Engine→pricing coherence — deliberate stop (2026-06-03).** The continuous Itô
> engine `itoIntegralCLM_T` has its flagship consumer (`itoIntegralCLM_T_brownian`:
> `∫₀ᵀ B dB = ½(B_T²−B₀²−T)` through the CLM), and the operational continuous-time
> pricing result — the discounted GBM is a `Q`-martingale (`discountedGBM_isMartingale`,
> via the Wald exponential) — is already proved (an AxiomAudit-pinned library theorem). The one *missing* link, identifying the
> discounted price *with* the engine (`e^{−rt}S_t = S₀ + itoIntegralCLM_T(σ·e^{−r·}S_·)`),
> was scoped and **declined**: the GBM exponential is unbounded, so it is not a short
> argument but a second keystone (~400 lines — a parallel clamp-truncation layer plus the
> martingale-difference L² limit `∑σM_{t_k}ΔB → M_T−1`). It would yield an *alternative
> derivation route* to a theorem already held, not a new result, so it is recorded here as
> a known, bounded, **not-pursued** build. See *Geometric Brownian motion* /
> *Continuous-time first FTAP* in `blueprint.md`.

> **Path-1 upgrades (2026-06-04).** Seven reduced cores earned `full` by the
> upgrade-properly discipline (build the genuinely deeper theorem; never relabel):
> `mart-thm-2.3.6` — the conditional-expectation-form **optional sampling
> inequality** for submartingales (`Foundations/OptionalSamplingInequality.lean`),
> absent from Mathlib, derived as *optional sampling equality + monotone
> compensator* through the Doob decomposition;
> `mf-markowitz-n-psd` — PSD **derived** from genuine L² random returns via the
> self-dot variance identity, consuming Mathlib's `variance_sum'`
> (`Portfolio/CovariancePSD.lean`);
> `mf-cvar-rockafellar-uryasev` — the genuine **Rockafellar–Uryasev variational
> theorem** (`IsLeast`) for the Gaussian loss, minimality by the pointwise tail
> certificate (`RiskMeasures/RockafellarUryasev.lean`, which previously recorded
> only the additive identity and explicitly deferred this);
> `mf-newton-raphson-fixed-at-root` — genuine **local quadratic convergence**
> at the sharp Newton–Kantorovich constant `(L/(2m))·e²` (integral form of the
> Taylor remainder) + basin convergence of the Newton iterates
> (`BlackScholes/NewtonConvergence.lean`);
> `mf-kmv-survival-Phi-d2` — re-pointed at the probabilistic survival statement
> `Q(V_T > F) = Φ(DD)` through the lognormal tail;
> `mf-american-supermartingale` + `mf-american-intrinsic-bound` — the
> **path-space Snell envelope** (`Binomial/SnellEnvelope.lean`): payoff
> dominance, supermartingale property, adaptedness, and minimality over
> arbitrary path-processes, plus the identification theorem
> `snell = e^{−rk}·americanPrice` exhibiting the scalar Bellman recursion as
> the Markov instance (the conditional expectation is the explicit node
> average, which on a finite tree it *is* — same pathwise idiom as
> `Binomial/MartingaleRepresentation.lean`).
> All new load-bearing theorems are AxiomAudit-pinned.

> **Post-audit values sweep (2026-06-04, follow-up).** A second adversarial
> audit (four fresh reviewers over the Path-1 commit) confirmed the
> load-bearing layer — counts, statuses, scope notes, axiom pins, and the
> absence of all five headline theorems from Mathlib/BrownianMotion all
> re-verified independently — and surfaced finishing work, applied in full:
> `submartingale_optional_sampling` now consumes Mathlib's
> `Submartingale.monotone_predictablePart` (the local helper had re-derived it
> verbatim) and documents the BrownianMotion package's `sorry`-stubbed `⊓`-form
> sibling as an upstream-donation candidate;
> `portfolioVarN_covariance_eq_variance` consumes `variance_sum'` instead of
> re-tracing its bilinearity chain; **Newton sharpened to the textbook
> constant** — `(L/(2m))·e²` via the integral form of the Taylor remainder,
> basin relaxed to `L·δ ≤ m` (the uniform mean-value bound had silently cost a
> factor 2); two dead `have`s and an orphaned `@[simp]` lemma removed; the
> seven upgraded entries' stale `description` fields rewritten (four still
> asserted pre-upgrade "NOT the stronger result" disclaimers); and the build
> log swept clean — six `ring`-falls-back-to-`ring_nf` info sites and one
> `simpa` lint fixed at root (`congr`/`convert` depth bumps so `ring` sees a
> genuine ring goal instead of `exp A = exp B`).

> **Headline-theorem wiring (2026-06-04, same day).** The library's deepest
> results were benchmark-orphaned — proved on main since 2026-05-30 and
> AxiomAudit-pinned, but visible in no benchmark entry. Three entries added,
> each verified L5 in-container before landing:
> `mf-crr-gaussian-limit` (`crr_tendsto_gaussian_inDistribution` — the
> distributional CLT for the CRR tree: per-step charFun computed exactly,
> upgraded to weak convergence by Lévy's continuity theorem),
> `mf-crr-bs-call-convergence` (`binomialPrice_call_tendsto_bs_closed` — the
> n-step binomial call price converges to the literal
> `S₀·Φ(d₁) − K·e^{−rT}·Φ(d₂)`; bounded-put + put-call-parity route, no
> uniform-integrability machinery), and `gir-continuous-ftap`
> (`discountedGBM_isMartingale` — the discounted GBM is a martingale under
> the risk-neutral measure: the EMM property, i.e. the operational
> continuous-time first FTAP). The stale `mf-crr-prob-half` scope sentence
> claiming the distributional convergence "is upstream-gated on
> triangular-array CLT" (false since 2026-05-30) was corrected to point at
> the new entries. In the same pass, all 157 stale `lean/MathFin/<X>.lean`
> prose path references (the pre-reorg flat layout) were remapped to the real
> `MathFin/<Section>/<X>.lean` paths, using each entry's own compiled imports
> as the authoritative mapping (the old combined files that were *split* in
> the reorg — e.g. `StrikeConvexityAndRiskAdditivity.lean` — map to different
> targets per entry, which a global rename table would have gotten wrong);
> the ten entries whose snippet docstrings changed were re-verified
> in-container.

> **FTAP tower (2026-06-24 through 2026-06-26, corpus 285→289).** Three new
> FTAP rungs, each `full`, built in sequence: (1) **finite-Ω multi-period FTAP**
> `ftap_discrete` (`mf-ftap-discrete-complete`) — Harrison–Pliska for a scalar
> discounted excess return on a full-support finite probability space and a finite
> discrete filtration; backward via a global geometric Hahn–Banach separation of
> the attainable-gains subspace from the standard simplex (the reusable kernel
> `Foundations/ConvexSeparation.lean`) and forward via martingale-transform
> telescoping (`Foundations/FTAPDiscrete.lean`). (2) **General-Ω one-period
> scalar FTAP** `ftap_one_period` (`mf-ftap-one-period-general`) — Föllmer–Schied
> 1.55 for an arbitrary probability space and a single scalar `L⁰` excess return;
> backward via a bounded-density reduction to `L¹`, the scalar no-arbitrage
> dichotomy, and a two-region balancing `withDensity` — no Hahn–Banach, no
> Kreps–Yan (`Foundations/FTAPOnePeriod.lean`). (3) **D-asset one-period FTAP**
> `ftap_one_period_vector` (`mf-ftap-one-period-vector`) — Föllmer–Schied 1.6 for
> any finite-dimensional inner-product space `F`; the Esscher/minimal-divergence
> EMM minimises the convex softplus potential `θ ↦ ∫ log(1 + exp⟪θ,Y⟫)`, which
> is coercive on `Nᗮ` (the orthogonal complement of the gains kernel `N = {θ :
> ⟪θ,Y⟫ = 0 a.e.}`), so its minimiser on `Nᗮ` is automatically global; the
> first-order condition (differentiation under the integral) produces the
> strictly-positive bounded density; redundant assets are absorbed by `N`,
> dropping the earlier non-redundancy assumption (`Foundations/FTAPOnePeriodVector.lean`).
> `isEquivProbMeasure_withDensity` de-duplicated into `Foundations/EquivMeasure.lean`.
> Net: corpus 285 → **289**, **254 full** + 18 = 272/289 delivery-ready, 17 reduced.
> Open rung: general-Ω multi-period DMW (L⁰-closedness + measurable selection).

> **Itô pathwise regularity arc (2026-06-25 through 2026-06-26, corpus 289→292).**
> Three full entries complete the pathwise-regularity layer. (1) **Continuous
> modification on `[0,T]`** (`sc-ito-general-continuous-modification`,
> `exists_continuous_modification_itoProcess`,
> `Foundations/ItoIntegralProcessContinuousModification.lean`, corpus 290): the
> general-integrand Itô process `t ↦ (φ●B)_t` admits an a.s.-continuous
> representative agreeing a.e. with the L² value at each `t ≤ T`. Route: Degenne's
> continuous-time Doob maximal inequality → Chebyshev on simple-process maxima →
> Borel–Cantelli on a fast subsequence (geometric `2⁻ⁿ` bounds) → pathwise uniform
> convergence on the subsequence → continuous limit process `itoContinuousMod`.
> The running-max keystone binds the pathwise norm under the supremum over `[0,T]`.
> (2) **Continuous local martingale on `[0,T]`** (`sc-ito-general-local-martingale`,
> `exists_continuous_localMartingale_modification`,
> `Foundations/ItoIntegralProcessLocalMartingaleGeneral.lean`, corpus 291): the
> continuous modification is upgraded to a genuine `IsLocalMartingale` on the
> **null-augmented** Brownian filtration `𝓕ᴮ ⊔ 𝓝`. The measure-theoretic core is
> `condExp_sup_nulls` (conditioning on the null augmentation agrees a.e. with
> conditioning on `𝓕ᴮ`, its σ-algebra crux consuming Mathlib's
> `eventuallyMeasurableSpace`); the null-augmentation setup shows every
> `(𝓕 ⊔ 𝓝)`-measurable set is a.e. a `𝓕`-set. Non-redundant with Degenne's
> (sorry-backed) general càdlàg modification. (3) **Continuous local martingale on
> `[0,∞)`** (`sc-ito-infinite-local-martingale`,
> `exists_continuous_localMartingale_modification_infinite`,
> `Foundations/ItoIntegralProcessLocalMartingaleInfinite.lean`, corpus 292): the
> per-horizon `[0,T=n]` continuous local martingales are **glued** into one path
> continuous on all of `ℝ≥0`. Horizon consistency (`itoProcessL2Inf_eq_itoProcessCLM`,
> resting on a hand-built `[0,T]` clamp of Degenne's `SimpleProcess` and the
> band-restriction CLM `restrictToBand`) makes each finite-horizon local martingale a
> modification of the *same* unbounded-horizon process; `indistinguishable_of_modification_on`
> agrees them on overlaps. With no horizon clamp, the martingale property is the
> *global* `itoProcessL2Inf_isMartingale` delivered through `condExp_sup_nulls`.
> All three entries are axioms-clean and values-panel PASS. Net: corpus 289 → **292**,
> **257 full** + 18 = 275/292 delivery-ready, 17 reduced, 0 placeholders.

> **Itô → pricing bridge: the deterministic-integrand Wiener integral is Gaussian, and
> the Vasicek terminal law derived (2026-06-27, corpus 292→294).** The deep Itô tower
> (complete through the `[0,∞)` continuous local martingale) gained its first
> *deterministic-integrand* pricing consumer. `sc-wiener-integral-gaussian`
> (`wienerIntegralLp_map_eq_gaussianReal`, `Foundations/WienerIntegralGaussian.lean`):
> a deterministic-integrand Wiener integral is `gaussianReal 0 ‖f‖²` — the distribution
> the isometry construction left open — by the characteristic-function route
> (simple-process Gaussianity via `IsGaussianProcess.of_isGaussianProcess` +
> `map_eq_gaussianReal`, lifted to all `L²` by a `|t|`-Lipschitz-charFun
> `DenseRange.induction_on` + `Measure.ext_of_charFun`). Its consumer
> `mf-vasicek-sde-terminal-gaussian` (`vasicekShortRate_hasLaw_gaussian`,
> `FixedIncome/VasicekSDEGaussian.lean`) **derives** the Vasicek terminal law
> `r_T ~ N(vasicekSDEMean, σ²(1−e^{−2κT})/(2κ))` that `VasicekSDE.lean` previously only
> posited — variance via the FTC integral `∫₀ᵀ e^{−2κ(T−s)} ds`, affine transport via
> `gaussianReal_const_mul`/`gaussianReal_const_add`. First Itô-tower consumer in
> FixedIncome. Both axioms-clean. Net: corpus 292 → **294**, **259 full** + 18 =
> 277/294 delivery-ready, 17 reduced, 0 placeholders.

The line below is the pre-re-audit historical record (kept for provenance):
**235 / 251 delivery-ready** (211 full + 24 library wrappers), 16 reduced cores, 0 placeholders.

## History

Per-pass session logs and the pre-2026-05 hybrid-backend validation records
were removed from this file on 2026-05-30, when the SymPy and Isabelle backends
were stripped (the project is Lean-only). They remain in git history. The
2026-05-29 honesty re-audit — the basis for the current counts above — is also
recorded in `docs/deep-review-2026-05-29.md`.
