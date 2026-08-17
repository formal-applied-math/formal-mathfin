# The leaps: deriving the risk-neutral measure and beyond

The static Black-Scholes world in this library is complete and axioms-clean,
but for a long time it rested on one *assumption*: `BSCallHyp` — "the driver
`Z` is standard normal under the risk-neutral measure `Q`" — was a hypothesis
that 14 pricing files took on faith. The 2026-05-23 "leaps" close that gap and
push past it. Each leap is foundation-certain and build-enforced
(`MathFin/AxiomAudit.lean`); none introduces a hypothesis-form theorem whose
substantive hypothesis is left undischarged.

This document is the narrative. For the per-theorem audit see
[`coverage.md`](coverage.md); for the bridge catalogue see
[`bridges.md`](bridges.md).

## Leap 1 — static Girsanov: the risk-neutral measure is *derived*

`MathFin/Foundations/GaussianGirsanov.lean`.

`BSCallHyp` is no longer an axiom. The risk-neutral measure `Q` is
*constructed* from the physical measure `P` by an explicit Radon-Nikodym
(Esscher) density, and the recentred driver is *proven* standard normal under
it. The deductive chain, bottom-up:

| Step | Theorem | Content |
|---|---|---|
| 1 | `gaussian_esscher_pdf` | Completing the square: `exp(c·x − c²/2)·φ₀,₁(x) = φ_c,₁(x)`. |
| 2 | `gaussianReal_withDensity_esscher` | Measure level: tilting `N(0,1)` by the Esscher density gives exactly `N(c,1)` — mean shift `c`, variance fixed. The static (single-Gaussian) Girsanov theorem. |
| 3 | `map_withDensity_comp` | Pushforward commutes with a density factoring through the map: `(P.withDensity (g∘W)).map W = (P.map W).withDensity g`. Proved from `Measure.ext` + `setLIntegral_map`; **upstreamable to Mathlib**. |
| 4 | `hasLaw_esscher_tilt` | Girsanov for a random variable: if `W ~ N(0,1)` under `P`, then `W ~ N(c,1)` under `Q := P.withDensity(exp(c·W − c²/2))`. |
| 5 | `hasLaw_sub_const` | Recentring: `W − c ~ N(0,1)` under `Q`. |
| 6 | `esscherTilt_isProbabilityMeasure` | `Q` is a probability measure (the Esscher density is normalised). |
| 7 | **`BSCallHyp.exists_of_physical`** | **The capstone.** There exists a probability measure `Q` — the explicit Esscher tilt — under which `BSCallHyp` holds for the recentred driver. The risk-neutral hypothesis is now a *theorem*. |
| 8 | `bsTerminal_physical_eq_riskNeutral` | The conceptual heart: the Girsanov shift `c = (r − μ)·√T/σ` reprices the *same* asset with drift `μ → r`. `S_T` is invariant; only its drift changes. |

Economic reading: `c = −θ·√T` with market price of risk `θ = (μ−r)/σ`; the
recentred driver `W − c = W + θ√T` is the risk-neutral driver. This is the
slice of Girsanov tractable without the path-wise stochastic integral.

## Leap 2 — the genesis cascade: physical → EMM → pricing

`MathFin/Foundations/GaussianGirsanov.lean` (same file).

Two composites wire the Girsanov construction into the prior pricing
artifacts — making `GaussianGirsanov` load-bearing rather than a dead leaf:

- `discounted_terminal_eq_S0_of_physical` — the constructed `Q` is a *genuine
  equivalent martingale measure*: `E_Q[e^{−rT}·S_T] = S₀` (the discounted
  asset is a `Q`-martingale). This is the defining property of an EMM, so the
  Esscher construction yields a real risk-neutral measure, not merely one
  under which the driver is standard normal.
- `bs_call_formula_of_physical` — the full chain `physical → Girsanov → Q → BS
  closed form`.

These are **additive bridges**: the pricing files keep `BSCallHyp` as their
clean abstraction, and Girsanov sits above them (the same pattern as
`PricingFromBrownian` / `BSCallHypFromBrownian`). The pricing files are *not*
refactored to depend on Girsanov — that would invert the dependency graph.
The spine is `physical measure → Girsanov → Q → BSCallHyp → pricing`.

## Leap 3 — multivariate: Margrabe's exchange option

`MathFin/BlackScholes/ExchangeOption.lean`.

The first genuinely multivariate result. The exchange option pays
`max(S¹_T − S²_T, 0)`; its structural fact (Margrabe 1978) is that it depends
only on the ratio `S¹/S²`, lognormal at **effective volatility**
`σ² = σ₁² + σ₂² − 2ρσ₁σ₂`, so the two-asset problem collapses to a one-asset
Black-Scholes problem. It reuses the 1-D machinery rather than re-deriving —
the same structural-reduction discipline as `PowerCall`.

| Theorem | Content |
|---|---|
| `margrabe_variance_sub` | `Var[L₁ − L₂] = Var L₁ + Var L₂ − 2·cov(L₁,L₂)` via covariance bilinearity. First consumer of the covariance machinery shared with `Foundations/BivariateGaussian` — makes it load-bearing. |
| `margrabe_effective_variance` | Substituting `σ₁²T, σ₂²T, ρσ₁σ₂T` gives the effective variance `(σ₁²+σ₂²−2ρσ₁σ₂)·T`. |
| `exchange_payoff_eq_ratio` | `max(a−b,0) = b·max(a/b−1,0)` — the exchange payoff is `S²_T` times a vanilla call on the ratio. |
| `margrabe_eq_bsVGarman` | Margrabe **is** a `GarmanNormalForm` instance at `A=S¹₀, K=S²₀, DF=1`, effective vol `σ`. A multivariate option is the same formula `V = A·Φ(d₁) − K·DF·Φ(d₂)` as every BS-family price. |
| `margrabe_parity` | Exchange-option parity: `Margrabe(S¹,S²) − Margrabe(S²,S¹) = S¹ − S²` (the analog of put-call parity), via `Φ(x)+Φ(−x)=1`. |
| **`margrabe_price_via_call`** | **Price-level reduction.** In the `S²`-numeraire, the exchange option is `bs_call_formula` on the ratio: `S²₀·E_Q[max(R_T − 1, 0)] = margrabePrice`. |

The price-level result takes `BSCallHyp` for the *ratio* `R = S¹/S²` — exactly
the abstraction `bs_call_formula` takes for any underlying.

**Leap 3 grounding (done)** — `MathFin/BlackScholes/MargrabeGrounding.lean`.
That `BSCallHyp` for the ratio is now *derived*, the Margrabe-analog of leap 1:

| Theorem | Content |
|---|---|
| `normalizedSpread_hasLaw_std` | **Bivariate → univariate reduction.** For a jointly-gaussian pair `(W₁,W₂)` of standard drivers with correlation `ρ`, the normalized log-spread driver `(σ₁W₁ − σ₂W₂)/σ_eff` is `N(0,1)`: gaussianity is preserved under the linear map (`HasGaussianLaw.map_of_measurable`), and the variance is pinned to `1` by covariance bilinearity (`margrabe_effective_variance`) — making `Foundations/BivariateGaussian`'s machinery load-bearing. |
| **`margrabe_bsCallHyp_of_gaussian`** | **The capstone.** From the joint gaussian model there exists a probability measure `Q` (the explicit Esscher tilt — the `S²`-numeraire change) and a standard-normal driver under which `BSCallHyp` holds for the ratio at the effective vol. The two-asset grounding *reduces to* the one-asset Girsanov (`BSCallHyp.exists_of_physical`, leap 1) applied to the single effective driver — the gaussian-vector reduction is the only new ingredient. |

Composing `margrabe_bsCallHyp_of_gaussian` with `margrabe_price_via_call`
prices the exchange option with **no** assumed risk-neutral hypothesis.

## The honest abstraction boundary

Across leaps 1 and 3 there is one consistent, deliberately-drawn line: a
pricing hypothesis (`BSCallHyp`, or `BSCallHyp` for the ratio) may be taken as
a primitive at the level the whole library operates, and the *deepest*
grounding of that primitive from a Brownian motion / a joint model is a
distinct, harder result. Leap 1 is that grounding for the 1-D `BSCallHyp`;
the leap-3 grounding (`MargrabeGrounding.lean`) is the corresponding one for
the ratio's `BSCallHyp` — both are now *derived*, not assumed. The discipline
holds: no hypothesis-form theorem is committed unless its hypotheses are
discharged in the same arc or are the standard library-level pricing
primitive.

## Leap 4 — the adapted Itô isometry (done, discrete)

`MathFin/Foundations/ItoIsometryAdapted.lean`.

The Wiener integral (`Foundations/WienerIntegralL2.lean`) handles
*deterministic* integrands, where cross-terms vanish by the BM covariance.
That is **not** the Itô integral. Leap 4 builds the genuinely-stochastic
core: a **random, adapted** integrand `φ`, where the cross-terms vanish for a
deeper reason — the next increment `B_{t₁} − B_{t₀}` is *independent of the
past* `𝓕_{t₀}` (the weak Markov property `IsPreBrownian.indepFun_shift`) and
has mean zero.

The increment-independence this was long thought to wait on is **not** WIP:
it is `IsPreBrownian.hasIndepIncrements` and `IsPreBrownian.indepFun_shift`,
fully proven in Degenne's package. The deductive chain:

| Theorem | Content |
|---|---|
| `adapted_indepFun_increment` | An integrand adapted to `𝓕_{t₀}` is independent of the forward increment `B_{t₁} − B_{t₀}` (via `indepFun_shift`). |
| `integral_adapted_mul_increment` | **Martingale-difference property.** `E[φ·(B_{t₁}−B_{t₀})] = 0` for adapted `φ` — the reason the Itô integral is a martingale, and it holds for *random* `φ`. |
| `integral_adapted_sq_mul_increment_sq` | **Isometry kernel.** `E[φ²·(B_{t₁}−B_{t₀})²] = E[φ²]·(t₁−t₀)`. |
| `adaptedAt_eval`/`.mono`/`.mul`/`.sub` | The adaptedness algebra (the natural Brownian filtration `𝓕_{t₀}` as a closure), used to certify the cross-term factors are `𝓕_{tₖ}`-measurable. |
| **`ito_isometry_discrete`** | **The discrete Itô isometry.** `E[(Σₖ φₖ·ΔBₖ)²] = Σₖ E[φₖ²]·(t_{k+1}−t_k)` for adapted `L²` integrands. Diagonal = variance kernel; off-diagonal = 0 by the martingale-difference property. |
| **`ito_isometry_brownian_self`** | **The `∫₀ᵀ B dB` Riemann-sum isometry**, `E[(Σₖ B(tₖ)·ΔBₖ)²] = Σₖ tₖ·Δtₖ` — a fully-discharged instance (no remaining hypotheses beyond measurability + a monotone partition). |

All build-enforced axioms-clean (`MathFin/AxiomAudit.lean`).

## Leap 4, continuous — the bounded-horizon CLM, now consumed (2026-05-29)

The L²(adapted) Cauchy completion is **built**: `ItoIntegralCLM.itoIntegralCLM_T`
is the continuous Itô integral as a CLM `Lp 2 trim_T →L[ℝ] Lp 2 μ` with the
isometry `‖∫₀ᵀ f dB‖ = ‖f‖` (density via `simpleAssembly_T_denseRange`, the
orthogonal-complement → π-λ argument). Bounded horizon `[0,T]`; the unbounded-`ℝ≥0`
CLM (σ-finite predictable exhaustion) stays gated.

It now has its **first genuine consumer** (`Foundations/ItoIntegralBrownian.lean`,
`itoIntegralCLM_T_brownian`): `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` as a real
`itoIntegralCLM_T` identity, bridging the abstract CLM to the concrete
quadratic-variation limit. The unbounded Gaussian integrand `s ↦ Bₛ` is realised
as the `trim_T`-limit of its clamp-truncated left-endpoint step processes — the
genuine construction of the Itô integral for an unbounded `L²` integrand.

Still open: the *general* Itô formula / path-wise SDE form and the time-indexed
martingale/isometry on `t ↦ (V●B)_t`, which would clear the remaining Itô-gated
`reduced_core`s in [`coverage.md`](coverage.md).

(The Margrabe `BSCallHyp`-grounding, previously gated here, is **done** — see
Leap 3 above, `MargrabeGrounding.lean`.)

## Leap 5 — martingale representation: the hedge is *derived* (2026-08-07)

`MathFin/Foundations/MartingaleRepresentation.lean`,
`MathFin/Foundations/MarketCompleteness.lean`.

Leap 4's continuous half built the Itô integral as an isometry `φ ↦ ∫₀ᵀ φ dB` from
the predictable `L²(dt⊗dμ)` integrands into `L²(μ)`. What that isometry does *not*
say is which claims it reaches. The binomial tower has replication and its uniqueness
because a finite tree can be solved backwards; in continuous time the library could
integrate a strategy it was handed, and had no theorem saying a strategy exists.
Leap 5 identifies the image exactly. `itoIntegralCLM_T` is onto the **centered
`𝓕ᴮ_T`-measurable** part of `L²(μ)`, so the hedge exists, is unique, and is produced
by the theorem rather than posited.

The route is not Malliavin calculus and not Clark–Ocone. Surjectivity of an isometry
onto a closed subspace is a *totality* statement about its range, and the two halves
come from separate modules:

| Theorem | Content |
|---|---|
| `BrownianCylinderGeneration.iSup_cylinderFiltration_eq_natFiltration` | The Brownian filtration is generated by the dyadic cylinder σ-algebras, `⨆ₙ cylinderSigma B T n = natFiltration`. Path continuity enters exactly once, turning `B qₙ → B s` along dyadic `qₙ → s` into measurability against the supremum. Bundled as a genuine `Filtration ℕ`, which is what Lévy's upward convergence theorem consumes. |
| `ItoIntegralLocality.coeFn_smulAdapted` | `𝓕_a`-linearity of the terminal integral: scaling a predictable integrand by an `𝓕_a`-measurable factor supported on `(a, T]` scales the integral. Proved by equalizing two continuous linear maps on the dense range of simple-process assemblies (`DenseRange.equalizer`). |
| `DoleansStepRepresentation.stepDoleans_sub_one_mem_range` | Every step-integrand Doléans exponential, minus one, is **inside** the range. The induction over the partition is where `𝓕_a`-linearity is spent. |
| `WienerExponentialTotality.eq_zero_of_orthogonal_stepDoleans` | The other half: an `L²(𝓕ᴮ_T)` variable orthogonal to all of them is zero. Abel summation reduces to a linear exponential, MGF analytic continuation settles it on each cylinder σ-algebra, and Lévy upward convergence lifts it to `𝓕ᴮ_T`. |
| **`itoIntegralCLM_T_surjective_onto_centered`** | **The capstone.** The Itô integrals together with the constants exhaust `lpMeas ℝ ℝ 𝓕ᴮ_T 2 μ`. A centered `𝓕ᴮ_T`-measurable `F` splits as `y + z` against the range (closed, being an isometry's image, hence orthogonally complemented); `z` inherits measurability and centering from `F`, so `∫ z·D = ∫ z·(D − 1) + ∫ z = 0` for every step Doléans `D`, and totality kills `z`. |
| `exists_itoIntegral_representation` | Terminal form, `∃!`: `F =ᵐ 𝔼[F] + ∫₀ᵀ φ dB`, uniqueness being injectivity of an isometry. |
| `itoIsometryEquiv` | The two bundled: a `LinearIsometryEquiv` from the predictable integrands onto `centeredBrownianL2`. |
| `martingale_representation` | Process form: every square-integrable martingale on the Brownian filtration is `M_t = M_0 + ∫₀ᵗ φ dB` (corpus `gir-thm-9.3.4`, flipped `reduced_core → full`). |

`𝔼[∫₀ᵀ φ dB] = 0` is proved, not assumed, one floor down as
`ItoIntegralProcessGeneral.integral_itoIntegralCLM_T`.

**The finance reading** (`MarketCompleteness.lean`): `exists_replicating_strategy`
says every square-integrable `𝓕ᴮ_T`-claim is the terminal wealth `𝔼_μ[H] + ∫₀ᵀ φ dB`
of a strategy, with a unique hedge, and `superReplication_eq_emm_price` says the least
initial wealth from which some strategy dominates `H` is that same `𝔼_μ[H]`. The
strategy class is the Itô-integrable predictable integrands, wider than
`ContinuousMarket.SimpleStrategy`; the widening is forced, since a general `L²` claim
is not the terminal value of any piecewise-constant holding.

**The abstraction boundary, drawn as deliberately as in leaps 1 and 3.**
`measure_eq_of_pricesGainsAtZero` proves uniqueness of the pricing measure on the
Brownian filtration *for measures that price the traded gains at zero*. That is not
the unconditional second FTAP, and it is worth being exact about why. The textbook
argument needs the replicating wealth to be a stochastic integral against the price
`S`, hence a martingale under every EMM. The wealth process martingale representation
builds is an integral against `B`, and `S` and `B` share only a filtration, so nothing
in `IsEMM S Q` makes `∫₀ᵀ φ dB` a `Q`-fair game. The fair-game step is therefore
hypothesised under its own name, `PricesGainsAtZero`: step (i) of the textbook proof
assumed, step (ii) proved. Two proved facts keep it honest rather than convenient —
`pricesGainsAtZero_self` (`μ` itself satisfies it, so nothing is vacuous) and
`pricesGainsAtZero_of_gains_martingale` (the textbook gains-martingale condition
implies it). The corollary `emm_unique_of_complete` consumes only the `isProb` and
`ac` fields of `IsEMM`. Closing the gap means the stochastic integral `∫ φ dS` against
a general price, whose absence `ContinuousMarket` already records as deliberate.

Only `complete ⟹ unique` is delivered. The converse needs the Jacod–Yor extreme-point
characterisation of the set of martingale measures and is out of scope, additive in
the same sense as the Delbaen–Schachermayer boundary `ContinuousMarket` records.
`superReplication_eq_emm_price` does not close the finite-state Farkas gap in
`Foundations/SuperhedgingDuality`: separation proves the duality there, martingale
representation proves it here, and neither implies the other.

**The gap named in the last paragraph is closed by Leap 6 (2026-08-16).** `∫ φ dS` now exists,
`PricesGainsAtZero` is derivable rather than assumed, and the hedge is held in the price. The
paragraph above stands as written — every statement in it is still true — but the absence it
records is no longer an absence.

## Leap 6 — the chain rule: the hedge is held in the *price* (2026-08-16)

`MathFin/Foundations/ItoIntegralAgainstMartingale.lean`,
`MathFin/Foundations/MarketCompletenessInPrice.lean`,
`MathFin/Foundations/PricingMeasureL2Density.lean`.

Leap 5 identified the image of `φ ↦ ∫₀ᵀ φ dB` exactly, and with it produced a hedge. What it
could not say is that the hedge is a *holding in the traded asset*: the wealth it builds is an
integral against `B`, and a trader holds units of `S`. Six places in the repo recorded the same
missing primitive, `∫ φ dS`. Leap 6 builds it.

The construction is a transport, not a second tower. For a driver `φ`, the Itô integral process
`M = φ●B` has bracket `d⟨M⟩ = φ² ds`, so the integrands square-integrable against `M` are the
weighted space `L²(φ²·trim_T)`; and `ψ ↦ ψφ` is an isometry from it into `L²(trim_T)`. Composing
with `itoIntegralCLM_T` gives `∫· dM` with the right domain and the right isometry for free.

| Theorem | Content |
|---|---|
| `LpMulIsometry.mulLI` | Multiplication by `f` as a `LinearIsometry` `L²(f²·ν) →ₗᵢ L²(ν)`. Mathlib has only `p = 1` (`withDensitySMulLI`), where density and multiplier coincide; at `p = 2` the multiplier is the density's square root, which is what makes the norm come out right. The content is well-definedness: `{f = 0}` is `(f²·ν)`-null but not `ν`-null, so representatives of one class can differ on a `ν`-non-null set — and the map is still well defined, because on `{f = 0}` both products vanish. |
| `PredictableDensityGeneral.simpleAssembly_sqWeight_denseRange` | Simple processes are dense in the weighted `L²`. The flat π-λ induction is not ported: its core only ever uses *integrability*, so the weight moves into the integrand as `h := f²·g`, which is `L¹` and generally not `L²` — which is why the core had to be weakened from an `L²` class to an integrable function. |
| `ItoIntegralAgainstMartingale.itoIntegralAgainst_eq_itoIntegral` | **The chain rule.** `∫ψ dM = ∫ψφ dB`. |
| `ItoIntegralAgainstMartingale.norm_itoIntegralAgainstCLM` | The Itô isometry against `M`: `‖∫ψ dM‖_{L²(μ)} = ‖ψ‖_{L²(⟨M⟩)}`. |
| **`ItoIntegralAgainstMartingale.itoIntegralAgainst_elementary`** | **What earns the name.** On a band `Z·1_{(a,b]}` with `Z` bounded and `𝓕_a`-measurable, the integral is `Z·(M_b − M_a)` — the Riemann–Stieltjes sum. Defining by a formula proves nothing; this is the theorem that says the formula computes the integral one wanted. Both halves came from the locality file: `1_{(a,b]}·φ` is a difference of two `restrictAfterCLM`, and the `𝓕_a`-measurable factor passes through by `itoIntegralCLM_T_smulAdapted`. |
| `MarketCompletenessInPrice.exists_replicating_strategy_in_price` | **Completeness, in the price.** Every square-integrable `𝓕ᴮ_T`-claim is the terminal wealth of a *unique* holding `ψ` in `S = S₀ + (σ●B)`. Only `σ ≠ 0` a.e. is needed, not a uniform lower bound: `‖ψ‖²_{L²(⟨S⟩)} = ∫(φ/σ)²σ² = ‖φ‖²`, so the weighted norm rescales and the holding is admissible however small `σ` gets. |
| **`PricingMeasureL2Density.measure_eq_of_density`** | **The capstone.** If `S` is a `Q`-martingale and `Q = D·μ` with `D ∈ L²(μ)`, then `Q` agrees with `μ` on all of `𝓕ᴮ_T`. Leap 5's `PricesGainsAtZero` is a *conclusion* here, not a hypothesis. |

The pricing-measure argument is four steps, and none of them is stochastic integration under
`Q`. The functional `ψ ↦ 𝔼_Q[∫ψ dS]` is `⟪D, ∫ψ dS⟫` — an inner product against a fixed `L²(μ)`
element composed with an isometry — so continuity is `innerSL`'s and square-integrability of the
density is exactly what buys it. On a band the integral is `Z·(S_b − S_a)`, a bounded predictable
weight against a `Q`-martingale increment, whose mean is zero by a lemma that predates all of
this (`ContinuousMarket.increment_integral_zero`, previously private). A simple process is the
finite sum of its bands. And the simple processes are dense. That is the whole proof.

**The abstraction boundary, again drawn deliberately.** Square-integrability of the density is
not removable by this argument — it is what makes the functional continuous, and without it the
dense-set step has nothing to stand on. The price is **driftless**: `S = S₀ + (σ●B)`, which is
what a discounted price is under the reference measure; a drift `∫b ds` is additive, reuses the
pathwise drift object the Girsanov work already built, and is what the HJM bond dynamics need.
Only `complete ⟹ unique` is delivered; the converse still needs Jacod–Yor. And the agreement
`Q = μ` is **on `𝓕ᴮ_T`** — it says nothing off that σ-algebra. Finally, the band identity is for a
single band: the summed version over a general simple process is not stated as a theorem, only
the `Lp` decomposition it would follow from, and the uniqueness clause takes agreement on simple
processes rather than on written-out Riemann–Stieltjes sums. Degenne's axiomatic
`IsStochasticIntegral` is the right frame for that clause and exists only on `v4.33.0-rc1`, so
instantiating it waits for a stable pin.
