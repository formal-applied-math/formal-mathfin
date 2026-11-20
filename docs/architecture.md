# Architecture

This page owns two things: the order of the layers, and the rules that decide where a module
goes. The mathematics each layer holds is in [`organization.md`](organization.md) and
[`mathematical-architecture.md`](mathematical-architecture.md); the principles for definitions and
statements are in [`design.md`](design.md).

## Layers

`Probability/` → `Contracts/` → `Pricing/` → the limbs `Models/`, `Risk/`, `Choice/`,
`Insurance/`, `Markets/`. Imports point that way. A limb reaches another limb only along an edge
declared in `tools/verify/layers.py` (`layers.EDGES`, each with its reason), and
`tests/test_architecture.py` holds the imports against the direction at zero. Every module lives in
one layer, and every module imports a library module or is imported by one.

This is the single statement of the layer order; other documents link here rather than repeat it.
Probability is load-bearing only when the modules above it consume it, so a join, such as a
constructor `X.of_isPreBrownian` or an equality between two encodings, is built in the module that
uses it. There is no separate bridges directory.

## Principles

1. **Name the structural fact, do not repeat the algebra.** When one mathematical principle
   generates many theorems, it gets its own module and the consumers delegate; downstream proofs
   then collapse to one or two lines.
2. **Be honest about proof depth.** Algebraic closed-form bookkeeping is necessary but not deep. The
   corpus records the difference as a formalization status, below.
3. **A principle must be load-bearing.** A master file whose identity no consumer uses is a
   docstring pretending to be a module.

## Proof depth and the corpus statuses

Each corpus entry declares `full`, `library_wrapper` or `reduced_core` (see the
[glossary](glossary.md#status)); delivery claims count only the first two, and
[`coverage.md`](coverage.md) audits them. Proof shape differs along the same line.

* **Foundational proofs** (`full`): multi-page derivations in probability, integration and calculus,
  such as the Wiener integral, Brownian martingales, Doob `L^p` convergence, Itô drift, Girsanov,
  the FTAP variants, the binomial and Black–Scholes closed forms. Axiom-clean, with nothing from
  outside Mathlib and BrownianMotion.
* **Principle modules** (`full`): the structural-principle table below. The master file does the
  work and consumers compose in one or two lines.
* **Closed-form verifications** (`full`, shallow): that a textbook formula has its claimed algebraic
  property, for example `risk_parity_equal_contribution`, `gaussianVaR_translation`, the scale
  invariance of the Sharpe ratio. The proof is `unfold; field_simp; ring` or close to it, and the
  content is in the definition. These are necessary, since otherwise a formula is a string, but
  they should not be conflated with the first kind in a claim.
* **Reduced cores** (`reduced_core`): a result that proves less than the theorem it is named after.
  Run `python3 -m tools.verify.coverage_report` for the current list; the Limitations section of
  the [README](../README.md) and each entry's `formalization_scope` say what is missing.

## The structural-principle modules


Every path in this table exists under `MathFin/`.

| Principle module | The fact | Where it's load-bearing |
|---|---|---|
| `Models/BlackScholes/GarmanNormalForm.lean` | Every BS-family closed form is `V = A · Φ(d_1) − K · DF · Φ(d_2)`, parameterised by `(A, K, DF, σ, T)`. | `bsV` (standard BS), Black-76 RHS, BS-Merton dividends RHS, KMV-Merton distance-to-default, and **Margrabe's exchange option** (`ExchangeOption.margrabe_eq_bsVGarman`, at `A = S¹₀, K = S²₀, DF = 1`, effective vol `√(σ₁²+σ₂²−2ρσ₁σ₂)`) are **provably the same formula** at different `(A, DF, σ)`. Even a *multivariate* option is one instance — six-plus apparent pricing variants are one. |
| `Models/BlackScholes/StrikeConvexity.lean` | K-convexity at **four scales**: payoff (`K ↦ max(S − K, 0)` convex), price under any law with a finite mean (`K ↦ ∫ (X − K)⁺ dμ` convex, `convexOn_integral_call`, and strictly convex where the law charges every interval of strikes), finite-state price (`K ↦ Σ q_i · max(S_i − K, 0)` convex via `ConvexPricingFunctional`), continuous BS price (`K ↦ bsV K r σ S τ` convex on `(0, ∞)`, the standard normal case of `convexOn_integral_call`). | `Spreads.lean` (bull-spread = antitone face; butterfly = convex face at payoff *and* price); `BreedenLitzenberger.lean` (PDF positivity = infinitesimal convex face). |
| `Models/ModelFree/PriceBounds.lean` | `0 ≤ bsV`, `0 ≤ bsP`, `Φ ≤ 1`, and put-call parity (the "no-arbitrage rectangle"). | `bsV ≤ S`, `bsP ≤ K · e^{−rT}`, forward lower bound, intrinsic-style put bound, box-spread identity, Merton 1973 strict dominance — all one-line corollaries. Subsumes the former `StaticBounds.lean` and `AmericanCallNoDividend.lean`. |
| `Models/BlackScholes/GreekSigns.lean` | Sign constraints on each BS Greek (δ ∈ [0, 1], γ > 0, ρ ≥ 0, ∂_K V ≤ 0, ∂²_K V ≥ 0). | Names the qualitative content (call is increasing+convex in spot, increasing in vol/rate, decreasing+convex in strike) — sign facts were derivable from `PDE` / `StrikeGreeks` / `HigherGreeks` but never named. |
| `Pricing/ConvexPricingFunctional.lean` | Non-negative linear pricing functional preserves `ConvexOn`. | Call price convex in strike (finite-state), butterfly non-negativity at the *price* level (not just payoff), consumed by `PricingKernel`'s FTAP butterfly; its general-law form `convexOn_integral_call` (`StrikeConvexity`) is what Breeden–Litzenberger PDF positivity uses. |
| `Probability/Gaussian/StandardGaussianMGF.lean` | `∫ exp(α + β · z) ∂N(0, 1) = exp(α + β²/2)` (affine-shifted gaussian MGF). | `PowerOption.lean` (`nthMoment_terminal` is a direct instance); `LognormalMoments.lean` (`secondMoment_terminal = nthMoment_terminal 2`). |
| `Probability/Analysis/ExponentialDiscount.lean` | `−d/dt log(exp(−H(t))) = H'(t)` (rate as negative log-derivative). | Conceptual core of `ForwardRate.lean` (forward = −∂_T log P), `Mortality.lean` (force = −∂_t log S), `HazardCurve.lean` (hazard = −∂_t log S). |
| `Models/Binomial/MertonAmericanCallTree.lean` | Merton 1973 in the binomial tree, **at any horizon `n`**: `americanPrice = binomialPrice` for the non-dividend call. The one-period continuation dominates the discounted intrinsic (Jensen for `max(·, 0)` + martingale identity + discount shift); the multi-step `intrinsic ≤ binomialPrice` and `americanPrice ≤ binomialPrice` then follow by induction on `n` + monotonicity of the one-period operator. | Combined with `binomialPrice ≤ americanPrice` (`bermudanPrice_mono`, `Models.Binomial.Bermudan`, trivial direction), gives the equality at every step. |
| `Models/Binomial/ReplicatingUniqueness.lean` | Single-period replicating portfolio `(Δ, B)` is uniquely determined by target payoffs. | Discrete-time market-completeness statement. Combined with First+Second FTAP, completes the FTAP equivalence chain. |
| `Models/Binomial/PathReflection.lean` | **André's reflection principle** (1887, full): for paths `ω : Fin n → Bool` viewed as `±1` walks, (a) algebraic identity `walkPos (reflectAfter τ ω) k = 2 · walkPos ω τ − walkPos ω k` for `τ ≤ k`; (b) reflection-at-first-hitting-time `reflectAtFirstHit a` is an involution on `{ω : HitsLevel a ω}`; (c) the **bijection** `reflectionPrincipleEquiv a b : {ω : hits a, ends at b} ≃ {ω : hits a, ends at 2a − b}` as a Mathlib `Equiv`; (d) the **discrete IVT** `walkPos ω n ≥ a > 0 ⟹ HitsLevel a ω`; (e) the **simplified barrier bijection** `reflectionPrincipleEquivBelow`. | Counting backbone of barrier-option pricing in the binomial tree. The IVT drops the `HitsLevel` condition on one side of the bijection, giving the form actually used: "paths that touch the barrier and end below" ≃ "paths that end above (reflected position)." |
| `Models/Binomial/SnellEnvelope.lean` | **Snell envelope characterisation** of `bermudanPrice E` (`E = univ` is `americanPrice`): it is the *smallest* `V : ℕ → ℝ → ℝ` simultaneously dominating the payoff at maturity and the exercise dates (`V ≥ g`) and supermartingale w.r.t. the one-step discounted Q-expectation. | Optimal-stopping characterisation of the American price without defining stopping rules on the path space. Combines `le_bermudanPrice` + `bermudanPrice_supermartingale` (existence) with `bermudanPrice_le_of_supermartingale_dominating` (universality); monotonicity in the exercise set (`Bermudan`) and Merton below are instances of the minimality. |
| `Pricing/NoArbitrageDerivations.lean` | **Put-call parity and the forward price as consequences of no-arbitrage**, stated abstractly for any non-negative linear pricing functional `Λ(g) = ∑ q_i · g_i` with bond constraint `Λ(1) = DF` and stock constraint `Λ(S_T) = S_0`. Proves `C(K) − P(K) = S_0 − K · DF` and `F = S_0 / DF` (fair forward strike). | First-principles derivations of two canonical static no-arb identities — independent of any closed form (BS, Bachelier, binomial). |
| `Models/BlackScholes/RiskNeutralProbabilities.lean` | **Probabilistic interpretation of `bsd2`**: under the risk-neutral hypothesis, `Q(S_T > K) = Φ(bsd2 S_0 K r σ T)` — the right factor of the BS formula has *content* (exercise probability), not just algebraic form. | Closes the structural narrative on the BS formula: `Φ(d_2)` is the risk-neutral probability of finishing in the money. The companion `Φ(d_1) = Q^{(S)}(S_T > K)` (stock numeraire) is in `StockNumeraire.lean`. |
| `Choice/Performance/Ratios.lean` (extended) | **Sharpe-ratio full affine invariance**: `Sh(c · μ + d, c · r_f + d, c · σ) = Sh(μ, r_f, σ)` for any `c ≠ 0`. Algebraic master `diff_div_affine_invariant` (and signed variant) factor the proofs into one-line corollaries. | The standard "ratio scale invariance" master generalised to full affine invariance — the canonical algebraic content of why Sharpe is a *ratio* and why it cares only about excess return / risk shape, not absolute units. |
| `Models/Rates/DurationSensitivity.lean` | **Modified duration as the negative log-derivative of bond price**: `P'(y) = −ModNum(y)`, hence `P'(y) / P(y) = −D_mod(y)`. Derived from per-cashflow `HasDerivAt` of `c / (1+y)^n` with the `n = 0` and `n ≥ 1` cases bundled by `field_simp + ring`. | First-principles derivation of the operational content of duration: it measures the *percentage* sensitivity of bond price to yield. |
| `Models/Rates/ConvexitySensitivity.lean` | **Bond convexity as the second derivative of price**: `P''(y) = ConvNum(y)`. Completes the discrete yield-Taylor expansion `ΔP / P ≈ −D_mod · Δy + ½ C · (Δy)²`. | Bond convexity is *literally* the second derivative of price w.r.t. yield, not a separately-defined moment — obtained by applying `hasDerivAt_coupon_term` from `DurationSensitivity` a second time. |
| `Choice/Portfolio/SharpeFOCDerivation.lean` | **Markowitz cross-product FOC derived from Sharpe-ratio maximisation**: defines `Sh²(w) = E(w)² / V(w)`, computes `HasDerivAt` with the textbook formula `Sh²' = (2EE'V − E²V') / V²`, and shows the numerator factors as `2E · (r₁(Σw)₂ − r₂(Σw)₁)`. With `E ≠ 0, V > 0`, critical points of `Sh²` are exactly the cross-product FOC. | Closes the loop with the pre-existing `tangentTwo_satisfies_FOC`: the FOC arises as the critical-point condition of a real maximisation problem, not as a stated identity. |
| `Choice/Portfolio/MarkowitzLagrangian.lean` | **N-asset Markowitz constrained-variance critical points from the Lagrangian** (forward direction): defines `IsConstrainedVarianceCriticalPoint` variationally, proves that any portfolio satisfying the Lagrangian FOC `Σw = λ_1 · 1 + λ_2 · μ` componentwise is a critical point of `(1/2) w^T Σ w` subject to budget + target-return constraints. The `λ_1 = 0` corollary recovers `IsTangentPortfolioN`. | Extends 2-asset `SharpeFOCDerivation` to the N-asset textbook Markowitz formulation. Backward direction (critical point ⟹ FOC) requires `Submodule.orthogonalComplement` machinery and is deferred. |
| `Choice/Portfolio/CAPMEquilibrium.lean` | **CAPM from market equilibrium**: under the equilibrium hypothesis that the market portfolio satisfies the tangent-portfolio cross-product FOC `μ_excess(k) · (Σw_M)_j = μ_excess(j) · (Σw_M)_k`, every asset's excess return equals its beta times the market excess return: `μ_excess(i) = β_i · μ_M`. | The discrete-Lagrangian derivation: multiply the FOC by `w_M(j)` and sum to fold `(Σw_M)` into `Var(R_M)` and `μ_excess` into `μ_M`. Derives the SML from optimal portfolio choice + market clearing. |
| `Choice/Portfolio/RiskParityFOC.lean` | **Risk parity from log-barrier Lagrangian FOC**: defines `riskContribution_i := w_i · (Σw)_i`, shows `∑ RC_i = portfolioVarN`, and proves the canonical risk-budget portfolio satisfies `RC_i = b_i` from the FOC `(Σw)_i = b_i / w_i` (the log-barrier-regularised variance minimisation). | Risk parity stated as the *output of an optimisation* (log-barrier-regularised variance minimisation), matching the Roncalli-Maillard treatment used in production. |
| `Choice/Portfolio/BlackLittermanND.lean` | **N-dim Black-Litterman posterior as normal-equation solution**: defines `blPosteriorPrecision := Σ_inv + Pᵀ · Ω_inv · P` (additive precision update), the precision-weighted RHS `Σ_inv · π + Pᵀ · Ω_inv · Q`, and proves the explicit form `posterior_precision⁻¹ · RHS` satisfies the BL normal equation. | Extends the 1-D closed form to the N-asset / m-view matrix formulation, characterising the posterior as the unique linear-system solution rather than a memorised inverse formula. |
| `Models/BlackScholes/StockNumeraire.lean` | **Delta as stock-numeraire exercise probability**: `Φ(d_1) = Q^(S)(S_T > K)`, where `Q^(S) = Q.withDensity (e^{−rT} · S_T / S_0)` is the stock-numeraire measure. | Closes the structural narrative: both `Φ` factors in the BS formula are exercise probabilities — `Φ(d_2)` under the money-market numeraire, `Φ(d_1)` under the stock numeraire. Their difference `Φ(d_1) − Φ(d_2)` is the "value of optionality." |
| `Models/BlackScholes/PowerCall.lean` | **Powered call closed form via structural reduction to BS-call**: `(S_T)^a` is itself a BS terminal with *effective spot* `S_0^a · exp((a − 1) r T + a(a − 1) / 2 · σ² T)` and *effective volatility* `aσ`. | Power options reuse `bs_call_formula` whole — no new gaussian integral. The only new content is the algebraic identification of `(S_T)^a` as a standard BS terminal. |
| `Models/BlackScholes/ChooserComposition.lean` | **Chooser option as call + put portfolio via PCP at chooser date**: closed-form `chooserPrice := bsV(K, T) + bsP(K · e^{−r(T − t_1)}, t_1)`, and linearity-of-expectation `chooser_integral_decomp`. | The "chooser = call + put with adjusted strike" identity is *not* just an algebraic decomposition — it's the BS pricing identification produced by combining `chooser_via_pcp` (algebra) with `integral_add` (linearity of expectation). |
| `Models/Credit/KMVMertonStructural.lean` | **KMV-Merton `kmvPD` as actual risk-neutral default probability**: combines `riskNeutralProb_S_T_gt_K` with the algebraic survival identity `1 − kmvPD = Φ(bsd2)` to show `kmvPD = 1 − Q({V_T > F}).toReal`. Merton equity is `bs_call_formula` read at `(V_0, F, σ_V)`. | Connects the algebraic kmvPD definition to the actual `Q(V_T ≤ F)` probability via the same BS structure. |
| `Models/Credit/CDSTimeVarying.lean` | **CDS fair-spread cash-flow balance for time-varying hazard**: `c · annuity(T) = (1 − R) · losses(T)` via integral identities. Plus the discrete multi-period survival factorisation `∏ exp(−h_i Δt_i) = exp(−∑ h_i Δt_i)`. | Generalises constant-hazard `c = h(1 − R)` to the cash-flow-balance form that holds for any deterministic hazard curve. |
| `Risk/UtilityDerivation.lean` | **Acceptance under expected utility, and why it is not coherent**: acceptance under a utility is unchanged by affine changes of the utility and closed under mixing lotteries; under log utility it is the Kelly-growth condition (`acceptableUnderUtility_log_iff_kellyGrowth`) and it is **not** a cone (`not_exists_isCoherentRiskMeasure_log_acceptance`), so no coherent risk measure has it as acceptance set. | Separates convex from coherent risk at the utility primitive. |
| `Models/BlackScholes/BSCallHypFromBrownian.lean` | **`BSCallHyp` / `BachelierHyp` derivable from a pre-Brownian motion**: core scaling lemma `scaled_isPreBrownian_eval_law` shows `W T.toNNReal / √T ∼ N(0, 1)` under `IsPreBrownianReal W Q`. Constructors `BSCallHyp.of_isPreBrownian` and `BachelierHyp.of_isPreBrownian` then discharge the BS / Bachelier hypotheses additively. | First architectural bridge between the Brownian machinery of `Probability/` and pricing-module consumption. Existing pricing modules continue to work unchanged; downstream consumers gain an optional BM-based constructor. |
| `Models/BlackScholes/PricingFromBrownian.lean` | **Full BS / Bachelier / Digital / Power / Dividends / StockNumeraire / KMV pricing pipeline derivable from a pre-Brownian motion**: 11 one-line composite corollaries showing that every pricing entry-point that consumes `BSCallHyp` or `BachelierHyp` can be driven from a single primitive (`IsPreBrownianReal W Q`). | Demonstrates that the entire BS-family pricing infrastructure is *structurally* a corollary of "you have a Brownian motion." |
| `Models/ModelFree/VarianceSwapFromQV.lean` + `VarianceSwapEquipartition.lean` + `VarianceSwapLimit.lean` | **Variance-swap fair strike as a QV limit**: under refinement, `E[Σ (X-increments)²]` converges to `σ² · T`. Chain of (a) per-increment QV identity, (b) finite-`n` equipartition closed form, (c) limit as `n → ∞`. | First downstream use of `Probability/Brownian/BrownianQuadraticVariation.lean`. The companion log-payoff form and this QV form are two functionals of the same BS price process, both yielding `σ²` (after `1/T` rescaling). |
| `Pricing/PricingKernel.lean` | **Pricing kernel from two-state FTAP backward direction**: discounted EMM weights as state prices, the standard pricing kernel `V_0(X) = e^{−rT}(q_up · X_up + q_down · X_down)`. | The stochastic-discount-factor framework instantiated in the simplest finite-state market — every claim's no-arb price is a single linear functional, derived from no-arbitrage rather than assumed. |

## Joins

Probability such as the Brownian construction, the Wiener integral, Doob `L^p` and quadratic
variation is useful to the pricing modules only when they consume it. A join is additive: the
consuming module introduces a constructor `XHyp.of_isPreBrownian` that discharges an existing
hypothesis (`BSCallHyp`, `BachelierHyp`, `BrownianMartingaleHyp`) from a single Brownian-motion
primitive, and existing modules continue to work unchanged. The joins between limbs and the
design reasons are in [`organization.md`](organization.md) and [`design.md`](design.md) §4. The
historical audit that first listed them is [`bridges.md`](bridges.md).

## Naming and organisation

- Files are organised by layer and topic under `MathFin/<Layer>/…/`. One
  theorem per file when the theorem is non-trivial; helper lemmas in the
  same file as `private`.
- Below the layer, directory names are user-facing: `Models/BlackScholes/`,
  `Models/Binomial/`, `Choice/Portfolio/`, `Risk/Credit/`, etc. Match the textbook
  chapter you'd reach for if you were looking up the result.
- File names are the *result* name, not the technique: `RiskParityFOC.lean`
  not `LogBarrierFOC.lean`. The technique appears in the docstring.
- Inside files, follow Mathlib convention: lemma names in `lower_snake_case`,
  definitions in `camelCase`, types in `PascalCase`. Greek letters work
  but use Roman replacements where the Greek is reserved (e.g. `Sg_inv`
  for `Σ_inv` since capital sigma is a Lean reserved token).

## What the library does not prove

The corpus marks each result it states but does not prove in full as `reduced_core`.
`python3 -m tools.verify.coverage_report` gives the current list, and [`coverage.md`](coverage.md)
records each one's scope. They fall in four groups.

- **Brownian path properties.** The reflection principle, nowhere differentiability and the law of
  the iterated logarithm are recorded as fields of a structure, not derived. (BrownianMotion's own
  law of the iterated logarithm is still a `sorry` at our pin.) The reflection identity for ±1
  walks, the algebraic core of the discrete reflection principle, is proved in
  `Models/Binomial/PathReflection.lean`.
- **Stochastic calculus beyond the proved cases.** Itô's formula is proved for `C²` functions of
  Brownian motion (`f`, `f_t`, `f_x`, `f_xx` jointly continuous, with `HasDerivAt` witnesses) with
  no growth condition, in local-martingale form, and for Itô processes with bounded adapted coefficients;
  Girsanov's theorem for bounded predictable `θ`. Still reduced: the two-dimensional Itô formula,
  Girsanov for general progressive `θ` under Novikov, and Novikov's condition itself. Lévy's
  characterization of Brownian motion is proved, with the bracket as the hypothesis that
  `M² − t` is a local martingale.
- **Markov chains.** The strong Markov property, the recurrence criterion, uniqueness of the
  stationary distribution, the ergodic theorem and convergence to equilibrium.
- **Single results elsewhere.** The first arrival of a Poisson process is exponential; the
  Heynen–Kat two-asset barrier at zero correlation and Stulz's call on the maximum at zero strike;
  the decay of the first three Hermite modes under the Vasicek law.

None of these counts toward the delivery total (`full` + `library_wrapper`).
