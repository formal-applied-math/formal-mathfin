# formal-mathfin

[![build](https://github.com/formal-applied-math/formal-mathfin/actions/workflows/build.yml/badge.svg)](https://github.com/formal-applied-math/formal-mathfin/actions/workflows/build.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2606.01356-b31b1b.svg)](https://arxiv.org/abs/2606.01356)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20477781.svg)](https://doi.org/10.5281/zenodo.20477781)
[![dataset](https://img.shields.io/badge/Hugging%20Face-dataset-ffcc4d.svg)](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems)

A library of mathematical finance in [Lean 4](https://lean-lang.org), built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and
[BrownianMotion](https://github.com/RemyDegenne/brownian-motion). It covers stochastic calculus
(the Itô integral, Itô's formula, Girsanov's theorem, martingale representation, stochastic
differential equations), no-arbitrage theory, derivative pricing, fixed income, portfolio theory,
risk measures and actuarial mathematics.

The library is meant to be read, used and extended: to learn the mathematics from statements a
machine has checked, to build on them in other Lean projects, and to see what is proved, what is
stated and open, and where a new result would fit. It is written for mathematicians and for AI
agents alike.

The [corpus](docs/glossary.md#corpus) records 908 results from the literature in
[`benchmarks/`](benchmarks), each with a Lean statement and proof. Of these, 868 are proved in
full, 18 restate a lemma from Mathlib or BrownianMotion, and 22 are
[reduced cores](docs/glossary.md#status) that prove less than the result they are named after.
Each entry records its status and what it leaves out. The library contains no `sorry`, and a
build-time audit checks that every library theorem the benchmark's proofs cite depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

Here, for example, is the convergence of the Cox–Ross–Rubinstein call price to the Black–Scholes
price, from [`CRRClosedForm.lean`](MathFin/Models/Binomial/CRRClosedForm.lean):

```lean
theorem binomialPrice_call_tendsto_bs_closed {r σ T S₀ K : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (hS₀ : 0 < S₀) (hK : 0 < K)
    (hna : ∀ n, 0 < n → BinomialNoArb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)) :
    Tendsto (fun n : ℕ ↦ binomialPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        (fun x ↦ max (x - K) 0) n S₀) atTop
      (𝓝 (S₀ * Phi (bsd1 S₀ K r σ T)
          - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T)))
```

The hypothesis `hna`, that the $`n`$-step tree is free of arbitrage for every $`n \ge 1`$, holds
whenever $`|r|\sqrt{T} < \sigma`$ ([`binomialNoArb_crr`](MathFin/Models/Binomial/CRRConvergence.lean)).

## Where to start

- **To learn.** The [landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html)
  prints the headline theorems exactly as Lean states them, with nothing to install; the
  [documentation site](https://formal-applied-math.github.io/formal-mathfin/) has a page for every
  area and module and a search over every declaration. The
  [beginners' manual](docs/beginners-manual.md) teaches Lean through the library, with checked
  exercises, and [`MathFinExamples/Applications/`](MathFinExamples/Applications) applies it to
  concrete problems, from a capped call to a chain-ladder reserve. The
  [glossary](docs/glossary.md) explains the library's own vocabulary.
- **To use it.** [Using the library in a project](#using-the-library-in-a-project) below gives the
  dependency lines. Cite an entry as the named theorem only when its status is `full` or
  `library_wrapper`, and read its `description` for what it proves.
- **To contribute.** [`CONTRIBUTING.md`](CONTRIBUTING.md) gives the rules and
  [`docs/onboarding.md`](docs/onboarding.md) walks through a first pull request.
- **To do research.** The [blueprint](docs/blueprint.md) maps what is proved and the
  [frontier](docs/glossary.md#frontier) of results stated next;
  [`docs/research-problems/`](docs/research-problems/README.md) catalogues open problems of the
  field with precise statements; [`docs/organization.md`](docs/organization.md) explains how the
  pieces fit.
- **For AI agents.** [`AGENTS.md`](AGENTS.md) covers using and developing the library, and the
  site publishes [`llms.txt`](https://formal-applied-math.github.io/formal-mathfin/llms.txt) and a
  JSON search index. The corpus is also a
  [Hugging Face dataset](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems).

## Main results

Each result below links to its Lean declaration. The
[landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html) prints the
exact statement of each one, and what it leaves out.

- **Itô's formula.** For f(t,x) with continuous partial derivatives and no growth condition,
  f(t,B_t) minus its drift integral agrees, at each time almost surely, with a continuous local
  martingale ([`ito_formula_unrestricted`](MathFin/Probability/Brownian/Ito/ItoFormulaUnrestrictedLocMart.lean)).
  For an Itô process with continuous adapted coefficients, the change-of-variables formula holds
  almost surely at every t ≤ T at once
  ([`ito_formula_adapted_unbounded_process`](MathFin/Probability/Brownian/Ito/ItoFormulaAdaptedProcess.lean)).
- **Lévy's characterization.** A continuous adapted M with M₀ = 0 such that M and M² − t are local
  martingales is a Brownian motion for the filtration
  ([`isFilteredPreBrownian_of_localMartingale`](MathFin/Probability/Brownian/LevyCharacterization.lean)).
- **Girsanov's theorem.** For bounded predictable θ, under dQ = exp(−∫₀ᵀ θ dB − ½∫₀ᵀ θ² dt) dP, a
  modification of B + ∫ θ dt has independent N(0, t − s) increments for the Brownian filtration, and
  continuous paths when B has them
  ([`Btheta_isFilteredPreBrownian_predictable_of_bdd`](MathFin/Probability/Brownian/Girsanov/GirsanovFiltered.lean)).
- **Martingale representation.** For a Brownian motion with every path continuous, every
  square-integrable F^B_T-measurable H is E[H] + ∫₀ᵀ φ dB for a unique φ, so it is replicated from
  E[H] by a unique strategy
  ([`exists_replicating_strategy`](MathFin/Pricing/MarketCompleteness.lean)).
- **Stochastic differential equations.** For Lipschitz coefficients and any horizon, the Picard map
  of dX = b(X) dt + σ(X) dB has a unique fixed point in the predictable L² space
  ([`picardMap_exists_unique_fixedPoint_any_horizon`](MathFin/Probability/Brownian/SDE/SDEExistence.lean)).
- **Fundamental theorem of asset pricing.** On a finite probability space of full support with one
  risky asset, no arbitrage holds if and only if there is an equivalent martingale measure, and,
  with full information at the horizon, the market is complete if and only if that measure is unique
  ([`ftap_discrete`](MathFin/Pricing/FTAP/FTAPDiscrete.lean),
  [`ftap_two`](MathFin/Pricing/FTAP/FTAPComplete.lean)). On any probability space, multi-period no
  arbitrage is equivalent to no arbitrage in each conditional one-period market
  ([`noArbitrage_iff_noArbitrageLocal`](MathFin/Pricing/FTAP/NoArbitrageLocal.lean)), and for one
  real asset no arbitrage is equivalent to an equivalent martingale measure
  ([`OneAsset.noArbitrage_iff_exists_isEMM`](MathFin/Pricing/FTAP/OneAssetDMW.lean)).
- **Coherent risk measures.** On a finite state space, a coherent risk measure is the supremum of
  expected losses over the probability vectors that price every acceptable loss nonpositively
  ([`coherentRisk_isLUB`](MathFin/Risk/AcceptanceSet.lean)).
- **The Black–Scholes PDE from Feynman–Kac.** The call price is a heat-kernel integral of the
  payoff, and the PDE follows from the heat equation for the kernel
  ([`bsV_satisfies_bs_pde_via_feynmanKac`](MathFin/Models/BlackScholes/PDEFromFeynmanKac.lean)).
- **The delta hedge.** Almost surely, for all t ≤ T′ < T at once, e^(−rt) C(t, S_t) = C(0, S₀) + ∫₀ᵗ
  Φ(d₁) σ e^(−rs) S_s dB_s, and C(0, S₀) is the value of the call contract
  ([`bs_delta_hedge_replication`](MathFin/Models/BlackScholes/DeltaHedge.lean),
  [`europeanCall_deltaHedge`](MathFin/Models/BlackScholes/BlackScholesHedge.lean)).
- **Jump-diffusions.** For an assumed jump-diffusion, the discounted price is a martingale exactly
  at the compensated drift, and with Gaussian log-jumps at that drift the conditional call price is
  Merton's series
  ([`JumpDiffusionProcess.martingale_iff`](MathFin/Models/Jumps/JumpDiffusionProcess.lean),
  [`condExp_call_eq_mertonCallPrice`](MathFin/Models/Jumps/JumpDiffusionMerton.lean)).
- **The American put.** For r > 0 and dividend yield 0 ≤ q ≤ r, the early-exercise boundary is
  strictly convex in the time to expiry, and its logarithm is convex
  ([`PhysicalBoundaryConvexity.lean`](MathFin/Models/BlackScholes/American/Stopping/PhysicalBoundaryConvexity.lean)).
- **Raw SVI.** A polynomial-sign formula in the five parameters holds exactly when the parameters
  are admissible and the call priced through the smile is convex in the strike. With one more sign,
  it holds exactly when that call is a normalized call price, free of butterfly arbitrage
  ([`extendedCertificateFormula_iff_bsSmile_convex`](MathFin/Models/ModelFree/SVI/ExtendedFormula.lean),
  [`butterflyFreeFormula_iff_isNormalizedCallPrice`](MathFin/Models/ModelFree/SVI/TailCondition.lean)).
- **Contracts, separate from models.** One contract term is priced in interchangeable models. A call
  less a put is worth the forward in any martingale model
  ([`value_europeanCall_sub_put_of_martingale`](MathFin/Pricing/Parity.lean)), and the call's
  values in the binomial tree converge to its Black–Scholes value when |r|√T < σ
  ([`tendsto_binomial_value_europeanCall`](MathFin/Models/Binomial/BinomialLimit.lean)). Every
  fixed-dated contract on the physical Black–Scholes asset has, under the Girsanov measure, its
  risk-neutral value
  ([`value_physical_eq_riskNeutral`](MathFin/Models/BlackScholes/BlackScholesPhysical.lean)).
- **Interest rates.** In Vasicek and Hull–White, the bond price at t is an exponential-affine
  function of the short rate, and the bond put is a Black put under the forward measure
  ([`bondPrice_hullWhite`](MathFin/Models/Rates/HullWhiteBond.lean),
  [`value_bondPut_hullWhite`](MathFin/Models/Rates/Jamshidian.lean)). Swaptions and the CMS
  swaplet are priced under the annuity measure
  ([`value_payerSwaption`](MathFin/Models/Rates/CMSContract.lean)).

## How the library is organized

Financial mathematics has one economic object, a price system: positions in a market and the set
of pricing measures that price them. Its deep theorems are three dualities of that set: with the
gains of trading strategies (valuation: the fundamental theorems, superhedging), with the
positions a risk measure accepts (risk: the robust representation), and with the positions an
investor prefers (choice: marginal utility is a state-price density). The model families (trees,
diffusions, volatility, jumps, term structures, default, mortality and claims, market
mechanisms) are a second axis; probability and statistics are the tools.

[`docs/organization.md`](docs/organization.md) gives the account. The module directories, the
[blueprint](docs/blueprint.md), the issue labels and the
[documentation site](https://formal-applied-math.github.io/formal-mathfin/) all read the structure
from one file, [`docs/taxonomy.toml`](docs/taxonomy.toml), and the site's
[program tree](https://formal-applied-math.github.io/formal-mathfin/tree.html) draws it.

| | Topics |
|---|---|
| **Probability** | conditional expectation, martingales and stopping times, the Snell envelope, Markov chains; Brownian motion, the Itô integral and isometry, quadratic variation, Itô's formula, Girsanov's theorem, martingale representation, SDEs, Feynman–Kac; Poisson processes and the compensated Poisson integral; the quantile function, GEV and GPD domains of attraction, maxima of Poisson-many losses; copulas and Sklar's theorem (continuous margins), Fréchet–Hoeffding bounds, Hoeffding's covariance identity, Marshall–Olkin common shocks; convex separation |
| **Statistics** | Sharpe, Sortino, Treynor and information ratios; estimators, empirical quantiles, the Roll spread, calibration of an AR(1) to an Ornstein–Uhlenbeck process |
| **Positions and markets** | a contract language that separates payoffs from pricing models; markets, numéraires, self-financing strategies and their gains; the value of a contract under a measure; the fundamental theorems: no arbitrage as the existence of an equivalent martingale measure (finite space, Dalang–Morton–Willinger for one asset, the market form), completeness as its uniqueness |
| **Valuation** | *arbitrage pricing:* change of numéraire, state prices, market completeness, superhedging duality, the American price of an exercise right · *trees:* binomial replication, Cox–Ross–Rubinstein convergence, André's reflection principle · *Black–Scholes and Bachelier:* prices and Greeks, the PDE, dividends; digital, exchange (Margrabe), chooser, barrier, lookback, geometric Asian, power and quanto options, spreads · *American options:* the Snell envelope in the binomial tree, Bermudan exercise, the American put · *volatility models:* Dupire's formula at zero rates, for a market's call prices, the explicit Heston transform and its pricing equation · *the smile:* Roper's characterisation of call-price functions, implied volatility, a polynomial-sign certificate for strike-convexity of raw SVI, Breeden–Litzenberger · *jumps:* Merton's formula and Greeks, Esscher pricing, incompleteness at one date · *interest rates:* bonds, yield curves, forward rates, FRAs, swaps, caps and caplets, swaptions and CMS under the annuity measure, the forward measure, Vasicek, Hull–White and GSR, Jamshidian's bond options, duration, convexity and immunization · *forwards, FX and commodities:* FX (Garman–Kohlhagen), interest-rate parity, Black-76, futures · *credit:* hazard rates, CDS, CVA, first-to-default, KMV–Merton · *life contingencies:* survival models, mortality and annuities · *static replication:* Carr–Madan spanning and its reading as a market's put and call prices, variance swaps, constant-product AMM positions as option portfolios |
| **Choice** | *preferences:* expected utility · *portfolios:* Markowitz, two-fund separation, the tangency portfolio, risk parity, Black–Litterman · *equilibrium:* CAPM · *dynamic:* the Kelly criterion · *microstructure:* Avellaneda–Stoikov market making, the Glosten–Milgrom spread |
| **Risk** | *risk measures:* coherent and spectral risk measures, coherence of expected shortfall and its dual representation, elicitability of value-at-risk by the pinball loss and non-elicitability of expected shortfall, expectiles · *value-at-risk and expected shortfall* for every law, Rockafellar–Uryasev · *aggregation:* failure of VaR subadditivity (the exact range for independent defaults; infinite-mean Pareto), concentration indices · *credit portfolios:* Bernoulli mixtures, the one-factor Gaussian threshold model, the Basel IRB formula as the limit of portfolio VaR · *collective risk theory:* compound Poisson losses |

## Limitations

- **Reduced cores.** Twenty-two of the results prove less than the theorem they are named after.
  - Eleven assume a structure whose fields include the textbook conclusion: the reflection
    principle, nowhere differentiability and the law of the iterated logarithm for Brownian motion,
    Novikov's condition, the general Girsanov theorem, the two-dimensional Itô formula, and five
    theorems on Markov chains.
  - Three rest on a named hypothesis that is not proved. The Dalang–Morton–Willinger theorem for
    several assets assumes a conditional one-period fundamental theorem (for one asset the theorem
    is proved without it). Fixed cash flows in a Heath–Jarrow–Morton model assume the bond-pricing
    identity that the drift condition would deliver. The backward-looking caplet assumes the
    lognormal law of the compounded overnight rate.
  - Eight prove a special case or check transcribed closed forms against each other: the first
    arrival of a Poisson process, the Ornstein–Uhlenbeck Hermite modes up to degree 2, Stulz's call
    on the maximum at zero strike, the Heynen–Kat barrier at zero correlation, Haug's and
    Rubinstein–Reiner's barrier formulas, a piecewise-linear interpolation of call quotes weaker
    than Kahalé's, and the transcribed Goldman–Sosin–Gatto lookback, bounded below by the call.
- **Girsanov.** Only bounded θ. Novikov's condition is not proved.
- **Completeness.** In the Brownian market only completeness ⇒ uniqueness of the pricing measure is
  proved, and the hedge is not identified (Clark–Ocone,
  [#182](https://github.com/formal-applied-math/formal-mathfin/issues/182)). In the Black–Scholes
  market the pricing measure's restriction to 𝓕_T is unique among those with a density
  square-integrable under the Girsanov measure, in particular among bounded densities against the
  physical measure (`BlackScholes.trim_eq_of_isPricingMeasure_withDensity`); a pricing measure with an arbitrary
  density is not covered.
- **Itô calculus.** The Itô process is built from one Brownian motion with continuous coefficients.
  Itô's formula for a general continuous semimartingale and a quadratic-variation process are not
  proved.
- **SDEs.** The solution is a fixed point in the L² space of predictable processes, not a process
  with continuous adapted paths, and pathwise uniqueness is not proved. The Black–Scholes path
  solves its SDE but is not identified with the fixed point.
- **Jump-diffusions.** The process is assumed. Only the jump-free case is constructed.
- **Interest rates.** That the Wiener-integral representation of the short rate solves its SDE is
  cited, not proved. Outside Vasicek and Hull–White, the bonds are hypotheses of the model.

Each landmark's scope on the
[landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html) gives the
details, and every corpus entry publishes its own in `formalization_scope`.

## Building

With [elan](https://github.com/leanprover/elan) installed:

```bash
git clone https://github.com/formal-applied-math/formal-mathfin.git
cd formal-mathfin
lake exe cache get   # prebuilt Mathlib
lake build
```

To reproduce a release's claims in one command, run
[`scripts/reproduce.sh`](scripts/reproduce.sh) from a clone at its tag: it builds the library
(every proof, and the axiom pins below), then runs the repository's checks on the sources and the
corpus. `scripts/reproduce.sh --corpus` also re-checks every benchmark snippet against the library,
which takes hours on one machine.

[`lean-toolchain`](lean-toolchain) pins the Lean version and
[`lake-manifest.json`](lake-manifest.json) pins Mathlib and BrownianMotion. BrownianMotion and the
library itself are compiled from source. [`CONTRIBUTING.md`](CONTRIBUTING.md) describes a prebuilt
Docker image and a faster edit-and-check loop for contributors.

## Using the library in a project

Create a Lean project whose [`lean-toolchain`](lean-toolchain) matches the library's, and add the
dependency to its `lakefile.toml`:

```toml
[[require]]
name = "MathFin"
git = "https://github.com/formal-applied-math/formal-mathfin"
rev = "v2.0.0"
```

Then fetch it and the prebuilt Mathlib files:

```bash
lake update
lake exe cache get
lake build
```

and import it with `import MathFin`. Each release tag fixes the Lean toolchain, Mathlib and
BrownianMotion together; to follow `main` instead, use `rev = "main"` with the toolchain from that
revision. The first build compiles BrownianMotion and the library from source.
[`MathFinTest/Readme.lean`](MathFinTest/Readme.lean) is such a client: it imports only `MathFin`
and states the theorem quoted above, and a weekly workflow builds it in a fresh project that
requires this repository.

## Verification

A successful `lake build` checks every proof in the library. Outside it, `sorry` appears in two
places, on purpose: [`Challenge.lean`](Challenge.lean), whose two theorems are left unproved for
the comparator, and [`MathFinFrontier/`](MathFinFrontier), which states open problems in Lean.
Nothing in `MathFin` imports either.

- **Axioms.** [`MathFin/AxiomAudit.lean`](MathFin/AxiomAudit.lean) and the generated
  [`MathFin/AxiomAuditGen.lean`](MathFin/AxiomAuditGen.lean) pin the `#print axioms` output of the
  headline results and of every constant a benchmark proof cites. The pins include the upstream
  theorems that `library_wrapper` entries re-export: BrownianMotion has `sorry`s of its own, and
  none of those theorems depends on one.
- **Comparator.** [`Solution.lean`](Solution.lean) proves the Mathlib-only statement of the
  coherent-risk representation in [`Challenge.lean`](Challenge.lean). `lake comparator --paranoid`
  checks that the statements match, that only the three standard axioms are used, and that every
  kernel bundled with Lean accepts the proofs ([`docs/palomar.md`](docs/palomar.md)).
- **Benchmark.** Each entry in [`benchmarks/`](benchmarks) records a result's Lean statement, status
  and scope. [`verification_ledger.json`](verification_ledger.json) stores a hash of the inputs each
  entry was checked under, and CI fails if they change without a re-check. The entries are
  published as a
  [Hugging Face dataset](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems).
- **Kernel replay.** A monthly workflow replays every module through `leanchecker`, below the
  elaborator.
- **Provenance.** [`formalization.yaml`](formalization.yaml) records how the library was written,
  including AI assistance.

## Documentation

[`docs/README.md`](docs/README.md) indexes every document by what a reader wants to do. The ones
most readers need are listed under [Where to start](#where-to-start);
[`docs/coverage.md`](docs/coverage.md) is the dated log of status changes and corrections.

## Contributing

Contributions are welcome, from people and from agents working for them.
[`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to add a theorem, and
[`docs/onboarding.md`](docs/onboarding.md) walks through a first contribution. Issues labelled
[good first issue](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22)
are the usual starting point.

## Contributors

Raphael Coelho maintains the library, with contributions from:

- [Godstime Aburu](https://github.com/BboyGT): the issue-label taxonomy.
- [Alfredo Garcia](https://github.com/oxarbitrage): Glosten–Milgrom adverse selection, a drift term
  in the Itô-process price and the CIR bond loadings.
- [Robert Martin](https://github.com/robertmartin8): log-convexity of the American put exercise
  boundary.
- [Aleksey Salkutsan](https://github.com/kernelpanic888): forward rate agreements and downside
  performance metrics.
- [Mert Unsal](https://github.com/mertunsall): the Black–Scholes charm.
- [Yang Ye](https://github.com/leafyoung): the integrated Itô–drift identity, Hull–White
  calibration, a Monte Carlo pricer, Cox credit, CMS rates and curve bootstrapping; the bivariate
  normal CDF, the Schwartz futures price, CVA, inflation, the LHP tranche loss, calendar arbitrage,
  joint elicitability, CreditMetrics, SA-CCR, two-asset options and DeFi lending and AMM
  mechanics; trinomial and willow lattices, arbitrage-free interpolation of call quotes, natural
  cubic splines, FX smile quotes, SABR chain-rule Greeks, the continuous lookback and the shout
  floor, Marchenko–Pastur edges and historical VaR for concentrated liquidity; the Bachelier spread
  call, the Nelson–Siegel–Svensson decay limit, the backward-looking caplet, the lognormal
  volatility swap and the Heston transform at maturity.
- [Adam Kiezun](https://github.com/akiezun): whole-life insurance on the survival function, the
  life table, two-life annuities, Thiele's reserve equation, Bühlmann credibility, sampled stopping
  rules, CDS recovery timing, the stop-loss recursion, discrete Almgren–Chriss liquidation, and
  the chain ladder with its exact rational evaluation.

Each module's header names its authors.

## Citation

```bibtex
@article{coelho2026mathfin,
  title   = {A Formally Verified Library of Mathematical Finance in {Lean} 4},
  author  = {Coelho, Raphael},
  journal = {arXiv preprint arXiv:2606.01356},
  year    = {2026},
  doi     = {10.48550/arXiv.2606.01356}
}
```

To cite the software itself, use the Zenodo DOI
[10.5281/zenodo.20477781](https://doi.org/10.5281/zenodo.20477781), which resolves to the latest
release. Both are in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

The library depends on Mathlib and on BrownianMotion, the formalization of Brownian motion and
stochastic integration led by Rémy Degenne. The stochastic-processes part of the benchmark follows
Yuri F. Saporito's *Stochastic Processes*. The contract language takes its design ideas, but no
code, from Paul Bilokon's *The Contract Is Not the Model* (2026), and the survival models draw on
Yosuke Ito's Archive of Formal Proofs entry on actuarial mathematics
([`docs/sources.md`](docs/sources.md)). The American put results are ported from Robert Martin's
[AmericanPutConvexity](https://github.com/robertmartin8/AmericanPutConvexity), and the SVI
polynomial-sign certificate from his
[ButterflyFreeSVI](https://github.com/robertmartin8/ButterflyFreeSVI).

## License

Apache 2.0. See [`LICENSE`](LICENSE).
