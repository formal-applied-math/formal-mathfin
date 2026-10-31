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

The corpus records 754 results from the literature in [`benchmarks/`](benchmarks), each with a
Lean statement and proof. Of these, 721 are proved in full, 18 restate a lemma from Mathlib or
BrownianMotion, and 15 are reduced cores that prove less than the result they are named after.
Each entry records its status and what it leaves out. The library contains no `sorry`, and a
build-time audit checks that every library theorem the benchmark's proofs cite depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

Here, for example, is the convergence of the Cox–Ross–Rubinstein call price to the Black–Scholes
price, from [`CRRClosedForm.lean`](MathFin/Binomial/CRRClosedForm.lean):

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
whenever $`|r|\sqrt{T} < \sigma`$ ([`binomialNoArb_crr`](MathFin/Binomial/CRRConvergence.lean)).

## Main results

- **Itô's formula.** For $`f(t,x)`$ with continuous $`f`$, $`\partial_t f`$, $`\partial_x f`$ and
  $`\partial_x^2 f`$, and no growth condition, the process
  $`f(t,B_t) - f(0,B_0) - \int_0^t \big(\partial_t f + \tfrac12 \partial_x^2 f\big)(s,B_s)\,ds`$
  is a continuous local martingale
  ([`ito_formula_unrestricted`](MathFin/Foundations/ItoFormulaUnrestrictedLocMart.lean)). For an
  Itô process $`X = x_0 + \int b\,ds + \int \sigma\,dB`$ with continuous adapted coefficients and
  no bounds on them or on $`f`$, almost surely, at every $`t \le T`$ at once,

  ```math
  f(t,X_t) - f(0,x_0) = \int_0^t f_x(s,X_s)\,\sigma_s\,dB_s
    + \int_0^t \Big(f_t + f_x\,b_s + \tfrac12 f_{xx}\,\sigma_s^2\Big)(s,X_s)\,ds,
  ```

  and the stochastic integral has a version that is a continuous local martingale for the
  augmented Brownian filtration
  ([`ito_formula_adapted_unbounded_process`](MathFin/Foundations/ItoFormulaAdaptedProcess.lean),
  [`exists_localMartingale_ito_formula`](MathFin/Foundations/ItoFormulaAdaptedProcess.lean)).

- **Lévy's characterization.** A continuous adapted process $`M`$ with $`M_0 = 0`$ such that $`M`$
  and $`M^2 - t`$ are local martingales for a filtration $`\mathcal{F}`$ is an
  $`\mathcal{F}`$-Brownian motion
  ([`isFilteredPreBrownian_of_localMartingale`](MathFin/Foundations/LevyCharacterization.lean)).

- **Girsanov's theorem.** For bounded predictable $`\theta`$, let
  $`dQ = \exp\big(-\int_0^T \theta\,dB - \tfrac12 \int_0^T \theta^2\,dt\big)\,dP`$. Under $`Q`$, on
  $`[0,T]`$, the process $`B_t + \int_0^t \theta_s\,ds`$ starts at $`0`$ and has independent
  $`\mathcal{N}(0,t-s)`$ increments
  ([`Btheta_isQBrownianMotion_predictable_of_bdd`](MathFin/Foundations/GirsanovPredictableTheta.lean),
  stated for an adapted modification, which has the same finite-dimensional laws).

- **Martingale representation.** Every square-integrable $`\mathcal{F}^B_T`$-measurable $`H`$ is
  $`\mathbb{E}[H] + \int_0^T \varphi\,dB`$ for a unique $`\varphi`$: each such claim is replicated
  from initial wealth $`\mathbb{E}[H]`$ by a unique strategy
  ([`exists_replicating_strategy`](MathFin/Foundations/MarketCompleteness.lean)).

- **Stochastic differential equations.** For Lipschitz $`b`$ and $`\sigma`$ (constants $`L_b`$,
  $`L_\sigma`$), the Picard map of $`dX = b(X)\,dt + \sigma(X)\,dB`$ has a unique fixed point in
  the $`L^2`$ space of predictable processes on $`[0,T]`$ when $`T L_b + \sqrt{T} L_\sigma < 1`$
  ([`picardMap_exists_unique_fixedPoint`](MathFin/Foundations/SDEExistence.lean)).

- **Fundamental theorem of asset pricing.** A finite-horizon market with one risky asset on a finite
  probability space of full support has no arbitrage if and only if it has an equivalent martingale
  measure ([`ftap_discrete`](MathFin/Foundations/FTAPDiscrete.lean)); the one-period theorem holds
  on any probability space with finitely many assets
  ([`ftap_one_period_vector`](MathFin/Foundations/FTAPOnePeriodVector.lean)).

- **Coherent risk measures.** On a finite state space a coherent risk measure of losses is
  $`\rho(L) = \sup_{q \in \mathcal{Q}_\rho} \mathbb{E}_q[L]`$, the supremum over the probability
  vectors that price every acceptable loss nonpositively
  ([`coherentRisk_isLUB`](MathFin/RiskMeasures/AcceptanceSet.lean)). It and the finite FTAP both
  come from the cone-separation lemmas in
  [`ConvexDuality.lean`](MathFin/Foundations/ConvexDuality.lean).

- **The Black–Scholes PDE from Feynman–Kac.** The call price is a heat-kernel integral, and the
  PDE follows from the heat equation for the kernel, without differentiating the closed form
  ([`bsV_satisfies_bs_pde_via_feynmanKac`](MathFin/BlackScholes/PDEFromFeynmanKac.lean)).

- **Jump-diffusions.** Let $`X`$ be adapted, start at $`0`$, and have increments over $`\tau`$
  independent of the past and distributed as $`b\tau + \sigma\sqrt{\tau}\,Z + \sum_{i<N} J_i`$,
  with $`Z \sim \mathcal{N}(0,1)`$, $`N \sim \mathrm{Poisson}(\Lambda\tau)`$ and i.i.d. jumps of
  law $`\nu`$, all independent. If $`S_0 \neq 0`$ and $`\int e^x\,d\nu < \infty`$, the discounted
  price $`e^{-rt} S_0 e^{X_t}`$ is a martingale exactly when
  $`b = r - \sigma^2/2 - \Lambda\big(\int e^x\,d\nu - 1\big)`$
  ([`JumpDiffusionProcess.martingale_iff`](MathFin/BlackScholes/JumpDiffusionProcess.lean)). With
  Gaussian jumps and $`\sigma, S_0, K > 0`$, the conditional value of the call at every date
  before maturity is then Merton's 1976 series
  ([`condExp_call_eq_mertonCallPrice`](MathFin/BlackScholes/JumpDiffusionMerton.lean)).

- **The American put.** A supermartingale dominating the discounted reward bounds the value, and a
  stopping rule attaining its initial value is optimal
  ([`value_eq_of_attained`](MathFin/BlackScholes/AmericanPut/Stopping/Verification.lean)). With
  $`r > 0`$ and dividend yield $`0 \le q \le r`$, the early-exercise boundary $`B(\tau)`$ is
  strictly convex in the time to expiry and $`\log(B(\tau)/K)`$ is convex
  ([`PhysicalBoundaryConvexity.lean`](MathFin/BlackScholes/AmericanPut/Stopping/PhysicalBoundaryConvexity.lean),
  [`docs/american-put-boundary.md`](docs/american-put-boundary.md)).

- **Raw SVI.** A fixed Boolean combination of polynomial signs in $`(a, b, \rho, m, \sigma)`$ holds
  exactly when $`\sigma, b \ge 0`$, $`\rho^2 \le 1`$, the total variance is positive and the
  Black–Scholes call with the SVI volatility is convex in the strike (Durrleman's condition for
  $`\sigma > 0`$). With one more sign, $`b(1+\rho) < 2`$, it holds exactly when that call is also
  nonincreasing, lies between $`(1-K)^+`$ and $`1`$, and has the limits of a call price
  ([`extendedCertificateFormula_iff_bsSmile_convex`](MathFin/BlackScholes/SVI/ExtendedFormula.lean),
  [`butterflyFreeFormula_iff_isNormalizedCallPrice`](MathFin/BlackScholes/SVI/TailCondition.lean)).

- **Contracts, separate from models.** Payoffs are terms of a contract language, priced by
  interchangeable models:
  - the values of `europeanCall K T` in the $`n`$-step CRR tree converge to its Black–Scholes
    value when $`|r|\sqrt{T} < \sigma`$
    ([`tendsto_binomial_value_europeanCall`](MathFin/Contracts/Models/BinomialLimit.lean));
  - in any model whose discounted price is a martingale from $`S_0`$, a call less a put is worth
    the forward, $`S_0 - K D(T)`$
    ([`value_europeanCall_sub_put_of_martingale`](MathFin/Contracts/Parity.lean));
  - the power call, the exchange option and the geometric Asian call are worth their Black–Scholes
    closed forms, and the chooser's replicating portfolio is worth Rubinstein's
    ([`Contracts/Models/`](MathFin/Contracts/Models)).

- **Interest rates.** In Vasicek and in Hull–White with continuous forcing, discounting by
  $`e^{-\int_0^t r_s\,ds}`$:
  - the bond price at $`t`$ is $`A_t(T-t)\,e^{-B(T-t)\,r_t}`$ almost surely
    ([`bondPrice_hullWhite`](MathFin/Contracts/Models/HullWhiteBond.lean));
  - the bond put is a Black put on the bond, which is lognormal under the forward measure
    (Jamshidian), and a caplet is $`1+\delta K`$ such puts
    ([`valueDisc_bondPut_hullWhite`](MathFin/Contracts/Models/Jamshidian.lean),
    [`valueDisc_caplet_eq_bondPut`](MathFin/Contracts/Models/Caplet.lean)).

  For any discount factor, a swap rate tied to the bonds by a model bundle gives:
  - the payer swaption as $`A(0)\,\mathbb{E}^A[(S-K)^+]`$ under the annuity measure;
  - the CMS swaplet as its forward value plus an exact covariance adjustment
    ([`valueDisc_payerSwaption`](MathFin/Contracts/Models/CMS.lean),
    [`SwapModel.valueDisc_cmsSwaplet_eq`](MathFin/Contracts/Models/CMS.lean)).

## Contents

| Area | Topics |
|---|---|
| Probability | conditional expectation, martingales and stopping times, Brownian motion, Poisson processes, Markov chains |
| Stochastic calculus | Itô integral and isometry, quadratic variation, Itô's formula, Girsanov's theorem, martingale representation, SDEs, Feynman–Kac, compensated Poisson integral |
| No-arbitrage | fundamental theorems, equivalent martingale measures, change of numéraire, market completeness, superreplication |
| Option pricing | Black–Scholes prices and Greeks, the Black–Scholes PDE, implied volatility, dividends, FX (Garman–Kohlhagen), Bachelier, Black-76, jump-diffusions (Merton's formula and Greeks, Esscher pricing, incompleteness at one date), Breeden–Litzenberger, a polynomial-sign certificate for strike-convexity of raw SVI |
| Exotic options | digital, exchange (Margrabe), chooser, barrier, lookback, geometric Asian, power and quanto options; spreads; variance swaps |
| Lattice models | binomial replication, American and Bermudan options via the Snell envelope, Cox–Ross–Rubinstein convergence, André's reflection principle |
| Fixed income and credit | bonds, duration and convexity, immunization, yield curves, forward rates, FRAs, swaps, caps and caplets, swaptions and CMS under the annuity measure, the forward measure, Vasicek, Hull–White and GSR, Jamshidian's bond options, hazard rates, CDS, CVA, first-to-default, KMV–Merton |
| Portfolio theory | Markowitz, CAPM, two-fund separation, the tangency portfolio, risk parity, Black–Litterman; Sharpe, Sortino, Treynor and information ratios; the Kelly criterion |
| Risk measures | the quantile function; value-at-risk and expected shortfall for every law: Rockafellar–Uryasev, coherence of ES, its dual representation, VaR superadditivity, elicitability (VaR yes, ES no), expectiles; coherent and spectral risk measures, expected utility, concentration indices |
| Dependence and extremes | copulas and Sklar's theorem (continuous margins), Fréchet–Hoeffding bounds, Hoeffding's covariance identity, Marshall–Olkin common shocks; GEV and GPD domains of attraction, maxima of Poisson-many losses |
| Credit portfolios | Bernoulli mixtures, the one-factor Gaussian threshold model, and the Basel IRB formula as the limit of portfolio VaR |
| Market microstructure | Avellaneda–Stoikov market making, the Glosten–Milgrom spread |
| Other | a contract language that separates payoffs from pricing models, with prices in Black–Scholes, the binomial tree and the Gaussian short-rate models; survival models, mortality and annuities; compound Poisson losses; constant-product AMMs |

## Limitations

- Fifteen of the 754 results are reduced cores. Eleven assume a structure whose fields include the
  textbook conclusion, so the conclusion is not derived: the reflection principle, nowhere
  differentiability and the law of the iterated logarithm for Brownian motion, Novikov's condition,
  the general form of Girsanov's theorem, the two-dimensional Itô formula,
  and five theorems on Markov chains. The other four prove special cases: the first interarrival
  time of a Poisson process is exponential; Stulz's call on the maximum is checked only in its
  zero-strike limit, and the Heynen–Kat two-asset barrier only at zero correlation, neither formula
  being derived as an expected payoff; the Ornstein–Uhlenbeck Hermite modes decay at their
  eigenvalues only for degree at most 2.
- Girsanov's theorem is proved only for bounded $`\theta`$ (predictable, or adapted with continuous
  paths), and only at the level of finite-dimensional laws: neither path continuity of the new
  process nor independence of its increments from the past is stated.
- Of the second fundamental theorem, only the direction from completeness to uniqueness is proved:
  for a price $`S = S_0 + \int_0^t \sigma\,dB`$ with $`\sigma \neq 0`$ almost everywhere, a
  probability measure with square-integrable density with respect to $`P`$, under which $`S`$ is a
  martingale, agrees with $`P`$ on $`\mathcal{F}^B_T`$.
- Martingale representation proves that a hedge exists and is unique, but does not identify it;
  that needs the Clark–Ocone formula
  ([#182](https://github.com/formal-applied-math/formal-mathfin/issues/182), open).
- The SVI certificate's formula is defined structurally, not written out as a list of
  inequalities. Butterfly-freeness is proved as a list of properties of the call price as a
  function of the strike; the risk-neutral law is not constructed from them. At $`\sigma = 0`$
  convexity of the call is not tied to Durrleman's condition.
- Itô's formula for an Itô process is proved on a finite horizon $`[0, T]`$, for a process built
  from a single Brownian motion with continuous adapted coefficients and a deterministic starting
  point. Itô's formula for a continuous semimartingale not built from $`B`$ is not proved, and
  neither is a quadratic-variation process for a general continuous local martingale, so Lévy's
  characterization asks that $`M^2 - t`$ be a local martingale rather than that
  $`\langle M\rangle_t = t`$.
- The jump-diffusion results on a process assume the properties listed above
  (`JumpDiffusionProcess`). A process with them is constructed only without jumps, as Brownian
  motion with drift. A change of measure on the process that alters the jump rate or the jump law
  is not covered.
- Existence for SDEs with Lipschitz coefficients is proved only on horizons with
  $`T L_b + \sqrt{T} L_\sigma < 1`$.
- The binomial limit is proved for call prices and for the law of the terminal log-return.
  Convergence of the price process (Donsker's invariance principle) is not formalized.
- The multi-period fundamental theorem and the representation of coherent risk measures are proved
  on finite probability spaces only.
- Bond options and caplets are priced in Vasicek and in Hull–White with continuous forcing, where
  the bond prices are derived. Elsewhere the observed bond is a hypothesis of the model bundle, and
  so is the lognormality behind the Black-76 caplet and Black's swaption formula. The CMS
  adjustment is exact for payment at the fixing date. Its sign is proved only when every bond but
  the last is known at the fixing date.

## Building

With [elan](https://github.com/leanprover/elan) installed:

```bash
git clone https://github.com/formal-applied-math/formal-mathfin.git
cd formal-mathfin
lake exe cache get   # prebuilt Mathlib
lake build
```

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
rev = "v1.7.0"
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

A successful `lake build` checks every proof in the library. The benchmark entries are not Lake
targets and are checked separately (see Benchmark below). In this repository, `sorry` appears only
in the two theorems of [`Challenge.lean`](Challenge.lean), which are left unproved on purpose (see
Comparator below).

- **Axioms.** [`MathFin/AxiomAudit.lean`](MathFin/AxiomAudit.lean) and the generated
  [`MathFin/AxiomAuditGen.lean`](MathFin/AxiomAuditGen.lean) run `#print axioms` on a curated list
  of headline results and on every library constant that a benchmark entry's proof cites, and
  compare the output with `#guard_msgs`. A `sorry` or an extra axiom anywhere in the proof of one of
  them fails the build. Citations are found by where a name is declared, so a name cited under
  `open`, by dot notation, or from a namespace other than `MathFin` is covered. The Mathlib and
  BrownianMotion theorems that `library_wrapper` entries re-export are pinned too: BrownianMotion
  has `sorry`s of its own, and none of those theorems depends on one.

- **Comparator.** [`Challenge.lean`](Challenge.lean) states the coherent-risk representation
  theorem, with a witness that its hypothesis is satisfiable, using only Mathlib;
  [`Solution.lean`](Solution.lean) proves both from the library, converting the Challenge's
  positions convention to the library's loss convention with
  [`isCoherentRiskMeasure_neg_iff`](MathFin/RiskMeasures/PositionsConvention.lean).
  [Comparator](https://github.com/leanprover/comparator), configured by
  [`comparator.json`](comparator.json), checks that the two files state the same theorems and that
  the proofs use only the three standard axioms. It accepted an earlier Solution at commit
  `06f88ca`. It has not been re-run on the current one and is not part of CI; see
  [`docs/palomar.md`](docs/palomar.md).

- **Benchmark.** Each entry in [`benchmarks/`](benchmarks) records a result's Lean statement, its
  status and its scope. The ledger runner, `tools/verify/ledger.py`, checks each entry's snippet
  against the library, and [`verification_ledger.json`](verification_ledger.json) stores a hash of
  the inputs it was checked under; CI fails if any entry's inputs have changed since. The entries
  are published as a
  [Hugging Face dataset](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems).

- **Kernel replay.** A workflow replays every declaration through `leanchecker`, but the full
  Mathlib environment it loads does not fit on a 16 GB hosted runner, and the replay has not
  completed.

- **Provenance.** [`formalization.yaml`](formalization.yaml) describes how the library was written,
  including AI assistance and the entries drafted by an automated pipeline. The American put port
  records its own provenance in [`docs/american-put-boundary.md`](docs/american-put-boundary.md).

## Documentation

- [`docs/beginners-manual.md`](docs/beginners-manual.md): Lean and the library for mathematicians who
  have not used Lean, with exercises.
- [`docs/coverage.md`](docs/coverage.md): a dated log of status changes and corrections, with
  verification evidence.
- [`docs/blueprint.md`](docs/blueprint.md): a dependency graph from Brownian motion to Black–Scholes,
  generated from the Lean source.
- [`docs/mathematical-architecture.md`](docs/mathematical-architecture.md): the principles the
  library is organized around, and the theorems that connect them.
- [`MathFinExamples/Tour.lean`](MathFinExamples/Tour.lean): five representative proofs.
- [`MathFinExamples/Applications/`](MathFinExamples/Applications): the library applied to concrete
  problems: a capped call, put–call parity on quotes, a binomial tree, a Gaussian risk report, a
  bootstrapped curve, default correlation in a credit pool and a minimum-variance portfolio. Each
  ends in one statement the build checks.
- [`docs/open-problems.md`](docs/open-problems.md): a survey of open problems in mathematical
  finance.
- [`docs/status.md`](docs/status.md): where the program stands, and its backlog, the
  [issue tracker](https://github.com/formal-applied-math/formal-mathfin/issues).
- [`docs/roadmap.md`](docs/roadmap.md): where it is going and why.
- [`docs/README.md`](docs/README.md): an index of the remaining documents.

## Contributing

Contributions are welcome. [`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to add a theorem, and
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
  mechanics.

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
