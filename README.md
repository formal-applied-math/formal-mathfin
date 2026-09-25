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

Release 1.4.0 records 373 results from the literature in [`benchmarks/`](benchmarks), each with a
Lean statement and proof. Of these, 342 are proved in full, 18 restate a lemma from Mathlib or
BrownianMotion, and 13 are reduced cores that prove less than the result they are named after.
Each entry records its status and what it leaves out. The library contains no `sorry`, and a
build-time audit checks that the main results below, and most other theorems the benchmark cites,
depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

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

- **Itô's formula.** For every $`C^3`$ function $`f(t,x)`$, with no growth condition,
  $`f(t,B_t) - f(0,B_0) - \int_0^t \big(\partial_t f + \tfrac12 \partial_x^2 f\big)(s,B_s)\,ds`$
  is a continuous local martingale
  ([`ito_formula_unrestricted`](MathFin/Foundations/ItoFormulaUnrestrictedLocMart.lean)). When the
  partial derivatives of $`f`$ are bounded, its value at time $`T`$ is the Itô integral
  $`\int_0^T \partial_x f(s,B_s)\,dB_s`$
  ([`ito_formula_td_L2_bddDeriv`](MathFin/Foundations/ItoFormulaTD.lean)).

- **Girsanov's theorem.** For bounded predictable $`\theta`$, let
  $`dQ = \exp\big(-\int_0^T \theta\,dB - \tfrac12 \int_0^T \theta^2\,dt\big)\,dP`$. On $`[0,T]`$,
  under $`Q`$, the process $`B_t + \int_0^t \theta_s\,ds`$ starts at $`0`$, has
  $`\mathcal{N}(0,t-s)`$ increments, and any two non-overlapping increments are independent
  ([`Btheta_isQBrownianMotion_predictable_of_bdd`](MathFin/Foundations/GirsanovPredictableTheta.lean)).

- **Martingale representation.** Every square-integrable, $`\mathcal{F}^B_T`$-measurable random
  variable $`H`$ can be written $`H = \mathbb{E}[H] + \int_0^T \varphi\,dB`$ for a unique
  $`\varphi`$. In trading terms, each such claim is replicated from initial wealth
  $`\mathbb{E}[H]`$ by a unique strategy
  ([`exists_replicating_strategy`](MathFin/Foundations/MarketCompleteness.lean)).

- **Stochastic differential equations.** If $`b`$ and $`\sigma`$ are Lipschitz with constants
  $`L_b`$ and $`L_\sigma`$, the Picard map
  $`X \mapsto \eta + \int_0^{\cdot} b(X)\,ds + \int_0^{\cdot} \sigma(X)\,dB`$ of
  $`dX = b(X)\,dt + \sigma(X)\,dB`$ has a unique fixed point in the $`L^2`$ space of predictable
  processes on $`[0,T]`$ whenever $`T L_b + \sqrt{T} L_\sigma < 1`$
  ([`picardMap_exists_unique_fixedPoint`](MathFin/Foundations/SDEExistence.lean)).

- **Fundamental theorem of asset pricing.** A market with one risky asset, finitely many periods
  and a finite probability space of full support has no arbitrage if and only if it has an
  equivalent martingale measure ([`ftap_discrete`](MathFin/Foundations/FTAPDiscrete.lean)). The
  one-period theorem holds on any probability space with finitely many assets
  ([`ftap_one_period_vector`](MathFin/Foundations/FTAPOnePeriodVector.lean)).

- **Coherent risk measures.** On a finite state space, a coherent risk measure satisfies
  $`\rho(X) = \sup_{q \in \mathcal{Q}_\rho} \mathbb{E}_q[-X]`$, where $`\mathcal{Q}_\rho`$ is the
  set of probability vectors that give every acceptable position a nonnegative price
  ([`coherentRisk_isLUB`](MathFin/RiskMeasures/AcceptanceSet.lean)). This theorem and the finite
  fundamental theorem are both derived from the cone-separation lemmas in
  [`ConvexDuality.lean`](MathFin/Foundations/ConvexDuality.lean).

- **The Black–Scholes PDE from Feynman–Kac.** The call price is written as a heat-kernel integral,
  and the Black–Scholes PDE follows from the heat equation for the kernel, without differentiating
  the closed-form price
  ([`bsV_satisfies_bs_pde_via_feynmanKac`](MathFin/BlackScholes/PDEFromFeynmanKac.lean)).

- **The American put.** In the Black–Scholes model with interest rate $`r > 0`$ and dividend yield
  $`0 \le q \le r`$, the early-exercise boundary $`B(\tau)`$ of the American put is strictly convex
  in the time to expiry, and $`\log(B(\tau)/K)`$ is convex
  ([`PhysicalBoundaryConvexity.lean`](MathFin/BlackScholes/AmericanPut/Stopping/PhysicalBoundaryConvexity.lean),
  described in [`docs/american-put-boundary.md`](docs/american-put-boundary.md)).

## Contents

| Area | Topics |
|---|---|
| Probability | conditional expectation, martingales and stopping times, Brownian motion, Poisson processes, Markov chains |
| Stochastic calculus | Itô integral and isometry, quadratic variation, Itô's formula, Girsanov's theorem, martingale representation, SDEs, Feynman–Kac, compensated Poisson integral |
| No-arbitrage | fundamental theorems, equivalent martingale measures, change of numéraire, market completeness, superreplication |
| Option pricing | Black–Scholes prices and Greeks, the Black–Scholes PDE, implied volatility, dividends, FX (Garman–Kohlhagen), Bachelier, Black-76, Merton jump-diffusion, Breeden–Litzenberger |
| Exotic options | digital, exchange (Margrabe), chooser, barrier, lookback, geometric Asian, power and quanto options; spreads; variance swaps |
| Lattice models | binomial replication, American and Bermudan options via the Snell envelope, Cox–Ross–Rubinstein convergence, André's reflection principle |
| Fixed income and credit | bonds, duration and convexity, immunization, yield curves, forward rates, FRAs, swaps and swaptions, the forward measure, Vasicek, hazard rates, CDS, first-to-default, KMV–Merton |
| Portfolio theory | Markowitz, CAPM, two-fund separation, the tangency portfolio, risk parity, Black–Litterman; Sharpe, Sortino, Treynor and information ratios; the Kelly criterion |
| Risk measures | Gaussian VaR and CVaR, coherent and spectral risk measures, Rockafellar–Uryasev, expected utility, concentration indices |
| Market microstructure | Avellaneda–Stoikov market making, the Glosten–Milgrom spread |
| Other | a contract language that separates payoffs from pricing models; survival models, mortality and annuities; compound Poisson losses; constant-product AMMs |

## Limitations

- Thirteen of the 373 results are reduced cores. Twelve assume a structure whose fields include the
  textbook conclusion, so the conclusion is not derived: the reflection principle, nowhere
  differentiability and the law of the iterated logarithm for Brownian motion, Novikov's condition,
  the general form of Girsanov's theorem, Lévy's characterization, the two-dimensional Itô formula,
  and five theorems on Markov chains. The thirteenth proves a special case: the first interarrival
  time of a Poisson process is exponential.
- Girsanov's theorem is proved only for bounded predictable $`\theta`$.
- Of the second fundamental theorem, only the direction from completeness to uniqueness is proved:
  for a price $`S = S_0 + \int_0^t \sigma\,dB`$ with $`\sigma \neq 0`$ almost everywhere, a
  probability measure with square-integrable density with respect to $`P`$, under which $`S`$ is a
  martingale, agrees with $`P`$ on $`\mathcal{F}^B_T`$.
- Martingale representation proves that a hedge exists and is unique, but does not identify it;
  that needs the Clark–Ocone formula
  ([#182](https://github.com/formal-applied-math/formal-mathfin/issues/182), open).
- Existence for SDEs with Lipschitz coefficients is proved only on horizons with
  $`T L_b + \sqrt{T} L_\sigma < 1`$.
- The binomial limit is proved for call prices and for the law of the terminal log-return.
  Convergence of the price process (Donsker's invariance principle) is not formalized.
- The multi-period fundamental theorem and the representation of coherent risk measures are proved
  on finite probability spaces only.

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

## Verification

A successful `lake build` checks every proof in the library. The benchmark entries are not Lake
targets and are checked separately (see Benchmark below). In this repository, `sorry` appears only
in the two theorems of [`Challenge.lean`](Challenge.lean), which are left unproved on purpose (see
Comparator below).

- **Axioms.** [`MathFin/AxiomAudit.lean`](MathFin/AxiomAudit.lean) and the generated
  [`MathFin/AxiomAuditGen.lean`](MathFin/AxiomAuditGen.lean) run `#print axioms` on a curated list
  of headline results and on every library theorem that a benchmark entry cites by its full
  `MathFin.` name, and compare the output with `#guard_msgs`. A `sorry` or an extra axiom anywhere
  in the proof of one of them fails the build. Theorems cited under a shorter name are not yet
  covered.

- **Comparator.** [`Challenge.lean`](Challenge.lean) states the coherent-risk representation
  theorem, with a witness that its hypothesis is satisfiable, using only Mathlib;
  [`Solution.lean`](Solution.lean) proves both from the library.
  [Comparator](https://github.com/leanprover/comparator), configured by
  [`comparator.json`](comparator.json), checks that the two files state the same theorems and that
  the proofs use only the three standard axioms. It accepted both at commit `06f88ca` and is not
  run in CI; see [`docs/palomar.md`](docs/palomar.md).

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

- [`docs/coverage.md`](docs/coverage.md): a dated log of status changes and corrections, with
  verification evidence.
- [`docs/blueprint.md`](docs/blueprint.md): a dependency graph from Brownian motion to Black–Scholes,
  generated from the Lean source.
- [`docs/mathematical-architecture.md`](docs/mathematical-architecture.md): the principles the
  library is organized around, and the theorems that connect them.
- [`MathFin/Examples.lean`](MathFin/Examples.lean): five representative proofs.
- [`docs/open-problems.md`](docs/open-problems.md): a survey of open problems in mathematical
  finance.
- [`docs/roadmap.md`](docs/roadmap.md) and the
  [issue tracker](https://github.com/formal-applied-math/formal-mathfin/issues): planned work.
- [`docs/README.md`](docs/README.md): an index of the remaining documents.

## Contributing

Contributions are welcome. [`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to add a theorem, and
[`docs/onboarding.md`](docs/onboarding.md) walks through a first contribution. Issues labelled
[good first issue](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22)
are the usual starting point.

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
stochastic integration led by Rémy Degenne. Much of the benchmark follows Yuri F. Saporito's
*Stochastic Processes*. The contract language takes its design ideas, but no code, from Paul
Bilokon's *The Contract Is Not the Model* (2026), and the survival models draw on Yosuke Ito's
Archive of Formal Proofs entry on actuarial mathematics ([`docs/sources.md`](docs/sources.md)). The
American put results are ported from Robert Martin's
[AmericanPutConvexity](https://github.com/robertmartin8/AmericanPutConvexity).

## License

Apache 2.0. See [`LICENSE`](LICENSE).
