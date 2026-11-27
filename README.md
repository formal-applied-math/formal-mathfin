# formal-mathfin

[![build](https://github.com/formal-applied-math/formal-mathfin/actions/workflows/build.yml/badge.svg)](https://github.com/formal-applied-math/formal-mathfin/actions/workflows/build.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2606.01356-b31b1b.svg)](https://arxiv.org/abs/2606.01356)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20477781.svg)](https://doi.org/10.5281/zenodo.20477781)
[![dataset](https://img.shields.io/badge/Hugging%20Face-dataset-ffcc4d.svg)](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems)

A library of mathematical finance in [Lean 4](https://lean-lang.org), built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and Rémy Degenne's
[BrownianMotion](https://github.com/RemyDegenne/brownian-motion). A theorem enters only when every
hypothesis is stated and every step is checked by Lean's kernel. It covers stochastic calculus,
no-arbitrage theory, derivative pricing, fixed income, portfolio choice, risk measures and
actuarial mathematics.

The [corpus](docs/glossary.md#corpus) records 924 results from the literature in
[`benchmarks/`](benchmarks), each with a Lean statement and proof. Of these, 877 are proved in
full, 18 restate a lemma from Mathlib or BrownianMotion, and 29 are
[reduced cores](docs/glossary.md#status) that prove less than the result they are named after,
and say so. The library contains no `sorry`, and a build-time audit checks that every library
theorem the corpus cites depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Here is the convergence of the Cox–Ross–Rubinstein call price to the Black–Scholes price
([`CRRClosedForm.lean`](MathFin/Models/Binomial/CRRClosedForm.lean)):

```lean
theorem binomialPrice_call_tendsto_bs_closed {r σ T S₀ K : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (hS₀ : 0 < S₀) (hK : 0 < K)
    (hna : ∀ n, 0 < n → BinomialNoArb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)) :
    Tendsto (fun n : ℕ ↦ binomialPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        (fun x ↦ max (x - K) 0) n S₀) atTop
      (𝓝 (S₀ * Phi (bsd1 S₀ K r σ T)
          - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T)))
```

The textbook proof leaves `hna` implicit: the tree must be free of arbitrage at every step. Lean
will not proceed without it, and [`binomialNoArb_crr`](MathFin/Models/Binomial/CRRConvergence.lean)
shows it holds whenever $`|r|\sqrt{T} < \sigma`$.

## Main results

The [landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html) prints
each of these exactly as Lean states it, with what it does not prove beside it.

- **Stochastic calculus.** Itô's formula for f(t, B_t) with no growth condition, and for Itô
  processes with continuous adapted coefficients; Lévy's characterization; Girsanov's theorem for
  bounded θ; martingale representation; for Lipschitz coefficients, a unique fixed point of the
  SDE's Picard map.
- **No arbitrage.** The fundamental theorems of asset pricing on a finite space, and for one real
  asset on any probability space (Dalang–Morton–Willinger).
- **Black–Scholes.** The PDE from Feynman–Kac, the delta hedge, and the call value as the value of
  a contract.
- **Trees and the limit.** Cox–Ross–Rubinstein converges to Black–Scholes.
- **The smile.** An exact polynomial-sign certificate for butterfly-free raw SVI; calendar
  arbitrage as monotone total variance; Dupire's equation in the sense of distributions, with no
  smoothness assumed of the call surface.
- **The American put.** Its exercise boundary is convex in time to expiry for 0 ≤ q ≤ r, an open
  question settled here by Robert Martin's proof.
- **Jumps and rates.** Merton's jump-diffusion price derived from the model; Vasicek and
  Hull–White bonds, Jamshidian's bond options, swaptions under the annuity measure.
- **Risk.** On a finite state space, a coherent risk measure is the supremum of expected losses
  over a set of probability vectors.

## How it is kept honest

- **Every entry has a status**, and only `full` and `library_wrapper` entries may be cited as the
  named theorem. Each entry also publishes, beside its description, what it leaves out.
- **Reduced cores.** Twenty-nine of the results prove less than the theorem they are named after.
  Eleven assume a structure whose fields include the textbook conclusion, six rest on a named
  hypothesis that is not proved, and twelve prove a special case. Each is listed in
  [`docs/coverage.md`](docs/coverage.md).
- **Known gaps.** Girsanov is proved for bounded θ only, and Novikov's condition is not. In the
  Brownian market only completeness ⇒ uniqueness of the pricing measure is proved, and the hedge
  is not identified (Clark–Ocone, [#182](https://github.com/formal-applied-math/formal-mathfin/issues/182)).
  A multi-dimensional Itô formula is not yet in the library.
- **Prose against statement.** The failure this library has actually met is prose that claims
  more than its Lean proves, while the build stays green. [`docs/faithfulness.md`](docs/faithfulness.md)
  records the 107 times it happened and what now catches it.
- **Below the elaborator.** Axiom pins on every constant the corpus cites, a comparator check of
  the [Palomar](docs/palomar.md) statements, and a monthly `leanchecker` replay of every module.
  BrownianMotion has `sorry`s of its own; the pins show that no cited theorem depends on one.
  Outside the library, `sorry` appears on purpose in [`Challenge.lean`](Challenge.lean), the
  comparator's statement, and in [`MathFinFrontier/`](MathFinFrontier), which states open problems
  in Lean.

## How AI is used here

Much of this library was written by AI agents working for the maintainer, under the rules in
[`CLAUDE.md`](CLAUDE.md) and the gates above. The kernel decides whether a proof is correct. The
maintainer decides what the library contains, directs and reviews the work, and commissions the
review of proof content that closes each working session. [`docs/ai.md`](docs/ai.md) says who did what, where AI went wrong, and how the
library's open-problem work, the cátedra, puts its review on faithfulness rather than correctness.

## How the library is organized

Financial mathematics has one economic object, a price system: positions in a market and the set
of pricing measures that price them. Its deep theorems are three dualities of that set: with
trading gains (valuation), with the positions a risk measure accepts (risk), and with the positions
an investor prefers (choice). The library is one tree: probability at the roots, the price system
as the trunk, valuation, choice and risk as the limbs, with the model families as a second axis.
Contracts are terms of their own language, priced by any model.

The [program tree](https://formal-applied-math.github.io/formal-mathfin/tree.html) draws it, with
what is proved and what is stated next. [`docs/organization.md`](docs/organization.md) gives the
account; one file, [`docs/taxonomy.toml`](docs/taxonomy.toml), drives the directories, the
[blueprint](docs/blueprint.md), the issue labels and the site.

## Where to start

- **To read.** The [documentation site](https://formal-applied-math.github.io/formal-mathfin/), with
  a page for every module and a search over every declaration; nothing to install.
- **To learn Lean through the library.** The [beginners' manual](docs/beginners-manual.md), with
  checked exercises, and worked [applications](MathFinExamples/Applications), from a capped call to a
  chain-ladder reserve.
- **To do research.** The [open problems](docs/research-problems/README.md) of the field, each with a
  precise statement and dated sources, and the blueprint's frontier.
- **To contribute.** [`CONTRIBUTING.md`](CONTRIBUTING.md) and [`docs/onboarding.md`](docs/onboarding.md).
- **For agents.** [`AGENTS.md`](AGENTS.md), the site's
  [`llms.txt`](https://formal-applied-math.github.io/formal-mathfin/llms.txt), and the corpus as a
  [Hugging Face dataset](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems).

## Building and using

```bash
git clone https://github.com/formal-applied-math/formal-mathfin.git
cd formal-mathfin
lake exe cache get   # prebuilt Mathlib
lake build           # checks every proof
```

To depend on it, add to your `lakefile.toml`, with a `lean-toolchain` matching the library's:

```toml
[[require]]
name = "MathFin"
git = "https://github.com/formal-applied-math/formal-mathfin"
rev = "v2.0.0"
```

and `import MathFin`. [`scripts/reproduce.sh`](scripts/reproduce.sh) reproduces a release's claims
from its tag; [`docs/README.md`](docs/README.md) indexes the rest of the documentation.

## Contributors

Raphael Coelho maintains the library, with contributions from:

- [Godstime Aburu](https://github.com/BboyGT): the issue-label taxonomy.
- [Alfredo Garcia](https://github.com/oxarbitrage): Glosten–Milgrom adverse selection, a drift term
  in the Itô-process price and the CIR bond loadings.
- [Robert Martin](https://github.com/robertmartin8): log-convexity of the American put exercise
  boundary, and the SVI polynomial-sign certificate, ported from his
  [AmericanPutConvexity](https://github.com/robertmartin8/AmericanPutConvexity) and
  [ButterflyFreeSVI](https://github.com/robertmartin8/ButterflyFreeSVI).
- [Aleksey Salkutsan](https://github.com/kernelpanic888): forward rate agreements and downside
  performance metrics.
- [Mert Unsal](https://github.com/mertunsall): the Black–Scholes charm.
- [WorldianAI](https://github.com/WorldianAI): the Ho–Lee bond price, the security policy and the
  pin-bump policy.
- [Yang Ye](https://github.com/leafyoung), much of whose work mirrors QuantLib's pricing engines
  in Lean and proves the limits and special cases the code handles by hand: the integrated
  Itô–drift identity, Hull–White calibration, a Monte Carlo pricer, Cox credit, CMS rates and
  curve bootstrapping; the bivariate normal CDF, the Schwartz futures price, CVA, inflation, the
  LHP tranche loss, calendar arbitrage, joint elicitability, CreditMetrics, SA-CCR, two-asset
  options and DeFi lending and AMM mechanics; trinomial and willow lattices, arbitrage-free
  interpolation of call quotes, natural cubic splines, FX smile quotes, SABR chain-rule Greeks,
  the continuous lookback and the shout floor, Marchenko–Pastur edges and historical VaR for
  concentrated liquidity; the Bachelier spread call, the Nelson–Siegel–Svensson decay limit, the
  backward-looking caplet, the lognormal volatility swap, the Jarrow–Yildirim inflation caplet and
  year-on-year forward, the average-strike Asian conditioning bound, the Heston transform at
  maturity and the Broadie–Glasserman–Kou barrier shift for discrete monitoring; the forward-start
  call, the strict American put premium, contango and basis convergence, the Balancer
  constant-mean pool, the numéraire density as a Radon–Nikodym derivative and the Ho–Lee limit of
  Vasicek.
- [Adam Kiezun](https://github.com/akiezun): whole-life insurance on the survival function, the
  life table, two-life annuities, Thiele's reserve equation, Bühlmann credibility, sampled stopping
  rules, CDS recovery timing, the stop-loss recursion, discrete Almgren–Chriss liquidation, and
  the chain ladder with its exact rational evaluation.

Each module's header names its authors.

## Citation and acknowledgements

Cite the library paper, [arXiv:2606.01356](https://arxiv.org/abs/2606.01356), or the software
through the Zenodo DOI [10.5281/zenodo.20477781](https://doi.org/10.5281/zenodo.20477781), which
resolves to the latest release; both are in [`CITATION.cff`](CITATION.cff).

The library depends on Mathlib and on BrownianMotion, the formalization of Brownian motion and
stochastic integration led by Rémy Degenne. The stochastic-processes part of the corpus follows
Yuri F. Saporito's *Stochastic Processes*. The contract language takes its design ideas, but no
code, from Paul Bilokon's *The Contract Is Not the Model* (2026), and the survival models draw on
Yosuke Ito's Archive of Formal Proofs entry on actuarial mathematics
([`docs/sources.md`](docs/sources.md)).

Apache 2.0. See [`LICENSE`](LICENSE).
