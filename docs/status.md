# Status

Where the program stands, in one page: what it covers, how its parts connect, and where the work
is. Strategy is in [`roadmap.md`](roadmap.md); the per-theorem audit is in
[`coverage.md`](coverage.md).

## Scope

MathFin is a Lean 4 library of mathematical finance on Mathlib and Degenne's BrownianMotion, and on
nothing else. Its claims are the benchmark corpus in [`../benchmarks/`](../benchmarks/), one Lean
statement and proof per entry. Every entry declares what it proves (`full`, `library_wrapper` or
`reduced_core`), and its `description` says what the Lean proves, not the textbook result it is
named after. For the current split, run:

```bash
python3 -m tools.verify.coverage_report
```

The corpus is grouped by area: no-arbitrage, Black–Scholes, exotic options, jumps and variance
swaps, interest rates, credit, risk measures, quantitative risk management, portfolio and
performance, binomial models, contracts, actuarial mathematics, market microstructure,
commodities and DeFi, with the results that tie the stochastic foundations to them. Next to these sit the stochastic-calculus files (Brownian motion, martingales,
stochastic calculus, Girsanov), the American-put boundary and the SVI certificate.

## How the parts connect

The library is organised around four pillars and the bridges between them, described with their
current state in [`mathematical-architecture.md`](mathematical-architecture.md):

| Pillar | Core |
|---|---|
| I. No-arbitrage as convex duality | the FTAPs, state prices, superhedging, the coherent-risk representation, all on one separation root |
| II. Stochastic calculus | the Itô integral and formula, Girsanov, martingale representation, the integral against a price |
| III. Probabilistic ↔ analytic | Feynman–Kac and the Black–Scholes PDE |
| IV. Gaussian and exponential families | one normal law, its partial moments and quantile, the exponential of an integrated intensity |

Three rules keep it one library, each enforced by a test:

* **Every module connects** (`tests/test_architecture.py`). It imports a library module or is
  imported by one, and is imported by another module or cited by a corpus entry. `Foundations/`
  imports only `Foundations/`; joins between sections live in `Bridges/`.
* **Every claim is checked.** No `sorry`, and every cited constant axiom-pinned
  (`MathFin/AxiomAudit*.lean`). Prose may not outrun the statement (`tests/test_values.py`). The
  verification ledger re-checks exactly the entries whose inputs changed.
* **The values review keeps pace.** A review is due when the corpus or the module count outgrows
  the last recorded one ([`values-review.md`](values-review.md)).

## The backlog

The single backlog is the [issue tracker](https://github.com/formal-applied-math/formal-mathfin/issues).
Labels follow [`issue-labels.md`](issue-labels.md). By area:

| Area | Open issues |
|---|---|
| Foundations | [area:foundations](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Afoundations) |
| Fixed income | [area:fixed-income](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Afixed-income) |
| Credit | [area:credit](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Acredit) |
| Risk | [area:risk](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Arisk) |
| Black–Scholes and stochastic volatility | [area:black-scholes](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Ablack-scholes), [area:stoch-vol](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Astoch-vol) |
| Actuarial | [area:actuarial](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Aactuarial) |
| Futures, FX, DeFi, execution, binomial | [futures](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Afutures), [fx](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Afx), [defi](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Adefi), [execution](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Aexecution), [binomial](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Abinomial) |

Work that is ready to pick up carries
[`status:ready`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Astatus%3Aready);
work waiting on a design or on upstream carries `status:blocked-design` or
`status:blocked-upstream`. Each values review ends in a ranked backlog
([`values-review.md`](values-review.md)), and its items are filed as issues. The backlog lists in
older review entries are a record of what each review found, not a second tracker.

## Where to read next

The index of every document is [`README.md`](README.md). For a first contribution, read
[`onboarding.md`](onboarding.md) and [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
