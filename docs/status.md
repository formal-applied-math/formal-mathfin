# Status

Where the program stands, in one page: what it covers, how its parts connect, and where the work
is. Strategy is in [`roadmap.md`](roadmap.md); the log of status changes is
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

The corpus is grouped by area, one file per area in [`../benchmarks/`](../benchmarks/): the
stochastic-processes files follow the chapters of Saporito's *Stochastic Processes* (Brownian
motion, martingales, Markov chains, Poisson processes, stochastic calculus, Girsanov), and the
finance files follow the field (no arbitrage, Black–Scholes, exotic options, jumps and variance
swaps, interest rates, credit, risk measures, quantitative risk management, portfolios and
performance, binomial models, contracts, actuarial mathematics, market microstructure,
commodities and DeFi). The site's [corpus page](https://formal-applied-math.github.io/formal-mathfin/corpus.html)
lists every entry with its status.

## How the parts connect

[`organization.md`](organization.md) is the account: one object (positions in a market and the
pricing measures that price them), three questions asked of it (valuation, risk, choice), the
model families as a second axis, probability and statistics as the tools. The four methods the
results are proved with, and the seams between them, are in
[`mathematical-architecture.md`](mathematical-architecture.md).

Three rules keep it one library, each enforced by a test:

* **Every module connects** (`tests/test_architecture.py`). It imports a library module or is
  imported by one, and is imported by another module or cited by a corpus entry. Imports follow
  the layers of [`architecture.md`](architecture.md).
* **Every claim is checked.** No `sorry`, and every cited constant
  [axiom-pinned](glossary.md#axiom-pin). Prose may not outrun the statement
  (`tests/test_values.py`). The [ledger](glossary.md#ledger) re-checks exactly the entries whose
  inputs changed.
* **The values review keeps pace.** A review is due when the corpus or the module count outgrows
  the last recorded one ([`values-review.md`](values-review.md)).

## The backlog

The single backlog is the [issue tracker](https://github.com/formal-applied-math/formal-mathfin/issues).
Labels follow [`issue-labels.md`](issue-labels.md). Every mathematical issue carries the
`area:<cell>` and `family:<family>` labels its blueprint nodes derive, from the one taxonomy of
[`organization.md`](organization.md): for instance [`area:valuation/term`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Avaluation%2Fterm),
[`area:choice/equilibrium`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Achoice%2Fequilibrium), [`area:risk/measures`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Aarea%3Arisk%2Fmeasures), [`family:jumps`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Afamily%3Ajumps).

Work that is ready to pick up carries
[`status:ready`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3Astatus%3Aready);
work waiting on a design or on upstream carries `status:blocked-design` or
`status:blocked-upstream`. Each values review ends in a ranked backlog
([`values-review.md`](values-review.md)), and its items are filed as issues. The backlog lists in
older review entries are a record of what each review found, not a second tracker: each item ends
with its outcome (`[#N]`, `[done: …]` or `[retired: …]`), and
`python3 -m tools.verify.review_backlog --open` lists any that do not.

## Where to read next

The index of every document is [`README.md`](README.md). For a first contribution, read
[`onboarding.md`](onboarding.md) and [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
