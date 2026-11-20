# How the library is organized

Financial mathematics has one economic object, a **price system**: positions (random payoffs) in
a market, and the set of **pricing measures** that price them. Its deep theorems say that this one
set of measures is dual to three different sets of positions. MathFin is organized around that
structure, and it measures, from its own statements, how much of the library actually hangs
from it. The design and its reasons are in
[`specs/2026-11-08-chain-design.md`](specs/2026-11-08-chain-design.md); the structure is stated
once in [`taxonomy.toml`](taxonomy.toml), and the module tree, the blueprint, the issue labels,
the documentation site and the program tree all read it.

## The trunk: positions, markets, pricing measures

A **position** is a random payoff, possibly paid at several dates, written in a payoff language
(`Contract`) that mentions no measure and no model. A **market** (`Market`) is a filtered space
with traded assets and a positive numéraire. A **pricing measure** (`Market.IsPricingMeasure`) is a
probability measure equivalent to the reference one up to the horizon under which every deflated
asset is a martingale. The **price** of a contract under it (`Market.price`) is the expectation of
its deflated cash flows. A price depends on the market only through the law of what the contract
reads (`price_eq_of_map_observation_eq`), so a formula proved in one concrete model is the price
in every market with that law.

The **fundamental theorems** sit on the trunk as well, because they are what makes the pricing
measures its object rather than an assumption: no arbitrage is the existence of an equivalent
martingale measure (`ftap_discrete` on a finite space, by Stiemke's lemma;
`Market.noArbitrage_iff_exists_isPricingMeasure` for one asset on a general space), and on a
finite space completeness is its uniqueness (`ftap_two`, whose existence half is the first
theorem).

## Three dualities of one set of measures

| primal set | what the duality says | in the library |
|---|---|---|
| the gains of self-financing strategies | **valuation**: no arbitrage iff a pricing measure exists (FTAP); the superhedging price is the supremum of prices over pricing measures | the FTAP in its discrete forms, for bare price processes; joined to `Market` by one adapter (`DiscreteMarket`) |
| the positions a risk measure accepts | **risk**: a coherent risk measure is the worst expected loss over a set of measures | on a finite state space (`coherentRisk_isLUB`); expected shortfall's dual on any space |
| the positions an investor prefers | **choice**: at an optimum, marginal utility is a state-price density, so the investor's optimum defines a pricing measure | in a complete market on a finite sample space (`exists_deriv_eq_mul_sdf_of_stationary`) |

The three questions (what a position is worth, how dangerous it is, whether to hold it) are the
[limbs](glossary.md#limb); the dualities are where they meet, and the library calls those
theorems [joints](glossary.md#joint), or bridges between limbs. Not
everything should be forced through a market: a value at risk is a quantile of a law, a Sharpe
ratio is a ratio of moments, a Markowitz frontier is a quadratic programme. Such cells declare
that they stand alone and say how their object reads in a market.

## How connected it is

The library measures connection from statements only (`tools/verify/chain_reach.py`, reported on
every build). A finance theorem is one step from the trunk when its statement mentions a market
object, two steps when it mentions an object one step away, and so on. Renaming, moving or
relabelling changes nothing; only a theorem does. The site's
[program tree](https://formal-applied-math.github.io/formal-mathfin/tree.html) draws every result
at its measured height, and its
[markets page](https://formal-applied-math.github.io/formal-mathfin/markets.html) lists, for each
model family, the theorem that prices it as a market. The counts are ratchets: a build fails if
one gets worse.

A missing link is stated as a [frontier](glossary.md#frontier) node, carried by an issue: a
**market statement** proves a model family is a market, a **bridge between limbs** joins two
limbs. The program tree draws each as a dashed dot between the parts it would join.

## The bridges between limbs

| bridge | limbs | status |
|---|---|---|
| Marginal utility at the optimum is a state-price density. | choice, valuation | in a complete market on a finite sample space (`Market.IsPricingMeasure.exists_deriv_eq_mul_sdf_of_stationary`) |
| CAPM and the Hansen–Jagannathan bound follow from the stochastic discount factor. | choice, valuation | for every asset of a market with a pricing measure (`Market.IsPricingMeasure.abs_sharpeRatio_le`, `Market.IsPricingMeasure.capm_of_affine_sdf`) |
| The log-optimal portfolio is the numéraire portfolio. | choice, valuation | for log utility on a finite complete market, the prices deflated by the optimal wealth are martingales in one period (`Market.IsPricingMeasure.integral_div_logOptimal_mul`); the Kelly bet as its two-outcome case (`kelly_statePrices`) |
| The superhedging price is a coherent risk measure, represented by the pricing measures. | valuation, risk | coherence and the representation (`superhedgingPrice_isLUB`) on a finite space |
| A premium principle is a risk-loaded price; the Esscher premium is a price under the Esscher measure. | valuation, risk | the Esscher tilt is a pricing measure of the insured market, under which the loss is worth its Esscher premium (`price_insuredMarket_tilted`) |

Convex duality is the method behind all of them, and
[`mathematical-architecture.md`](mathematical-architecture.md) follows it (Pillar I) through the
library.

## Kinds of randomness: the model families

A model family is a kind of randomness, with its own state variables and its own sources of
tractability. It is a second axis, not a question, because one family serves several questions.
A default model prices a credit default swap (valuation) and gives the loss distribution of a
credit portfolio (risk). A model of claims gives premiums and ruin probabilities.

| family | what is random |
|---|---|
| trees | finitely many states, binomial paths |
| Gaussian diffusions | Black–Scholes, Bachelier, Brownian markets |
| volatility | local, stochastic and rough volatility; the smile |
| jumps | compound Poisson and Lévy |
| term structures | interest rates, FX, futures and commodity forward curves |
| default | structural and intensity models of default |
| mortality and claims | lifetimes, claim counts and sizes |
| market mechanisms | order books, automated market makers, lending protocols |
| model-free | nothing: static replication and robust bounds |

Insurance, decentralized finance and market microstructure are families, not separate subjects.
A life annuity is valued, a ruin probability measures risk, and a Kyle equilibrium is a choice
under asymmetric information. Each family has a colour on the tree and a page on the
documentation site that gathers it across the three questions.

## The tools

- **Probability:**
  - discrete-time martingales and optimal stopping;
  - continuous martingales;
  - Brownian calculus (the Itô integral and formula, Girsanov, martingale representation,
    Feynman–Kac, stochastic differential equations);
  - jumps;
  - Gaussian analysis and laws;
  - dependence and copulas;
  - convex analysis.
- **Statistics:** estimation, empirical distribution functions, performance statistics,
  backtesting and credibility. Every question consumes estimates, so statistics is a tool rather
  than a question.

Each concept has one home. Girsanov's theorem lives in Brownian calculus, and the exponential tilt
of a Gaussian law is its marginal at a single time. Feynman–Kac lives in Brownian calculus, and
the heat kernel is its constant-coefficient case.

## Finding things

- A module's directory is its place: `Contracts/` and `Pricing/` hold the trunk and arbitrage
  theory, `Models/` the model families, `Choice/` and `Risk/` their limbs, `Probability/` the
  tools. `docs/taxonomy.toml` assigns every module to one cell; where a directory does not yet
  match (statistics modules under `Choice/Performance`, the static no-arbitrage theory under
  `Models/ModelFree`), the taxonomy says where it belongs.
- A [blueprint](glossary.md#blueprint) node is a landmark (a definition or theorem with a textbook name, at the generality
  proved), a bridge between limbs, a market statement for a model family, or a definition several
  limbs share. A frontier node is stated and not proved; a frontier node with a `lean` field is
  stated in Lean in `MathFinFrontier/`, closed by `sorry`. The field's open problems are catalogued
  in [`research-problems/`](research-problems/README.md).
- An issue carries the cell and the family of the blueprint node it advances (`area:`,
  `family:`), written by the blueprint-sync bot.
- The [documentation site](https://formal-applied-math.github.io/formal-mathfin/) has a page per
  cell, and the program tree draws the structure at its measured height.
