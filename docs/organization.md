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

## Three dualities of one set of measures

| primal set | what the duality says | in the library |
|---|---|---|
| the gains of self-financing strategies | **valuation**: no arbitrage iff a pricing measure exists (FTAP); the superhedging price is the supremum of prices over pricing measures | the FTAP in its discrete forms, for bare price processes; joined to `Market` by one adapter (`DiscreteMarket`) |
| the positions a risk measure accepts | **risk**: a coherent risk measure is the worst expected loss over a set of measures | on a finite state space (`coherentRisk_isLUB`); expected shortfall's dual on any space |
| the positions an investor prefers | **choice**: at an optimum, marginal utility is a state-price density, so the investor's optimum defines a pricing measure | for a two-outcome bet (Kelly); the finite-state case is in review |

The three questions (what a position is worth, how dangerous it is, whether to hold it) are the
limbs; the dualities are where they meet, and the library calls those theorems **joints**. Not
everything should be forced through a market: a value at risk is a quantile of a law, a Sharpe
ratio is a ratio of moments, a Markowitz frontier is a quadratic programme. Such cells declare
that they stand alone and say how their object reads in a market.

## How connected it is today

The library measures connection from statements only (`tools/verify/chain_reach.py`, reported on
every build): a theorem is near the trunk when its statement mentions an object that some proved
statement ties to the trunk. Renaming, moving or relabelling changes nothing; only a theorem does.
On 2026-11-08:

- half of the 3,471 finance theorems (R3 49.7%) are within three statement hops of the trunk;
- **one** of nine model families is proved to be a market with a pricing measure (the binomial
  tree): Black–Scholes, jumps, rates, credit and the rest value contracts under a hypothesis
  bundle, not yet as markets;
- most of choice (58% of its theorems) and a quarter of risk are not connected at all.

The missing links are stated as Lean theorems in the connector library `MathFinFrontier`, each
carried by an issue: a **socket** proves a model family is a market, a **joint** joins two limbs,
a **summit** gives a tower one capstone. The program tree draws each as a phantom between the
parts it would join.

## The joints

| joint | limbs | status |
|---|---|---|
| Marginal utility at the optimum is a state-price density. | choice, valuation | finite-state case in review (#473) |
| CAPM and the Hansen–Jagannathan bound follow from the stochastic discount factor. | choice, valuation | in review (#475) |
| The log-optimal (Kelly) portfolio is the numéraire portfolio. | choice, valuation | proved for a two-outcome bet (`KellyNumeraire`) |
| The superhedging price is a coherent risk measure, represented by the pricing measures. | valuation, risk | coherence and the representation (`superhedgingPrice_isLUB`) proved on a finite space |
| A premium principle is a risk-loaded price; the Esscher premium is a price under the Esscher measure. | valuation, risk | frontier |

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
  `Models/ModelFree`), the taxonomy says where it belongs and the module moves are scheduled.
- A blueprint node is a landmark (a definition or theorem with a textbook name, at the generality
  proved), a joint, a socket, or a definition several limbs share. A frontier node is stated and
  not proved; a frontier node with a `lean` field is a connector, stated in `MathFinFrontier/`.
- An issue carries the cell and the family of the blueprint node it advances (`area:`,
  `family:`), written by the blueprint-sync bot.
- The [documentation site](https://formal-applied-math.github.io/formal-mathfin/) has a page per
  cell, and the program tree draws the structure at its measured height.
