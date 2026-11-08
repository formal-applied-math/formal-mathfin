# How the library is organized

MathFin formalizes financial mathematics as one structure: one object, three questions asked of
it, the theorems that join the questions, the kinds of randomness the questions are asked about,
and the tools underneath. The module tree, the blueprint, the issue labels, the documentation
site and the program tree all show this one structure. All of them are generated from or
checked against [`taxonomy.toml`](taxonomy.toml). The reasons for each choice are in the design,
[`specs/2026-11-08-organization-design.md`](specs/2026-11-08-organization-design.md).

## The object: positions in a market

A **position** is a random payoff, possibly paid at several dates, on a filtered probability
space. The library writes positions in a payoff language (`Contract`) that mentions no measure and
no model. A **market** (`Market`) names the positions that trade and a numéraire. A
**self-financing strategy** in the market has gains, and those gains are positions as well.
`Contract.value Q D X c` is the expectation of a deflated position under a measure `Q`. It is not
yet a price: it becomes one when `Q` is a pricing measure.

This is the trunk. Every question below is asked about positions, and two of them (valuation, and
choice in a market) are asked about the gains of strategies.

## Three questions

| | question | the functional | characteristic theorem |
|---|---|---|---|
| **Valuation** | What is the position worth? | linear on what can be replicated, sublinear (the superhedging price) above it | the fundamental theorems of asset pricing; the superhedging duality |
| **Choice** | Should one hold it, and how much? | concave: expected utility | von Neumann–Morgenstern; the first-order condition of optimal investment |
| **Risk** | How dangerous is it? | convex, monotone, cash-invariant: a risk measure | the robust representation by a set of measures |

Inside each question the order is generality. The general theorem comes first. Its instances in a
model come next, and the formula for a product comes last. On the tree, height is this
generality.

Not every result travels through the pricing functional, and none should be forced to. A
value at risk is a quantile of a law. A Sharpe ratio is a ratio of moments. A Markowitz frontier
is a quadratic programme. Each sits in the question it answers.

## Where the questions meet

The three functionals are dual to each other, and the theorems that say so are the field's
deepest. The library calls them joints. A joint belongs to the question whose object it
characterizes, and the tree draws it in the fork between the two limbs.

| joint | questions | in the library |
|---|---|---|
| Marginal utility at the optimum is a state-price density. | choice, valuation | frontier |
| CAPM and the Hansen–Jagannathan bound follow from the stochastic discount factor. | choice, valuation | frontier |
| The log-optimal (Kelly) portfolio is the numéraire portfolio. | choice, valuation | proved for a two-outcome bet (`Choice/Performance/KellyNumeraire`) |
| The superhedging price is a coherent risk measure, represented by the pricing measures. | valuation, risk | proved on a finite probability space; the equality with the supremum awaits Minkowski–Weyl |
| A premium principle is a risk-loaded price; the Esscher premium is a price under the Esscher measure. | valuation, risk | frontier |

Convex duality is the method behind all of them, and [`mathematical-architecture.md`](mathematical-architecture.md)
follows it (Pillar I) through the library.

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

- A module's directory is its place: `Pricing/` and `Models/` are valuation, `Choice/` is
  choice, `Risk/` is risk, and `Probability/` and `Statistics/` are the tools. A file's family
  appears in its module path (`Models/Credit`, `Risk/Credit`).
- A blueprint node is a landmark: a definition or theorem with a textbook name, a joint, or a
  definition several questions share. Every question and every tool has its characteristic
  theorem on the blueprint, proved or on the frontier.
- An issue carries the cell and the family of the blueprint node it advances (`area:`,
  `family:`).
- The [documentation site](https://formal-applied-math.github.io/formal-mathfin/) has a page per
  cell and per family, and the program tree draws the whole structure.
