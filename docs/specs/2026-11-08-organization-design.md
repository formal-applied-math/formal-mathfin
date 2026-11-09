# How the library organizes financial mathematics

Status: design, 2026-11-08. It amends [`2026-11-07-one-trunk-design.md`](2026-11-07-one-trunk-design.md):
its invariants I1, I2 and I5 stand for valuation; I3 (every limb hangs on a pricing hinge) and I4
(the module layout) are replaced by §3 and §4 here. The tree map follows from §3. Its drawing is
the last projection, not the source.

## 0. The question and the answer

How should the library organize financial mathematics? The organization should hold the same way
in every place the library shows itself: modules, blueprint, issues, docs, corpus and tree. Each
of those places should be generated from one statement of it. A financial mathematician with no
context on the repo should recognize the field in it.

The answer, in one paragraph. The common object is a **position**: a random payoff in a filtered
probability space, with the **market** that trades some positions and the **gains** of strategies
in it. That is the trunk. The field asks three questions of a position, and each question is a
functional of a different shape:
- **what it is worth** is a linear functional, through pricing measures;
- **whether to hold it** is a concave functional, through expected utility;
- **how dangerous it is** is a convex functional, through risk measures.

Those are the three limbs: **valuation, choice and risk**. Classical duality theorems join them:
- marginal utility is a state-price density;
- the superhedging price is a coherent risk measure, represented by the pricing measures;
- the entropic risk measure is the certainty equivalent of exponential utility.

These joints are the interesting part of the picture. Across the three questions runs a second
axis, the **model families**: trees, Gaussian diffusions, volatility models, jumps, term
structures, default, mortality and claims, market mechanisms, and model-free. One family serves
several questions. A default model prices a CDS and gives a credit portfolio's loss distribution.
The **roots** are the tools: probability, stochastic calculus, Gaussian analysis, dependence,
convex analysis and statistics.

## 1. Where the library stands

### Ten taxonomies

The library organizes itself in ten places, and each cuts the field differently.

| where | cut | example of disagreement |
|---|---|---|
| `MathFin/` directories | by object | credit sits in `Models/Credit`, `Risk/Credit` and `Markets/DeFi` (Aave liquidation as KMV default) |
| `docs_site.SECTIONS` | by directory, with roots, trunk and limbs | `Risk` is a "limb" of "contracts and pricing" |
| `program_tree.SECTION_AREA`, `AREA_PLACE` | directory → area label | `Choice` → `portfolio`; `Markets` → `execution` |
| `program_tree.DIR_PLACE` | directory → place on the tree | `Probability.Dependence` → `risk/dependence` |
| `tree_map.toml` | roots, one pricing trunk, five limbs | choice, risk and insurance drawn as limbs of the pricing functional |
| `tree.js` `AREA_TXT` | display names | a copy of the area list |
| issue labels `area:*` (17) | by practice area | `fx` and `futures` apart, but no label for choice or statistics |
| `blueprint_frontier.toml` `area` | the issue labels | inherits the gaps |
| `benchmarks/*.json` (28 files), `Domain` enum (11) | by course or topic; the enum by process type | all of finance is one `Domain` value |
| `docs/landmarks.toml` (14) beside the blueprint | headline results | two lists of the library's main results |

`docs/mathematical-architecture.md` adds an eleventh cut, by method: four pillars (convex
duality, stochastic calculus, the PDE duality, exponential families). It is right, but it
describes how theorems are proved, not where they sit.

The one-trunk spec saw part of this. Its §2 says "`valueAtRisk` is a quantile of a law; the
Sharpe ratio is a ratio of moments; `portfolioVarN` is a quadratic form", and that such objects
should not be forced through the pricing functional. The tree map then draws them as limbs of
that functional anyway. A reader takes the picture at its word.

### The blueprint is a delivery log

Nodes were tagged as phases shipped them, so they mix landmarks with proof-engineering waypoints:
- "Itô formula, L² (C³ bounded — Summit A)";
- "BSCallHyp from a Brownian model";
- "GBM coefficient matching (algebraic)".

Meanwhile results the library has proved for months are not nodes:
- the FTAP in six forms (`Pricing/FTAP/`);
- Arrow–Debreu state prices and the pricing kernel;
- the superhedging duality;
- von Neumann–Morgenstern expected utility (`Choice/Utility`);
- the KMV structural default probability (`Models/Credit/KMVMertonStructural`).

One concept appears as several unlinked nodes:
- Girsanov four times: Esscher tilt, static call, Brownian characterisation, the EMM frontier;
- Black–Scholes as three objects: `def:gbm`, the `BSCallHyp` bundle, `BlackScholes.market`;
- Feynman–Kac twice: a heat kernel and an "expectation-form Itô".

The landmark survey of 2026-11-08 (§5, appendix) counts the gap per cell.

### Measured on the tree (main at `23f88739`)

- 267 limb entries, of which 17 rest on a trunk node.
- 73 limb nodes, of which 5 use one.
- 224 corpus entries off the map, and 10 islands.

None of these numbers moved through phases 0–2c. The trunk grew only by its own new entries.

## 2. The organization of the field

### The trunk: positions, markets, strategies

A **position** is a random payoff, possibly dated, over `(Ω, 𝓕, P)` with a filtration. The
library writes positions in the payoff language `Contract`, which has no measure and no model. A
**market** names the traded positions (assets) and a numéraire. A **self-financing strategy** has
gains, and the gains are positions too. These are the objects all three questions are asked about:
- valuation asks which pricing measures make the gains fair;
- choice asks which gains to pick;
- risk asks how much capital makes a position acceptable, possibly after trading.

`Contract.value Q D X c` is the generic expectation of a deflated position. It belongs to the trunk.
`Market.IsPricingMeasure` and `Market.price` belong to valuation.

### Three questions, three functionals

| limb | question | shape | characteristic theorem | the library's object |
|---|---|---|---|---|
| valuation | what is it worth? | linear on the attainable, sublinear above | FTAP I and II; superhedging duality | `Market.price`, `IsPricingMeasure` |
| choice | whether, and how much, to hold it? | concave | von Neumann–Morgenstern; the optimal-investment first-order condition | `expectedUtility`, Markowitz, CAPM |
| risk | how dangerous is it? | convex, monotone, cash-invariant | the robust representation (Artzner–Delbaen–Eber–Heath, Föllmer–Schied) | `IsCoherentRiskMeasure`, `valueAtRisk`, `expectedShortfall` |

Within each limb the order is generality. The general theorem sits at the base: FTAP; vNM and
risk aversion; acceptance sets and the representation. The model instances sit above it, and the
product formulas are at the tips.

### The joints

The three functionals are dual to each other, and the field's best theorems say so. A joint is a
theorem whose statement involves two limbs. It belongs to the limb whose object it characterizes,
and the tree draws it in the fork.

| joint | limbs | state in the library |
|---|---|---|
| marginal utility at the optimum is a state-price density | choice–valuation | frontier `thm:utility-state-price-density` |
| CAPM and Hansen–Jagannathan from the stochastic discount factor | choice–valuation | frontier `thm:sdf-capm-hansen-jagannathan` |
| the log-optimal portfolio is the numéraire portfolio | choice–valuation | frontier `thm:log-optimal-numeraire`; `Choice/Performance/KellyNumeraire` proves a part |
| the superhedging price is a coherent risk measure, represented by the pricing measures | valuation–risk | proved on a finite space (#470); equality needs Minkowski–Weyl (#456) |
| the entropic risk measure is the certainty equivalent of exponential utility | choice–risk | to survey |
| a premium principle is a risk-loaded price (Esscher premium = price under the Esscher measure) | valuation–risk | frontier `thm:premium-is-price` |
| utility indifference pricing | all three | absent |

The method behind every joint is convex duality. That is Pillar I of
`mathematical-architecture.md`, which this design keeps as the account of *why* the joints hold.

### The second axis: model families

A family is a kind of randomness with its own state variables and tractability. It is not a
question.

| family | state | valuation | choice | risk |
|---|---|---|---|---|
| one-period and trees | finite `Ω`, binomial paths | FTAP on finite `Ω`, CRR, American by Snell | — | — |
| Gaussian diffusions | Black–Scholes, Bachelier | formula, PDE, Greeks, hedging, exotics, American put | Merton portfolio | Gaussian VaR/ES |
| volatility | local, stochastic, rough; the smile | Dupire, Heston, SABR, SVI, model-free bounds | — | — |
| jumps and Lévy | compound Poisson, exponential Lévy | Merton, Kou, Esscher EMM | — | compound-Poisson CVaR |
| term structures | rates, FX, futures and commodities (forward curves) | bonds, affine, HJM, forward measure, LMM, Black-76, parity, duration and immunization | — | — |
| default | structural, intensity | Merton/KMV, Black–Cox, CDS, CVA | — | Vasicek, CreditMetrics, CreditRisk+, tranches |
| mortality and claims | lifetimes, claim counts | life annuities, reserves, Thiele | — | ruin, Panjer |
| market mechanisms | order books, AMMs, lending | LP positions, money-market accounts | Kyle, Glosten–Milgrom, market making, execution | liquidation |
| model-free | none | Carr–Madan, variance swaps, smile no-arbitrage | — | worst-case risk |

Insurance, DeFi and microstructure are families, not limbs. Their results answer one of the three
questions, and the family keeps them findable: one hue on the tree, one family page in the docs,
one `family:` label on issues.

### The roots

- Probability:
  - discrete time (martingales, Snell envelope, path measures, Markov chains);
  - continuous martingales;
  - Brownian calculus (Itô, Girsanov, representation, Feynman–Kac, SDEs);
  - jumps;
  - Gaussian analysis and laws (Φ, quantiles, the exponential tilt, the heat kernel);
  - dependence (copulas, Sklar).
- Analysis: convexity and separation, optimization.
- **Statistics**, a new root: estimation, empirical laws (Glivenko–Cantelli), quantile
  convergence, performance statistics (Sharpe ratio, drawdown), backtesting (purged
  cross-validation, label uniqueness, fractional differencing), credibility. Every question
  consumes estimates, so statistics is a tool and not a question.

Each concept has one home. Girsanov lives in Brownian calculus, and the Gaussian exponential tilt
is its time-`T` marginal. Feynman–Kac lives in Brownian calculus, and the heat kernel is its
constant-coefficient case.

### The hard cases, decided

| result | cell | why |
|---|---|---|
| CDS, CVA | valuation · default | a price |
| Vasicek large pool, one-factor copula, CreditRisk+ | risk · default | a loss distribution |
| Aave liquidation as a KMV default probability | risk · mechanisms, using default | a default probability |
| Uniswap v3 position ≤ covered call | valuation · mechanisms | a price bound |
| Kyle, Glosten–Milgrom | choice · mechanisms | equilibrium under asymmetric information |
| Almgren–Chriss, market-making Riccati | choice · mechanisms | stochastic control |
| propagator no-arbitrage | valuation · mechanisms | absence of price manipulation is an arbitrage statement |
| life annuity EPV, Thiele | valuation · mortality | a value of a cash-flow stream |
| standard-deviation premium principle | risk · mortality and claims | a risk-loaded functional of a loss |
| Cramér–Lundberg, Lundberg bound | risk · claims | collective risk theory |
| Bühlmann credibility | statistics | an estimator |
| Sharpe ratio, drawdown, purged CV | statistics | statistics of returns |
| Kelly | choice · growth | log-utility optimum |
| covered interest parity | valuation · term structures | rests on the pricing functional, not on Black–Scholes |
| duration, immunization, key-rate durations | valuation · term structures | sensitivities of a price, as the Greeks are; immunization is hedging |
| completeness and uniqueness on the Brownian filtration | valuation · Gaussian diffusions | instances of FTAP II, not the trunk |

## 3. Modules: the directory is the cell

```
MathFin/
  Init.lean
  Probability/   roots: Discrete/, Martingales/, Brownian/, Jumps/, Gaussian/, Laws/,
                 Dependence/, Analysis/ (gains Convexity/: the separation root from Pricing/Duality)
  Statistics/    root: Estimation/, Empirical/, Performance/, Backtesting/, Credibility/
  Contracts/     trunk: the payoff language (unchanged)
  Market/        trunk: Market, strategies and gains, numéraire, Contract.value
  Pricing/       valuation, general: FTAP/, StatePrices, Superhedging, Completeness, Replication
  Models/        valuation by family: Binomial/, BlackScholes/, Bachelier/, LocalVol/, StochVol/,
                 ModelFree/, Jumps/, Rates/, Forwards/, Credit/, Insurance/, Mechanisms/
  Choice/        Preferences/, Portfolio/, Equilibrium/, Dynamic/, Trading/
  Risk/          Measures/, LawInvariant/, Aggregation/, Credit/, Ruin/, Exposure/, Premium/
```

Moves from the current layout:
- `Insurance/` dissolves:
  - survival, EPV and reserves go to `Models/Insurance/`;
  - premium principles go to `Risk/Premium/`;
  - ruin goes to `Risk/Ruin/` when it is proved.
- `Markets/` dissolves:
  - AMMs and lending go to `Models/Mechanisms/`;
  - microstructure and execution go to `Choice/Trading/`;
  - liquidation default goes to `Risk/Credit/`.
- `Choice/Performance/` moves by content:
  - ratios, drawdown, PurgedCV, LabelUniqueness and FracDiff go to `Statistics/`;
  - Kelly and KellyNumeraire go to `Choice/Dynamic/`.
- `Probability/Laws/Estimation` and `QuantileConvergence` go to `Statistics/`.
- `Pricing/Market` and `Pricing/Numeraire`, with the strategy and gains files, go to `Market/`.
  `Contract.value` (`Pricing/Value`) goes to `Market/`.
- `Pricing/Duality/` goes to `Probability/Analysis/Convexity/`.
- `Risk/` and `Choice/` split into the subdirectories above.

Imports point one way:
- roots → trunk → limbs;
- `Models/` imports `Pricing/`;
- a limb imports another limb only for a joint, or for a family's model definition. For example,
  `Choice/Dynamic` imports the Black–Scholes market for Merton's portfolio.

`tests/test_architecture.py` checks the direction from the taxonomy.

Module paths change again before v2.0.0. That is the release that already changes them (one-trunk
§9.3), so the move costs one rename list in the release notes, not a second major version.

## 4. One source, every projection

`docs/taxonomy.toml` states §2 once:
- the cells (roots, trunk, limbs with their subcells);
- the families and their hues;
- for each cell, its title, a one-line blurb, its directories, its JEL/MSC codes, its issue label
  and its characteristic landmarks (Lean names).

Everything else is generated from it, or checked against it.

| projection | today | from the taxonomy |
|---|---|---|
| modules | directories chosen per PR | `test_taxonomy`: every directory belongs to exactly one cell |
| blueprint | tags as phases shipped | nodes are the cells' landmarks and the joints (§5); every cell has its characteristic node, proved or frontier |
| frontier `area` | issue-label names | a cell key, checked |
| issues | 17 `area:*` labels set by hand | `area:<cell>` and `family:<family>`, derived from the node named in the issue's `Blueprint:` line and checked by `blueprint_issues` |
| docs site | `SECTIONS` dict | limb pages (question, characteristic theorem, joints, families) and family pages across limbs; the landmarks page reads the blueprint's landmark nodes |
| README, status, coverage | prose per doc | one "how the library is organized" section from `docs/organization.md`; coverage by cell |
| corpus / HF dataset | file grouping, `Domain` | each entry gets `cell` and `family`, from its nearest node or its cited module, exported beside `subjects` |
| tree | `tree_map.toml`, `DIR_PLACE`, `AREA_PLACE`, `SECTION_AREA`, `AREA_TXT` | parts, branches, places and hues read from the taxonomy; `tree_map.toml` keeps only per-node exceptions, each with a reason |

`docs/organization.md` is the readable form of §2: the trunk, the three questions, the joints,
the families, the roots and the picture. Two documents then point to it:
- the README's "How the library is organized";
- `mathematical-architecture.md`, whose pillars become the methods the joints are proved with.

`landmarks.toml` keeps its prose. Each entry names a blueprint label, and `test_values` checks
that it is a node.

## 5. The blueprint as a map of landmarks

A node is one of:
1. a **landmark**: a definition or theorem with a textbook name, stated at the generality the
   library proves;
2. a **joint**: a theorem whose statement involves two limbs;
3. a **shared definition** that the landmarks of more than one cell use (`Market`, `Contract`,
   `IsPricingMeasure`, `IsCoherentRiskMeasure`, `expectedUtility`).

A waypoint is not a node. That covers a hypothesis bundle, a proof step, a special case of a
landmark that is already a node, or a bridge between two encodings. Its corpus entries still hang
on the nearest landmark. Titles are textbook names. Any narrowing is said in the statement prose,
never in the title. The curation follows the landmark survey: tag what is proved, fold waypoints
in, rename, and give every cell its characteristic node.

## 6. The tree

- The roots are the probability, analysis and statistics roots.
- The trunk is the market: positions, markets, strategies and gains.
- Three limbs: valuation in the middle, choice and risk on either side.
- Each limb's branches are its subcells. The joints sit in the forks between the limbs.
- A node is coloured by its family, the same hue in every limb. Credit in valuation and credit in
  risk read as one family seen by two questions.
- Height is generality: general theorems near the fork, instances above, product formulas at the
  tips.
- The legend lists the families. There are no captions over the crown.

## 7. Measurements

The counts that say whether the organization holds:
- `entries_through_trunk`, for valuation entries (the one-trunk counts, I5);
- per limb, the share of nodes resting on that limb's characteristic theorem;
- `landmarks_not_nodes`: proved landmarks listed in the taxonomy and not tagged;
- `cells_without_characteristic_node`;
- `joints_proved`, out of the joints listed;
- off-map entries and islands.

The first three are ratchets.

## 8. Execution

Each step is one PR, in this order:

1. **Taxonomy (tools only).**
   - Add `docs/taxonomy.toml` and `docs/organization.md`.
   - `program_tree`, `docs_site`, `tree.js` and `blueprint_issues` read the taxonomy, and their
     own constants go.
   - Add `tests/test_taxonomy.py`.
   - The tree is redrawn on the new cut.
2. **Module moves.** Scripted as in phase 1, content-free. One CI build and a ledger sweep.
3. **Blueprint curation.**
   - Edit `Blueprint.lean` tags and titles, from the survey.
   - Assign frontier `area`s to cells.
   - Point `landmarks.toml` at labels.
   - Run one CI export.
4. **Issues.** Create the label set from the taxonomy, relabel open issues from their nodes, and
   retire the old `area:*` labels.
5. **Docs.** Write the README section and reframe `mathematical-architecture.md`. Add the site's
   limb and family pages. Organize `status.md` and `coverage.md` by cell.

The one-trunk phases continue inside the valuation limb: Black–Scholes uniqueness, prices defined
as prices, the rates, credit and jumps limbs. For choice and risk the work becomes their
characteristic theorems and the joints, replacing the "hinge to pricing" framing of one-trunk §5.
