# The library as one structure: sockets, joints and connectors

Status: adopted 2026-11-08. It replaces the framing of
[`2026-11-08-organization-design.md`](2026-11-08-organization-design.md) ("one object, three
questions") and its metrics. From that design it keeps the taxonomy as the layer that displays the
structure (`docs/taxonomy.toml`, the issue labels, the families as a second axis, the blueprint
as landmarks), with cells defined by the object their statements are over. It amends one-trunk
([`2026-11-07-one-trunk-design.md`](2026-11-07-one-trunk-design.md)), whose phases continue as the
sockets below.

The analysis (§§0–6) was written by an agent given the code, the declaration index and the
maintainer's question, who read the earlier designs only after forming its own view. The
decisions and the corrections are the maintainer's.

## Decisions

1. **The bones change, not the labels.** Each model family gets a *socket*: a theorem that its
   model is a `Market` with a proved pricing measure, from which its formulas are prices
   (`price_eq_of_map_observation_eq`). Each pair of limbs gets *joints*: theorems whose statements
   mention both. The FTAP is stated over `Market`. Choice is restated over measures. Towers get a
   summit. Where an object is defined several times (no-arbitrage, equivalent martingale
   measures, finite laws), one survives and the rest become its instances (CLAUDE.md: no parallel
   objects, no aliases).
2. **Connectors are Lean.** A missing link is a theorem in the `MathFinFrontier` library, closed
   by `sorry`, named by one frontier node (`lean = "MathFinFrontier.…"`) carried by an open issue.
   `MathFin` never imports it and stays sorry-free; the build checks that every connector
   elaborates. Delivering one moves it into `MathFin/` with a proof.
3. **The measure is chain reach** (`tools/verify/chain_reach.py`, §4), computed from statements
   only, reported on every build with each connector's gain. Alongside it: sockets (families with
   a proved pricing measure), joint span (theorems per pair of limbs) and the blueprint's islands.
4. **The tree shows the measure.** Height is the measured distance to the trunk; disconnected
   clusters float as islands, labelled with a declared reason or flagged; towers are single
   nodes; open issues are dots, and a connector is a phantom dot in the gap it would close, with
   dashed edges to both ends, sized by its gain.
5. **Standalone is declared.** A cell that legitimately stands alone (a law functional, an
   algebraic certificate, a deterministic mechanism, a tool, a convex programme) says so with its
   reason and the socket that reads it in a market; the count is ratcheted.

## Corrections to the numbers below

- The agent's tokenizer missed methods printed in dot notation (`(market …).IsPricingMeasure T
  Q`, `M.price Q c`). With them resolved, on main at 23f88739: **R3 49.7%, R2 27.6%** of 3,471
  finance theorems (guarded); sockets **1 of 9** (trees); joint span choice+risk 15,
  choice+valuation 6, risk+valuation 18. The spine is the taxonomy's `market` and
  `valuation/general` cells; the tools are `probability/*` and `statistics`.
- The blueprint over landmarks alone has **26 islands**; the trunk is split among them (`Market`
  and the pricing measure in one, the FTAP in another).

## 0. The thesis in one paragraph

The field has one economic object, a **price system on state-contingent payoffs**, and its deep theorems
are the three ways a *set of positive linear functionals* (state prices, pricing measures, SDFs) is
dual to a *set of payoffs*: the gains cone (FTAP, superhedging), the acceptance set (robust representation
of risk measures), the preference's upper-contour set (marginal utility = state price). The library today
has the *trunk* of this (`Market`, `Contract`, `IsPricingMeasure`, ~400 declarations, 6% of the library)
and an enormous mass of *satellite calculus* (Black-Scholes formulas and Greeks, an American-put tower, an
SVI certificate tower, Brownian calculus) that touches the trunk, if at all, through one hypothesis
bundle per family. The previous design relabelled the satellites. It did not change what a satellite's
theorems say. The fix has to be in the statements: every family gets a **socket** (a theorem that its
model is a `Market` with proved pricing measure(s)), every limb gets a **joint** (a theorem whose
statement mentions both its own central object and the trunk's), and what truly stands alone says so in a
declaration the tests read. Phantom connectors are *Lean statements that elaborate* in a never-imported
`MathFinFrontier` library, so a phantom link cannot be vague and cannot point at a declaration that
does not exist.

---------------------------------------------------------------------------------------------------

## 1. How the field is organized

### 1.1 The spine (Föllmer-Schied, Delbaen-Schachermayer, Duffie, Cochrane)

Every standard text is built on the same three things, in this order.

1. **Payoffs and strategies.** A space `L` of positions `X : Ω → ℝ` on `(Ω, 𝓕, (𝓕_t), P)`; traded
   assets `S`, a numéraire `N`; gains of self-financing strategies form a cone `K ⊂ L`
   (FS ch. 1, 5; DS "Mathematics of Arbitrage").
2. **The dual object.** Positive functionals on `L` normalised on the numéraire: probability measures
   `Q ≪ P`, equivalently stochastic discount factors `m = (dQ/dP)·(N₀/N_T)` (Cochrane: "one equation,
   `p = E[mx]`"). Everything is asked of the pair `(L, 𝒬)` where `𝒬 = {Q : deflated S are Q-martingales}`.
3. **Three primal sets, one duality.** Each primal convex set has a dual set of measures, and the
   bipolar/separation theorem is the proof every time:

| primal set | dual set | theorem | where (FS / other) |
|---|---|---|---|
| gains cone `K` | `𝒬` (martingale measures) | FTAP: `K ∩ L₊ = {0}` iff `𝒬^e ≠ ∅`; superhedging price `= sup_𝒬 E_Q[X]` | FS 1.6, 5.4; DMW |
| acceptance set `𝒜 = {ρ ≤ 0}` | `{Q : α(Q) < ∞}` | robust representation `ρ(X) = sup_Q (E_Q[-X] - α(Q))` | FS 4.2-4.4; Delbaen |
| upper-contour set of `u` | the state-price density at the optimum | `u'(X*) = λ·dQ/dP·(N₀/N_T)`; Kramkov-Schachermayer | FS 3.3; Cochrane 1; Duffie |

Two facts make this a *spine* and not just a table. (a) The three sets live in the same space `L`, so
a risk measure applied to a hedged position (`ρ(X - gains)`) is a single expression. (b) The superhedging
price is itself a coherent risk measure (FS Thm 4.15 and the discussion before it), the one place where the
valuation and risk limbs are literally the same functional, and the Kelly/log-optimal portfolio is the
numéraire portfolio (Long 1990), the one place where the choice and valuation limbs are the same object.

### 1.2 What sits on the spine

* **Models.** A model is a *specification of the filtered law of `S`* that makes `Market` concrete:
  trees (CRR), Gaussian diffusions (Bachelier, Black-Scholes, Vasicek), local/stochastic/rough volatility,
  jumps (Merton, Lévy), term structure (HJM, short rate, LMM), default (structural: Merton/KMV/Black-Cox;
  reduced-form: hazard, Cox), mortality (a survival law is a default law). Björk/Shreve/Brigo-Mercurio
  organize *by model*; Hull and the desks organize *by instrument and asset class*. Both are legitimate
  second axes. A model's output is a market plus a dictionary (contract → price/Greeks/PDE) and the proof
  that its `Q` prices the market. It is never a new notion of price.
* **Static no-arbitrage** (Breeden-Litzenberger, Carr-Madan, Roper, Davis-Hobson, Gatheral SVI
  butterfly-freedom). This is usually filed as "model-free" or "smile"; mathematically it is the *static
  FTAP on the vector space spanned by calls*: a call-price function is arbitrage-free iff it is the
  marginal-call function of a martingale. It belongs next to the FTAP, not next to models.
* **Preferences and portfolios.** Utility theory (VNM, risk aversion, certainty equivalents), optimal
  investment (Merton, Kramkov-Schachermayer), mean-variance (Markowitz, tangent, two-fund, CAPM as
  equilibrium), growth-optimal/Kelly. Cochrane's view collapses CAPM, APT and mean-variance into
  statements about the SDF (Hansen-Jagannathan bound `|E R^e|/σ(R^e) ≤ σ(m)/E[m]`). Where reasonable
  people differ: asset managers file "portfolio theory + performance measurement" as a subject of its own
  with only a distant link to arbitrage theory (Markowitz did not assume a market in the FS sense).
* **Risk** has two legitimate anchors, which the field keeps distinct: the *axiomatic* anchor
  (monetary/convex/coherent risk measures, acceptance sets, duality: FS ch. 4) and the *statistical*
  anchor (the loss distribution, VaR/ES as functionals of a law, dependence/copulas, EVT, aggregation,
  credit portfolio models: McNeil-Frey-Embrechts). VaR "is a quantile of a law" and is allowed to stand
  there; its link to the spine is only the loss of a position, `loss(c) = price paid - discounted payoff`.
* **Actuarial** (survival, annuities, premium principles, ruin) shares objects with credit: a lifetime
  `τ` with hazard `λ` is a default time, an annuity is a CDS premium leg with another name, an
  Esscher premium is an expectation under the Esscher measure, i.e. a price.
* **Market mechanisms** (Kyle, Glosten-Milgrom, AMMs, lending protocols). The field files these under
  microstructure/market design. Their interface with the spine is "the price process the mechanism
  generates is a martingale of the market maker's filtration / is a replicable payoff".

### 1.3 Where reasonable people organize it differently

1. *By instrument* (equity/rates/credit/FX/commodity), as the desks and Hull do. Cost: it hides that
   Black-Scholes, Bachelier, Black-76 and Vasicek caplets are one computation. Benefit: it is how
   every practitioner searches.
2. *By technique* (martingale vs PDE vs transform vs Monte Carlo; Shreve). Cost: spreads one model across
   chapters. The library already has this as `mathematical-architecture.md`'s four pillars; it is a
   method axis, not a place.
3. *Preference-first* (Cochrane, Duffie dynamic asset pricing) vs *arbitrage-first* (FS, Björk). I choose
   arbitrage-first for the trunk because the library's definitions (`Market`, `IsPricingMeasure`) are
   arbitrage-first, but I keep preference as a limb with its own central object and mandatory joints.
4. Whether *risk* is a limb of valuation (superhedging price is a risk measure) or a sibling (QRM).
   I keep it a sibling with a mandatory joint.

The unifying device I would adopt: **a mathematical cell is named by the object its statements are
over, and carries a declared relation to the spine**: `instance-of` (a family of markets), `dual-to`
(a limb), `consumes` (a tool), `standalone` (with reason and socket).

---------------------------------------------------------------------------------------------------

## 2. What the library actually has (measured from the index, not from docs)

### 2.1 Mass

Public+private declarations by top directory: Models 3,655 (51%), Probability 2,189 (31%), Risk 407,
Pricing 353, Choice 256, Markets 170, Contracts 53, Insurance 49. **The trunk (`Pricing` + `Contracts`) is
406 declarations, 5.7% of the library.** Single towers: the American put free-boundary/stopping tower is
**174 modules and 1,284 declarations (18% of all declarations)**, with exactly one consumer outside it
(`Models.Jumps.JumpDiffusionBrownian`); its external statement dependencies are `snellEnvelope`,
`feynmanU`/`heatKernel`, `bsPDiv`, `sampledFiltration`, never `Market`. The SVI certificate is 49 of
`ModelFree`'s 56 modules. These are *towers over one capstone*, not cells.

### 2.2 How much of the statement text is about probability at all

Share of public theorems whose type mentions `MeasureTheory`/`ProbabilityTheory`: Black-Scholes 33%,
Binomial 22%, StochVol 8%, ModelFree 11%, Choice 9-12%, Utility 0%, Pricing/Duality 0%. The library is
largely *formula calculus* (Greeks, convexity, PDE verification, algebraic certificates), with the
probabilistic content concentrated in bridges. That is fine; it means the organization must make
bridges first-class, because they carry the probability.

### 2.3 Who builds on which central object (statements, not imports)

The index gives `type` (the statement) and `uses` (proof constants). I tokenised each statement for
library constants. Findings:

* **`Market` is constructed in exactly two places**: `Contracts.Binomial.market` (a full instance: market,
  `exists_isPricingMeasure_iff` giving existence of a pricing measure iff `BinomialNoArb`, the price
  theorem `price_market_pay_eq_binomialPrice`) and the generic adapter `DiscreteMarket.toMarket`
  (`isPricingMeasure_toMarket_iff`). No Black-Scholes, Bachelier, jump, HJM, Heston or credit market is a
  `Market`; their prices are `Contract.value Q D X c` under a hypothesis bundle (`BSCallHyp`,
  `BachelierHyp`, `JumpDiffusionHyp`, `HasBondPrice`, `BondModel`, ...) with no theorem that `Q` prices a
  market. `IsPricingMeasure` appears in 3 modules outside `Pricing/Market.lean` (Binomial.Market,
  DiscreteMarket, MartingaleFrozen). So "priced under Q" is the library's word for what is, in the
  main models, an integral with a name.
* **The FTAP tower is a chain but not under `Market`.** The six forms (`TwoState → MultiState →
  OnePeriodVector → OnePeriod → Discrete → Complete`; `DensityPasting → DMW`; `Continuous`) are linked by
  iff-bridges and share `Pricing/Duality/ConvexSeparation`. They state `NoArbitrage` for a *bare process*
  `S : ℕ → Ω → F`. `Market` imports only `EquivMartingaleMeasure` and `StatePrices`; the join is the
  single module `DiscreteMarket`. So the FTAP's 110 theorems reach `Market` through one adapter. Counts of
  the parallel notions: **8 no-arbitrage predicates** (`NoArbitrage`, `NoArbitrageLocal`/`At`,
  `OnePeriod.NoArbitrage`, `OnePeriodVector.NoArbitrage`, `HasArbitrageTwoState`, `HasArbitrageMultiState`,
  `ContinuousMarket.NoArbitrageSimple`, plus `BinomialNoArb`) and **7 EMM notions** (`IsEMM`,
  `OnePeriod.IsEMM`, `OnePeriodVector.IsEMM`, `HasEMMTwoState`, `HasEMMMultiState`,
  `Market.IsPricingMeasure`, `LocalEMMDensities`). They are bridged along a spine, which is good, but only
  `IsEMM ↔ IsPricingMeasure` reaches the market.
* **"Price" is not one object.** 70 defs match `price|value` in the index; exactly one routes through
  the trunk (`Market.price`). Others: `binomialPrice`, `americanPrice`, `bermudanPrice`, `mertonCallPrice`,
  `jumpDiffusionCallPrice`, `margrabePrice`, `kirkSpreadPrice`, `bondPriceDisc`, `payerSwapValue`,
  `schwartzFuturesPrice`, the 15 American-put value/price definitions, `statePricePricing`,
  `superReplicationPrice`. The bridges that exist are one-per-family (`Contracts.BlackScholes.value_*`,
  `Contracts.Binomial.price_*`, `Models.Rates.Jamshidian`, `Models.Credit.DefaultTime`). Only 25 non-trunk
  modules have a theorem whose statement mentions a trunk object (93 theorems).
* **Four encodings of "a finite law", five with the two-point ones.** `Finset ι → (ι → ℝ)` weights
  (VNM `expectedUtility`, `acceptableUnderUtility`, `statePricePricing`, `spectralRiskFinite`,
  `herfindahl`; appears in 55 Choice, 38 Risk, 62 Models, 14 Pricing declarations); `Measure Ω` with an
  `Ω → ℝ` (VaR/ES, Coherent, Market; 1,000+ declarations); `Measure ℝ` (`kellyReturnMeasure`,
  `Elicitability`, `esLevelMixture`; Risk 19, Models 156); `StdSimplex ℝ ι` with `finiteLaw` (DiscreteVaR
  only); and concrete `Fin 2`/`![p, 1-p]` (`acceptableUnderUtility_log_iff_kellyGrowth`). Only
  `DiscreteVaR.finiteLaw` converts. `Choice` declares 15 statements over `Measure`, against 55 over
  weights.
* **Utility is a toy and risk measures are fine.** `Choice/Utility` is one module (20 declarations,
  `expectedUtility s p u` over a `Finset`). `IsCoherentRiskMeasure P ρ` is on `Ω → ℝ` and is reused for
  finite `ι` in `AcceptanceSet` (`coherentRisk_isLUB`), so the risk-measure object is *not* duplicated;
  the duplication is on the Choice side. `valueAtRisk X P α` and `expectedShortfall` are on `Ω → ℝ` with
  `P`, i.e. law functionals; `gaussianVaR`, `portfolioVaRN`, `componentVaR`, `finiteVaR` are closed
  forms, a fifth of Risk's declarations.
* **Cross-section theorems** (public theorems whose statement mentions concepts of two sections, tools
  excluded): Models-Pricing 126; Choice-Risk 27 (all `UtilityDerivation` and the Gaussian-Markowitz risk
  modules); Markets-Models 13; Insurance-Models 6; **Pricing-Risk 4; Choice-Pricing 0**; Models-Risk 1.
  Joint count with the trunk for the Choice limb is zero.
* **Module-level components** (statement references between modules, with the 12 hub modules removed,
  `Call`, `StandardNormal`, `ItoIntegralL2`, the American `Problem`, `Pricing.Value`, ...): 171
  components; one giant of 485 modules (BS 165, Brownian 81, Rates 44, Risk 37-32, Binomial 23, Choice
  19, ...), a 42-module SVI island, a 7-module jumps-tools island, and **153 singleton modules**
  (BlackScholes 54, Brownian 24, ModelFree 9, Probability 29 across the rest). Choice sits in the
  giant component *via Risk*, not via the trunk: no Choice concept is within 2 statement-hops of the
  trunk except one. "In the giant component" is therefore too weak a notion of connected.

### 2.4 The real clusters, and what each is built on

| cluster | size | built on | honest status |
|---|---|---|---|
| FTAP/duality | 11 modules + Duality 2 | `ConvexSeparation`, `IsEMM`, bare processes | a connected chain; joined to `Market` by one adapter |
| Market/Contract trunk | ~6 + 21 | `Market`, `Contract.value` | used by Binomial, Rates (bond), Credit (default time) |
| Binomial | 25 | `Market`, `BinomialNoArb` | fully rooted (the template) |
| Black-Scholes calculus | 231 | `BSCallHyp`, `Phi`, `bsd1/bsd2` | `Contract.value` for 9 contracts; no market; Greeks, PDE, exotics reach the bundle via 2-4 hops |
| American tower | 174 (in BS) | `snellEnvelope`, heat kernel | one capstone, never `Market` |
| Rates | 50 | `HasBondPrice`, `BondModel`, `HJMModel` | 36 theorems through the trunk; best-connected family |
| Credit (Models) | 12 | `Contract.value` via `DefaultTime`, `CDS`; KMV on `BSCallHyp` | well connected |
| Credit portfolio (Risk/Credit) | 6 | `oneFactorPD`, `gaussianThreshold`, `tranchePayoff` | **not** tied to `kmvPD` or to `Contract` |
| Jumps | 22 | `JumpDiffusionHyp`, Esscher | via mixing and incompleteness; no `Market` |
| StochVol / LocalVol / Bachelier | 6 / 2 / 2 | reals, `Dupire.callSurface`, `BachelierHyp` | LocalVol 3% reach, Bachelier 0% |
| ModelFree (calls, SVI, variance swap) | 56 | `IsNormalizedCallPrice`, `SVI.Params`, `blackCall` | statically complete, **not** tied to `Market`; SVI reaches BS price via `blackCall_eq_bsSmile` |
| Risk laws | ~20 | `valueAtRisk`, `quantile`, `Phi` | internally dense; 4 theorems reach the trunk (`ContractRisk`) |
| Risk axioms | ~8 | `IsCoherentRiskMeasure`, `ConvexDuality` | shares the duality root with FTAP; not tied to superhedging in the library's statements (frontier #456) |
| Choice: Portfolio | 17 | covariance matrices, `Finset ι` | self-contained, with real probabilistic bridges (`portfolioVarN_covariance_eq_variance`) |
| Choice: Performance | 10 | reals, finite models | 4 of the 10 modules are financial ML statistics (purged CV, fractional differentiation, label uniqueness, bet sizing) |
| Choice: Utility | 1 | `Finset` weights | one-line link to Risk, none to the trunk |
| Insurance | 6 | `SurvivalModel`, `hazardSurvival` | `survivalFunction_eq_hazardSurvival` already unifies mortality with hazard curves |
| Markets: DeFi | 8 | AMM reals; KMV liquidation | liquidation tied to `kmvPD`; AMM isolated |
| Markets: Microstructure | 7 | Bayes posteriors | 15% reach after `condExp_payoff_eq_quote` |

---------------------------------------------------------------------------------------------------

## 3. The target organization

### 3.1 Central definitions (what each part is stated over)

The principle: **at most a dozen central objects; every cell's headline statements mention one of them
or declare why not.** Where the object exists, say so; where it must be introduced or generalised, say
what the old one becomes (per CLAUDE.md, an instance, never a parallel).

| # | object | today | what changes |
|---|---|---|---|
| O1 | `Contract ι`, `Payoff ι`, `Scenario` | `Contracts/Core` | stays; add the instruments the sockets need (`trancheLeg`, `lpPosition` as `Payoff` terms via `rpow`/`min`/`max`) |
| O2 | `Market ι Ω` with `price`, `priceAt`, `IsPricingMeasure` | `Pricing/Market` | add `Market.pricingMeasures T := {Q \| IsPricingMeasure T Q}`, `Market.superPrice`, and the public landmark `Market.noArbitrage_iff_exists_pricingMeasure` (discrete) as a specialisation of the existing bare-process FTAP, so the six FTAP forms read as `Market` statements |
| O3 | the dual set `𝒬(M)` and one **convex-duality interface** | `Pricing/Duality/ConvexSeparation`, `ConvexDuality`, `SuperhedgingDuality` | one lemma `separation_gives_state_price` consumed by FTAP, `AcceptanceSet`, and the utility joint; the three limbs literally call the same lemma |
| O4 | `IsConvexRiskMeasure P ρ` as the base structure, `IsCoherentRiskMeasure` extending it by positive homogeneity | `Risk/Coherent` | introduce the base (entropic risk, utility acceptance sets are convex, not coherent; the library already proves `not_exists_isCoherentRiskMeasure_log_acceptance`) |
| O5 | `IsLawInvariant P ρ` (a predicate), with `valueAtRisk`, `expectedShortfall`, `expectile`, `spectralRiskMeasure` as the instances | implicit | the formal home of "stands alone: a quantile of a law" |
| O6 | **a single finite-law adaptor** `Measure.ofWeights s p` (today `DiscreteVaR.finiteLaw`), and `expectedUtility s p u = ∫ u ∂ofWeights`, `statePricePricing = ∫`, `spectralRiskFinite = spectralRiskMeasure` | five encodings | move `finiteLaw` to `Probability/Laws`; restate the `Finset ι` APIs as corollaries; this is the move that lets Choice mention `Measure` |
| O7 | `expectedUtility P u X := ∫ u ∘ X ∂P` on random variables | weights over a `Finset` | the VNM theorem is the finite case |
| O8 | `SDF`: `Market.sdf Q T := (dQ/dP)·deflator T` (the object `Market.statePrice` is the finite-space shadow) | partially (`statePrice`, `StatePrices`, `PricingKernel`) | name it, so HJ and CAPM have something to be about |
| O9 | `SurvivalModel` / `hazardSurvival` as the single lifetime object for Insurance and Credit | unified by `survivalFunction_eq_hazardSurvival` | remove the duplicate premium-leg/annuity definitions: `lifeAnnuityDue` and `cdsPremiumLeg` as one contract |
| O10 | **Model socket**: per family, `Models/<F>/Market.lean` exporting `market`, `isPricingMeasure`, and either `pricingMeasure_unique` (complete) or `pricingMeasures_not_subsingleton` (incomplete) | Binomial only | the template is `Models/Binomial/Market.lean` |
| O11 | `IsNormalizedCallPrice` as the static-FTAP object | `ModelFree/CallPriceFunction` | its home moves next to `Market` (see layout) |
| O12 | the law-of-observation bridge `Market.price_eq_of_map_observation_eq` | `Pricing/Market` | promoted to the designated way a closed-form family connects: a formula connects once, here |

A remark on O12, as the maintainer notes: because `price_eq_of_map_observation_eq` says the price is a
function of the *law of what the contract reads*, a family needs one socket theorem of the form
"this explicit law (`gaussianReal`, lognormal, two-point) is the law of the observation of a `Market`
under a pricing measure". Everything downstream (every `bsd1` Greek, every barrier formula that is a
`Contract` value) is then connected through the formula without importing the market. The metric in §4
therefore must follow *statements through definitions*, not imports.

### 3.2 Module layout and import discipline

I would not rename directories for taste. The moves that change what the layout *means*:

```
MathFin/
  Probability/ Analysis/ (Convexity)/ Statistics/        tools. No finance vocabulary in statements.
  Contracts/                                            O1.
  Pricing/                                              the spine: Market, FTAP/, Duality/, StaticArbitrage/ (ModelFree moves here),
                                                        Hedging/ (superhedging, completeness), Numeraire/, SDF/.
  Models/<Family>/   Market.lean (the socket, O10)  +  Formulas/ Greeks/ Exotics/ PDE/ Towers/<Name>/{Summit.lean,…}
  Preferences/       Utility/ (O7), MeanVariance/ (Markowitz…, CAPM), Growth/ (Kelly), Equilibrium/
  Risk/              Axioms/ (O4, AcceptanceSet), Laws/ (O5: VaR, ES, expectile), Aggregation/, CreditPortfolio/, Exposure/
  Actuarial/         Survival (O9), Premium, Ruin
  Mechanisms/        Microstructure/, AMM/, Lending/
  Statistics/        Performance/ (ratios), Backtesting/ (purged CV, fractional differencing, bet sizing)
  Bridges/           only place allowed to import two sibling sections (suffix …Bridge in a section is the alternative)
```

Moves with content: (i) `ModelFree/` (56 modules) → `Pricing/StaticArbitrage/`: it is the static FTAP, not a model;
(ii) the four financial-ML modules of `Choice/Performance` → `Statistics/Backtesting` (they are
statistics, and "Choice" had one module of actual choice theory); (iii) `Choice` splits into
`Preferences/` and the portfolio theory under it; (iv) towers (`American`, `SVI`) get a `Summit.lean`
that states the capstone and is the only module of the tower the rest of the library and the blueprint
may cite; (v) `Markets/` becomes `Mechanisms/` (its contents are price-formation mechanisms).

Import rules, each testable:

1. **Layering.** tools < Contracts < Pricing < {Models, Preferences, Risk/Axioms, Actuarial} <
   {Mechanisms, Statistics, Risk/{Laws, CreditPortfolio, Exposure}}. A module may import only
   lower or same-section layers. The current inversion where a general piece sits below a specialisation
   is fixed by the O2 move: FTAP states over `Market`.
2. **Sibling imports only in `Bridges/`.** Joins between Preferences, Risk and Models are bridge modules
   (the repo already uses this idea for `Foundations/`).
3. **A bridge module contains at least one theorem whose statement mentions concepts from both sides**
   (test from the index; this stops an empty `Bridges/X.lean` from being a relabelled import).
4. **Every cell either has a socket/joint to the spine or a `standalone` declaration** (below).
5. **Towers** have one `Summit.lean`; library code outside the tower cites only the summit.

### 3.3 What legitimately stands alone, and how it is declared

A cell may stand alone for exactly one of these reasons. The reason is a field in the module docstring
(`## Standalone` section, a controlled vocabulary like `docs/subjects.toml`), and `standalone` requires
a `socket:` naming the one theorem or the one frontier connector that says how the object reads in a
market.

| reason | examples | the socket it must name |
|---|---|---|
| `law-functional`: depends only on the law of its argument (O5) | `valueAtRisk`, `expectedShortfall`, `expectile`, `herfindahl`, Kelly growth | `Contracts.valueAtRisk_loss_europeanCall_le` style: a position's loss in a market |
| `algebraic-certificate`: a real-closed-field certificate for an analytic statement | the SVI tower | the call-price condition: `fullCertificateFormula_iff_bsSmile_convex` plus connector K2 |
| `deterministic-mechanism` | constant-product AMM invariants, swap fees | the LP position as a `Contract` (K12) |
| `tool`: pure analysis/probability, with no finance vocabulary | Brownian calculus, Gaussian analysis, copula algebra | none; excluded from the denominators of §4; candidates for upstreaming to BrownianMotion/Mathlib |
| `convex-program`: a finite-dimensional optimisation stated over reals | Markowitz KKT, risk parity FOC | the Gaussian-utility joint K9 |

Rule: standalone is a *declared* property of a cell, ratcheted: the number of standalone modules may not
rise, and each must keep a named socket. Unlabelled isolation (the 153 singleton modules, 54 of them in
Black-Scholes) is what the metric reports.

### 3.4 Blueprint: what a node is, what an edge means

* **Nodes are of five kinds.** `object` (O1-O12 and the family sockets), `landmark` (a textbook-named
  result at the generality proved), `joint` (a theorem whose statement mentions two limbs' objects),
  `socket` (a model is a `Market`), and `connector` (a phantom: stated, not proved). A *waypoint* is not a
  node (the previous design's rule stands).
* **Edges have three meanings, never mixed.**
  1. `uses`: proof-term dependence (what the existing Lean blueprint already computes). It is the faint
     background edge.
  2. `states`: the statement of the target mentions the source (computed from the index). This is the
     edge that makes the metric of §4 and that the tree draws solid.
  3. `connects`: a connector (a joint or a phantom) joins two objects that no `uses` edge links. Solid if
     proved, dashed if phantom.
* **Every landmark carries the object it is over.** A node with no object and no `standalone` reason is
  a lint failure (a result that is "about" nothing the library defines is either a tool or isolated).

### 3.5 Issues: how the work is encoded

* **Three issue types** instead of 17 `area:*` labels plus `type:*`:
  `connector` (a phantom: `Blueprint: conn:<from>-<to>`; label `joins: A+B`), `socket`
  (`Blueprint: sock:<family>`), `tower-summit` (`Blueprint: summit:<tower>`), plus the existing
  `type:proof|research` for proofs inside a node. The area of an issue is the *pair of objects it
  joins*, not a topic: issue #456 is `joins: Pricing+Risk`, and its body carries the Lean statement.
* **A connector issue always contains the statement as Lean code.** It lives as a `sorry` in
  `MathFinFrontier/` (a `lean_lib` that is never imported by `MathFin`, not in `AxiomAudit`, built by a
  separate workflow so `sorry` there is allowed and counted). CI checks (a) it elaborates, so both sides
  are existing declarations and the types match, (b) the connector's frontier label equals the issue
  body, (c) there is no `sorry` anywhere in `MathFin/` (unchanged gate). Delivering the connector means
  moving the statement into `MathFin/Bridges/` or the right section, filling the proof, tagging it, and
  deleting the file. This also makes the 12-15 connectors usable as an open-problem benchmark in the
  dataset: stated, type-checked, unsolved.
* **Sizing and ordering come from the metric.** The what-if numbers in §5 are computed by adding the
  connector's edge to the statement graph; the issue carries the number.
* **Connectors can chain through other phantoms.** A phantom whose two ends are also phantom-dependent
  (e.g. K3 needs O8) lists `needs:` links, which is what lets the tree draw a dashed path.

### 3.6 Docs

* Each section page opens with **the object it is over**, the one-line relation to the spine (instance /
  dual / consumes / standalone-with-reason), and a generated *Where this appears elsewhere* table: the
  theorems of other sections whose statements mention this section's objects (computed from the index,
  so it cannot be edited into existence). The sentence "stands alone" appears only for declared
  standalone cells and shows the socket.
* A **Joints page**: the three dualities of §1.1 as a table whose rows are `proved`, `proved in the
  finite case`, `phantom`, with links to the statement. This replaces the prose table in
  `docs/organization.md`, which currently says "frontier" for five of seven rows.
* The README landmark table lists only landmarks whose statement is as strong as the prose (the
  last-step check in CLAUDE.md), by reading `states` edges rather than titles.
* Remove the claim that valuation/choice/risk are "three questions asked of a position" from the front
  door: the library does not state choice or risk over `Contract` positions (statement count 0 and 4).
  Say instead: three dualities of one price system, of which the library has the first, part of the
  second, and none of the third, plus the statistical risk toolbox.

### 3.7 The tree

* **Height is measured:** y = chain distance to the spine (§4) for finance concepts, import depth for
  tools. A cell whose objects have no finite distance does not hang from the trunk: it floats beside it
  as an island with its declared reason as a label. The picture can then say "SVI is disconnected" or
  "connected only by a dashed edge", which the current picture cannot.
* **Edges:** solid = `states` bridge theorem (proved), thin grey = `uses` (hidden unless asked), dashed =
  phantom connector, with the metric gain as the dash weight. Joints are drawn at the fork between the
  two limbs they join.
* **Node size:** declarations supported (log scale); towers are drawn as a single node with the module
  count in the label (an American-put tower of 174 modules must not be 174 leaves).
* **Colour:** the model family, the same hue in every limb (the previous design's good idea). **Ring:**
  a standalone declaration. **Badge:** socket proved.
* The roots show the `tool` cells; the Brownian tower is marked "upstream candidate".

---------------------------------------------------------------------------------------------------

## 4. A metric that relabelling cannot move: chain reach

Definition (computable from `decl-index.json`; reference implementation `tools/verify/chain_reach.py`, to be
`tools/verify/chain_reach.py` plus a `ratchet.json` baseline).

* *Concepts* `C`: non-private `def`/`structure`/`inductive` outside tools (`Probability/`,
  `Pricing/Duality`, `Init`). *Spine* `S ⊂ C`: those in `Pricing/` and `Contracts/` (106 concepts).
* *Edges:* (a) two concepts mentioned in the **statement** of a non-private theorem (≤ 15 concepts per
  statement), where the theorem's proof uses at least two constants other than those concepts; (b) a
  non-structure `def`'s body uses another concept, unless the def is Prop-valued (hypothesis bundles do
  not link). Edges are undirected; **no edge comes from a module's directory, a docstring, a blueprint
  tag, a taxonomy entry or an import**.
* *Distance* `d(c)` = BFS distance from `S`. For a theorem `t` outside the tools and the spine,
  `hop(t) = 1 + min_{c in statement(t)} d(c)`; `hop = ∞` if the statement mentions no concept.
* **Headline: `R3` = share of finance theorems with `hop ≤ 3`; `R2` with `hop ≤ 2`.** Per-cell vectors
  are the real report. Secondary counts: (i) **socket coverage** = families with a proved
  `IsPricingMeasure` theorem for a `Market` / families; (ii) **joint span** = public theorems whose
  statements mention objects of two limbs, per pair; (iii) **unlabelled isolation** = modules in no
  component with a concept of distance ≤ 3 and not declared `standalone`.

Why it resists gaming. Moving or renaming modules changes no declaration, so no number. Restating a
docstring changes nothing. Importing a module changes nothing. A new `structure` bundling two concepts
adds no edge (Prop-valued and structures are skipped). A trivial lemma `rfl`-bridging two concepts is
dropped by the "two non-concept proof constants" rule (it dropped 405 theorems and moved ModelFree from
52.2% to 13.7%, which shows the rule bites). Tool concepts (`Phi`, `bsd1` as a hub) cannot glue two
families because tools are excluded from the graph. What it does reward is a true statement whose terms
come from both sides. What it cannot see is a *vacuous* bridge hypothesis; that stays with the values
review.

**Today's values (main, guarded variant):**

| cell | finance theorems | R3 |
|---|---|---|
| Choice/Performance | 76 | 0.0% |
| Choice/Utility | 17 | 0.0% |
| Choice/Portfolio | 95 | 26.3% |
| Markets/Microstructure | 59 | 0.0% |
| Markets/Execution | 4 | 0.0% |
| Markets/DeFi | 64 | 48.4% |
| Models/Bachelier | 9 | 0.0% |
| Models/LocalVol | 33 | 3.0% |
| Models/ModelFree | 255 | 13.7% (52.2% unguarded: the guard exposes trivial edges) |
| Risk/Credit | 51 | 33.3% |
| Risk | 284 | 72.2% |
| Models/StochVol | 95 | 55.8% |
| Models/BlackScholes | 1,407 | 52.8% |
| Models/Forwards | 38 | 55.3% |
| Insurance | 36 | 58.3% |
| Models/Rates | 380 | 75.3% |
| Models/Jumps | 263 | 77.2% |
| Models/Credit | 93 | 77.4% |
| Models/Binomial | 252 | 81.3% |
| **all (3,511)** | | **R3 = 54.6%, R2 = 28.3%** |

Socket coverage: 1 of 9 market families (Binomial), plus the generic discrete adapter. Joint span:
Pricing-Risk 4, Choice-Risk 27, **Choice-Pricing 0**. Unlabelled isolation: 153 singleton modules.

Two honest cautions. First, R3 saturates inside a family: the big BS cell is 52.8% because its Greeks/PDE
modules are hop 4+ through `bsd1`-like functions, so the headline is a floor, and the interesting
quantity is the *per-cell* vector and sockets. Second, single connectors move R3 by 0.1-1.1 points (§5);
the sockets move *meaning* (value under a bundle → price in a market) more than R3. Both should be
tracked: R3 and socket coverage.

---------------------------------------------------------------------------------------------------

## 5. Connector inventory

`R3 gain` is computed by adding the stated edge to the guarded-free graph (the unguarded variant, a
proxy; baseline R3 58.6% unguarded, 2,059 of 3,511). All twelve together: 62.9%, R2 28.8% → 32.3%.
Statements are mathematically exact modulo implicit hypotheses; arguments marked `…` are routine.
"Exists" means checked in the index.

**K1. Black-Scholes is a market (socket; issue #452).**
Declarations: `Contracts.BlackScholes.constGirsanovMeasure`, `value_physical_eq_riskNeutral`,
`value_europeanCall`, `MarketCompleteness.emm_unique_of_complete`, `BSCallHyp.of_isPreBrownian`.
```
def bsMarket (hW : IsPreBrownianReal W μ) (S₀ m r σ : ℝ) : Market Unit Ω
  -- asset () t = S₀ * exp ((m - σ²/2) * t + σ * W t),  numeraire t = exp (r * t),  𝓕 = natural filtration of W
theorem bsMarket_isPricingMeasure (hσ : σ ≠ 0) (H : ℝ≥0) :
    (bsMarket hW S₀ m r σ).IsPricingMeasure H (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
theorem bsMarket_price_unique {Q} (hQ : (bsMarket …).IsPricingMeasure H Q) {c : Contract Unit}
    (hc : c.FixedDated) (hH : ∀ t ∈ c.dates, t ≤ H) :
    (bsMarket …).price Q c = (bsMarket …).price (constGirsanovMeasure …) c
```
Then `(bsMarket …).price Q (europeanCall K T) = S₀ Φ(d₁) - K e^{-rT} Φ(d₂)` by `price_eq_of_map_observation_eq`
and the existing `value_europeanCall`. Chains all 231 BS modules, every exotic that is a `Contract.value`,
and the Bachelier/Garman/Margrabe grounding modules. Gain: 2 theorems by R3 (it is mostly semantic).
Hardest piece: `IsPricingMeasure` needs the exponential martingale under `Q_θ` on the natural filtration
(Girsanov is in the library).

**K2. Call-price functions are the static FTAP (ties ModelFree and SVI to Market).**
Declarations: `IsNormalizedCallPrice`, `SVI.blackCall`, `fullCertificateFormula_iff_bsSmile_convex`,
`Dupire.callSurface`, `Dupire.breedenLitzenberger_weak`, `Market.price`, `Contracts.europeanCall`.
```
theorem Market.isNormalizedCallPrice {M : Market Unit Ω} (hQ : M.IsPricingMeasure T Q)
    (hpos : ∀ ω, 0 < M.asset () T ω) … :
  IsNormalizedCallPrice (fun k => M.price Q (europeanCall (k * F) T) / F)    -- F := M.price Q (pay T (obs () T))
-- converse (Roper 2010, Thm 2.1; Kellerer):
theorem exists_market_of_isNormalizedCallPrice {C} (hC : IsNormalizedCallPrice C) :
  ∃ (M : Market Unit (ℝ≥0)) (Q), M.IsPricingMeasure 1 Q ∧ ∀ k > 0, M.price Q (europeanCall k 1) = C k
-- consequence for the SVI tower:
theorem svi_arbitrage_free (p : SVI.Params) (h : fullCertificateFormula p) :
  ∃ M Q, M.IsPricingMeasure … ∧ ∀ k > 0, M.price Q (europeanCall k T) = blackCall p k
```
Forward part is a few lines from `price_pay_obs` and the Jensen/monotonicity facts the module already has.
The converse needs the Breeden-Litzenberger measure from a convex `C` (the weak form is in
`Dupire`). Gain: +7 theorems (guarded: ModelFree 13.7% to ~50%).

**K3a. Hansen-Jagannathan (choice ↔ valuation; issue #458).** Declarations: `sharpeRatio`,
`Market.IsPricingMeasure`, `Market.statePrice`, `IsEquivProbMeasure`, Mathlib `covariance`/`variance`.
```
def Market.sdf (M) (Q) (T) : Ω → ℝ := fun ω => (Q.rnDeriv M.P ω).toReal * M.deflator T ω
theorem hansen_jagannathan (hQ : M.IsPricingMeasure T Q) (i : ι) (hS : MemLp (M.asset i T) 2 M.P) … :
  |sharpeRatio (E_P[R_i]) R_f (sd_P R_i)| ≤ sd_P (M.sdf Q T) / E_P (M.sdf Q T)      -- R_i = S_i(T)/S_i(0), R_f = 1/E_P[sdf]
```
Proof is Cauchy-Schwarz on `E[m R^e] = 0`. Gain: **+39 theorems**, the largest single one, and it lifts
`Choice/Performance` from 0% (the first edge from that cell to the trunk).

**K3b. CAPM from an affine SDF.**
```
theorem sml_of_affine_sdf (hm : M.sdf Q T =ᵐ[M.P] fun ω => a - b * R_M ω) (i) :
  E_P R_i - R_f = beta (Cov R_i R_M) (Var R_M) * (E_P R_M - R_f)  -- i.e. securityMarketLine (beta …) …
```
Using `CAPM.beta`, `securityMarketLine`, and the equilibrium `CAPMEquilibrium` as its mean-variance
converse (`CAPMEquilibrium` proves the SML from the market portfolio's marginal-variance FOC; this
statement shows the same SML from the SDF). Gain with K3a: +4.

**K4. Marginal utility is a state price (finite Ω first; #457).** Declarations: `expectedUtility`,
`Contracts.Binomial.market`, `Market.statePrice`, `Market.IsPricingMeasure`. Needs O6.
```
theorem expectedUtility_eq_integral (hp : ∑ i ∈ s, p i = 1) : expectedUtility s p u = ∫ u ∂(Measure.ofWeights s p)
theorem utility_state_price (hM : complete finite market, hQ : M.IsPricingMeasure T Q) (hu : StrictConcaveOn … ∧ C¹)
    (hX : IsMaxOn (fun X => ∫ u ∘ X ∂M.P) {X | M.price Q (pay T X) ≤ w} X*) :
  ∃ λ > 0, ∀ ω, deriv u (X* ω) = λ * M.sdf Q T ω
```
Gain +22 (Choice/Utility 0% → 94%).

**K5. The Kelly portfolio is the numéraire portfolio (#log-optimal-numeraire).** Declarations:
`kellyReturnMeasure`, `kellyFraction`, `kellyGrowth`, `kellyNumeraire_isRiskNeutral`, `Market.withNumeraire`,
`Market.price_pay_withNumeraire`, `numeraireMeasure`.
```
def kellyMarket (p b : ℝ) : Market Unit Bool    -- Bernoulli(p); asset = bet payoff, numeraire = 1
theorem kellyMarket_withNumeraire_isPricingMeasure :
  ((kellyMarket p b).withNumeraire (kellyGOPWealth p b)).IsPricingMeasure 1 (kellyMarket p b).P        -- P prices under the GOP numéraire
theorem kelly_fair_odds : numeraireMeasure P (fun ω => W* ω) … = fairOddsMeasure b           -- q₊ = 1/(b+1), already proved on reals
```
Generalisation (finite Ω): the log-optimal wealth `W*` makes `S/W*` a `P`-martingale (benchmark approach).
Gain +24.

**K6. The superhedging price is a coherent risk measure, represented by the pricing measures (#456).**
Declarations: `SuperReplicates`, `martingaleProbVectors`, `exists_pos_price_le_superReplication`,
`IsCoherentRiskMeasure`, `coherentRisk_isLUB`, `representingSet`.
```
def superPriceFn (z : Fin M → Fin N → ℝ) (L : Fin N → ℝ) : ℝ := sInf {x | ∃ θ, SuperReplicates z L x θ}
theorem superPriceFn_isCoherent (h : ¬ HasArbitrageMultiState z) (P : Measure (Fin N)) (hP : ∀ n, P {n} ≠ 0) :
  IsCoherentRiskMeasure P (superPriceFn z)
theorem representingSet_superPriceFn : representingSet (superPriceFn z) = closure (martingaleProbVectors z ∩ stdSimplex)
```
(Already "proved on a finite space" per the previous design's table; the sharper claim is the equality with
the closure, which needs Minkowski-Weyl for the polyhedron `martingaleProbVectors`.) Gain +9 (R3), but
this is the joint that makes Risk a limb of the duality rather than a neighbour.

**K7. Entropic risk is the certainty equivalent of exponential utility (choice ↔ risk).** Declarations:
`acceptableUnderUtility`, `acceptableUnderUtility_convex`, `not_exists_isCoherentRiskMeasure_log_acceptance`.
```
def entropicRisk (γ) (X) (P) := (1/γ) * log (∫ exp (-γ * X) ∂P)
theorem acceptableUnderUtility_exp_iff (hγ : 0 < γ) :
  acceptableUnderUtility s p (fun x => -exp (-γ * x)) 0 X ↔ entropicRisk γ (id) … X ≤ 0
theorem isConvexRiskMeasure_entropicRisk : IsConvexRiskMeasure P (entropicRisk γ)    -- O4
theorem not_isCoherent_entropicRisk : ¬ IsCoherentRiskMeasure P (entropicRisk γ)
```
Gain +0 R3 (already Choice-Risk) but removes a joint listed as "to survey"; it is where O4 is born.

**K8. Mean-variance is expected utility with Gaussian returns (choice ↔ choice; makes Choice one limb).**
Declarations: `expectedUtility`, `portfolioVarN`, `portfolioVarN_covariance_eq_variance`,
`IsTangentPortfolioN`, `Markowitz`/`TangentPortfolio`, Mathlib `mgf_gaussianReal`.
```
theorem ce_exp_gaussian (hX : HasLaw X (gaussianReal μ σ²) P) (γ) :
  certaintyEquivalent (fun x => -exp (-γ x)) X P = μ - γ * σ² / 2
theorem tangent_is_cara_optimum (hΣ : Σ PD) (hR : HasLaw R (multivariate Gaussian μ Σ) P) :
  IsTangentPortfolioN s (γ⁻¹ • Σ⁻¹ μ) …  ↔  w maximises ∫ -exp (-γ (wᵀR)) ∂P
```
Gain +4 inside Choice, but it is what lets the Portfolio and Utility cells share a statement and thus
reach the trunk once through K3/K4.

**K9. Glosten-Milgrom quotes are a pricing measure (#460).** Declarations:
`Execution.condExp_payoff_eq_quote`, `postBuy`, `postSell`, `Market.IsPricingMeasure`, Mathlib `martingale_condExp`.
```
def gmMarket (order flow (B n)) : Market Unit Ω   -- asset n = E[V | 𝓖 n]; numeraire 1; 𝓕 = the public filtration
theorem gm_pricingMeasure : (gmMarket …).IsPricingMeasure N P                        -- P prices its own mid-quote
```
Gain +9 and Microstructure 0% → 15%.

**K10. LP position is a contract (#461).** Declarations: `DeFi.v3PositionValue`, `DeFi.coveredCall_sub_v3PositionValue`,
`Contracts.Payoff` (has `rpow`, `min`, `max`), `Contracts.powerCall`.
```
def lpPayoff (L a b : ℝ) : Payoff Unit   -- built from rpow ½, min, max
theorem eval_lpPayoff : Payoff.eval (scenarioAt X ω) (lpPayoff L a b) = DeFi.v3PositionValue L a b (X () T ω)
theorem lp_price_bs : (bsMarket …).price Q (pay T (lpPayoff L a b)) = closed form in Φ(d), e^{-(r+σ²/8)T}
```
Gain +0 (R3), +8 (R2); it moves the AMM from `deterministic-mechanism` standalone to a declared socket.

**K11. Credit portfolio is Merton (Gordy 2003; Risk/Credit ↔ Models/Credit).** Declarations: `kmvPD`,
`kmvDistanceToDefault_eq_bsd2`, `oneFactorPD`, `asrfQuantile`, `tranchePayoff`, `integral_tranchePayoff_oneFactorPD`,
`Contracts.cdsProtectionLeg`, `CVA.cva`.
```
theorem condPD_eq_oneFactorPD (hW : W^i = √ρ·M + √(1-ρ)·ε^i, M, ε^i iid N(0,1)) :
  Q (V^i_T < F | M = f) = oneFactorPD (kmvPD V₀ F r σ T) ρ f
def trancheLeg (a d : ℝ) (T) : Contract Unit      -- built from min/max/sub in `Payoff`
theorem value_trancheLeg : Contract.value Q D X (trancheLeg a d T) = D T * ∫ tranchePayoff a d (L_T) ∂Q    -- CDO tranche price
```
Gain 0 in R3 (the guarded graph sees `kmvPD` already attached to BS), but it removes the only Risk/Credit
island (17 of 51 theorems unreached).

**K12. American value is the Snell envelope of a market's price and dominates the European (the
American tower's summit).** Declarations: `americanPutValue`, `snellEnvelope`, `Contracts.Binomial.market`,
`binomialPrice`, `americanPrice`, `Market.price`, `bsMarket`.
```
theorem americanPrice_eq_snell (binomial) : americanPrice … = snellEnvelope Q_crr 𝓕 … 0 0          -- finite, provable now
theorem americanPutValue_ge_european : americanPutValue Q 𝓕 X … ≥ (bsMarket …).price Q (europeanPut K T)
theorem americanPutValue_eq_superPrice (complete) : americanPutValue … = (bsMarket …).superPrice (put)
```
Gain +24 (R3), **+31 (R2)**, the largest R2 gain: the tower's 174 modules get an arrow to the trunk.

**K13. Insurance is Credit (O9; #459).** Declarations: `lifeAnnuityDue`, `survivalFunction_eq_hazardSurvival`,
`cdsPremiumLeg`, `Contracts.payFlows`, `esscherTilt_isEquivProbMeasure`, `hasLaw_esscher_tilt`, `stdDevPrinciple`.
```
theorem lifeAnnuityDue_eq_value : lifeAnnuityDue i S n = Contract.value Q (fun t _ => (1+i)^(-t)) X (payFlows k (fun k => 1{τ>k}) n)
theorem esscherPremium_eq_price : esscherPremium h X P = ∫ X ∂(esscherTilt h X P)
                                 = Market.price (insuredMarket) (esscherTilt h X P) (pay T X)
```
Gain +5; removes the duplicated "annuity = premium leg" definitions.

**K14. Discrete FTAP is a statement about `Market` (not a connector; a rewrite).** Declarations: the six
FTAP forms, `isPricingMeasure_toMarket_iff`. State `Market.noArbitrage_iff_exists_pricingMeasure` once and
make the bare-process forms `abbrev`s. Gain: 0 (R3), it is the reading fix that makes `Pricing/FTAP` a
`Market` page.

Order of value: K1, K12, K3a/b, K4, K5, K2, K6 (these seven cover every limb and the two largest masses),
then K7-K11, K13.

---------------------------------------------------------------------------------------------------

## 6. Critique of the previous design (`one-trunk` 2026-11-07 and `organization-design` 2026-11-08)

**What it gets right.**
* The diagnosis in `organization-design` §1 is accurate and honest: ten taxonomies, a blueprint that is a
  delivery log, and "none of these numbers moved through phases 0-2c".
* It rejects forcing everything through the pricing functional (VaR is a quantile; Sharpe is a ratio).
* It sees that the deep theorems are the *joints* (dualities between limbs) and makes them first-class.
  Its joint table (utility = state price, superhedging = coherent risk, Kelly = numéraire, entropic =
  exponential CE, premium = price, indifference pricing) is the right list; K3-K7 are those, made exact.
* The second axis (model families, one hue everywhere) and "families, not subjects" for insurance/DeFi
  are right. Kill-list for waypoints in the blueprint is right.
* Hinge issues #451-#462 already exist and carry blueprint labels; the connector idea is half-built.

**What is cosmetic.**
* The cell/family/joint taxonomy is a relabelling. Most of the directory moves it prescribes already
  exist (`Choice/`, `Risk/`, `Models/<Family>/` are there on main). `Choice` stays a limb of "positions"
  although its Utility cell is one module and its Portfolio/Performance cells state nothing over
  `Contract` or `Market` (statement count 0).
* Its metrics (`landmarks_not_nodes`, `cells_without_characteristic_node`, `joints_proved`, per-limb "share
  of nodes resting on that limb's characteristic theorem") are curation counts. A node can be tagged
  without the statement changing. Only `entries_through_trunk` measures connection, and it is an
  import/proof-term measure: it counts a module that imports `Pricing.Value` and uses it in a proof,
  and misses a closed form bridged once by `price_eq_of_map_observation_eq`, which is the very pattern
  the maintainer identified.
* "The directory is the cell" gives `Models/` the whole of "valuation", i.e. 51% of declarations,
  with Heston, SVI certificates and DeFi liquidation under one label. "Valuation" then says nothing.
* "Three questions asked of a position" and "three functionals: linear, concave, convex" are
  attractive and partly false: expected utility is linear in probabilities and concave in wealth;
  mean-variance utility is a quadratic functional of a *return vector*; none of Choice's cells is a
  functional of a `Contract`. The framing invites the reader to expect statements the library does not
  contain.

**What it misses.**
1. *The trunk is at the wrong level.* "Positions in a market" is syntax. The theorems join at the dual
   set `𝒬(M)` and the convex-duality lemma, which the previous design names only as "the method" in
   `mathematical-architecture.md`. Without O3, the "joints" are just labels on three unrelated proofs.
2. *Sockets are absent.* The measurement "limb entries resting on the trunk: 17 of 267" does not lead to
   "give each model family a theorem that it is a `Market`"; it leads to hinge issues one per limb, so a
   family connects by an ad hoc bundle forever (BSCallHyp: 49 modules use it, none is a `Market`).
3. *The masses.* American (18% of declarations) and SVI (49 modules) are not mentioned as structural
   facts. Any design that does not give a tower one capstone and one connector is silent on 20-25% of
   the library.
4. *Parallel encodings of law.* Five encodings, one adaptor. Not noticed, so Choice cannot state
   anything about measures, so no joint with Choice can be stated.
5. *ModelFree is mis-filed.* It is the static FTAP, not a model family.
6. *Phantom connectors have no form.* The frontier TOML has a one-sentence `statement` and a `uses`
   list; nothing checks that the sentence parses, that the two sides exist, or what it would gain.
7. *Height is assigned, not measured.* The tree places by the taxonomy, so a disconnected cluster is
   drawn as a branch.
8. *Standalone has no machinery.* "None should be forced" is a sentence, not a declaration with a
   ratchet and a socket.

---------------------------------------------------------------------------------------------------

## 7. An ordered program

Metric columns: R3 (headline), sockets (of 9 market families), unlabelled isolation (singleton modules not
declared). Baselines: 54.6% (guarded) / 58.6% (unguarded), 1/9, 153.

| step | change | R3 | sockets | isolation |
|---|---|---|---|---|
| 0 | Land `chain_reach.py`, `ratchet.json` baselines, `MathFinFrontier` lib with a check that statements elaborate; port the 14 existing frontier connectors into it. No semantic change. | baseline | 1 | 153 |
| 1 | O6: `Measure.ofWeights` + `expectedUtility = ∫`, `statePricePricing = ∫`, `spectralRiskFinite`; restate the weight APIs as corollaries. | 0 | 1 | -3 |
| 2 | K14 + O2 additions: `Market.noArbitrage_iff_exists_pricingMeasure`, `pricingMeasures`, `superPrice`, `sdf`. | +0.2 | 1 | 0 |
| 3 | K1 (Black-Scholes socket; then Bachelier as a corollary). | +0.1 R3; sockets +2 | 3 | -4 |
| 4 | K3a, K3b (HJ, CAPM), K4 (utility), K5 (Kelly): the Choice limb reaches the trunk. | +1.8 (+39+4+22+24 theorems, unguarded) | 3 | -8 |
| 5 | K12 (American summit, with `Summit.lean` for the tower); collapse the tower in the tree. | +0.7 R3, **+0.9 R2** | 3 | 0 |
| 6 | K2 and the `ModelFree` move to `Pricing/StaticArbitrage`; SVI becomes `algebraic-certificate` with socket. | +0.2 (guarded: ModelFree 13.7% → ~50%) | 3 | -9 |
| 7 | K6, K7 (O4: `IsConvexRiskMeasure` base): the risk limb joins the duality. | +0.3 | 3 | 0 |
| 8 | Sockets for Jumps (incompleteness: two distinct pricing measures with different call prices; `exists_call_esscher_ne_merton` is half of it), Rates (HJM), Credit, Forwards, LocalVol (Dupire), StochVol (Heston): follow the Binomial template. | 0 | 9 | -10 |
| 9 | K8-K11, K13: Choice becomes one limb; Microstructure, AMM, credit portfolio and insurance get their sockets. | +1.0 | 9 | -25 |
| 10 | Declare `standalone` on the residue (laws, tools, certificates) with named sockets; ratchet the count; docs `Joints` page, section pages with generated cross-reference tables; redraw the tree with measured height, dashed phantoms and tower nodes. | 0 | 9 | 0 unlabelled |

Expected endpoint: R3 up by ~5-6 points on the unguarded count and 10-15 on the guarded one (the guarded
number is dominated by ModelFree, Choice, Microstructure and LocalVol moving from near zero), sockets 9/9,
Choice-Pricing joint span from 0 to ≥ 4, every limb with at least one *proved* joint, every standalone
cell with a named socket. The R3 headline is deliberately modest because the dominating mass (BS Greeks,
PDE, American) moves only when Greeks and PDE are restated against `bsMarket`'s price rather than
against `bsd1`: step 11, optional and large: state the Greeks and the pricing PDE for `Market.price` of a
parametrised contract (a `priceFunction : (S₀ ...) → ℝ` obtained from the socket), which is what a
financial mathematician would expect to see ("the Greeks of the price"), and the one change that turns
the 231-module BS directory from a calculus of `bsd1` into a calculus of a market.

Caveats. (1) I measured statements by tokenising `type` strings against declaration names; instance-implicit
arguments and notation do not appear, so a few edges may be missed (a lower bound). (2) The unguarded
vs guarded split changes ModelFree and a few cells; the guarded numbers are the ones I would ratchet.
(3) K2's converse, K6's closure equality and K12's third statement are research-grade; the rest are
straightforward given existing modules. (4) I did not read `tools/verify/docs_site/` (absent from this
branch) and used `program_tree.py` only for what it places; the tree remarks are about the picture the
design promises, not the renderer.
