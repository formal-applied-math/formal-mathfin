# The methods

[`organization.md`](organization.md) states the library's structure: one object, a price system
(positions in a market and the pricing measures that price them), three questions about it
(valuation, risk, choice), met by three dualities, and the model families as a second axis. The
source tree follows the layers of [`architecture.md`](architecture.md). This page is about a
different question: what the proofs are made of.

Four methods recur across the questions and the families. Each is a piece of mathematics with a
root in the library, and each does its work in several [cells](glossary.md#cell). A new result
usually calls one or two of them, and knowing which tells you which root to build on and which
limb it belongs to.

| method | the mathematics | where it works |
|---|---|---|
| I. Convex duality | separation of a cone from a simplex; Legendre–Fenchel | the fundamental theorems and superhedging (valuation); the robust representation of a coherent risk measure (risk) |
| II. Itô calculus | the stochastic integral, Itô's formula, Girsanov, martingale representation | the diffusion, volatility and term-structure families; completeness in arbitrage theory |
| III. Generator and PDE | Feynman–Kac, the Kolmogorov backward equation | diffusion and term-structure valuation as a PDE |
| IV. Intensities and exponential families | the exponential of an integrated intensity; the exponential tilt | the jump, default and mortality-and-claims families |

## I. Convex duality

The fundamental theorem of asset pricing is a separating-hyperplane theorem. The cone of
attainable gains meets the positive orthant only at zero exactly when a strictly positive
functional vanishes on the cone, and that functional, normalised, is an equivalent martingale
measure. The same separation proves the robust representation of a coherent risk measure as a
supremum of expectations over a set of measures, and bounds the superhedging price by the pricing
measures.

* Root: `exists_pos_separating_of_cone_disjoint_simplex` and its companion
  `exists_separating_of_not_mem_cone` (`Pricing/Duality/ConvexDuality.lean`).
  `exists_pos_dual_of_disjoint_stdSimplex` (`Pricing/Duality/ConvexSeparation.lean`) is the
  finite-state form that the FTAP files use.
* Valuation: `ftap_discrete` (`Pricing/FTAP/FTAPDiscrete.lean`), `ftap_two`
  (`Pricing/FTAP/FTAPComplete.lean`), and the agreement of the one-period constructions with the
  multi-state notion, `hasEMMMultiState_iff_exists_isEMM` (`Pricing/FTAP/FTAPMultiState.lean`).
  Superhedging: `emm_le_superReplication` and `exists_pos_price_le_superReplication`
  (`Pricing/SuperhedgingDuality.lean`).
* Risk: `coherentRisk_isLUB` (`Risk/AcceptanceSet.lean`).
* Joint of valuation and risk: `superhedgingPrice_isLUB` (`Risk/Superhedging.lean`), the
  superhedging price of a one-period finite-state market as the supremum of prices over its
  martingale probability vectors.

Not proved: the superhedging duality over strictly positive pricing measures, in several periods,
or on a general space. The
fundamental theorems are proved on a finite space, and for one asset on a general space; the
several-asset Dalang–Morton–Willinger theorem assumes a conditional one-period theorem. The dual
of choice (marginal utility as a state-price density) is stated for a two-outcome bet and open
for a finite state space.

## II. Itô calculus

Every continuous-time model is a process `dX = b dt + σ dB`, and the stochastic integral with
Itô's formula makes functionals of `X` computable. Girsanov's theorem turns a drift into a change
of measure, and martingale representation says every square-integrable claim on the Brownian
filtration is an Itô integral, which is completeness.

* The integral: `itoIntegralCLM` (`Probability/Brownian/Ito/ItoIntegralCLM.lean`), a continuous
  linear map out of `L²` of the predictable integrands with the Itô isometry.
* The formula: `ito_formula_adapted_local_le`
  (`Probability/Brownian/Ito/ItoFormulaAdaptedTD.lean`), Itô's formula along an Itô process with
  bounded adapted continuous coefficients; `Probability/Brownian/Ito/ItoFormulaUnrestrictedLocMart.lean`
  for functions of Brownian motion as a local martingale.
* Change of measure: `changeOfMeasure_setIntegral_eq`
  (`Probability/Martingales/ChangeOfMeasure.lean`), the Bayes rule for martingales;
  `bs_discounted_isQMartingale` (`Pricing/Girsanov.lean`), the Black–Scholes pricing measure as a
  density tilt; `isBrownianOn_of_expMartingale`
  (`Probability/Brownian/ExpMartingaleQBrownian.lean`) and
  `Btheta_isBrownianOn_predictable_of_bdd`
  (`Probability/Brownian/Girsanov/GirsanovPredictableTheta.lean`) for the drift-removed process.
* Representation and completeness: `itoIntegralCLM_surjective_onto_centered` and
  `martingale_representation` (`Probability/Brownian/MartingaleRepresentation.lean`);
  `exists_replicating_strategy_in_price` (`Pricing/MarketCompletenessInPrice.lean`), the hedge as a
  holding in the price.
* Bracket: `norm_sq_increment_eq_bracket`
  (`Probability/Brownian/Ito/ItoIntegralAgainstMartingale.lean`) and `condExp_band_second_moment`
  (`Probability/Martingales/PointwiseBracket.lean`).

Not proved: Girsanov's theorem is proved for bounded predictable `θ`; Novikov's condition and the
general progressive `θ` are not. Itô's formula for a general continuous semimartingale and a
quadratic-variation process are not proved; the Itô process is built from one Brownian motion
with continuous coefficients. In the Brownian market the hedge is not identified with an explicit
integrand (Clark–Ocone, [#182](https://github.com/formal-applied-math/formal-mathfin/issues/182)),
and the converse of completeness (uniqueness of the pricing measure implies completeness) is not
proved. Stochastic differential equations are solved as a fixed point in `L²` of predictable
processes, not as a process with continuous adapted paths.

## III. Generator and PDE

A price is both a risk-neutral expectation and the solution of a PDE. The bridge is the
infinitesimal generator: Itô's formula gives the Kolmogorov backward equation, and Feynman–Kac
identifies the expectation with its solution. In the library the constant-coefficient case is
proved through the heat kernel.

* Root: `heatKernel` and its derivative lemmas
  (`Probability/Gaussian/FeynmanKacHeatEquation.lean`).
* Where it works: `bsV_satisfies_bs_pde_via_feynmanKac`
  (`Models/BlackScholes/PDEFromFeynmanKac.lean`), the Black–Scholes price satisfies the
  Black–Scholes PDE by reading it off the Feynman–Kac form; `discountedCallBrownian_heat_equation`
  (`Models/BlackScholes/PDEFromIto.lean`), the PDE in the Brownian coordinate.

Not proved: a general generator framework. Feynman–Kac is not stated for an arbitrary diffusion
with a Kolmogorov backward equation of which the Black–Scholes PDE, the heat equation and the
Vasicek PDE would be instances, and the step from a local-martingale form of Itô's formula to the
PDE is not carried out in general.

## IV. Intensities and exponential families

Closed forms come from Gaussian and exponential structure, and one construction recurs: the
exponential of an integrated intensity. It is a discount factor when the intensity is a rate, a
survival probability when it is a hazard or a force of mortality, and the survival function of the
first arrival when it is a Poisson rate. The exponential tilt is the other recurring device; it is
the Esscher transform, a change of measure by an exponential density.

* Root: `rate_eq_neg_log_deriv`, `survivalFromIntensity` and
  `hasDerivAt_neg_log_survivalFromIntensity`
  (`Probability/Analysis/ExponentialDiscount.lean`).
* Mortality and credit are the same object: `survivalFunction_eq_hazardSurvival`
  (`Insurance/SurvivalUnification.lean`); the Cox default time `coxDefaultTime` for a deterministic
  intensity (`Models/Credit/Cox.lean`).
* The tilt: `gaussianReal_withDensity_esscher` (`Models/BlackScholes/GaussianGirsanov.lean`), and
  `esscherPremium_eq_price` (`Insurance/EsscherPremium.lean`), the Esscher premium as a price
  under the tilted measure. That theorem is the joint of valuation and risk for premium
  principles.

Not proved: intensities are deterministic. A stochastic (doubly stochastic) intensity is not
constructed, and the discrete Esscher tilt is not unified with the continuous Girsanov change of
measure.

## Seams between the methods

Proved connections:

* I and II. The pricing measure of the Black–Scholes market is an explicit Girsanov density
  (`bs_discounted_isQMartingale`), and martingale representation gives attainability by a unique
  hedge when σ is almost everywhere nonzero (`martingale_representation`,
  `exists_replicating_strategy_in_price`).
* I and IV. The numéraire measure (`numeraireMeasure`, `Pricing/Numeraire.lean`) gives the
  Black–Scholes stock numéraire (`Models/BlackScholes/StockNumeraire.lean`), and the change of
  numéraire (`changeOfNumeraire`) prices Margrabe's exchange option
  (`Models/BlackScholes/ExchangeOption.lean`); the log-optimal
  portfolio is the numéraire portfolio in the discrete Kelly market
  (`kellyMarket_numeraire_portfolio`, `Choice/Performance/KellyNumeraire.lean`).
* II and III. The Black–Scholes PDE is derived from the Feynman–Kac form
  (`bsV_satisfies_bs_pde_via_feynmanKac`).
* Discrete and continuous. The binomial price of a call converges to the Black–Scholes price
  (`binomialPrice_call_tendsto_bs`, `Models/Binomial/CRRCharFun.lean`), by characteristic
  functions and Lévy's continuity theorem. Donsker's invariance principle is not formalized.
* Valuation and risk. `superhedgingPrice_isLUB` and `esscherPremium_eq_price`.

Open connections:

* The continuous numéraire-portfolio theorem (Long, Platen), which needs a state-price-density
  model.
* The finite-state dual of choice (marginal utility as a state-price density) and the
  Hansen–Jagannathan bound, which join convex duality to the choice limb.
* A general generator abstraction joining II and III.
* Stochastic intensity joining IV to the Brownian calculus of II.

The stated and unproved results are the [frontier](glossary.md#frontier) nodes of
[`blueprint.md`](blueprint.md).
