# Blueprint — the map of what is proved and what is stated next

This page is the [blueprint](glossary.md#blueprint): a map of the library's main results and of the
results stated next. It answers two questions. For a reader, which theorems carry the rest and
where is each one in Lean. For a contributor, where a new result fits and what it can build on.
The same page, with clickable nodes, is the
[blueprint page of the docs site](https://formal-applied-math.github.io/formal-mathfin/blueprint.html);
the [program tree](glossary.md#program-tree) draws the same nodes as a tree with the corpus entries
as its leaves.

## How to read the graph and the table

Each box in the graph below is a [node](glossary.md#node): one result or one shared definition,
with a label such as `thm:ito-formula-c2` or `def:emm`. An arrow runs from a result to a result
that uses it. The arrows are not drawn by hand. They are read from the Lean proof terms: an arrow
appears when the proof of one tagged declaration consumes another, passing through untagged
helper lemmas. Prose that says one result rests on another leaves no arrow unless the proof does,
and where the two disagree the graph is right. A node with no incoming arrow is a root: its proof
uses no other node.

There are three kinds of node.

- Proved (green, or blue for a result consumed from Mathlib or BrownianMotion). The node is a
  declaration tagged `@[blueprint]` in [`MathFin/Blueprint.lean`](../MathFin/Blueprint.lean). The
  headline declarations are also pinned axiom-clean in
  [`AxiomAudit.lean`](../MathFin/AxiomAudit.lean). Orange marks a result proved in part, with the
  missing step named in its file. The proved nodes that the other results rest on, joined through
  the objects and theorems they share, form the [spine](glossary.md#spine); the
  [landmarks](glossary.md#landmark) are its headline statements, listed with their scope on the
  [landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html).
- Frontier (yellow, grouped by area, marked ⏳). The node is a result that is stated and not yet
  formalized, with its entry in [`blueprint_frontier.toml`](blueprint_frontier.toml). A frontier
  node is not proved, and its sentence is a statement of what proving it would establish.
- Retired. A label that was once a node and was folded into a larger one, recorded in
  [`blueprint_retired.toml`](blueprint_retired.toml) so that issues which named it stay valid. A
  retired label does not appear in the graph.

The table under the graph lists every node with its status and a link, `issues`, to the GitHub
issues and pull requests whose body names the node. The link is a live search, not a copy.

Two relations to the rest of the library. A proved node reaches the corpus entries whose proofs
cite its declaration, so the program tree shows which entries rest on which node. Of the proved
nodes, those that no recorded edge ties to the part of the graph holding Brownian motion are the
[islands](glossary.md#island); a tagged node joins the tree through a shared object its proof uses
or a bridge theorem that uses it, and the number of islands is held down by a
[ratchet](glossary.md#ratchet). The distance of a result from the [trunk](glossary.md#trunk), and
the [sockets](glossary.md#socket) where a [model family](glossary.md#model-family) meets a market,
are drawn on the tree and described in the [glossary](glossary.md).

## Where a new result fits

Search the declaration index and this table first (`python3 -m tools.verify.find <term>`). A result
that extends a proved node lands in the [limb](glossary.md#limb) of the library it belongs to and,
when it is a landmark or a joint between limbs, is tagged in `MathFin/Blueprint.lean`. A result the
library does not yet have gets a frontier entry before any Lean is written; see
[The frontier](#the-frontier) below. [`coverage.md`](coverage.md) catalogues the remaining results
with their faithfulness status.

<!-- BEGIN GENERATED SPINE (tools/blueprint_render.py — do not hand-edit) -->
```mermaid
graph TD
  brownianMotion["Brownian motion (Mathlib, upstream)"]:::upstream
  chainLadderPrediction["Chain-ladder prediction"]:::proved
  coinFlipMeasure["The coin-flip path law"]:::proved
  contract["Contract"]:::proved
  convexRiskMeasure["Convex risk measure"]:::proved
  copula["Copula"]:::proved
  emm["Equivalent martingale measure"]:::proved
  expectedUtility["Expected utility"]:::proved
  gbm["Geometric Brownian motion"]:::proved
  hazardSurvival["Survival curve of a hazard rate"]:::proved
  hestonTransform["The explicit Heston transform"]:::proved
  lawInvariant["Law-invariant risk functional"]:::proved
  market["Market"]:::proved
  portfolioVariance["Portfolio variance"]:::proved
  quantile["Quantile function"]:::proved
  riskContribution["Risk contribution"]:::proved
  sharpeRatio["Sharpe ratio"]:::proved
  snellEnvelope["Snell envelope"]:::proved
  standardNormalCdf["Standard normal distribution function Φ"]:::proved
  survivalFunction["Survival function"]:::proved
  v3PositionValue["Value of a concentrated-liquidity position"]:::proved
  bondImmunization["Duration and immunization"]:::proved
  carrMadan["Carr–Madan spanning identity"]:::proved
  changeOfNumeraire["Change of numéraire"]:::proved
  compoundPoissonMgf["Compound Poisson moment generating function"]:::proved
  coneSeparation["Separation theorem for closed convex cones"]:::proved
  doobDecomposition["Doob decomposition"]:::proved
  doobMaximalInequality["Doob's $L^p$ maximal inequality"]:::proved
  empiricalCdfStrongLaw["Strong law for the empirical distribution function"]:::proved
  esscherTilt["Esscher transform of a Gaussian"]:::proved
  feynmanKacHeatEq["Feynman–Kac formula for the heat equation"]:::proved
  kellyCriterion["The Kelly fraction is a critical point of the growth rate"]:::proved
  keyRateDuration["Key-rate durations"]:::proved
  kktSufficiency["Karush–Kuhn–Tucker sufficiency for convex quadratic programs"]:::proved
  markovPathLaw["Ionescu–Tulcea theorem: the law of a Markov chain"]:::proved
  martingaleTransform["Martingale transform"]:::proved
  optionalSampling["Optional sampling theorem"]:::proved
  sdfCapmHansenJagannathan["CAPM from a discount factor affine in the market return"]:::proved
  stiemke["Stiemke's lemma"]:::proved
  superhedgingPriceLowerBound["The superhedging price dominates every martingale price"]:::proved
  utilityStatePriceDensity["Marginal utility is a state-price density"]:::proved
  vasicekBondPde["The Vasicek bond price solves the term-structure equation"]:::proved
  americanPrice["The American price of an exercise right"]:::proved
  coherentRiskMeasure["Coherent risk measure"]:::proved
  contractValue["Value of a contract"]:::proved
  hjmModel["Heath–Jarrow–Morton model"]:::proved
  itoIntegralClm["Itô integral and Itô isometry"]:::proved
  mertonDefaultProbability["Merton's default probability"]:::proved
  pricingMeasure["Pricing measure"]:::proved
  valueAtRisk["Value-at-risk"]:::proved
  americanPriceSnellEnvelope["The binomial American price is the Snell envelope"]:::proved
  americanPutOptimalExercise["Optimal exercise of the American put"]:::proved
  binomialBarrierReflection["Binomial barrier prices via reflection"]:::proved
  binomialRepresentation["Martingale representation in the binomial model"]:::proved
  bracketCompensator["Bracket of the Itô integral"]:::proved
  breedenLitzenberger["Breeden–Litzenberger formula"]:::proved
  brownianDoobMaximal["Doob's maximal inequality for Brownian motion on a grid"]:::proved
  bsDelta["Black–Scholes Greeks"]:::proved
  bsPde["The Black–Scholes formula solves the Black–Scholes equation"]:::proved
  buhlmannCredibility["Bühlmann credibility"]:::proved
  capmEquilibrium["CAPM beta relation, given tangency of the market portfolio"]:::proved
  coinFlipMarkov["The coin-flip law is a Markov chain's path law"]:::proved
  continuousFtap["An equivalent martingale measure excludes simple arbitrage in continuous time"]:::proved
  dupireZeroRates["Dupire's formula at zero rates, from the conditional local variance"]:::proved
  entropicRiskCertaintyEquivalent["Entropic risk is the certainty equivalent of exponential utility"]:::proved
  expectedUtilityAxioms["Expected utility satisfies independence and continuity"]:::proved
  expectedUtilityIntegral["Expected utility is the integral against the lottery"]:::proved
  firstFtap["First fundamental theorem on a finite space (Harrison–Pliska)"]:::proved
  forwardMeasure["Forward measure"]:::proved
  frechetHoeffding["Fréchet–Hoeffding bounds"]:::proved
  gaussianQuantile["Gaussian quantile function"]:::proved
  girsanovBrownianCharacterisation["Girsanov's theorem"]:::proved
  hansenJagannathanBound["The Hansen–Jagannathan bound"]:::proved
  hestonPde["The explicit Heston transform solves the pricing equation"]:::proved
  intensityDefaultModel["Intensity model of default"]:::proved
  jumpDiffusionIncompleteness["Incompleteness of jump-diffusion markets"]:::proved
  jumpDiffusionMixing["Merton's jump-diffusion formula"]:::proved
  largePortfolioLimit["Vasicek's large-portfolio limit"]:::proved
  levyCharacterization["Lévy's characterization of Brownian motion"]:::proved
  lifeInsuranceEpv["Whole-life insurance and the life annuity-due: A = 1 − d ä"]:::proved
  mackChainLadder["Mack's model: the chain-ladder predictions are a martingale"]:::proved
  margrabe["Margrabe's exchange option formula"]:::proved
  markowitzLagrangian["Markowitz mean–variance optimality"]:::proved
  marshallOlkin["Marshall–Olkin first-to-default"]:::proved
  martingaleConvergence["Convergence of L²-bounded martingales"]:::proved
  mertonRiskNeutralDrift["Risk-neutral drift of a jump-diffusion"]:::proved
  quadraticVariation["Quadratic variation of Brownian motion"]:::proved
  quantileTransform["Quantile transform and probability integral transform"]:::proved
  riskParityFoc["The log-barrier first-order condition gives risk parity"]:::proved
  schwartzCommodityFutures["Schwartz commodity futures price"]:::proved
  sdePathwiseUniqueness["Pathwise uniqueness for Itô SDEs with Lipschitz coefficients"]:::proved
  sdeStrongSolution["Existence and uniqueness of solutions of Lipschitz SDEs"]:::proved
  snellDoobDecomposition["Doob decomposition of the Snell envelope"]:::proved
  snellEnvelope["Snell's theorem: the envelope is the value of optimal stopping"]:::proved
  snellOptionalSampling["Optional sampling under the Snell envelope"]:::proved
  thieleReserve["Thiele's differential equation"]:::proved
  unilateralCva["Credit valuation adjustment"]:::proved
  uniswapV3CoveredCall["A concentrated-liquidity position is dominated by a covered call"]:::proved
  varianceSwapJumpBias["Variance swap and the log contract"]:::proved
  willowTreeBrownianCovariance["The willow tree reproduces Brownian covariance"]:::proved
  expectedShortfall["Expected shortfall"]:::proved
  gaussianFactorCopula["One-factor Gaussian copula"]:::proved
  pricingFunctional["The pricing functional"]:::proved
  aaveLiquidationKmv["Liquidation of a lending position is Merton default"]:::proved
  binomialAmericanMarket["The binomial American put is the market's American price"]:::proved
  blackScholesMarket["Black–Scholes is a market"]:::proved
  black76Caplet["Black's caplet formula, given a lognormal forward rate"]:::proved
  coherentRiskRepresentation["Robust representation of coherent risk measures on a finite space"]:::proved
  conditionalExpectationPricingMeasure["A conditional-expectation process is priced by its own measure"]:::proved
  creditPortfolioIsMerton["The one-factor credit portfolio is Merton's"]:::proved
  crrBsConvergence["Cox–Ross–Rubinstein convergence to Black–Scholes"]:::proved
  dmwFtap["Dalang–Morton–Willinger FTAP for one asset on a general space"]:::proved
  gaussianPortfolioVar["Value-at-risk of a Gaussian portfolio"]:::proved
  itoFormulaC2["Itô's formula"]:::proved
  logUtilityAcceptance["Acceptance sets from expected utility"]:::proved
  marketFtap["The fundamental theorem of asset pricing for a market"]:::proved
  martingaleRepresentation["Martingale representation theorem"]:::proved
  mertonStructuralDefault["Merton's structural model of default"]:::proved
  oneDateMarket["The one-date market and its pricing measures"]:::proved
  physicalMeasurePricing["Black–Scholes pricing under the physical measure"]:::proved
  potentialFutureExposure["Potential future exposure"]:::proved
  premiumIsPrice["The life annuity-due is a contract value"]:::proved
  putCallParity["Put-call parity"]:::proved
  secondFtap["Second fundamental theorem on a finite space"]:::proved
  sklar["Sklar's theorem"]:::proved
  stochasticFubini["Stochastic Fubini theorem for the Itô integral"]:::proved
  superhedgingCoherent["The superhedging price is a coherent risk measure"]:::proved
  tangentPortfolioEfficient["Tangent portfolio"]:::proved
  trancheLegPrice["A CDO tranche leg is a contract"]:::proved
  varNotSubadditive["Value-at-risk is not subadditive"]:::proved
  vasicekMarket["The Vasicek bond market"]:::proved
  americanPutBoundaryConvex["Convexity of the American put exercise boundary"]:::proved
  americanPutDominatesEuropean["The American put value dominates the Black–Scholes European price"]:::proved
  bachelierCall["Bachelier call price formula"]:::proved
  balancerInvariant["Balancer constant-mean AMM"]:::proved
  binomialKnockInMarket["The binomial market prices the knock-in by reflection"]:::proved
  bsAmericanMarket["The Black–Scholes market's American put is the canonical American put"]:::proved
  bsCall["The Black–Scholes price of a call in the Black–Scholes market"]:::proved
  bsDeltaHedge["Black–Scholes delta hedging"]:::proved
  esscherPremiumIsPrice["The Esscher premium is a price"]:::proved
  eulerAllocation["Euler allocation of Gaussian value at risk"]:::proved
  expectedShortfallCoherent["Expected shortfall is a law-invariant coherent risk measure"]:::proved
  expectedShortfallDual["Dual representation of expected shortfall"]:::proved
  expectedShortfallNotElicitable["Expected shortfall is not elicitable"]:::proved
  glostenMilgromPricingMeasure["The Glosten–Milgrom quote sequence is a martingale for the dealer's measure"]:::proved
  hedgedPositionRisk["Risk of a hedged position"]:::proved
  hestonBsMarketLimit["As vol-of-vol vanishes the Heston transform is a Black–Scholes price"]:::proved
  hoeffdingCovariance["Hoeffding's covariance identity"]:::proved
  insuredMarket["The insured market and its Esscher pricing measure"]:::proved
  interestRateParity["Covered interest-rate parity"]:::proved
  itoProductRule["Itô's product rule"]:::proved
  jumpDiffusionMarket["The jump-diffusion market at one date"]:::proved
  jumpDiffusionPrice["Jump-diffusion prices under the Esscher pricing measure"]:::proved
  lpPositionPrice["An AMM liquidity position is a contract"]:::proved
  marginalUtilityIsSdf["Marginal utility is the stochastic discount factor of a complete market"]:::proved
  marketCallPriceNormalized["A pricing measure gives a normalised call price function"]:::proved
  marketCallSurface["Breeden–Litzenberger for a market's call prices"]:::proved
  marketCarrMadan["Carr–Madan replication in a market"]:::proved
  marketCompleteness["Brownian market: the superreplication price is the market price"]:::proved
  marketDupire["Dupire's formula for a market's call prices, at zero rates"]:::proved
  marketHansenJagannathan["The Hansen–Jagannathan bound for a market with a pricing measure"]:::proved
  marketSdfCapm["The security market line for a market with a pricing measure"]:::proved
  quantileElicitability["Elicitability of the quantile"]:::proved
  rockafellarUryasev["Rockafellar–Uryasev formula"]:::proved
  smileNoArbitrage["Roper's converse: every normalised call price function is a market's"]:::proved
  superhedgingDuality["Superhedging duality, one period and finitely many states"]:::proved
  timeDependentVolMarket["Black–Scholes with a deterministic volatility clock is a market"]:::proved
  trinomialMomentMatching["Trinomial lattice step as a pricing measure"]:::proved
  vasicekPriceSolvesPde["The Vasicek market price solves the Vasicek PDE"]:::proved
  zeroCouponBondPrice["The zero-coupon bond price is a price"]:::proved
  bsArbitrageFreePrice["Uniqueness of the Black–Scholes pricing measure among square-integrable densities"]:::proved
  fisslerZiegel["A strictly consistent score for value at risk and expected shortfall"]:::proved
  glostenMilgromQuote["Glosten–Milgrom bid and ask quotes"]:::proved
  immunizationMarketPrice["Immunization for market prices"]:::proved
  impermanentLoss["Impermanent loss"]:::proved
  jumpDiffusionMarketIncomplete["The jump-diffusion market has two pricing measures"]:::proved
  keyRateMarketPrice["Key-rate durations for market prices"]:::proved
  logOptimalNumeraireOnePeriod["A stationary log portfolio is the numéraire portfolio, one period"]:::proved
  quotesMarketRealisation["Arbitrage-free call quotes are the prices of a market"]:::proved
  sviMarketRealisation["A butterfly-free SVI slice is a market"]:::proved
  kellyIsLogOptimal["The Kelly wealth is the numéraire portfolio of the betting market"]:::proved
  subgraph frontier_choiceDynamic["⏳ frontier · Choice · Dynamic choice"]
    relaxedControlledDiffusion["Relaxed controlled diffusions"]:::frontier
    logOptimalNumeraire["Log-optimal portfolio is the numéraire"]:::frontier
    mertonPortfolioFraction["Merton myopic risky fraction"]:::frontier
    timeInconsistentEquilibrium["Relaxed equilibria under time inconsistency"]:::frontier
  end
  subgraph frontier_choiceEquilibrium["⏳ frontier · Choice · Equilibrium"]
    aptPricing["APT exact-factor pricing"]:::frontier
  end
  subgraph frontier_choicePortfolio["⏳ frontier · Choice · Portfolio choice"]
    markowitzKktNecessity["Markowitz first-order conditions are necessary"]:::frontier
    riskParityNAsset["N-asset risk parity exists and is unique"]:::frontier
  end
  subgraph frontier_choicePreferences["⏳ frontier · Choice · Preferences"]
    expectedUtilityRiskAversion["Expected utility and risk aversion"]:::frontier
    vonNeumannMorgenstern["von Neumann–Morgenstern representation theorem"]:::frontier
  end
  subgraph frontier_choiceTrading["⏳ frontier · Choice · Market microstructure"]
    kyleEquilibrium["Kyle single-period equilibrium"]:::frontier
    kyleEquilibriumUnique["Uniqueness of the Kyle equilibrium"]:::frontier
    propagatorNoArbitrage["Transient-impact propagator no-arbitrage"]:::frontier
  end
  subgraph frontier_market["⏳ frontier · Positions and markets"]
    delbaenSchachermayer["Delbaen–Schachermayer: no free lunch with vanishing risk"]:::frontier
    dmwMultiAsset["Dalang–Morton–Willinger for several assets"]:::frontier
    secondFtapConverse["Second FTAP: uniqueness implies completeness"]:::frontier
  end
  subgraph frontier_probabilityBrownian["⏳ frontier · Probability · Brownian calculus"]
    pathSignature["Signatures of paths"]:::frontier
    bracketQuadraticVariation["Bracket is the quadratic variation of an Itô integral"]:::frontier
    brownianNowhereDifferentiable["Brownian paths are nowhere differentiable"]:::frontier
    clarkOcone["L¹ martingale representation and Clark–Ocone"]:::frontier
    expectedSignatureMomentProblem["Expected signature of stopped Brownian motion"]:::frontier
    feynmanKacVariableCoefficient["Variable-coefficient Feynman–Kac"]:::frontier
    itoFormula2d["Two-process Itô formula"]:::frontier
    itoIntegralMartingale["General-integrand Itô process is a martingale"]:::frontier
    lawIteratedLogarithm["Law of the iterated logarithm"]:::frontier
    martingaleRepresentationVector["Vector martingale representation"]:::frontier
    novikovGirsanov["Novikov Girsanov for unbounded θ"]:::frontier
    reflectionPrinciple["Reflection principle for Brownian motion"]:::frontier
    sdeContinuousSolution["Continuous strong solutions on every horizon"]:::frontier
    stochasticFubiniProcess["Stochastic Fubini for the integral process"]:::frontier
  end
  subgraph frontier_probabilityDependence["⏳ frontier · Probability · Dependence"]
    sklarGeneral["Sklar's theorem for arbitrary margins"]:::frontier
  end
  subgraph frontier_probabilityDiscrete["⏳ frontier · Probability · Discrete time"]
    perronFrobeniusMarkov["Perron–Frobenius and finite Markov chain ergodicity"]:::frontier
  end
  subgraph frontier_probabilityGaussian["⏳ frontier · Probability · Gaussian analysis"]
    realErf["erf / erfc / erfinv for Mathlib"]:::frontier
  end
  subgraph frontier_probabilityJumps["⏳ frontier · Probability · Jumps"]
    compensatedPoissonIntegral["Compensated-Poisson integral"]:::frontier
    itoLevyFormula["Itô–Lévy change of variables"]:::frontier
    jumpDiffusionLaw["Compound-Poisson and jump-diffusion law"]:::frontier
    poissonInterarrivalIid["Poisson interarrivals are iid exponential"]:::frontier
    stochasticFubiniLevy["Stochastic Fubini for Itô–Lévy integrals"]:::frontier
  end
  subgraph frontier_probabilityMartingales["⏳ frontier · Probability · Continuous martingales"]
    markovMartingale["Markov martingales"]:::frontier
    semimartingaleIntegral["The stochastic integral against a semimartingale"]:::frontier
  end
  subgraph frontier_riskAggregation["⏳ frontier · Risk · Aggregation and diversification"]
    boundedLawCompleteMixability["Complete mixability of bounded absolutely continuous laws"]:::frontier
    convexOrderMinimalSum["Convex-order minimal sums"]:::frontier
    uniformConvexCompleteMixability["Complete mixability of uniform laws on convex bodies"]:::frontier
  end
  subgraph frontier_riskCredit["⏳ frontier · Risk · Credit portfolio risk"]
    aaveHealthFactorBound["Aave multi-asset health factor: a liquidation bound"]:::frontier
    largePoolLoss["Large homogeneous pool loss law"]:::frontier
    liquidationFirstPassage["Liquidation before maturity as first passage"]:::frontier
    oneFactorCopulaDefault["One-factor Gaussian copula default"]:::frontier
  end
  subgraph frontier_riskInsurance["⏳ frontier · Risk · Collective risk theory"]
    optimalDividendProblem["Optimal dividend problems"]:::frontier
    cramerLundbergClaims["Cramér–Lundberg claims"]:::frontier
    lundbergRuinBound["Lundberg ruin bound"]:::frontier
    multidimensionalDividendBoundary["Optimal dividends of several insurers on the free boundary"]:::frontier
    panjerRecursion["Panjer recursion"]:::frontier
  end
  subgraph frontier_riskMeasures["⏳ frontier · Risk · Risk measures"]
    delbaenRepresentation["Delbaen's representation of coherent risk measures"]:::frontier
    kusuoka["Kusuoka representation"]:::frontier
    riskMeasureFamilies["Entropic, distortion and expectile risk measures"]:::frontier
  end
  subgraph frontier_statistics["⏳ frontier · Statistics"]
    zakaiEquation["The Zakai equation"]:::frontier
    glivenkoCantelli["Glivenko–Cantelli theorem"]:::frontier
    purgedCvIndependence["Purged cross-validation: σ-algebra independence"]:::frontier
    quantileConvergenceInDistribution["Quantiles under convergence in distribution"]:::frontier
    zakaiUniquenessSingularControl["Zakai uniqueness under singular control"]:::frontier
  end
  subgraph frontier_valuationAmerican["⏳ frontier · Valuation · American options and optimal stopping"]
    americanPutPremium["American put early-exercise premium"]:::frontier
    americanPutSuperhedgingPrice["The American put value is the superhedging price"]:::frontier
    perpetualAmerican["Perpetual American option"]:::frontier
    robustAmericanIrregularDuality["Robust American hedging with irregular payoffs"]:::frontier
  end
  subgraph frontier_valuationDefault["⏳ frontier · Valuation · Credit"]
    supercooledStefanSolution["Physical solutions of the supercooled Stefan problem"]:::frontier
    blackCoxDefault["Black–Cox first-passage default"]:::frontier
    cvaIsPrice["CVA is the price of the default loss"]:::frontier
    mertonCreditSpread["Merton structural credit spread"]:::frontier
    stefanUniqueness["Stefan uniqueness with accumulating jumps"]:::frontier
  end
  subgraph frontier_valuationDiffusions["⏳ frontier · Valuation · Black–Scholes and Bachelier"]
    barrierLookbackClosedForms["Barrier and lookback closed forms"]:::frontier
    forwardStartCall["Forward-start call"]:::frontier
    girsanovContinuousEmm["Girsanov EMM from the Itô tower"]:::frontier
    margrabeNumeraire["Margrabe and chooser via the S²-numéraire"]:::frontier
    twoAssetOptionFormulas["Stulz and Heynen–Kat two-asset formulas"]:::frontier
  end
  subgraph frontier_valuationForwards["⏳ frontier · Valuation · Forwards, FX and commodities"]
    futuresBasisConvergence["Contango, backwardation and basis convergence"]:::frontier
    futuresForwardConvexity["Futures–forward convexity adjustment"]:::frontier
    siegelParadox["Siegel's paradox"]:::frontier
  end
  subgraph frontier_valuationGeneral["⏳ frontier · Valuation · Arbitrage pricing"]
    calibratedMartingaleMeasures["Calibrated martingale measures of finite entropy"]:::frontier
    semistaticStrategy["Semistatic trading strategies"]:::frontier
    semistaticFtap["Semistatic FTAP with entropy"]:::frontier
    varianceOptimalHedging["Variance-optimal hedging"]:::frontier
  end
  subgraph frontier_valuationInsurance["⏳ frontier · Valuation · Life contingencies"]
    survivalModel["Survival model and life tables"]:::frontier
  end
  subgraph frontier_valuationJumps["⏳ frontier · Valuation · Jump models"]
    esscherEmmLevy["Esscher EMM for exponential-Lévy markets"]:::frontier
    kouJumpDiffusion["Kou double-exponential jump-diffusion"]:::frontier
    mertonPide["Merton PIDE"]:::frontier
    varianceGammaCall["Variance-gamma European call"]:::frontier
  end
  subgraph frontier_valuationModelFree["⏳ frontier · Valuation · Static replication and model-free bounds"]
    convexOrder["Convex order"]:::frontier
    nondominatedModel["Nondominated models"]:::frontier
    compoundExchangeRateBridge["Compound's exchange rate as a money-market account"]:::frontier
    modelFreeVariance["Model-free implied variance replication"]:::frontier
    rawFiltrationMimickingMartingale["Mimicking Markov martingales for the raw filtration"]:::frontier
  end
  subgraph frontier_valuationSmile["⏳ frontier · Valuation · The smile"]
    sabrModel["The SABR model"]:::frontier
    carrLeeMoment["Carr–Lee moment formula"]:::frontier
    impliedVolExistence["Implied volatility for every arbitrage-free price"]:::frontier
    sabrRightTailCorrection["SABR right tail: the k^{3/2} correction"]:::frontier
  end
  subgraph frontier_valuationTerm["⏳ frontier · Valuation · Interest rates"]
    affineTermStructure["Affine term structure"]:::frontier
    bermudanCallableSnell["Callable bonds and Bermudan swaptions by Snell envelope"]:::frontier
    cirBondLoadings["CIR bond-price loadings"]:::frontier
    cmsConvexityAdjustment["CMS convexity adjustment"]:::frontier
    hjmAffineModels["HJM recovers Ho–Lee and Vasicek"]:::frontier
    hjmBondDynamics["HJM bond-price dynamics"]:::frontier
    hjmDriftCondition["HJM drift condition"]:::frontier
    hjmLogBondDynamics["HJM log-bond dynamics"]:::frontier
    hjmMusiela["HJM Musiela parametrization"]:::frontier
    hjmShortRate["HJM induces a short-rate model"]:::frontier
    lmmForwardMartingale["LIBOR market model forward martingale"]:::frontier
  end
  subgraph frontier_valuationTrees["⏳ frontier · Valuation · Trees"]
    robustBinomialDuality["Quasi-sure duality for the robust multi-period binomial model"]:::frontier
  end
  subgraph frontier_valuationVolatility["⏳ frontier · Valuation · Volatility models"]
    stochasticVolterraEquation["Stochastic Volterra equations"]:::frontier
    batesCf["Bates characteristic function"]:::frontier
    cevCall["CEV European call"]:::frontier
    dupireLocalVol["Dupire local volatility"]:::frontier
    hestonCf["Heston characteristic function"]:::frontier
    roughHestonPathwiseUniqueness["Rough-Heston pathwise uniqueness"]:::frontier
    sabrHagan["SABR Hagan asymptotic implied vol"]:::frontier
    schrodingerSpxVix["Schrödinger calibration of SPX/VIX"]:::frontier
  end

  market --> americanPrice
  convexRiskMeasure --> coherentRiskMeasure
  contract --> contractValue
  brownianMotion --> hjmModel
  brownianMotion --> itoIntegralClm
  standardNormalCdf --> mertonDefaultProbability
  market --> pricingMeasure
  quantile --> valueAtRisk
  coinFlipMeasure --> americanPriceSnellEnvelope
  snellEnvelope --> americanPriceSnellEnvelope
  brownianMotion --> americanPutOptimalExercise
  snellEnvelope --> americanPutOptimalExercise
  coinFlipMeasure --> binomialBarrierReflection
  coinFlipMeasure --> binomialRepresentation
  brownianMotion --> bracketCompensator
  carrMadan --> breedenLitzenberger
  brownianMotion --> brownianDoobMaximal
  doobMaximalInequality --> brownianDoobMaximal
  standardNormalCdf --> bsDelta
  standardNormalCdf --> bsPde
  portfolioVariance --> buhlmannCredibility
  portfolioVariance --> capmEquilibrium
  coinFlipMeasure --> coinFlipMarkov
  markovPathLaw --> coinFlipMarkov
  emm --> continuousFtap
  martingaleTransform --> continuousFtap
  brownianMotion --> dupireZeroRates
  carrMadan --> dupireZeroRates
  expectedUtility --> entropicRiskCertaintyEquivalent
  expectedUtility --> expectedUtilityAxioms
  expectedUtility --> expectedUtilityIntegral
  emm --> firstFtap
  martingaleTransform --> firstFtap
  stiemke --> firstFtap
  changeOfNumeraire --> forwardMeasure
  copula --> frechetHoeffding
  quantile --> gaussianQuantile
  brownianMotion --> girsanovBrownianCharacterisation
  sharpeRatio --> hansenJagannathanBound
  hestonTransform --> hestonPde
  hazardSurvival --> intensityDefaultModel
  compoundPoissonMgf --> jumpDiffusionIncompleteness
  standardNormalCdf --> jumpDiffusionMixing
  compoundPoissonMgf --> jumpDiffusionMixing
  quantile --> largePortfolioLimit
  standardNormalCdf --> largePortfolioLimit
  empiricalCdfStrongLaw --> largePortfolioLimit
  brownianMotion --> levyCharacterization
  survivalFunction --> lifeInsuranceEpv
  chainLadderPrediction --> mackChainLadder
  emm --> mackChainLadder
  standardNormalCdf --> margrabe
  esscherTilt --> margrabe
  portfolioVariance --> markowitzLagrangian
  kktSufficiency --> markowitzLagrangian
  hazardSurvival --> marshallOlkin
  survivalFunction --> marshallOlkin
  doobMaximalInequality --> martingaleConvergence
  compoundPoissonMgf --> mertonRiskNeutralDrift
  brownianMotion --> quadraticVariation
  quantile --> quantileTransform
  riskContribution --> riskParityFoc
  brownianMotion --> schwartzCommodityFutures
  brownianMotion --> sdePathwiseUniqueness
  brownianMotion --> sdeStrongSolution
  snellEnvelope --> snellDoobDecomposition
  doobDecomposition --> snellDoobDecomposition
  snellEnvelope --> snellEnvelope
  snellEnvelope --> snellOptionalSampling
  optionalSampling --> snellOptionalSampling
  hazardSurvival --> thieleReserve
  hazardSurvival --> unilateralCva
  standardNormalCdf --> unilateralCva
  v3PositionValue --> uniswapV3CoveredCall
  compoundPoissonMgf --> varianceSwapJumpBias
  brownianMotion --> willowTreeBrownianCovariance
  valueAtRisk --> expectedShortfall
  copula --> gaussianFactorCopula
  quantile --> gaussianFactorCopula
  standardNormalCdf --> gaussianFactorCopula
  quantileTransform --> gaussianFactorCopula
  contract --> pricingFunctional
  contractValue --> pricingFunctional
  market --> pricingFunctional
  mertonDefaultProbability --> aaveLiquidationKmv
  standardNormalCdf --> aaveLiquidationKmv
  americanPrice --> binomialAmericanMarket
  coinFlipMeasure --> binomialAmericanMarket
  market --> binomialAmericanMarket
  snellEnvelope --> binomialAmericanMarket
  americanPriceSnellEnvelope --> binomialAmericanMarket
  snellEnvelope --> binomialAmericanMarket
  brownianMotion --> blackScholesMarket
  gbm --> blackScholesMarket
  market --> blackScholesMarket
  pricingMeasure --> blackScholesMarket
  girsanovBrownianCharacterisation --> blackScholesMarket
  contract --> black76Caplet
  contractValue --> black76Caplet
  standardNormalCdf --> black76Caplet
  forwardMeasure --> black76Caplet
  coherentRiskMeasure --> coherentRiskRepresentation
  convexRiskMeasure --> coherentRiskRepresentation
  coneSeparation --> coherentRiskRepresentation
  emm --> conditionalExpectationPricingMeasure
  market --> conditionalExpectationPricingMeasure
  pricingMeasure --> conditionalExpectationPricingMeasure
  mertonDefaultProbability --> creditPortfolioIsMerton
  quantile --> creditPortfolioIsMerton
  standardNormalCdf --> creditPortfolioIsMerton
  coinFlipMeasure --> crrBsConvergence
  contract --> crrBsConvergence
  contractValue --> crrBsConvergence
  standardNormalCdf --> crrBsConvergence
  emm --> dmwFtap
  market --> dmwFtap
  pricingMeasure --> dmwFtap
  martingaleTransform --> dmwFtap
  portfolioVariance --> gaussianPortfolioVar
  quantile --> gaussianPortfolioVar
  valueAtRisk --> gaussianPortfolioVar
  gaussianQuantile --> gaussianPortfolioVar
  brownianMotion --> itoFormulaC2
  itoIntegralClm --> itoFormulaC2
  coherentRiskMeasure --> logUtilityAcceptance
  expectedUtility --> logUtilityAcceptance
  emm --> marketFtap
  market --> marketFtap
  pricingMeasure --> marketFtap
  firstFtap --> marketFtap
  martingaleTransform --> marketFtap
  brownianMotion --> martingaleRepresentation
  itoIntegralClm --> martingaleRepresentation
  mertonDefaultProbability --> mertonStructuralDefault
  standardNormalCdf --> mertonStructuralDefault
  market --> oneDateMarket
  pricingMeasure --> oneDateMarket
  brownianMotion --> physicalMeasurePricing
  contract --> physicalMeasurePricing
  contractValue --> physicalMeasurePricing
  gbm --> physicalMeasurePricing
  quantile --> potentialFutureExposure
  valueAtRisk --> potentialFutureExposure
  gaussianQuantile --> potentialFutureExposure
  contract --> premiumIsPrice
  contractValue --> premiumIsPrice
  survivalFunction --> premiumIsPrice
  contract --> putCallParity
  contractValue --> putCallParity
  emm --> secondFtap
  firstFtap --> secondFtap
  martingaleTransform --> secondFtap
  quantile --> sklar
  quantileTransform --> sklar
  brownianMotion --> stochasticFubini
  itoIntegralClm --> stochasticFubini
  coherentRiskMeasure --> superhedgingCoherent
  convexRiskMeasure --> superhedgingCoherent
  superhedgingPriceLowerBound --> superhedgingCoherent
  portfolioVariance --> tangentPortfolioEfficient
  markowitzLagrangian --> tangentPortfolioEfficient
  contract --> trancheLegPrice
  contractValue --> trancheLegPrice
  quantile --> varNotSubadditive
  valueAtRisk --> varNotSubadditive
  brownianMotion --> vasicekMarket
  market --> vasicekMarket
  pricingMeasure --> vasicekMarket
  brownianMotion --> americanPutBoundaryConvex
  snellEnvelope --> americanPutBoundaryConvex
  americanPutOptimalExercise --> americanPutBoundaryConvex
  feynmanKacHeatEq --> americanPutBoundaryConvex
  itoFormulaC2 --> americanPutBoundaryConvex
  brownianMotion --> americanPutDominatesEuropean
  contract --> americanPutDominatesEuropean
  contractValue --> americanPutDominatesEuropean
  gbm --> americanPutDominatesEuropean
  market --> americanPutDominatesEuropean
  pricingFunctional --> americanPutDominatesEuropean
  brownianMotion --> bachelierCall
  contract --> bachelierCall
  contractValue --> bachelierCall
  market --> bachelierCall
  pricingFunctional --> bachelierCall
  standardNormalCdf --> bachelierCall
  contract --> balancerInvariant
  contractValue --> balancerInvariant
  market --> balancerInvariant
  pricingFunctional --> balancerInvariant
  coinFlipMeasure --> binomialKnockInMarket
  contract --> binomialKnockInMarket
  contractValue --> binomialKnockInMarket
  market --> binomialKnockInMarket
  pricingFunctional --> binomialKnockInMarket
  pricingMeasure --> binomialKnockInMarket
  binomialBarrierReflection --> binomialKnockInMarket
  americanPrice --> bsAmericanMarket
  brownianMotion --> bsAmericanMarket
  gbm --> bsAmericanMarket
  market --> bsAmericanMarket
  pricingMeasure --> bsAmericanMarket
  snellEnvelope --> bsAmericanMarket
  blackScholesMarket --> bsAmericanMarket
  girsanovBrownianCharacterisation --> bsAmericanMarket
  brownianMotion --> bsCall
  contract --> bsCall
  contractValue --> bsCall
  gbm --> bsCall
  market --> bsCall
  pricingFunctional --> bsCall
  standardNormalCdf --> bsCall
  girsanovBrownianCharacterisation --> bsCall
  physicalMeasurePricing --> bsCall
  brownianMotion --> bsDeltaHedge
  standardNormalCdf --> bsDeltaHedge
  bsDelta --> bsDeltaHedge
  feynmanKacHeatEq --> bsDeltaHedge
  itoFormulaC2 --> bsDeltaHedge
  contract --> esscherPremiumIsPrice
  contractValue --> esscherPremiumIsPrice
  market --> esscherPremiumIsPrice
  pricingFunctional --> esscherPremiumIsPrice
  portfolioVariance --> eulerAllocation
  quantile --> eulerAllocation
  riskContribution --> eulerAllocation
  valueAtRisk --> eulerAllocation
  gaussianPortfolioVar --> eulerAllocation
  coherentRiskMeasure --> expectedShortfallCoherent
  convexRiskMeasure --> expectedShortfallCoherent
  expectedShortfall --> expectedShortfallCoherent
  lawInvariant --> expectedShortfallCoherent
  quantile --> expectedShortfallCoherent
  valueAtRisk --> expectedShortfallCoherent
  quantileTransform --> expectedShortfallCoherent
  expectedShortfall --> expectedShortfallDual
  quantile --> expectedShortfallDual
  valueAtRisk --> expectedShortfallDual
  quantileTransform --> expectedShortfallDual
  expectedShortfall --> expectedShortfallNotElicitable
  quantile --> expectedShortfallNotElicitable
  valueAtRisk --> expectedShortfallNotElicitable
  quantileTransform --> expectedShortfallNotElicitable
  market --> glostenMilgromPricingMeasure
  pricingMeasure --> glostenMilgromPricingMeasure
  conditionalExpectationPricingMeasure --> glostenMilgromPricingMeasure
  coinFlipMeasure --> hedgedPositionRisk
  contract --> hedgedPositionRisk
  contractValue --> hedgedPositionRisk
  expectedShortfall --> hedgedPositionRisk
  quantile --> hedgedPositionRisk
  valueAtRisk --> hedgedPositionRisk
  binomialRepresentation --> hedgedPositionRisk
  brownianMotion --> hestonBsMarketLimit
  contract --> hestonBsMarketLimit
  contractValue --> hestonBsMarketLimit
  gbm --> hestonBsMarketLimit
  hestonTransform --> hestonBsMarketLimit
  market --> hestonBsMarketLimit
  pricingFunctional --> hestonBsMarketLimit
  pricingMeasure --> hestonBsMarketLimit
  blackScholesMarket --> hestonBsMarketLimit
  girsanovBrownianCharacterisation --> hestonBsMarketLimit
  copula --> hoeffdingCovariance
  quantile --> hoeffdingCovariance
  quantileTransform --> hoeffdingCovariance
  sklar --> hoeffdingCovariance
  market --> insuredMarket
  pricingMeasure --> insuredMarket
  oneDateMarket --> insuredMarket
  contract --> interestRateParity
  contractValue --> interestRateParity
  market --> interestRateParity
  pricingFunctional --> interestRateParity
  brownianMotion --> itoProductRule
  itoFormulaC2 --> itoProductRule
  market --> jumpDiffusionMarket
  pricingMeasure --> jumpDiffusionMarket
  compoundPoissonMgf --> jumpDiffusionMarket
  oneDateMarket --> jumpDiffusionMarket
  contract --> jumpDiffusionPrice
  contractValue --> jumpDiffusionPrice
  market --> jumpDiffusionPrice
  pricingFunctional --> jumpDiffusionPrice
  standardNormalCdf --> jumpDiffusionPrice
  compoundPoissonMgf --> jumpDiffusionPrice
  jumpDiffusionMixing --> jumpDiffusionPrice
  contract --> lpPositionPrice
  contractValue --> lpPositionPrice
  market --> lpPositionPrice
  pricingFunctional --> lpPositionPrice
  v3PositionValue --> lpPositionPrice
  contract --> marginalUtilityIsSdf
  contractValue --> marginalUtilityIsSdf
  market --> marginalUtilityIsSdf
  pricingFunctional --> marginalUtilityIsSdf
  pricingMeasure --> marginalUtilityIsSdf
  utilityStatePriceDensity --> marginalUtilityIsSdf
  contract --> marketCallPriceNormalized
  contractValue --> marketCallPriceNormalized
  market --> marketCallPriceNormalized
  pricingFunctional --> marketCallPriceNormalized
  pricingMeasure --> marketCallPriceNormalized
  contract --> marketCallSurface
  contractValue --> marketCallSurface
  market --> marketCallSurface
  pricingFunctional --> marketCallSurface
  pricingMeasure --> marketCallSurface
  breedenLitzenberger --> marketCallSurface
  contract --> marketCarrMadan
  contractValue --> marketCarrMadan
  market --> marketCarrMadan
  pricingFunctional --> marketCarrMadan
  pricingMeasure --> marketCarrMadan
  carrMadan --> marketCarrMadan
  brownianMotion --> marketCompleteness
  contract --> marketCompleteness
  contractValue --> marketCompleteness
  itoIntegralClm --> marketCompleteness
  market --> marketCompleteness
  pricingFunctional --> marketCompleteness
  pricingMeasure --> marketCompleteness
  brownianMotion --> marketDupire
  contract --> marketDupire
  contractValue --> marketDupire
  market --> marketDupire
  pricingFunctional --> marketDupire
  dupireZeroRates --> marketDupire
  contract --> marketHansenJagannathan
  contractValue --> marketHansenJagannathan
  market --> marketHansenJagannathan
  pricingFunctional --> marketHansenJagannathan
  pricingMeasure --> marketHansenJagannathan
  sharpeRatio --> marketHansenJagannathan
  hansenJagannathanBound --> marketHansenJagannathan
  contract --> marketSdfCapm
  contractValue --> marketSdfCapm
  market --> marketSdfCapm
  pricingFunctional --> marketSdfCapm
  pricingMeasure --> marketSdfCapm
  sdfCapmHansenJagannathan --> marketSdfCapm
  expectedShortfall --> quantileElicitability
  quantile --> quantileElicitability
  valueAtRisk --> quantileElicitability
  quantileTransform --> quantileElicitability
  expectedShortfall --> rockafellarUryasev
  quantile --> rockafellarUryasev
  valueAtRisk --> rockafellarUryasev
  quantileTransform --> rockafellarUryasev
  contract --> smileNoArbitrage
  contractValue --> smileNoArbitrage
  market --> smileNoArbitrage
  pricingFunctional --> smileNoArbitrage
  pricingMeasure --> smileNoArbitrage
  oneDateMarket --> smileNoArbitrage
  coherentRiskRepresentation --> superhedgingDuality
  superhedgingCoherent --> superhedgingDuality
  superhedgingPriceLowerBound --> superhedgingDuality
  brownianMotion --> timeDependentVolMarket
  gbm --> timeDependentVolMarket
  market --> timeDependentVolMarket
  pricingMeasure --> timeDependentVolMarket
  blackScholesMarket --> timeDependentVolMarket
  market --> trinomialMomentMatching
  pricingMeasure --> trinomialMomentMatching
  oneDateMarket --> trinomialMomentMatching
  brownianMotion --> vasicekPriceSolvesPde
  contract --> vasicekPriceSolvesPde
  contractValue --> vasicekPriceSolvesPde
  market --> vasicekPriceSolvesPde
  pricingFunctional --> vasicekPriceSolvesPde
  pricingMeasure --> vasicekPriceSolvesPde
  vasicekBondPde --> vasicekPriceSolvesPde
  vasicekMarket --> vasicekPriceSolvesPde
  contract --> zeroCouponBondPrice
  contractValue --> zeroCouponBondPrice
  market --> zeroCouponBondPrice
  pricingFunctional --> zeroCouponBondPrice
  brownianMotion --> bsArbitrageFreePrice
  contract --> bsArbitrageFreePrice
  contractValue --> bsArbitrageFreePrice
  gbm --> bsArbitrageFreePrice
  itoIntegralClm --> bsArbitrageFreePrice
  market --> bsArbitrageFreePrice
  pricingFunctional --> bsArbitrageFreePrice
  pricingMeasure --> bsArbitrageFreePrice
  standardNormalCdf --> bsArbitrageFreePrice
  blackScholesMarket --> bsArbitrageFreePrice
  bsCall --> bsArbitrageFreePrice
  girsanovBrownianCharacterisation --> bsArbitrageFreePrice
  expectedShortfall --> fisslerZiegel
  quantile --> fisslerZiegel
  valueAtRisk --> fisslerZiegel
  quantileElicitability --> fisslerZiegel
  quantileTransform --> fisslerZiegel
  market --> glostenMilgromQuote
  pricingMeasure --> glostenMilgromQuote
  glostenMilgromPricingMeasure --> glostenMilgromQuote
  contract --> immunizationMarketPrice
  market --> immunizationMarketPrice
  pricingFunctional --> immunizationMarketPrice
  bondImmunization --> immunizationMarketPrice
  zeroCouponBondPrice --> immunizationMarketPrice
  contract --> impermanentLoss
  contractValue --> impermanentLoss
  market --> impermanentLoss
  pricingFunctional --> impermanentLoss
  v3PositionValue --> impermanentLoss
  lpPositionPrice --> impermanentLoss
  contract --> jumpDiffusionMarketIncomplete
  contractValue --> jumpDiffusionMarketIncomplete
  market --> jumpDiffusionMarketIncomplete
  pricingFunctional --> jumpDiffusionMarketIncomplete
  pricingMeasure --> jumpDiffusionMarketIncomplete
  compoundPoissonMgf --> jumpDiffusionMarketIncomplete
  jumpDiffusionIncompleteness --> jumpDiffusionMarketIncomplete
  jumpDiffusionMarket --> jumpDiffusionMarketIncomplete
  oneDateMarket --> jumpDiffusionMarketIncomplete
  contract --> keyRateMarketPrice
  market --> keyRateMarketPrice
  pricingFunctional --> keyRateMarketPrice
  keyRateDuration --> keyRateMarketPrice
  zeroCouponBondPrice --> keyRateMarketPrice
  market --> logOptimalNumeraireOnePeriod
  pricingMeasure --> logOptimalNumeraireOnePeriod
  marginalUtilityIsSdf --> logOptimalNumeraireOnePeriod
  contract --> quotesMarketRealisation
  market --> quotesMarketRealisation
  pricingFunctional --> quotesMarketRealisation
  pricingMeasure --> quotesMarketRealisation
  smileNoArbitrage --> quotesMarketRealisation
  contract --> sviMarketRealisation
  market --> sviMarketRealisation
  pricingFunctional --> sviMarketRealisation
  pricingMeasure --> sviMarketRealisation
  standardNormalCdf --> sviMarketRealisation
  smileNoArbitrage --> sviMarketRealisation
  contract --> kellyIsLogOptimal
  contractValue --> kellyIsLogOptimal
  market --> kellyIsLogOptimal
  pricingFunctional --> kellyIsLogOptimal
  pricingMeasure --> kellyIsLogOptimal
  kellyCriterion --> kellyIsLogOptimal
  logOptimalNumeraireOnePeriod --> kellyIsLogOptimal
  oneDateMarket --> kellyIsLogOptimal
  emm --> calibratedMartingaleMeasures
  marketCarrMadan --> calibratedMartingaleMeasures
  marketCarrMadan --> convexOrder
  brownianMotion --> markovMartingale
  emm --> nondominatedModel
  cramerLundbergClaims --> optimalDividendProblem
  brownianMotion --> pathSignature
  standardNormalCdf --> realErf
  sdeStrongSolution --> relaxedControlledDiffusion
  sdeStrongSolution --> sabrModel
  emm --> semistaticStrategy
  marketCarrMadan --> semistaticStrategy
  itoIntegralClm --> stochasticVolterraEquation
  sdeStrongSolution --> stochasticVolterraEquation
  brownianMotion --> supercooledStefanSolution
  itoIntegralClm --> zakaiEquation
  aaveLiquidationKmv --> aaveHealthFactorBound
  vasicekBondPde --> affineTermStructure
  snellEnvelope --> americanPutPremium
  americanPutDominatesEuropean --> americanPutSuperhedgingPrice
  marketCompleteness --> americanPutSuperhedgingPrice
  emm --> aptPricing
  capmEquilibrium --> aptPricing
  reflectionPrinciple --> barrierLookbackClosedForms
  bsCall --> barrierLookbackClosedForms
  hestonCf --> batesCf
  jumpDiffusionLaw --> batesCf
  snellEnvelope --> bermudanCallableSnell
  reflectionPrinciple --> blackCoxDefault
  standardNormalCdf --> blackCoxDefault
  frechetHoeffding --> boundedLawCompleteMixability
  bracketCompensator --> bracketQuadraticVariation
  quadraticVariation --> bracketQuadraticVariation
  itoIntegralMartingale --> bracketQuadraticVariation
  brownianMotion --> brownianNowhereDifferentiable
  bsCall --> carrLeeMoment
  bsCall --> cevCall
  affineTermStructure --> cirBondLoadings
  martingaleRepresentation --> clarkOcone
  changeOfNumeraire --> cmsConvexityAdjustment
  bondImmunization --> compoundExchangeRateBridge
  convexOrder --> convexOrderMinimalSum
  frechetHoeffding --> convexOrderMinimalSum
  compoundPoissonMgf --> cramerLundbergClaims
  pricingFunctional --> cvaIsPrice
  unilateralCva --> cvaIsPrice
  coherentRiskRepresentation --> delbaenRepresentation
  expectedShortfallDual --> delbaenRepresentation
  continuousFtap --> delbaenSchachermayer
  semimartingaleIntegral --> delbaenSchachermayer
  dmwMultiAsset --> delbaenSchachermayer
  dmwFtap --> dmwMultiAsset
  coneSeparation --> dmwMultiAsset
  bsPde --> dupireLocalVol
  feynmanKacVariableCoefficient --> dupireLocalVol
  dupireZeroRates --> dupireLocalVol
  esscherTilt --> esscherEmmLevy
  jumpDiffusionLaw --> esscherEmmLevy
  pathSignature --> expectedSignatureMomentProblem
  feynmanKacHeatEq --> feynmanKacVariableCoefficient
  sdeContinuousSolution --> feynmanKacVariableCoefficient
  itoFormulaC2 --> feynmanKacVariableCoefficient
  bsCall --> forwardStartCall
  interestRateParity --> futuresBasisConvergence
  affineTermStructure --> futuresForwardConvexity
  continuousFtap --> girsanovContinuousEmm
  itoFormulaC2 --> girsanovContinuousEmm
  esscherTilt --> girsanovContinuousEmm
  empiricalCdfStrongLaw --> glivenkoCantelli
  hestonPde --> hestonCf
  hjmDriftCondition --> hjmAffineModels
  affineTermStructure --> hjmAffineModels
  hjmLogBondDynamics --> hjmBondDynamics
  itoFormulaC2 --> hjmBondDynamics
  hjmModel --> hjmBondDynamics
  hjmBondDynamics --> hjmDriftCondition
  hjmModel --> hjmDriftCondition
  stochasticFubiniProcess --> hjmLogBondDynamics
  hjmModel --> hjmLogBondDynamics
  hjmDriftCondition --> hjmMusiela
  hjmDriftCondition --> hjmShortRate
  bsCall --> impliedVolExistence
  bsDelta --> impliedVolExistence
  itoFormulaC2 --> itoFormula2d
  itoProductRule --> itoFormula2d
  itoIntegralClm --> itoIntegralMartingale
  marketCompleteness --> itoIntegralMartingale
  itoFormulaC2 --> itoLevyFormula
  itoIntegralClm --> itoLevyFormula
  compoundPoissonMgf --> jumpDiffusionLaw
  jumpDiffusionLaw --> kouJumpDiffusion
  bsCall --> kouJumpDiffusion
  expectedShortfallCoherent --> kusuoka
  coherentRiskMeasure --> kusuoka
  kyleEquilibrium --> kyleEquilibriumUnique
  glostenMilgromQuote --> kyleEquilibriumUnique
  oneFactorCopulaDefault --> largePoolLoss
  gaussianFactorCopula --> largePoolLoss
  standardNormalCdf --> largePoolLoss
  largePortfolioLimit --> largePoolLoss
  brownianMotion --> lawIteratedLogarithm
  blackCoxDefault --> liquidationFirstPassage
  aaveLiquidationKmv --> liquidationFirstPassage
  changeOfNumeraire --> lmmForwardMartingale
  changeOfNumeraire --> logOptimalNumeraire
  continuousFtap --> logOptimalNumeraire
  cramerLundbergClaims --> lundbergRuinBound
  compoundPoissonMgf --> lundbergRuinBound
  margrabe --> margrabeNumeraire
  changeOfNumeraire --> margrabeNumeraire
  markowitzLagrangian --> markowitzKktNecessity
  martingaleRepresentation --> martingaleRepresentationVector
  bsCall --> mertonCreditSpread
  itoLevyFormula --> mertonPide
  jumpDiffusionMixing --> mertonPide
  itoFormulaC2 --> mertonPortfolioFraction
  portfolioVariance --> mertonPortfolioFraction
  marketCarrMadan --> modelFreeVariance
  optimalDividendProblem --> multidimensionalDividendBoundary
  girsanovContinuousEmm --> novikovGirsanov
  gaussianFactorCopula --> oneFactorCopulaDefault
  standardNormalCdf --> oneFactorCopulaDefault
  largePortfolioLimit --> oneFactorCopulaDefault
  compoundPoissonMgf --> panjerRecursion
  snellEnvelope --> perpetualAmerican
  bsPde --> perpetualAmerican
  markovPathLaw --> perronFrobeniusMarkov
  brownianMotion --> purgedCvIndependence
  quantile --> quantileConvergenceInDistribution
  convexOrder --> rawFiltrationMimickingMartingale
  markovMartingale --> rawFiltrationMimickingMartingale
  brownianMotion --> reflectionPrinciple
  coherentRiskMeasure --> riskMeasureFamilies
  riskParityFoc --> riskParityNAsset
  nondominatedModel --> robustAmericanIrregularDuality
  snellEnvelope --> robustAmericanIrregularDuality
  nondominatedModel --> robustBinomialDuality
  coinFlipMeasure --> robustBinomialDuality
  stochasticVolterraEquation --> roughHestonPathwiseUniqueness
  bsCall --> sabrHagan
  sabrModel --> sabrRightTailCorrection
  calibratedMartingaleMeasures --> schrodingerSpxVix
  modelFreeVariance --> schrodingerSpxVix
  sdeStrongSolution --> sdeContinuousSolution
  marketCompleteness --> secondFtapConverse
  secondFtap --> secondFtapConverse
  itoIntegralClm --> semimartingaleIntegral
  levyCharacterization --> semimartingaleIntegral
  calibratedMartingaleMeasures --> semistaticFtap
  semistaticStrategy --> semistaticFtap
  dmwFtap --> semistaticFtap
  itoFormulaC2 --> siegelParadox
  quantile --> sklarGeneral
  supercooledStefanSolution --> stefanUniqueness
  stochasticFubini --> stochasticFubiniLevy
  stochasticFubini --> stochasticFubiniProcess
  survivalFunction --> survivalModel
  relaxedControlledDiffusion --> timeInconsistentEquilibrium
  margrabe --> twoAssetOptionFormulas
  bsCall --> twoAssetOptionFormulas
  frechetHoeffding --> uniformConvexCompleteMixability
  bsCall --> varianceGammaCall
  martingaleTransform --> varianceOptimalHedging
  emm --> varianceOptimalHedging
  expectedUtilityAxioms --> vonNeumannMorgenstern
  expectedUtility --> vonNeumannMorgenstern
  zakaiEquation --> zakaiUniquenessSingularControl

  classDef proved fill:#d4edda,stroke:#28a745,color:#111;
  classDef upstream fill:#d9e8f6,stroke:#1f6fb2,color:#111;
  classDef partial fill:#ffe5d0,stroke:#d9534f,color:#111;
  classDef frontier fill:#fff3cd,stroke:#d39e00,color:#111;
```

| node | status | issues |
|---|---|---|
| `def:brownian-motion` Brownian motion (Mathlib, upstream) | ✅ upstream | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Abrownian-motion%22%20in%3Abody) |
| `def:chain-ladder-prediction` Chain-ladder prediction | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Achain-ladder-prediction%22%20in%3Abody) |
| `def:coin-flip-measure` The coin-flip path law | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acoin-flip-measure%22%20in%3Abody) |
| `def:contract` Contract | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acontract%22%20in%3Abody) |
| `def:convex-risk-measure` Convex risk measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aconvex-risk-measure%22%20in%3Abody) |
| `def:copula` Copula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acopula%22%20in%3Abody) |
| `def:emm` Equivalent martingale measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aemm%22%20in%3Abody) |
| `def:expected-utility` Expected utility | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aexpected-utility%22%20in%3Abody) |
| `def:gbm` Geometric Brownian motion | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Agbm%22%20in%3Abody) |
| `def:hazard-survival` Survival curve of a hazard rate | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Ahazard-survival%22%20in%3Abody) |
| `def:heston-transform` The explicit Heston transform | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aheston-transform%22%20in%3Abody) |
| `def:law-invariant` Law-invariant risk functional | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Alaw-invariant%22%20in%3Abody) |
| `def:market` Market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Amarket%22%20in%3Abody) |
| `def:portfolio-variance` Portfolio variance | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aportfolio-variance%22%20in%3Abody) |
| `def:quantile` Quantile function | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aquantile%22%20in%3Abody) |
| `def:risk-contribution` Risk contribution | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Arisk-contribution%22%20in%3Abody) |
| `def:sharpe-ratio` Sharpe ratio | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asharpe-ratio%22%20in%3Abody) |
| `def:snell-envelope` Snell envelope | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asnell-envelope%22%20in%3Abody) |
| `def:standard-normal-cdf` Standard normal distribution function Φ | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Astandard-normal-cdf%22%20in%3Abody) |
| `def:survival-function` Survival function | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asurvival-function%22%20in%3Abody) |
| `def:v3-position-value` Value of a concentrated-liquidity position | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Av3-position-value%22%20in%3Abody) |
| `thm:bond-immunization` Duration and immunization | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abond-immunization%22%20in%3Abody) |
| `thm:carr-madan` Carr–Madan spanning identity | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acarr-madan%22%20in%3Abody) |
| `thm:change-of-numeraire` Change of numéraire | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Achange-of-numeraire%22%20in%3Abody) |
| `thm:compound-poisson-mgf` Compound Poisson moment generating function | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompound-poisson-mgf%22%20in%3Abody) |
| `thm:cone-separation` Separation theorem for closed convex cones | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acone-separation%22%20in%3Abody) |
| `thm:doob-decomposition` Doob decomposition | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adoob-decomposition%22%20in%3Abody) |
| `thm:doob-maximal-inequality` Doob's $L^p$ maximal inequality | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adoob-maximal-inequality%22%20in%3Abody) |
| `thm:empirical-cdf-strong-law` Strong law for the empirical distribution function | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aempirical-cdf-strong-law%22%20in%3Abody) |
| `thm:esscher-tilt` Esscher transform of a Gaussian | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aesscher-tilt%22%20in%3Abody) |
| `thm:feynman-kac-heat-eq` Feynman–Kac formula for the heat equation | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afeynman-kac-heat-eq%22%20in%3Abody) |
| `thm:kelly-criterion` The Kelly fraction is a critical point of the growth rate | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akelly-criterion%22%20in%3Abody) |
| `thm:key-rate-duration` Key-rate durations | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akey-rate-duration%22%20in%3Abody) |
| `thm:kkt-sufficiency` Karush–Kuhn–Tucker sufficiency for convex quadratic programs | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akkt-sufficiency%22%20in%3Abody) |
| `thm:markov-path-law` Ionescu–Tulcea theorem: the law of a Markov chain | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkov-path-law%22%20in%3Abody) |
| `thm:martingale-transform` Martingale transform | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-transform%22%20in%3Abody) |
| `thm:optional-sampling` Optional sampling theorem | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aoptional-sampling%22%20in%3Abody) |
| `thm:sdf-capm-hansen-jagannathan` CAPM from a discount factor affine in the market return | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asdf-capm-hansen-jagannathan%22%20in%3Abody) |
| `thm:stiemke` Stiemke's lemma | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astiemke%22%20in%3Abody) |
| `thm:superhedging-price-lower-bound` The superhedging price dominates every martingale price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asuperhedging-price-lower-bound%22%20in%3Abody) |
| `thm:utility-state-price-density` Marginal utility is a state-price density | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Autility-state-price-density%22%20in%3Abody) |
| `thm:vasicek-bond-pde` The Vasicek bond price solves the term-structure equation | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avasicek-bond-pde%22%20in%3Abody) |
| `def:american-price` The American price of an exercise right | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aamerican-price%22%20in%3Abody) |
| `def:coherent-risk-measure` Coherent risk measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acoherent-risk-measure%22%20in%3Abody) |
| `def:contract-value` Value of a contract | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acontract-value%22%20in%3Abody) |
| `def:hjm-model` Heath–Jarrow–Morton model | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Ahjm-model%22%20in%3Abody) |
| `def:ito-integral-clm` Itô integral and Itô isometry | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aito-integral-clm%22%20in%3Abody) |
| `def:merton-default-probability` Merton's default probability | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Amerton-default-probability%22%20in%3Abody) |
| `def:pricing-measure` Pricing measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Apricing-measure%22%20in%3Abody) |
| `def:value-at-risk` Value-at-risk | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Avalue-at-risk%22%20in%3Abody) |
| `thm:american-price-snell-envelope` The binomial American price is the Snell envelope | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-price-snell-envelope%22%20in%3Abody) |
| `thm:american-put-optimal-exercise` Optimal exercise of the American put | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-optimal-exercise%22%20in%3Abody) |
| `thm:binomial-barrier-reflection` Binomial barrier prices via reflection | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-barrier-reflection%22%20in%3Abody) |
| `thm:binomial-representation` Martingale representation in the binomial model | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-representation%22%20in%3Abody) |
| `thm:bracket-compensator` Bracket of the Itô integral | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abracket-compensator%22%20in%3Abody) |
| `thm:breeden-litzenberger` Breeden–Litzenberger formula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abreeden-litzenberger%22%20in%3Abody) |
| `thm:brownian-doob-maximal` Doob's maximal inequality for Brownian motion on a grid | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abrownian-doob-maximal%22%20in%3Abody) |
| `thm:bs-delta` Black–Scholes Greeks | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-delta%22%20in%3Abody) |
| `thm:bs-pde` The Black–Scholes formula solves the Black–Scholes equation | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-pde%22%20in%3Abody) |
| `thm:buhlmann-credibility` Bühlmann credibility | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abuhlmann-credibility%22%20in%3Abody) |
| `thm:capm-equilibrium` CAPM beta relation, given tangency of the market portfolio | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acapm-equilibrium%22%20in%3Abody) |
| `thm:coin-flip-markov` The coin-flip law is a Markov chain's path law | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acoin-flip-markov%22%20in%3Abody) |
| `thm:continuous-ftap` An equivalent martingale measure excludes simple arbitrage in continuous time | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acontinuous-ftap%22%20in%3Abody) |
| `thm:dupire-zero-rates` Dupire's formula at zero rates, from the conditional local variance | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adupire-zero-rates%22%20in%3Abody) |
| `thm:entropic-risk-certainty-equivalent` Entropic risk is the certainty equivalent of exponential utility | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aentropic-risk-certainty-equivalent%22%20in%3Abody) |
| `thm:expected-utility-axioms` Expected utility satisfies independence and continuity | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-utility-axioms%22%20in%3Abody) |
| `thm:expected-utility-integral` Expected utility is the integral against the lottery | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-utility-integral%22%20in%3Abody) |
| `thm:first-ftap` First fundamental theorem on a finite space (Harrison–Pliska) | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afirst-ftap%22%20in%3Abody) |
| `thm:forward-measure` Forward measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aforward-measure%22%20in%3Abody) |
| `thm:frechet-hoeffding` Fréchet–Hoeffding bounds | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afrechet-hoeffding%22%20in%3Abody) |
| `thm:gaussian-quantile` Gaussian quantile function | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agaussian-quantile%22%20in%3Abody) |
| `thm:girsanov-brownian-characterisation` Girsanov's theorem | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agirsanov-brownian-characterisation%22%20in%3Abody) |
| `thm:hansen-jagannathan-bound` The Hansen–Jagannathan bound | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahansen-jagannathan-bound%22%20in%3Abody) |
| `thm:heston-pde` The explicit Heston transform solves the pricing equation | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aheston-pde%22%20in%3Abody) |
| `thm:intensity-default-model` Intensity model of default | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aintensity-default-model%22%20in%3Abody) |
| `thm:jump-diffusion-incompleteness` Incompleteness of jump-diffusion markets | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-incompleteness%22%20in%3Abody) |
| `thm:jump-diffusion-mixing` Merton's jump-diffusion formula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-mixing%22%20in%3Abody) |
| `thm:large-portfolio-limit` Vasicek's large-portfolio limit | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alarge-portfolio-limit%22%20in%3Abody) |
| `thm:levy-characterization` Lévy's characterization of Brownian motion | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alevy-characterization%22%20in%3Abody) |
| `thm:life-insurance-epv` Whole-life insurance and the life annuity-due: A = 1 − d ä | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alife-insurance-epv%22%20in%3Abody) |
| `thm:mack-chain-ladder` Mack's model: the chain-ladder predictions are a martingale | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amack-chain-ladder%22%20in%3Abody) |
| `thm:margrabe` Margrabe's exchange option formula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amargrabe%22%20in%3Abody) |
| `thm:markowitz-lagrangian` Markowitz mean–variance optimality | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkowitz-lagrangian%22%20in%3Abody) |
| `thm:marshall-olkin` Marshall–Olkin first-to-default | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarshall-olkin%22%20in%3Abody) |
| `thm:martingale-convergence` Convergence of L²-bounded martingales | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-convergence%22%20in%3Abody) |
| `thm:merton-risk-neutral-drift` Risk-neutral drift of a jump-diffusion | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-risk-neutral-drift%22%20in%3Abody) |
| `thm:quadratic-variation` Quadratic variation of Brownian motion | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquadratic-variation%22%20in%3Abody) |
| `thm:quantile-transform` Quantile transform and probability integral transform | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquantile-transform%22%20in%3Abody) |
| `thm:risk-parity-foc` The log-barrier first-order condition gives risk parity | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-parity-foc%22%20in%3Abody) |
| `thm:schwartz-commodity-futures` Schwartz commodity futures price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aschwartz-commodity-futures%22%20in%3Abody) |
| `thm:sde-pathwise-uniqueness` Pathwise uniqueness for Itô SDEs with Lipschitz coefficients | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-pathwise-uniqueness%22%20in%3Abody) |
| `thm:sde-strong-solution` Existence and uniqueness of solutions of Lipschitz SDEs | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-strong-solution%22%20in%3Abody) |
| `thm:snell-doob-decomposition` Doob decomposition of the Snell envelope | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asnell-doob-decomposition%22%20in%3Abody) |
| `thm:snell-envelope` Snell's theorem: the envelope is the value of optimal stopping | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asnell-envelope%22%20in%3Abody) |
| `thm:snell-optional-sampling` Optional sampling under the Snell envelope | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asnell-optional-sampling%22%20in%3Abody) |
| `thm:thiele-reserve` Thiele's differential equation | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Athiele-reserve%22%20in%3Abody) |
| `thm:unilateral-cva` Credit valuation adjustment | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aunilateral-cva%22%20in%3Abody) |
| `thm:uniswap-v3-covered-call` A concentrated-liquidity position is dominated by a covered call | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Auniswap-v3-covered-call%22%20in%3Abody) |
| `thm:variance-swap-jump-bias` Variance swap and the log contract | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-swap-jump-bias%22%20in%3Abody) |
| `thm:willow-tree-brownian-covariance` The willow tree reproduces Brownian covariance | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Awillow-tree-brownian-covariance%22%20in%3Abody) |
| `def:expected-shortfall` Expected shortfall | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aexpected-shortfall%22%20in%3Abody) |
| `def:gaussian-factor-copula` One-factor Gaussian copula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Agaussian-factor-copula%22%20in%3Abody) |
| `def:pricing-functional` The pricing functional | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Apricing-functional%22%20in%3Abody) |
| `thm:aave-liquidation-kmv` Liquidation of a lending position is Merton default | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaave-liquidation-kmv%22%20in%3Abody) |
| `thm:binomial-american-market` The binomial American put is the market's American price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-american-market%22%20in%3Abody) |
| `thm:black-scholes-market` Black–Scholes is a market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ablack-scholes-market%22%20in%3Abody) |
| `thm:black76-caplet` Black's caplet formula, given a lognormal forward rate | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ablack76-caplet%22%20in%3Abody) |
| `thm:coherent-risk-representation` Robust representation of coherent risk measures on a finite space | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acoherent-risk-representation%22%20in%3Abody) |
| `thm:conditional-expectation-pricing-measure` A conditional-expectation process is priced by its own measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aconditional-expectation-pricing-measure%22%20in%3Abody) |
| `thm:credit-portfolio-is-merton` The one-factor credit portfolio is Merton's | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acredit-portfolio-is-merton%22%20in%3Abody) |
| `thm:crr-bs-convergence` Cox–Ross–Rubinstein convergence to Black–Scholes | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acrr-bs-convergence%22%20in%3Abody) |
| `thm:dmw-ftap` Dalang–Morton–Willinger FTAP for one asset on a general space | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Admw-ftap%22%20in%3Abody) |
| `thm:gaussian-portfolio-var` Value-at-risk of a Gaussian portfolio | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agaussian-portfolio-var%22%20in%3Abody) |
| `thm:ito-formula-c2` Itô's formula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-c2%22%20in%3Abody) |
| `thm:log-utility-acceptance` Acceptance sets from expected utility | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alog-utility-acceptance%22%20in%3Abody) |
| `thm:market-ftap` The fundamental theorem of asset pricing for a market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-ftap%22%20in%3Abody) |
| `thm:martingale-representation` Martingale representation theorem | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-representation%22%20in%3Abody) |
| `thm:merton-structural-default` Merton's structural model of default | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-structural-default%22%20in%3Abody) |
| `thm:one-date-market` The one-date market and its pricing measures | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aone-date-market%22%20in%3Abody) |
| `thm:physical-measure-pricing` Black–Scholes pricing under the physical measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aphysical-measure-pricing%22%20in%3Abody) |
| `thm:potential-future-exposure` Potential future exposure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apotential-future-exposure%22%20in%3Abody) |
| `thm:premium-is-price` The life annuity-due is a contract value | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apremium-is-price%22%20in%3Abody) |
| `thm:put-call-parity` Put-call parity | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aput-call-parity%22%20in%3Abody) |
| `thm:second-ftap` Second fundamental theorem on a finite space | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asecond-ftap%22%20in%3Abody) |
| `thm:sklar` Sklar's theorem | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asklar%22%20in%3Abody) |
| `thm:stochastic-fubini` Stochastic Fubini theorem for the Itô integral | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini%22%20in%3Abody) |
| `thm:superhedging-coherent` The superhedging price is a coherent risk measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asuperhedging-coherent%22%20in%3Abody) |
| `thm:tangent-portfolio-efficient` Tangent portfolio | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atangent-portfolio-efficient%22%20in%3Abody) |
| `thm:tranche-leg-price` A CDO tranche leg is a contract | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atranche-leg-price%22%20in%3Abody) |
| `thm:var-not-subadditive` Value-at-risk is not subadditive | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avar-not-subadditive%22%20in%3Abody) |
| `thm:vasicek-market` The Vasicek bond market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avasicek-market%22%20in%3Abody) |
| `thm:american-put-boundary-convex` Convexity of the American put exercise boundary | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-boundary-convex%22%20in%3Abody) |
| `thm:american-put-dominates-european` The American put value dominates the Black–Scholes European price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-dominates-european%22%20in%3Abody) |
| `thm:bachelier-call` Bachelier call price formula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abachelier-call%22%20in%3Abody) |
| `thm:balancer-invariant` Balancer constant-mean AMM | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abalancer-invariant%22%20in%3Abody) |
| `thm:binomial-knock-in-market` The binomial market prices the knock-in by reflection | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-knock-in-market%22%20in%3Abody) |
| `thm:bs-american-market` The Black–Scholes market's American put is the canonical American put | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-american-market%22%20in%3Abody) |
| `thm:bs-call` The Black–Scholes price of a call in the Black–Scholes market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-call%22%20in%3Abody) |
| `thm:bs-delta-hedge` Black–Scholes delta hedging | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-delta-hedge%22%20in%3Abody) |
| `thm:esscher-premium-is-price` The Esscher premium is a price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aesscher-premium-is-price%22%20in%3Abody) |
| `thm:euler-allocation` Euler allocation of Gaussian value at risk | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aeuler-allocation%22%20in%3Abody) |
| `thm:expected-shortfall-coherent` Expected shortfall is a law-invariant coherent risk measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-coherent%22%20in%3Abody) |
| `thm:expected-shortfall-dual` Dual representation of expected shortfall | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-dual%22%20in%3Abody) |
| `thm:expected-shortfall-not-elicitable` Expected shortfall is not elicitable | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-not-elicitable%22%20in%3Abody) |
| `thm:glosten-milgrom-pricing-measure` The Glosten–Milgrom quote sequence is a martingale for the dealer's measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglosten-milgrom-pricing-measure%22%20in%3Abody) |
| `thm:hedged-position-risk` Risk of a hedged position | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahedged-position-risk%22%20in%3Abody) |
| `thm:heston-bs-market-limit` As vol-of-vol vanishes the Heston transform is a Black–Scholes price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aheston-bs-market-limit%22%20in%3Abody) |
| `thm:hoeffding-covariance` Hoeffding's covariance identity | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahoeffding-covariance%22%20in%3Abody) |
| `thm:insured-market` The insured market and its Esscher pricing measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ainsured-market%22%20in%3Abody) |
| `thm:interest-rate-parity` Covered interest-rate parity | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ainterest-rate-parity%22%20in%3Abody) |
| `thm:ito-product-rule` Itô's product rule | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-product-rule%22%20in%3Abody) |
| `thm:jump-diffusion-market` The jump-diffusion market at one date | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-market%22%20in%3Abody) |
| `thm:jump-diffusion-price` Jump-diffusion prices under the Esscher pricing measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-price%22%20in%3Abody) |
| `thm:lp-position-price` An AMM liquidity position is a contract | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alp-position-price%22%20in%3Abody) |
| `thm:marginal-utility-is-sdf` Marginal utility is the stochastic discount factor of a complete market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarginal-utility-is-sdf%22%20in%3Abody) |
| `thm:market-call-price-normalized` A pricing measure gives a normalised call price function | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-call-price-normalized%22%20in%3Abody) |
| `thm:market-call-surface` Breeden–Litzenberger for a market's call prices | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-call-surface%22%20in%3Abody) |
| `thm:market-carr-madan` Carr–Madan replication in a market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-carr-madan%22%20in%3Abody) |
| `thm:market-completeness` Brownian market: the superreplication price is the market price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-completeness%22%20in%3Abody) |
| `thm:market-dupire` Dupire's formula for a market's call prices, at zero rates | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-dupire%22%20in%3Abody) |
| `thm:market-hansen-jagannathan` The Hansen–Jagannathan bound for a market with a pricing measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-hansen-jagannathan%22%20in%3Abody) |
| `thm:market-sdf-capm` The security market line for a market with a pricing measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-sdf-capm%22%20in%3Abody) |
| `thm:quantile-elicitability` Elicitability of the quantile | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquantile-elicitability%22%20in%3Abody) |
| `thm:rockafellar-uryasev` Rockafellar–Uryasev formula | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arockafellar-uryasev%22%20in%3Abody) |
| `thm:smile-no-arbitrage` Roper's converse: every normalised call price function is a market's | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asmile-no-arbitrage%22%20in%3Abody) |
| `thm:superhedging-duality` Superhedging duality, one period and finitely many states | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asuperhedging-duality%22%20in%3Abody) |
| `thm:time-dependent-vol-market` Black–Scholes with a deterministic volatility clock is a market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atime-dependent-vol-market%22%20in%3Abody) |
| `thm:trinomial-moment-matching` Trinomial lattice step as a pricing measure | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atrinomial-moment-matching%22%20in%3Abody) |
| `thm:vasicek-price-solves-pde` The Vasicek market price solves the Vasicek PDE | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avasicek-price-solves-pde%22%20in%3Abody) |
| `thm:zero-coupon-bond-price` The zero-coupon bond price is a price | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Azero-coupon-bond-price%22%20in%3Abody) |
| `thm:bs-arbitrage-free-price` Uniqueness of the Black–Scholes pricing measure among square-integrable densities | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-arbitrage-free-price%22%20in%3Abody) |
| `thm:fissler-ziegel` A strictly consistent score for value at risk and expected shortfall | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afissler-ziegel%22%20in%3Abody) |
| `thm:glosten-milgrom-quote` Glosten–Milgrom bid and ask quotes | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglosten-milgrom-quote%22%20in%3Abody) |
| `thm:immunization-market-price` Immunization for market prices | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aimmunization-market-price%22%20in%3Abody) |
| `thm:impermanent-loss` Impermanent loss | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aimpermanent-loss%22%20in%3Abody) |
| `thm:jump-diffusion-market-incomplete` The jump-diffusion market has two pricing measures | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-market-incomplete%22%20in%3Abody) |
| `thm:key-rate-market-price` Key-rate durations for market prices | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akey-rate-market-price%22%20in%3Abody) |
| `thm:log-optimal-numeraire-one-period` A stationary log portfolio is the numéraire portfolio, one period | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alog-optimal-numeraire-one-period%22%20in%3Abody) |
| `thm:quotes-market-realisation` Arbitrage-free call quotes are the prices of a market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquotes-market-realisation%22%20in%3Abody) |
| `thm:svi-market-realisation` A butterfly-free SVI slice is a market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asvi-market-realisation%22%20in%3Abody) |
| `thm:kelly-is-log-optimal` The Kelly wealth is the numéraire portfolio of the betting market | ✅ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akelly-is-log-optimal%22%20in%3Abody) |
| `def:calibrated-martingale-measures` Calibrated martingale measures of finite entropy | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acalibrated-martingale-measures%22%20in%3Abody) |
| `def:convex-order` Convex order | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aconvex-order%22%20in%3Abody) |
| `def:markov-martingale` Markov martingales | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Amarkov-martingale%22%20in%3Abody) |
| `def:nondominated-model` Nondominated models | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Anondominated-model%22%20in%3Abody) |
| `def:optimal-dividend-problem` Optimal dividend problems | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aoptimal-dividend-problem%22%20in%3Abody) |
| `def:path-signature` Signatures of paths | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Apath-signature%22%20in%3Abody) |
| `def:real-erf` erf / erfc / erfinv for Mathlib | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Areal-erf%22%20in%3Abody) |
| `def:relaxed-controlled-diffusion` Relaxed controlled diffusions | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Arelaxed-controlled-diffusion%22%20in%3Abody) |
| `def:sabr-model` The SABR model | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asabr-model%22%20in%3Abody) |
| `def:semistatic-strategy` Semistatic trading strategies | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asemistatic-strategy%22%20in%3Abody) |
| `def:stochastic-volterra-equation` Stochastic Volterra equations | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Astochastic-volterra-equation%22%20in%3Abody) |
| `def:supercooled-stefan-solution` Physical solutions of the supercooled Stefan problem | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asupercooled-stefan-solution%22%20in%3Abody) |
| `def:zakai-equation` The Zakai equation | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Azakai-equation%22%20in%3Abody) |
| `thm:aave-health-factor-bound` Aave multi-asset health factor: a liquidation bound | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaave-health-factor-bound%22%20in%3Abody) |
| `thm:affine-term-structure` Affine term structure | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaffine-term-structure%22%20in%3Abody) |
| `thm:american-put-premium` American put early-exercise premium | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-premium%22%20in%3Abody) |
| `thm:american-put-superhedging-price` The American put value is the superhedging price | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-superhedging-price%22%20in%3Abody) |
| `thm:apt-pricing` APT exact-factor pricing | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aapt-pricing%22%20in%3Abody) |
| `thm:barrier-lookback-closed-forms` Barrier and lookback closed forms | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abarrier-lookback-closed-forms%22%20in%3Abody) |
| `thm:bates-cf` Bates characteristic function | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abates-cf%22%20in%3Abody) |
| `thm:bermudan-callable-snell` Callable bonds and Bermudan swaptions by Snell envelope | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abermudan-callable-snell%22%20in%3Abody) |
| `thm:black-cox-default` Black–Cox first-passage default | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ablack-cox-default%22%20in%3Abody) |
| `thm:bounded-law-complete-mixability` Complete mixability of bounded absolutely continuous laws | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abounded-law-complete-mixability%22%20in%3Abody) |
| `thm:bracket-quadratic-variation` Bracket is the quadratic variation of an Itô integral | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abracket-quadratic-variation%22%20in%3Abody) |
| `thm:brownian-nowhere-differentiable` Brownian paths are nowhere differentiable | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abrownian-nowhere-differentiable%22%20in%3Abody) |
| `thm:carr-lee-moment` Carr–Lee moment formula | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acarr-lee-moment%22%20in%3Abody) |
| `thm:cev-call` CEV European call | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acev-call%22%20in%3Abody) |
| `thm:cir-bond-loadings` CIR bond-price loadings | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acir-bond-loadings%22%20in%3Abody) |
| `thm:clark-ocone` L¹ martingale representation and Clark–Ocone | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aclark-ocone%22%20in%3Abody) |
| `thm:cms-convexity-adjustment` CMS convexity adjustment | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acms-convexity-adjustment%22%20in%3Abody) |
| `thm:compensated-poisson-integral` Compensated-Poisson integral | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompensated-poisson-integral%22%20in%3Abody) |
| `thm:compound-exchange-rate-bridge` Compound's exchange rate as a money-market account | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompound-exchange-rate-bridge%22%20in%3Abody) |
| `thm:convex-order-minimal-sum` Convex-order minimal sums | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aconvex-order-minimal-sum%22%20in%3Abody) |
| `thm:cramer-lundberg-claims` Cramér–Lundberg claims | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acramer-lundberg-claims%22%20in%3Abody) |
| `thm:cva-is-price` CVA is the price of the default loss | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acva-is-price%22%20in%3Abody) |
| `thm:delbaen-representation` Delbaen's representation of coherent risk measures | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adelbaen-representation%22%20in%3Abody) |
| `thm:delbaen-schachermayer` Delbaen–Schachermayer: no free lunch with vanishing risk | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adelbaen-schachermayer%22%20in%3Abody) |
| `thm:dmw-multi-asset` Dalang–Morton–Willinger for several assets | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Admw-multi-asset%22%20in%3Abody) |
| `thm:dupire-local-vol` Dupire local volatility | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adupire-local-vol%22%20in%3Abody) |
| `thm:esscher-emm-levy` Esscher EMM for exponential-Lévy markets | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aesscher-emm-levy%22%20in%3Abody) |
| `thm:expected-signature-moment-problem` Expected signature of stopped Brownian motion | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-signature-moment-problem%22%20in%3Abody) |
| `thm:expected-utility-risk-aversion` Expected utility and risk aversion | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-utility-risk-aversion%22%20in%3Abody) |
| `thm:feynman-kac-variable-coefficient` Variable-coefficient Feynman–Kac | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afeynman-kac-variable-coefficient%22%20in%3Abody) |
| `thm:forward-start-call` Forward-start call | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aforward-start-call%22%20in%3Abody) |
| `thm:futures-basis-convergence` Contango, backwardation and basis convergence | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afutures-basis-convergence%22%20in%3Abody) |
| `thm:futures-forward-convexity` Futures–forward convexity adjustment | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afutures-forward-convexity%22%20in%3Abody) |
| `thm:girsanov-continuous-emm` Girsanov EMM from the Itô tower | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agirsanov-continuous-emm%22%20in%3Abody) |
| `thm:glivenko-cantelli` Glivenko–Cantelli theorem | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglivenko-cantelli%22%20in%3Abody) |
| `thm:heston-cf` Heston characteristic function | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aheston-cf%22%20in%3Abody) |
| `thm:hjm-affine-models` HJM recovers Ho–Lee and Vasicek | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-affine-models%22%20in%3Abody) |
| `thm:hjm-bond-dynamics` HJM bond-price dynamics | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-bond-dynamics%22%20in%3Abody) |
| `thm:hjm-drift-condition` HJM drift condition | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-drift-condition%22%20in%3Abody) |
| `thm:hjm-log-bond-dynamics` HJM log-bond dynamics | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-log-bond-dynamics%22%20in%3Abody) |
| `thm:hjm-musiela` HJM Musiela parametrization | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-musiela%22%20in%3Abody) |
| `thm:hjm-short-rate` HJM induces a short-rate model | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-short-rate%22%20in%3Abody) |
| `thm:implied-vol-existence` Implied volatility for every arbitrage-free price | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aimplied-vol-existence%22%20in%3Abody) |
| `thm:ito-formula-2d` Two-process Itô formula | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-2d%22%20in%3Abody) |
| `thm:ito-integral-martingale` General-integrand Itô process is a martingale | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-integral-martingale%22%20in%3Abody) |
| `thm:ito-levy-formula` Itô–Lévy change of variables | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-levy-formula%22%20in%3Abody) |
| `thm:jump-diffusion-law` Compound-Poisson and jump-diffusion law | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-law%22%20in%3Abody) |
| `thm:kou-jump-diffusion` Kou double-exponential jump-diffusion | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akou-jump-diffusion%22%20in%3Abody) |
| `thm:kusuoka` Kusuoka representation | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akusuoka%22%20in%3Abody) |
| `thm:kyle-equilibrium` Kyle single-period equilibrium | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akyle-equilibrium%22%20in%3Abody) |
| `thm:kyle-equilibrium-unique` Uniqueness of the Kyle equilibrium | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akyle-equilibrium-unique%22%20in%3Abody) |
| `thm:large-pool-loss` Large homogeneous pool loss law | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alarge-pool-loss%22%20in%3Abody) |
| `thm:law-iterated-logarithm` Law of the iterated logarithm | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alaw-iterated-logarithm%22%20in%3Abody) |
| `thm:liquidation-first-passage` Liquidation before maturity as first passage | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aliquidation-first-passage%22%20in%3Abody) |
| `thm:lmm-forward-martingale` LIBOR market model forward martingale | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Almm-forward-martingale%22%20in%3Abody) |
| `thm:log-optimal-numeraire` Log-optimal portfolio is the numéraire | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alog-optimal-numeraire%22%20in%3Abody) |
| `thm:lundberg-ruin-bound` Lundberg ruin bound | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alundberg-ruin-bound%22%20in%3Abody) |
| `thm:margrabe-numeraire` Margrabe and chooser via the S²-numéraire | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amargrabe-numeraire%22%20in%3Abody) |
| `thm:markowitz-kkt-necessity` Markowitz first-order conditions are necessary | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkowitz-kkt-necessity%22%20in%3Abody) |
| `thm:martingale-representation-vector` Vector martingale representation | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-representation-vector%22%20in%3Abody) |
| `thm:merton-credit-spread` Merton structural credit spread | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-credit-spread%22%20in%3Abody) |
| `thm:merton-pide` Merton PIDE | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-pide%22%20in%3Abody) |
| `thm:merton-portfolio-fraction` Merton myopic risky fraction | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-portfolio-fraction%22%20in%3Abody) |
| `thm:model-free-variance` Model-free implied variance replication | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amodel-free-variance%22%20in%3Abody) |
| `thm:multidimensional-dividend-boundary` Optimal dividends of several insurers on the free boundary | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amultidimensional-dividend-boundary%22%20in%3Abody) |
| `thm:novikov-girsanov` Novikov Girsanov for unbounded θ | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Anovikov-girsanov%22%20in%3Abody) |
| `thm:one-factor-copula-default` One-factor Gaussian copula default | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aone-factor-copula-default%22%20in%3Abody) |
| `thm:panjer-recursion` Panjer recursion | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apanjer-recursion%22%20in%3Abody) |
| `thm:perpetual-american` Perpetual American option | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aperpetual-american%22%20in%3Abody) |
| `thm:perron-frobenius-markov` Perron–Frobenius and finite Markov chain ergodicity | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aperron-frobenius-markov%22%20in%3Abody) |
| `thm:poisson-interarrival-iid` Poisson interarrivals are iid exponential | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apoisson-interarrival-iid%22%20in%3Abody) |
| `thm:propagator-no-arbitrage` Transient-impact propagator no-arbitrage | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apropagator-no-arbitrage%22%20in%3Abody) |
| `thm:purged-cv-independence` Purged cross-validation: σ-algebra independence | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apurged-cv-independence%22%20in%3Abody) |
| `thm:quantile-convergence-in-distribution` Quantiles under convergence in distribution | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquantile-convergence-in-distribution%22%20in%3Abody) |
| `thm:raw-filtration-mimicking-martingale` Mimicking Markov martingales for the raw filtration | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Araw-filtration-mimicking-martingale%22%20in%3Abody) |
| `thm:reflection-principle` Reflection principle for Brownian motion | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Areflection-principle%22%20in%3Abody) |
| `thm:risk-measure-families` Entropic, distortion and expectile risk measures | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-measure-families%22%20in%3Abody) |
| `thm:risk-parity-n-asset` N-asset risk parity exists and is unique | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-parity-n-asset%22%20in%3Abody) |
| `thm:robust-american-irregular-duality` Robust American hedging with irregular payoffs | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arobust-american-irregular-duality%22%20in%3Abody) |
| `thm:robust-binomial-duality` Quasi-sure duality for the robust multi-period binomial model | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arobust-binomial-duality%22%20in%3Abody) |
| `thm:rough-heston-pathwise-uniqueness` Rough-Heston pathwise uniqueness | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arough-heston-pathwise-uniqueness%22%20in%3Abody) |
| `thm:sabr-hagan` SABR Hagan asymptotic implied vol | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asabr-hagan%22%20in%3Abody) |
| `thm:sabr-right-tail-correction` SABR right tail: the k^{3/2} correction | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asabr-right-tail-correction%22%20in%3Abody) |
| `thm:schrodinger-spx-vix` Schrödinger calibration of SPX/VIX | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aschrodinger-spx-vix%22%20in%3Abody) |
| `thm:sde-continuous-solution` Continuous strong solutions on every horizon | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-continuous-solution%22%20in%3Abody) |
| `thm:second-ftap-converse` Second FTAP: uniqueness implies completeness | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asecond-ftap-converse%22%20in%3Abody) |
| `thm:semimartingale-integral` The stochastic integral against a semimartingale | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asemimartingale-integral%22%20in%3Abody) |
| `thm:semistatic-ftap` Semistatic FTAP with entropy | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asemistatic-ftap%22%20in%3Abody) |
| `thm:siegel-paradox` Siegel's paradox | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asiegel-paradox%22%20in%3Abody) |
| `thm:sklar-general` Sklar's theorem for arbitrary margins | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asklar-general%22%20in%3Abody) |
| `thm:stefan-uniqueness` Stefan uniqueness with accumulating jumps | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astefan-uniqueness%22%20in%3Abody) |
| `thm:stochastic-fubini-levy` Stochastic Fubini for Itô–Lévy integrals | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini-levy%22%20in%3Abody) |
| `thm:stochastic-fubini-process` Stochastic Fubini for the integral process | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini-process%22%20in%3Abody) |
| `thm:survival-model` Survival model and life tables | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asurvival-model%22%20in%3Abody) |
| `thm:time-inconsistent-equilibrium` Relaxed equilibria under time inconsistency | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atime-inconsistent-equilibrium%22%20in%3Abody) |
| `thm:two-asset-option-formulas` Stulz and Heynen–Kat two-asset formulas | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atwo-asset-option-formulas%22%20in%3Abody) |
| `thm:uniform-convex-complete-mixability` Complete mixability of uniform laws on convex bodies | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Auniform-convex-complete-mixability%22%20in%3Abody) |
| `thm:variance-gamma-call` Variance-gamma European call | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-gamma-call%22%20in%3Abody) |
| `thm:variance-optimal-hedging` Variance-optimal hedging | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-optimal-hedging%22%20in%3Abody) |
| `thm:von-neumann-morgenstern` von Neumann–Morgenstern representation theorem | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avon-neumann-morgenstern%22%20in%3Abody) |
| `thm:zakai-uniqueness-singular-control` Zakai uniqueness under singular control | ⏳ | [issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Azakai-uniqueness-singular-control%22%20in%3Abody) |
<!-- END GENERATED SPINE -->

## The spine, stage by stage

The graph above lists every node. This section follows the arc that starts at Brownian motion and
ends at pricing, and says for each stage what is proved, in which declarations, and what is not.
The exact statements, with their scope, are on the
[landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html) and in the
README's Limitations.

### Brownian motion and the Itô integral

The definition of Brownian motion, `IsPreBrownianReal`, comes from Mathlib, and the continuous
modification and the filtered versions come from the BrownianMotion package. The library proves
the quadratic variation of Brownian motion in L² (`tendsto_qv`) and the adapted Itô isometry for
simple integrands (`ito_isometry_discrete`). The isometry extends to a continuous linear isometry
`itoIntegralCLM` from the predictable L² processes on `[0,T]` to L²
([`ItoIntegralCLM.lean`](../MathFin/Probability/Brownian/Ito/ItoIntegralCLM.lean)). The stochastic
integral is Brownian only. An integral against a general continuous semimartingale is a frontier
node (`thm:semimartingale-integral`).

### Itô's formula

For `f(t,x)` with continuous `f`, `f_t`, `f_x` and `f_xx` and no growth condition,
`ito_formula_unrestricted` states that `f(t,B_t) − f(0,B_0) − ∫₀ᵗ (f_t + ½ f_xx)(s,B_s) ds` is a
continuous local martingale for the augmented Brownian filtration. For an Itô process built from one
Brownian motion, with continuous adapted coefficients, the full change-of-variables formula holds
almost surely at every `t ≤ T` at once
(`ItoFormulaAdapted.ito_formula_adapted_unbounded_process`). Not proved: the formula for a
continuous semimartingale not built from `B`, and a quadratic-variation process for a general
continuous local martingale.

### Change of measure

For bounded predictable `θ`, `Btheta_isFilteredPreBrownian_predictable_of_bdd` shows that under the
measure with density `exp(−∫₀ᵀ θ dB − ½∫₀ᵀ θ² dt)` an adapted modification of
`B_t + ∫₀^{t∧T} θ_s ds` is a Brownian motion for the Brownian filtration. Lévy's characterization
(`LevyCharacterization.isFilteredPreBrownian_of_localMartingale`) is proved with the hypothesis that
`M² − t` is a local martingale. The static form for a Gaussian is the Esscher tilt
(`gaussianReal_withDensity_esscher`, in
[`GaussianGirsanov.lean`](../MathFin/Models/BlackScholes/GaussianGirsanov.lean)). Not proved:
unbounded `θ`, Novikov's condition (`thm:novikov-girsanov`) and the general form of Girsanov's
theorem, which are reduced cores in the corpus.

### Martingale representation and completeness

`exists_replicating_strategy` shows that every square-integrable `F^B_T`-measurable claim is its
mean plus a stochastic integral of a unique integrand, so it is replicated from initial wealth
`E[H]` by a unique strategy. On the binomial tree the hedge is identified node by node
(`binomial_martingale_representation`). Not proved: the identification of the Brownian hedge, which
needs the Clark–Ocone formula (`thm:clark-ocone`). In the Black–Scholes market the pricing measure
on `𝓕_T` is unique among those with a density square-integrable under the Girsanov measure
(`BlackScholes.trim_eq_of_isPricingMeasure_withDensity`); a pricing measure with an arbitrary
density is not covered.

### Pricing: the fundamental theorems, the Black–Scholes model, contracts

`ftap_discrete` is the first theorem of asset pricing in discrete time: no arbitrage if and only if
an equivalent martingale measure exists (`IsEMM`), on a finite space of full support, and for one
asset on any probability space (`OneAsset.noArbitrage_iff_exists_isEMM`). `ftap_two` gives the
second theorem for one risky asset on a finite space. In continuous time only the easy direction is
proved: an equivalent martingale measure precludes arbitrage by simple strategies
(`discountedGBM_isMartingale` is its Black–Scholes instance, via the Wald exponential). The
Dalang–Morton–Willinger theorem for several assets rests on a named conditional one-period
hypothesis, and the Delbaen–Schachermayer theorem is a frontier node.

In the Black–Scholes model, `bs_call_formula` gives the call price `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` and
`bs_pde_holds` the partial differential equation. The PDE is also derived from the heat equation for
the Gaussian kernel without differentiating the closed form
(`bsV_satisfies_bs_pde_via_feynmanKac`), and `bs_delta_hedge_replication` proves
`e^{−rt}C(t,S_t) = C(0,S₀) + ∫₀ᵗ Δ σ e^{−rs} S_s dB_s` on `[0,T']` for `T' < T`; the hedge is not
packaged as an admissible self-financing strategy. The binomial price converges to the Black–Scholes
price (`binomialPrice_call_tendsto_bs`).

Contracts are terms of a payoff language, priced in a model by `Contract.value`
([`Pricing/Value.lean`](../MathFin/Pricing/Value.lean)). In any model whose discounted price is a
martingale, `value_europeanCall_sub_put_of_martingale` is put–call parity. The models, risk
measures, term-structure and other limbs build on these objects; their results are in the graph and
catalogued in [`coverage.md`](coverage.md).

## The frontier

A frontier node is a result that is stated and not yet in Lean. It has a label (`thm:` or `def:`
followed by a kebab-case name), a one-sentence statement, the nodes it `uses`, and the `area` of the
library it belongs to. Its entry lives in [`blueprint_frontier.toml`](blueprint_frontier.toml); the
graph and table above show it, and the site's blueprint page prints its statement. The statement
says what proving the node would establish. It is not a claim that the result holds: a node
marked as an open problem is a question, and a node whose resolution has been reported but not
checked says so in its sentence.

A frontier node grows from the proved part of the map. Its `uses` reach a proved node through other
frontier nodes if need be, or its `ground` field names the Mathlib material it builds on. A `core`
field lists the corpus entries that already prove part of the node, which the program tree draws as
partly grown.

The node is tied to three other records.

- Issues. Every open issue that does mathematical work carries a body line `Blueprint: <label>`, and
  every frontier node is named by at least one open issue. The `issues` link in the table opens the
  search for the label. `python3 -m tools.verify.blueprint_issues check` holds both directions.
- A Lean statement. When the proposition can be written down in Lean before it can be proved, the
  entry's `lean` field names the declaration, stated and closed by `sorry`, in
  [`MathFinFrontier/`](../MathFinFrontier). That directory is the [frontier
  connector](glossary.md#frontier-connector) and is outside the library, so the library itself
  stays sorry-free.
- The research catalogue. The field's open problems are recorded with stable ids `MF-OP-NNN` in
  [`research-problems/`](research-problems/README.md), with their literature status and the
  frontier definitions they need. A frontier statement names its id when it has one.

To deliver a frontier node, prove it under `MathFin/`, tag the declaration in
[`MathFin/Blueprint.lean`](../MathFin/Blueprint.lean) with the same label, and delete the entry
from `blueprint_frontier.toml`. Regenerate this page with `python3 tools/blueprint_render.py`
(the graph is extracted by `lake exe blueprint_export MathFin.Blueprint > docs/blueprint_nodes.json`
inside the verify container). [`CONTRIBUTING.md`](../CONTRIBUTING.md) describes the checks a pull
request passes. To add a result the map does not have, add a frontier entry first, with an issue
that carries its label; a node folded into a larger one later is recorded in
`blueprint_retired.toml`.
