# Blueprint — the program's map

How option-pricing theory is built here, starting from Brownian motion: the
risk-neutral measure is *derived* (not assumed), the Black–Scholes formula and
PDE follow, and the frontier — every result the program is working towards —
hangs off the spine it builds on.

The proved nodes are the spine, the load-bearing arc. The other results (the
full Greek matrix, fixed income, portfolio theory, risk measures, …) are
catalogued with their faithfulness status in [`coverage.md`](coverage.md).

**The blueprint and the issues are one system.** Every open issue doing math
work (`type:proof`, `type:research`, `open-problem`, `frontier`) names the node
it advances with a body line `Blueprint: <label>`; every ⏳ frontier node is
named by an open issue; every proved node is named by the issue or pull request
that delivered it. The link is stored only in the issue, so the table under the
graph links each node to a live search rather than a copy.
[`tools/verify/blueprint_issues.py`](../tools/verify/blueprint_issues.py) checks
both directions on every push (`build.yml`) and every issue event
(`blueprint-sync.yml`, which also comments on an issue that is missing its
line). A new result enters the blueprint as a frontier entry in
[`blueprint_frontier.toml`](blueprint_frontier.toml); when it is delivered, its
declaration is tagged in [`MathFin/Blueprint.lean`](../MathFin/Blueprint.lean)
under the same label and the frontier entry goes.

**Status legend.** Green: machine-checked in Lean 4, and — for the headline
nodes — `#print axioms`-clean ([`AxiomAudit.lean`](../MathFin/AxiomAudit.lean)
build-pins them to `[propext, Classical.choice, Quot.sound]`). Blue: consumed
from upstream (Mathlib's `IsPreBrownianReal`) — coherence made
visible. 🚧 *partially* formalized — a genuine machine-checked core with an
explicitly deferred lifting step (the gap is named in the file, never papered
over). ⏳ on the program, not yet formalized — the frontier, grouped by area. No node
is colored proved unless it is.

**Objects and anchors.** Besides the deductive spine, the blueprint tags the program's central
objects (`def:quantile`, `def:value-at-risk`, `def:emm`, `def:contract-value`,
`def:portfolio-variance`, …) and one anchor result per area that had none (risk, portfolio,
DeFi, execution, actuarial). Most corpus entries reach the library through these
shared definitions rather than through a deep theorem, so they are what places the corpus on the
map: [`tools/verify/program_tree.py`](../tools/verify/program_tree.py) puts an entry on a node
when the constants its proof cites depend on the node's declaration. The entries in no such
relation are counted by the ratchet `corpus_off_blueprint`, and the docs site draws the whole
picture as the program tree. Every frontier node grows from the proved nodes: its `uses` reach
one, or its `ground` field names the Mathlib material it builds on. A frontier node whose `core`
lists corpus entries is proved in part.

**Shared objects and bridges.** A tag adds a node; only a proof adds an edge. The proved nodes are
joined into one tree by the objects their proofs share (`def:gbm`, `def:black-scholes-model`,
`def:martingale-transform`, `def:marginal-variance`, …) and by theorems that already join two
parts of the map (the VaR of a Gaussian portfolio, the binomial price as the cost of a hedge, the
caplet as a Black-76 call under the forward measure, the jump-diffusion call as a mixture of
Black–Scholes prices, …). The proved nodes that remain apart are `program_tree.islands`, counted by
the ratchet `blueprint_islands`; the tree draws them growing from the soil beside the trunk.

**The graph below is generated, not drawn.** Nodes are `@[blueprint]`-tagged
declarations ([`MathFin/Blueprint.lean`](../MathFin/Blueprint.lean)); edges are
*inferred from the proof terms* (LeanArchitect's `collectUsed`, a transitive
walk that passes through untagged helpers and stops at tagged constants —
[`MathFinTools/Blueprint.lean`](../MathFinTools/Blueprint.lean) →
[`tools/blueprint_render.py`](../tools/blueprint_render.py)). An edge here is
a theorem actually *consuming* another — narrative lineage with no proof-term
trace does not appear, and where this page's prose once disagreed with the
graph, the graph won (see *Black–Scholes PDE* below). A node with no inbound
edge is a genuine logical root.

<!-- BEGIN GENERATED SPINE (tools/blueprint_render.py — do not hand-edit) -->
```mermaid
graph TD
  brownianMotion["Brownian motion (Mathlib, upstream)"]:::upstream
  coherentRiskMeasure["Coherent risk measure"]:::proved
  contract["Contract"]:::proved
  copula["Copula"]:::proved
  emm["Equivalent martingale measure"]:::proved
  expectedUtility["Expected utility"]:::proved
  gaussianFactorCopula["One-factor Gaussian copula"]:::proved
  gbm["Geometric Brownian motion"]:::proved
  market["Market"]:::proved
  portfolioVariance["Portfolio variance"]:::proved
  quantile["Quantile function"]:::proved
  sharpeRatio["Sharpe ratio"]:::proved
  standardNormalCdf["Standard normal distribution function Φ"]:::proved
  survivalFunction["Survival function"]:::proved
  binomialRepresentation["Martingale representation in the binomial model"]:::proved
  bondImmunization["Duration and immunization"]:::proved
  carrMadan["Carr–Madan static replication"]:::proved
  changeOfNumeraire["Change of numéraire"]:::proved
  compoundPoissonMgf["Compound Poisson moment generating function"]:::proved
  coneSeparation["Separation theorem for closed convex cones"]:::proved
  doobDecomposition["Doob decomposition"]:::proved
  doobMaximalInequality["Doob's $L^p$ maximal inequality"]:::proved
  empiricalCdfStrongLaw["Strong law for the empirical distribution function"]:::proved
  esscherTilt["Esscher transform of a Gaussian"]:::proved
  feynmanKacHeatEq["Feynman–Kac formula for the heat equation"]:::proved
  glostenMilgromQuote["Glosten–Milgrom bid and ask quotes"]:::proved
  hestonPde["Heston model pricing equation"]:::proved
  hoeffdingCovariance["Hoeffding's covariance identity"]:::proved
  impermanentLoss["Impermanent loss"]:::proved
  intensityDefaultModel["Intensity model of default"]:::proved
  interestRateParity["Covered interest-rate parity"]:::proved
  kellyCriterion["Kelly criterion"]:::proved
  keyRateDuration["Key-rate durations"]:::proved
  kktSufficiency["Karush–Kuhn–Tucker sufficiency for convex quadratic programs"]:::proved
  markovPathLaw["Ionescu–Tulcea theorem: the law of a Markov chain"]:::proved
  marshallOlkin["Marshall–Olkin first-to-default"]:::proved
  martingaleTransform["Martingale transform"]:::proved
  optionalSampling["Optional sampling theorem"]:::proved
  riskParityFoc["Risk parity"]:::proved
  sdePathwiseUniqueness["Pathwise uniqueness for SDEs with Lipschitz coefficients"]:::proved
  snellEnvelope["Snell envelope"]:::proved
  stochasticFubini["Stochastic Fubini theorem"]:::proved
  uniswapV3CoveredCall["A concentrated-liquidity position is dominated by a covered call"]:::proved
  vasicekBondPde["Vasicek bond price"]:::proved
  contractValue["Value of a contract"]:::proved
  hjmModel["Heath–Jarrow–Morton model"]:::proved
  itoIntegralClm["Itô integral and Itô isometry"]:::proved
  pricingMeasure["Pricing measure"]:::proved
  valueAtRisk["Value-at-risk"]:::proved
  aaveLiquidationKmv["Liquidation of a lending position is Merton default"]:::proved
  americanPutOptimalExercise["Optimal exercise of the American put"]:::proved
  bachelierCall["Bachelier call price formula"]:::proved
  bracketCompensator["Bracket of the Itô integral"]:::proved
  breedenLitzenberger["Breeden–Litzenberger formula"]:::proved
  bsCall["Black–Scholes call price formula"]:::proved
  bsDelta["Black–Scholes Greeks"]:::proved
  bsPde["Black–Scholes partial differential equation"]:::proved
  capmEquilibrium["Capital asset pricing model"]:::proved
  coherentRiskRepresentation["Robust representation of coherent risk measures"]:::proved
  continuousFtap["Fundamental theorem of asset pricing in continuous time"]:::proved
  dupireZeroRates["Dupire's local volatility formula"]:::proved
  expectedUtilityAxioms["von Neumann–Morgenstern expected utility"]:::proved
  firstFtap["First fundamental theorem of asset pricing"]:::proved
  forwardMeasure["Forward measure"]:::proved
  frechetHoeffding["Fréchet–Hoeffding bounds"]:::proved
  gaussianQuantile["Gaussian quantile function"]:::proved
  girsanovBrownianCharacterisation["Girsanov's theorem"]:::proved
  jumpDiffusionIncompleteness["Incompleteness of jump-diffusion markets"]:::proved
  largePortfolioLimit["Vasicek's large-portfolio limit"]:::proved
  levyCharacterization["Lévy's characterization of Brownian motion"]:::proved
  logUtilityAcceptance["Acceptance sets from expected utility"]:::proved
  markowitzLagrangian["Markowitz mean–variance optimality"]:::proved
  martingaleConvergence["Martingale convergence theorem"]:::proved
  mertonRiskNeutralDrift["Risk-neutral drift of a jump-diffusion"]:::proved
  mertonStructuralDefault["Merton's structural model of default"]:::proved
  quadraticVariation["Quadratic variation of Brownian motion"]:::proved
  quantileTransform["Quantile transform and probability integral transform"]:::proved
  schwartzCommodityFutures["Schwartz commodity futures price"]:::proved
  sdeStrongSolution["Existence and uniqueness of solutions of Lipschitz SDEs"]:::proved
  secondFtap["Second fundamental theorem of asset pricing"]:::proved
  varianceSwapJumpBias["Variance swap and the log contract"]:::proved
  expectedShortfall["Expected shortfall"]:::proved
  black76Caplet["Black's caplet formula"]:::proved
  crrBsConvergence["Cox–Ross–Rubinstein convergence to Black–Scholes"]:::proved
  gaussianPortfolioVar["Value-at-risk of a Gaussian portfolio"]:::proved
  itoFormulaC2["Itô's formula"]:::proved
  jumpDiffusionMixing["Merton's jump-diffusion formula"]:::proved
  margrabe["Margrabe's exchange option formula"]:::proved
  marketCompleteness["Completeness of the Brownian market"]:::proved
  martingaleRepresentation["Martingale representation theorem"]:::proved
  physicalMeasurePricing["Black–Scholes pricing under the physical measure"]:::proved
  potentialFutureExposure["Potential future exposure"]:::proved
  putCallParity["Put-call parity"]:::proved
  sklar["Sklar's theorem"]:::proved
  tangentPortfolioEfficient["Tangent portfolio"]:::proved
  unilateralCva["Credit valuation adjustment"]:::proved
  varNotSubadditive["Value-at-risk is not subadditive"]:::proved
  bsDeltaHedge["Black–Scholes delta hedging"]:::proved
  eulerAllocation["Euler allocation of value-at-risk"]:::proved
  expectedShortfallCoherent["Expected shortfall is coherent"]:::proved
  expectedShortfallDual["Dual representation of expected shortfall"]:::proved
  expectedShortfallNotElicitable["Expected shortfall is not elicitable"]:::proved
  hedgedPositionRisk["Risk of a hedged position"]:::proved
  itoProductRule["Itô's product rule"]:::proved
  quantileElicitability["Elicitability of the quantile"]:::proved
  rockafellarUryasev["Rockafellar–Uryasev formula"]:::proved
  subgraph frontier_choiceDynamic["⏳ frontier · Choice · Dynamic choice"]
    logOptimalNumeraire["Log-optimal portfolio is the numéraire"]:::frontier
    mertonPortfolioFraction["Merton myopic risky fraction"]:::frontier
    timeInconsistentEquilibrium["Relaxed equilibria under time inconsistency"]:::frontier
  end
  subgraph frontier_choiceEquilibrium["⏳ frontier · Choice · Equilibrium"]
    aptPricing["APT exact-factor pricing"]:::frontier
    sdfCapmHansenJagannathan["CAPM and Hansen–Jagannathan from the discount factor"]:::frontier
  end
  subgraph frontier_choicePortfolio["⏳ frontier · Choice · Portfolio choice"]
    markowitzKktNecessity["Markowitz first-order conditions are necessary"]:::frontier
    riskParityNAsset["N-asset risk parity exists and is unique"]:::frontier
  end
  subgraph frontier_choicePreferences["⏳ frontier · Choice · Preferences"]
    expectedUtilityRiskAversion["Expected utility and risk aversion"]:::frontier
    utilityStatePriceDensity["Marginal utility is a state-price density"]:::frontier
    vonNeumannMorgenstern["von Neumann–Morgenstern representation theorem"]:::frontier
  end
  subgraph frontier_choiceTrading["⏳ frontier · Choice · Strategic trading"]
    glostenMilgromPricingMeasure["The Glosten–Milgrom quote process is a martingale"]:::frontier
    kyleEquilibrium["Kyle single-period equilibrium"]:::frontier
  end
  subgraph frontier_probabilityBrownian["⏳ frontier · Probability · Brownian calculus"]
    bracketQuadraticVariation["Bracket is the quadratic variation of an Itô integral"]:::frontier
    brownianNowhereDifferentiable["Brownian paths are nowhere differentiable"]:::frontier
    clarkOcone["L¹ martingale representation and Clark–Ocone"]:::frontier
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
  subgraph frontier_riskCredit["⏳ frontier · Risk · Credit portfolio risk"]
    aaveHealthFactorBound["Aave multi-asset health factor: a liquidation bound"]:::frontier
    largePoolLoss["Large homogeneous pool loss law"]:::frontier
    liquidationFirstPassage["Liquidation before maturity as first passage"]:::frontier
    oneFactorCopulaDefault["One-factor Gaussian copula default"]:::frontier
  end
  subgraph frontier_riskInsurance["⏳ frontier · Risk · Premiums and ruin"]
    cramerLundbergClaims["Cramér–Lundberg claims"]:::frontier
    lundbergRuinBound["Lundberg ruin bound"]:::frontier
    panjerRecursion["Panjer recursion"]:::frontier
  end
  subgraph frontier_riskMeasures["⏳ frontier · Risk · Risk measures"]
    delbaenRepresentation["Delbaen's representation of coherent risk measures"]:::frontier
    kusuoka["Kusuoka representation"]:::frontier
    riskMeasureFamilies["Entropic, distortion and expectile risk measures"]:::frontier
    superhedgingCoherent["The superhedging price is a coherent risk measure"]:::frontier
  end
  subgraph frontier_statistics["⏳ frontier · Statistics"]
    buhlmannCredibility["Bühlmann credibility"]:::frontier
    glivenkoCantelli["Glivenko–Cantelli theorem"]:::frontier
    purgedCvIndependence["Purged cross-validation: σ-algebra independence"]:::frontier
    quantileConvergenceInDistribution["Quantiles under convergence in distribution"]:::frontier
  end
  subgraph frontier_valuationDefault["⏳ frontier · Valuation · Credit"]
    blackCoxDefault["Black–Cox first-passage default"]:::frontier
    cvaIsPrice["CVA is the price of the default loss"]:::frontier
    mertonCreditSpread["Merton structural credit spread"]:::frontier
    stefanUniqueness["Stefan uniqueness with accumulating jumps"]:::frontier
  end
  subgraph frontier_valuationDiffusions["⏳ frontier · Valuation · Black–Scholes and Bachelier"]
    barrierLookbackClosedForms["Barrier and lookback closed forms"]:::frontier
    bsArbitrageFreePrice["The Black–Scholes price is the arbitrage-free price"]:::frontier
    forwardStartCall["Forward-start call"]:::frontier
    girsanovContinuousEmm["Girsanov EMM from the Itô tower"]:::frontier
    impliedVolExistence["Implied volatility for every arbitrage-free price"]:::frontier
    margrabeNumeraire["Margrabe and chooser via the S²-numéraire"]:::frontier
    perpetualAmerican["Perpetual American option"]:::frontier
    twoAssetOptionFormulas["Stulz and Heynen–Kat two-asset formulas"]:::frontier
  end
  subgraph frontier_valuationGeneral["⏳ frontier · Valuation · Arbitrage theory"]
    pricingFunctional["The pricing functional"]:::frontier
    dmwFtap["Dalang–Morton–Willinger FTAP"]:::frontier
    secondFtapConverse["Second FTAP: uniqueness implies completeness"]:::frontier
    semistaticFtap["Semistatic FTAP with entropy"]:::frontier
    varianceOptimalHedging["Variance-optimal hedging"]:::frontier
  end
  subgraph frontier_valuationInsurance["⏳ frontier · Valuation · Life and insurance contracts"]
    lifeInsuranceEpv["Life annuity and insurance EPV"]:::frontier
    premiumIsPrice["Insurance premiums are prices"]:::frontier
    survivalModel["Survival model and life tables"]:::frontier
    thieleReserve["Thiele reserve"]:::frontier
  end
  subgraph frontier_valuationJumps["⏳ frontier · Valuation · Jump models"]
    esscherEmmLevy["Esscher EMM for exponential-Lévy markets"]:::frontier
    jumpDiffusionPrice["Jump-diffusion prices under the Esscher pricing measure"]:::frontier
    kouJumpDiffusion["Kou double-exponential jump-diffusion"]:::frontier
    mertonPide["Merton PIDE"]:::frontier
    varianceGammaCall["Variance-gamma European call"]:::frontier
  end
  subgraph frontier_valuationMechanisms["⏳ frontier · Valuation · Market mechanisms"]
    balancerInvariant["Balancer constant-mean AMM"]:::frontier
    compoundExchangeRateBridge["Compound's exchange rate as a money-market account"]:::frontier
    lpPositionPrice["An AMM liquidity position is a contract"]:::frontier
    propagatorNoArbitrage["Transient-impact propagator no-arbitrage"]:::frontier
  end
  subgraph frontier_valuationModelFree["⏳ frontier · Valuation · Model-free"]
    modelFreeVariance["Model-free implied variance replication"]:::frontier
  end
  subgraph frontier_valuationTerm["⏳ frontier · Valuation · Term structures"]
    affineTermStructure["Affine term structure"]:::frontier
    bermudanCallableSnell["Callable bonds and Bermudan swaptions by Snell envelope"]:::frontier
    cirBondLoadings["CIR bond-price loadings"]:::frontier
    cmsConvexityAdjustment["CMS convexity adjustment"]:::frontier
    futuresBasisConvergence["Contango, backwardation and basis convergence"]:::frontier
    futuresForwardConvexity["Futures–forward convexity adjustment"]:::frontier
    hjmAffineModels["HJM recovers Ho–Lee and Vasicek"]:::frontier
    hjmBondDynamics["HJM bond-price dynamics"]:::frontier
    hjmDriftCondition["HJM drift condition"]:::frontier
    hjmLogBondDynamics["HJM log-bond dynamics"]:::frontier
    hjmMusiela["HJM Musiela parametrization"]:::frontier
    hjmShortRate["HJM induces a short-rate model"]:::frontier
    lmmForwardMartingale["LIBOR market model forward martingale"]:::frontier
    siegelParadox["Siegel's paradox"]:::frontier
    zeroCouponBondPrice["The zero-coupon bond price is a price"]:::frontier
  end
  subgraph frontier_valuationTrees["⏳ frontier · Valuation · Trees"]
    americanPutPremium["American put early-exercise premium"]:::frontier
    binomialBarrierReflection["Binomial barrier prices via reflection"]:::frontier
  end
  subgraph frontier_valuationVolatility["⏳ frontier · Valuation · Volatility"]
    batesCf["Bates characteristic function"]:::frontier
    carrLeeMoment["Carr–Lee moment formula"]:::frontier
    cevCall["CEV European call"]:::frontier
    dupireLocalVol["Dupire local volatility"]:::frontier
    hestonCf["Heston characteristic function"]:::frontier
    roughHestonPathwiseUniqueness["Rough-Heston pathwise uniqueness"]:::frontier
    sabrHagan["SABR Hagan asymptotic implied vol"]:::frontier
    schrodingerSpxVix["Schrödinger calibration of SPX/VIX"]:::frontier
    smileNoArbitrage["Smile no-arbitrage (Roper, SVI)"]:::frontier
  end

  contract --> contractValue
  brownianMotion --> hjmModel
  brownianMotion --> itoIntegralClm
  market --> pricingMeasure
  quantile --> valueAtRisk
  standardNormalCdf --> aaveLiquidationKmv
  brownianMotion --> americanPutOptimalExercise
  gbm --> americanPutOptimalExercise
  standardNormalCdf --> bachelierCall
  brownianMotion --> bracketCompensator
  carrMadan --> breedenLitzenberger
  standardNormalCdf --> bsCall
  standardNormalCdf --> bsDelta
  standardNormalCdf --> bsPde
  portfolioVariance --> capmEquilibrium
  coherentRiskMeasure --> coherentRiskRepresentation
  coneSeparation --> coherentRiskRepresentation
  emm --> continuousFtap
  martingaleTransform --> continuousFtap
  brownianMotion --> dupireZeroRates
  carrMadan --> dupireZeroRates
  expectedUtility --> expectedUtilityAxioms
  emm --> firstFtap
  martingaleTransform --> firstFtap
  changeOfNumeraire --> forwardMeasure
  copula --> frechetHoeffding
  quantile --> gaussianQuantile
  brownianMotion --> girsanovBrownianCharacterisation
  compoundPoissonMgf --> jumpDiffusionIncompleteness
  quantile --> largePortfolioLimit
  standardNormalCdf --> largePortfolioLimit
  empiricalCdfStrongLaw --> largePortfolioLimit
  brownianMotion --> levyCharacterization
  coherentRiskMeasure --> logUtilityAcceptance
  expectedUtility --> logUtilityAcceptance
  portfolioVariance --> markowitzLagrangian
  kktSufficiency --> markowitzLagrangian
  doobMaximalInequality --> martingaleConvergence
  compoundPoissonMgf --> mertonRiskNeutralDrift
  standardNormalCdf --> mertonStructuralDefault
  brownianMotion --> quadraticVariation
  quantile --> quantileTransform
  brownianMotion --> schwartzCommodityFutures
  brownianMotion --> sdeStrongSolution
  emm --> secondFtap
  martingaleTransform --> secondFtap
  compoundPoissonMgf --> varianceSwapJumpBias
  valueAtRisk --> expectedShortfall
  contract --> black76Caplet
  contractValue --> black76Caplet
  standardNormalCdf --> black76Caplet
  bsCall --> black76Caplet
  forwardMeasure --> black76Caplet
  contract --> crrBsConvergence
  contractValue --> crrBsConvergence
  standardNormalCdf --> crrBsConvergence
  portfolioVariance --> gaussianPortfolioVar
  quantile --> gaussianPortfolioVar
  valueAtRisk --> gaussianPortfolioVar
  gaussianQuantile --> gaussianPortfolioVar
  brownianMotion --> itoFormulaC2
  itoIntegralClm --> itoFormulaC2
  standardNormalCdf --> jumpDiffusionMixing
  bsCall --> jumpDiffusionMixing
  compoundPoissonMgf --> jumpDiffusionMixing
  standardNormalCdf --> margrabe
  bsCall --> margrabe
  esscherTilt --> margrabe
  brownianMotion --> marketCompleteness
  itoIntegralClm --> marketCompleteness
  brownianMotion --> martingaleRepresentation
  itoIntegralClm --> martingaleRepresentation
  brownianMotion --> physicalMeasurePricing
  contract --> physicalMeasurePricing
  contractValue --> physicalMeasurePricing
  quantile --> potentialFutureExposure
  valueAtRisk --> potentialFutureExposure
  gaussianQuantile --> potentialFutureExposure
  contract --> putCallParity
  contractValue --> putCallParity
  quantile --> sklar
  quantileTransform --> sklar
  portfolioVariance --> tangentPortfolioEfficient
  markowitzLagrangian --> tangentPortfolioEfficient
  standardNormalCdf --> unilateralCva
  bachelierCall --> unilateralCva
  quantile --> varNotSubadditive
  valueAtRisk --> varNotSubadditive
  brownianMotion --> bsDeltaHedge
  gbm --> bsDeltaHedge
  standardNormalCdf --> bsDeltaHedge
  bsCall --> bsDeltaHedge
  bsDelta --> bsDeltaHedge
  feynmanKacHeatEq --> bsDeltaHedge
  itoFormulaC2 --> bsDeltaHedge
  portfolioVariance --> eulerAllocation
  quantile --> eulerAllocation
  valueAtRisk --> eulerAllocation
  gaussianPortfolioVar --> eulerAllocation
  coherentRiskMeasure --> expectedShortfallCoherent
  expectedShortfall --> expectedShortfallCoherent
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
  contract --> hedgedPositionRisk
  contractValue --> hedgedPositionRisk
  expectedShortfall --> hedgedPositionRisk
  quantile --> hedgedPositionRisk
  valueAtRisk --> hedgedPositionRisk
  binomialRepresentation --> hedgedPositionRisk
  brownianMotion --> itoProductRule
  itoFormulaC2 --> itoProductRule
  expectedShortfall --> quantileElicitability
  quantile --> quantileElicitability
  valueAtRisk --> quantileElicitability
  quantileTransform --> quantileElicitability
  expectedShortfall --> rockafellarUryasev
  quantile --> rockafellarUryasev
  valueAtRisk --> rockafellarUryasev
  quantileTransform --> rockafellarUryasev
  emm --> pricingFunctional
  contractValue --> pricingFunctional
  changeOfNumeraire --> pricingFunctional
  secondFtap --> pricingFunctional
  marketCompleteness --> pricingFunctional
  standardNormalCdf --> realErf
  aaveLiquidationKmv --> aaveHealthFactorBound
  vasicekBondPde --> affineTermStructure
  snellEnvelope --> americanPutPremium
  emm --> aptPricing
  capmEquilibrium --> aptPricing
  impermanentLoss --> balancerInvariant
  reflectionPrinciple --> barrierLookbackClosedForms
  bsCall --> barrierLookbackClosedForms
  hestonCf --> batesCf
  jumpDiffusionLaw --> batesCf
  snellEnvelope --> bermudanCallableSnell
  binomialRepresentation --> binomialBarrierReflection
  reflectionPrinciple --> blackCoxDefault
  standardNormalCdf --> blackCoxDefault
  bracketCompensator --> bracketQuadraticVariation
  quadraticVariation --> bracketQuadraticVariation
  itoIntegralMartingale --> bracketQuadraticVariation
  brownianMotion --> brownianNowhereDifferentiable
  pricingFunctional --> bsArbitrageFreePrice
  bsCall --> bsArbitrageFreePrice
  physicalMeasurePricing --> bsArbitrageFreePrice
  marketCompleteness --> bsArbitrageFreePrice
  bsDeltaHedge --> bsArbitrageFreePrice
  bsCall --> carrLeeMoment
  bsCall --> cevCall
  affineTermStructure --> cirBondLoadings
  martingaleRepresentation --> clarkOcone
  changeOfNumeraire --> cmsConvexityAdjustment
  bondImmunization --> compoundExchangeRateBridge
  compoundPoissonMgf --> cramerLundbergClaims
  pricingFunctional --> cvaIsPrice
  unilateralCva --> cvaIsPrice
  coherentRiskRepresentation --> delbaenRepresentation
  expectedShortfallDual --> delbaenRepresentation
  firstFtap --> dmwFtap
  emm --> dmwFtap
  bsPde --> dupireLocalVol
  feynmanKacVariableCoefficient --> dupireLocalVol
  dupireZeroRates --> dupireLocalVol
  esscherTilt --> esscherEmmLevy
  jumpDiffusionLaw --> esscherEmmLevy
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
  glostenMilgromQuote --> glostenMilgromPricingMeasure
  pricingFunctional --> glostenMilgromPricingMeasure
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
  pricingFunctional --> jumpDiffusionPrice
  esscherEmmLevy --> jumpDiffusionPrice
  jumpDiffusionMixing --> jumpDiffusionPrice
  mertonRiskNeutralDrift --> jumpDiffusionPrice
  jumpDiffusionLaw --> kouJumpDiffusion
  bsCall --> kouJumpDiffusion
  expectedShortfallCoherent --> kusuoka
  coherentRiskMeasure --> kusuoka
  oneFactorCopulaDefault --> largePoolLoss
  gaussianFactorCopula --> largePoolLoss
  standardNormalCdf --> largePoolLoss
  largePortfolioLimit --> largePoolLoss
  brownianMotion --> lawIteratedLogarithm
  survivalModel --> lifeInsuranceEpv
  survivalFunction --> lifeInsuranceEpv
  blackCoxDefault --> liquidationFirstPassage
  aaveLiquidationKmv --> liquidationFirstPassage
  changeOfNumeraire --> lmmForwardMartingale
  changeOfNumeraire --> logOptimalNumeraire
  continuousFtap --> logOptimalNumeraire
  pricingFunctional --> lpPositionPrice
  uniswapV3CoveredCall --> lpPositionPrice
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
  carrMadan --> modelFreeVariance
  girsanovContinuousEmm --> novikovGirsanov
  gaussianFactorCopula --> oneFactorCopulaDefault
  standardNormalCdf --> oneFactorCopulaDefault
  largePortfolioLimit --> oneFactorCopulaDefault
  compoundPoissonMgf --> panjerRecursion
  snellEnvelope --> perpetualAmerican
  bsPde --> perpetualAmerican
  markovPathLaw --> perronFrobeniusMarkov
  pricingFunctional --> premiumIsPrice
  survivalFunction --> premiumIsPrice
  esscherTilt --> premiumIsPrice
  brownianMotion --> purgedCvIndependence
  quantile --> quantileConvergenceInDistribution
  brownianMotion --> reflectionPrinciple
  coherentRiskMeasure --> riskMeasureFamilies
  riskParityFoc --> riskParityNAsset
  sdeStrongSolution --> roughHestonPathwiseUniqueness
  bsCall --> sabrHagan
  modelFreeVariance --> schrodingerSpxVix
  sdeStrongSolution --> sdeContinuousSolution
  utilityStatePriceDensity --> sdfCapmHansenJagannathan
  capmEquilibrium --> sdfCapmHansenJagannathan
  sharpeRatio --> sdfCapmHansenJagannathan
  marketCompleteness --> secondFtapConverse
  secondFtap --> secondFtapConverse
  dmwFtap --> semistaticFtap
  carrMadan --> semistaticFtap
  itoFormulaC2 --> siegelParadox
  quantile --> sklarGeneral
  carrMadan --> smileNoArbitrage
  bsCall --> smileNoArbitrage
  brownianMotion --> stefanUniqueness
  stochasticFubini --> stochasticFubiniLevy
  stochasticFubini --> stochasticFubiniProcess
  pricingFunctional --> superhedgingCoherent
  coherentRiskMeasure --> superhedgingCoherent
  survivalFunction --> survivalModel
  survivalModel --> thieleReserve
  survivalFunction --> thieleReserve
  sdeStrongSolution --> timeInconsistentEquilibrium
  margrabe --> twoAssetOptionFormulas
  bsCall --> twoAssetOptionFormulas
  pricingFunctional --> utilityStatePriceDensity
  kellyCriterion --> utilityStatePriceDensity
  bsCall --> varianceGammaCall
  martingaleTransform --> varianceOptimalHedging
  emm --> varianceOptimalHedging
  expectedUtilityAxioms --> vonNeumannMorgenstern
  expectedUtility --> vonNeumannMorgenstern
  pricingFunctional --> zeroCouponBondPrice
  bondImmunization --> zeroCouponBondPrice

  classDef proved fill:#d4edda,stroke:#28a745,color:#111;
  classDef upstream fill:#d9e8f6,stroke:#1f6fb2,color:#111;
  classDef partial fill:#ffe5d0,stroke:#d9534f,color:#111;
  classDef frontier fill:#fff3cd,stroke:#d39e00,color:#111;
```

| node | status | issues and pull requests |
|---|---|---|
| `def:brownian-motion` Brownian motion (Mathlib, upstream) | ✅ upstream | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Abrownian-motion%22%20in%3Abody) |
| `def:coherent-risk-measure` Coherent risk measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acoherent-risk-measure%22%20in%3Abody) |
| `def:contract` Contract | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acontract%22%20in%3Abody) |
| `def:copula` Copula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acopula%22%20in%3Abody) |
| `def:emm` Equivalent martingale measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aemm%22%20in%3Abody) |
| `def:expected-utility` Expected utility | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aexpected-utility%22%20in%3Abody) |
| `def:gaussian-factor-copula` One-factor Gaussian copula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Agaussian-factor-copula%22%20in%3Abody) |
| `def:gbm` Geometric Brownian motion | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Agbm%22%20in%3Abody) |
| `def:market` Market | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Amarket%22%20in%3Abody) |
| `def:portfolio-variance` Portfolio variance | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aportfolio-variance%22%20in%3Abody) |
| `def:quantile` Quantile function | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aquantile%22%20in%3Abody) |
| `def:sharpe-ratio` Sharpe ratio | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asharpe-ratio%22%20in%3Abody) |
| `def:standard-normal-cdf` Standard normal distribution function Φ | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Astandard-normal-cdf%22%20in%3Abody) |
| `def:survival-function` Survival function | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asurvival-function%22%20in%3Abody) |
| `thm:binomial-representation` Martingale representation in the binomial model | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-representation%22%20in%3Abody) |
| `thm:bond-immunization` Duration and immunization | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abond-immunization%22%20in%3Abody) |
| `thm:carr-madan` Carr–Madan static replication | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acarr-madan%22%20in%3Abody) |
| `thm:change-of-numeraire` Change of numéraire | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Achange-of-numeraire%22%20in%3Abody) |
| `thm:compound-poisson-mgf` Compound Poisson moment generating function | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompound-poisson-mgf%22%20in%3Abody) |
| `thm:cone-separation` Separation theorem for closed convex cones | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acone-separation%22%20in%3Abody) |
| `thm:doob-decomposition` Doob decomposition | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adoob-decomposition%22%20in%3Abody) |
| `thm:doob-maximal-inequality` Doob's $L^p$ maximal inequality | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adoob-maximal-inequality%22%20in%3Abody) |
| `thm:empirical-cdf-strong-law` Strong law for the empirical distribution function | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aempirical-cdf-strong-law%22%20in%3Abody) |
| `thm:esscher-tilt` Esscher transform of a Gaussian | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aesscher-tilt%22%20in%3Abody) |
| `thm:feynman-kac-heat-eq` Feynman–Kac formula for the heat equation | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afeynman-kac-heat-eq%22%20in%3Abody) |
| `thm:glosten-milgrom-quote` Glosten–Milgrom bid and ask quotes | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglosten-milgrom-quote%22%20in%3Abody) |
| `thm:heston-pde` Heston model pricing equation | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aheston-pde%22%20in%3Abody) |
| `thm:hoeffding-covariance` Hoeffding's covariance identity | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahoeffding-covariance%22%20in%3Abody) |
| `thm:impermanent-loss` Impermanent loss | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aimpermanent-loss%22%20in%3Abody) |
| `thm:intensity-default-model` Intensity model of default | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aintensity-default-model%22%20in%3Abody) |
| `thm:interest-rate-parity` Covered interest-rate parity | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ainterest-rate-parity%22%20in%3Abody) |
| `thm:kelly-criterion` Kelly criterion | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akelly-criterion%22%20in%3Abody) |
| `thm:key-rate-duration` Key-rate durations | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akey-rate-duration%22%20in%3Abody) |
| `thm:kkt-sufficiency` Karush–Kuhn–Tucker sufficiency for convex quadratic programs | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akkt-sufficiency%22%20in%3Abody) |
| `thm:markov-path-law` Ionescu–Tulcea theorem: the law of a Markov chain | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkov-path-law%22%20in%3Abody) |
| `thm:marshall-olkin` Marshall–Olkin first-to-default | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarshall-olkin%22%20in%3Abody) |
| `thm:martingale-transform` Martingale transform | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-transform%22%20in%3Abody) |
| `thm:optional-sampling` Optional sampling theorem | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aoptional-sampling%22%20in%3Abody) |
| `thm:risk-parity-foc` Risk parity | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-parity-foc%22%20in%3Abody) |
| `thm:sde-pathwise-uniqueness` Pathwise uniqueness for SDEs with Lipschitz coefficients | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-pathwise-uniqueness%22%20in%3Abody) |
| `thm:snell-envelope` Snell envelope | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asnell-envelope%22%20in%3Abody) |
| `thm:stochastic-fubini` Stochastic Fubini theorem | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini%22%20in%3Abody) |
| `thm:uniswap-v3-covered-call` A concentrated-liquidity position is dominated by a covered call | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Auniswap-v3-covered-call%22%20in%3Abody) |
| `thm:vasicek-bond-pde` Vasicek bond price | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avasicek-bond-pde%22%20in%3Abody) |
| `def:contract-value` Value of a contract | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acontract-value%22%20in%3Abody) |
| `def:hjm-model` Heath–Jarrow–Morton model | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Ahjm-model%22%20in%3Abody) |
| `def:ito-integral-clm` Itô integral and Itô isometry | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aito-integral-clm%22%20in%3Abody) |
| `def:pricing-measure` Pricing measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Apricing-measure%22%20in%3Abody) |
| `def:value-at-risk` Value-at-risk | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Avalue-at-risk%22%20in%3Abody) |
| `thm:aave-liquidation-kmv` Liquidation of a lending position is Merton default | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaave-liquidation-kmv%22%20in%3Abody) |
| `thm:american-put-optimal-exercise` Optimal exercise of the American put | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-optimal-exercise%22%20in%3Abody) |
| `thm:bachelier-call` Bachelier call price formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abachelier-call%22%20in%3Abody) |
| `thm:bracket-compensator` Bracket of the Itô integral | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abracket-compensator%22%20in%3Abody) |
| `thm:breeden-litzenberger` Breeden–Litzenberger formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abreeden-litzenberger%22%20in%3Abody) |
| `thm:bs-call` Black–Scholes call price formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-call%22%20in%3Abody) |
| `thm:bs-delta` Black–Scholes Greeks | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-delta%22%20in%3Abody) |
| `thm:bs-pde` Black–Scholes partial differential equation | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-pde%22%20in%3Abody) |
| `thm:capm-equilibrium` Capital asset pricing model | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acapm-equilibrium%22%20in%3Abody) |
| `thm:coherent-risk-representation` Robust representation of coherent risk measures | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acoherent-risk-representation%22%20in%3Abody) |
| `thm:continuous-ftap` Fundamental theorem of asset pricing in continuous time | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acontinuous-ftap%22%20in%3Abody) |
| `thm:dupire-zero-rates` Dupire's local volatility formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adupire-zero-rates%22%20in%3Abody) |
| `thm:expected-utility-axioms` von Neumann–Morgenstern expected utility | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-utility-axioms%22%20in%3Abody) |
| `thm:first-ftap` First fundamental theorem of asset pricing | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afirst-ftap%22%20in%3Abody) |
| `thm:forward-measure` Forward measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aforward-measure%22%20in%3Abody) |
| `thm:frechet-hoeffding` Fréchet–Hoeffding bounds | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afrechet-hoeffding%22%20in%3Abody) |
| `thm:gaussian-quantile` Gaussian quantile function | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agaussian-quantile%22%20in%3Abody) |
| `thm:girsanov-brownian-characterisation` Girsanov's theorem | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agirsanov-brownian-characterisation%22%20in%3Abody) |
| `thm:jump-diffusion-incompleteness` Incompleteness of jump-diffusion markets | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-incompleteness%22%20in%3Abody) |
| `thm:large-portfolio-limit` Vasicek's large-portfolio limit | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alarge-portfolio-limit%22%20in%3Abody) |
| `thm:levy-characterization` Lévy's characterization of Brownian motion | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alevy-characterization%22%20in%3Abody) |
| `thm:log-utility-acceptance` Acceptance sets from expected utility | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alog-utility-acceptance%22%20in%3Abody) |
| `thm:markowitz-lagrangian` Markowitz mean–variance optimality | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkowitz-lagrangian%22%20in%3Abody) |
| `thm:martingale-convergence` Martingale convergence theorem | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-convergence%22%20in%3Abody) |
| `thm:merton-risk-neutral-drift` Risk-neutral drift of a jump-diffusion | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-risk-neutral-drift%22%20in%3Abody) |
| `thm:merton-structural-default` Merton's structural model of default | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-structural-default%22%20in%3Abody) |
| `thm:quadratic-variation` Quadratic variation of Brownian motion | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquadratic-variation%22%20in%3Abody) |
| `thm:quantile-transform` Quantile transform and probability integral transform | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquantile-transform%22%20in%3Abody) |
| `thm:schwartz-commodity-futures` Schwartz commodity futures price | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aschwartz-commodity-futures%22%20in%3Abody) |
| `thm:sde-strong-solution` Existence and uniqueness of solutions of Lipschitz SDEs | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-strong-solution%22%20in%3Abody) |
| `thm:second-ftap` Second fundamental theorem of asset pricing | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asecond-ftap%22%20in%3Abody) |
| `thm:variance-swap-jump-bias` Variance swap and the log contract | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-swap-jump-bias%22%20in%3Abody) |
| `def:expected-shortfall` Expected shortfall | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aexpected-shortfall%22%20in%3Abody) |
| `thm:black76-caplet` Black's caplet formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ablack76-caplet%22%20in%3Abody) |
| `thm:crr-bs-convergence` Cox–Ross–Rubinstein convergence to Black–Scholes | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acrr-bs-convergence%22%20in%3Abody) |
| `thm:gaussian-portfolio-var` Value-at-risk of a Gaussian portfolio | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agaussian-portfolio-var%22%20in%3Abody) |
| `thm:ito-formula-c2` Itô's formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-c2%22%20in%3Abody) |
| `thm:jump-diffusion-mixing` Merton's jump-diffusion formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-mixing%22%20in%3Abody) |
| `thm:margrabe` Margrabe's exchange option formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amargrabe%22%20in%3Abody) |
| `thm:market-completeness` Completeness of the Brownian market | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-completeness%22%20in%3Abody) |
| `thm:martingale-representation` Martingale representation theorem | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-representation%22%20in%3Abody) |
| `thm:physical-measure-pricing` Black–Scholes pricing under the physical measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aphysical-measure-pricing%22%20in%3Abody) |
| `thm:potential-future-exposure` Potential future exposure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apotential-future-exposure%22%20in%3Abody) |
| `thm:put-call-parity` Put-call parity | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aput-call-parity%22%20in%3Abody) |
| `thm:sklar` Sklar's theorem | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asklar%22%20in%3Abody) |
| `thm:tangent-portfolio-efficient` Tangent portfolio | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atangent-portfolio-efficient%22%20in%3Abody) |
| `thm:unilateral-cva` Credit valuation adjustment | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aunilateral-cva%22%20in%3Abody) |
| `thm:var-not-subadditive` Value-at-risk is not subadditive | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avar-not-subadditive%22%20in%3Abody) |
| `thm:bs-delta-hedge` Black–Scholes delta hedging | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-delta-hedge%22%20in%3Abody) |
| `thm:euler-allocation` Euler allocation of value-at-risk | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aeuler-allocation%22%20in%3Abody) |
| `thm:expected-shortfall-coherent` Expected shortfall is coherent | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-coherent%22%20in%3Abody) |
| `thm:expected-shortfall-dual` Dual representation of expected shortfall | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-dual%22%20in%3Abody) |
| `thm:expected-shortfall-not-elicitable` Expected shortfall is not elicitable | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-not-elicitable%22%20in%3Abody) |
| `thm:hedged-position-risk` Risk of a hedged position | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahedged-position-risk%22%20in%3Abody) |
| `thm:ito-product-rule` Itô's product rule | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-product-rule%22%20in%3Abody) |
| `thm:quantile-elicitability` Elicitability of the quantile | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquantile-elicitability%22%20in%3Abody) |
| `thm:rockafellar-uryasev` Rockafellar–Uryasev formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arockafellar-uryasev%22%20in%3Abody) |
| `def:pricing-functional` The pricing functional | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Apricing-functional%22%20in%3Abody) |
| `def:real-erf` erf / erfc / erfinv for Mathlib | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Areal-erf%22%20in%3Abody) |
| `thm:aave-health-factor-bound` Aave multi-asset health factor: a liquidation bound | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaave-health-factor-bound%22%20in%3Abody) |
| `thm:affine-term-structure` Affine term structure | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaffine-term-structure%22%20in%3Abody) |
| `thm:american-put-premium` American put early-exercise premium | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aamerican-put-premium%22%20in%3Abody) |
| `thm:apt-pricing` APT exact-factor pricing | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aapt-pricing%22%20in%3Abody) |
| `thm:balancer-invariant` Balancer constant-mean AMM | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abalancer-invariant%22%20in%3Abody) |
| `thm:barrier-lookback-closed-forms` Barrier and lookback closed forms | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abarrier-lookback-closed-forms%22%20in%3Abody) |
| `thm:bates-cf` Bates characteristic function | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abates-cf%22%20in%3Abody) |
| `thm:bermudan-callable-snell` Callable bonds and Bermudan swaptions by Snell envelope | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abermudan-callable-snell%22%20in%3Abody) |
| `thm:binomial-barrier-reflection` Binomial barrier prices via reflection | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-barrier-reflection%22%20in%3Abody) |
| `thm:black-cox-default` Black–Cox first-passage default | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ablack-cox-default%22%20in%3Abody) |
| `thm:bracket-quadratic-variation` Bracket is the quadratic variation of an Itô integral | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abracket-quadratic-variation%22%20in%3Abody) |
| `thm:brownian-nowhere-differentiable` Brownian paths are nowhere differentiable | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abrownian-nowhere-differentiable%22%20in%3Abody) |
| `thm:bs-arbitrage-free-price` The Black–Scholes price is the arbitrage-free price | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-arbitrage-free-price%22%20in%3Abody) |
| `thm:buhlmann-credibility` Bühlmann credibility | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abuhlmann-credibility%22%20in%3Abody) |
| `thm:carr-lee-moment` Carr–Lee moment formula | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acarr-lee-moment%22%20in%3Abody) |
| `thm:cev-call` CEV European call | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acev-call%22%20in%3Abody) |
| `thm:cir-bond-loadings` CIR bond-price loadings | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acir-bond-loadings%22%20in%3Abody) |
| `thm:clark-ocone` L¹ martingale representation and Clark–Ocone | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aclark-ocone%22%20in%3Abody) |
| `thm:cms-convexity-adjustment` CMS convexity adjustment | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acms-convexity-adjustment%22%20in%3Abody) |
| `thm:compensated-poisson-integral` Compensated-Poisson integral | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompensated-poisson-integral%22%20in%3Abody) |
| `thm:compound-exchange-rate-bridge` Compound's exchange rate as a money-market account | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompound-exchange-rate-bridge%22%20in%3Abody) |
| `thm:cramer-lundberg-claims` Cramér–Lundberg claims | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acramer-lundberg-claims%22%20in%3Abody) |
| `thm:cva-is-price` CVA is the price of the default loss | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acva-is-price%22%20in%3Abody) |
| `thm:delbaen-representation` Delbaen's representation of coherent risk measures | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adelbaen-representation%22%20in%3Abody) |
| `thm:dmw-ftap` Dalang–Morton–Willinger FTAP | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Admw-ftap%22%20in%3Abody) |
| `thm:dupire-local-vol` Dupire local volatility | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adupire-local-vol%22%20in%3Abody) |
| `thm:esscher-emm-levy` Esscher EMM for exponential-Lévy markets | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aesscher-emm-levy%22%20in%3Abody) |
| `thm:expected-utility-risk-aversion` Expected utility and risk aversion | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-utility-risk-aversion%22%20in%3Abody) |
| `thm:feynman-kac-variable-coefficient` Variable-coefficient Feynman–Kac | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afeynman-kac-variable-coefficient%22%20in%3Abody) |
| `thm:forward-start-call` Forward-start call | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aforward-start-call%22%20in%3Abody) |
| `thm:futures-basis-convergence` Contango, backwardation and basis convergence | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afutures-basis-convergence%22%20in%3Abody) |
| `thm:futures-forward-convexity` Futures–forward convexity adjustment | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afutures-forward-convexity%22%20in%3Abody) |
| `thm:girsanov-continuous-emm` Girsanov EMM from the Itô tower | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agirsanov-continuous-emm%22%20in%3Abody) |
| `thm:glivenko-cantelli` Glivenko–Cantelli theorem | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglivenko-cantelli%22%20in%3Abody) |
| `thm:glosten-milgrom-pricing-measure` The Glosten–Milgrom quote process is a martingale | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglosten-milgrom-pricing-measure%22%20in%3Abody) |
| `thm:heston-cf` Heston characteristic function | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aheston-cf%22%20in%3Abody) |
| `thm:hjm-affine-models` HJM recovers Ho–Lee and Vasicek | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-affine-models%22%20in%3Abody) |
| `thm:hjm-bond-dynamics` HJM bond-price dynamics | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-bond-dynamics%22%20in%3Abody) |
| `thm:hjm-drift-condition` HJM drift condition | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-drift-condition%22%20in%3Abody) |
| `thm:hjm-log-bond-dynamics` HJM log-bond dynamics | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-log-bond-dynamics%22%20in%3Abody) |
| `thm:hjm-musiela` HJM Musiela parametrization | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-musiela%22%20in%3Abody) |
| `thm:hjm-short-rate` HJM induces a short-rate model | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ahjm-short-rate%22%20in%3Abody) |
| `thm:implied-vol-existence` Implied volatility for every arbitrage-free price | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aimplied-vol-existence%22%20in%3Abody) |
| `thm:ito-formula-2d` Two-process Itô formula | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-2d%22%20in%3Abody) |
| `thm:ito-integral-martingale` General-integrand Itô process is a martingale | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-integral-martingale%22%20in%3Abody) |
| `thm:ito-levy-formula` Itô–Lévy change of variables | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-levy-formula%22%20in%3Abody) |
| `thm:jump-diffusion-law` Compound-Poisson and jump-diffusion law | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-law%22%20in%3Abody) |
| `thm:jump-diffusion-price` Jump-diffusion prices under the Esscher pricing measure | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ajump-diffusion-price%22%20in%3Abody) |
| `thm:kou-jump-diffusion` Kou double-exponential jump-diffusion | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akou-jump-diffusion%22%20in%3Abody) |
| `thm:kusuoka` Kusuoka representation | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akusuoka%22%20in%3Abody) |
| `thm:kyle-equilibrium` Kyle single-period equilibrium | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akyle-equilibrium%22%20in%3Abody) |
| `thm:large-pool-loss` Large homogeneous pool loss law | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alarge-pool-loss%22%20in%3Abody) |
| `thm:law-iterated-logarithm` Law of the iterated logarithm | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alaw-iterated-logarithm%22%20in%3Abody) |
| `thm:life-insurance-epv` Life annuity and insurance EPV | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alife-insurance-epv%22%20in%3Abody) |
| `thm:liquidation-first-passage` Liquidation before maturity as first passage | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aliquidation-first-passage%22%20in%3Abody) |
| `thm:lmm-forward-martingale` LIBOR market model forward martingale | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Almm-forward-martingale%22%20in%3Abody) |
| `thm:log-optimal-numeraire` Log-optimal portfolio is the numéraire | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alog-optimal-numeraire%22%20in%3Abody) |
| `thm:lp-position-price` An AMM liquidity position is a contract | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alp-position-price%22%20in%3Abody) |
| `thm:lundberg-ruin-bound` Lundberg ruin bound | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alundberg-ruin-bound%22%20in%3Abody) |
| `thm:margrabe-numeraire` Margrabe and chooser via the S²-numéraire | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amargrabe-numeraire%22%20in%3Abody) |
| `thm:markowitz-kkt-necessity` Markowitz first-order conditions are necessary | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkowitz-kkt-necessity%22%20in%3Abody) |
| `thm:martingale-representation-vector` Vector martingale representation | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-representation-vector%22%20in%3Abody) |
| `thm:merton-credit-spread` Merton structural credit spread | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-credit-spread%22%20in%3Abody) |
| `thm:merton-pide` Merton PIDE | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-pide%22%20in%3Abody) |
| `thm:merton-portfolio-fraction` Merton myopic risky fraction | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-portfolio-fraction%22%20in%3Abody) |
| `thm:model-free-variance` Model-free implied variance replication | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amodel-free-variance%22%20in%3Abody) |
| `thm:novikov-girsanov` Novikov Girsanov for unbounded θ | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Anovikov-girsanov%22%20in%3Abody) |
| `thm:one-factor-copula-default` One-factor Gaussian copula default | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aone-factor-copula-default%22%20in%3Abody) |
| `thm:panjer-recursion` Panjer recursion | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apanjer-recursion%22%20in%3Abody) |
| `thm:perpetual-american` Perpetual American option | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aperpetual-american%22%20in%3Abody) |
| `thm:perron-frobenius-markov` Perron–Frobenius and finite Markov chain ergodicity | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aperron-frobenius-markov%22%20in%3Abody) |
| `thm:poisson-interarrival-iid` Poisson interarrivals are iid exponential | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apoisson-interarrival-iid%22%20in%3Abody) |
| `thm:premium-is-price` Insurance premiums are prices | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apremium-is-price%22%20in%3Abody) |
| `thm:propagator-no-arbitrage` Transient-impact propagator no-arbitrage | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apropagator-no-arbitrage%22%20in%3Abody) |
| `thm:purged-cv-independence` Purged cross-validation: σ-algebra independence | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apurged-cv-independence%22%20in%3Abody) |
| `thm:quantile-convergence-in-distribution` Quantiles under convergence in distribution | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquantile-convergence-in-distribution%22%20in%3Abody) |
| `thm:reflection-principle` Reflection principle for Brownian motion | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Areflection-principle%22%20in%3Abody) |
| `thm:risk-measure-families` Entropic, distortion and expectile risk measures | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-measure-families%22%20in%3Abody) |
| `thm:risk-parity-n-asset` N-asset risk parity exists and is unique | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-parity-n-asset%22%20in%3Abody) |
| `thm:rough-heston-pathwise-uniqueness` Rough-Heston pathwise uniqueness | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arough-heston-pathwise-uniqueness%22%20in%3Abody) |
| `thm:sabr-hagan` SABR Hagan asymptotic implied vol | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asabr-hagan%22%20in%3Abody) |
| `thm:schrodinger-spx-vix` Schrödinger calibration of SPX/VIX | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aschrodinger-spx-vix%22%20in%3Abody) |
| `thm:sde-continuous-solution` Continuous strong solutions on every horizon | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-continuous-solution%22%20in%3Abody) |
| `thm:sdf-capm-hansen-jagannathan` CAPM and Hansen–Jagannathan from the discount factor | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asdf-capm-hansen-jagannathan%22%20in%3Abody) |
| `thm:second-ftap-converse` Second FTAP: uniqueness implies completeness | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asecond-ftap-converse%22%20in%3Abody) |
| `thm:semistatic-ftap` Semistatic FTAP with entropy | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asemistatic-ftap%22%20in%3Abody) |
| `thm:siegel-paradox` Siegel's paradox | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asiegel-paradox%22%20in%3Abody) |
| `thm:sklar-general` Sklar's theorem for arbitrary margins | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asklar-general%22%20in%3Abody) |
| `thm:smile-no-arbitrage` Smile no-arbitrage (Roper, SVI) | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asmile-no-arbitrage%22%20in%3Abody) |
| `thm:stefan-uniqueness` Stefan uniqueness with accumulating jumps | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astefan-uniqueness%22%20in%3Abody) |
| `thm:stochastic-fubini-levy` Stochastic Fubini for Itô–Lévy integrals | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini-levy%22%20in%3Abody) |
| `thm:stochastic-fubini-process` Stochastic Fubini for the integral process | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini-process%22%20in%3Abody) |
| `thm:superhedging-coherent` The superhedging price is a coherent risk measure | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asuperhedging-coherent%22%20in%3Abody) |
| `thm:survival-model` Survival model and life tables | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asurvival-model%22%20in%3Abody) |
| `thm:thiele-reserve` Thiele reserve | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Athiele-reserve%22%20in%3Abody) |
| `thm:time-inconsistent-equilibrium` Relaxed equilibria under time inconsistency | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atime-inconsistent-equilibrium%22%20in%3Abody) |
| `thm:two-asset-option-formulas` Stulz and Heynen–Kat two-asset formulas | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atwo-asset-option-formulas%22%20in%3Abody) |
| `thm:utility-state-price-density` Marginal utility is a state-price density | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Autility-state-price-density%22%20in%3Abody) |
| `thm:variance-gamma-call` Variance-gamma European call | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-gamma-call%22%20in%3Abody) |
| `thm:variance-optimal-hedging` Variance-optimal hedging | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-optimal-hedging%22%20in%3Abody) |
| `thm:von-neumann-morgenstern` von Neumann–Morgenstern representation theorem | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avon-neumann-morgenstern%22%20in%3Abody) |
| `thm:zero-coupon-bond-price` The zero-coupon bond price is a price | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Azero-coupon-bond-price%22%20in%3Abody) |
<!-- END GENERATED SPINE -->

---

## Foundations

### Brownian motion ✅ *(upstream)*
The driving noise: a process with independent, stationary, Gaussian increments,
`B t ~ N(0, t)`. The definition, `IsPreBrownianReal`, and its basic API are now in Mathlib
(`Mathlib/Probability/BrownianMotion/Basic.lean`). Rémy Degenne's
[`brownian-motion`](https://github.com/RemyDegenne/brownian-motion) package, on which this library
also builds, supplies the continuous modification and the filtered versions.

### Quadratic variation ✅
`∑ (B_{t_{k+1}} − B_{t_k})² → T` as the partition refines — in **L²**
(`tendsto_qv`) and **in probability** (`tendstoInMeasure_qv`).
→ *Finance:* realized variance accumulates linearly in time at unit rate — the
root of the "volatility² · time" that pervades pricing.
[`Probability/Brownian/QuadraticVariationL2.lean`](../MathFin/Probability/Brownian/QuadraticVariationL2.lean)

### Wiener isometry (L²) ✅
For **deterministic** step integrands, `E[(∫ φ dB)²] = ∫ φ² dt`
(`wiener_assembly_isometry`, `wienerIntegralLp_integral_sq`); step functions are
dense (`stepAssembly_denseRange`), giving the L² Wiener integral.
→ *Finance:* the L² geometry of payoffs built from a fixed (non-reacting)
position in Brownian noise.
[`Probability/Brownian/Wiener/WienerIntegralL2.lean`](../MathFin/Probability/Brownian/Wiener/WienerIntegralL2.lean)

### Adapted Itô isometry ✅
The genuinely stochastic version: for **random adapted** simple integrands,
`E[(∑ φₖ ΔBₖ)²] = ∑ E[φₖ²] Δtₖ` (`ito_isometry_discrete`). The cross terms vanish
by the **weak Markov property** (`integral_cross_increment_bilinear_eq_zero`) —
the distinction that separates Itô from Wiener — with the `∫ B dB` capstone
(`ito_isometry_brownian_self`).
→ *Finance:* a self-financing strategy whose position reacts to the path still
has variance equal to the sum of its per-period variances.
[`Probability/Brownian/Ito/ItoIsometryAdapted.lean`](../MathFin/Probability/Brownian/Ito/ItoIsometryAdapted.lean)

### Continuous Itô integral as a CLM on `[0,T]` ✅
The discrete Itô isometry (`assembly_isometry`) extended to a continuous linear
isometry `itoIntegralCLM : Lp ℝ 2 (timeMeasureHorizon ⊗ μ).trim 𝓕.predictable →L[ℝ]
Lp ℝ 2 μ` with `itoIntegralCLM_norm`. Density of T-bounded simple processes
(`simpleAssemblyHorizon_denseRange`) is proved by Dynkin's π-λ theorem on the basic
predictable rectangles (`isPiSystem_predictableRect`,
`generateFrom_predictableRect`), reducing orthogonality to `∫_R g dμ = 0` for
every basic rect `R = (a, b] × F` with `F ∈ ℱ_a`, then to all measurable sets
via `setIntegral_eq_zero_of_orthogonal_pred`, and finally to `g = 0` via
`Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`. The CLM falls out of
`LinearMap.extendOfNorm`. Its first genuine consumer is
`itoIntegralCLM_brownian`: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` *through the CLM* —
bridging the abstract integral to the concrete quadratic-variation limit, and
itself the template (clamp-truncation + isometry-Cauchy completion) any
unbounded-coefficient consumer would reuse.
→ *Finance:* the analytic foundation for the Itô calculus layer — every
predictable `L²` integrand on `[0, T]` has a well-defined Itô integral with
the isometry norm identity, the bedrock of SDE existence/uniqueness and the
Black–Scholes PDE derivation downstream.
[`Probability/Brownian/Ito/ItoIntegralCLM.lean`](../MathFin/Probability/Brownian/Ito/ItoIntegralCLM.lean)

### Itô's lemma — discrete pathwise core + continuous `x²` L² form ✅
The exact pathwise identity `f(X_N) − f(X_0) = ∑ f′(X_k)ΔX_k + ½∑ f″(X_k)(ΔX_k)²
+ ∑ R_k` (`discrete_ito_formula`), with the Taylor remainder `R_k` computed in
closed form for the keystone polynomials: `x²` (remainder `0`,
`discrete_squaring_identity`), `x³` (`discrete_cubing_identity`), `x⁴`. The
**continuous L² form** for `x²`: along the uniform partition, the Riemann sums
`∑ B·ΔB → ½(B_T² − B_0² − T)` in `L²(μ)` (`itoSquared_L2_tendsto_div2`), one
algebraic step from the discrete identity + the `L²` quadratic variation
`tendsto_qv`. The **time-dependent 2D** formula (`discrete_ito_formula_2d`,
`itoDrift2D`) carries the `∂_t f · Δt` term.
→ *Finance:* the `B_t² = 2∫B dB + t` keystone behind variance-swap pricing
and Doob's stochastic-integral definition.
[`Probability/Brownian/Ito/ItoSquaringIdentity.lean`](../MathFin/Probability/Brownian/Ito/ItoSquaringIdentity.lean),
[`Probability/Discrete/DiscreteItoPolynomial.lean`](../MathFin/Probability/Discrete/DiscreteItoPolynomial.lean),
[`Probability/Brownian/Ito/ItoFormulaSquaredL2.lean`](../MathFin/Probability/Brownian/Ito/ItoFormulaSquaredL2.lean),
[`Probability/Brownian/Ito/ItoLemma2D.lean`](../MathFin/Probability/Brownian/Ito/ItoLemma2D.lean)

### Geometric Brownian motion — SDE coefficient matching 🚧
Two honestly-distinct layers, NOT a continuous SDE-solution theorem:
* **Genuine (full):** the partials of `S(t, x) = S₀·exp((μ − ½σ²)t + σx)` are
  real `HasDerivAt` derivations from the `Real.exp` chain rule —
  `hasDerivAt_gbmValue_space` (`∂_x = σS`), `_time` (`∂_t = (μ−½σ²)S`),
  `_space_space` (`∂_xx = σ²S`).
* **Coefficient matching (algebraic):** `gbm_solves_sde` takes those partials as
  `HasDerivAt` hypotheses (so `HasDerivAt.unique` *forces* them to the genuine
  derivatives) and shows the 2D Itô drift under the Brownian generator
  `(0, 1)` is `μ·S` with diffusion `σ·S` — i.e. `S(t, B_t)` matches the Itô
  coefficients of `dS = μS dt + σS dB`. The `−½σ²` exponent cancels the `+½σ²`
  Itô term — that cancellation *is* the Itô correction.

What is **deferred** — and why it is *deferral, not absence*: the continuous-time
partition-limit Itô formula now **exists** as Summit A (`ito_formula_L2_bddDeriv`,
the L² Itô formula for `C³` functions with *bounded* derivatives), but it does not
directly reach GBM, whose exponential has *unbounded* derivatives. Bridging the
engine to GBM needs an unbounded-coefficient lift — a second keystone in the shape
of `itoIntegralCLM_brownian` (clamp-truncation + a martingale-difference L²
limit `∑ σM_{t_k} ΔB → M_T − 1`), or Summit-C localization. This is **deliberately
not built**: the operational result it would prove — *the discounted GBM is a
`Q`-martingale* — is already established directly via the Wald exponential
(`discountedGBM_isMartingale`; see *Continuous-time first FTAP* below). The lift
would buy an alternative *derivation route* to a theorem we already hold, not a new
result, so it is a poor trade against ~400 lines of parallel keystone.

The Black–Scholes PDE read in the Brownian coordinate is the next section's backward heat equation;
deriving it from a no-arbitrage `Q`-martingale by Itô's formula is not proved.
→ *Finance:* the asset dynamics underlying every BS-family closed form — the
genuine GBM derivatives in hand, the SDE-solution limit still to come.
[`Probability/Brownian/Ito/ItoLemma2D.lean`](../MathFin/Probability/Brownian/Ito/ItoLemma2D.lean)

### Expectation-form Itô / Feynman–Kac ✅
`E[f(Bₜ)] = f(0) + ½ ∫₀ᵗ E[f''(Bₛ)] ds` (`expectation_ito`,
`expectation_ito_isPreBrownian`), proved via the heat equation
(`heatConvolution_eq_add_integral_deriv`, `feynmanKac_boundary`).
→ *Finance:* how the expected value of a function of the asset evolves — the
`½σ²` second-order term that drives the Black–Scholes PDE.
[`Probability/Gaussian/FeynmanKacHeatEquation.lean`](../MathFin/Probability/Gaussian/FeynmanKacHeatEquation.lean)

### Feynman–Kac heat flow — kernel-side derivatives ✅
The kernel convolution `feynmanU g t x = ∫ z, g z · K(t, z − x) dz`, with the
heat kernel **jointly Fréchet-differentiable** (`hasFDerivAt_heatKernel` — the
one genuinely-2D ingredient), giving `∂_t/∂_x/∂_xx` of `feynmanU` by dominated
differentiation under the integral, and the heat equation `∂_t U = ½ ∂_xx U`
(`feynmanU_heat_equation`) for sub-Gaussian payoffs.
→ *Finance:* the heat flow whose discounted log-transform *is* the
Black–Scholes price surface — the analytic engine of the FK keystone (Pricing
section below).
[`Probability/Gaussian/FeynmanKacHeatEquation.lean`](../MathFin/Probability/Gaussian/FeynmanKacHeatEquation.lean)

### Markov path law (Ionescu–Tulcea) ✅
The law of a countable-state Markov chain constructed on path space via
`Kernel.trajMeasure`, with the finite-cylinder factorization through the
transition kernels (`markovPathMeasure_cylinder`) — proved by comp-product
marginal induction, not assumed.
→ *Finance:* the path-space measure underlying lattice/tree models — every
discrete pricing tree is a Markov path law.
[`Probability/Discrete/MarkovPathMeasure.lean`](../MathFin/Probability/Discrete/MarkovPathMeasure.lean)

## Change of measure — the centerpiece

### Static Girsanov via an Esscher tilt ✅
Tilting the physical Gaussian by an Esscher (exponential) density
(`gaussianReal_withDensity_esscher`, `hasLaw_esscher_tilt`) yields an *equivalent
probability measure* (`esscherTilt_isProbabilityMeasure`) under which the
discounted asset is a martingale and the call price is the discounted
risk-neutral expectation (`bs_call_formula_of_physical`).
→ *Finance:* **the risk-neutral measure is not an axiom — it is constructed from
the physical measure.** `BSCallHyp` stops being a hypothesis.
The tilt is the case `N(0,1)` of the Gaussian Esscher transform
`gaussianReal_tilted_const_mul` ([`Probability/Laws/Esscher.lean`](../MathFin/Probability/Laws/Esscher.lean)).
The same lemma gives the Esscher transform of a jump-diffusion without jumps
(`jumpDiffusionIncrementLaw_zero_tilted`). The same file's tilted moments and identification of
a law by its moment-generating function give the case with jumps
(`jumpDiffusionIncrementLaw_tilted`).
[`Models/BlackScholes/GaussianGirsanov.lean`](../MathFin/Models/BlackScholes/GaussianGirsanov.lean)

### BSCallHyp from a Brownian model ✅
A concrete Brownian-driven physical model produces the pricing hypothesis
directly (`BSCallHyp.of_isPreBrownian`, `bsTerminal_via_brownian`) — the second
route into `BSCallHyp`.
[`Models/BlackScholes/BSCallHypFromBrownian.lean`](../MathFin/Models/BlackScholes/BSCallHypFromBrownian.lean)

### Continuous-time first FTAP — discounted price is a `Q`-martingale ✅
Under the risk-neutral measure, the discounted Black–Scholes price
`e^{−rt} S_t = S₀ · exp(σ X_t − σ² t / 2)` is a continuous-time martingale w.r.t.
the Brownian filtration (`discountedGBM_isMartingale`) — the defining property of
the equivalent martingale measure, and the operational content of the first FTAP
in continuous time. It falls out *directly* from the **Wald exponential
martingale** (`IsFilteredPreBrownian.waldExponential_isMartingale`), with no
stochastic-integral machinery: the `− σ² t / 2` correction is exactly what makes
the conditional mean of the increment one. This is *why* the engine→GBM
Itô-representation bridge (see *Geometric Brownian motion* above) is deferral, not
a gap — the martingale property is already in hand.
→ *Finance:* the continuous-time EMM property — the discounted price is a fair
game under `Q`, the bedrock of arbitrage-free pricing.
[`Pricing/FTAP/ContinuousFTAP.lean`](../MathFin/Pricing/FTAP/ContinuousFTAP.lean)

## Pricing

### Black–Scholes call formula ✅
Under `BSCallHyp`, the call price is `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)`
(`bs_call_formula`).
→ *Finance:* the option price.
[`Models/BlackScholes/Call.lean`](../MathFin/Models/BlackScholes/Call.lean)

### `bs_identity` — the magic collapse ✅
The algebraic identity `S · φ(d₁) = K e^{−rτ} · φ(d₂)` (`bs_identity`) that makes
the pdf cross-terms cancel. It depends only on the `d₁`/`d₂` definitions and the
Gaussian density — a self-contained algebraic input, so it is a *root* in the
graph above (nothing in the spine proves it); it feeds the Greeks and the PDE.
→ *Finance:* the cancellation behind every clean Greek formula.
[`Models/BlackScholes/PDE.lean`](../MathFin/Models/BlackScholes/PDE.lean)

### Greeks ✅
δ (`hasDerivAt_bsV_S`), γ (`hasDerivAt_deriv_bsV_S`), vega (`hasDerivAt_bsV_sigma`),
θ (`hasDerivAt_bsV_t`), ρ (`hasDerivAt_bsV_r`) — each derived through
`bs_identity`.
→ *Finance:* the hedging sensitivities.
[`Models/BlackScholes/PDE.lean`](../MathFin/Models/BlackScholes/PDE.lean)

### Black–Scholes PDE ✅
`bsV` satisfies the Black–Scholes PDE (`bs_pde_holds`). *Correction recorded
2026-06-06, forced by the generated graph:* this page used to say "verified via
the Greeks and `bs_identity`" — the proof term shows otherwise. The PDE
statement carries the Greeks' closed forms in its slots, and the verification
is self-contained field algebra (`rw [bsV]; field_simp; ring`); it consumes
neither the Greek theorems nor `bs_identity`. The conceptual route Greeks →
PDE is real mathematics but a *different proof* than the one formalized; the
graph shows `thm:bs-pde` as a root, and that is the truth.
[`Models/BlackScholes/PDE.lean`](../MathFin/Models/BlackScholes/PDE.lean)

### BS PDE in the Brownian coordinate ✅
Read along the Brownian state, the discounted call price
`f(t,x) = e^{−rt}·V(S₀e^{(r−σ²/2)t+σx}, T−t)` solves the backward heat equation
`∂_t f + ½∂_xx f = 0` for `t < T` (`discountedCallBrownian_heat_equation`), with
`∂_x f = σ e^{−rt} S Φ(d₁)` (`hasDerivAt_discountedCallBrownian_x`), from the Feynman–Kac
heat-flow form of the price. This is the analytic fact behind the delta hedge. What is **not**
proved: that `f(t, B_t)` is a local martingale, by Itô's formula. The value function's `Γ` is
unbounded as `S → 0`, so the bounded time-dependent formula (`sc-thm-7.1.2`) does not reach it.
Until 2026-10-21 this section described `ring` identities between the PDE and an Itô-drift
balance; they were removed as restatements.
[`Models/BlackScholes/PDEFromIto.lean`](../MathFin/Models/BlackScholes/PDEFromIto.lean)

### BS PDE from Feynman–Kac ✅
The keystone `bsV_satisfies_bs_pde_via_feynmanKac`: the Black–Scholes PDE
`−∂_τV + ½σ²S²∂_SSV + rS∂_SV − rV = 0` derived **independently of Itô** from
the representation `bsV = e^{−rτ} · feynmanU` (the discounted heat flow,
`bsV_eq_discount_feynmanU`), the FK Greeks `hasDerivAt_bsV_{tau,S,SS}_fk`, and
the kernel heat equation — the exact drift cancellation (`U_x` coefficient
`−(r−σ²/2)−½σ²+r = 0`, `U_xx` coefficient `−½σ²+½σ²=0`) assembles the
operator. A *second, independent* derivation of the PDE (the closed-form check
above is the first); the Itô/martingale route remains open.
→ *Finance:* the PDE obtained from the risk-neutral expectation representation
— Feynman–Kac as practitioners actually use it.
[`Models/BlackScholes/PDEFromFeynmanKac.lean`](../MathFin/Models/BlackScholes/PDEFromFeynmanKac.lean)

### Itô formula in L² — Summit A ✅
The continuous-time L² Itô formula
`f(B_T) − f(B_0) = ∫₀ᵀ f′(B_s) dB_s + ½∫₀ᵀ f″(B_s) ds` for `C³` functions with
**bounded** derivatives (`ito_formula_L2_bddDeriv`), proved from primitives:
weighted quadratic variation, the Taylor-remainder limit, and the Riemann↔CLM
bridge — three limit arguments on top of `discrete_ito_formula` and the
continuous Itô integral. The boundedness restriction is the honestly-named
boundary: GBM's exponential sits outside it (see *Geometric Brownian motion*
above for why that lift is deferral, not absence).
→ *Finance:* the engine that turns pathwise second-order algebra into
distributional statements — the analytic heart of every drift argument.
[`Probability/Brownian/Ito/ItoFormulaCLM.lean`](../MathFin/Probability/Brownian/Ito/ItoFormulaCLM.lean)

### Time-dependent Itô formula in L² — Summit A′ ✅
The classical `df = f_x dB + (f_t + ½f_xx) dt` in integrated form:
`f(T, B_T) − f(0, B_0) = ∫₀ᵀ f_x(s, B_s) dB_s + ∫₀ᵀ (f_t + ½f_xx)(s, B_s) ds`
for `C^{1,2}` functions with bounded higher partials
(`ito_formula_td_L2_bddDeriv`). The three Summit-A limit arguments redone with
`(t,x)`-dependence: the weighted quadratic variation generalized to bounded
**adapted weight processes** (the fluctuation engine never cared the weight was
`g(B_s)`), the 2D Itô–Taylor remainder vanishing at `O(1/n)` under the Gaussian
moments, and the time-dependent Riemann↔CLM bridge. The joint continuity of
`f_t` is *derived* from its bounded partials (jointly Lipschitz), not assumed;
the boundedness restriction stays the honestly-named boundary, as in Summit A.
→ *Finance:* the form pricing actually uses — value functions depend on time,
and the `f_t + ½f_xx` drift is the Black–Scholes operator itself.
[`Probability/Brownian/Ito/ItoFormulaTD.lean`](../MathFin/Probability/Brownian/Ito/ItoFormulaTD.lean)

### CRR → Black–Scholes convergence ✅
The binomial (CRR) call price converges to the Black–Scholes call price as the
tree refines (`binomialPrice_call_tendsto_bs`): characteristic functions →
Lévy continuity → convergence in distribution, with **put–call parity lifting
the bounded put's weak convergence to the call** (avoiding a uniform-
integrability/Vitali argument). The discrete and continuous pricing theories
meet where they should.
→ *Finance:* the lattice methods used on every trading desk are not a separate
model — they are the same price, in the limit.
[`Models/Binomial/CRRCharFun.lean`](../MathFin/Models/Binomial/CRRCharFun.lean)

### Margrabe exchange option ✅
Under two correlated lognormal assets with drift `r`, the discounted expected payoff of
the option to exchange one for the other is Margrabe's closed form, a Black–Scholes call
on the ratio with effective volatility `√(σ₁² + σ₂² − 2ρσ₁σ₂)` (`margrabe_exchange_price`,
via `margrabe_bsCallHyp_of_gaussian` and `normalizedSpread_hasLaw_std`) — the
multivariate corollary.
[`Models/BlackScholes/MargrabeGrounding.lean`](../MathFin/Models/BlackScholes/MargrabeGrounding.lean)

### Carr–Madan static replication — spanning formula ✅
Any twice-differentiable payoff `f` decomposes, around a reference level `κ`, as cash, a
forward, and a static book of out-of-the-money options weighted by its convexity `f''`:
`f S = f κ + f' κ·(S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`
(`carrMadan_spanning`, the honest compact strike-range form). One integration by parts — the
second-order Taylor remainder `∫_κ^S (S−t) f''(t) dt = f S − f κ − f' κ (S−κ)` — plus a case
split in which each option leg's positive part either vanishes or reproduces the remainder. The
log payoff specialises to the **variance-swap log-contract** (`carrMadan_log_spanning`):
`−1/K²`-weighted strips of OTM puts and calls.
→ *Finance:* model-free static replication — every European claim is a portfolio of vanilla
options, and the `1/K²` density is exactly what a variance swap holds.
[`Models/ModelFree/CarrMadan.lean`](../MathFin/Models/ModelFree/CarrMadan.lean)

### Binomial martingale representation — market completeness ✅
On the binomial tree (i.i.d. `Bernoulli(q)` coin flips, `0 < q < 1`), every Mathlib `Martingale` `M`
of the flips' natural filtration (`flipFiltration`) is its initial value plus the
`martingaleTransform` of a **predictable** hedge (`StronglyAdapted`) against the discounted asset:
`M_N = M_0 + ∑_{k<N} A_{k+1}·(S_{k+1} − S_k)` (`binomial_martingale_representation`). The hedge is
the node-wise delta `A = ΔM/ΔS`, predictable because it is fixed *before* the next flip is
revealed. The conditional expectation is the node average `q·X^U + (1−q)·X^D = X`
(`oneStep_of_martingale`), and the proof is the pathwise one-period delta hedge, telescoped. The
converse of `martingaleTransform_isMartingale` (`Probability/Discrete/MartingaleTransform.lean`).
→ *Finance:* **completeness** — the second pillar of the FTAP: every contingent claim is
replicable by a self-financing strategy, so the risk-neutral price is the *unique* arbitrage-free
price.
[`Models/Binomial/MartingaleRepresentation.lean`](../MathFin/Models/Binomial/MartingaleRepresentation.lean)

### Merton jump-diffusion dominance ✅
Jump risk is never free: the Black–Scholes price is dominated by the Merton
(1976) jump-diffusion price, `bsV ≤ mertonCallPrice`
(`bsV_le_mertonCallPrice`), through two channels — vega (per-term vol
widening) and gamma/Jensen (the mixture over jump counts, with the tangent's
linear term killed by `integral_mertonSpot`); the classic `Λ′ = Λ(1+k)`
weights display is `MertonClassicDisplay`.
→ *Finance:* ignoring jumps *underprices* options — the model-risk inequality,
as a theorem.
[`Models/Jumps/MertonDominance.lean`](../MathFin/Models/Jumps/MertonDominance.lean)

## The frontier ⏳

The frontier is the ⏳ part of the graph and of the table above: one node per
result the open issues are working towards, each with its statement in
[`blueprint_frontier.toml`](blueprint_frontier.toml). Some are gated on
upstream infrastructure (the pathwise Itô / SDE layer beyond the `[0,T]`
continuous integral, whose localization entry point
`itoSimpleProcess_isLocalMartingale` is delivered); the issue named on each
node says which.

---

*This page is the lightweight blueprint: a GitHub-native dependency graph
linking each statement to its Lean proof. The graph regenerates from the
proof terms — inside the verify container:
`lake build MathFin.Blueprint blueprint_export && lake exe blueprint_export
MathFin.Blueprint > docs/blueprint_nodes.json`, then host-side
`python3 tools/blueprint_render.py`. For the per-theorem faithfulness audit
see [`coverage.md`](coverage.md); for an overview and build instructions
see the [README](../README.md).*
