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
  binomialNoArbitrage["Binomial no-arbitrage condition"]:::proved
  brownianMotion["Brownian motion (Mathlib, upstream)"]:::upstream
  coherentRiskMeasure["Coherent risk measure"]:::proved
  contract["The contract language"]:::proved
  equivalentMeasure["Equivalent probability measure"]:::proved
  gaussianFactorCopula["One-factor Gaussian copula"]:::proved
  numeraireMeasure["Numéraire measure as a Radon–Nikodym change"]:::proved
  portfolioVariance["Portfolio variance"]:::proved
  quantile["Quantile function (generalized inverse CDF)"]:::proved
  snellEnvelope["Snell envelope (the recursion)"]:::proved
  standardNormalCdf["Standard normal CDF Φ"]:::proved
  survivalFunction["Survival function of a lifetime"]:::proved
  zeroCouponBond["Zero-coupon bond, constant short rate"]:::proved
  binomialRepresentation["Binomial martingale representation (completeness)"]:::proved
  bsIdentity["bs_identity: S·φ(d₁) = Ke^{−rτ}·φ(d₂)"]:::proved
  carrMadan["Carr–Madan static replication"]:::proved
  compoundPoissonMgf["Compound-Poisson MGF"]:::proved
  discreteIto["Discrete Itô formula (pathwise)"]:::proved
  empiricalCdfStrongLaw["Strong law for the empirical CDF"]:::proved
  esscherTilt["Esscher tilt is the Gaussian Girsanov"]:::proved
  expectationIto["Expectation-form Itô / Feynman–Kac"]:::proved
  feynmanKacHeatEq["Heat equation for the kernel convolution"]:::proved
  gbmSde["GBM coefficient matching (algebraic)"]:::proved
  glostenMilgromQuote["Glosten–Milgrom: quotes are conditional expectations"]:::proved
  hestonPde["Heston transform profile solves the pricing PDE"]:::proved
  impermanentLoss["Impermanent loss is never positive"]:::proved
  interestRateParity["Covered and uncovered interest-rate parity"]:::proved
  keyRateDuration["Key-rate durations sum to the parallel shift"]:::proved
  markovPathLaw["Markov path law (Ionescu–Tulcea)"]:::proved
  markowitzLagrangian["Markowitz: the Lagrangian condition is sufficient"]:::proved
  marshallOlkin["Marshall–Olkin first-to-default"]:::proved
  martingaleTransform["The martingale transform is a martingale"]:::proved
  noArbitrageLocal["No arbitrage is local"]:::proved
  riskParityFoc["Risk parity from the log-barrier condition"]:::proved
  stochasticFubini["Stochastic Fubini (L² form)"]:::proved
  uniswapV3CoveredCall["A Uniswap v3 position is at most a covered call"]:::proved
  vasicekBondPde["The Vasicek bond price solves its PDE"]:::proved
  contractValue["Value of a contract"]:::proved
  emm["Equivalent martingale measure"]:::proved
  hjmModel["The HJM model"]:::proved
  itoIntegralClm["Continuous Itô integral (CLM on [0,T])"]:::proved
  valueAtRisk["Value-at-risk"]:::proved
  aaveLiquidationKmv["Aave liquidation probability is a KMV default probability"]:::proved
  bondImmunization["First-order immunization"]:::proved
  bsCall["Black–Scholes call formula"]:::proved
  bsDelta["Greeks (δ shown; γ vega θ ρ alongside)"]:::proved
  bsPde["Black–Scholes PDE (from the closed form)"]:::proved
  bscallhypBrownian["BSCallHyp from a Brownian model"]:::proved
  continuousFtap["Discounted risk-neutral GBM is a martingale (EMM property)"]:::proved
  itoIsometryAdapted["Adapted Itô isometry"]:::proved
  mertonRiskNeutralDrift["Jump-diffusion risk-neutral drift"]:::proved
  quadraticVariation["Quadratic variation: ∑(ΔB)² → T in L²"]:::proved
  snellEnvelope["Snell envelope: the smallest dominating supermartingale"]:::proved
  unilateralCva["Unilateral CVA, Gaussian exposure"]:::proved
  varianceSwapJumpBias["Variance-swap jump bias"]:::proved
  wienerIsometry["Wiener isometry (deterministic L²)"]:::proved
  expectedShortfall["Expected shortfall"]:::proved
  bsPdeBrownian["BS PDE in the Brownian coordinate"]:::proved
  bsPdeFeynmanKac["Black–Scholes PDE (from Feynman–Kac)"]:::proved
  conditionalBracket["The bracket is conditional"]:::proved
  crrBsConvergence["CRR → Black–Scholes convergence"]:::proved
  emmDensityPasting["Pasting one-period densities into an EMM"]:::proved
  girsanovBrownianCharacterisation["Girsanov: the shifted process is a filtered Brownian motion"]:::proved
  girsanovCall["Call price under an Esscher-tilted Gaussian (static Girsanov)"]:::proved
  itoFormulaC2["Itô's formula for C² functions"]:::proved
  itoFormulaTdL2["Time-dependent Itô formula, L² (Summit A′)"]:::proved
  itoSquaredL2["Itô for x² in L²: ∑B·ΔB → ½(B_T²−B₀²−T)"]:::proved
  margrabe["Margrabe exchange option"]:::proved
  mertonDominance["Merton call price dominates Black–Scholes at the diffusion vol"]:::proved
  physicalMeasurePricing["Contracts on the physical asset, priced under the Girsanov measure"]:::proved
  schwartzCommodityFutures["Schwartz commodity futures"]:::proved
  sdeStrongSolution["Picard fixed point on every horizon"]:::proved
  bracketCompensator["The bracket compensates the square"]:::proved
  bsDeltaHedge["The Black–Scholes delta hedge"]:::proved
  expectedShortfallCoherent["Expected shortfall is coherent"]:::proved
  itoFormulaL2["Itô formula, L² (C³ bounded — Summit A)"]:::proved
  itoIntegralBrownian["∫₀ᵀ B dB = ½(B_T² − B₀² − T)"]:::proved
  itoProductRule["Itô product rule"]:::proved
  martingaleRepresentation["Martingale representation (terminal form)"]:::proved
  rockafellarUryasev["Rockafellar–Uryasev: ES as a minimum"]:::proved
  bsSelfFinancing["The delta hedge satisfies the self-financing equation"]:::proved
  marketCompleteness["Completeness of the Brownian market"]:::proved
  martingaleRepresentationProcess["Martingale representation (process form)"]:::proved
  pricingMeasure["The pricing measure on 𝓕ᴮ_T is unique"]:::proved
  subgraph frontier_actuarial["⏳ frontier · actuarial"]
    buhlmannCredibility["Bühlmann credibility"]:::frontier
    cramerLundbergClaims["Cramér–Lundberg claims"]:::frontier
    lifeInsuranceEpv["Life annuity and insurance EPV"]:::frontier
    lundbergRuinBound["Lundberg ruin bound"]:::frontier
    panjerRecursion["Panjer recursion"]:::frontier
    survivalModel["Survival model and life tables"]:::frontier
    thieleReserve["Thiele reserve"]:::frontier
  end
  subgraph frontier_binomial["⏳ frontier · binomial"]
    americanPutPremium["American put early-exercise premium"]:::frontier
    binomialBarrierReflection["Binomial barrier prices via reflection"]:::frontier
  end
  subgraph frontier_blackScholes["⏳ frontier · black-scholes"]
    barrierLookbackClosedForms["Barrier and lookback closed forms"]:::frontier
    carrLeeMoment["Carr–Lee moment formula"]:::frontier
    forwardStartCall["Forward-start call"]:::frontier
    impliedVolExistence["Implied volatility for every arbitrage-free price"]:::frontier
    kouJumpDiffusion["Kou double-exponential jump-diffusion"]:::frontier
    margrabeNumeraire["Margrabe and chooser via the S²-numéraire"]:::frontier
    mertonPide["Merton PIDE"]:::frontier
    perpetualAmerican["Perpetual American option"]:::frontier
    twoAssetOptionFormulas["Stulz and Heynen–Kat two-asset formulas"]:::frontier
    varianceGammaCall["Variance-gamma European call"]:::frontier
  end
  subgraph frontier_credit["⏳ frontier · credit"]
    blackCoxDefault["Black–Cox first-passage default"]:::frontier
    largePoolLoss["Large homogeneous pool loss law"]:::frontier
    mertonCreditSpread["Merton structural credit spread"]:::frontier
    oneFactorCopulaDefault["One-factor Gaussian copula default"]:::frontier
    stefanUniqueness["Stefan uniqueness with accumulating jumps"]:::frontier
  end
  subgraph frontier_defi["⏳ frontier · defi"]
    aaveHealthFactorBound["Aave multi-asset health factor: a liquidation bound"]:::frontier
    balancerInvariant["Balancer constant-mean AMM"]:::frontier
    compoundExchangeRateBridge["Compound's exchange rate as a money-market account"]:::frontier
    liquidationFirstPassage["Liquidation before maturity as first passage"]:::frontier
  end
  subgraph frontier_execution["⏳ frontier · execution"]
    kyleEquilibrium["Kyle single-period equilibrium"]:::frontier
  end
  subgraph frontier_fixedIncome["⏳ frontier · fixed-income"]
    affineTermStructure["Affine term structure"]:::frontier
    bermudanCallableSnell["Callable bonds and Bermudan swaptions by Snell envelope"]:::frontier
    cirBondLoadings["CIR bond-price loadings"]:::frontier
    cmsConvexityAdjustment["CMS convexity adjustment"]:::frontier
    futuresForwardConvexity["Futures–forward convexity adjustment"]:::frontier
    hjmAffineModels["HJM recovers Ho–Lee and Vasicek"]:::frontier
    hjmBondDynamics["HJM bond-price dynamics"]:::frontier
    hjmDriftCondition["HJM drift condition"]:::frontier
    hjmLogBondDynamics["HJM log-bond dynamics"]:::frontier
    hjmMusiela["HJM Musiela parametrization"]:::frontier
    hjmShortRate["HJM induces a short-rate model"]:::frontier
    lmmForwardMartingale["LIBOR market model forward martingale"]:::frontier
  end
  subgraph frontier_foundations["⏳ frontier · foundations"]
    realErf["erf / erfc / erfinv for Mathlib"]:::frontier
    bracketQuadraticVariation["Bracket is the quadratic variation of an Itô integral"]:::frontier
    brownianNowhereDifferentiable["Brownian paths are nowhere differentiable"]:::frontier
    clarkOcone["L¹ martingale representation and Clark–Ocone"]:::frontier
    compensatedPoissonIntegral["Compensated-Poisson integral"]:::frontier
    dmwFtap["Dalang–Morton–Willinger FTAP"]:::frontier
    esscherEmmLevy["Esscher EMM for exponential-Lévy markets"]:::frontier
    feynmanKacVariableCoefficient["Variable-coefficient Feynman–Kac"]:::frontier
    girsanovContinuousEmm["Girsanov EMM from the Itô tower"]:::frontier
    itoFormula2d["Two-process Itô formula"]:::frontier
    itoIntegralMartingale["General-integrand Itô process is a martingale"]:::frontier
    itoLevyFormula["Itô–Lévy change of variables"]:::frontier
    jumpDiffusionLaw["Compound-Poisson and jump-diffusion law"]:::frontier
    lawIteratedLogarithm["Law of the iterated logarithm"]:::frontier
    martingaleRepresentationVector["Vector martingale representation"]:::frontier
    novikovGirsanov["Novikov Girsanov for unbounded θ"]:::frontier
    perronFrobeniusMarkov["Perron–Frobenius and finite Markov chain ergodicity"]:::frontier
    poissonInterarrivalIid["Poisson interarrivals are iid exponential"]:::frontier
    propagatorNoArbitrage["Transient-impact propagator no-arbitrage"]:::frontier
    reflectionPrinciple["Reflection principle for Brownian motion"]:::frontier
    sdeContinuousSolution["Continuous strong solutions on every horizon"]:::frontier
    secondFtapConverse["Second FTAP: uniqueness implies completeness"]:::frontier
    semistaticFtap["Semistatic FTAP with entropy"]:::frontier
    stochasticFubiniLevy["Stochastic Fubini for Itô–Lévy integrals"]:::frontier
    stochasticFubiniProcess["Stochastic Fubini for the integral process"]:::frontier
  end
  subgraph frontier_futures["⏳ frontier · futures"]
    futuresBasisConvergence["Contango, backwardation and basis convergence"]:::frontier
  end
  subgraph frontier_fx["⏳ frontier · fx"]
    siegelParadox["Siegel's paradox"]:::frontier
  end
  subgraph frontier_portfolio["⏳ frontier · portfolio"]
    aptPricing["APT exact-factor pricing"]:::frontier
    logOptimalNumeraire["Log-optimal portfolio is the numéraire"]:::frontier
    markowitzKktNecessity["Markowitz first-order conditions are necessary"]:::frontier
    mertonPortfolioFraction["Merton myopic risky fraction"]:::frontier
    purgedCvIndependence["Purged cross-validation: σ-algebra independence"]:::frontier
    riskParityNAsset["N-asset risk parity exists and is unique"]:::frontier
    timeInconsistentEquilibrium["Relaxed equilibria under time inconsistency"]:::frontier
    varianceOptimalHedging["Variance-optimal hedging"]:::frontier
  end
  subgraph frontier_risk["⏳ frontier · risk"]
    cvarRockafellarUryasev["CVaR via Rockafellar–Uryasev"]:::frontier
    expectedUtilityRiskAversion["Expected utility and risk aversion"]:::frontier
    glivenkoCantelli["Glivenko–Cantelli theorem"]:::frontier
    kusuoka["Kusuoka representation"]:::frontier
    quantileConvergenceInDistribution["Quantiles under convergence in distribution"]:::frontier
    riskMeasureFamilies["Entropic, distortion and expectile risk measures"]:::frontier
    sklarGeneral["Sklar's theorem for arbitrary margins"]:::frontier
  end
  subgraph frontier_stochVol["⏳ frontier · stoch-vol"]
    batesCf["Bates characteristic function"]:::frontier
    cevCall["CEV European call"]:::frontier
    dupireLocalVol["Dupire local volatility"]:::frontier
    hestonCf["Heston characteristic function"]:::frontier
    modelFreeVariance["Model-free implied variance replication"]:::frontier
    roughHestonPathwiseUniqueness["Rough-Heston pathwise uniqueness"]:::frontier
    sabrHagan["SABR Hagan asymptotic implied vol"]:::frontier
    schrodingerSpxVix["Schrödinger calibration of SPX/VIX"]:::frontier
    smileNoArbitrage["Smile no-arbitrage (Roper, SVI)"]:::frontier
  end

  contract --> contractValue
  equivalentMeasure --> emm
  brownianMotion --> hjmModel
  brownianMotion --> itoIntegralClm
  quantile --> valueAtRisk
  standardNormalCdf --> aaveLiquidationKmv
  zeroCouponBond --> bondImmunization
  standardNormalCdf --> bsCall
  standardNormalCdf --> bsDelta
  bsIdentity --> bsDelta
  standardNormalCdf --> bsPde
  brownianMotion --> bscallhypBrownian
  brownianMotion --> continuousFtap
  brownianMotion --> itoIsometryAdapted
  compoundPoissonMgf --> mertonRiskNeutralDrift
  brownianMotion --> quadraticVariation
  snellEnvelope --> snellEnvelope
  standardNormalCdf --> unilateralCva
  compoundPoissonMgf --> varianceSwapJumpBias
  brownianMotion --> wienerIsometry
  valueAtRisk --> expectedShortfall
  standardNormalCdf --> bsPdeBrownian
  bsCall --> bsPdeBrownian
  feynmanKacHeatEq --> bsPdeBrownian
  standardNormalCdf --> bsPdeFeynmanKac
  bsCall --> bsPdeFeynmanKac
  bsDelta --> bsPdeFeynmanKac
  bsIdentity --> bsPdeFeynmanKac
  feynmanKacHeatEq --> bsPdeFeynmanKac
  brownianMotion --> conditionalBracket
  itoIntegralClm --> conditionalBracket
  binomialNoArbitrage --> crrBsConvergence
  contract --> crrBsConvergence
  contractValue --> crrBsConvergence
  standardNormalCdf --> crrBsConvergence
  emm --> emmDensityPasting
  equivalentMeasure --> emmDensityPasting
  brownianMotion --> girsanovBrownianCharacterisation
  itoIntegralClm --> girsanovBrownianCharacterisation
  standardNormalCdf --> girsanovCall
  bsCall --> girsanovCall
  esscherTilt --> girsanovCall
  brownianMotion --> itoFormulaC2
  itoIntegralClm --> itoFormulaC2
  brownianMotion --> itoFormulaTdL2
  itoIntegralClm --> itoFormulaTdL2
  brownianMotion --> itoSquaredL2
  discreteIto --> itoSquaredL2
  quadraticVariation --> itoSquaredL2
  standardNormalCdf --> margrabe
  bsCall --> margrabe
  esscherTilt --> margrabe
  standardNormalCdf --> mertonDominance
  bsCall --> mertonDominance
  bsDelta --> mertonDominance
  bsIdentity --> mertonDominance
  brownianMotion --> physicalMeasurePricing
  contract --> physicalMeasurePricing
  contractValue --> physicalMeasurePricing
  itoIntegralClm --> physicalMeasurePricing
  brownianMotion --> schwartzCommodityFutures
  wienerIsometry --> schwartzCommodityFutures
  brownianMotion --> sdeStrongSolution
  itoIntegralClm --> sdeStrongSolution
  brownianMotion --> bracketCompensator
  conditionalBracket --> bracketCompensator
  brownianMotion --> bsDeltaHedge
  itoIntegralClm --> bsDeltaHedge
  standardNormalCdf --> bsDeltaHedge
  bsDelta --> bsDeltaHedge
  bsPdeBrownian --> bsDeltaHedge
  itoFormulaC2 --> bsDeltaHedge
  coherentRiskMeasure --> expectedShortfallCoherent
  expectedShortfall --> expectedShortfallCoherent
  quantile --> expectedShortfallCoherent
  valueAtRisk --> expectedShortfallCoherent
  brownianMotion --> itoFormulaL2
  itoIntegralClm --> itoFormulaL2
  itoFormulaTdL2 --> itoFormulaL2
  brownianMotion --> itoIntegralBrownian
  itoIntegralClm --> itoIntegralBrownian
  itoIsometryAdapted --> itoIntegralBrownian
  itoSquaredL2 --> itoIntegralBrownian
  brownianMotion --> itoProductRule
  itoIntegralClm --> itoProductRule
  itoFormulaC2 --> itoProductRule
  brownianMotion --> martingaleRepresentation
  itoIntegralClm --> martingaleRepresentation
  itoFormulaTdL2 --> martingaleRepresentation
  expectedShortfall --> rockafellarUryasev
  quantile --> rockafellarUryasev
  valueAtRisk --> rockafellarUryasev
  brownianMotion --> bsSelfFinancing
  contract --> bsSelfFinancing
  contractValue --> bsSelfFinancing
  itoIntegralClm --> bsSelfFinancing
  standardNormalCdf --> bsSelfFinancing
  bsCall --> bsSelfFinancing
  bsDeltaHedge --> bsSelfFinancing
  bscallhypBrownian --> bsSelfFinancing
  itoFormulaC2 --> bsSelfFinancing
  brownianMotion --> marketCompleteness
  itoIntegralClm --> marketCompleteness
  martingaleRepresentation --> marketCompleteness
  brownianMotion --> martingaleRepresentationProcess
  itoIntegralClm --> martingaleRepresentationProcess
  martingaleRepresentation --> martingaleRepresentationProcess
  brownianMotion --> pricingMeasure
  itoIntegralClm --> pricingMeasure
  marketCompleteness --> pricingMeasure
  standardNormalCdf --> realErf
  aaveLiquidationKmv --> aaveHealthFactorBound
  vasicekBondPde --> affineTermStructure
  snellEnvelope --> americanPutPremium
  emm --> aptPricing
  impermanentLoss --> balancerInvariant
  reflectionPrinciple --> barrierLookbackClosedForms
  bsCall --> barrierLookbackClosedForms
  hestonCf --> batesCf
  jumpDiffusionLaw --> batesCf
  snellEnvelope --> bermudanCallableSnell
  binomialNoArbitrage --> binomialBarrierReflection
  reflectionPrinciple --> blackCoxDefault
  standardNormalCdf --> blackCoxDefault
  bracketCompensator --> bracketQuadraticVariation
  quadraticVariation --> bracketQuadraticVariation
  itoIntegralMartingale --> bracketQuadraticVariation
  brownianMotion --> brownianNowhereDifferentiable
  bsCall --> carrLeeMoment
  bsCall --> cevCall
  affineTermStructure --> cirBondLoadings
  martingaleRepresentationProcess --> clarkOcone
  numeraireMeasure --> cmsConvexityAdjustment
  zeroCouponBond --> compoundExchangeRateBridge
  compoundPoissonMgf --> cramerLundbergClaims
  rockafellarUryasev --> cvarRockafellarUryasev
  compoundPoissonMgf --> cvarRockafellarUryasev
  noArbitrageLocal --> dmwFtap
  emmDensityPasting --> dmwFtap
  bsPde --> dupireLocalVol
  feynmanKacVariableCoefficient --> dupireLocalVol
  esscherTilt --> esscherEmmLevy
  jumpDiffusionLaw --> esscherEmmLevy
  feynmanKacHeatEq --> feynmanKacVariableCoefficient
  sdeContinuousSolution --> feynmanKacVariableCoefficient
  itoFormulaTdL2 --> feynmanKacVariableCoefficient
  bsCall --> forwardStartCall
  interestRateParity --> futuresBasisConvergence
  affineTermStructure --> futuresForwardConvexity
  continuousFtap --> girsanovContinuousEmm
  itoFormulaTdL2 --> girsanovContinuousEmm
  esscherTilt --> girsanovContinuousEmm
  empiricalCdfStrongLaw --> glivenkoCantelli
  hestonPde --> hestonCf
  hjmDriftCondition --> hjmAffineModels
  affineTermStructure --> hjmAffineModels
  hjmLogBondDynamics --> hjmBondDynamics
  itoFormulaL2 --> hjmBondDynamics
  hjmModel --> hjmBondDynamics
  hjmBondDynamics --> hjmDriftCondition
  hjmModel --> hjmDriftCondition
  stochasticFubiniProcess --> hjmLogBondDynamics
  hjmModel --> hjmLogBondDynamics
  hjmDriftCondition --> hjmMusiela
  hjmDriftCondition --> hjmShortRate
  bsCall --> impliedVolExistence
  bsDelta --> impliedVolExistence
  itoFormulaL2 --> itoFormula2d
  itoFormulaTdL2 --> itoFormula2d
  itoProductRule --> itoFormula2d
  itoIntegralClm --> itoIntegralMartingale
  marketCompleteness --> itoIntegralMartingale
  itoFormulaL2 --> itoLevyFormula
  itoIntegralClm --> itoLevyFormula
  compoundPoissonMgf --> jumpDiffusionLaw
  jumpDiffusionLaw --> kouJumpDiffusion
  bsCall --> kouJumpDiffusion
  expectedShortfallCoherent --> kusuoka
  coherentRiskMeasure --> kusuoka
  oneFactorCopulaDefault --> largePoolLoss
  gaussianFactorCopula --> largePoolLoss
  standardNormalCdf --> largePoolLoss
  brownianMotion --> lawIteratedLogarithm
  survivalModel --> lifeInsuranceEpv
  survivalFunction --> lifeInsuranceEpv
  blackCoxDefault --> liquidationFirstPassage
  aaveLiquidationKmv --> liquidationFirstPassage
  numeraireMeasure --> lmmForwardMartingale
  numeraireMeasure --> logOptimalNumeraire
  continuousFtap --> logOptimalNumeraire
  cramerLundbergClaims --> lundbergRuinBound
  compoundPoissonMgf --> lundbergRuinBound
  margrabe --> margrabeNumeraire
  numeraireMeasure --> margrabeNumeraire
  markowitzLagrangian --> markowitzKktNecessity
  martingaleRepresentationProcess --> martingaleRepresentationVector
  bsCall --> mertonCreditSpread
  itoLevyFormula --> mertonPide
  mertonDominance --> mertonPide
  gbmSde --> mertonPortfolioFraction
  portfolioVariance --> mertonPortfolioFraction
  carrMadan --> modelFreeVariance
  girsanovContinuousEmm --> novikovGirsanov
  gaussianFactorCopula --> oneFactorCopulaDefault
  standardNormalCdf --> oneFactorCopulaDefault
  compoundPoissonMgf --> panjerRecursion
  snellEnvelope --> perpetualAmerican
  bsPde --> perpetualAmerican
  markovPathLaw --> perronFrobeniusMarkov
  brownianMotion --> purgedCvIndependence
  quantile --> quantileConvergenceInDistribution
  brownianMotion --> reflectionPrinciple
  coherentRiskMeasure --> riskMeasureFamilies
  riskParityFoc --> riskParityNAsset
  sdeStrongSolution --> roughHestonPathwiseUniqueness
  bsCall --> sabrHagan
  modelFreeVariance --> schrodingerSpxVix
  sdeStrongSolution --> sdeContinuousSolution
  marketCompleteness --> secondFtapConverse
  pricingMeasure --> secondFtapConverse
  dmwFtap --> semistaticFtap
  carrMadan --> semistaticFtap
  gbmSde --> siegelParadox
  quantile --> sklarGeneral
  carrMadan --> smileNoArbitrage
  bsCall --> smileNoArbitrage
  brownianMotion --> stefanUniqueness
  stochasticFubini --> stochasticFubiniLevy
  stochasticFubini --> stochasticFubiniProcess
  survivalFunction --> survivalModel
  survivalModel --> thieleReserve
  survivalFunction --> thieleReserve
  sdeStrongSolution --> timeInconsistentEquilibrium
  margrabe --> twoAssetOptionFormulas
  bsCall --> twoAssetOptionFormulas
  bsCall --> varianceGammaCall
  martingaleTransform --> varianceOptimalHedging
  emm --> varianceOptimalHedging

  classDef proved fill:#d4edda,stroke:#28a745,color:#111;
  classDef upstream fill:#d9e8f6,stroke:#1f6fb2,color:#111;
  classDef partial fill:#ffe5d0,stroke:#d9534f,color:#111;
  classDef frontier fill:#fff3cd,stroke:#d39e00,color:#111;
```

| node | status | issues and pull requests |
|---|---|---|
| `def:binomial-no-arbitrage` Binomial no-arbitrage condition | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Abinomial-no-arbitrage%22%20in%3Abody) |
| `def:brownian-motion` Brownian motion (Mathlib, upstream) | ✅ upstream | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Abrownian-motion%22%20in%3Abody) |
| `def:coherent-risk-measure` Coherent risk measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acoherent-risk-measure%22%20in%3Abody) |
| `def:contract` The contract language | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acontract%22%20in%3Abody) |
| `def:equivalent-measure` Equivalent probability measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aequivalent-measure%22%20in%3Abody) |
| `def:gaussian-factor-copula` One-factor Gaussian copula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Agaussian-factor-copula%22%20in%3Abody) |
| `def:numeraire-measure` Numéraire measure as a Radon–Nikodym change | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Anumeraire-measure%22%20in%3Abody) |
| `def:portfolio-variance` Portfolio variance | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aportfolio-variance%22%20in%3Abody) |
| `def:quantile` Quantile function (generalized inverse CDF) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aquantile%22%20in%3Abody) |
| `def:snell-envelope` Snell envelope (the recursion) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asnell-envelope%22%20in%3Abody) |
| `def:standard-normal-cdf` Standard normal CDF Φ | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Astandard-normal-cdf%22%20in%3Abody) |
| `def:survival-function` Survival function of a lifetime | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Asurvival-function%22%20in%3Abody) |
| `def:zero-coupon-bond` Zero-coupon bond, constant short rate | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Azero-coupon-bond%22%20in%3Abody) |
| `thm:binomial-representation` Binomial martingale representation (completeness) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abinomial-representation%22%20in%3Abody) |
| `thm:bs-identity` bs_identity: S·φ(d₁) = Ke^{−rτ}·φ(d₂) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-identity%22%20in%3Abody) |
| `thm:carr-madan` Carr–Madan static replication | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acarr-madan%22%20in%3Abody) |
| `thm:compound-poisson-mgf` Compound-Poisson MGF | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompound-poisson-mgf%22%20in%3Abody) |
| `thm:discrete-ito` Discrete Itô formula (pathwise) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Adiscrete-ito%22%20in%3Abody) |
| `thm:empirical-cdf-strong-law` Strong law for the empirical CDF | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aempirical-cdf-strong-law%22%20in%3Abody) |
| `thm:esscher-tilt` Esscher tilt is the Gaussian Girsanov | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aesscher-tilt%22%20in%3Abody) |
| `thm:expectation-ito` Expectation-form Itô / Feynman–Kac | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpectation-ito%22%20in%3Abody) |
| `thm:feynman-kac-heat-eq` Heat equation for the kernel convolution | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Afeynman-kac-heat-eq%22%20in%3Abody) |
| `thm:gbm-sde` GBM coefficient matching (algebraic) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agbm-sde%22%20in%3Abody) |
| `thm:glosten-milgrom-quote` Glosten–Milgrom: quotes are conditional expectations | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aglosten-milgrom-quote%22%20in%3Abody) |
| `thm:heston-pde` Heston transform profile solves the pricing PDE | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aheston-pde%22%20in%3Abody) |
| `thm:impermanent-loss` Impermanent loss is never positive | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aimpermanent-loss%22%20in%3Abody) |
| `thm:interest-rate-parity` Covered and uncovered interest-rate parity | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ainterest-rate-parity%22%20in%3Abody) |
| `thm:key-rate-duration` Key-rate durations sum to the parallel shift | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akey-rate-duration%22%20in%3Abody) |
| `thm:markov-path-law` Markov path law (Ionescu–Tulcea) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkov-path-law%22%20in%3Abody) |
| `thm:markowitz-lagrangian` Markowitz: the Lagrangian condition is sufficient | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarkowitz-lagrangian%22%20in%3Abody) |
| `thm:marshall-olkin` Marshall–Olkin first-to-default | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarshall-olkin%22%20in%3Abody) |
| `thm:martingale-transform` The martingale transform is a martingale | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-transform%22%20in%3Abody) |
| `thm:no-arbitrage-local` No arbitrage is local | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Ano-arbitrage-local%22%20in%3Abody) |
| `thm:risk-parity-foc` Risk parity from the log-barrier condition | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arisk-parity-foc%22%20in%3Abody) |
| `thm:stochastic-fubini` Stochastic Fubini (L² form) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini%22%20in%3Abody) |
| `thm:uniswap-v3-covered-call` A Uniswap v3 position is at most a covered call | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Auniswap-v3-covered-call%22%20in%3Abody) |
| `thm:vasicek-bond-pde` The Vasicek bond price solves its PDE | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avasicek-bond-pde%22%20in%3Abody) |
| `def:contract-value` Value of a contract | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Acontract-value%22%20in%3Abody) |
| `def:emm` Equivalent martingale measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aemm%22%20in%3Abody) |
| `def:hjm-model` The HJM model | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Ahjm-model%22%20in%3Abody) |
| `def:ito-integral-clm` Continuous Itô integral (CLM on [0,T]) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aito-integral-clm%22%20in%3Abody) |
| `def:value-at-risk` Value-at-risk | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Avalue-at-risk%22%20in%3Abody) |
| `thm:aave-liquidation-kmv` Aave liquidation probability is a KMV default probability | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aaave-liquidation-kmv%22%20in%3Abody) |
| `thm:bond-immunization` First-order immunization | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abond-immunization%22%20in%3Abody) |
| `thm:bs-call` Black–Scholes call formula | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-call%22%20in%3Abody) |
| `thm:bs-delta` Greeks (δ shown; γ vega θ ρ alongside) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-delta%22%20in%3Abody) |
| `thm:bs-pde` Black–Scholes PDE (from the closed form) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-pde%22%20in%3Abody) |
| `thm:bscallhyp-brownian` BSCallHyp from a Brownian model | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abscallhyp-brownian%22%20in%3Abody) |
| `thm:continuous-ftap` Discounted risk-neutral GBM is a martingale (EMM property) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acontinuous-ftap%22%20in%3Abody) |
| `thm:ito-isometry-adapted` Adapted Itô isometry | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-isometry-adapted%22%20in%3Abody) |
| `thm:merton-risk-neutral-drift` Jump-diffusion risk-neutral drift | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-risk-neutral-drift%22%20in%3Abody) |
| `thm:quadratic-variation` Quadratic variation: ∑(ΔB)² → T in L² | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aquadratic-variation%22%20in%3Abody) |
| `thm:snell-envelope` Snell envelope: the smallest dominating supermartingale | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asnell-envelope%22%20in%3Abody) |
| `thm:unilateral-cva` Unilateral CVA, Gaussian exposure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aunilateral-cva%22%20in%3Abody) |
| `thm:variance-swap-jump-bias` Variance-swap jump bias | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-swap-jump-bias%22%20in%3Abody) |
| `thm:wiener-isometry` Wiener isometry (deterministic L²) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Awiener-isometry%22%20in%3Abody) |
| `def:expected-shortfall` Expected shortfall | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22def%3Aexpected-shortfall%22%20in%3Abody) |
| `thm:bs-pde-brownian` BS PDE in the Brownian coordinate | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-pde-brownian%22%20in%3Abody) |
| `thm:bs-pde-feynman-kac` Black–Scholes PDE (from Feynman–Kac) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-pde-feynman-kac%22%20in%3Abody) |
| `thm:conditional-bracket` The bracket is conditional | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aconditional-bracket%22%20in%3Abody) |
| `thm:crr-bs-convergence` CRR → Black–Scholes convergence | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acrr-bs-convergence%22%20in%3Abody) |
| `thm:emm-density-pasting` Pasting one-period densities into an EMM | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aemm-density-pasting%22%20in%3Abody) |
| `thm:girsanov-brownian-characterisation` Girsanov: the shifted process is a filtered Brownian motion | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agirsanov-brownian-characterisation%22%20in%3Abody) |
| `thm:girsanov-call` Call price under an Esscher-tilted Gaussian (static Girsanov) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Agirsanov-call%22%20in%3Abody) |
| `thm:ito-formula-c2` Itô's formula for C² functions | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-c2%22%20in%3Abody) |
| `thm:ito-formula-td-l2` Time-dependent Itô formula, L² (Summit A′) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-td-l2%22%20in%3Abody) |
| `thm:ito-squared-l2` Itô for x² in L²: ∑B·ΔB → ½(B_T²−B₀²−T) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-squared-l2%22%20in%3Abody) |
| `thm:margrabe` Margrabe exchange option | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amargrabe%22%20in%3Abody) |
| `thm:merton-dominance` Merton call price dominates Black–Scholes at the diffusion vol | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amerton-dominance%22%20in%3Abody) |
| `thm:physical-measure-pricing` Contracts on the physical asset, priced under the Girsanov measure | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aphysical-measure-pricing%22%20in%3Abody) |
| `thm:schwartz-commodity-futures` Schwartz commodity futures | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aschwartz-commodity-futures%22%20in%3Abody) |
| `thm:sde-strong-solution` Picard fixed point on every horizon | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asde-strong-solution%22%20in%3Abody) |
| `thm:bracket-compensator` The bracket compensates the square | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abracket-compensator%22%20in%3Abody) |
| `thm:bs-delta-hedge` The Black–Scholes delta hedge | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-delta-hedge%22%20in%3Abody) |
| `thm:expected-shortfall-coherent` Expected shortfall is coherent | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aexpected-shortfall-coherent%22%20in%3Abody) |
| `thm:ito-formula-l2` Itô formula, L² (C³ bounded — Summit A) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-formula-l2%22%20in%3Abody) |
| `thm:ito-integral-brownian` ∫₀ᵀ B dB = ½(B_T² − B₀² − T) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-integral-brownian%22%20in%3Abody) |
| `thm:ito-product-rule` Itô product rule | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aito-product-rule%22%20in%3Abody) |
| `thm:martingale-representation` Martingale representation (terminal form) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-representation%22%20in%3Abody) |
| `thm:rockafellar-uryasev` Rockafellar–Uryasev: ES as a minimum | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Arockafellar-uryasev%22%20in%3Abody) |
| `thm:bs-self-financing` The delta hedge satisfies the self-financing equation | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abs-self-financing%22%20in%3Abody) |
| `thm:market-completeness` Completeness of the Brownian market | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amarket-completeness%22%20in%3Abody) |
| `thm:martingale-representation-process` Martingale representation (process form) | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Amartingale-representation-process%22%20in%3Abody) |
| `thm:pricing-measure` The pricing measure on 𝓕ᴮ_T is unique | ✅ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Apricing-measure%22%20in%3Abody) |
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
| `thm:buhlmann-credibility` Bühlmann credibility | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Abuhlmann-credibility%22%20in%3Abody) |
| `thm:carr-lee-moment` Carr–Lee moment formula | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acarr-lee-moment%22%20in%3Abody) |
| `thm:cev-call` CEV European call | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acev-call%22%20in%3Abody) |
| `thm:cir-bond-loadings` CIR bond-price loadings | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acir-bond-loadings%22%20in%3Abody) |
| `thm:clark-ocone` L¹ martingale representation and Clark–Ocone | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aclark-ocone%22%20in%3Abody) |
| `thm:cms-convexity-adjustment` CMS convexity adjustment | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acms-convexity-adjustment%22%20in%3Abody) |
| `thm:compensated-poisson-integral` Compensated-Poisson integral | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompensated-poisson-integral%22%20in%3Abody) |
| `thm:compound-exchange-rate-bridge` Compound's exchange rate as a money-market account | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acompound-exchange-rate-bridge%22%20in%3Abody) |
| `thm:cramer-lundberg-claims` Cramér–Lundberg claims | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acramer-lundberg-claims%22%20in%3Abody) |
| `thm:cvar-rockafellar-uryasev` CVaR via Rockafellar–Uryasev | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Acvar-rockafellar-uryasev%22%20in%3Abody) |
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
| `thm:kou-jump-diffusion` Kou double-exponential jump-diffusion | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akou-jump-diffusion%22%20in%3Abody) |
| `thm:kusuoka` Kusuoka representation | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akusuoka%22%20in%3Abody) |
| `thm:kyle-equilibrium` Kyle single-period equilibrium | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Akyle-equilibrium%22%20in%3Abody) |
| `thm:large-pool-loss` Large homogeneous pool loss law | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alarge-pool-loss%22%20in%3Abody) |
| `thm:law-iterated-logarithm` Law of the iterated logarithm | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alaw-iterated-logarithm%22%20in%3Abody) |
| `thm:life-insurance-epv` Life annuity and insurance EPV | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alife-insurance-epv%22%20in%3Abody) |
| `thm:liquidation-first-passage` Liquidation before maturity as first passage | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Aliquidation-first-passage%22%20in%3Abody) |
| `thm:lmm-forward-martingale` LIBOR market model forward martingale | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Almm-forward-martingale%22%20in%3Abody) |
| `thm:log-optimal-numeraire` Log-optimal portfolio is the numéraire | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Alog-optimal-numeraire%22%20in%3Abody) |
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
| `thm:second-ftap-converse` Second FTAP: uniqueness implies completeness | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asecond-ftap-converse%22%20in%3Abody) |
| `thm:semistatic-ftap` Semistatic FTAP with entropy | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asemistatic-ftap%22%20in%3Abody) |
| `thm:siegel-paradox` Siegel's paradox | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asiegel-paradox%22%20in%3Abody) |
| `thm:sklar-general` Sklar's theorem for arbitrary margins | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asklar-general%22%20in%3Abody) |
| `thm:smile-no-arbitrage` Smile no-arbitrage (Roper, SVI) | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asmile-no-arbitrage%22%20in%3Abody) |
| `thm:stefan-uniqueness` Stefan uniqueness with accumulating jumps | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astefan-uniqueness%22%20in%3Abody) |
| `thm:stochastic-fubini-levy` Stochastic Fubini for Itô–Lévy integrals | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini-levy%22%20in%3Abody) |
| `thm:stochastic-fubini-process` Stochastic Fubini for the integral process | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Astochastic-fubini-process%22%20in%3Abody) |
| `thm:survival-model` Survival model and life tables | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Asurvival-model%22%20in%3Abody) |
| `thm:thiele-reserve` Thiele reserve | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Athiele-reserve%22%20in%3Abody) |
| `thm:time-inconsistent-equilibrium` Relaxed equilibria under time inconsistency | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atime-inconsistent-equilibrium%22%20in%3Abody) |
| `thm:two-asset-option-formulas` Stulz and Heynen–Kat two-asset formulas | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Atwo-asset-option-formulas%22%20in%3Abody) |
| `thm:variance-gamma-call` Variance-gamma European call | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-gamma-call%22%20in%3Abody) |
| `thm:variance-optimal-hedging` Variance-optimal hedging | ⏳ | [linked](https://github.com/formal-applied-math/formal-mathfin/issues?q=%22thm%3Avariance-optimal-hedging%22%20in%3Abody) |
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
[`Foundations/QuadraticVariationL2.lean`](../MathFin/Foundations/QuadraticVariationL2.lean)

### Wiener isometry (L²) ✅
For **deterministic** step integrands, `E[(∫ φ dB)²] = ∫ φ² dt`
(`wiener_assembly_isometry`, `wienerIntegralLp_integral_sq`); step functions are
dense (`stepAssembly_denseRange`), giving the L² Wiener integral.
→ *Finance:* the L² geometry of payoffs built from a fixed (non-reacting)
position in Brownian noise.
[`Foundations/WienerIntegralL2.lean`](../MathFin/Foundations/WienerIntegralL2.lean)

### Adapted Itô isometry ✅
The genuinely stochastic version: for **random adapted** simple integrands,
`E[(∑ φₖ ΔBₖ)²] = ∑ E[φₖ²] Δtₖ` (`ito_isometry_discrete`). The cross terms vanish
by the **weak Markov property** (`integral_cross_increment_bilinear_eq_zero`) —
the distinction that separates Itô from Wiener — with the `∫ B dB` capstone
(`ito_isometry_brownian_self`).
→ *Finance:* a self-financing strategy whose position reacts to the path still
has variance equal to the sum of its per-period variances.
[`Foundations/ItoIsometryAdapted.lean`](../MathFin/Foundations/ItoIsometryAdapted.lean)

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
[`Foundations/ItoIntegralCLM.lean`](../MathFin/Foundations/ItoIntegralCLM.lean)

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
[`Foundations/ItoSquaringIdentity.lean`](../MathFin/Foundations/ItoSquaringIdentity.lean),
[`Foundations/DiscreteItoPolynomial.lean`](../MathFin/Foundations/DiscreteItoPolynomial.lean),
[`Foundations/ItoFormulaSquaredL2.lean`](../MathFin/Foundations/ItoFormulaSquaredL2.lean),
[`Foundations/ItoLemma2D.lean`](../MathFin/Foundations/ItoLemma2D.lean)

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
[`Foundations/ItoLemma2D.lean`](../MathFin/Foundations/ItoLemma2D.lean)

### Expectation-form Itô / Feynman–Kac ✅
`E[f(Bₜ)] = f(0) + ½ ∫₀ᵗ E[f''(Bₛ)] ds` (`expectation_ito`,
`expectation_ito_isPreBrownian`), proved via the heat equation
(`heatConvolution_eq_add_integral_deriv`, `feynmanKac_boundary`).
→ *Finance:* how the expected value of a function of the asset evolves — the
`½σ²` second-order term that drives the Black–Scholes PDE.
[`Foundations/FeynmanKacHeatEquation.lean`](../MathFin/Foundations/FeynmanKacHeatEquation.lean)

### Feynman–Kac heat flow — kernel-side derivatives ✅
The kernel convolution `feynmanU g t x = ∫ z, g z · K(t, z − x) dz`, with the
heat kernel **jointly Fréchet-differentiable** (`hasFDerivAt_heatKernel` — the
one genuinely-2D ingredient), giving `∂_t/∂_x/∂_xx` of `feynmanU` by dominated
differentiation under the integral, and the heat equation `∂_t U = ½ ∂_xx U`
(`feynmanU_heat_equation`) for sub-Gaussian payoffs.
→ *Finance:* the heat flow whose discounted log-transform *is* the
Black–Scholes price surface — the analytic engine of the FK keystone (Pricing
section below).
[`Foundations/FeynmanKacHeatEquation.lean`](../MathFin/Foundations/FeynmanKacHeatEquation.lean)

### Markov path law (Ionescu–Tulcea) ✅
The law of a countable-state Markov chain constructed on path space via
`Kernel.trajMeasure`, with the finite-cylinder factorization through the
transition kernels (`markovPathMeasure_cylinder`) — proved by comp-product
marginal induction, not assumed.
→ *Finance:* the path-space measure underlying lattice/tree models — every
discrete pricing tree is a Markov path law.
[`Foundations/MarkovPathMeasure.lean`](../MathFin/Foundations/MarkovPathMeasure.lean)

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
`gaussianReal_tilted_const_mul` ([`Foundations/Esscher.lean`](../MathFin/Foundations/Esscher.lean)).
The same lemma gives the Esscher transform of a jump-diffusion without jumps
(`jumpDiffusionIncrementLaw_zero_tilted`). The same file's tilted moments and identification of
a law by its moment-generating function give the case with jumps
(`jumpDiffusionIncrementLaw_tilted`).
[`Bridges/GaussianGirsanov.lean`](../MathFin/Bridges/GaussianGirsanov.lean)

### BSCallHyp from a Brownian model ✅
A concrete Brownian-driven physical model produces the pricing hypothesis
directly (`BSCallHyp.of_isPreBrownian`, `bsTerminal_via_brownian`) — the second
route into `BSCallHyp`.
[`Bridges/BSCallHypFromBrownian.lean`](../MathFin/Bridges/BSCallHypFromBrownian.lean)

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
[`Foundations/ContinuousFTAP.lean`](../MathFin/Foundations/ContinuousFTAP.lean)

## Pricing

### Black–Scholes call formula ✅
Under `BSCallHyp`, the call price is `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)`
(`bs_call_formula`).
→ *Finance:* the option price.
[`BlackScholes/Call.lean`](../MathFin/BlackScholes/Call.lean)

### `bs_identity` — the magic collapse ✅
The algebraic identity `S · φ(d₁) = K e^{−rτ} · φ(d₂)` (`bs_identity`) that makes
the pdf cross-terms cancel. It depends only on the `d₁`/`d₂` definitions and the
Gaussian density — a self-contained algebraic input, so it is a *root* in the
graph above (nothing in the spine proves it); it feeds the Greeks and the PDE.
→ *Finance:* the cancellation behind every clean Greek formula.
[`BlackScholes/PDE.lean`](../MathFin/BlackScholes/PDE.lean)

### Greeks ✅
δ (`hasDerivAt_bsV_S`), γ (`hasDerivAt_deriv_bsV_S`), vega (`hasDerivAt_bsV_sigma`),
θ (`hasDerivAt_bsV_t`), ρ (`hasDerivAt_bsV_r`) — each derived through
`bs_identity`.
→ *Finance:* the hedging sensitivities.
[`BlackScholes/PDE.lean`](../MathFin/BlackScholes/PDE.lean)

### Black–Scholes PDE ✅
`bsV` satisfies the Black–Scholes PDE (`bs_pde_holds`). *Correction recorded
2026-06-06, forced by the generated graph:* this page used to say "verified via
the Greeks and `bs_identity`" — the proof term shows otherwise. The PDE
statement carries the Greeks' closed forms in its slots, and the verification
is self-contained field algebra (`rw [bsV]; field_simp; ring`); it consumes
neither the Greek theorems nor `bs_identity`. The conceptual route Greeks →
PDE is real mathematics but a *different proof* than the one formalized; the
graph shows `thm:bs-pde` as a root, and that is the truth.
[`BlackScholes/PDE.lean`](../MathFin/BlackScholes/PDE.lean)

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
[`BlackScholes/PDEFromIto.lean`](../MathFin/BlackScholes/PDEFromIto.lean)

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
[`BlackScholes/PDEFromFeynmanKac.lean`](../MathFin/BlackScholes/PDEFromFeynmanKac.lean)

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
[`Foundations/ItoFormulaCLM.lean`](../MathFin/Foundations/ItoFormulaCLM.lean)

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
[`Foundations/ItoFormulaTD.lean`](../MathFin/Foundations/ItoFormulaTD.lean)

### CRR → Black–Scholes convergence ✅
The binomial (CRR) call price converges to the Black–Scholes call price as the
tree refines (`binomialPrice_call_tendsto_bs`): characteristic functions →
Lévy continuity → convergence in distribution, with **put–call parity lifting
the bounded put's weak convergence to the call** (avoiding a uniform-
integrability/Vitali argument). The discrete and continuous pricing theories
meet where they should.
→ *Finance:* the lattice methods used on every trading desk are not a separate
model — they are the same price, in the limit.
[`Binomial/CRRCharFun.lean`](../MathFin/Binomial/CRRCharFun.lean)

### Margrabe exchange option ✅
Under two correlated lognormal assets with drift `r`, the discounted expected payoff of
the option to exchange one for the other is Margrabe's closed form, a Black–Scholes call
on the ratio with effective volatility `√(σ₁² + σ₂² − 2ρσ₁σ₂)` (`margrabe_exchange_price`,
via `margrabe_bsCallHyp_of_gaussian` and `normalizedSpread_hasLaw_std`) — the
multivariate corollary.
[`BlackScholes/MargrabeGrounding.lean`](../MathFin/BlackScholes/MargrabeGrounding.lean)

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
[`Foundations/CarrMadan.lean`](../MathFin/Foundations/CarrMadan.lean)

### Binomial martingale representation — market completeness ✅
On the binomial tree (i.i.d. `Bernoulli(q)` coin flips, `0 < q < 1`), every Mathlib `Martingale` `M`
of the flips' natural filtration (`flipFiltration`) is its initial value plus the
`martingaleTransform` of a **predictable** hedge (`StronglyAdapted`) against the discounted asset:
`M_N = M_0 + ∑_{k<N} A_{k+1}·(S_{k+1} − S_k)` (`binomial_martingale_representation`). The hedge is
the node-wise delta `A = ΔM/ΔS`, predictable because it is fixed *before* the next flip is
revealed. The conditional expectation is the node average `q·X^U + (1−q)·X^D = X`
(`oneStep_of_martingale`), and the proof is the pathwise one-period delta hedge, telescoped. The
converse of `martingaleTransform_isMartingale` (`Foundations/MartingaleTransform.lean`).
→ *Finance:* **completeness** — the second pillar of the FTAP: every contingent claim is
replicable by a self-financing strategy, so the risk-neutral price is the *unique* arbitrage-free
price.
[`Binomial/MartingaleRepresentation.lean`](../MathFin/Binomial/MartingaleRepresentation.lean)

### Merton jump-diffusion dominance ✅
Jump risk is never free: the Black–Scholes price is dominated by the Merton
(1976) jump-diffusion price, `bsV ≤ mertonCallPrice`
(`bsV_le_mertonCallPrice`), through two channels — vega (per-term vol
widening) and gamma/Jensen (the mixture over jump counts, with the tangent's
linear term killed by `integral_mertonSpot`); the classic `Λ′ = Λ(1+k)`
weights display is `MertonClassicDisplay`.
→ *Finance:* ignoring jumps *underprices* options — the model-risk inequality,
as a theorem.
[`BlackScholes/MertonDominance.lean`](../MathFin/BlackScholes/MertonDominance.lean)

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
