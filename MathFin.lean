/-
  MathFin (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import MathFin` to pull
  everything in, or `import MathFin.<Section>.<Module>` for a
  specific submodule.

  Modules are organized by topic:

  * `Foundations/`   — probability primitives reused across finance.
  * `BlackScholes/`  — BS family (call, put, digitals, Greeks, PDE,
                       Asian / chooser / capped / power / lookback,
                       Breeden-Litzenberger, bisection IV, …).
  * `Futures/`       — Black-76 model.
  * `Binomial/`      — discrete-time tree, CRR convergence, Bermudan
                       sandwich, Merton 1973 American-call dominance.
  * `FixedIncome/`   — ZCB, coupon bonds, duration, convexity, YTM,
                       bootstrap, credit (constant + time-varying hazard),
                       forward-rate non-flat, Vasicek deterministic,
                       Macaulay-vs-modified discrete.
  * `Portfolio/`     — Markowitz, CAPM, two-fund separation, risk parity,
                       Black-Litterman, tangent portfolio FOC.
  * `Performance/`   — Sharpe / Sortino / Treynor / IR / Kelly.
  * `RiskMeasures/`  — VaR/CVaR + coherent-risk axioms, Rockafellar-Uryasev,
                       spectral risk, Herfindahl concentration.
  * `Actuarial/`     — net premium, Gompertz force of mortality.
  * `Execution/`     — Market microstructure and execution: Glosten-Milgrom
                       adverse-selection spread.
  * `DeFi/`          — Decentralized-finance market microstructure:
                       constant-product AMMs (Uniswap v2-style), swap
                       output, invariant preservation, internal price.
-/

-- Foundations
import MathFin.Foundations.StandardNormal
import MathFin.Foundations.DoobDecomposition
import MathFin.Foundations.L2MartingaleConvergence
import MathFin.Foundations.BrownianMarkov
-- Markov-chain path law derived from the pin's Ionescu–Tulcea trajectory
-- kernels (Saporito 1.1.2)
import MathFin.Foundations.MarkovPathMeasure
import MathFin.Foundations.ErlangSum
-- Poisson-process theory: superposition, thinning, marginal-from-arrivals,
-- first-interarrival law (Saporito 3.3.5/3.3.6/3.3.9/3.3.10)
import MathFin.Foundations.PoissonSuperposition
import MathFin.Foundations.PoissonThinning
import MathFin.Foundations.PoissonCounting
import MathFin.Foundations.PoissonInterarrival
-- Poisson probability generating function E[x^N] = e^{r(x−1)} (absent from
-- Mathlib); the engine behind Merton-mixture compensation identities
import MathFin.Foundations.PoissonPgf
-- The freezing lemma: E[g(X, Y)] = ∫ x, E[g(x, Y)] d(law X) for independent X, Y
import MathFin.Foundations.IndepFreezing
import MathFin.Foundations.PoissonRandomMeasure
import MathFin.Foundations.PoissonCompensatedIsometryAdapted
import MathFin.Foundations.PoissonCompensatedBilinear
import MathFin.Foundations.PoissonCompensatedIntegralL2
import MathFin.Foundations.PoissonCompensatedIntegralL2Dense
import MathFin.Foundations.PoissonCompensatedSimpleIntegrand
import MathFin.Foundations.PoissonCompensatedIntegralOperator
-- QV of an Itô process: drift contributes nothing (Saporito 7.4.5)
import MathFin.Foundations.ItoProcessQV
import MathFin.Foundations.GaussianMoments
import MathFin.Foundations.BivariateGaussian
import MathFin.Foundations.GaussianCDFDeriv
import MathFin.Foundations.GaussianGirsanov
import MathFin.Foundations.FeynmanKacHeatEquation
import MathFin.Foundations.BrownianMartingale
-- Continuous-time first FTAP: discounted GBM price is a Q-martingale (Wald exponential)
import MathFin.Foundations.ContinuousFTAP
-- Model-agnostic continuous-market vocabulary: IsEMM on a process, simple strategies, no-arbitrage
import MathFin.Foundations.ContinuousMarket
-- Bayes change-of-measure engine + Black–Scholes EMM via an explicit Girsanov density
import MathFin.Foundations.ChangeOfMeasure
import MathFin.Foundations.Girsanov
import MathFin.Foundations.ExpMartingaleQBrownian
import MathFin.Foundations.GirsanovConstantTheta
import MathFin.Foundations.SimpleDoleansExponential
import MathFin.Foundations.GirsanovSimpleTheta
import MathFin.Foundations.Numeraire
import MathFin.Foundations.BrownianQuadraticVariation
import MathFin.Foundations.QuadraticVariationL2
import MathFin.Foundations.ExpMin
import MathFin.Foundations.NoArbitrageCore
import MathFin.Foundations.FTAP
import MathFin.Foundations.OptionalSamplingInequality
import MathFin.Foundations.LpContinuousMartingaleConvergence
import MathFin.Foundations.MartingaleTransform
import MathFin.Foundations.DoobLpMaximalInequality
import MathFin.Foundations.ExtendOfNormIsometry
import MathFin.Foundations.WienerIntegralL2
import MathFin.Foundations.WienerIntegralGaussian
-- Wiener integral of a step indicator is the increment (∫𝟙_{(s,t]} dB = B_t − B_s)
import MathFin.Foundations.WienerIntegralIndicator
-- Structural / principle modules:
import MathFin.Foundations.StandardGaussianMGF
import MathFin.Foundations.ExponentialDiscount
import MathFin.Foundations.Bisection
-- The quantile function (generalized inverse CDF): Galois connection, quantile transform,
-- probability integral transform, equivariance; and the standard normal quantile Φ⁻¹
import MathFin.Foundations.Quantile
import MathFin.Foundations.NormalQuantile
import MathFin.Foundations.NormalTail
-- QRM foundations: quantile convergence, copulas and Sklar's theorem, Hoeffding's covariance
-- identity, Marshall–Olkin common shocks, correlation fallacies, extreme value theory (GEV, GPD,
-- maxima of Poisson-many losses)
import MathFin.Foundations.QuantileConvergence
import MathFin.Foundations.Copula
import MathFin.Foundations.Sklar
import MathFin.Foundations.CopulaFamilies
import MathFin.Foundations.HoeffdingCovariance
import MathFin.Foundations.MarshallOlkin
import MathFin.Foundations.CorrelationFallacies
import MathFin.Foundations.ExtremeValue
import MathFin.Foundations.GeneralizedPareto
import MathFin.Foundations.PoissonMaxima
-- Phase 13 additions:
import MathFin.Foundations.StatePrices
import MathFin.Foundations.TriangleArbitrage
import MathFin.Foundations.CarrMadan
import MathFin.Foundations.AlmgrenChriss
import MathFin.Foundations.DerivOfDeriv
import MathFin.Foundations.MarketMakingRiccati
import MathFin.Foundations.MatrixMarketMakingRiccati
import MathFin.Foundations.ConvexPricingFunctional
import MathFin.Foundations.ConvexSeparation
-- Phase 1 (convex-duality unification): cone-separation root generalizing
-- ConvexSeparation from a subspace (two-sided `= 0`) to a closed convex cone (`≤ 0`)
import MathFin.Foundations.ConvexDuality
-- Phase 30 (Bridge A): BSCallHyp / BachelierHyp from IsPreBrownian
import MathFin.Foundations.BSCallHypFromBrownian
-- Phase 31: Pricing entry points from IsPreBrownian (composite corollaries)
import MathFin.Foundations.PricingFromBrownian
-- Phase 32: Variance-swap log-price squared-increment from BrownianQuadraticVariation
import MathFin.Foundations.VarianceSwapFromQV
-- Phase 33: Variance-swap equipartition sum from BrownianQuadraticVariation
import MathFin.Foundations.VarianceSwapEquipartition
-- Phase 34: Variance-swap QV limit theorem (realised-variance → σ²T as n → ∞)
import MathFin.Foundations.VarianceSwapLimit
-- Variance-swap drift immunity: realized variance → σ²T in L² for ANY drift
-- (consumes ItoProcessQV; strengthens phase 34 from expectation-level to L²)
import MathFin.Foundations.VarianceSwapDriftImmunity
-- Phase 35: Discrete Itô formula (adapted from Nagy 2026, SSRN 6336503)
import MathFin.Foundations.DiscreteIto
-- The adapted Itô isometry (increment-independence cornerstone)
import MathFin.Foundations.ItoIsometryAdapted
-- Continuous L²-adapted Itô integral (construction, anchored on Degenne SimpleProcess)
import MathFin.Foundations.ItoIntegralL2
-- 𝓕ᴮ_T is the countable supremum of dyadic cylinder σ-algebras (path continuity)
import MathFin.Foundations.BrownianCylinderGeneration
-- The Itô integral as a continuous linear isometry `Lp 2 trim_T → Lp 2 μ` on `[0,T]`
import MathFin.Foundations.ItoIntegralCLM
import MathFin.Foundations.LpMulIsometry
import MathFin.Foundations.PredictableDensityGeneral
import MathFin.Foundations.ItoIntegralAgainstMartingale
-- BrownianMotion's axiomatic characterisation, instantiated: the integral against M = φ●B is an
-- `IsStochasticIntegral` (Riemann–Stieltjes values, dominated convergence, uniqueness)
import MathFin.Foundations.StochasticIntegralCharacterisation
-- The pointwise bracket: conditional Brownian kernels + single-band generators whose
-- integrals evaluate to explicit increments (the rung toward the conditional second moment)
import MathFin.Foundations.BracketCompensator
import MathFin.Foundations.PointwiseBracket
-- The unbounded-horizon `[0,∞)` Itô integral CLM `Lp 2 trim_full → Lp 2 μ` (Summit B / B2)
import MathFin.Foundations.ItoIntegralL2Dense
-- Covariation of Itô integrals: the bilinear Itô isometry ⟪∫φdB,∫ψdB⟫=⟪φ,ψ⟫ (D1)
import MathFin.Foundations.ItoIntegralCovariation
-- The elementary Itô integral as a process `t ↦ (V●B)_t`, with genuine `L²` content
import MathFin.Foundations.ItoIntegralProcess
-- The Itô integral process is an adapted L² martingale (Summit B / B1a)
import MathFin.Foundations.ItoIntegralProcessMartingale
-- The elementary Itô integral as a continuous local martingale (Summit B / B3)
import MathFin.Foundations.ItoIntegralProcessLocalMartingale
-- The general-integrand Itô integral as an L² martingale on [0,T] (Summit B / B1b)
import MathFin.Foundations.ItoIntegralProcessGeneral
-- The deferred time-indexed Itô isometry E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds (B1b refinement)
import MathFin.Foundations.ItoIntegralProcessIsometry
-- Continuous modification of the general-integrand Itô process on [0,T] (the gate)
import MathFin.Foundations.ItoIntegralProcessContinuousModification
-- Predictability of the assembled Itô process (the SDE-existence keystone)
import MathFin.Foundations.ItoProcessPredictable
-- Predictability of the assembled drift process (SDE-existence keystone II)
-- Cauchy–Schwarz on a finite measure (shared by the drift L² bound and SDE uniqueness)
import MathFin.Foundations.FiniteMeasureCauchySchwarz
import MathFin.Foundations.DriftProcessPredictable
-- σ-realization: a bounded adapted continuous process as an Itô-integrand L² class (α4 gap)
import MathFin.Foundations.AdaptedProcessToLp
-- Bounded-in-L² ⟹ uniformly-integrable-in-L¹ (Chebyshev truncation; the α4 Vitali producer)
import MathFin.Foundations.UnifIntegrableL2
-- The Picard map and its contraction estimate (SDE existence, #44)
import MathFin.Foundations.SDEExistence
-- Pathwise SDE uniqueness via the L²-energy Grönwall argument (#19)
import MathFin.Foundations.SDEUniqueness
-- The assembled drift's pathwise realization: convergence + coeFn = driftContinuousMod (SDE-existence bridge)
import MathFin.Foundations.DriftProcessModification
-- The strong solution as a pathwise process: slicing the Picard fixed point (pathwise SDE existence)
import MathFin.Foundations.SDEPathwise
-- The general-integrand Itô process as a continuous local martingale (null-augmented filtration)
import MathFin.Foundations.ItoIntegralProcessLocalMartingaleGeneral
-- The unbounded-horizon Itô process: the L² process, horizon consistency (the [0,∞) climb)
import MathFin.Foundations.ItoIntegralProcessL2Infinite
-- The [0,∞) crown: the unbounded-horizon Itô integral as a continuous local martingale on ℝ≥0
import MathFin.Foundations.ItoIntegralProcessLocalMartingaleInfinite
-- Pathwise discrete Itô identity for `f(x) = x²` (the squaring keystone)
import MathFin.Foundations.ItoSquaringIdentity
-- Polynomial Itô remainders (x³, x⁴) + the pathwise discrete cubing identity
import MathFin.Foundations.DiscreteItoPolynomial
-- Continuous-time L² Itô formula for `f(x) = x²`: `∑ B ΔB → ½(B_T² − B_0² − T)`
import MathFin.Foundations.ItoFormulaSquaredL2
-- Keystone: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` as a genuine `itoIntegralCLM_T` identity
-- (the continuous Itô integral's first real consumer)
import MathFin.Foundations.ItoIntegralBrownian
-- `𝓕_a`-linearity: a bounded `𝓕_a`-measurable factor passes through `∫₀ᵀ · dB`
-- when the integrand lives on `(a,T]` (locality of the stochastic integral)
import MathFin.Foundations.ItoIntegralLocality
-- Summit A: bounded-derivative continuous-time Itô formula in L² (CLM-identified)
import MathFin.Foundations.WeightedQuadraticVariation
import MathFin.Foundations.ItoFormulaRemainder
import MathFin.Foundations.ItoFormulaC2
import MathFin.Foundations.ItoIntegralRiemannBridge
-- Riemann↔CLM bridge for a bounded adapted continuous integrand θ (α4 brick b): ∫θdB CLM
import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
-- Step B1 of the adapted-coefficient Itô formula: freezing the integrand on a partition
import MathFin.Foundations.AdaptedStochasticIntegralFreezing
-- Step B2: the quadratic variation of an Itô process with adapted σ, ∑ w(ΔX)² → ∫ wσ² ds in L¹
import MathFin.Foundations.AdaptedQuadraticVariation
-- First-order term of the adapted Itô formula (martingale part): ∑ w(tₖ)ΔMₖ → ∫ w dM in L²
import MathFin.Foundations.AdaptedRiemannStieltjes
-- The drift of the adapted Itô formula: A = ∫b ds is Lipschitz, predictable, and ∑ g(tₖ)ΔAₖ → ∫ g·b ds
import MathFin.Foundations.AdaptedDrift
import MathFin.Foundations.ItoFormulaAdapted
-- Deterministic drift Riemann-convergence (α4 brick b-tail): ∑θ(tₖ)²·Δτ → ∫₀ᵀθ²ds
import MathFin.Foundations.DriftRiemannConvergence
-- Continuous adapted-θ Girsanov assembly (α4 (c)): convergence core toward Btheta_isQBrownianMotion_adapted
import MathFin.Foundations.GirsanovAdaptedTheta
-- Rung 1 (bounded predictable θ Girsanov, Route B): marshal a SimpleProcess into single-partition
-- (s,c) form; generic simple-Doléans moment bounds; the predictable distributional Girsanov theorem.
import MathFin.Foundations.SimpleProcessPartition
import MathFin.Foundations.GirsanovSimpleDoleansMoments
import MathFin.Foundations.GirsanovPredictableTheta
import MathFin.Foundations.ItoFormulaCLM
-- Summit A′: time-dependent Itô formula in L² — TD Taylor remainder vanishes,
-- TD Riemann↔CLM bridge, and the assembly f(T,B_T) = f(0,B₀) + ∫f_x dB + ∫(f_t+½f_xx)ds
import MathFin.Foundations.ItoFormulaTDRemainder
import MathFin.Foundations.ItoIntegralRiemannBridgeTD
import MathFin.Foundations.ItoFormulaTD
import MathFin.Foundations.BrownianExpMoment
import MathFin.Foundations.ItoFormulaLocalized
import MathFin.Foundations.ItoFormulaItoProcess
import MathFin.Foundations.ItoFormulaGBM
-- Martingale representation, step 3: the Doléans exponential of a deterministic step
-- integrand is an Itô integral (time locality of `∫·dB` + unbounded `𝓕_a`-scaling)
import MathFin.Foundations.DoleansStepRepresentation
-- Martingale representation, step 4: the Wiener exponentials are total in `L²(𝓕ᴮ_T)`
-- (Abel summation + Laplace-transform uniqueness on `ℝⁿ` + Lévy's upward theorem)
import MathFin.Foundations.WienerExponentialTotality
-- Martingale representation, step 5: the Itô integral is onto the centered `𝓕ᴮ_T`-measurable
-- part of `L²(μ)` — terminal, submodule and process forms of the representation theorem
import MathFin.Foundations.MartingaleRepresentation
-- Martingale representation, step 6: its finance reading — replication, superreplication
-- duality, and uniqueness of the pricing measure on the Brownian filtration
import MathFin.Foundations.MarketCompleteness
import MathFin.Foundations.MarketCompletenessInPrice
-- The price with a drift, S = S₀ + ∫b ds + (σ●B), and the integral against it
import MathFin.Foundations.PricePathDrift
import MathFin.Foundations.PricingMeasureL2Density
import MathFin.Foundations.ItoFormulaProcess
import MathFin.Foundations.ExitTime
import MathFin.Foundations.ItoFormulaUnrestricted
import MathFin.Foundations.ItoFormulaUnrestrictedLocMart
-- Phase 37: FTAP both directions, two-state market (adapted from Nagy 2026)
import MathFin.Foundations.FTAPTwoState
-- Phase 38: Constant-product AMM (adapted from Pusceddu-Bartoletti FMBC 2024)
import MathFin.DeFi.ConstantProductAMM
-- Phase 39: Itô structural drift formula + GBM log-drift (after Nagy 2026)
import MathFin.Foundations.ItoLemma
-- Time-dependent (2D) Itô formula + GBM-as-SDE-solution (genuine exp partials)
import MathFin.Foundations.ItoLemma2D
-- Phase 45: Variance swap log-payoff and QV-limit form equivalence
import MathFin.Foundations.VarianceSwapEquivalence
-- Phase 53: Pricing kernel from two-state FTAP (state-prices composition)
import MathFin.Foundations.PricingKernel
-- Shared change-of-measure helper: a positive normalised density gives an
-- equivalent probability measure (consumed by the one-period FTAP files)
import MathFin.Foundations.EquivMeasure
-- Phase 42: Multi-state FTAP backward (hypothesis-form, forward direction proved)
import MathFin.Foundations.FTAPMultiState
import MathFin.Foundations.FTAPDiscrete
-- General-Ω one-period FTAP (Föllmer–Schied 1.55 / one-period DMW, scalar)
import MathFin.Foundations.FTAPOnePeriod
-- General-Ω one-period FTAP, d assets (Esscher minimal-divergence EMM, full — finite-dim market)
import MathFin.Foundations.FTAPOnePeriodVector
-- BlackScholes
import MathFin.BlackScholes.Call
import MathFin.BlackScholes.Put
import MathFin.BlackScholes.PDE
import MathFin.BlackScholes.PutGreeks
import MathFin.BlackScholes.Digital
import MathFin.BlackScholes.DigitalGreeks
import MathFin.BlackScholes.Dividends
import MathFin.BlackScholes.DividendsGreeks
import MathFin.BlackScholes.Forward
import MathFin.BlackScholes.HigherGreeks
import MathFin.BlackScholes.StrikeGreeks
import MathFin.BlackScholes.PutStrikeConvexity
import MathFin.BlackScholes.StaticBounds
import MathFin.BlackScholes.AsianInequality
-- Geometric-average Asian: two-date log-driver is Gaussian with the covariance-sum variance
import MathFin.BlackScholes.AsianGeometric
-- Geometric-average Asian: n-date driver law + closed-form price via effective-BS reduction
import MathFin.BlackScholes.AsianGeometricN
import MathFin.BlackScholes.ImpliedVolatility
import MathFin.BlackScholes.LognormalMoments
import MathFin.BlackScholes.VarianceSwap
-- Merton (1976) jump-diffusion: Poisson-mixture price, compensation
-- identity, parity (consumes Foundations.PoissonPgf + Call/Put formulas)
import MathFin.BlackScholes.MertonJumpDiffusion
-- Merton dominance (jump risk is never free: vega + gamma/Jensen channels)
-- and the classic Λ′ = Λ(1+k) display (rate-shift identity)
import MathFin.BlackScholes.MertonDominance
import MathFin.BlackScholes.MertonClassicDisplay
-- Merton's model derived: the jump-diffusion terminal price (Gaussian diffusion,
-- Poisson count, i.i.d. lognormal jumps) prices to the Poisson mixture
import MathFin.BlackScholes.MertonModel
-- Merton Greeks: delta, gamma, vega as Poisson mixtures of Black–Scholes Greeks
import MathFin.BlackScholes.MertonGreeks
import MathFin.BlackScholes.Bachelier
import MathFin.BlackScholes.BachelierGreeks
import MathFin.BlackScholes.Chooser
import MathFin.BlackScholes.CappedCall
import MathFin.BlackScholes.Spreads
import MathFin.BlackScholes.Lookback
import MathFin.BlackScholes.BarrierParity
import MathFin.BlackScholes.PowerOption
import MathFin.BlackScholes.BreedenLitzenberger
import MathFin.BlackScholes.BisectionIV
-- Structural / principle modules:
import MathFin.BlackScholes.StrikeConvexity
import MathFin.BlackScholes.SpotConvexity
import MathFin.BlackScholes.PriceBounds
import MathFin.BlackScholes.CallPriceFunction
-- Phase 13 additions:
import MathFin.BlackScholes.Quanto
-- Quanto correction derived from a joint-Gaussian FX model (Girsanov-grounded)
import MathFin.BlackScholes.QuantoGrounding
import MathFin.BlackScholes.NewtonConvergence
import MathFin.BlackScholes.NewtonRaphsonIV
import MathFin.BlackScholes.LognormalCOV

-- Futures
import MathFin.Futures.Black76
import MathFin.Futures.Black76Greeks
-- Phase 13 additions:
import MathFin.Futures.Swaption

-- Binomial
import MathFin.Binomial.Model
import MathFin.Binomial.American
import MathFin.Binomial.CRRConvergence
import MathFin.Binomial.DriftLimit
import MathFin.Binomial.Bermudan
import MathFin.Binomial.MartingaleRepresentation
import MathFin.Binomial.AmericanCallNoDividend
-- Phase 13 additions:
import MathFin.Binomial.Girsanov
import MathFin.Binomial.SecondFTAP
-- Phase 14: real new theorems
import MathFin.Binomial.MertonAmericanCallTree
import MathFin.Binomial.ReplicatingUniqueness
import MathFin.BlackScholes.GreekSigns
-- Phase 16: reflection-principle algebraic core (André 1887)
import MathFin.Binomial.PathReflection
-- Barrier-option counting: reflection card identity + maximal-distribution (running-max law)
import MathFin.Binomial.BarrierReflection
-- Phase 19: Snell envelope characterization of americanPrice
import MathFin.Binomial.SnellEnvelope
-- Phase 43: Binomial up-probability as two-state FTAP EMM
import MathFin.Binomial.BinomialFromFTAP
-- Phase 44: CRR binomial scheme as discrete-Itô process (drift + QV limits)
import MathFin.Binomial.CRRDiscreteIto
-- CRR → BS characteristic-function convergence (the distributional CLT heart)
import MathFin.Binomial.CRRCharFun
-- CRR → BS in literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (Φ-landing corollary)
import MathFin.Binomial.CRRClosedForm
-- Phase 20: first-principles core derivations
import MathFin.Foundations.NoArbitrageDerivations
import MathFin.BlackScholes.RiskNeutralProbabilities
-- Phase 22: delta as stock-numeraire probability (Φ(d_1) = Q^(S)(S_T > K))
import MathFin.BlackScholes.StockNumeraire
-- Phase 24: powered call closed form via reduction to BS-call (effective spot/vol)
import MathFin.BlackScholes.PowerCall
-- BS-family Garman normal form (`V = A·Φ(d_1) − K·DF·Φ(d_2)`): the single
-- numéraire-parameterised template consumed by ExchangeOption, Black-76, KMVMerton
import MathFin.BlackScholes.GarmanNormalForm
import MathFin.BlackScholes.ExchangeOption
-- Margrabe BSCallHyp grounding from a joint two-GBM gaussian model (leap-3 closure)
import MathFin.BlackScholes.MargrabeGrounding
-- Phase 25: chooser option as call + put portfolio via PCP at chooser date
import MathFin.BlackScholes.ChooserComposition
-- Phase 46: BS PDE derived from Itô drift + no-arbitrage
import MathFin.BlackScholes.PDEFromIto
-- Feynman–Kac → BS PDE keystone (step 2: the FK price representation)
import MathFin.BlackScholes.PDEFromFeynmanKac
-- Phase 40: Itô lemma L¹-expectation form applied to GBM log (mean + variance)
import MathFin.BlackScholes.GBMLogMoments

-- FixedIncome
import MathFin.FixedIncome.ZCB
import MathFin.FixedIncome.CouponBonds
import MathFin.FixedIncome.Immunization
import MathFin.FixedIncome.ConvexityImmunization
import MathFin.FixedIncome.YieldCurve
import MathFin.FixedIncome.Credit
-- First-to-default: basket intensity = Σ single-name intensities
-- (bridges Foundations.ExpMin into the Credit vocabulary)
import MathFin.FixedIncome.FirstToDefault
import MathFin.FixedIncome.MacaulayModified
import MathFin.FixedIncome.HazardCurve
import MathFin.FixedIncome.ForwardRate
import MathFin.FixedIncome.Vasicek
-- Phase 13 additions:
import MathFin.FixedIncome.KMVMerton
import MathFin.FixedIncome.MeanReversionHalfLife
import MathFin.FixedIncome.CDS
-- Phase 21: first-principles duration-as-price-sensitivity
import MathFin.FixedIncome.DurationSensitivity
-- Phase 22: first-principles convexity-as-second-derivative
import MathFin.FixedIncome.ConvexitySensitivity
-- Phase 27: KMV-Merton structural derivation (probabilistic content of `kmvPD`)
import MathFin.FixedIncome.KMVMertonStructural
-- Phase 28: CDS fair spread under time-varying hazard (cash-flow balance)
import MathFin.FixedIncome.CDSTimeVarying
-- Phase 41: Vasicek SDE closed-form (full SDE, mean + variance)
import MathFin.FixedIncome.VasicekSDE
-- Itô→pricing bridge: Vasicek terminal law derived (Wiener integral is Gaussian)
import MathFin.FixedIncome.VasicekSDEGaussian
-- Vasicek zero-coupon bond price: the affine term structure (Gaussian Laplace transform)
import MathFin.FixedIncome.VasicekBondPrice
-- The T-forward measure: the zero-coupon bond as numéraire (change-of-numéraire instance)
import MathFin.FixedIncome.ForwardMeasure

-- Portfolio
import MathFin.Portfolio.Markowitz
import MathFin.Portfolio.CovariancePSD
import MathFin.Portfolio.MarkowitzNAsset
import MathFin.Portfolio.CAPM
import MathFin.Portfolio.TwoFundSeparation
import MathFin.Portfolio.RiskParity
import MathFin.Portfolio.BlackLitterman
import MathFin.Portfolio.TangentPortfolio
-- Phase 13 additions:
import MathFin.Portfolio.TangentPortfolioN
-- Phase 21: first-principles Sharpe-FOC and CAPM-equilibrium derivations
import MathFin.Portfolio.SharpeFOCDerivation
import MathFin.Portfolio.CAPMEquilibrium
-- Phase 23: N-asset Markowitz Lagrangian FOC (forward direction)
import MathFin.Portfolio.MarkowitzLagrangian
-- Phase 26: N-asset risk parity from log-barrier Lagrangian FOC
import MathFin.Portfolio.RiskParityFOC
-- Phase 29: N-dim Black-Litterman posterior (matrix form)
import MathFin.Portfolio.BlackLittermanND

-- Performance
import MathFin.Performance.Ratios
import MathFin.Performance.RatiosExtended
import MathFin.Performance.DownsideMetrics
import MathFin.Performance.Kelly
import MathFin.Performance.KellyNumeraire

-- RiskMeasures
import MathFin.RiskMeasures.Gaussian
import MathFin.RiskMeasures.CoherentAxioms
import MathFin.RiskMeasures.Additivity
import MathFin.RiskMeasures.RockafellarUryasev
import MathFin.RiskMeasures.Spectral
import MathFin.RiskMeasures.Concentration
-- Phase 21: first-principles coherent-axiom derivation from concave utility
import MathFin.RiskMeasures.UtilityDerivation
-- The layer beneath UtilityDerivation, which takes the expected-utility form as given:
-- von Neumann-Morgenstern lotteries, the mixture algebra, affinity of expected utility in
-- the mixture, and the vNM axioms verified for the induced preference (the soundness half,
-- plus invariance of the preference under positive affine rescaling of the utility)
import MathFin.RiskMeasures.VonNeumannMorgenstern
-- Phase 1 (convex-duality unification): coherent-risk ADEH representation — acceptance cone
-- separation giving the representing probability measures (risk-side Hahn–Banach)
import MathFin.RiskMeasures.AcceptanceSet
-- Phase 1 (convex-duality unification): worst-case loss — the most conservative coherent risk
-- measure, concrete instance of the ADEH representation (sup over the entire probability simplex)
import MathFin.RiskMeasures.WorstCaseRisk
-- Value-at-risk and expected shortfall of a general loss (any law, atoms included), and the
-- Gaussian closed forms identified as the VaR of the law at z = Φ⁻¹(α)
import MathFin.RiskMeasures.ValueAtRisk
import MathFin.RiskMeasures.GaussianValueAtRisk
-- Expected shortfall: Rockafellar–Uryasev for every law, coherence, dual representation; the
-- Gaussian ES closed form; VaR by bisection; VaR superadditivity; closed forms and tail ratios;
-- elicitability (VaR elicitable, ES not); Bernoulli mixtures and the Basel IRB limit theorem
import MathFin.RiskMeasures.ExpectedShortfall
import MathFin.RiskMeasures.GaussianExpectedShortfall
import MathFin.RiskMeasures.ValueAtRiskBisection
import MathFin.RiskMeasures.VaRSuperadditivity
import MathFin.RiskMeasures.RiskClosedForms
import MathFin.RiskMeasures.Elicitability
import MathFin.RiskMeasures.Expectile
import MathFin.RiskMeasures.StandardDeviationPrinciple
import MathFin.RiskMeasures.BernoulliMixture
import MathFin.RiskMeasures.VasicekIRB
-- Phase 1 (convex-duality unification): fundamental superhedging bound — every EMM prices a claim
-- at most its super-replication cost (the pricing-side companion of the coherent-risk representation)
import MathFin.Foundations.SuperhedgingDuality

-- Bridges (certified cross-domain unifications)
import MathFin.Bridges.ConcentrationVariance
import MathFin.Bridges.SurvivalUnification

-- Actuarial
import MathFin.Actuarial.Insurance
import MathFin.Actuarial.Mortality
-- Phase 13 additions:
import MathFin.Actuarial.CompoundPoisson
-- Compound-Poisson aggregate-loss MGF: iid-sum MGF composed with the Poisson pgf
import MathFin.Actuarial.CompoundPoissonMGF
-- Survival model (re-formalized from Yosuke Ito's AFP `Survival_Model`, BSD, cited)
import MathFin.Actuarial.SurvivalModel

-- Upstream (Degenne BrownianMotion) modules consumed ONLY by benchmark
-- wrappers, imported here so `lake build` puts them in the build graph —
-- nothing else in MathFin/ imports them, and a snippet import of an unbuilt
-- module fails with a silently-empty environment (found 2026-06-05 via
-- cm-thm-4.3.7; its sibling cm-thm-4.3.9 works only because
-- Foundations/LpContinuousMartingaleConvergence imports Degenne's DoobLp).
import BrownianMotion.StochasticIntegral.LocalMartingale
import MathFin.FixedIncome.InterestRateSwap
import MathFin.FixedIncome.FRA
import MathFin.Actuarial.ActuarialInsurance

-- Contracts tower: a reified payoff language, model-agnostic until priced
-- (Bilokon, "The Contract Is Not the Model", 9 August 2026)
import MathFin.Contracts.Core
import MathFin.Contracts.Adapted
import MathFin.Contracts.Pricing
import MathFin.Contracts.BlackScholes
import MathFin.Contracts.CappedCall

-- Execution: market microstructure — the Glosten-Milgrom adverse-selection
-- spread, plus a six-point model witnessing that its hypotheses are satisfiable
import MathFin.Execution.GlostenMilgrom
import MathFin.Execution.GlostenMilgromModel
-- Continuous-time American put option exercise-boundary geometry
import MathFin.BlackScholes.AmericanPut.Stopping.PhysicalBoundaryConvexity
import MathFin.BlackScholes.AmericanPut.Stopping.AEHorizonValue
-- QRM bridges: equicorrelation, Gaussian VaR/ES-optimal = Markowitz portfolios, the HHI
-- systematic floor, and the square-root-of-time rule for GBM losses
import MathFin.Portfolio.Equicorrelation
import MathFin.Bridges.GaussianRiskMarkowitz
import MathFin.Bridges.EquicorrelationConcentration
import MathFin.Bridges.SquareRootOfTime
-- The SVI no-butterfly certificate (Robert Martin, #174)
import MathFin.BlackScholes.SVI.Admissibility
import MathFin.BlackScholes.SVI.Assembly
import MathFin.BlackScholes.SVI.AssociatedTrace
import MathFin.BlackScholes.SVI.BlackScholesBridge
import MathFin.BlackScholes.SVI.BlackSmile
import MathFin.BlackScholes.SVI.CallConvexity
import MathFin.BlackScholes.SVI.ClearedSignature
import MathFin.BlackScholes.SVI.Companion
import MathFin.BlackScholes.SVI.ConvexKink
import MathFin.BlackScholes.SVI.CriticalPoints
import MathFin.BlackScholes.SVI.DegreeProgram
import MathFin.BlackScholes.SVI.Denominators
import MathFin.BlackScholes.SVI.Derivatives
import MathFin.BlackScholes.SVI.DomainFormula
import MathFin.BlackScholes.SVI.ExtendedFormula
import MathFin.BlackScholes.SVI.FiniteCertificate
import MathFin.BlackScholes.SVI.HermiteIdentity
import MathFin.BlackScholes.SVI.ImaginaryTraceSignature
import MathFin.BlackScholes.SVI.Matrices
import MathFin.BlackScholes.SVI.MatrixCertificate
import MathFin.BlackScholes.SVI.MatrixSignature
import MathFin.BlackScholes.SVI.NilpotentSquareRoot
import MathFin.BlackScholes.SVI.ParameterPolynomials
import MathFin.BlackScholes.SVI.Polynomial
import MathFin.BlackScholes.SVI.PolynomialCertificate
import MathFin.BlackScholes.SVI.ProductSignature
import MathFin.BlackScholes.SVI.QuadraticRay
import MathFin.BlackScholes.SVI.QuadraticRootSignature
import MathFin.BlackScholes.SVI.QuotientProduct
import MathFin.BlackScholes.SVI.RankOneSignature
import MathFin.BlackScholes.SVI.RealIrreducibles
import MathFin.BlackScholes.SVI.RealRootSignature
import MathFin.BlackScholes.SVI.RealRootTrace
import MathFin.BlackScholes.SVI.Reduction
import MathFin.BlackScholes.SVI.SigmaZeroCertificate
import MathFin.BlackScholes.SVI.SigmaZeroConvexity
import MathFin.BlackScholes.SVI.SigmaZeroDerivatives
import MathFin.BlackScholes.SVI.SignFormula
import MathFin.BlackScholes.SVI.SignVariations
import MathFin.BlackScholes.SVI.SignatureProgram
import MathFin.BlackScholes.SVI.TraceForm
import MathFin.BlackScholes.SVI.TraceSignature
-- The SVI tail condition d₊ → −∞ iff b(1+ρ) < 2, and the butterfly-free sign formula
import MathFin.BlackScholes.SVI.TailCondition
