/-
  MathFin (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import MathFin` to pull
  everything in, or `import MathFin.<Layer>.<…>.<Module>` for a
  specific submodule.

  Modules are organized in layers, and imports point one way
  (docs/specs/2026-11-07-one-trunk-design.md, §3 I4):
  * `Probability/` — the roots: discrete and continuous martingales, Brownian motion and Itô calculus, jumps, Gaussian and other laws.
  * `Contracts/`   — the payoff language: payoffs, contracts, measurability and adaptedness.
  * `Pricing/`     — the trunk: equivalent martingale measures, the FTAPs, state prices, numéraires, replication, completeness, superhedging, contract value.
  * `Models/`      — limb: Black–Scholes (and the American put), Bachelier, local and stochastic volatility, jumps, rates, credit, binomial, forwards, model-free.
  * `Risk/`        — limb: law functionals (VaR), coherent risk measures and their duals, credit portfolio risk, exposure.
  * `Choice/`      — limb: utility, portfolios, performance, equilibrium.
  * `Insurance/`   — limb: survival, premiums, compound losses.
  * `Markets/`     — limb: price formation, execution, AMMs and lending.
-/

import MathFin.Init

-- Probability
import MathFin.Probability.Gaussian.StandardNormal
import MathFin.Probability.Discrete.DoobDecomposition
import MathFin.Probability.Discrete.SnellDoobDecomposition
import MathFin.Probability.Discrete.SnellEnvelope
import MathFin.Probability.Discrete.L2MartingaleConvergence
import MathFin.Probability.Brownian.BrownianMarkov
-- Markov-chain path law derived from the pin's Ionescu–Tulcea trajectory
-- kernels (Saporito 1.1.2)
import MathFin.Probability.Discrete.MarkovPathMeasure
import MathFin.Probability.Laws.ErlangSum
-- Poisson-process theory: superposition, thinning, marginal-from-arrivals,
-- first-interarrival law (Saporito 3.3.5/3.3.6/3.3.9/3.3.10)
import MathFin.Probability.Jumps.PoissonSuperposition
import MathFin.Probability.Jumps.PoissonThinning
import MathFin.Probability.Jumps.PoissonCounting
import MathFin.Probability.Jumps.PoissonInterarrival
-- Poisson probability generating function E[x^N] = e^{r(x−1)} (absent from
-- Mathlib); the engine behind Merton-mixture compensation identities
import MathFin.Probability.Jumps.PoissonPgf
-- CreditRisk+ sector pgf: Poisson default count mixed over a Gamma sector factor, as an
-- iterated integral
import MathFin.Probability.Laws.GammaPoissonMixturePgf
-- The freezing lemma: E[g(X, Y)] = ∫ x, E[g(x, Y)] d(law X) for independent X, Y
import MathFin.Probability.Analysis.IndepFreezing
-- Jensen's inequality through a supporting line (no closed domain needed)
import MathFin.Probability.Analysis.AffineMinorant
-- The exponential martingale of a process with independent increments
import MathFin.Probability.Jumps.ExpMartingaleIndepIncrements
import MathFin.Probability.Jumps.PoissonRandomMeasure
import MathFin.Probability.Jumps.PoissonCompensatedIsometryAdapted
import MathFin.Probability.Jumps.PoissonCompensatedBilinear
import MathFin.Probability.Jumps.PoissonCompensatedIntegralL2
import MathFin.Probability.Jumps.PoissonCompensatedIntegralL2Dense
import MathFin.Probability.Jumps.PoissonCompensatedSimpleIntegrand
import MathFin.Probability.Jumps.PoissonCompensatedIntegralOperator
-- QV of an Itô process: drift contributes nothing (Saporito 7.4.5)
import MathFin.Probability.Brownian.Ito.ItoProcessQV
import MathFin.Probability.Gaussian.GaussianMoments
import MathFin.Probability.Gaussian.BivariateGaussian
import MathFin.Probability.Gaussian.BivariateNormalCDF
import MathFin.Probability.Gaussian.GaussianCDFDeriv
-- The Esscher transform of a law on ℝ (Mathlib's `Measure.tilted`): tilted moments, a law with
-- every exponential moment is fixed by its MGF, and the Gaussian tilt N(m, v) ↦ N(m + θv, v)
import MathFin.Probability.Laws.Esscher
import MathFin.Probability.Gaussian.FeynmanKacHeatEquation
import MathFin.Probability.Brownian.BrownianMartingale
-- Bayes change-of-measure engine + Black–Scholes EMM via an explicit Girsanov density
import MathFin.Probability.Martingales.ChangeOfMeasure
import MathFin.Probability.Brownian.ExpMartingaleQBrownian
import MathFin.Probability.Martingales.LevyQuadraticSums
import MathFin.Probability.Martingales.LevyExpMartingale
import MathFin.Probability.Brownian.ExpMartingaleBrownian
import MathFin.Probability.Martingales.StoppedProcessPaths
import MathFin.Probability.Martingales.BoundedLocalMartingale
import MathFin.Probability.Brownian.LevyCharacterization
import MathFin.Probability.Brownian.Girsanov.GirsanovConstantTheta
import MathFin.Probability.Brownian.Girsanov.SimpleDoleansExponential
import MathFin.Probability.Brownian.Girsanov.GirsanovSimpleTheta
import MathFin.Probability.Brownian.BrownianQuadraticVariation
-- The uniform partition of [0, T] (and [s, t]): the one equipartition of the Itô stack
import MathFin.Probability.Brownian.UnifPart
import MathFin.Probability.Brownian.QuadraticVariationL2
import MathFin.Probability.Laws.ExpMin
import MathFin.Probability.Discrete.OptionalSamplingInequality
import MathFin.Probability.Martingales.LpContinuousMartingaleConvergence
import MathFin.Probability.Martingales.MartingaleSetIntegral
import MathFin.Probability.Analysis.IndepIsometryKernel
import MathFin.Probability.Discrete.MartingaleTransform
import MathFin.Probability.Discrete.DoobLpMaximalInequality
import MathFin.Probability.Analysis.ExtendOfNormIsometry
import MathFin.Probability.Brownian.Wiener.WienerIntegralL2
import MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian
-- Wiener integral of a step indicator is the increment (∫𝟙_{(s,t]} dB = B_t − B_s)
import MathFin.Probability.Brownian.Wiener.WienerIntegralIndicator
import MathFin.Probability.Brownian.Wiener.WienerIntegralIto
import MathFin.Probability.Brownian.Wiener.WienerIntegralFiltration
-- Structural / principle modules:
import MathFin.Probability.Gaussian.StandardGaussianMGF
import MathFin.Probability.Analysis.ExponentialDiscount
import MathFin.Probability.Analysis.Bisection
-- The quantile function (generalized inverse CDF): Galois connection, quantile transform,
-- probability integral transform, equivariance; and the standard normal quantile Φ⁻¹
import MathFin.Probability.Laws.Quantile
import MathFin.Probability.Gaussian.NormalQuantile
import MathFin.Probability.Gaussian.NormalTail
-- The Student-t law: density in closed form, the ν = 1 Cauchy anchor, the tail first moment
import MathFin.Probability.Laws.StudentT
-- QRM foundations: quantile convergence, copulas and Sklar's theorem, Hoeffding's covariance
-- identity, Marshall–Olkin common shocks, correlation fallacies, extreme value theory (GEV, GPD,
-- maxima of Poisson-many losses)
import MathFin.Probability.Laws.QuantileConvergence
import MathFin.Probability.Dependence.Copula
import MathFin.Probability.Dependence.Sklar
import MathFin.Probability.Dependence.CopulaFamilies
import MathFin.Probability.Dependence.GaussianCopula
import MathFin.Probability.Dependence.HoeffdingCovariance
import MathFin.Probability.Dependence.MarshallOlkin
import MathFin.Probability.Dependence.CorrelationFallacies
import MathFin.Probability.Laws.ExtremeValue
import MathFin.Probability.Laws.GeneralizedPareto
import MathFin.Probability.Jumps.PoissonMaxima
import MathFin.Probability.Analysis.DerivOfDeriv
-- Phase 35: Discrete Itô formula (adapted from Nagy 2026, SSRN 6336503)
import MathFin.Probability.Discrete.DiscreteIto
-- The adapted Itô isometry (increment-independence cornerstone)
import MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
-- Continuous L²-adapted Itô integral (construction, anchored on Degenne SimpleProcess)
import MathFin.Probability.Brownian.Ito.ItoIntegralL2
-- 𝓕ᴮ_T is the countable supremum of dyadic cylinder σ-algebras (path continuity)
import MathFin.Probability.Brownian.BrownianCylinderGeneration
-- The Itô integral as a continuous linear isometry `Lp 2 trim_T → Lp 2 μ` on `[0,T]`
import MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense
import MathFin.Probability.Brownian.Ito.ItoIntegralCLM
import MathFin.Probability.Analysis.LpMulIsometry
import MathFin.Probability.Brownian.Girsanov.PredictableDensityGeneral
import MathFin.Probability.Brownian.Ito.ItoIntegralAgainstMartingale
-- BrownianMotion's axiomatic characterisation, instantiated: the integral against M = φ●B is an
-- `IsStochasticIntegral` (Riemann–Stieltjes values, dominated convergence, uniqueness)
import MathFin.Probability.Brownian.Ito.StochasticIntegralCharacterisation
-- The pointwise bracket: conditional Brownian kernels + single-band generators whose
-- integrals evaluate to explicit increments (the rung toward the conditional second moment)
import MathFin.Probability.Martingales.BracketCompensator
import MathFin.Probability.Martingales.PointwiseBracket
-- The unbounded-horizon `[0,∞)` Itô integral CLM `Lp 2 trim_full → Lp 2 μ` (Summit B / B2)
import MathFin.Probability.Brownian.Ito.ItoIntegralL2Dense
-- Covariation of Itô integrals: the bilinear Itô isometry ⟪∫φdB,∫ψdB⟫=⟪φ,ψ⟫ (D1)
import MathFin.Probability.Brownian.Ito.ItoIntegralCovariation
-- The elementary Itô integral as a process `t ↦ (V●B)_t`, with genuine `L²` content
import MathFin.Probability.Brownian.Ito.ItoIntegralProcess
-- The Itô integral process is an adapted L² martingale (Summit B / B1a)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessMartingale
-- The elementary Itô integral as a continuous local martingale (Summit B / B3)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingale
-- The general-integrand Itô integral as an L² martingale on [0,T] (Summit B / B1b)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
-- The deferred time-indexed Itô isometry E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds (B1b refinement)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessIsometry
-- Continuous modification of the general-integrand Itô process on [0,T] (the gate)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessContinuousModification
-- Predictability of the assembled Itô process (the SDE-existence keystone)
import MathFin.Probability.Brownian.Ito.ItoProcessPredictable
-- Predictability of the assembled drift process (SDE-existence keystone II)
-- Cauchy–Schwarz on a finite measure (shared by the drift L² bound and SDE uniqueness)
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
import MathFin.Probability.Analysis.StdSimplexProd
import MathFin.Probability.Brownian.Ito.DriftProcessPredictable
-- σ-realization: a bounded adapted continuous process as an Itô-integrand L² class (α4 gap)
import MathFin.Probability.Brownian.Ito.AdaptedProcessToLp
-- Bounded-in-L² ⟹ uniformly-integrable-in-L¹ (Chebyshev truncation; the α4 Vitali producer)
import MathFin.Probability.Martingales.UnifIntegrableL2
-- The Picard map and its contraction estimate (SDE existence, #44)
import MathFin.Probability.Brownian.SDE.SDEExistence
-- Pathwise SDE uniqueness via the L²-energy Grönwall argument (#19)
import MathFin.Probability.Brownian.SDE.SDEUniqueness
-- The assembled drift's pathwise realization: convergence + coeFn = driftContinuousMod
-- (SDE-existence bridge)
import MathFin.Probability.Brownian.Ito.DriftProcessModification
-- The strong solution as a pathwise process: slicing the Picard fixed point (pathwise SDE
-- existence)
import MathFin.Probability.Brownian.SDE.SDEPathwise
-- The general-integrand Itô process as a continuous local martingale (null-augmented filtration)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleGeneral
-- The unbounded-horizon Itô process: the L² process, horizon consistency (the [0,∞) climb)
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessL2Inf
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessL2Infinite
-- The [0,∞) crown: the unbounded-horizon Itô integral as a continuous local martingale on ℝ≥0
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleInfinite
-- Pathwise discrete Itô identity for `f(x) = x²` (the squaring keystone)
import MathFin.Probability.Brownian.Ito.ItoSquaringIdentity
-- Polynomial Itô remainders (x³, x⁴) + the pathwise discrete cubing identity
import MathFin.Probability.Discrete.DiscreteItoPolynomial
-- Continuous-time L² Itô formula for `f(x) = x²`: `∑ B ΔB → ½(B_T² − B_0² − T)`
import MathFin.Probability.Brownian.Ito.ItoFormulaSquaredL2
-- The Riemann-Itô sum `riemannσ`: the one left-endpoint sum every bridge below is a case of
import MathFin.Probability.Brownian.Ito.ItoRiemannSum
-- Keystone: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` as a genuine `itoIntegralCLM_T` identity
-- (the continuous Itô integral's first real consumer)
import MathFin.Probability.Brownian.Ito.ItoIntegralBrownian
-- `𝓕_a`-linearity: a bounded `𝓕_a`-measurable factor passes through `∫₀ᵀ · dB`
-- when the integrand lives on `(a,T]` (locality of the stochastic integral)
import MathFin.Probability.Brownian.Ito.ItoIntegralLocality
-- Summit A: bounded-derivative continuous-time Itô formula in L² (CLM-identified)
import MathFin.Probability.Brownian.WeightedQuadraticVariation
import MathFin.Probability.Brownian.Ito.ItoFormulaRemainder
-- Riemann↔CLM bridge for a bounded adapted continuous integrand θ (α4 brick b): ∫θdB CLM
import MathFin.Probability.Brownian.Ito.ItoIntegralRiemannBridgeAdapted
-- Step B1 of the adapted-coefficient Itô formula: freezing the integrand on a partition
import MathFin.Probability.Brownian.Ito.AdaptedStochasticIntegralFreezing
-- Step B2: the quadratic variation of an Itô process with adapted σ, ∑ w(ΔX)² → ∫ wσ² ds in L¹
import MathFin.Probability.Brownian.AdaptedQuadraticVariation
-- First-order term of the adapted Itô formula (martingale part): ∑ w(tₖ)ΔMₖ → ∫ w dM in L²
import MathFin.Probability.Brownian.AdaptedRiemannStieltjes
-- The drift of the adapted Itô formula: A = ∫b ds is Lipschitz, predictable, and ∑ g(tₖ)ΔAₖ → ∫ g·b
-- ds
import MathFin.Probability.Brownian.Ito.AdaptedDrift
import MathFin.Probability.Brownian.Ito.ItoFormulaAdapted
-- Itô's formula for adapted coefficients, localised to every C² f and every t ≤ T
import MathFin.Probability.Martingales.LocalisationInMeasure
-- Itô's formula for f(t, X_t) along an Itô process with adapted coefficients, every t ≤ T
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedTD
-- The Itô integral of an unbounded continuous adapted integrand, by localisation
import MathFin.Probability.Brownian.Ito.ItoIntegralLocalised
-- The Itô integral of an unbounded continuous adapted integrand is a local martingale
import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedLocalMartingale
-- Itô's formula along an Itô process with unbounded adapted coefficients
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedUnbounded
-- Riemann sums of a bounded predictable integrand with almost surely continuous paths
import MathFin.Probability.Brownian.Ito.ItoIntegralPredictableRiemann
-- The Itô integral of a predictable integrand with almost surely continuous paths
import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedPredictable
-- Itô's formula as an identity of processes; its stochastic term is a local martingale
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
-- The product rule for two Itô processes driven by one Brownian motion
import MathFin.Probability.Brownian.Ito.ItoProductRule
-- Deterministic drift Riemann-convergence (α4 brick b-tail): ∑θ(tₖ)²·Δτ → ∫₀ᵀθ²ds
import MathFin.Probability.Brownian.Ito.DriftRiemannConvergence
-- Continuous adapted-θ Girsanov assembly (α4 (c)): convergence core toward
-- Btheta_isQBrownianMotion_adapted
import MathFin.Probability.Brownian.Girsanov.GirsanovAdaptedTheta
-- Rung 1 (bounded predictable θ Girsanov, Route B): marshal a SimpleProcess into single-partition
-- (s,c) form; generic simple-Doléans moment bounds; the predictable distributional Girsanov
-- theorem.
import MathFin.Probability.Brownian.SimpleProcessPartition
import MathFin.Probability.Brownian.Girsanov.GirsanovSimpleDoleansMoments
import MathFin.Probability.Brownian.Girsanov.GirsanovPredictableTheta
import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
import MathFin.Probability.Brownian.Ito.ItoFormulaCLM
-- Summit A′: time-dependent Itô formula in L² — TD Taylor remainder vanishes,
-- TD Riemann↔CLM bridge, and the assembly f(T,B_T) = f(0,B₀) + ∫f_x dB + ∫(f_t+½f_xx)ds
import MathFin.Probability.Brownian.Ito.ItoFormulaTDRemainder
import MathFin.Probability.Brownian.Ito.ItoIntegralRiemannBridgeTD
import MathFin.Probability.Brownian.Ito.ItoFormulaTD
import MathFin.Probability.Brownian.BrownianExpMoment
import MathFin.Probability.Brownian.Ito.ItoFormulaLocalized
import MathFin.Probability.Brownian.Ito.ItoFormulaItoProcess
import MathFin.Probability.Brownian.Ito.ItoFormulaGBM
import MathFin.Probability.Brownian.Ito.ItoDriftExpectation
-- The integrated Itô–drift identity for adapted coefficients along `X_t = c + ∫β + M`,
-- conditional on a hypothesized adapted, path-continuous version `M` of the Itô integral
-- (the library does not construct one for general δ)
import MathFin.Probability.Brownian.Ito.ItoDriftIncrementEnergy
import MathFin.Probability.Brownian.Ito.ItoDriftWeightedIsometry
import MathFin.Probability.Brownian.Ito.ItoDriftGapDecay
import MathFin.Probability.Brownian.Ito.ItoStepSumFourthMoment
import MathFin.Probability.Brownian.Ito.ItoDriftMomentBounds
import MathFin.Probability.Brownian.Ito.ItoDriftBlock
import MathFin.Probability.Brownian.Ito.ItoDriftQuadraticCorrections
import MathFin.Probability.Brownian.Ito.ItoDriftTaylorRemainder
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedDrift
-- The companion with no hypothesized M (for B with continuous paths): the same identity for
-- the constructed process, derived from ito_formula_adapted (centering + Fubini)
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedDriftConstructed
-- Cross-horizon consistency of the CLM Itô integral: one pinned `M` (`hMeq`) represents
-- the CLM integral at every horizon `τ ≤ T` (band-transfer kernel + freeze law)
import MathFin.Probability.Brownian.Ito.ItoIntegralCrossHorizon
import MathFin.Probability.Brownian.SDE.GyongyMimicry
-- Martingale representation, step 3: the Doléans exponential of a deterministic step
-- integrand is an Itô integral (time locality of `∫·dB` + unbounded `𝓕_a`-scaling)
import MathFin.Probability.Brownian.Ito.DoleansStepRepresentation
-- Martingale representation, step 4: the Wiener exponentials are total in `L²(𝓕ᴮ_T)`
-- (Abel summation + Laplace-transform uniqueness on `ℝⁿ` + Lévy's upward theorem)
import MathFin.Probability.Brownian.WienerExponentialTotality
-- Martingale representation, step 5: the Itô integral is onto the centered `𝓕ᴮ_T`-measurable
-- part of `L²(μ)` — terminal, submodule and process forms of the representation theorem
import MathFin.Probability.Brownian.MartingaleRepresentation
import MathFin.Probability.Brownian.Ito.ItoFormulaProcess
import MathFin.Probability.Brownian.ExitTime
import MathFin.Probability.Brownian.Ito.ItoFormulaCutoff
import MathFin.Probability.Brownian.Ito.ItoFormulaUnrestrictedLocMart
-- Phase 39: Itô structural drift formula + GBM log-drift (after Nagy 2026)
import MathFin.Probability.Brownian.Ito.ItoLemma
-- Time-dependent (2D) Itô formula + GBM-as-SDE-solution (genuine exp partials)
import MathFin.Probability.Brownian.Ito.ItoLemma2D
-- Shared change-of-measure helper: a positive normalised density gives an
-- equivalent probability measure (consumed by the one-period FTAP files)
import MathFin.Probability.Martingales.EquivMeasure
import MathFin.Probability.Martingales.TimeChange
-- OU generator on polynomials: the Hermite spectral layer of the OU/Vasicek family
import MathFin.Probability.Brownian.SDE.OUSpectral
-- Estimation: Gaussian variance-ratio KL, realised-variance noise bias, square-root bias
import MathFin.Probability.Laws.Estimation
-- Phase 13 additions:
-- Compound-Poisson aggregate-loss MGF: iid-sum MGF composed with the Poisson pgf
import MathFin.Probability.Jumps.CompoundPoissonMGF
import MathFin.Probability.Gaussian.GaussianPairLinearLaw
import MathFin.Probability.Gaussian.GaussianPartialMoments
import MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment
import MathFin.Probability.Brownian.Girsanov.WienerIntegralGirsanov
-- Weak uniqueness for the constant-coefficient integrated weak forward equation, via
-- the characteristic-function/Groenwall method
import MathFin.Probability.Gaussian.WeakForwardUniqueness
-- Stochastic Fubini for a continuous linear L²-integral, and its Itô and Wiener instances
import MathFin.Probability.Brownian.Ito.StochasticFubini
import MathFin.Probability.Brownian.Ito.StochasticFubiniIto

-- Contracts
import MathFin.Contracts.Instruments.CallPayoff
-- Contracts tower: a reified payoff language, model-agnostic until priced
-- (Bilokon, "The Contract Is Not the Model", 9 August 2026)
import MathFin.Contracts.Core
import MathFin.Contracts.Adapted
import MathFin.Contracts.Instruments.Options
import MathFin.Contracts.Instruments.FixedIncome
import MathFin.Contracts.Instruments.Credit

-- Pricing
-- Continuous-time first FTAP: discounted GBM price is a Q-martingale (Wald exponential)
import MathFin.Pricing.FTAP.ContinuousFTAP
-- Model-agnostic continuous-market vocabulary: IsEMM on a process, simple strategies, no-arbitrage
import MathFin.Pricing.ContinuousMarket
import MathFin.Pricing.Girsanov
import MathFin.Pricing.Numeraire
-- The T-forward measure: the zero-coupon bond as numéraire (change-of-numéraire instance)
import MathFin.Pricing.ForwardMeasure
import MathFin.Pricing.NoArbitrageCore
import MathFin.Pricing.FTAP.FTAP
import MathFin.Pricing.ReplicationPricing
-- Phase 13 additions:
import MathFin.Pricing.StatePrices
import MathFin.Pricing.ConvexPricingFunctional
import MathFin.Pricing.Duality.ConvexSeparation
-- Phase 1 (convex-duality unification): cone-separation root generalizing
-- ConvexSeparation from a subspace (two-sided `= 0`) to a closed convex cone (`≤ 0`)
import MathFin.Pricing.Duality.ConvexDuality
-- Martingale representation, step 6: its finance reading — replication, superreplication
-- duality, and uniqueness of the pricing measure on the Brownian filtration
import MathFin.Pricing.MarketCompleteness
import MathFin.Pricing.MarketCompletenessInPrice
-- The price with a drift, S = S₀ + ∫b ds + (σ●B), and the integral against it
import MathFin.Pricing.PricePathDrift
import MathFin.Pricing.PricingMeasureL2Density
-- Phase 37: FTAP both directions, two-state market (adapted from Nagy 2026)
import MathFin.Pricing.FTAP.FTAPTwoState
-- Phase 53: Pricing kernel from two-state FTAP (state-prices composition)
import MathFin.Pricing.PricingKernel
-- Phase 42: Multi-state FTAP backward (hypothesis-form, forward direction proved)
import MathFin.Pricing.FTAP.FTAPMultiState
import MathFin.Pricing.FTAP.FTAPDiscrete
import MathFin.Pricing.FTAP.FTAPComplete
-- General-Ω one-period FTAP (Föllmer–Schied §1.2 / one-period DMW, scalar)
import MathFin.Pricing.FTAP.FTAPOnePeriod
-- General-Ω one-period FTAP, d assets (Esscher minimal-divergence EMM, full — finite-dim market)
import MathFin.Pricing.FTAP.FTAPOnePeriodVector
-- Multi-period FTAP on a general space: no arbitrage is local, one-period densities paste, and
-- the Dalang–Morton–Willinger theorem reduces to the conditional one-period FTAP
import MathFin.Pricing.FTAP.NoArbitrageLocal
import MathFin.Pricing.FTAP.DensityPasting
import MathFin.Pricing.FTAP.DalangMortonWillinger
-- Phase 20: first-principles core derivations
import MathFin.Pricing.NoArbitrageDerivations
-- Phase 1 (convex-duality unification): fundamental superhedging bound — every EMM prices a claim
-- at most its super-replication cost (the pricing-side companion of the coherent-risk
-- representation)
import MathFin.Pricing.SuperhedgingDuality
import MathFin.Pricing.Value
import MathFin.Pricing.Market
import MathFin.Pricing.Parity
import MathFin.Pricing.DiscreteMarket
-- The law of a Wiener-represented rate under the forward measure of a Wiener-represented account
import MathFin.Pricing.WienerIntegralForwardMeasure

-- Models
import MathFin.Models.BlackScholes.GaussianGirsanov
import MathFin.Models.Forwards.TriangleArbitrage
import MathFin.Models.ModelFree.CarrMadan
-- Phase 30 (Bridge A): BSCallHyp / BachelierHyp from IsPreBrownian
import MathFin.Models.BlackScholes.BSCallHypFromBrownian
-- Phase 31: Pricing entry points from IsPreBrownian (composite corollaries)
import MathFin.Models.BlackScholes.PricingFromBrownian
-- Phase 32: Variance-swap log-price squared-increment from BrownianQuadraticVariation
import MathFin.Models.ModelFree.VarianceSwapFromQV
-- Phase 33: Variance-swap equipartition sum from BrownianQuadraticVariation
import MathFin.Models.ModelFree.VarianceSwapEquipartition
-- Phase 34: Variance-swap QV limit theorem (realised-variance → σ²T as n → ∞)
import MathFin.Models.ModelFree.VarianceSwapLimit
-- Variance-swap drift immunity: realized variance → σ²T in L² for ANY drift
-- (consumes ItoProcessQV; strengthens phase 34 from expectation-level to L²)
import MathFin.Models.ModelFree.VarianceSwapDriftImmunity
import MathFin.Models.Rates.HullWhiteCalibration
import MathFin.Models.Rates.HullWhiteBondPriceAt
import MathFin.Models.BlackScholes.MonteCarloPricer
-- Phase 45: Variance swap log-payoff and QV-limit form equivalence
import MathFin.Models.ModelFree.VarianceSwapEquivalence
import MathFin.Models.BlackScholes.Call
import MathFin.Models.BlackScholes.Put
import MathFin.Models.BlackScholes.PDE
import MathFin.Models.BlackScholes.PutGreeks
import MathFin.Models.BlackScholes.Digital
import MathFin.Models.BlackScholes.DigitalGreeks
import MathFin.Models.BlackScholes.Dividends
import MathFin.Models.BlackScholes.DividendsGreeks
import MathFin.Models.BlackScholes.Forward
import MathFin.Models.BlackScholes.HigherGreeks
import MathFin.Models.BlackScholes.StrikeGreeks
-- Local-vol skew of a tilted smile surface via Dupire's ratio; the rule of two
import MathFin.Models.LocalVol.ForwardSmile
import MathFin.Models.BlackScholes.PutStrikeConvexity
import MathFin.Models.BlackScholes.AsianInequality
-- Geometric-average Asian: two-date log-driver is Gaussian with the covariance-sum variance
import MathFin.Models.BlackScholes.AsianGeometric
-- Geometric-average Asian: n-date driver law + closed-form price via effective-BS reduction
import MathFin.Models.BlackScholes.AsianGeometricN
import MathFin.Models.BlackScholes.ImpliedVolatility
-- SABR (Hagan-Kumar-Lesniewski-Woodward 2002) lognormal implied-vol asymptotic
-- approximation: eq. 2.17 -> eq. 2.18 as K -> f, backbone law, ATM Black-76 price
import MathFin.Models.StochVol.SABRImpliedVol
-- Le Floc'h-Kennedy SABR building blocks: y(k) -> -log(F/k) as beta -> 1,
-- Dint -> -y/alpha as nu -> 0 (the removable singularities of the closed forms)
import MathFin.Models.StochVol.SABRFlochKennedyLimits
import MathFin.Models.BlackScholes.LognormalMoments
import MathFin.Models.ModelFree.VarianceSwap
-- Merton (1976) jump-diffusion: Poisson-mixture price, compensation
-- identity, parity (consumes Probability.Jumps.PoissonPgf + Call/Put formulas)
import MathFin.Models.Jumps.MertonJumpDiffusion
-- Merton dominance (jump risk is never free: vega + gamma/Jensen channels)
-- and the classic Λ′ = Λ(1+k) display (rate-shift identity)
import MathFin.Models.Jumps.MertonDominance
import MathFin.Models.Jumps.MertonClassicDisplay
-- Merton's model derived: the jump-diffusion terminal price (Gaussian diffusion,
-- Poisson count, i.i.d. lognormal jumps) prices to the Poisson mixture
-- Merton Greeks: delta, gamma, vega as Poisson mixtures of Black–Scholes Greeks
import MathFin.Models.Jumps.MertonGreeks
-- Merton's strike derivatives: the digital series and the density series (Poisson mixtures of
-- Black–Scholes digitals and of lognormal density formulas), and Merton's Breeden–Litzenberger
import MathFin.Models.Jumps.MertonStrikeGreeks
-- Jump-diffusions with an arbitrary jump law: the mixing formula, the
-- compound-Poisson compensator, and Merton's formula for a general jump law
import MathFin.Models.Jumps.JumpDiffusionMixing
-- Compensated jumps lift the Black–Scholes implied volatility strictly above σ
import MathFin.Models.Jumps.JumpImpliedVol
-- The Ju-Zhong quadratic approximation's r -> 0 limit: the pre-fix and post-fix
-- closed forms agree for every r != 0, and agree in the limit as r -> 0 too
import MathFin.Models.BlackScholes.American.JuZhongZeroRateLimit
-- The canonical jump-diffusion model: the hypotheses are satisfiable for every
-- expected jump count and jump law, and the call depends only on these two
import MathFin.Models.Jumps.JumpDiffusionCanonical
-- The jump-diffusion price process: discounted, a martingale exactly at the compensated drift
import MathFin.Models.Jumps.JumpDiffusionProcess
-- Option prices at intermediate dates: a function of the current price and the
-- remaining maturity
import MathFin.Models.Jumps.JumpDiffusionOptionPrices
import MathFin.Models.BlackScholes.GaussianSmoothing
import MathFin.Models.Jumps.JumpDiffusionMerton
import MathFin.Models.Jumps.JumpDiffusionBrownian
-- Scaling a jump-diffusion; the exponential martingales e^{θX_t − κ(θ)t} for the Laplace
-- exponent κ (where the jump law has the moment of order θ); power claims at each date
import MathFin.Models.Jumps.JumpDiffusionExponent
-- The Esscher transform of a jump-diffusion log-return law: again a jump-diffusion law when the
-- jump law's moment-generating function is finite near θ; Esscher pricing is Merton's formula for
-- the tilted jumps, and Black–Scholes without jumps
import MathFin.Models.Jumps.JumpDiffusionEsscher
-- The law at one date determines the drift, σ² and the Lévy measure off 0 (Lévy–Khintchine
-- uniqueness for jump laws whose moment-generating function is finite near 0)
import MathFin.Models.Jumps.JumpDiffusionIdentifiability
-- Incompleteness at one date: for σ ≠ 0 the Esscher law and the Merton measure are both
-- equivalent to the physical law (with any drift) and compensated, yet price some call
-- differently when the jumps are nontrivial
import MathFin.Models.Jumps.JumpDiffusionIncompleteness
-- The log-return law is a Gaussian mixture; with σ ≠ 0 and τ > 0 it has a continuous density, so
-- no atoms, and with σ = 0 it has an atom at bτ; the tail of a law with a density is
-- differentiable where the density is continuous; the law of the price Seʸ has the density
-- f(log(K/S))/K
import MathFin.Models.Jumps.JumpDiffusionDensity
-- Digital options and Breeden–Litzenberger with jumps: for σ ≠ 0 and τ > 0 the strike derivative
-- of the call price is minus the digital price and the second one is the discounted density of the
-- price; without jumps, at the drift r − σ²/2, these are e^{−rτ}Φ(d₂) and lognormalTerminalPDF;
-- with Gaussian log-jumps, Merton's digital and density series; with σ = 0 the call price has a
-- kink at the strike Se^{bτ}; lognormalTerminalPDF and mertonTerminalPDF as densities of the price
import MathFin.Models.Jumps.JumpDiffusionDigital
-- Strict convexity in the strike: the call price is convex under any law, and strictly convex
-- where the law charges every interval; with σ ≠ 0 and τ > 0 the jump-diffusion density is
-- positive, so with S > 0 and a finite forward the call price is strictly convex on (0, ∞) for
-- any jump law, and so are the Black–Scholes price and Merton's series
import MathFin.Models.Jumps.JumpDiffusionStrikeConvexity
-- The mean, variance and second moment of the jump-diffusion log-return, from the first two
-- derivatives at 0 of its cumulant generating function κ(θ)τ
import MathFin.Models.Jumps.JumpDiffusionMoments
-- Variance swaps with jumps: at the compensated drift the log contract has expected payoff
-- σ² + 2ΛE[eᴶ − 1 − J], which differs from the variance per unit time σ² + ΛE[J²] by the jump
-- bias 2ΛE[eᴶ − 1 − J − J²/2], ≤ 0 for jumps ≤ 0 and < 0 if moreover Λ > 0 and the jumps are
-- negative with positive probability. On the process, under a measure that makes the discounted
-- price a martingale, the log contract minus the expected realized variance per unit time along
-- n + 1 equal steps of [0, T] is the jump bias less (b + ΛE[J])²T/(n + 1), at every n, so it tends
-- to the jump bias; Black–Scholes (Brownian motion) is a corollary on the process, and Merton's
-- Gaussian jumps a corollary at the level of the law (log contract against Var[Y]/τ)
import MathFin.Models.Jumps.JumpDiffusionVarianceSwap
import MathFin.Models.Bachelier.Bachelier
import MathFin.Models.Bachelier.BachelierGreeks
import MathFin.Models.BlackScholes.Chooser
import MathFin.Models.ModelFree.Spreads
-- Call spreads tend to the digital, so call prices at every strike determine the law (the first-
-- order Breeden–Litzenberger, for any law with a finite mean); the call price is differentiable
-- in the strike exactly where the law has no atom, and there its derivative is minus the digital
import MathFin.Models.ModelFree.CallSpreadDigital
import MathFin.Models.BlackScholes.DeltaHedge
import MathFin.Models.LocalVol.Dupire
-- The Heston 2D affine transform at the generator/PDE level: the rho-shifted Riccati
-- closed forms, the pricing PDE, and the gated real-moment expectation
import MathFin.Models.StochVol.Heston
-- The Heston transform at vanishing vol-of-vol: the Black-Scholes moment with the integrated
-- deterministic variance
import MathFin.Models.StochVol.HestonSmallVolOfVol
import MathFin.Models.BlackScholes.Lookback
import MathFin.Models.BlackScholes.BarrierParity
import MathFin.Models.BlackScholes.BinaryBarrierOption
-- Also consumes the bivariate normal CDF (Probability/Gaussian/BivariateNormalCDF),
-- like Stulz/Heynen-Kat below
import MathFin.Models.BlackScholes.PartialTimeBarrierOption
import MathFin.Models.BlackScholes.PowerOption
import MathFin.Models.ModelFree.BreedenLitzenberger
import MathFin.Models.BlackScholes.BisectionIV
-- Structural / principle modules:
import MathFin.Models.BlackScholes.StrikeConvexity
import MathFin.Models.BlackScholes.SpotConvexity
import MathFin.Models.ModelFree.PriceBounds
import MathFin.Models.ModelFree.CallPriceFunction
-- Phase 13 additions:
-- Quanto correction derived from a joint-Gaussian FX model (Girsanov-grounded)
import MathFin.Models.BlackScholes.QuantoGrounding
import MathFin.Models.BlackScholes.NewtonConvergence
import MathFin.Models.Forwards.Black76
import MathFin.Models.Forwards.Black76Greeks
import MathFin.Models.Forwards.SchwartzOneFactor
-- Phase 13 additions:
import MathFin.Models.Binomial.Model
import MathFin.Models.Binomial.American
import MathFin.Models.Binomial.CRRConvergence
import MathFin.Models.Binomial.DriftLimit
import MathFin.Models.Binomial.Bermudan
import MathFin.Models.Binomial.MartingaleRepresentation
import MathFin.Models.Binomial.EuropeanReplication
import MathFin.Models.Binomial.FlipPaths
-- Phase 13 additions:
import MathFin.Models.Binomial.Girsanov
import MathFin.Models.Binomial.SecondFTAP
-- Phase 14: real new theorems
import MathFin.Models.Binomial.MertonAmericanCallTree
import MathFin.Models.Binomial.ReplicatingUniqueness
import MathFin.Models.BlackScholes.GreekSigns
-- Phase 16: reflection-principle algebraic core (André 1887)
import MathFin.Models.Binomial.PathReflection
-- Barrier-option counting: reflection card identity + maximal-distribution (running-max law)
import MathFin.Models.Binomial.BarrierReflection
-- Phase 19: Snell envelope characterization of americanPrice
import MathFin.Models.Binomial.SnellEnvelope
-- Phase 43: Binomial up-probability as two-state FTAP EMM
import MathFin.Models.Binomial.BinomialFromFTAP
-- Phase 44: CRR binomial scheme as discrete-Itô process (drift + QV limits)
import MathFin.Models.Binomial.CRRDiscreteIto
-- CRR → BS characteristic-function convergence (the distributional CLT heart)
import MathFin.Models.Binomial.CRRCharFun
-- CRR → BS in literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (Φ-landing corollary)
import MathFin.Models.Binomial.CRRClosedForm
import MathFin.Models.BlackScholes.RiskNeutralProbabilities
-- Phase 22: delta as stock-numeraire probability (Φ(d_1) = Q^(S)(S_T > K))
import MathFin.Models.BlackScholes.StockNumeraire
-- Phase 24: powered call closed form via reduction to BS-call (effective spot/vol)
import MathFin.Models.BlackScholes.PowerCall
-- BS-family Garman normal form (`V = A·Φ(d_1) − K·DF·Φ(d_2)`): the single
-- numéraire-parameterised template consumed by ExchangeOption, Black-76, KMVMerton
import MathFin.Models.BlackScholes.GarmanNormalForm
-- Basket option pricing via moment-matching to a single lognormal (approximation)
import MathFin.Models.BlackScholes.BasketMomentMatching
import MathFin.Models.BlackScholes.ExchangeOption
-- Two-asset closed forms (Stulz rainbow, Heynen–Kat barrier) on the bivariate normal CDF
import MathFin.Models.BlackScholes.StulzTwoAssetRainbow
import MathFin.Models.BlackScholes.HeynenKatTwoAssetBarrier
-- Margrabe BSCallHyp grounding from a joint two-GBM gaussian model (leap-3 closure)
import MathFin.Models.BlackScholes.MargrabeGrounding
-- Kirk's (1995) approximation for spread options (K ≠ 0), a Garman-normal-form instance
import MathFin.Models.BlackScholes.KirkSpreadApproximation
-- Phase 25: chooser option as call + put portfolio via PCP at chooser date
import MathFin.Models.BlackScholes.ChooserComposition
-- Phase 46: BS PDE derived from Itô drift + no-arbitrage
import MathFin.Models.BlackScholes.PDEFromIto
-- Feynman–Kac → BS PDE keystone (step 2: the FK price representation)
import MathFin.Models.BlackScholes.PDEFromFeynmanKac
-- Phase 40: Itô lemma L¹-expectation form applied to GBM log (mean + variance)
import MathFin.Models.BlackScholes.GBMLogMoments
import MathFin.Models.Rates.ZCB
import MathFin.Models.Rates.CouponBonds
import MathFin.Models.Rates.Immunization
import MathFin.Models.Rates.ConvexityImmunization
import MathFin.Models.Rates.YieldCurve
import MathFin.Models.Rates.Bootstrapping
import MathFin.Models.Credit.Credit
-- First-to-default: basket intensity = Σ single-name intensities
-- (bridges Probability.Laws.ExpMin into the Credit vocabulary)
import MathFin.Models.Credit.FirstToDefault
import MathFin.Models.Rates.MacaulayModified
import MathFin.Models.Credit.HazardCurve
import MathFin.Models.Rates.ForwardRate
import MathFin.Models.Rates.TimingAdjustment
import MathFin.Models.Rates.Vasicek
-- Phase 13 additions:
import MathFin.Models.Credit.KMVMerton
-- Phase 21: first-principles duration-as-price-sensitivity
import MathFin.Models.Rates.DurationSensitivity
-- Phase 22: first-principles convexity-as-second-derivative
import MathFin.Models.Rates.ConvexitySensitivity
-- Phase 27: KMV-Merton structural derivation (probabilistic content of `kmvPD`)
import MathFin.Models.Credit.KMVMertonStructural
-- Phase 28: CDS fair spread under time-varying hazard (cash-flow balance)
import MathFin.Models.Credit.CDSTimeVarying
import MathFin.Models.Credit.Cox
-- Default-time density of a deterministic hazard curve (law of τ as Lebesgue density)
import MathFin.Models.Credit.DefaultDensity
-- CVA under exposure independent of default (Fubini reduction; Gaussian expected exposure in
-- closed form)
import MathFin.Models.Credit.CVA
-- DVA from CVA: negate the exposure, swap in the bank's own default time; DVA as the integral
-- of the expected negative exposure
import MathFin.Models.Credit.DVA
-- Phase 41: Vasicek SDE closed-form (full SDE, mean + variance)
import MathFin.Models.Rates.VasicekSDE
-- Itô→pricing bridge: Vasicek terminal law derived (Wiener integral is Gaussian)
import MathFin.Models.Rates.VasicekSDEGaussian
-- Sum of two squared OU fluctuations: mean θ(1 − e^{−kt}) + v₀e^{−kt}, the borderline CIR mean
import MathFin.Models.Rates.CIRSquaredOU
-- Vasicek zero-coupon bond price: the affine term structure (Gaussian Laplace transform)
import MathFin.Models.Rates.VasicekBondPrice
-- Vasicek bond price at t > 0: the conditional discount factor is affine in the short rate
import MathFin.Models.Rates.VasicekBondPriceAt
-- Vasicek real-world vs. risk-neutral terminal mean; an Esscher tilt reproducing the
-- risk-neutral terminal law
import MathFin.Models.Rates.VasicekMarketPriceOfRisk
-- Vasicek bond price as κ → 0⁺: the three-term cancellation limit to the driftless model
import MathFin.Models.Rates.VasicekZeroMeanReversionLimit
-- CIR loadings: B solves the Riccati equation, A solves A' = −κθB
import MathFin.Models.Rates.CIRRiccati
-- The Black–Scholes forward price under the T-forward measure
import MathFin.Models.Rates.ForwardMeasure
-- Inflation is FX: the zero-coupon inflation swap and the YoY convexity
import MathFin.Models.Rates.Inflation
-- ABCD instantaneous volatility: closed-form integrated variance over a window
import MathFin.Models.Rates.ABCDVolatility
-- GSR (Gaussian short rate): two-piece piecewise-constant-volatility bond price
import MathFin.Models.Rates.GSRPiecewiseVol
import MathFin.Models.Rates.GSRBondPriceAt
-- LSV calibration: the leverage-posterior core (L²·E[v | S = K] = σ_loc²)
import MathFin.Models.StochVol.LSVLeverage
-- Upstream (Degenne BrownianMotion) modules consumed ONLY by benchmark
-- wrappers, imported here so `lake build` puts them in the build graph —
-- nothing else in MathFin/ imports them, and a snippet import of an unbuilt
-- module fails with a silently-empty environment (found 2026-06-05 via
-- cm-thm-4.3.7; its sibling cm-thm-4.3.9 works only because
-- Probability/Martingales/LpContinuousMartingaleConvergence imports Degenne's DoobLp).
import MathFin.Models.Rates.InterestRateSwap
import MathFin.Models.Rates.CMS
import MathFin.Models.Rates.FRA
import MathFin.Models.Rates.DeterministicCurve
import MathFin.Models.Rates.NelsonSiegelSvensson
import MathFin.Models.BlackScholes.BlackScholes
import MathFin.Models.BlackScholes.BlackScholesExchange
import MathFin.Models.BlackScholes.BlackScholesAsian
import MathFin.Models.BlackScholes.BlackScholesSDE
import MathFin.Models.BlackScholes.BlackScholesChooser
import MathFin.Models.BlackScholes.BlackScholesHedge
import MathFin.Models.BlackScholes.BlackScholesPhysical
-- The Black–Scholes delta hedge is self-financing: the product rule with the factor e^{rt}
import MathFin.Models.BlackScholes.BlackScholesSelfFinancing
import MathFin.Models.Binomial.Binomial
import MathFin.Models.Binomial.BinomialCompleteMarket
import MathFin.Models.Binomial.BinomialLimit
import MathFin.Models.Binomial.Market
import MathFin.Models.Rates.Caplet
import MathFin.Models.Rates.CMSContract
import MathFin.Models.Rates.ShortRate
import MathFin.Models.Rates.VasicekBond
import MathFin.Models.Rates.HullWhiteBond
import MathFin.Models.Rates.GSRBond
import MathFin.Models.Rates.Jamshidian
import MathFin.Models.Credit.DefaultTime
import MathFin.Models.Credit.DefaultTimeMesh
-- Continuous-time American put option exercise-boundary geometry
import MathFin.Models.BlackScholes.American.Stopping.PhysicalBoundaryConvexity
import MathFin.Models.BlackScholes.American.Stopping.PlanePartial
import MathFin.Models.BlackScholes.American.Stopping.AEHorizonValue
import MathFin.Models.BlackScholes.American.Stopping.AugmentedValue
import MathFin.Models.BlackScholes.American.Stopping.LocalPriceIto
-- The American put exercise boundary tends to the strike at expiry
import MathFin.Models.BlackScholes.American.Stopping.ActualBoundaryExpiryLimit
-- The Andersen-Lake-Offengenden QD+ fixed-point quadrature integrand's endpoint
-- limits, and that differentiability of the boundary cannot be weakened to continuity
import MathFin.Models.BlackScholes.American.AmericanQDPlusLimits
-- The SVI no-butterfly certificate (Robert Martin, #174)
import MathFin.Models.ModelFree.SVI.Admissibility
import MathFin.Models.ModelFree.SVI.Assembly
import MathFin.Models.ModelFree.SVI.AssociatedTrace
import MathFin.Models.ModelFree.SVI.BlackScholesBridge
import MathFin.Models.ModelFree.SVI.BlackSmile
import MathFin.Models.ModelFree.SVI.CallConvexity
import MathFin.Models.ModelFree.SVI.ClearedSignature
import MathFin.Models.ModelFree.SVI.Companion
import MathFin.Models.ModelFree.SVI.ConvexKink
import MathFin.Models.ModelFree.SVI.CriticalPoints
import MathFin.Models.ModelFree.SVI.DegreeProgram
import MathFin.Models.ModelFree.SVI.Denominators
import MathFin.Models.ModelFree.SVI.Derivatives
import MathFin.Models.ModelFree.SVI.DomainFormula
import MathFin.Models.ModelFree.SVI.ExtendedFormula
import MathFin.Models.ModelFree.SVI.FiniteCertificate
import MathFin.Models.ModelFree.SVI.HermiteIdentity
import MathFin.Models.ModelFree.SVI.ImaginaryTraceSignature
import MathFin.Models.ModelFree.SVI.Matrices
import MathFin.Models.ModelFree.SVI.MatrixCertificate
import MathFin.Models.ModelFree.SVI.MatrixSignature
import MathFin.Models.ModelFree.SVI.NilpotentSquareRoot
import MathFin.Models.ModelFree.SVI.ParameterPolynomials
import MathFin.Models.ModelFree.SVI.Polynomial
import MathFin.Models.ModelFree.SVI.PolynomialCertificate
import MathFin.Models.ModelFree.SVI.ProductSignature
import MathFin.Models.ModelFree.SVI.QuadraticRay
import MathFin.Models.ModelFree.SVI.QuadraticRootSignature
import MathFin.Models.ModelFree.SVI.QuotientProduct
import MathFin.Models.ModelFree.SVI.RankOneSignature
import MathFin.Models.ModelFree.SVI.RealIrreducibles
import MathFin.Models.ModelFree.SVI.RealRootSignature
import MathFin.Models.ModelFree.SVI.RealRootTrace
import MathFin.Models.ModelFree.SVI.Reduction
import MathFin.Models.ModelFree.SVI.SigmaZeroCertificate
import MathFin.Models.ModelFree.SVI.SigmaZeroConvexity
import MathFin.Models.ModelFree.SVI.SigmaZeroDerivatives
import MathFin.Models.ModelFree.SVI.SignFormula
import MathFin.Models.ModelFree.SVI.SignVariations
import MathFin.Models.ModelFree.SVI.SignatureProgram
import MathFin.Models.ModelFree.SVI.TraceForm
import MathFin.Models.ModelFree.SVI.TraceSignature
-- The SVI tail condition d₊ → −∞ iff b(1+ρ) < 2, and the butterfly-free sign formula
import MathFin.Models.ModelFree.SVI.TailCondition
-- Calendar-spread arbitrage (Gatheral–Jacquier Lemma 2.1) and its raw-SVI form
import MathFin.Models.ModelFree.CalendarArbitrage
-- Fisher/Sraffa own rate: Sraffa's implied own rate from spot, forward and financing rate
import MathFin.Models.Forwards.FisherSraffaOwnRate
-- Theory of storage: convenience yield and the kink point of the storage price curve
import MathFin.Models.Forwards.TheoryOfStorage
-- AR(1) <-> Ornstein-Uhlenbeck parameter inversion for commodity calibration
import MathFin.Models.Forwards.AR1OUCalibration
import MathFin.Models.Binomial.PathMeasure
import MathFin.Models.Binomial.MultiPeriodFTAP
import MathFin.Models.Jumps.JumpDiffusionThinning
import MathFin.Models.Rates.ABCDBlack76
import MathFin.Models.BlackScholes.American.AmericanPutEuropeanBound
import MathFin.Models.Rates.OUHermiteVasicek
import MathFin.Models.Rates.AffineTermStructurePDE
import MathFin.Models.Rates.PeriodicCompounding
import MathFin.Models.Rates.VasicekYieldNelsonSiegel
import MathFin.Models.StochVol.LSVPosteriorConditionalExpectation
-- Clean/dirty price and accrued interest; clean price continuous across a coupon date
import MathFin.Models.Rates.CleanPriceAccrued
-- Bond forward price derived from forward_price_from_no_arbitrage
import MathFin.Models.Rates.BondForward
-- Covered and uncovered interest parity, from no-arbitrage and the Garman–Kohlhagen measure
import MathFin.Models.Forwards.FxForwardParity
-- Loan amortization: bullet, equal-principal, and level-payment against annuityValue
import MathFin.Models.Rates.LoanAmortization
-- Key-rate partials sum to the parallel-shift derivative; on a flat curve, to dP/dy
import MathFin.Models.Rates.KeyRateDuration
-- The Heath–Jarrow–Morton model bundle: forward curve, bond, short rate, bank account
import MathFin.Models.Rates.HJM
-- Fixed cash flows in the HJM model: the discount factor, and pricing off the initial bond curve
import MathFin.Models.Rates.HJMBond

-- Risk
import MathFin.Risk.Gaussian
import MathFin.Risk.CoherentAxioms
import MathFin.Risk.Additivity
import MathFin.Risk.RockafellarUryasev
import MathFin.Risk.Spectral
import MathFin.Risk.Concentration
-- Phase 21: first-principles coherent-axiom derivation from concave utility
import MathFin.Risk.UtilityDerivation
-- The one coherence structure: the four ADEH axioms for losses, ρ(0) = 0, convexity, and (finite
-- state) pointwise monotonicity and continuity
import MathFin.Risk.Coherent
-- The positions convention of the ADEH paper is the loss convention at L ↦ ρ(−L)
import MathFin.Risk.PositionsConvention
-- Phase 1 (convex-duality unification): coherent-risk ADEH representation — acceptance cone
-- separation giving the representing probability measures (risk-side Hahn–Banach)
import MathFin.Risk.AcceptanceSet
-- Phase 1 (convex-duality unification): worst-case loss — the most conservative coherent risk
-- measure, concrete instance of the ADEH representation (sup over the entire probability simplex)
import MathFin.Risk.WorstCaseRisk
-- Value-at-risk and expected shortfall of a general loss (any law, atoms included), and the
-- Gaussian closed forms identified as the VaR of the law at z = Φ⁻¹(α)
import MathFin.Risk.ValueAtRisk
import MathFin.Risk.GaussianValueAtRisk
-- Expected negative exposure, potential future exposure (the VaR of V⁺) and netting
-- subadditivity on the CVA expected-exposure substrate; collateralized exposure under a
-- Brownian-driven process, the collateral the same process a lag earlier
import MathFin.Risk.ExposureMeasures
import MathFin.Risk.CollateralizedExposureBrownian
-- Expected shortfall: Rockafellar–Uryasev for every law, coherence, dual representation; the
-- Gaussian ES closed form; VaR by bisection; VaR superadditivity; closed forms and tail ratios;
-- VaR and ES of the Student-t law (McNeil–Frey–Embrechts closed forms); elicitability
-- (VaR elicitable, ES not); Bernoulli mixtures and the Basel IRB limit theorem
import MathFin.Risk.ExpectedShortfall
import MathFin.Risk.CompoundPoissonCVaR
import MathFin.Risk.GaussianExpectedShortfall
import MathFin.Risk.ValueAtRiskBisection
import MathFin.Risk.VaRSuperadditivity
import MathFin.Risk.DiscreteVaR
import MathFin.Risk.RiskClosedForms
import MathFin.Risk.StudentTValueAtRisk
import MathFin.Risk.Elicitability
import MathFin.Risk.JointElicitability
import MathFin.Risk.Expectile
import MathFin.Risk.Credit.BernoulliMixture
import MathFin.Risk.Credit.CreditMetrics
import MathFin.Risk.Credit.VasicekIRB
-- LHP tranche expected loss: the Vasicek (2002) stop-loss closed form and the finite-pool limit
import MathFin.Risk.Credit.TrancheLoss
import MathFin.Risk.SACCRExposure
-- Bridges (certified cross-domain unifications)
import MathFin.Risk.ConcentrationVariance
import MathFin.Risk.ContractRisk
import MathFin.Risk.GaussianRiskMarkowitz
import MathFin.Risk.EquicorrelationConcentration
import MathFin.Risk.SquareRootOfTime
-- Component VaR (the Euler decomposition of portfolio VaR) and the single-index covariance
-- structure with its large-N limit
import MathFin.Risk.ComponentVaR
import MathFin.Risk.Credit.CreditRiskPlus
import MathFin.Risk.Credit.OneFactorCopula

-- Choice
import MathFin.Choice.Portfolio.Markowitz
import MathFin.Choice.Portfolio.CovariancePSD
import MathFin.Choice.Portfolio.MarkowitzNAsset
import MathFin.Choice.Portfolio.CAPM
import MathFin.Choice.Portfolio.TwoFundSeparation
import MathFin.Choice.Portfolio.RiskParity
import MathFin.Choice.Portfolio.BlackLitterman
import MathFin.Choice.Portfolio.TangentPortfolio
-- Phase 13 additions:
-- Phase 21: first-principles Sharpe-FOC and CAPM-equilibrium derivations
import MathFin.Choice.Portfolio.SharpeFOCDerivation
import MathFin.Choice.Portfolio.CAPMEquilibrium
-- Phase 23: N-asset Markowitz Lagrangian FOC (forward direction)
import MathFin.Choice.Portfolio.MarkowitzLagrangian
-- Phase 26: N-asset risk parity from log-barrier Lagrangian FOC
import MathFin.Choice.Portfolio.RiskParityFOC
-- Phase 29: N-dim Black-Litterman posterior (matrix form)
import MathFin.Choice.Portfolio.BlackLittermanND
-- Convex QP KKT sufficiency/uniqueness and a feasible-ratio-test step bound
import MathFin.Choice.Portfolio.ConvexQPKKT
-- PSD-form Cauchy–Schwarz and the mean–standard-deviation tradeoff at a mean–variance KKT point
import MathFin.Choice.Portfolio.PosSemidefCauchySchwarz
import MathFin.Choice.Performance.Ratios
import MathFin.Choice.Performance.RatiosExtended
import MathFin.Choice.Performance.DownsideMetrics
import MathFin.Choice.Performance.RelativeDrawdown
import MathFin.Choice.Performance.Kelly
import MathFin.Choice.Performance.KellyNumeraire
import MathFin.Choice.Performance.FracDiffWeights
import MathFin.Choice.Performance.LabelUniqueness
import MathFin.Choice.Performance.BetSizeSigmoid
import MathFin.Choice.Performance.PurgedCV
-- The layer beneath UtilityDerivation, which takes the expected-utility form as given:
-- von Neumann-Morgenstern lotteries, the mixture algebra, affinity of expected utility in
-- the mixture, and the vNM axioms verified for the induced preference (the soundness half,
-- plus invariance of the preference under positive affine rescaling of the utility)
import MathFin.Choice.Utility.VonNeumannMorgenstern
-- QRM bridges: equicorrelation, Gaussian VaR/ES-optimal = Markowitz portfolios, the HHI
-- systematic floor, and the square-root-of-time rule for GBM losses
import MathFin.Choice.Portfolio.Equicorrelation
import MathFin.Choice.Portfolio.SingleIndexModel

-- Insurance
import MathFin.Insurance.StandardDeviationPrinciple
import MathFin.Insurance.SurvivalUnification
import MathFin.Insurance.Insurance
import MathFin.Insurance.Mortality
-- Survival model (re-formalized from Yosuke Ito's AFP `Survival_Model`, BSD, cited)
import MathFin.Insurance.SurvivalModel
import MathFin.Insurance.ActuarialInsurance

-- Markets
import MathFin.Markets.Execution.AlmgrenChriss
import MathFin.Markets.Microstructure.MarketMakingRiccati
import MathFin.Markets.Microstructure.MatrixMarketMakingRiccati
-- Phase 38: Constant-product AMM (adapted from Pusceddu-Bartoletti FMBC 2024)
import MathFin.Markets.DeFi.ConstantProductAMM
-- DeFi/AMM group: Uniswap v2/v3 mechanics (impermanent loss, TWAP, fee invariant, v3 real reserves)
import MathFin.Markets.DeFi.UniswapMechanics
-- DeFi/lending group: Aave kinked-rate + health factor, Compound cToken exchange rate
import MathFin.Markets.DeFi.Aave
import MathFin.Markets.DeFi.Compound
-- Dai stability fee and vault liquidation condition
import MathFin.Markets.DeFi.Dai
-- Execution: market microstructure — the Glosten-Milgrom adverse-selection
-- spread, plus a six-point model witnessing that its hypotheses are satisfiable
import MathFin.Markets.Microstructure.GlostenMilgrom
import MathFin.Markets.Microstructure.GlostenMilgromModel
import MathFin.Markets.Microstructure.RollSpread
import MathFin.Markets.DeFi.ConstantProductLPLognormal
import MathFin.Markets.DeFi.LiquidationAsStructuralDefault
import MathFin.Markets.DeFi.UniswapV3CoveredCallPrice
import MathFin.Markets.Microstructure.GlostenMilgromCondExp
