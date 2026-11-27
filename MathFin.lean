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
module

public import MathFin.Init

-- Probability
public import MathFin.Probability.Gaussian.StandardNormal
public import MathFin.Probability.Discrete.DoobDecomposition
public import MathFin.Probability.Discrete.SnellDoobDecomposition
public import MathFin.Probability.Discrete.SnellEnvelope
public import MathFin.Probability.Discrete.L2MartingaleConvergence
public import MathFin.Probability.Brownian.BrownianMarkov
-- Markov-chain path law derived from the pin's Ionescu–Tulcea trajectory
-- kernels (Saporito 1.1.2)
public import MathFin.Probability.Discrete.MarkovPathMeasure
public import MathFin.Probability.Laws.ErlangSum
-- Poisson-process theory: superposition, thinning, marginal-from-arrivals,
-- first-interarrival law (Saporito 3.3.5/3.3.6/3.3.9/3.3.10)
public import MathFin.Probability.Jumps.PoissonSuperposition
public import MathFin.Probability.Jumps.PoissonThinning
public import MathFin.Probability.Jumps.PoissonCounting
public import MathFin.Probability.Jumps.PoissonInterarrival
-- Poisson probability generating function E[x^N] = e^{r(x−1)} (absent from
-- Mathlib); the engine behind Merton-mixture compensation identities
public import MathFin.Probability.Jumps.PoissonPgf
-- CreditRisk+ sector pgf: Poisson default count mixed over a Gamma sector factor, as an
-- iterated integral
public import MathFin.Probability.Laws.GammaPoissonMixturePgf
-- The freezing lemma: E[g(X, Y)] = ∫ x, E[g(x, Y)] d(law X) for independent X, Y
public import MathFin.Probability.Analysis.IdentDistribSum
public import MathFin.Probability.Dependence.IndepPast
public import MathFin.Probability.Analysis.IndepFreezing
-- Jensen's inequality through a supporting line (no closed domain needed)
public import MathFin.Probability.Analysis.AffineMinorant
-- The exponential martingale of a process with independent increments
public import MathFin.Probability.Jumps.ExpMartingaleIndepIncrements
public import MathFin.Probability.Jumps.PoissonRandomMeasure
public import MathFin.Probability.Jumps.PoissonCompensatedIsometryAdapted
public import MathFin.Probability.Jumps.PoissonCompensatedBilinear
public import MathFin.Probability.Jumps.PoissonCompensatedIntegralL2
public import MathFin.Probability.Jumps.PoissonCompensatedIntegralL2Dense
public import MathFin.Probability.Jumps.PoissonCompensatedSimpleIntegrand
public import MathFin.Probability.Jumps.PoissonCompensatedIntegralOperator
-- QV of an Itô process: drift contributes nothing (Saporito 7.4.5)
public import MathFin.Probability.Brownian.Ito.ItoProcessQV
public import MathFin.Probability.Gaussian.GaussianMoments
public import MathFin.Probability.Gaussian.BivariateGaussian
public import MathFin.Probability.Gaussian.BivariateNormalCDF
public import MathFin.Probability.Gaussian.GaussianCDFDeriv
-- The Esscher transform of a law on ℝ (Mathlib's `Measure.tilted`): tilted moments, a law with
-- every exponential moment is fixed by its MGF, and the Gaussian tilt N(m, v) ↦ N(m + θv, v)
public import MathFin.Probability.Laws.Esscher
public import MathFin.Probability.Laws.FiniteWeights
public import MathFin.Probability.Gaussian.FeynmanKacHeatEquation
public import MathFin.Probability.Brownian.BrownianMartingale
public import MathFin.Probability.Brownian.BrownianDoobMaximal
-- Bayes change-of-measure engine + Black–Scholes EMM via an explicit Girsanov density
public import MathFin.Probability.Martingales.CondExpCallJensen
public import MathFin.Probability.Martingales.ChangeOfMeasure
public import MathFin.Probability.Brownian.ExpMartingaleQBrownian
public import MathFin.Probability.Martingales.LevyQuadraticSums
public import MathFin.Probability.Martingales.LevyExpMartingale
public import MathFin.Probability.Brownian.ExpMartingaleBrownian
public import MathFin.Probability.Martingales.StoppedProcessPaths
public import MathFin.Probability.Martingales.BoundedLocalMartingale
public import MathFin.Probability.Brownian.LevyCharacterization
public import MathFin.Probability.Brownian.Girsanov.GirsanovConstantTheta
public import MathFin.Probability.Brownian.Girsanov.SimpleDoleansExponential
public import MathFin.Probability.Brownian.Girsanov.GirsanovSimpleTheta
public import MathFin.Probability.Brownian.BrownianQuadraticVariation
-- The uniform partition of [0, T] (and [s, t]): the one equipartition of the Itô stack
public import MathFin.Probability.Brownian.UnifPart
public import MathFin.Probability.Brownian.QuadraticVariationL2
public import MathFin.Probability.Laws.ExpMin
public import MathFin.Probability.Discrete.OptionalSamplingInequality
public import MathFin.Probability.Martingales.LpContinuousMartingaleConvergence
public import MathFin.Probability.Martingales.MartingaleSetIntegral
public import MathFin.Probability.Analysis.IndepIsometryKernel
public import MathFin.Probability.Discrete.MartingaleTransform
public import MathFin.Probability.Discrete.DoobLpMaximalInequality
public import MathFin.Probability.Analysis.ExtendOfNormIsometry
public import MathFin.Probability.Brownian.Wiener.WienerIntegralL2
public import MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian
-- Wiener integral of a step indicator is the increment (∫𝟙_{(s,t]} dB = B_t − B_s)
public import MathFin.Probability.Brownian.Wiener.WienerIntegralIndicator
public import MathFin.Probability.Brownian.Wiener.WienerIntegralIto
public import MathFin.Probability.Brownian.Wiener.WienerIntegralFiltration
-- Structural / principle modules:
public import MathFin.Probability.Gaussian.StandardGaussianMGF
public import MathFin.Probability.Analysis.ExponentialDiscount
public import MathFin.Probability.Analysis.Bisection
-- The quantile function (generalized inverse CDF): Galois connection, quantile transform,
-- probability integral transform, equivariance; and the standard normal quantile Φ⁻¹
public import MathFin.Probability.Laws.Quantile
public import MathFin.Probability.Gaussian.NormalQuantile
public import MathFin.Probability.Gaussian.NormalTail
-- The Student-t law: density in closed form, the ν = 1 Cauchy anchor, the tail first moment
public import MathFin.Probability.Laws.StudentT
-- QRM foundations: quantile convergence, copulas and Sklar's theorem, Hoeffding's covariance
-- identity, Marshall–Olkin common shocks, correlation fallacies, extreme value theory (GEV, GPD,
-- maxima of Poisson-many losses)
public import MathFin.Probability.Laws.QuantileConvergence
public import MathFin.Probability.Dependence.Copula
public import MathFin.Probability.Dependence.Sklar
public import MathFin.Probability.Dependence.CopulaFamilies
public import MathFin.Probability.Dependence.GaussianCopula
public import MathFin.Probability.Dependence.HoeffdingCovariance
public import MathFin.Probability.Dependence.MarshallOlkin
public import MathFin.Probability.Dependence.CorrelationFallacies
public import MathFin.Probability.Laws.ExtremeValue
public import MathFin.Probability.Laws.ConvexOrder
public import MathFin.Probability.Laws.GeneralizedPareto
public import MathFin.Probability.Jumps.PoissonMaxima
public import MathFin.Probability.Analysis.DerivOfDeriv
-- Phase 35: Discrete Itô formula (adapted from Nagy 2026, SSRN 6336503)
public import MathFin.Probability.Discrete.DiscreteIto
-- The adapted Itô isometry (increment-independence cornerstone)
public import MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
-- Continuous L²-adapted Itô integral (construction, anchored on Degenne SimpleProcess)
public import MathFin.Probability.Brownian.Ito.ItoIntegralL2
-- 𝓕ᴮ_T is the countable supremum of dyadic cylinder σ-algebras (path continuity)
public import MathFin.Probability.Brownian.BrownianCylinderGeneration
-- The Itô integral as a continuous linear isometry `Lp 2 trim_T → Lp 2 μ` on `[0,T]`
public import MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense
public import MathFin.Probability.Brownian.Ito.ItoIntegralCLM
public import MathFin.Probability.Analysis.LpMulIsometry
public import MathFin.Probability.Brownian.Girsanov.PredictableDensityGeneral
public import MathFin.Probability.Brownian.Ito.ItoIntegralAgainstMartingale
-- BrownianMotion's axiomatic characterisation, instantiated: the integral against M = φ●B is an
-- `IsStochasticIntegral` (Riemann–Stieltjes values, dominated convergence, uniqueness)
public import MathFin.Probability.Brownian.Ito.StochasticIntegralCharacterisation
-- The pointwise bracket: conditional Brownian kernels + single-band generators whose
-- integrals evaluate to explicit increments (the rung toward the conditional second moment)
public import MathFin.Probability.Martingales.BracketCompensator
public import MathFin.Probability.Martingales.PointwiseBracket
-- The unbounded-horizon `[0,∞)` Itô integral CLM `Lp 2 trim_full → Lp 2 μ` (Summit B / B2)
public import MathFin.Probability.Brownian.Ito.ItoIntegralL2Dense
-- Covariation of Itô integrals: the bilinear Itô isometry ⟪∫φdB,∫ψdB⟫=⟪φ,ψ⟫ (D1)
public import MathFin.Probability.Brownian.Ito.ItoIntegralCovariation
-- The elementary Itô integral as a process `t ↦ (V●B)_t`, with genuine `L²` content
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcess
-- The Itô integral process is an adapted L² martingale (Summit B / B1a)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessMartingale
-- The elementary Itô integral as a continuous local martingale (Summit B / B3)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingale
-- The general-integrand Itô integral as an L² martingale on [0,T] (Summit B / B1b)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
-- The deferred time-indexed Itô isometry E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds (B1b refinement)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessIsometry
-- Continuous modification of the general-integrand Itô process on [0,T] (the gate)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessContinuousModification
-- Predictability of the assembled Itô process (the SDE-existence keystone)
public import MathFin.Probability.Brownian.Ito.ItoProcessPredictable
-- Predictability of the assembled drift process (SDE-existence keystone II)
-- Cauchy–Schwarz on a finite measure (shared by the drift L² bound and SDE uniqueness)
public import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
public import MathFin.Probability.Analysis.StdSimplexProd
public import MathFin.Probability.Brownian.Ito.DriftProcessPredictable
-- σ-realization: a bounded adapted continuous process as an Itô-integrand L² class (α4 gap)
public import MathFin.Probability.Brownian.Ito.AdaptedProcessToLp
-- Bounded-in-L² ⟹ uniformly-integrable-in-L¹ (Chebyshev truncation; the α4 Vitali producer)
public import MathFin.Probability.Martingales.UnifIntegrableL2
-- The Picard map and its contraction estimate (SDE existence, #44)
public import MathFin.Probability.Brownian.SDE.SDEExistence
-- Pathwise SDE uniqueness via the L²-energy Grönwall argument (#19)
public import MathFin.Probability.Brownian.SDE.SDEUniqueness
-- The assembled drift's pathwise realization: convergence + coeFn = driftContinuousMod
-- (SDE-existence bridge)
public import MathFin.Probability.Brownian.Ito.DriftProcessModification
-- The strong solution as a pathwise process: slicing the Picard fixed point (pathwise SDE
-- existence)
public import MathFin.Probability.Brownian.SDE.SDEPathwise
-- The general-integrand Itô process as a continuous local martingale (null-augmented filtration)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleGeneral
-- The unbounded-horizon Itô process: the L² process, horizon consistency (the [0,∞) climb)
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessL2Inf
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessL2Infinite
-- The [0,∞) crown: the unbounded-horizon Itô integral as a continuous local martingale on ℝ≥0
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleInfinite
-- Pathwise discrete Itô identity for `f(x) = x²` (the squaring keystone)
public import MathFin.Probability.Brownian.Ito.ItoSquaringIdentity
-- Polynomial Itô remainders (x³, x⁴) + the pathwise discrete cubing identity
public import MathFin.Probability.Discrete.DiscreteItoPolynomial
-- Continuous-time L² Itô formula for `f(x) = x²`: `∑ B ΔB → ½(B_T² − B_0² − T)`
public import MathFin.Probability.Brownian.Ito.ItoFormulaSquaredL2
-- The Riemann-Itô sum `riemannσ`: the one left-endpoint sum every bridge below is a case of
public import MathFin.Probability.Brownian.Ito.ItoRiemannSum
-- Keystone: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` as a genuine `itoIntegralCLM_T` identity
-- (the continuous Itô integral's first real consumer)
public import MathFin.Probability.Brownian.Ito.ItoIntegralBrownian
-- `𝓕_a`-linearity: a bounded `𝓕_a`-measurable factor passes through `∫₀ᵀ · dB`
-- when the integrand lives on `(a,T]` (locality of the stochastic integral)
public import MathFin.Probability.Brownian.Ito.ItoIntegralLocality
-- Summit A: bounded-derivative continuous-time Itô formula in L² (CLM-identified)
public import MathFin.Probability.Brownian.WeightedQuadraticVariation
public import MathFin.Probability.Brownian.Ito.ItoFormulaRemainder
-- Riemann↔CLM bridge for a bounded adapted continuous integrand θ (α4 brick b): ∫θdB CLM
public import MathFin.Probability.Brownian.Ito.ItoIntegralRiemannBridgeAdapted
-- Step B1 of the adapted-coefficient Itô formula: freezing the integrand on a partition
public import MathFin.Probability.Brownian.Ito.AdaptedStochasticIntegralFreezing
-- Step B2: the quadratic variation of an Itô process with adapted σ, ∑ w(ΔX)² → ∫ wσ² ds in L¹
public import MathFin.Probability.Brownian.AdaptedQuadraticVariation
-- First-order term of the adapted Itô formula (martingale part): ∑ w(tₖ)ΔMₖ → ∫ w dM in L²
public import MathFin.Probability.Brownian.AdaptedRiemannStieltjes
-- The drift of the adapted Itô formula: A = ∫b ds is Lipschitz, predictable, and ∑ g(tₖ)ΔAₖ → ∫ g·b
-- ds
public import MathFin.Probability.Brownian.Ito.AdaptedDrift
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdapted
-- Itô's formula for adapted coefficients, localised to every C² f and every t ≤ T
public import MathFin.Probability.Martingales.LocalisationInMeasure
-- Itô's formula for f(t, X_t) along an Itô process with adapted coefficients, every t ≤ T
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedTD
-- The Itô integral of an unbounded continuous adapted integrand, by localisation
public import MathFin.Probability.Brownian.Ito.ItoIntegralLocalised
-- The Itô integral of an unbounded continuous adapted integrand is a local martingale
public import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedLocalMartingale
-- Itô's formula along an Itô process with unbounded adapted coefficients
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedUnbounded
-- Riemann sums of a bounded predictable integrand with almost surely continuous paths
public import MathFin.Probability.Brownian.Ito.ItoIntegralPredictableRiemann
-- The Itô integral of a predictable integrand with almost surely continuous paths
public import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedPredictable
-- Itô's formula as an identity of processes; its stochastic term is a local martingale
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
-- The product rule for two Itô processes driven by one Brownian motion
public import MathFin.Probability.Brownian.Ito.ItoProductRule
-- Deterministic drift Riemann-convergence (α4 brick b-tail): ∑θ(tₖ)²·Δτ → ∫₀ᵀθ²ds
public import MathFin.Probability.Brownian.Ito.DriftRiemannConvergence
public import MathFin.Probability.Brownian.Ito.DriftPath
-- Continuous adapted-θ Girsanov assembly (α4 (c)): convergence core toward
-- Btheta_isBrownianOn_adapted
public import MathFin.Probability.Brownian.Girsanov.GirsanovAdaptedTheta
-- Rung 1 (bounded predictable θ Girsanov, Route B): marshal a SimpleProcess into single-partition
-- (s,c) form; generic simple-Doléans moment bounds; the predictable distributional Girsanov
-- theorem.
public import MathFin.Probability.Brownian.SimpleProcessPartition
public import MathFin.Probability.Brownian.Girsanov.GirsanovSimpleDoleansMoments
public import MathFin.Probability.Brownian.Girsanov.GirsanovPredictableTheta
public import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
public import MathFin.Probability.Brownian.Ito.ItoFormulaCLM
-- Summit A′: time-dependent Itô formula in L² — TD Taylor remainder vanishes,
-- TD Riemann↔CLM bridge, and the assembly f(T,B_T) = f(0,B₀) + ∫f_x dB + ∫(f_t+½f_xx)ds
public import MathFin.Probability.Brownian.Ito.ItoFormulaTDRemainder
public import MathFin.Probability.Brownian.Ito.ItoIntegralRiemannBridgeTD
public import MathFin.Probability.Brownian.Ito.ItoFormulaTD
public import MathFin.Probability.Brownian.BrownianExpMoment
public import MathFin.Probability.Brownian.Ito.ItoFormulaLocalized
public import MathFin.Probability.Brownian.Ito.ItoFormulaItoProcess
public import MathFin.Probability.Brownian.Ito.ItoFormulaGBM
public import MathFin.Probability.Brownian.Ito.ItoDriftExpectation
-- The integrated Itô–drift identity for adapted coefficients along `X_t = c + ∫β + M`,
-- conditional on a hypothesized adapted, path-continuous version `M` of the Itô integral
-- (the library does not construct one for general δ)
public import MathFin.Probability.Brownian.Ito.ItoDriftIncrementEnergy
public import MathFin.Probability.Brownian.Ito.ItoDriftWeightedIsometry
public import MathFin.Probability.Brownian.Ito.ItoDriftGapDecay
public import MathFin.Probability.Brownian.Ito.ItoStepSumFourthMoment
public import MathFin.Probability.Brownian.Ito.ItoDriftMomentBounds
public import MathFin.Probability.Brownian.Ito.ItoDriftBlock
public import MathFin.Probability.Brownian.Ito.ItoDriftQuadraticCorrections
public import MathFin.Probability.Brownian.Ito.ItoDriftTaylorRemainder
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedDrift
-- The companion with no hypothesized M (for B with continuous paths): the same identity for
-- the constructed process, derived from ito_formula_adapted (centering + Fubini)
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedDriftConstructed
-- Cross-horizon consistency of the CLM Itô integral: one pinned `M` (`hMeq`) represents
-- the CLM integral at every horizon `τ ≤ T` (band-transfer kernel + freeze law)
public import MathFin.Probability.Brownian.Ito.ItoIntegralCrossHorizon
public import MathFin.Probability.Brownian.SDE.GyongyMimicry
-- Martingale representation, step 3: the Doléans exponential of a deterministic step
-- integrand is an Itô integral (time locality of `∫·dB` + unbounded `𝓕_a`-scaling)
public import MathFin.Probability.Brownian.Ito.DoleansStepRepresentation
-- Martingale representation, step 4: the Wiener exponentials are total in `L²(𝓕ᴮ_T)`
-- (Abel summation + Laplace-transform uniqueness on `ℝⁿ` + Lévy's upward theorem)
public import MathFin.Probability.Brownian.WienerExponentialTotality
-- Martingale representation, step 5: the Itô integral is onto the centered `𝓕ᴮ_T`-measurable
-- part of `L²(μ)` — terminal, submodule and process forms of the representation theorem
public import MathFin.Probability.Brownian.MartingaleRepresentation
public import MathFin.Probability.Brownian.MartingaleMeasureUniqueness
public import MathFin.Probability.Brownian.Ito.ItoFormulaProcess
public import MathFin.Probability.Brownian.ExitTime
public import MathFin.Probability.Brownian.Ito.ItoFormulaCutoff
public import MathFin.Probability.Brownian.Ito.ItoFormulaUnrestrictedLocMart
-- Phase 39: Itô structural drift formula + GBM log-drift (after Nagy 2026)
public import MathFin.Probability.Brownian.Ito.ItoLemma
-- Time-dependent (2D) Itô formula + GBM-as-SDE-solution (genuine exp partials)
public import MathFin.Probability.Brownian.Ito.ItoLemma2D
-- Shared change-of-measure helper: a positive normalised density gives an
-- equivalent probability measure (consumed by the one-period FTAP files)
public import MathFin.Probability.Martingales.EquivMeasure
public import MathFin.Probability.Martingales.TimeChange
-- OU generator on polynomials: the Hermite spectral layer of the OU/Vasicek family
public import MathFin.Probability.Brownian.SDE.OUSpectral
-- Estimation: Gaussian variance-ratio KL, realised-variance noise bias, square-root bias
public import MathFin.Probability.Laws.Estimation
-- Phase 13 additions:
-- Compound-Poisson aggregate-loss MGF: iid-sum MGF composed with the Poisson pgf
public import MathFin.Probability.Jumps.CompoundPoissonMGF
public import MathFin.Probability.Gaussian.GaussianPairLinearLaw
public import MathFin.Probability.Gaussian.GaussianPartialMoments
public import MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment
public import MathFin.Probability.Brownian.Girsanov.WienerIntegralGirsanov
-- Weak uniqueness for the constant-coefficient integrated weak forward equation, via
-- the characteristic-function/Groenwall method
public import MathFin.Probability.Gaussian.WeakForwardUniqueness
-- Stochastic Fubini for a continuous linear L²-integral, and its Itô and Wiener instances
public import MathFin.Probability.Brownian.Ito.StochasticFubini
public import MathFin.Probability.Brownian.Ito.StochasticFubiniIto

-- Contracts
public import MathFin.Contracts.Instruments.CallPayoff
-- Contracts tower: a reified payoff language, model-agnostic until priced
-- (Bilokon, "The Contract Is Not the Model", 9 August 2026)
public import MathFin.Contracts.Core
public import MathFin.Contracts.Adapted
public import MathFin.Contracts.Instruments.Options
public import MathFin.Contracts.StaticHedge
public import MathFin.Contracts.Instruments.FixedIncome
public import MathFin.Contracts.Instruments.Credit
public import MathFin.Risk.Credit.TrancheLeg

-- Pricing
-- Continuous-time first FTAP: discounted GBM price is a Q-martingale (Wald exponential)
public import MathFin.Pricing.FTAP.ContinuousFTAP
-- Model-agnostic continuous-market vocabulary: IsEMM on a process, simple strategies, no-arbitrage
public import MathFin.Pricing.ContinuousMarket
public import MathFin.Pricing.Girsanov
public import MathFin.Pricing.Numeraire
-- The T-forward measure: the zero-coupon bond as numéraire (change-of-numéraire instance)
public import MathFin.Pricing.ForwardMeasure
public import MathFin.Pricing.NoArbitrageCore
public import MathFin.Pricing.FTAP.FTAP
public import MathFin.Pricing.ReplicationPricing
-- Phase 13 additions:
public import MathFin.Pricing.StatePrices
public import MathFin.Pricing.ConvexPricingFunctional
public import MathFin.Pricing.Duality.ConvexSeparation
-- Phase 1 (convex-duality unification): cone-separation root generalizing
-- ConvexSeparation from a subspace (two-sided `= 0`) to a closed convex cone (`≤ 0`)
public import MathFin.Pricing.Duality.ConvexDuality
-- Martingale representation, step 6: its finance reading — replication, superreplication
-- duality, and uniqueness of the pricing measure on the Brownian filtration
public import MathFin.Pricing.MarketCompleteness
public import MathFin.Pricing.MarketCompletenessInPrice
-- The price with a drift, S = S₀ + ∫b ds + (σ●B), and the integral against it
public import MathFin.Pricing.PricePathDrift
public import MathFin.Pricing.PricingMeasureL2Density
-- Phase 37: FTAP both directions, two-state market (adapted from Nagy 2026)
public import MathFin.Pricing.FTAP.FTAPTwoState
-- Phase 53: Pricing kernel from two-state FTAP (state-prices composition)
public import MathFin.Pricing.PricingKernel
-- Phase 42: Multi-state FTAP backward (hypothesis-form, forward direction proved)
public import MathFin.Pricing.FTAP.FTAPMultiState
public import MathFin.Pricing.FTAP.FTAPDiscrete
public import MathFin.Pricing.FTAP.FTAPComplete
-- General-Ω one-period FTAP (Föllmer–Schied §1.2 / one-period DMW, scalar)
public import MathFin.Pricing.FTAP.FTAPOnePeriod
-- General-Ω one-period FTAP, d assets (Esscher minimal-divergence EMM, full — finite-dim market)
public import MathFin.Pricing.FTAP.FTAPOnePeriodVector
-- Multi-period FTAP on a general space: no arbitrage is local, one-period densities paste, and
-- the Dalang–Morton–Willinger theorem: the reduction, pasting and the one-asset theorem
public import MathFin.Pricing.FTAP.NoArbitrageLocal
public import MathFin.Pricing.FTAP.DensityPasting
public import MathFin.Pricing.FTAP.DalangMortonWillinger
public import MathFin.Pricing.FTAP.OneAssetDMW
public import MathFin.Pricing.FTAP.MarketFTAP
-- Phase 20: first-principles core derivations
public import MathFin.Pricing.NoArbitrageDerivations
-- Phase 1 (convex-duality unification): fundamental superhedging bound — every EMM prices a claim
-- at most its super-replication cost (the pricing-side companion of the coherent-risk
-- representation)
public import MathFin.Pricing.SuperhedgingDuality
public import MathFin.Pricing.Value
public import MathFin.Pricing.Market
public import MathFin.Pricing.BondPrice
public import MathFin.Pricing.AmericanPrice
public import MathFin.Pricing.OneDateMarket
public import MathFin.Pricing.Parity
public import MathFin.Pricing.StaticHedge
public import MathFin.Pricing.DiscreteMarket
-- The law of a Wiener-represented rate under the forward measure of a Wiener-represented account
public import MathFin.Pricing.WienerIntegralForwardMeasure

-- Models
public import MathFin.Models.BlackScholes.GaussianGirsanov
public import MathFin.Models.Forwards.TriangleArbitrage
public import MathFin.Models.ModelFree.CarrMadan
public import MathFin.Models.ModelFree.CarrMadanMarket
-- Phase 30 (Bridge A): BSCallHyp / BachelierHyp from IsPreBrownian
public import MathFin.Models.BlackScholes.BSCallHypFromBrownian
-- Phase 31: Pricing entry points from IsPreBrownian (composite corollaries)
public import MathFin.Models.BlackScholes.PricingFromBrownian
-- Phase 32: Variance-swap log-price squared-increment from BrownianQuadraticVariation
public import MathFin.Models.ModelFree.VarianceSwapFromQV
-- Phase 33: Variance-swap equipartition sum from BrownianQuadraticVariation
public import MathFin.Models.ModelFree.VarianceSwapEquipartition
-- Phase 34: Variance-swap QV limit theorem (realised-variance → σ²T as n → ∞)
public import MathFin.Models.ModelFree.VarianceSwapLimit
-- Variance-swap drift immunity: realized variance → σ²T in L² for ANY drift
-- (consumes ItoProcessQV; strengthens phase 34 from expectation-level to L²)
public import MathFin.Models.ModelFree.VarianceSwapDriftImmunity
public import MathFin.Models.Rates.HullWhiteCalibration
public import MathFin.Models.Rates.HullWhiteBondPriceAt
public import MathFin.Models.Rates.HoLeeBondPrice
public import MathFin.Models.BlackScholes.MonteCarloPricer
-- Phase 45: Variance swap log-payoff and QV-limit form equivalence
public import MathFin.Models.ModelFree.VarianceSwapEquivalence
public import MathFin.Models.BlackScholes.Call
public import MathFin.Models.BlackScholes.Put
public import MathFin.Models.BlackScholes.PDE
public import MathFin.Models.BlackScholes.PutGreeks
public import MathFin.Models.BlackScholes.Digital
public import MathFin.Models.BlackScholes.DigitalGreeks
public import MathFin.Models.BlackScholes.Dividends
public import MathFin.Models.BlackScholes.DividendsGreeks
public import MathFin.Models.BlackScholes.Forward
public import MathFin.Models.BlackScholes.ForwardStart
public import MathFin.Models.BlackScholes.HigherGreeks
public import MathFin.Models.BlackScholes.StrikeGreeks
-- Local-vol skew of a tilted smile surface via Dupire's ratio; the rule of two
public import MathFin.Models.LocalVol.ForwardSmile
public import MathFin.Models.LocalVol.MarketCallSurface
public import MathFin.Models.BlackScholes.PutStrikeConvexity
public import MathFin.Models.BlackScholes.AsianInequality
public import MathFin.Models.BlackScholes.AsianArithmeticAverageStrike
-- Geometric-average Asian: two-date log-driver is Gaussian with the covariance-sum variance
public import MathFin.Models.BlackScholes.AsianGeometric
-- Geometric-average Asian: n-date driver law + closed-form price via effective-BS reduction
public import MathFin.Models.BlackScholes.AsianGeometricN
public import MathFin.Models.BlackScholes.ImpliedVolatility
-- SABR (Hagan-Kumar-Lesniewski-Woodward 2002) lognormal implied-vol asymptotic
-- approximation: eq. 2.17 -> eq. 2.18 as K -> f, backbone law, ATM Black-76 price
public import MathFin.Models.StochVol.SABRImpliedVol
-- Le Floc'h-Kennedy SABR building blocks: y(k) -> -log(F/k) as beta -> 1,
-- Dint -> -y/alpha as nu -> 0 (the removable singularities of the closed forms)
public import MathFin.Models.StochVol.SABRFlochKennedyLimits
public import MathFin.Models.BlackScholes.LognormalMoments
public import MathFin.Models.ModelFree.VarianceSwap
-- the volatility-swap fair strike under an assumed lognormal law of realized variance
public import MathFin.Models.ModelFree.VolatilitySwapLognormal
-- Merton (1976) jump-diffusion: Poisson-mixture price, compensation
-- identity, parity (consumes Probability.Jumps.PoissonPgf + Call/Put formulas)
public import MathFin.Models.Jumps.MertonJumpDiffusion
-- Merton dominance (jump risk is never free: vega + gamma/Jensen channels)
-- and the classic Λ′ = Λ(1+k) display (rate-shift identity)
public import MathFin.Models.Jumps.MertonDominance
public import MathFin.Models.Jumps.MertonClassicDisplay
-- Merton's model derived: the jump-diffusion terminal price (Gaussian diffusion,
-- Poisson count, i.i.d. lognormal jumps) prices to the Poisson mixture
-- Merton Greeks: delta, gamma, vega as Poisson mixtures of Black–Scholes Greeks
public import MathFin.Models.Jumps.MertonGreeks
-- Merton's strike derivatives: the digital series and the density series (Poisson mixtures of
-- Black–Scholes digitals and of lognormal density formulas), and Merton's Breeden–Litzenberger
public import MathFin.Models.Jumps.MertonStrikeGreeks
-- Jump-diffusions with an arbitrary jump law: the mixing formula, the
-- compound-Poisson compensator, and Merton's formula for a general jump law
public import MathFin.Models.Jumps.JumpDiffusionMixing
-- Compensated jumps lift the Black–Scholes implied volatility strictly above σ
public import MathFin.Models.Jumps.JumpImpliedVol
-- The Ju-Zhong quadratic approximation's r -> 0 limit: the pre-fix and post-fix
-- closed forms agree for every r != 0, and agree in the limit as r -> 0 too
public import MathFin.Models.BlackScholes.American.JuZhongZeroRateLimit
-- The canonical jump-diffusion model: the hypotheses are satisfiable for every
-- expected jump count and jump law, and the call depends only on these two
public import MathFin.Models.Jumps.JumpDiffusionCanonical
-- The jump-diffusion price process: discounted, a martingale exactly at the compensated drift
public import MathFin.Models.Jumps.JumpDiffusionProcess
-- Option prices at intermediate dates: a function of the current price and the
-- remaining maturity
public import MathFin.Models.Jumps.JumpDiffusionOptionPrices
public import MathFin.Models.BlackScholes.GaussianSmoothing
public import MathFin.Models.Jumps.JumpDiffusionMerton
public import MathFin.Models.Jumps.JumpDiffusionBrownian
-- Scaling a jump-diffusion; the exponential martingales e^{θX_t − κ(θ)t} for the Laplace
-- exponent κ (where the jump law has the moment of order θ); power claims at each date
public import MathFin.Models.Jumps.JumpDiffusionExponent
-- The Esscher transform of a jump-diffusion log-return law: again a jump-diffusion law when the
-- jump law's moment-generating function is finite near θ; Esscher pricing is Merton's formula for
-- the tilted jumps, and Black–Scholes without jumps
public import MathFin.Models.Jumps.JumpDiffusionEsscher
-- The law at one date determines the drift, σ² and the Lévy measure off 0 (Lévy–Khintchine
-- uniqueness for jump laws whose moment-generating function is finite near 0)
public import MathFin.Models.Jumps.JumpDiffusionIdentifiability
-- Incompleteness at one date: for σ ≠ 0 the Esscher law and the Merton measure are both
-- equivalent to the physical law (with any drift) and compensated, yet price some call
-- differently when the jumps are nontrivial
public import MathFin.Models.Jumps.JumpDiffusionIncompleteness
public import MathFin.Models.Jumps.Market
-- The log-return law is a Gaussian mixture; with σ ≠ 0 and τ > 0 it has a continuous density, so
-- no atoms, and with σ = 0 it has an atom at bτ; the tail of a law with a density is
-- differentiable where the density is continuous; the law of the price Seʸ has the density
-- f(log(K/S))/K
public import MathFin.Models.Jumps.JumpDiffusionDensity
-- Digital options and Breeden–Litzenberger with jumps: for σ ≠ 0 and τ > 0 the strike derivative
-- of the call price is minus the digital price and the second one is the discounted density of the
-- price; without jumps, at the drift r − σ²/2, these are e^{−rτ}Φ(d₂) and lognormalTerminalPDF;
-- with Gaussian log-jumps, Merton's digital and density series; with σ = 0 the call price has a
-- kink at the strike Se^{bτ}; lognormalTerminalPDF and mertonTerminalPDF as densities of the price
public import MathFin.Models.Jumps.JumpDiffusionDigital
-- Strict convexity in the strike: the call price is convex under any law, and strictly convex
-- where the law charges every interval; with σ ≠ 0 and τ > 0 the jump-diffusion density is
-- positive, so with S > 0 and a finite forward the call price is strictly convex on (0, ∞) for
-- any jump law, and so are the Black–Scholes price and Merton's series
public import MathFin.Models.Jumps.JumpDiffusionStrikeConvexity
-- The mean, variance and second moment of the jump-diffusion log-return, from the first two
-- derivatives at 0 of its cumulant generating function κ(θ)τ
public import MathFin.Models.Jumps.JumpDiffusionMoments
-- Variance swaps with jumps: at the compensated drift the log contract has expected payoff
-- σ² + 2ΛE[eᴶ − 1 − J], which differs from the variance per unit time σ² + ΛE[J²] by the jump
-- bias 2ΛE[eᴶ − 1 − J − J²/2], ≤ 0 for jumps ≤ 0 and < 0 if moreover Λ > 0 and the jumps are
-- negative with positive probability. On the process, under a measure that makes the discounted
-- price a martingale, the log contract minus the expected realized variance per unit time along
-- n + 1 equal steps of [0, T] is the jump bias less (b + ΛE[J])²T/(n + 1), at every n, so it tends
-- to the jump bias; Black–Scholes (Brownian motion) is a corollary on the process, and Merton's
-- Gaussian jumps a corollary at the level of the law (log contract against Var[Y]/τ)
public import MathFin.Models.Jumps.JumpDiffusionVarianceSwap
public import MathFin.Models.Bachelier.Bachelier
public import MathFin.Models.Bachelier.BachelierSpread
public import MathFin.Models.Bachelier.BachelierGreeks
public import MathFin.Models.Bachelier.BachelierMarket
public import MathFin.Models.BlackScholes.Chooser
public import MathFin.Models.ModelFree.Spreads
-- Call spreads tend to the digital, so call prices at every strike determine the law (the first-
-- order Breeden–Litzenberger, for any law with a finite mean); the call price is differentiable
-- in the strike exactly where the law has no atom, and there its derivative is minus the digital
public import MathFin.Models.ModelFree.CallSpreadDigital
public import MathFin.Models.BlackScholes.DeltaHedge
public import MathFin.Models.LocalVol.Dupire
-- The Heston 2D affine transform at the generator/PDE level: the rho-shifted Riccati
-- closed forms, the pricing PDE, and the gated real-moment expectation
public import MathFin.Models.StochVol.Heston
-- The Heston transform at vanishing vol-of-vol: the Black-Scholes moment with the integrated
-- deterministic variance
public import MathFin.Models.StochVol.HestonSmallVolOfVol
-- The Heston transform at zero maturity: the Riccati flows vanish at τ = 0 and the
-- profile degenerates to the point-mass mgf (the undiscounted-payoff convention)
public import MathFin.Models.BlackScholes.Lookback
public import MathFin.Models.BlackScholes.BarrierReflection
public import MathFin.Models.BlackScholes.BarrierParity
public import MathFin.Models.BlackScholes.BinaryBarrierOption
-- Also consumes the bivariate normal CDF (Probability/Gaussian/BivariateNormalCDF),
-- like Stulz/Heynen-Kat below
public import MathFin.Models.BlackScholes.PartialTimeBarrierOption
-- Spatial and time-volatility scaling of the Black–Scholes call
public import MathFin.Models.BlackScholes.ScalingInvariance
-- Broadie–Glasserman–Kou barrier shift for discretely monitored down-and-out calls
public import MathFin.Models.BlackScholes.DiscreteBarrierCorrection
public import MathFin.Models.BlackScholes.PowerOption
public import MathFin.Models.ModelFree.BreedenLitzenberger
public import MathFin.Models.BlackScholes.BisectionIV
-- Structural / principle modules:
public import MathFin.Models.BlackScholes.StrikeConvexity
public import MathFin.Models.BlackScholes.SpotConvexity
public import MathFin.Models.ModelFree.PriceBounds
public import MathFin.Models.ModelFree.CallPriceFunction
public import MathFin.Models.ModelFree.MarketCallPrice
public import MathFin.Models.ModelFree.StaticHedgeMarket
public import MathFin.Models.ModelFree.RoperConverse
-- Phase 13 additions:
-- Quanto correction derived from a joint-Gaussian FX model (Girsanov-grounded)
public import MathFin.Models.BlackScholes.QuantoGrounding
public import MathFin.Models.BlackScholes.NewtonConvergence
public import MathFin.Models.Forwards.Black76
public import MathFin.Models.Forwards.Black76Greeks
public import MathFin.Models.Forwards.SchwartzOneFactor
-- Phase 13 additions:
public import MathFin.Models.Binomial.Model
public import MathFin.Models.Binomial.American
public import MathFin.Models.Binomial.AmericanMarket
public import MathFin.Models.Binomial.AmericanPutPremium
public import MathFin.Models.Binomial.CRRConvergence
public import MathFin.Models.Binomial.DriftLimit
public import MathFin.Models.Binomial.Bermudan
public import MathFin.Models.Binomial.MartingaleRepresentation
public import MathFin.Models.Binomial.EuropeanReplication
public import MathFin.Models.Binomial.FlipPaths
-- Phase 13 additions:
public import MathFin.Models.Binomial.Girsanov
public import MathFin.Models.Binomial.SecondFTAP
-- Phase 14: real new theorems
public import MathFin.Models.Binomial.MertonAmericanCallTree
public import MathFin.Models.Binomial.ReplicatingUniqueness
public import MathFin.Models.BlackScholes.GreekSigns
-- Phase 16: reflection-principle algebraic core (André 1887)
public import MathFin.Models.Binomial.PathReflection
-- Barrier-option counting: reflection card identity + maximal-distribution (running-max law)
public import MathFin.Models.Binomial.BarrierReflection
public import MathFin.Models.Binomial.BarrierMarket
-- Phase 19: Snell envelope characterization of americanPrice
public import MathFin.Models.Binomial.SnellEnvelope
-- Phase 43: Binomial up-probability as two-state FTAP EMM
public import MathFin.Models.Binomial.BinomialFromFTAP
-- Phase 44: CRR binomial scheme as discrete-Itô process (drift + QV limits)
public import MathFin.Models.Binomial.CRRDiscreteIto
-- CRR → BS characteristic-function convergence (the distributional CLT heart)
public import MathFin.Models.Binomial.CRRCharFun
-- CRR → BS in literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (Φ-landing corollary)
public import MathFin.Models.Binomial.CRRClosedForm
public import MathFin.Models.BlackScholes.RiskNeutralProbabilities
-- Phase 22: delta as stock-numeraire probability (Φ(d_1) = Q^(S)(S_T > K))
public import MathFin.Models.BlackScholes.StockNumeraire
-- Phase 24: powered call closed form via reduction to BS-call (effective spot/vol)
public import MathFin.Models.BlackScholes.PowerCall
-- BS-family Garman normal form (`V = A·Φ(d_1) − K·DF·Φ(d_2)`): the single
-- numéraire-parameterised template consumed by ExchangeOption, Black-76, KMVMerton
public import MathFin.Models.BlackScholes.GarmanNormalForm
-- Basket option pricing via moment-matching to a single lognormal (approximation)
public import MathFin.Models.BlackScholes.BasketMomentMatching
public import MathFin.Models.BlackScholes.ExchangeOption
-- Two-asset closed forms (Stulz rainbow, Heynen–Kat barrier) on the bivariate normal CDF
public import MathFin.Models.BlackScholes.StulzTwoAssetRainbow
public import MathFin.Models.BlackScholes.HeynenKatTwoAssetBarrier
-- Margrabe BSCallHyp grounding from a joint two-GBM gaussian model (leap-3 closure)
public import MathFin.Models.BlackScholes.MargrabeGrounding
-- Kirk's (1995) approximation for spread options (K ≠ 0), a Garman-normal-form instance
public import MathFin.Models.BlackScholes.KirkSpreadApproximation
-- Phase 25: chooser option as call + put portfolio via PCP at chooser date
public import MathFin.Models.BlackScholes.ChooserComposition
-- Phase 46: BS PDE derived from Itô drift + no-arbitrage
public import MathFin.Models.BlackScholes.PDEFromIto
-- Feynman–Kac → BS PDE keystone (step 2: the FK price representation)
public import MathFin.Models.BlackScholes.PDEFromFeynmanKac
-- Phase 40: Itô lemma L¹-expectation form applied to GBM log (mean + variance)
public import MathFin.Models.BlackScholes.GBMLogMoments
public import MathFin.Models.Rates.ZCB
public import MathFin.Models.Rates.CouponBonds
public import MathFin.Models.Rates.Immunization
public import MathFin.Models.Rates.ConvexityImmunization
public import MathFin.Models.Rates.YieldCurve
public import MathFin.Models.Rates.Bootstrapping
public import MathFin.Models.Credit.Credit
-- First-to-default: basket intensity = Σ single-name intensities
-- (bridges Probability.Laws.ExpMin into the Credit vocabulary)
public import MathFin.Models.Credit.FirstToDefault
public import MathFin.Models.Rates.MacaulayModified
public import MathFin.Models.Credit.HazardCurve
public import MathFin.Models.Rates.ForwardRate
public import MathFin.Models.Rates.TimingAdjustment
public import MathFin.Models.Rates.Vasicek
-- Phase 13 additions:
public import MathFin.Models.Credit.KMVMerton
-- Phase 21: first-principles duration-as-price-sensitivity
public import MathFin.Models.Rates.DurationSensitivity
-- Phase 22: first-principles convexity-as-second-derivative
public import MathFin.Models.Rates.ConvexitySensitivity
-- Phase 27: KMV-Merton structural derivation (probabilistic content of `kmvPD`)
public import MathFin.Models.Credit.KMVMertonStructural
public import MathFin.Models.Credit.MertonMarket
-- Phase 28: CDS fair spread under time-varying hazard (cash-flow balance)
public import MathFin.Models.Credit.CDSTimeVarying
public import MathFin.Models.Credit.Cox
-- Default-time density of a deterministic hazard curve (law of τ as Lebesgue density)
public import MathFin.Models.Credit.DefaultDensity
-- CVA under exposure independent of default (Fubini reduction; Gaussian expected exposure in
-- closed form)
public import MathFin.Models.Credit.CVA
-- DVA from CVA: negate the exposure, swap in the bank's own default time; DVA as the integral
-- of the expected negative exposure
public import MathFin.Models.Credit.DVA
-- Phase 41: Vasicek SDE closed-form (full SDE, mean + variance)
public import MathFin.Models.Rates.VasicekSDE
-- Itô→pricing bridge: Vasicek terminal law derived (Wiener integral is Gaussian)
public import MathFin.Models.Rates.VasicekSDEGaussian
-- Sum of two squared OU fluctuations: mean θ(1 − e^{−kt}) + v₀e^{−kt}, the borderline CIR mean
public import MathFin.Models.Rates.CIRSquaredOU
-- Vasicek zero-coupon bond price: the affine term structure (Gaussian Laplace transform)
public import MathFin.Models.Rates.VasicekBondPrice
-- Vasicek bond price at t > 0: the conditional discount factor is affine in the short rate
public import MathFin.Models.Rates.VasicekBondPriceAt
-- The Vasicek bond market: bank-account numéraire, zero-coupon bond, reference measure prices it
public import MathFin.Models.Rates.VasicekMarket
-- Vasicek real-world vs. risk-neutral terminal mean; an Esscher tilt reproducing the
-- risk-neutral terminal law
public import MathFin.Models.Rates.VasicekMarketPDE
public import MathFin.Models.Rates.VasicekMarketPriceOfRisk
-- Vasicek bond price as κ → 0⁺: the three-term cancellation limit to the driftless model
public import MathFin.Models.Rates.VasicekZeroMeanReversionLimit
-- The Nelson–Siegel/Svensson zero-rate at vanishing decay: the loading tends
-- to 1, the zero rate to c0 + c1, the Svensson second term to 0 (the guarded-limit values)
-- CIR loadings: B solves the Riccati equation, A solves A' = −κθB
public import MathFin.Models.Rates.CIRRiccati
-- The Black–Scholes forward price under the T-forward measure
public import MathFin.Models.Rates.ForwardMeasure
-- Inflation is FX: the zero-coupon inflation swap and the YoY convexity
public import MathFin.Models.Rates.Inflation
public import MathFin.Models.Rates.OvernightCompounding
public import MathFin.Models.Rates.JarrowYildirim
-- ABCD instantaneous volatility: closed-form integrated variance over a window
public import MathFin.Models.Rates.ABCDVolatility
-- GSR (Gaussian short rate): two-piece piecewise-constant-volatility bond price
public import MathFin.Models.Rates.GSRPiecewiseVol
public import MathFin.Models.Rates.GSRBondPriceAt
-- LSV calibration: the leverage-posterior core (L²·E[v | S = K] = σ_loc²)
public import MathFin.Models.StochVol.LSVLeverage
-- Upstream (Degenne BrownianMotion) modules consumed ONLY by benchmark
-- wrappers, imported here so `lake build` puts them in the build graph —
-- nothing else in MathFin/ imports them, and a snippet import of an unbuilt
-- module fails with a silently-empty environment (found 2026-06-05 via
-- cm-thm-4.3.7; its sibling cm-thm-4.3.9 works only because
-- Probability/Martingales/LpContinuousMartingaleConvergence imports Degenne's DoobLp).
public import MathFin.Models.Rates.InterestRateSwap
public import MathFin.Models.Rates.CMS
public import MathFin.Models.Rates.FRA
public import MathFin.Models.Rates.DeterministicCurve
public import MathFin.Models.Rates.DeterministicMarket
public import MathFin.Models.Rates.NelsonSiegelSvensson
public import MathFin.Models.BlackScholes.BlackScholes
public import MathFin.Models.BlackScholes.BlackScholesExchange
public import MathFin.Models.BlackScholes.BlackScholesAsian
public import MathFin.Models.BlackScholes.BlackScholesSDE
public import MathFin.Models.BlackScholes.BlackScholesChooser
public import MathFin.Models.BlackScholes.BlackScholesHedge
public import MathFin.Models.BlackScholes.BlackScholesPhysical
public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.PricingMeasureUnique
-- The Black–Scholes delta hedge is self-financing: the product rule with the factor e^{rt}
public import MathFin.Models.BlackScholes.BlackScholesSelfFinancing
public import MathFin.Models.Binomial.Binomial
public import MathFin.Models.Binomial.BinomialCompleteMarket
public import MathFin.Models.Binomial.BinomialLimit
public import MathFin.Models.Binomial.Market
public import MathFin.Models.LocalVol.TimeDependentVol
public import MathFin.Models.Rates.Caplet
public import MathFin.Models.Rates.CMSContract
public import MathFin.Models.Rates.ShortRate
public import MathFin.Models.Rates.VasicekBond
public import MathFin.Models.Rates.HullWhiteBond
public import MathFin.Models.Rates.GSRBond
public import MathFin.Models.Rates.Jamshidian
public import MathFin.Models.Credit.DefaultTime
public import MathFin.Models.Credit.DefaultTimeMesh
-- Continuous-time American put option exercise-boundary geometry
public import MathFin.Models.BlackScholes.American.Stopping.PhysicalBoundaryConvexity
public import MathFin.Models.BlackScholes.American.Stopping.PlanePartial
public import MathFin.Models.BlackScholes.American.Stopping.AEHorizonValue
public import MathFin.Models.BlackScholes.American.Stopping.AugmentedValue
public import MathFin.Models.BlackScholes.American.Stopping.LocalPriceIto
-- The American put exercise boundary tends to the strike at expiry
public import MathFin.Models.BlackScholes.American.Stopping.ActualBoundaryExpiryLimit
-- The Andersen-Lake-Offengenden QD+ fixed-point quadrature integrand's endpoint
-- limits, and that differentiability of the boundary cannot be weakened to continuity
public import MathFin.Models.BlackScholes.American.AmericanQDPlusLimits
-- The SVI no-butterfly certificate (Robert Martin, #174)
public import MathFin.Models.ModelFree.SVI.Admissibility
public import MathFin.Models.ModelFree.SVI.Assembly
public import MathFin.Models.ModelFree.SVI.AssociatedTrace
public import MathFin.Models.ModelFree.SVI.BlackScholesBridge
public import MathFin.Models.ModelFree.SVI.BlackSmile
public import MathFin.Models.ModelFree.SVI.CallConvexity
public import MathFin.Models.ModelFree.SVI.ClearedSignature
public import MathFin.Models.ModelFree.SVI.Companion
public import MathFin.Models.ModelFree.SVI.ConvexKink
public import MathFin.Models.ModelFree.SVI.CriticalPoints
public import MathFin.Models.ModelFree.SVI.DegreeProgram
public import MathFin.Models.ModelFree.SVI.Denominators
public import MathFin.Models.ModelFree.SVI.Derivatives
public import MathFin.Models.ModelFree.SVI.DomainFormula
public import MathFin.Models.ModelFree.SVI.ExtendedFormula
public import MathFin.Models.ModelFree.SVI.FiniteCertificate
public import MathFin.Models.ModelFree.SVI.HermiteIdentity
public import MathFin.Models.ModelFree.SVI.ImaginaryTraceSignature
public import MathFin.Models.ModelFree.SVI.MarketRealisation
public import MathFin.Models.ModelFree.SVI.Matrices
public import MathFin.Models.ModelFree.SVI.MatrixCertificate
public import MathFin.Models.ModelFree.SVI.MatrixSignature
public import MathFin.Models.ModelFree.SVI.NilpotentSquareRoot
public import MathFin.Models.ModelFree.SVI.ParameterPolynomials
public import MathFin.Models.ModelFree.SVI.Polynomial
public import MathFin.Models.ModelFree.SVI.PolynomialCertificate
public import MathFin.Models.ModelFree.SVI.ProductSignature
public import MathFin.Models.ModelFree.SVI.QuadraticRay
public import MathFin.Models.ModelFree.SVI.QuadraticRootSignature
public import MathFin.Models.ModelFree.SVI.QuotientProduct
public import MathFin.Models.ModelFree.SVI.RankOneSignature
public import MathFin.Models.ModelFree.SVI.RealIrreducibles
public import MathFin.Models.ModelFree.SVI.RealRootSignature
public import MathFin.Models.ModelFree.SVI.RealRootTrace
public import MathFin.Models.ModelFree.SVI.Reduction
public import MathFin.Models.ModelFree.SVI.SigmaZeroCertificate
public import MathFin.Models.ModelFree.SVI.SigmaZeroConvexity
public import MathFin.Models.ModelFree.SVI.SigmaZeroDerivatives
public import MathFin.Models.ModelFree.SVI.SignFormula
public import MathFin.Models.ModelFree.SVI.SignVariations
public import MathFin.Models.ModelFree.SVI.SignatureProgram
public import MathFin.Models.ModelFree.SVI.TraceForm
public import MathFin.Models.ModelFree.SVI.TraceSignature
-- The SVI tail condition d₊ → −∞ iff b(1+ρ) < 2, and the butterfly-free sign formula
public import MathFin.Models.ModelFree.SVI.TailCondition
public import MathFin.Models.ModelFree.SVI.SSVI
-- Calendar-spread arbitrage (Gatheral–Jacquier Lemma 2.1) and its raw-SVI form
public import MathFin.Models.ModelFree.CalendarArbitrage
-- Fisher/Sraffa own rate: Sraffa's implied own rate from spot, forward and financing rate
public import MathFin.Models.Forwards.FisherSraffaOwnRate
-- Theory of storage: convenience yield and the kink point of the storage price curve
public import MathFin.Models.Forwards.TheoryOfStorage
-- AR(1) <-> Ornstein-Uhlenbeck parameter inversion for commodity calibration
public import MathFin.Models.Forwards.AR1OUCalibration
public import MathFin.Models.Binomial.PathMeasure
public import MathFin.Models.Binomial.MultiPeriodFTAP
public import MathFin.Models.Jumps.JumpDiffusionThinning
public import MathFin.Models.Rates.ABCDBlack76
public import MathFin.Models.BlackScholes.American.AmericanPutEuropeanBound
public import MathFin.Models.BlackScholes.American.AmericanMarketPrice
public import MathFin.Models.BlackScholes.American.AmericanPutMarketBound
public import MathFin.Models.Rates.OUHermiteVasicek
public import MathFin.Models.Rates.AffineTermStructurePDE
public import MathFin.Models.Rates.PeriodicCompounding
public import MathFin.Models.Rates.VasicekYieldNelsonSiegel
public import MathFin.Models.StochVol.LSVPosteriorConditionalExpectation
-- Clean/dirty price and accrued interest; clean price continuous across a coupon date
public import MathFin.Models.Rates.CleanPriceAccrued
-- Bond forward price derived from forward_price_from_no_arbitrage
public import MathFin.Models.Rates.BondForward
-- Covered and uncovered interest parity, from no-arbitrage and the Garman–Kohlhagen measure
public import MathFin.Models.Forwards.FxForwardParity
-- Contango, backwardation and basis convergence for the cost-of-carry forward
public import MathFin.Models.Forwards.ContangoBackwardation
-- Loan amortization: bullet, equal-principal, and level-payment against annuityValue
public import MathFin.Models.Rates.LoanAmortization
-- Key-rate partials sum to the parallel-shift derivative; on a flat curve, to dP/dy
public import MathFin.Models.Rates.KeyRateDuration
-- The Heath–Jarrow–Morton model bundle: forward curve, bond, short rate, bank account
public import MathFin.Models.Rates.HJM
-- Fixed cash flows in the HJM model: the discount factor, and pricing off the initial bond curve
public import MathFin.Models.Rates.HJMBond

-- Risk
public import MathFin.Risk.Gaussian
public import MathFin.Risk.CoherentAxioms
public import MathFin.Risk.Additivity
public import MathFin.Risk.RockafellarUryasev
public import MathFin.Risk.Spectral
public import MathFin.Risk.Concentration
-- Phase 21: first-principles coherent-axiom derivation from concave utility
public import MathFin.Risk.UtilityDerivation
-- The one coherence structure: the four ADEH axioms for losses, ρ(0) = 0, convexity, and (finite
-- state) pointwise monotonicity and continuity
public import MathFin.Risk.Coherent
public import MathFin.Risk.CompleteMixability
public import MathFin.Risk.ConvexOrderSums
-- The positions convention of the ADEH paper is the loss convention at L ↦ ρ(−L)
public import MathFin.Risk.PositionsConvention
-- Phase 1 (convex-duality unification): coherent-risk ADEH representation — acceptance cone
-- separation giving the representing probability measures (risk-side Hahn–Banach)
public import MathFin.Risk.AcceptanceSet
public import MathFin.Risk.Superhedging
-- Phase 1 (convex-duality unification): worst-case loss — the most conservative coherent risk
-- measure, concrete instance of the ADEH representation (sup over the entire probability simplex)
public import MathFin.Risk.WorstCaseRisk
-- Value-at-risk and expected shortfall of a general loss (any law, atoms included), and the
-- Gaussian closed forms identified as the VaR of the law at z = Φ⁻¹(α)
public import MathFin.Risk.ValueAtRisk
public import MathFin.Risk.GaussianValueAtRisk
-- Expected negative exposure, potential future exposure (the VaR of V⁺) and netting
-- subadditivity on the CVA expected-exposure substrate; collateralized exposure under a
-- Brownian-driven process, the collateral the same process a lag earlier
public import MathFin.Risk.ExposureMeasures
public import MathFin.Risk.CollateralizedExposureBrownian
-- Expected shortfall: Rockafellar–Uryasev for every law, coherence, dual representation; the
-- Gaussian ES closed form; VaR by bisection; VaR superadditivity; closed forms and tail ratios;
-- VaR and ES of the Student-t law (McNeil–Frey–Embrechts closed forms); elicitability
-- (VaR elicitable, ES not); Bernoulli mixtures and the Basel IRB limit theorem
public import MathFin.Risk.ExpectedShortfall
public import MathFin.Risk.CompoundPoissonCVaR
-- The stop-loss transform across a gap in the law: the stop-loss recursion of an arithmetic loss
-- and the Rockafellar–Uryasev objective on its lattice
public import MathFin.Risk.StopLossGap
public import MathFin.Risk.GaussianExpectedShortfall
public import MathFin.Risk.ValueAtRiskBisection
public import MathFin.Risk.VaRSuperadditivity
public import MathFin.Risk.DependenceUncertainty
public import MathFin.Risk.DiscreteVaR
public import MathFin.Risk.RiskClosedForms
public import MathFin.Risk.StudentTValueAtRisk
public import MathFin.Risk.Elicitability
public import MathFin.Risk.JointElicitability
public import MathFin.Risk.Expectile
public import MathFin.Risk.EntropicRisk
public import MathFin.Risk.LawInvariance
public import MathFin.Risk.Credit.BernoulliMixture
public import MathFin.Risk.Credit.CreditMetrics
public import MathFin.Risk.Credit.VasicekIRB
-- LHP tranche expected loss: the Vasicek (2002) stop-loss closed form and the finite-pool limit
public import MathFin.Risk.Credit.TrancheLoss
public import MathFin.Risk.SACCRExposure
-- Bridges (certified cross-domain unifications)
public import MathFin.Risk.ConcentrationVariance
public import MathFin.Risk.ContractRisk
public import MathFin.Risk.GaussianRiskMarkowitz
public import MathFin.Risk.EquicorrelationConcentration
public import MathFin.Risk.SquareRootOfTime
-- Component VaR (the Euler decomposition of portfolio VaR) and the single-index covariance
-- structure with its large-N limit
public import MathFin.Risk.ComponentVaR
public import MathFin.Risk.Credit.CreditRiskPlus
public import MathFin.Risk.Credit.OneFactorCopula
public import MathFin.Risk.Credit.OneFactorMerton

-- Choice
public import MathFin.Choice.Portfolio.Markowitz
public import MathFin.Choice.Portfolio.CovariancePSD
public import MathFin.Choice.Portfolio.MarkowitzNAsset
public import MathFin.Choice.Portfolio.CAPM
public import MathFin.Choice.Portfolio.TwoFundSeparation
public import MathFin.Choice.Portfolio.RiskParity
public import MathFin.Choice.Portfolio.BlackLitterman
public import MathFin.Choice.Portfolio.TangentPortfolio
-- Phase 13 additions:
-- Phase 21: first-principles Sharpe-FOC and CAPM-equilibrium derivations
public import MathFin.Choice.Portfolio.SharpeFOCDerivation
public import MathFin.Choice.Portfolio.CAPMEquilibrium
public import MathFin.Choice.Portfolio.StochasticDiscountFactor
public import MathFin.Choice.Portfolio.MarketSDF
-- Phase 23: N-asset Markowitz Lagrangian FOC (forward direction)
public import MathFin.Choice.Portfolio.MarkowitzLagrangian
-- Phase 26: N-asset risk parity from log-barrier Lagrangian FOC
public import MathFin.Choice.Portfolio.RiskParityFOC
-- Phase 29: N-dim Black-Litterman posterior (matrix form)
public import MathFin.Choice.Portfolio.BlackLittermanND
-- Convex QP KKT sufficiency/uniqueness and a feasible-ratio-test step bound
public import MathFin.Choice.Portfolio.ConvexQPKKT
-- PSD-form Cauchy–Schwarz and the mean–standard-deviation tradeoff at a mean–variance KKT point
public import MathFin.Choice.Portfolio.PosSemidefCauchySchwarz
public import MathFin.Choice.Performance.Ratios
public import MathFin.Choice.Performance.RatiosExtended
public import MathFin.Choice.Performance.DownsideMetrics
public import MathFin.Choice.Performance.RelativeDrawdown
public import MathFin.Choice.Performance.Kelly
public import MathFin.Choice.Performance.KellyNumeraire
public import MathFin.Choice.Performance.FracDiffWeights
public import MathFin.Choice.Performance.LabelUniqueness
public import MathFin.Choice.Performance.BetSizeSigmoid
public import MathFin.Choice.Performance.PurgedCV
-- The layer beneath UtilityDerivation, which takes the expected-utility form as given:
-- von Neumann-Morgenstern lotteries, the mixture algebra, affinity of expected utility in
-- the mixture, and the vNM axioms verified for the induced preference (the soundness half,
-- plus invariance of the preference under positive affine rescaling of the utility)
public import MathFin.Choice.Utility.VonNeumannMorgenstern
public import MathFin.Choice.Utility.StatePriceDensity
public import MathFin.Choice.Utility.MarketMarginalUtility
-- QRM bridges: equicorrelation, Gaussian VaR/ES-optimal = Markowitz portfolios, the HHI
-- systematic floor, and the square-root-of-time rule for GBM losses
public import MathFin.Choice.Portfolio.Equicorrelation
public import MathFin.Choice.Portfolio.SingleIndexModel
public import MathFin.Choice.Portfolio.RegressionBeta

-- Insurance
public import MathFin.Insurance.StandardDeviationPrinciple
public import MathFin.Insurance.SurvivalUnification
public import MathFin.Insurance.Insurance
public import MathFin.Insurance.Mortality
-- Survival model (re-formalized from Yosuke Ito's AFP `Survival_Model`, BSD, cited)
public import MathFin.Insurance.SurvivalModel
public import MathFin.Insurance.ActuarialInsurance
public import MathFin.Insurance.AnnuityValue
public import MathFin.Insurance.BuhlmannCredibility
-- The chain ladder and Mack's model: the completion is the prediction by the selected factors,
-- and under Mack's model the predictions of the ultimate are a martingale
public import MathFin.Insurance.ChainLadder
public import MathFin.Insurance.EsscherPremium

-- Markets
public import MathFin.Markets.Execution.AlmgrenChriss
public import MathFin.Markets.Microstructure.MarketMakingRiccati
public import MathFin.Markets.Microstructure.MatrixMarketMakingRiccati
-- Phase 38: Constant-product AMM (adapted from Pusceddu-Bartoletti FMBC 2024)
public import MathFin.Markets.DeFi.ConstantProductAMM
-- Constant-mean (Balancer) AMM: the weighted-product invariant generalizing the pool above
public import MathFin.Markets.DeFi.ConstantMeanAMM
-- the constant-mean LP position as a payoff, priced (the bridge into the payoff language)
public import MathFin.Markets.DeFi.ConstantMeanLPContract
-- DeFi/AMM group: Uniswap v2/v3 mechanics (impermanent loss, TWAP, fee invariant, v3 real reserves)
public import MathFin.Markets.DeFi.UniswapMechanics
-- DeFi/lending group: Aave kinked-rate + health factor, Compound cToken exchange rate
public import MathFin.Markets.DeFi.Aave
public import MathFin.Markets.DeFi.Compound
-- Dai stability fee and vault liquidation condition
public import MathFin.Markets.DeFi.Dai
-- Execution: market microstructure — the Glosten-Milgrom adverse-selection
-- spread, plus a six-point model witnessing that its hypotheses are satisfiable
public import MathFin.Markets.Microstructure.GlostenMilgrom
public import MathFin.Markets.Microstructure.GlostenMilgromModel
public import MathFin.Markets.Microstructure.RollSpread
public import MathFin.Markets.DeFi.ConstantProductLPLognormal
public import MathFin.Markets.DeFi.LiquidationAsStructuralDefault
public import MathFin.Markets.DeFi.UniswapV3CoveredCallPrice
public import MathFin.Markets.DeFi.LPContract
public import MathFin.Markets.Microstructure.GlostenMilgromCondExp
public import MathFin.Markets.Microstructure.GlostenMilgromMarket
public import MathFin.Markets.Microstructure.GlostenMilgromSequential
-- Contributed 2026-11 (#432–#467): lattices, smile interpolation and quoting, SABR Greeks,
-- lookback and shout options, Marchenko–Pastur edges, concentrated-liquidity VaR
public import MathFin.Models.Binomial.TrinomialMomentMatching
public import MathFin.Models.Binomial.WillowTree
public import MathFin.Models.ModelFree.CallPriceInterpolation
public import MathFin.Models.ModelFree.CubicSplineSmile
public import MathFin.Markets.FxSmileQuotes
public import MathFin.Models.ModelFree.SABRChainRuleGreeks
public import MathFin.Models.BlackScholes.ContinuousLookbackPricing
public import MathFin.Models.BlackScholes.ShoutFloorMonotonicity
public import MathFin.Choice.Performance.MarchenkoPasturEdge
public import MathFin.Markets.DeFi.ConcentratedLiquidityVaR
public import MathFin.Models.ModelFree.BlackFormTail
