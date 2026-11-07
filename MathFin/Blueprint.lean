/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

import MathFin.Foundations.QuadraticVariationL2
import MathFin.Foundations.WienerIntegralL2
import MathFin.Foundations.ItoIsometryAdapted
import MathFin.Foundations.ItoIntegralCLM
import MathFin.Foundations.BracketCompensator
import MathFin.Foundations.ItoIntegralBrownian
import MathFin.Foundations.DiscreteIto
import MathFin.Foundations.ItoFormulaSquaredL2
import MathFin.Foundations.ItoFormulaCLM
import MathFin.Foundations.ItoFormulaTD
import MathFin.Foundations.ItoLemma2D
import MathFin.Foundations.FeynmanKacHeatEquation
import MathFin.Bridges.GaussianGirsanov
import MathFin.Bridges.BSCallHypFromBrownian
import MathFin.Foundations.ContinuousFTAP
import MathFin.Foundations.MarketCompleteness
import MathFin.Foundations.CarrMadan
import MathFin.BlackScholes.Call
import MathFin.BlackScholes.PDE
import MathFin.BlackScholes.PDEFromIto
import MathFin.BlackScholes.PDEFromFeynmanKac
import MathFin.BlackScholes.MargrabeGrounding
import MathFin.Binomial.MartingaleRepresentation
import MathFin.Binomial.CRRCharFun
import MathFin.Binomial.CRRClosedForm
import MathFin.BlackScholes.MertonDominance
import MathFin.Foundations.MarkovPathMeasure
import MathFin.Foundations.ItoFormulaAdaptedProcess
import MathFin.Futures.SchwartzOneFactor
import MathFin.FixedIncome.CVA
import MathFin.FixedIncome.FxForwardParity
import MathFin.BlackScholes.JumpDiffusionProcess
import MathFin.BlackScholes.JumpDiffusionVarianceSwap
import Architect

/-!
# Blueprint spine — post-hoc `@[blueprint]` tagging

Declares the blueprint nodes of the deductive spine (`docs/blueprint.md`) by
tagging existing declarations **post hoc** with LeanArchitect's
`attribute [blueprint …]`. The tags live HERE, in a leaf module nothing
imports, so the proof modules are untouched: their sources keep their
verification-ledger hashes (zero restale), and the spine's dependency edges
are *inferred from the proof terms* (`Architect.collectUsed` — a transitive
walk that stops at tagged constants, so edges pass through untagged helpers).
The graph in `docs/blueprint.md` is generated ground truth, never hand-drawn.

Regenerate after touching the spine:

  `lake build MathFin.Blueprint && lake exe blueprint_export MathFin.Blueprint`
  then `python3 tools/blueprint_render.py` (see that file's header).

Node prose lives in `(statement := …)`: one honest sentence per node — what
the mathematics says, with deferrals named, never papered over.
-/

@[expose] public section

-- ===== root: the driving noise (upstream — Mathlib) =====

attribute [blueprint "def:brownian-motion" (title := "Brownian motion (Mathlib, upstream)")
  (statement := /-- The driving noise: independent stationary Gaussian increments,
  $B_t \sim N(0,t)$ — `IsPreBrownianReal`, now in Mathlib. Rémy Degenne's
  `brownian-motion` package, on which this library also builds, supplies the
  continuous modification and the filtered versions. -/)]
  ProbabilityTheory.IsPreBrownianReal

-- ===== foundations =====

attribute [blueprint "thm:quadratic-variation" (title := "Quadratic variation: ∑(ΔB)² → T in L²")
  (statement := /-- Along the uniform partition of $[0,T]$ into $n$ pieces,
  $\sum_k (B_{t_{k+1}}-B_{t_k})^2 \to T$ in $L^2$ at rate $2T^2/n$: realized variance accumulates linearly in time at unit rate — the
  root of the "$\sigma^2 \cdot$ time" that pervades pricing. -/)]
  MathFin.QuadraticVariationL2.tendsto_qv

attribute [blueprint "thm:wiener-isometry" (title := "Wiener isometry (deterministic L²)")
  (statement := /-- For deterministic step integrands,
  $E[(\int \varphi\,dB)^2] = \int \varphi^2\,dt$: the $L^2$ geometry of a fixed
  (non-reacting) position in Brownian noise. -/)]
  MathFin.WienerIntegralL2.wiener_assembly_isometry

attribute [blueprint "thm:ito-isometry-adapted" (title := "Adapted Itô isometry")
  (statement := /-- For random *adapted* simple integrands,
  $E[(\sum_k \varphi_k \Delta B_k)^2] = \sum_k E[\varphi_k^2]\,\Delta t_k$ — the
  cross terms vanish by the weak Markov property, the exact point where Itô
  departs from Wiener. -/)]
  MathFin.ItoIsometryAdapted.ito_isometry_discrete

attribute [blueprint "def:ito-integral-clm" (title := "Continuous Itô integral (CLM on [0,T])")
  (statement := /-- The discrete isometry extended to a continuous linear isometry
  on predictable $L^2$ integrands over $[0,T]$, via density of simple processes
  (Dynkin π-λ on predictable rectangles) and `LinearMap.extendOfNorm`. -/)]
  MathFin.ItoIntegralCLM.itoIntegralCLM

attribute [blueprint "thm:ito-integral-brownian" (title := "∫₀ᵀ B dB = ½(B_T² − B₀² − T)")
  (statement := /-- The CLM's first genuine consumer: $\int_0^T B\,dB$ computed
  *through the abstract integral*, agreeing with the quadratic-variation limit —
  the clamp-truncation + isometry-Cauchy template any unbounded-coefficient
  consumer would reuse. -/)]
  MathFin.ItoIntegralBrownian.itoIntegralCLM_brownian

attribute [blueprint "thm:discrete-ito" (title := "Discrete Itô formula (pathwise)")
  (statement := /-- The exact pathwise identity
  $f(X_N) - f(X_0) = \sum f'(X_k)\Delta X_k + \tfrac12 \sum f''(X_k)(\Delta X_k)^2
  + \sum R_k$ — Itô's lemma before any limit is taken. -/)]
  MathFin.discrete_ito_formula

attribute [blueprint "thm:ito-squared-l2" (title := "Itô for x² in L²: ∑B·ΔB → ½(B_T²−B₀²−T)")
  (statement := /-- The continuous $L^2$ form for $x^2$: Riemann sums of
  $B\,dB$ converge along the uniform partition — one algebraic step from the
  discrete identity plus the $L^2$ quadratic variation. The
  $B_t^2 = 2\int B\,dB + t$ keystone behind variance-swap pricing. -/)]
  MathFin.itoSquared_L2_tendsto_div2

attribute [blueprint "thm:ito-formula-l2" (title := "Itô formula, L² (C³ bounded — Summit A)")
  (statement := /-- The continuous-time $L^2$ Itô formula
  $f(B_T) - f(B_0) = \int_0^T f'(B_s)\,dB_s + \tfrac12\int_0^T f''(B_s)\,ds$ for
  $C^3$ functions with bounded derivatives, proved from primitives (weighted QV,
  Taylor remainder, Riemann↔CLM bridge). Unbounded coefficients (e.g. GBM's
  exponential) are honestly out of scope — the named gap. -/)]
  MathFin.ito_formula_L2_bddDeriv

attribute [blueprint "thm:ito-formula-td-l2" (title := "Time-dependent Itô formula, L² (Summit A′)")
  (statement := /-- The classical $df = f_x\,dB + (f_t + \tfrac12 f_{xx})\,dt$ in
  integrated $L^2$ form: $f(T,B_T) - f(0,B_0) = \int_0^T f_x(s,B_s)\,dB_s
  + \int_0^T (f_t + \tfrac12 f_{xx})(s,B_s)\,ds$ for $C^{1,2}$ functions with bounded
  higher partials — the time-dependent extension of Summit A, with the drift Riemann
  term as the third vanishing limit and the joint continuity of $f_t$ *derived* from
  its bounded partials. Unbounded coefficients stay out of scope — the named gap. -/)]
  MathFin.ito_formula_td_L2_bddDeriv

attribute [blueprint "thm:expectation-ito" (title := "Expectation-form Itô / Feynman–Kac")
  (statement := /-- For $f$ with $f, f', f''$ bounded and $f''$ continuous,
  $E[f(B_t)] = f(0) + \tfrac12 \int_0^t E[f''(B_s)]\,ds$, proved
  via the heat equation: the $\tfrac12\sigma^2$ second-order term that drives the
  Black–Scholes PDE. -/)]
  MathFin.FeynmanKacHeatEquation.expectation_ito

attribute [blueprint "thm:gbm-sde" (title := "GBM coefficient matching (algebraic)")
  (statement := /-- $S(t,B_t)$ with $S = S_0 e^{(\mu-\sigma^2/2)t+\sigma x}$ matches
  the Itô coefficients of $dS = \mu S\,dt + \sigma S\,dB$: genuine `HasDerivAt`
  partials + the 2D Itô drift. Honestly *coefficient matching*, not a continuous
  SDE-solution theorem — the $-\sigma^2/2$ cancellation IS the Itô correction. -/)]
  MathFin.gbm_solves_sde

attribute [blueprint "thm:ito-formula-c2" (title := "Itô's formula for C² functions")
  (statement := /-- For an Itô process $X = x_0 + \int b\,ds + \int \sigma\,dB$ with adapted
  continuous coefficients (no boundedness) and $f(t,x)$ with jointly continuous $f_t$, $f_x$,
  $f_{xx}$, almost surely for every $t \in [0,T]$ at once
  $f(t,X_t) = f(0,x_0) + \int_0^t (f_t + f_x b + \tfrac12 f_{xx}\sigma^2)(s,X_s)\,ds
  + \bigl(\int f_x(\cdot,X)\,\sigma\,dB\bigr)_t$, the stochastic integral being the
  localised predictable Itô integral. The textbook $C^2$ scope, as an identity of
  processes. -/)]
  MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_process

-- ===== change of measure — the centerpiece =====

attribute [blueprint "thm:esscher-tilt" (title := "Esscher tilt is the Gaussian Girsanov")
  (statement := /-- Tilting the physical Gaussian by an exponential density yields
  an equivalent probability measure with shifted mean — static Girsanov,
  constructed, not assumed. -/)]
  MathFin.hasLaw_esscher_tilt

attribute [blueprint "thm:girsanov-call"
  (title := "Call price under an Esscher-tilted Gaussian (static Girsanov)")
  (statement := /-- For a standard normal $W$ under $P$ and any shift $c$, the tilt
  $Q = P\,e^{cW - c^2/2}$ makes $W - c$ standard normal, so the call on
  $S_0 e^{(r-\sigma^2/2)T + \sigma\sqrt T (W - c)}$ is worth the Black–Scholes closed form
  under $Q$. One date, Gaussian shift only. With $c = (r-\mu)\sqrt T/\sigma$ the same tilt
  reprices the physical-drift asset to $S_0$ (`discounted_physical_terminal_eq_S0`); the call
  formula for the physical-drift asset is not stated separately. -/)]
  MathFin.bs_call_formula_of_physical

attribute [blueprint "thm:bscallhyp-brownian" (title := "BSCallHyp from a Brownian model")
  (statement := /-- A concrete Brownian-driven physical model produces the pricing
  hypothesis directly — the second route into `BSCallHyp`. -/)]
  MathFin.BSCallHyp.of_isPreBrownian

attribute [blueprint "thm:continuous-ftap"
  (title := "Discounted risk-neutral GBM is a martingale (EMM property)")
  (statement := /-- Under the risk-neutral measure the discounted price
  $e^{-rt}S_t$ is a continuous-time martingale, straight from the Wald
  exponential — the defining EMM property, with no stochastic-integral
  machinery. It is not a continuous-time FTAP: only "an EMM precludes arbitrage by
  simple strategies" is proved, and the converse is not. -/)]
  MathFin.discountedGBM_isMartingale

attribute [blueprint "thm:martingale-representation"
  (title := "Martingale representation (terminal form)")
  (statement := /-- Every square-integrable $\mathcal{F}^B_T$-measurable claim is its
  own mean plus an Itô integral, $F = E[F] + \int_0^T \varphi\,dB$, for a *unique*
  integrand $\varphi$. The Itô isometry's range is closed, hence orthogonally
  complemented; the remainder of the decomposition is centered and
  $\mathcal{F}^B_T$-measurable, so it is orthogonal to every step-integrand Doléans
  exponential, and Wiener-exponential totality kills it. Uniqueness is injectivity of an
  isometry. -/)]
  MathFin.exists_itoIntegral_representation

attribute [blueprint "thm:martingale-representation-process"
  (title := "Martingale representation (process form)")
  (statement := /-- Every square-integrable martingale on the Brownian filtration is its
  initial value plus an Itô integral process, $M_t = M_0 + (\varphi\cdot B)_t$ for
  $t \le T$. The terminal form supplies the integrand; the martingale property spreads it
  over the horizon, because $(\varphi\cdot B)_t$ is the $\mathcal{F}_t$-conditional
  expectation of $\int_0^T\varphi\,dB$. That $M_0$ is a.e. constant is not assumed — it is
  the representation read at $t = 0$. -/)]
  MathFin.martingale_representation

attribute [blueprint "thm:market-completeness" (title := "Completeness of the Brownian market")
  (statement := /-- Every square-integrable $\mathcal{F}^B_T$-claim is replicated from
  initial wealth $E_\mu[H]$ by a unique Itô-integrable strategy — the representation
  theorem read as a trading statement, the integrand *being* the hedge. The strategy class
  is the predictable $L^2$ integrands (piecewise-constant holdings could not hedge a
  general $L^2$ claim), and the traded gain is the integral against $B$ itself: the
  stochastic integral $\int\varphi\,dS$ against a general price is absent by design. -/)]
  MathFin.exists_replicating_strategy

attribute [blueprint "thm:pricing-measure" (title := "The pricing measure on 𝓕ᴮ_T is unique")
  (statement := /-- A probability measure $Q \ll \mu$ that prices the traded Itô gains at
  zero agrees with $\mu$ on all of $\mathcal{F}^B_T$: replicate an event's indicator, and
  only the initial wealth $\mu(A)$ survives. This is *not* the unconditional second FTAP.
  Gains-neutrality is a hypothesis, not a consequence of $Q$ being a martingale measure for
  a price $S$ — the wealth built here is an integral against $B$, and nothing in
  $\mathrm{IsEMM}\,S\,Q$ makes that a $Q$-fair game. The hypothesis is guarded: $\mu$
  satisfies it, and the textbook gains-martingale condition implies it. Only
  complete $\Rightarrow$ unique is proved; the Jacod–Yor converse is out of scope. For a
  price $S = S_0 + \int \sigma\,dB$ with $\sigma \ne 0$ a.e. and $Q$ with a square-integrable
  density, the hypothesis does follow from $S$ being a $Q$-martingale
  (`measure_eq_of_density`). -/)]
  MathFin.measure_eq_of_pricesGainsAtZero

-- ===== pricing =====

attribute [blueprint "thm:bs-call" (title := "Black–Scholes call formula")
  (statement := /-- Under `BSCallHyp`, the call price is
  $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$. -/)]
  MathFin.bs_call_formula

attribute [blueprint "thm:bs-identity" (title := "bs_identity: S·φ(d₁) = Ke^{−rτ}·φ(d₂)")
  (statement := /-- The algebraic collapse that cancels the pdf cross-terms —
  a self-contained root (only the $d_1/d_2$ definitions and the Gaussian
  density), feeding every clean Greek formula and the PDE. -/)]
  MathFin.bs_identity

attribute [blueprint "thm:bs-delta" (title := "Greeks (δ shown; γ vega θ ρ alongside)")
  (statement := /-- $\partial V/\partial S = \Phi(d_1)$ — delta, the hedge ratio;
  representative of the five Greeks ($\delta, \gamma, \text{vega}, \theta, \rho$),
  each a real `HasDerivAt` derivation through `bs_identity`. -/)]
  MathFin.hasDerivAt_bsV_S

attribute [blueprint "thm:bs-pde" (title := "Black–Scholes PDE (from the closed form)")
  (statement := /-- The closed-form price satisfies
  $\theta + rS\delta + \tfrac12\sigma^2S^2\gamma - rV = 0$, verified through the
  Greeks and `bs_identity`. -/)]
  MathFin.bs_pde_holds

attribute [blueprint "thm:bs-pde-brownian" (title := "BS PDE in the Brownian coordinate")
  (statement := /-- The discounted call price read along the Brownian state,
  $f(t,x) = e^{-rt}\,V(S_0 e^{(r-\sigma^2/2)t + \sigma x},\,T-t)$, solves the backward heat
  equation $\partial_t f + \tfrac12\partial_{xx} f = 0$ for $t < T$, from the Feynman–Kac
  heat-flow form of the price. That $f(t, B_t)$ is then a local martingale is not proved. -/)]
  MathFin.discountedCallBrownian_heat_equation

attribute [blueprint "thm:feynman-kac-heat-eq" (title := "Heat equation for the kernel convolution")
  (statement := /-- The convolution $u(t,x) = \int g(z)\,K(t,z-x)\,dz$ against the
  Gaussian heat kernel solves $\partial_t u = \tfrac12\partial_{xx}u$, from the
  kernel identity $\partial_t K = \tfrac12\partial_{yy}K$ and differentiation under
  the integral — `g` need only be continuous and growth-controlled, so the call's
  kink is never differentiated. -/)]
  MathFin.FeynmanKacHeatEquation.feynmanU_heat_equation

attribute [blueprint "thm:bs-pde-feynman-kac" (title := "Black–Scholes PDE (from Feynman–Kac)")
  (statement := /-- The closed-form price's actual derivatives satisfy
  $-\partial_\tau V + \tfrac12\sigma^2 S^2\partial_{SS}V + rS\partial_S V - rV = 0$,
  derived *independently of Itô* from the heat-kernel representation: the kernel's
  joint Fréchet-differentiability feeds the three Greeks, and the heat equation
  $\partial_t u = \tfrac12\partial_{xx}u$ plus exact drift cancellation assembles
  the PDE — the second, probabilistically-grounded tower closing the two-tower gap. -/)]
  MathFin.bsV_satisfies_bs_pde_via_feynmanKac

attribute [blueprint "thm:margrabe" (title := "Margrabe exchange option")
  (statement := /-- For two geometric Brownian motions with correlated Gaussian drivers, the
  discounted expected exchange payoff $\mathbb E[e^{-rT}(S^1_T - S^2_T)^+]$ equals Margrabe's
  price: a Black–Scholes call on the ratio at effective volatility
  $\sqrt{\sigma_1^2 + \sigma_2^2 - 2\rho\sigma_1\sigma_2}$, by splitting off an independent
  residual. -/)]
  MathFin.margrabe_exchange_price

attribute [blueprint "thm:carr-madan" (title := "Carr–Madan static replication")
  (statement := /-- A payoff $f$ twice differentiable on $[L,U]$ with continuous $f''$
  decomposes, at every spot in $[L,U]$, as cash, a forward, and a static book of OTM
  options on the strikes in $[L,U]$ weighted by its convexity $f''$ — one integration by
  parts plus a positive-part case split. The unbounded-strike form is not proved. The log payoff
  specializes to the variance-swap $1/K^2$ strip. -/)]
  MathFin.carrMadan_spanning

attribute [blueprint "thm:binomial-representation"
  (title := "Binomial martingale representation (completeness)")
  (statement := /-- On the binomial tree every martingale is the discrete
  stochastic integral of a *predictable* hedge: $H = \Delta M/\Delta S$, fixed
  before the flip — completeness, the second pillar of the FTAP. The martingale
  is Mathlib's, for the natural filtration of the flips; the conditional
  expectation is the node average, so the proof is the one-period delta hedge,
  telescoped. -/)]
  MathFin.binomial_martingale_representation

attribute [blueprint "thm:crr-bs-convergence" (title := "CRR → Black–Scholes convergence")
  (statement := /-- When every $n$-step tree is arbitrage-free, the binomial call price
  converges to the Black–Scholes closed form $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$:
  charFun → Lévy continuity → weak convergence, with put–call parity lifting the
  (bounded) put's convergence to the call. -/)]
  MathFin.binomialPrice_call_tendsto_bs_closed

attribute [blueprint "thm:merton-dominance" (title := "Merton call price dominates Black–Scholes at the diffusion vol")
  (statement := /-- The Merton (1976) jump-diffusion call price dominates the
  Black–Scholes price at the diffusion vol, for every intensity, mean jump
  size $k > -1$, and jump vol: vega prices the jump-size channel (conditional
  vols exceed $\sigma$), gamma prices the jump-count channel — spot convexity
  gives a supporting tangent at $S_0$ whose linear term integrates to zero by
  the compensation identity $E[\mathrm{spot}_N] = S_0$. -/)]
  MathFin.bsV_le_mertonCallPrice

attribute [blueprint "thm:markov-path-law" (title := "Markov path law (Ionescu–Tulcea)")
  (statement := /-- The law of a countable-state Markov chain, constructed on
  infinite trajectories by Mathlib's Ionescu–Tulcea trajectory kernels from
  kernels reading only the last history coordinate; the finite-path
  factorization $P(X_0{=}i_0,\dots,X_n{=}i_n) = \mathrm{init}(i_0)\prod_k
  P(i_k,i_{k+1})$ is derived by induction through the comp-product recursion
  of the marginals (Saporito 1.1.2). -/)]
  MathFin.markovPathMeasure_cylinder

attribute [blueprint "thm:conditional-bracket" (title := "The bracket is conditional")
  (statement := /-- For the Itô integral process $M = \varphi\bullet B$ on $[0,T]$ and
  $a \le b \le T$, the conditional second moment of an increment is the conditional
  expectation of the pathwise bracket increment,
  $\mathbb{E}[(M_b-M_a)^2 \mid \mathcal{F}_a] = \mathbb{E}[\langle M\rangle_b -
  \langle M\rangle_a \mid \mathcal{F}_a]$, with $\langle M\rangle_b - \langle M\rangle_a
  = \int_a^b \varphi_u(\omega)^2\,du$ taken $\omega$-wise. The proof is the Itô isometry
  localised on an $\mathcal{F}_a$-set: $\mathbb{1}_F$ is a bounded $\mathcal{F}_a$-measurable
  factor, so it folds back inside a single Itô integral and squaring it costs nothing. -/)]
  MathFin.PointwiseBracket.condExp_band_second_moment

attribute [blueprint "thm:bracket-compensator"
  (title := "The bracket compensates the square")
  (statement := /-- $M^2 - \langle M\rangle$ is a martingale:
  $\mathbb{E}[M_b^2 - \langle M\rangle_b \mid \mathcal{F}_a] = M_a^2 - \langle M\rangle_a$
  for $a \le b \le T$. Expanding $(M_b-M_a)^2$, the cross term collapses by the martingale
  property of $M$, and the bracket increment splits off the conditional expectation because
  $\langle M\rangle_a$ is adapted — which holds because the predictable $\sigma$-algebra,
  traced onto a band $(a,b]\times\Omega$, is $\mathcal{B}(\mathbb{R}_{\ge 0})\otimes
  \mathcal{F}_b$-measurable. -/)]
  MathFin.BracketCompensator.condExp_sq_sub_bracket

attribute [blueprint "thm:merton-risk-neutral-drift"
  (title := "Jump-diffusion risk-neutral drift")
  (statement := /-- For a jump-diffusion $X$ with drift $b$, volatility $\sigma$, jump
  intensity $\Lambda$ and a jump law $\nu$ with $\mathbb{E}[e^J] < \infty$, and
  $S_0 \ne 0$, the discounted price $e^{-rt}S_0e^{X_t}$ is a martingale if and only if
  $b = r - \sigma^2/2 - \Lambda(\mathbb{E}[e^J] - 1)$. Merton's log-normal jumps have
  $\mathbb{E}[e^J] - 1 = \kappa$ (`integral_exp_mertonJump`), the compensation
  $r - \lambda\kappa$. -/)]
  MathFin.JumpDiffusionProcess.martingale_iff

attribute [blueprint "thm:variance-swap-jump-bias" (title := "Variance-swap jump bias")
  (statement := /-- At the compensated drift, the Demeterfi–Derman–Kamal–Zou log contract on
  the forward, scaled as a variance rate, has expected payoff
  $\sigma^2 + 2\Lambda\,\mathbb{E}[e^J - 1 - J]$ under the jump-diffusion increment law
  (jump law with $\mathbb{E}[e^J] < \infty$ and exponential moments near $0$). Without
  jumps it is $\sigma^2$, the Black–Scholes fair strike. -/)]
  MathFin.jumpDiffusion_logContract

attribute [blueprint "thm:schwartz-commodity-futures" (title := "Schwartz commodity futures")
  (statement := /-- With the log spot in its Ornstein–Uhlenbeck Wiener representation
  $\ln S_T = m_T + \sigma\int_0^T e^{-\kappa(T-s)}\,dB_s$ and $\kappa > 0$, the expected
  terminal spot is the closed form $\exp(m_T + v_T/2)$. The modelling bridge from the
  SDE to that representation is cited, not proved here. -/)]
  MathFin.schwartzFuturesPrice_eq_integral

attribute [blueprint "thm:interest-rate-parity"
  (title := "Covered and uncovered interest-rate parity")
  (statement := /-- In a finite-state market pricing the domestic bond at $e^{-r_dT}$ and the
  foreign bond, in domestic currency, at $Se^{-r_fT}$, the forward priced to zero is
  $F = Se^{(r_d-r_f)T}$; under the Garman–Kohlhagen risk-neutral measure it is also the
  expected terminal spot. A statement about the pricing measure, not the physical one. -/)]
  MathFin.covered_eq_uncovered_interest_parity

attribute [blueprint "thm:unilateral-cva" (title := "Unilateral CVA, Gaussian exposure")
  (statement := /-- With exposure $V_s = m(s) + \sigma(s)\sqrt s\,Z$, $Z \sim N(0,1)$,
  independent of a default time with continuous hazard $h \ge 0$ (no wrong-way risk), and
  $D$, $m$, $\sigma$ measurable and bounded with $\sigma > 0$:
  $\mathrm{CVA} = \mathrm{LGD}\int_0^T D(s)\,[m(s)\Phi(d_s) + \sigma(s)\sqrt s\,
  \varphi(d_s)]\,h(s)Q(s)\,ds$, $d_s = m(s)/(\sigma(s)\sqrt s)$. Only the marginal laws of
  the exposure enter; no exposure dynamics are modelled. -/)]
  MathFin.CVA.cva_gaussian
