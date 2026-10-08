/-
  GENERATED FILE — do not edit by hand.

  Exhaustive axiom audit: every constant declared in MathFin/ that a benchmark
  snippet's proof cites is #guard_msgs-pinned to its exact axiom set, so no
  benchmark-cited theorem can pick up `sorryAx` (a `sorry`) or a non-standard
  axiom without breaking `lake build`.

  The curated, storied audit is MathFin/AxiomAudit.lean (headliners + dated
  narrative); THIS file is its machine-written closure over the benchmark
  corpus (523 MathFin constants, 29 upstream). Citations
  are resolved by declaration (tools/verify/mathfin_index.py), so a name cited
  unqualified under `open`, by dot notation on a hypothesis, or declared
  outside the MathFin namespace is pinned like any other. Statement-position
  defs are exercised by elaboration + the verification ledger. The second
  section pins the Mathlib and BrownianMotion constants that library_wrapper
  entries cite (UPSTREAM_CITATIONS in the generator).

  Regenerate:  python3 -m tools.verify.axiom_audit_gen --write
  Freshness:   tests/test_values.py::test_axiom_audit_gen_is_fresh
  (Excluded from CI kernel replay like AxiomAudit: whole-library closure.)
-/
import MathFin
import BrownianMotion.Gaussian.BrownianMotion
import BrownianMotion.StochasticIntegral.DoobLp
import BrownianMotion.StochasticIntegral.LocalMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing

namespace MathFin.AxiomAuditGen

/-- info: 'MathFin.AdaptedQuadraticVariation.tendsto_qv_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedQuadraticVariation.tendsto_qv_adapted

/-- info: 'MathFin.AdaptedQuadraticVariation.tendsto_weighted_qv_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedQuadraticVariation.tendsto_weighted_qv_adapted

/-- info: 'MathFin.AdaptedRiemannStieltjes.coeFn_mulLI_weightLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedRiemannStieltjes.coeFn_mulLI_weightLp

/-- info: 'MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_stepσ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_stepσ

/-- info: 'MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_weightLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_weightLp

/-- info: 'MathFin.AdaptedRiemannStieltjes.tendsto_integral_sq_riemannStieltjes_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedRiemannStieltjes.tendsto_integral_sq_riemannStieltjes_sub

/-- info: 'MathFin.AdaptedRiemannStieltjes.tendsto_itoIntegralAgainst_stepσ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.AdaptedRiemannStieltjes.tendsto_itoIntegralAgainst_stepσ

/-- info: 'MathFin.BivariateGaussianHyp.conditional_expectation_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BivariateGaussianHyp.conditional_expectation_formula

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualLogBoundary_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualLogBoundary_convexOn

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualStockBoundary_strictConvexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualStockBoundary_strictConvexOn

/-- info: 'MathFin.BracketCompensator.condExp_sq_sub_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BracketCompensator.condExp_sq_sub_bracket

/-- info: 'MathFin.BrownianQuadraticVariation.qv_equals_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BrownianQuadraticVariation.qv_equals_t

/-- info: 'MathFin.Btheta_isQBrownianMotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Btheta_isQBrownianMotion

/-- info: 'MathFin.Btheta_isQBrownianMotion_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Btheta_isQBrownianMotion_adapted

/-- info: 'MathFin.Btheta_isQBrownianMotion_predictable_of_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Btheta_isQBrownianMotion_predictable_of_bdd

/-- info: 'MathFin.Btheta_map_eq_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Btheta_map_eq_gaussianReal

/-- info: 'MathFin.Btheta_simple_isQBrownianMotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Btheta_simple_isQBrownianMotion

/-- info: 'MathFin.ContinuousMarket.isEMM_noArbitrageSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ContinuousMarket.isEMM_noArbitrageSimple

/-- info: 'MathFin.ContinuousMarket.martingale_comp_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ContinuousMarket.martingale_comp_monotone

/-- info: 'MathFin.Contracts.Contract.pathPV_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.Contract.pathPV_both

/-- info: 'MathFin.Contracts.Contract.value_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.Contract.value_both

/-- info: 'MathFin.Contracts.Contract.value_deliverAsset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.Contract.value_deliverAsset

/-- info: 'MathFin.Contracts.Payoff.measurable_eval_of_obsTimes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.Payoff.measurable_eval_of_obsTimes_le

/-- info: 'MathFin.Contracts.cappedCall_payoff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.cappedCall_payoff_eq

/-- info: 'MathFin.Contracts.value_cappedCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.value_cappedCall

/-- info: 'MathFin.Contracts.value_digitalCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.value_digitalCall

/-- info: 'MathFin.Contracts.value_europeanCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.value_europeanCall

/-- info: 'MathFin.Contracts.value_europeanPut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Contracts.value_europeanPut

/-- info: 'MathFin.ErlangSum.sum_iidExp_law_gammaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ErlangSum.sum_iidExp_law_gammaMeasure

/-- info: 'MathFin.Execution.spread_pos_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Execution.spread_pos_of_model

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanKac_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.FeynmanKacHeatEquation.feynmanKac_boundary

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanU_eq_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.FeynmanKacHeatEquation.feynmanU_eq_expectation

/-- info: 'MathFin.IsCopula.sum_sub_le_measureReal_Iic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.IsCopula.sum_sub_le_measureReal_Iic

/-- info: 'MathFin.IsL2SolutionPair.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.IsL2SolutionPair.uniqueness

/-- info: 'MathFin.ItoFormulaAdapted.adaptedItoProcess_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoFormulaAdapted.adaptedItoProcess_ae_eq

/-- info: 'MathFin.ItoFormulaAdapted.ae_continuousOn_adaptedItoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoFormulaAdapted.ae_continuousOn_adaptedItoProcess

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted

/-- info: 'MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_elementary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_elementary

/-- info: 'MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_eq_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_eq_itoIntegral

/-- info: 'MathFin.ItoIntegralCovariation.covariation_itoIntegralCLM_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralCovariation.covariation_itoIntegralCLM_T

/-- info: 'MathFin.ItoIntegralL2.itoIntegralL2_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralL2.itoIntegralL2_norm

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcessLp_l2_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcessLp_l2_continuous

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isLocalMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isLocalMartingale

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isMartingale

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isometry_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isometry_time

/-- info: 'MathFin.ItoIntegralProcess.memLp_itoSimpleProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.memLp_itoSimpleProcess

/-- info: 'MathFin.ItoIntegralProcessContinuousModification.exists_continuous_modification_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessContinuousModification.exists_continuous_modification_itoProcess

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_isMartingale

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_l2_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_l2_continuous

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_terminal

/-- info: 'MathFin.ItoIntegralProcessLocalMartingaleGeneral.exists_continuous_localMartingale_modification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessLocalMartingaleGeneral.exists_continuous_localMartingale_modification

/-- info: 'MathFin.ItoLocalMartingaleInfinite.exists_continuous_localMartingale_modification_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoLocalMartingaleInfinite.exists_continuous_localMartingale_modification_infinite

/-- info: 'MathFin.ItoProcessQV.tendsto_qv_ito_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoProcessQV.tendsto_qv_ito_process

/-- info: 'MathFin.JumpDiffusionHyp.call_eq_integral_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.call_eq_integral_bsV

/-- info: 'MathFin.JumpDiffusionHyp.call_eq_integral_infinitePi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.call_eq_integral_infinitePi

/-- info: 'MathFin.JumpDiffusionHyp.call_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.call_eq_mertonCallPrice

/-- info: 'MathFin.JumpDiffusionHyp.call_poisson_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.call_poisson_mixture

/-- info: 'MathFin.JumpDiffusionHyp.discounted_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.discounted_terminal

/-- info: 'MathFin.JumpDiffusionHyp.discounted_terminal_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.discounted_terminal_eq_iff

/-- info: 'MathFin.JumpDiffusionHyp.impliedVol_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.impliedVol_gt

/-- info: 'MathFin.JumpDiffusionHyp.toMertonHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionHyp.toMertonHyp

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_call

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call_eq_merton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_call_eq_merton

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_call_eq_mertonCallPrice

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call_impliedVol_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_call_impliedVol_gt

/-- info: 'MathFin.JumpDiffusionProcess.condExp_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_comp

/-- info: 'MathFin.JumpDiffusionProcess.condExp_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_put

/-- info: 'MathFin.JumpDiffusionProcess.condExp_put_eq_mertonPutPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_put_eq_mertonPutPrice

/-- info: 'MathFin.JumpDiffusionProcess.condExp_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.condExp_rpow

/-- info: 'MathFin.JumpDiffusionProcess.martingale_exp_const_mul_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.martingale_exp_const_mul_sub

/-- info: 'MathFin.JumpDiffusionProcess.martingale_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.JumpDiffusionProcess.martingale_iff

/-- info: 'MathFin.MarketCompletenessInPrice.exists_replicating_strategy_in_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.MarketCompletenessInPrice.exists_replicating_strategy_in_price

/-- info: 'MathFin.OnePeriod.ftap_one_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.OnePeriod.ftap_one_period

/-- info: 'MathFin.OnePeriodVector.ftap_one_period_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.OnePeriodVector.ftap_one_period_vector

/-- info: 'MathFin.Phi_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Phi_le_one

/-- info: 'MathFin.PointwiseBracket.condExp_band_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PointwiseBracket.condExp_band_second_moment

/-- info: 'MathFin.PoissonCounting.map_count_eq_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonCounting.map_count_eq_poissonMeasure

/-- info: 'MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure

/-- info: 'MathFin.PoissonInterarrival.survival_factorizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonInterarrival.survival_factorizes

/-- info: 'MathFin.PoissonPgf.integral_pow_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonPgf.integral_pow_poissonMeasure

/-- info: 'MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure

/-- info: 'MathFin.PoissonThinning.thinned_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonThinning.thinned_streams

/-- info: 'MathFin.PredictableDensityGeneral.simpleAssembly_sqWeight_denseRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PredictableDensityGeneral.simpleAssembly_sqWeight_denseRange

/-- info: 'MathFin.PricePathDrift.gainsDrift_eq_setIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PricePathDrift.gainsDrift_eq_setIntegral

/-- info: 'MathFin.PricingMeasureL2Density.measure_eq_of_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PricingMeasureL2Density.measure_eq_of_density

/-- info: 'MathFin.SDEExistence.picardMap_exists_unique_fixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SDEExistence.picardMap_exists_unique_fixedPoint

/-- info: 'MathFin.SVI.bsSmile_convex_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.bsSmile_convex_iff

/-- info: 'MathFin.SVI.butterflyFreeFormula_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.butterflyFreeFormula_iff

/-- info: 'MathFin.SVI.butterflyFreeFormula_iff_isNormalizedCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.butterflyFreeFormula_iff_isNormalizedCallPrice

/-- info: 'MathFin.SVI.extendedCertificateFormula_iff_bsSmile_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.extendedCertificateFormula_iff_bsSmile_convex

/-- info: 'MathFin.SVI.fullCertificateFormula_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.fullCertificateFormula_iff

/-- info: 'MathFin.SVI.tendsto_blackPlus_atBot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.tendsto_blackPlus_atBot_iff

/-- info: 'MathFin.SVI.tendsto_bsSmile_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SVI.tendsto_bsSmile_zero_iff

/-- info: 'MathFin.StochasticIntegralCharacterisation.isStochasticIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.StochasticIntegralCharacterisation.isStochasticIntegral

/-- info: 'MathFin.SurvivalModel.survivalFunction_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SurvivalModel.survivalFunction_zero

/-- info: 'MathFin.SurvivalModel.survive_eq_survivalFunction_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.SurvivalModel.survive_eq_survivalFunction_ratio

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_integral_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.WienerIntegralL2.wienerIntegralLp_integral_sq

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal

/-- info: 'MathFin.almgrenChrissPath_satisfies_EL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.almgrenChrissPath_satisfies_EL

/-- info: 'MathFin.am_gm_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.am_gm_two

/-- info: 'MathFin.annuityDue_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.annuityDue_closed_form

/-- info: 'MathFin.annuityValue_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.annuityValue_closed_form

/-- info: 'MathFin.asianGeom_driver_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.asianGeom_driver_hasLaw

/-- info: 'MathFin.asian_payoff_geom_le_arith_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.asian_payoff_geom_le_arith_two

/-- info: 'MathFin.bachelier_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bachelier_call_formula

/-- info: 'MathFin.beta_linearity_finset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_linearity_finset

/-- info: 'MathFin.beta_linearity_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_linearity_two

/-- info: 'MathFin.beta_market' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_market

/-- info: 'MathFin.beta_of_riskFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_of_riskFree

/-- info: 'MathFin.binomialOptionPriceOnePeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialOptionPriceOnePeriod

/-- info: 'MathFin.binomialPrice_call_tendsto_bs_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_call_tendsto_bs_closed

/-- info: 'MathFin.binomialPrice_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_le_americanPrice

/-- info: 'MathFin.binomialPrice_le_bermudanPrice_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_le_bermudanPrice_le_americanPrice

/-- info: 'MathFin.binomialRN_expectation_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialRN_expectation_one

/-- info: 'MathFin.binomial_martingale_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomial_martingale_representation

/-- info: 'MathFin.binomial_maximal_distribution_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomial_maximal_distribution_card

/-- info: 'MathFin.blackLitterman_mean_eq_precision_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.blackLitterman_mean_eq_precision_weighted

/-- info: 'MathFin.blackLitterman_var_eq_inv_sum_precision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.blackLitterman_var_eq_inv_sum_precision

/-- info: 'MathFin.black_futures_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.black_futures_formula

/-- info: 'MathFin.bondPortfolio_immunization_first_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_immunization_first_order

/-- info: 'MathFin.bondPortfolio_immunization_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_immunization_second_order

/-- info: 'MathFin.bondPortfolio_single_bond_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_single_bond_conv

/-- info: 'MathFin.bondPortfolio_single_bond_dur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_single_bond_dur

/-- info: 'MathFin.bondPortfolio_single_bond_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_single_bond_value

/-- info: 'MathFin.bootstrap_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_consistency

/-- info: 'MathFin.bootstrap_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_solve

/-- info: 'MathFin.bootstrap_solve_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_solve_first

/-- info: 'MathFin.bootstrap_solve_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_solve_second

/-- info: 'MathFin.box_spread_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.box_spread_identity

/-- info: 'MathFin.breedenLitzenberger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.breedenLitzenberger

/-- info: 'MathFin.breedenLitzenberger_jumpDiffusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.breedenLitzenberger_jumpDiffusion

/-- info: 'MathFin.brownian_markov_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.brownian_markov_property

/-- info: 'MathFin.bsP_le_K_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsP_le_K_disc

/-- info: 'MathFin.bsV_ge_forward_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_ge_forward_lower_bound

/-- info: 'MathFin.bsV_le_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_le_S

/-- info: 'MathFin.bsV_le_jumpDiffusion_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_le_jumpDiffusion_call

/-- info: 'MathFin.bsV_le_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_le_mertonCallPrice

/-- info: 'MathFin.bsV_lt_jumpDiffusion_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_lt_jumpDiffusion_call

/-- info: 'MathFin.bsV_satisfies_bs_pde_via_feynmanKac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_satisfies_bs_pde_via_feynmanKac

/-- info: 'MathFin.bsV_spot_strictConvexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_spot_strictConvexOn

/-- info: 'MathFin.bsV_spot_tangent_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_spot_tangent_lt

/-- info: 'MathFin.bsV_strict_gt_immediate_exercise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_strict_gt_immediate_exercise

/-- info: 'MathFin.bs_asset_or_nothing_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_asset_or_nothing_formula

/-- info: 'MathFin.bs_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_call_formula

/-- info: 'MathFin.bs_cash_or_nothing_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_cash_or_nothing_formula

/-- info: 'MathFin.bs_discounted_isQMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_discounted_isQMartingale

/-- info: 'MathFin.bs_dividends_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_dividends_call_formula

/-- info: 'MathFin.bs_pde_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_pde_holds

/-- info: 'MathFin.bs_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_put_call_parity

/-- info: 'MathFin.bs_put_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_put_formula

/-- info: 'MathFin.bull_call_spread_payoff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bull_call_spread_payoff_le

/-- info: 'MathFin.butterfly_payoff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.butterfly_payoff_nonneg

/-- info: 'MathFin.caplet_floorlet_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.caplet_floorlet_parity

/-- info: 'MathFin.cappedCall_eq_bull_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cappedCall_eq_bull_spread

/-- info: 'MathFin.carrMadan_log_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.carrMadan_log_spanning

/-- info: 'MathFin.carrMadan_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.carrMadan_spanning

/-- info: 'MathFin.cdf_expMeasure_inMDA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cdf_expMeasure_inMDA

/-- info: 'MathFin.cds_leg_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cds_leg_equality

/-- info: 'MathFin.changeOfMeasure_setIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.changeOfMeasure_setIntegral_eq

/-- info: 'MathFin.changeOfNumeraire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.changeOfNumeraire

/-- info: 'MathFin.chooser_via_pcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.chooser_via_pcp

/-- info: 'MathFin.cml_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_equation

/-- info: 'MathFin.cml_mean_at_stdev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_mean_at_stdev

/-- info: 'MathFin.cml_sharpeRatio_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_sharpeRatio_invariant

/-- info: 'MathFin.cml_weight_recovers_stdev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_weight_recovers_stdev

/-- info: 'MathFin.cml_weight_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_weight_unique

/-- info: 'MathFin.coherentRisk_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.coherentRisk_isLUB

/-- info: 'MathFin.compensated_integral_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.compensated_integral_isometry

/-- info: 'MathFin.compensated_simple_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.compensated_simple_isometry

/-- info: 'MathFin.compoundPoisson_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.compoundPoisson_mgf

/-- info: 'MathFin.compoundPoisson_mgf_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.compoundPoisson_mgf_of_indepFun

/-- info: 'MathFin.condExp_comp_prodMk_of_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.condExp_comp_prodMk_of_indep

/-- info: 'MathFin.continuous_jumpDiffusionDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.continuous_jumpDiffusionDensity

/-- info: 'MathFin.copulaOf_comp_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.copulaOf_comp_strictMono

/-- info: 'MathFin.couponBondPrice_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.couponBondPrice_strictAnti

/-- info: 'MathFin.covariance_eq_integral_cdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.covariance_eq_integral_cdf

/-- info: 'MathFin.covariance_indicator_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.covariance_indicator_one_le

/-- info: 'MathFin.covariance_le_covariance_of_cdf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.covariance_le_covariance_of_cdf_le

/-- info: 'MathFin.covariance_le_sqrt_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.covariance_le_sqrt_mul_sqrt

/-- info: 'MathFin.creditSpread_eq_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.creditSpread_eq_hazard

/-- info: 'MathFin.creditSpread_eq_time_avg_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.creditSpread_eq_time_avg_hazard

/-- info: 'MathFin.crrProb_tendsto_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crrProb_tendsto_half

/-- info: 'MathFin.crr_drift_limit_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_drift_limit_h

/-- info: 'MathFin.crr_drift_limit_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_drift_limit_n

/-- info: 'MathFin.crr_one_step_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_one_step_martingale

/-- info: 'MathFin.crr_tendsto_gaussian_inDistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_tendsto_gaussian_inDistribution

/-- info: 'MathFin.crr_variance_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_variance_limit

/-- info: 'MathFin.defaultCorrelation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.defaultCorrelation_eq

/-- info: 'MathFin.discountedGBM_eq_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_eq_itoIntegral

/-- info: 'MathFin.discountedGBM_isEMM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_isEMM

/-- info: 'MathFin.discountedGBM_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_isMartingale

/-- info: 'MathFin.discountedGBM_noArbitrageSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_noArbitrageSimple

/-- info: 'MathFin.discounted_americanPrice_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discounted_americanPrice_supermartingale

/-- info: 'MathFin.discounted_intrinsic_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discounted_intrinsic_le_americanPrice

/-- info: 'MathFin.discrete_cubing_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discrete_cubing_identity

/-- info: 'MathFin.doob_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.doob_decomposition

/-- info: 'MathFin.downsideMetrics_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.downsideMetrics_bundle

/-- info: 'MathFin.emm_implies_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.emm_implies_no_arbitrage

/-- info: 'MathFin.emm_le_superReplication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.emm_le_superReplication

/-- info: 'MathFin.eq_copulaOf_of_measureReal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.eq_copulaOf_of_measureReal_le

/-- info: 'MathFin.exchangeOption_numeraire_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exchangeOption_numeraire_price

/-- info: 'MathFin.existsUnique_esscher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.existsUnique_esscher

/-- info: 'MathFin.existsUnique_expectileGap_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.existsUnique_expectileGap_eq_zero

/-- info: 'MathFin.exists_call_esscher_ne_merton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_call_esscher_ne_merton

/-- info: 'MathFin.exists_gaussian_uncorrelated_not_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_gaussian_uncorrelated_not_indepFun

/-- info: 'MathFin.exists_impliedVol_gt_of_bsV_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_impliedVol_gt_of_bsV_lt

/-- info: 'MathFin.exists_isCopula_fgm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_isCopula_fgm_iff

/-- info: 'MathFin.exists_pos_separating_of_cone_disjoint_simplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_pos_separating_of_cone_disjoint_simplex

/-- info: 'MathFin.exists_replicating_strategy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_replicating_strategy

/-- info: 'MathFin.expectedShortfall_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_add_le

/-- info: 'MathFin.expectedShortfall_eq_acerbiTasche' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_eq_acerbiTasche

/-- info: 'MathFin.expectedShortfall_isCoherentRiskMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_isCoherentRiskMeasure

/-- info: 'MathFin.expectedShortfall_isLUB_representingSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_isLUB_representingSet

/-- info: 'MathFin.expectedShortfall_mono_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_mono_level

/-- info: 'MathFin.expectedShortfall_of_hasLaw_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_of_hasLaw_expMeasure

/-- info: 'MathFin.expectedShortfall_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_of_hasLaw_gaussianReal

/-- info: 'MathFin.expectedShortfall_of_hasLaw_lomaxMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedShortfall_of_hasLaw_lomaxMeasure

/-- info: 'MathFin.expectedUtility_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectedUtility_mix

/-- info: 'MathFin.expected_terminal_eq_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expected_terminal_eq_forward

/-- info: 'MathFin.expectile_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expectile_mono

/-- info: 'MathFin.firstToDefault_spread_eq_sum_hazards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.firstToDefault_spread_eq_sum_hazards

/-- info: 'MathFin.forwardMeasure_bs_expected_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.forwardMeasure_bs_expected_terminal

/-- info: 'MathFin.forward_price_eq_spot_div_discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.forward_price_eq_spot_div_discount

/-- info: 'MathFin.fraValue_zcb_eq_discount_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.fraValue_zcb_eq_discount_difference

/-- info: 'MathFin.fraValue_zcb_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.fraValue_zcb_eq_zero_iff

/-- info: 'MathFin.ftap_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ftap_discrete

/-- info: 'MathFin.gainToPain_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gainToPain_nonneg

/-- info: 'MathFin.garman_kohlhagen_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.garman_kohlhagen_call_formula

/-- info: 'MathFin.gaussianCVaR_additive_at_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_additive_at_rho_one

/-- info: 'MathFin.gaussianCVaR_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_affine

/-- info: 'MathFin.gaussianCVaR_isLeast_ruObjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_isLeast_ruObjective

/-- info: 'MathFin.gaussianCVaR_monotone_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_monotone_mean

/-- info: 'MathFin.gaussianCVaR_positiveHomogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_positiveHomogeneity

/-- info: 'MathFin.gaussianCVaR_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_standard

/-- info: 'MathFin.gaussianCVaR_sub_VaR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_sub_VaR

/-- info: 'MathFin.gaussianCVaR_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_subadditive

/-- info: 'MathFin.gaussianCVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_translation

/-- info: 'MathFin.gaussianPDFReal_zero_one_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianPDFReal_zero_one_neg

/-- info: 'MathFin.gaussianReal_tilted_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianReal_tilted_const_mul

/-- info: 'MathFin.gaussianVaR_additive_at_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_additive_at_rho_one

/-- info: 'MathFin.gaussianVaR_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_affine

/-- info: 'MathFin.gaussianVaR_monotone_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_monotone_mean

/-- info: 'MathFin.gaussianVaR_positiveHomogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_positiveHomogeneity

/-- info: 'MathFin.gaussianVaR_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_standard

/-- info: 'MathFin.gaussianVaR_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_subadditive

/-- info: 'MathFin.gaussianVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_translation

/-- info: 'MathFin.gaussianVaR_volatility_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_volatility_scaling

/-- info: 'MathFin.geomAsianN_call_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.geomAsianN_call_price

/-- info: 'MathFin.geomAsianN_driver_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.geomAsianN_driver_hasLaw

/-- info: 'MathFin.geom_mean_le_arith_mean_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.geom_mean_le_arith_mean_n

/-- info: 'MathFin.gevCDF_max_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gevCDF_max_stable

/-- info: 'MathFin.gompertz_cumulative_force' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gompertz_cumulative_force

/-- info: 'MathFin.gpdCDF_inMDA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gpdCDF_inMDA

/-- info: 'MathFin.hasDerivAt_S_deriv_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_S_deriv_bsV_sigma

/-- info: 'MathFin.hasDerivAt_T_mul_spotRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_T_mul_spotRate

/-- info: 'MathFin.hasDerivAt_bachelierV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_S

/-- info: 'MathFin.hasDerivAt_bachelierV_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_T

/-- info: 'MathFin.hasDerivAt_bachelierV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_sigma

/-- info: 'MathFin.hasDerivAt_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_F

/-- info: 'MathFin.hasDerivAt_blackV_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_T

/-- info: 'MathFin.hasDerivAt_blackV_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_r

/-- info: 'MathFin.hasDerivAt_blackV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_sigma

/-- info: 'MathFin.hasDerivAt_bondPortfolioDur_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bondPortfolioDur_r

/-- info: 'MathFin.hasDerivAt_bondPortfolioValue_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bondPortfolioValue_r

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_S

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_r

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_sigma

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_tau

/-- info: 'MathFin.hasDerivAt_bsCashDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_S

/-- info: 'MathFin.hasDerivAt_bsCashDigital_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_r

/-- info: 'MathFin.hasDerivAt_bsCashDigital_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_sigma

/-- info: 'MathFin.hasDerivAt_bsCashDigital_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_tau

/-- info: 'MathFin.hasDerivAt_bsP_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_K

/-- info: 'MathFin.hasDerivAt_bsP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_S

/-- info: 'MathFin.hasDerivAt_bsP_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_r

/-- info: 'MathFin.hasDerivAt_bsP_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_sigma

/-- info: 'MathFin.hasDerivAt_bsP_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_tau

/-- info: 'MathFin.hasDerivAt_bsVDiv_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_S

/-- info: 'MathFin.hasDerivAt_bsVDiv_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_q

/-- info: 'MathFin.hasDerivAt_bsVDiv_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_r

/-- info: 'MathFin.hasDerivAt_bsVDiv_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_sigma

/-- info: 'MathFin.hasDerivAt_bsVDiv_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_tau

/-- info: 'MathFin.hasDerivAt_bsV_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_K

/-- info: 'MathFin.hasDerivAt_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_S

/-- info: 'MathFin.hasDerivAt_bsV_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_r

/-- info: 'MathFin.hasDerivAt_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_sigma

/-- info: 'MathFin.hasDerivAt_bsV_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_t

/-- info: 'MathFin.hasDerivAt_bsd1_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsd1_K

/-- info: 'MathFin.hasDerivAt_bsd2_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsd2_K

/-- info: 'MathFin.hasDerivAt_deriv_bachelierV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bachelierV_S

/-- info: 'MathFin.hasDerivAt_deriv_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_blackV_F

/-- info: 'MathFin.hasDerivAt_deriv_bondPortfolioValue_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bondPortfolioValue_r

/-- info: 'MathFin.hasDerivAt_deriv_bsAssetDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsAssetDigital_S

/-- info: 'MathFin.hasDerivAt_deriv_bsCashDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsCashDigital_S

/-- info: 'MathFin.hasDerivAt_deriv_bsP_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsP_K

/-- info: 'MathFin.hasDerivAt_deriv_bsP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsP_S

/-- info: 'MathFin.hasDerivAt_deriv_bsVDiv_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsVDiv_S

/-- info: 'MathFin.hasDerivAt_deriv_bsV_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsV_K

/-- info: 'MathFin.hasDerivAt_deriv_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsV_S

/-- info: 'MathFin.hasDerivAt_deriv_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_bsV_sigma

/-- info: 'MathFin.hasDerivAt_deriv_deriv_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_deriv_blackV_F

/-- info: 'MathFin.hasDerivAt_deriv_deriv_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_deriv_bsV_S

/-- info: 'MathFin.hasDerivAt_deriv_mertonCallPrice_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_deriv_mertonCallPrice_spot

/-- info: 'MathFin.hasDerivAt_integral_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_integral_call

/-- info: 'MathFin.hasDerivAt_jumpDiffusionCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_jumpDiffusionCallPrice_strike

/-- info: 'MathFin.hasDerivAt_matrixRiccatiCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_matrixRiccatiCoeff

/-- info: 'MathFin.hasDerivAt_mertonCallPrice_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_mertonCallPrice_sigma

/-- info: 'MathFin.hasDerivAt_mertonCallPrice_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_mertonCallPrice_spot

/-- info: 'MathFin.hasDerivAt_mmMatrixValueCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_mmMatrixValueCoeff

/-- info: 'MathFin.hasDerivAt_neg_log_zcb_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_neg_log_zcb_T

/-- info: 'MathFin.hasDerivAt_riccatiCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_riccatiCoeff

/-- info: 'MathFin.hasDerivAt_tau_deriv_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_tau_deriv_bsV_S

/-- info: 'MathFin.hasEMM_multi_iff_not_hasArbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasEMM_multi_iff_not_hasArbitrage

/-- info: 'MathFin.hasLaw_cdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasLaw_cdf

/-- info: 'MathFin.hasLaw_quantile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasLaw_quantile

/-- info: 'MathFin.hazardSurvival_eq_const_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hazardSurvival_eq_const_survival

/-- info: 'MathFin.hazard_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hazard_eq_neg_log_deriv_survival

/-- info: 'MathFin.herfindahl_card_inv_le_of_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.herfindahl_card_inv_le_of_sum_one

/-- info: 'MathFin.impliedVol_bisection_converges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.impliedVol_bisection_converges

/-- info: 'MathFin.impliedVol_bracket_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.impliedVol_bracket_exists

/-- info: 'MathFin.implied_volatility_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.implied_volatility_unique

/-- info: 'MathFin.informationRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.informationRatio_scale_invariant

/-- info: 'MathFin.integral_bilinear_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_bilinear_pairing

/-- info: 'MathFin.integral_bsV_mul_exp_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_bsV_mul_exp_gaussianReal

/-- info: 'MathFin.integral_call_tilted_eq_merton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_call_tilted_eq_merton

/-- info: 'MathFin.integral_call_tilted_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_call_tilted_eq_mertonCallPrice

/-- info: 'MathFin.integral_call_tilted_zero_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_call_tilted_zero_eq_bsV

/-- info: 'MathFin.integral_comp_prodMk_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_comp_prodMk_of_indepFun

/-- info: 'MathFin.integral_exp_const_mul_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_exp_const_mul_jumpDiffusionIncrementLaw

/-- info: 'MathFin.integral_exp_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_exp_gaussianReal

/-- info: 'MathFin.integral_exp_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_exp_jumpDiffusionIncrementLaw

/-- info: 'MathFin.integral_log_forward_div_bsTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_log_forward_div_bsTerminal_eq

/-- info: 'MathFin.integral_mertonSpot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_mertonSpot

/-- info: 'MathFin.integral_sub_cond_gpdMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_sub_cond_gpdMeasure

/-- info: 'MathFin.isCopula_copulaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isCopula_copulaOf

/-- info: 'MathFin.isGreatest_integral_mul_expectedShortfall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isGreatest_integral_mul_expectedShortfall

/-- info: 'MathFin.isLeast_rockafellarUryasev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isLeast_rockafellarUryasev

/-- info: 'MathFin.isLocalizingSequence_exitTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isLocalizingSequence_exitTime

/-- info: 'MathFin.isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN

/-- info: 'MathFin.isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN

/-- info: 'MathFin.isStoppingTime_hittingAfter_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isStoppingTime_hittingAfter_of_open

/-- info: 'MathFin.isTangent_of_proportional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isTangent_of_proportional

/-- info: 'MathFin.itoIntegralCLM_T_surjective_onto_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.itoIntegralCLM_T_surjective_onto_centered

/-- info: 'MathFin.itoLevyIntegralL2_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.itoLevyIntegralL2_norm

/-- info: 'MathFin.ito_formula_L2_bddDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_L2_bddDeriv

/-- info: 'MathFin.ito_formula_gbm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_gbm

/-- info: 'MathFin.ito_formula_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_itoProcess

/-- info: 'MathFin.ito_formula_td_L2_bddDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_L2_bddDeriv

/-- info: 'MathFin.ito_formula_td_localized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_localized

/-- info: 'MathFin.ito_formula_td_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_process

/-- info: 'MathFin.ito_formula_unrestricted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_unrestricted

/-- info: 'MathFin.ito_formula_unrestricted_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_unrestricted_local

/-- info: 'MathFin.joint_stdev_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.joint_stdev_le

/-- info: 'MathFin.jumpDiffusionCallPrice_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionCallPrice_eq

/-- info: 'MathFin.jumpDiffusionCallPrice_eq_of_compensated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionCallPrice_eq_of_compensated

/-- info: 'MathFin.jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice

/-- info: 'MathFin.jumpDiffusionCallPrice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionCallPrice_zero

/-- info: 'MathFin.jumpDiffusionDensity_div_eq_lognormalTerminalPDF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionDensity_div_eq_lognormalTerminalPDF

/-- info: 'MathFin.jumpDiffusionDigitalPrice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionDigitalPrice_zero

/-- info: 'MathFin.jumpDiffusionExponent_zero_esscher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionExponent_zero_esscher

/-- info: 'MathFin.jumpDiffusionHyp_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionHyp_canonical

/-- info: 'MathFin.jumpDiffusionIncrementLaw_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionIncrementLaw_eq_iff

/-- info: 'MathFin.jumpDiffusionIncrementLaw_eq_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionIncrementLaw_eq_withDensity

/-- info: 'MathFin.jumpDiffusionIncrementLaw_map_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionIncrementLaw_map_const_mul

/-- info: 'MathFin.jumpDiffusionIncrementLaw_tilted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionIncrementLaw_tilted

/-- info: 'MathFin.jumpDiffusionIncrementLaw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionIncrementLaw_zero

/-- info: 'MathFin.jumpDiffusionProcess_brownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionProcess_brownian

/-- info: 'MathFin.jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice

/-- info: 'MathFin.jumpDiffusionPutPrice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusionPutPrice_zero

/-- info: 'MathFin.jumpDiffusion_call_eq_integral_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusion_call_eq_integral_bsV

/-- info: 'MathFin.jumpDiffusion_call_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusion_call_le

/-- info: 'MathFin.jumpDiffusion_call_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusion_call_lt

/-- info: 'MathFin.jumpDiffusion_impliedVol_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.jumpDiffusion_impliedVol_gt

/-- info: 'MathFin.kellyFraction_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyFraction_eq_zero_iff

/-- info: 'MathFin.kellyFraction_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyFraction_lt_one

/-- info: 'MathFin.kellyFraction_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyFraction_pos_iff

/-- info: 'MathFin.kellyGrowth_deriv_at_kelly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyGrowth_deriv_at_kelly

/-- info: 'MathFin.kellyGrowth_n_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyGrowth_n_periods

/-- info: 'MathFin.kellyNumeraire_isRiskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyNumeraire_isRiskNeutral

/-- info: 'MathFin.kelly_n_periods_deriv_at_kelly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kelly_n_periods_deriv_at_kelly

/-- info: 'MathFin.kmvPD_eq_one_sub_survival_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kmvPD_eq_one_sub_survival_probability

/-- info: 'MathFin.knockIn_add_knockOut_eq_vanilla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.knockIn_add_knockOut_eq_vanilla

/-- info: 'MathFin.log_forward_div_bsTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.log_forward_div_bsTerminal_eq

/-- info: 'MathFin.lognormalTerminalPDF_change_of_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.lognormalTerminalPDF_change_of_variables

/-- info: 'MathFin.lookback_payoff_ge_vanilla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.lookback_payoff_ge_vanilla

/-- info: 'MathFin.lp_continuous_martingale_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.lp_continuous_martingale_full

/-- info: 'MathFin.markovPathMeasure_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.markovPathMeasure_cylinder

/-- info: 'MathFin.marshallOlkin_firstToDefault_spread_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.marshallOlkin_firstToDefault_spread_lt

/-- info: 'MathFin.marshallOlkin_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.marshallOlkin_survival

/-- info: 'MathFin.martingaleTransform_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.martingaleTransform_isMartingale

/-- info: 'MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto

/-- info: 'MathFin.martingale_exp_sub_of_indep_increments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.martingale_exp_sub_of_indep_increments

/-- info: 'MathFin.martingale_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.martingale_representation

/-- info: 'MathFin.measureReal_iInter_default_eq_integral_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.measureReal_iInter_default_eq_integral_pow

/-- info: 'MathFin.measureReal_le_eq_copulaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.measureReal_le_eq_copulaOf

/-- info: 'MathFin.measureReal_poisson_max_gpd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.measureReal_poisson_max_gpd

/-- info: 'MathFin.measure_eq_of_integral_call_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.measure_eq_of_integral_call_eq

/-- info: 'MathFin.measure_eq_of_pricesGainsAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.measure_eq_of_pricesGainsAtZero

/-- info: 'MathFin.medianShortfall_eq_valueAtRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.medianShortfall_eq_valueAtRisk

/-- info: 'MathFin.mertonCallPrice_eq_classic_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_eq_classic_tsum

/-- info: 'MathFin.mertonCallPrice_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_eq_tsum

/-- info: 'MathFin.mertonCallPrice_strictConvexOn_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_strictConvexOn_spot

/-- info: 'MathFin.mertonCallPrice_strictMonoOn_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_strictMonoOn_sigma

/-- info: 'MathFin.mertonCallPrice_strictMonoOn_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_strictMonoOn_spot

/-- info: 'MathFin.mertonDelta_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonDelta_lt_one

/-- info: 'MathFin.mertonDelta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonDelta_pos

/-- info: 'MathFin.mertonGamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonGamma_pos

/-- info: 'MathFin.mertonHyp_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonHyp_canonical

/-- info: 'MathFin.mertonVega_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonVega_pos

/-- info: 'MathFin.merton_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.merton_call_formula

/-- info: 'MathFin.merton_discounted_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.merton_discounted_terminal

/-- info: 'MathFin.merton_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.merton_put_call_parity

/-- info: 'MathFin.merton_put_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.merton_put_formula

/-- info: 'MathFin.minPortfolioVarTwo_perfect_anticorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.minPortfolioVarTwo_perfect_anticorr

/-- info: 'MathFin.minimum_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.minimum_survival

/-- info: 'MathFin.mmHalfSpread_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mmHalfSpread_const

/-- info: 'MathFin.mmSkew_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mmSkew_linear

/-- info: 'MathFin.modifiedNumerator_eq_macaulayNumerator_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.modifiedNumerator_eq_macaulayNumerator_div

/-- info: 'MathFin.mul_le_portfolioVarN_equicorrelated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mul_le_portfolioVarN_equicorrelated

/-- info: 'MathFin.newtonSeq_tendsto_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.newtonSeq_tendsto_root

/-- info: 'MathFin.newtonStep_quadratic_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.newtonStep_quadratic_error

/-- info: 'MathFin.noArbitrage_of_emm_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.noArbitrage_of_emm_multi

/-- info: 'MathFin.not_exists_isCopula_frechetLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.not_exists_isCopula_frechetLower

/-- info: 'MathFin.not_isElicitable_expectedShortfall_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.not_isElicitable_expectedShortfall_integrable

/-- info: 'MathFin.nthMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.nthMoment_terminal

/-- info: 'MathFin.oneFactor_measureReal_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.oneFactor_measureReal_default

/-- info: 'MathFin.payerSwapValue_zcb_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.payerSwapValue_zcb_eq_zero_iff

/-- info: 'MathFin.portfolioVarN_covariance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_covariance_nonneg

/-- info: 'MathFin.portfolioVarN_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_diag

/-- info: 'MathFin.portfolioVarN_equal_weights_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_equal_weights_iid

/-- info: 'MathFin.portfolioVarN_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_smul

/-- info: 'MathFin.portfolioVarN_two_asset_compat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_two_asset_compat

/-- info: 'MathFin.portfolioVarTwo_at_minVarWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarTwo_at_minVarWeight

/-- info: 'MathFin.portfolioVarTwo_eq_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarTwo_eq_quad

/-- info: 'MathFin.portfolioVarTwo_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarTwo_ge_min

/-- info: 'MathFin.posSemidef_equicorrelationMatrix_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.posSemidef_equicorrelationMatrix_iff

/-- info: 'MathFin.powerForward_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.powerForward_price

/-- info: 'MathFin.prefersEU_affine_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.prefersEU_affine_invariant

/-- info: 'MathFin.prefersEU_continuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.prefersEU_continuity

/-- info: 'MathFin.prefersEU_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.prefersEU_independence

/-- info: 'MathFin.premium_ge_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.premium_ge_mean

/-- info: 'MathFin.processToLpPredictable_coeFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.processToLpPredictable_coeFn

/-- info: 'MathFin.putCall_parity_from_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.putCall_parity_from_no_arbitrage

/-- info: 'MathFin.quantile_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quantile_gaussianReal

/-- info: 'MathFin.quantile_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quantile_le_iff

/-- info: 'MathFin.quantile_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quantile_map

/-- info: 'MathFin.quantoForward_of_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quantoForward_of_gaussian

/-- info: 'MathFin.quanto_correction_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quanto_correction_factor

/-- info: 'MathFin.quoteConstA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quoteConstA

/-- info: 'MathFin.quoteConstB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quoteConstB

/-- info: 'MathFin.reflectionPrincipleEquiv_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.reflectionPrincipleEquiv_below

/-- info: 'MathFin.reflection_principle_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.reflection_principle_card

/-- info: 'MathFin.replicating_payoff_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.replicating_payoff_down

/-- info: 'MathFin.replicating_payoff_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.replicating_payoff_up

/-- info: 'MathFin.replicating_portfolio_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.replicating_portfolio_cost

/-- info: 'MathFin.riskParityWeightTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.riskParityWeightTwo

/-- info: 'MathFin.risk_parity_equal_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.risk_parity_equal_contribution

/-- info: 'MathFin.secondMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.secondMoment_terminal

/-- info: 'MathFin.second_FTAP_single_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.second_FTAP_single_period

/-- info: 'MathFin.sharpeRatio_scaleT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sharpeRatio_scaleT

/-- info: 'MathFin.sharpeRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sharpeRatio_scale_invariant

/-- info: 'MathFin.sharpeSqTwo_critical_iff_crossProduct_FOC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sharpeSqTwo_critical_iff_crossProduct_FOC

/-- info: 'MathFin.sortinoRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sortinoRatio_scale_invariant

/-- info: 'MathFin.sortinoRatio_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sortinoRatio_translation

/-- info: 'MathFin.spearmanRho_fgmCopula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.spearmanRho_fgmCopula

/-- info: 'MathFin.spectralRisk_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.spectralRisk_translation

/-- info: 'MathFin.statePricePricing_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.statePricePricing_add

/-- info: 'MathFin.statePricePricing_eq_riskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.statePricePricing_eq_riskNeutral

/-- info: 'MathFin.stateprice_call_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.stateprice_call_butterfly_nonneg

/-- info: 'MathFin.stdDevPrinciple_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.stdDevPrinciple_add_le

/-- info: 'MathFin.stdDevPrinciple_not_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.stdDevPrinciple_not_monotone

/-- info: 'MathFin.strictlyElicits_pinballLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.strictlyElicits_pinballLoss

/-- info: 'MathFin.submartingale_optional_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.submartingale_optional_sampling

/-- info: 'MathFin.survival_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_at_zero

/-- info: 'MathFin.survival_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_pos

/-- info: 'MathFin.survival_probability_eq_Phi_distanceToDefault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_probability_eq_Phi_distanceToDefault

/-- info: 'MathFin.survival_strictAnti_of_pos_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_strictAnti_of_pos_hazard

/-- info: 'MathFin.swaption_payer_receiver_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.swaption_payer_receiver_parity

/-- info: 'MathFin.tendsto_bisectMid_valueAtRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_bisectMid_valueAtRisk

/-- info: 'MathFin.tendsto_bsV_sigma_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_bsV_sigma_atTop

/-- info: 'MathFin.tendsto_call_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_call_spread

/-- info: 'MathFin.tendsto_claytonCopulaFun_diag_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_claytonCopulaFun_diag_div

/-- info: 'MathFin.tendsto_expectedShortfall_div_valueAtRisk_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_expectedShortfall_div_valueAtRisk_expMeasure

/-- info: 'MathFin.tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure

/-- info: 'MathFin.tendsto_oneFactorLossFraction_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_oneFactorLossFraction_ae

/-- info: 'MathFin.tendsto_pow_iff_tendsto_nat_mul_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_pow_iff_tendsto_nat_mul_tail

/-- info: 'MathFin.tendsto_quantile_of_tendsto_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_quantile_of_tendsto_ae

/-- info: 'MathFin.tendsto_realizedVariance_gbm_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_realizedVariance_gbm_L2

/-- info: 'MathFin.tendsto_valueAtRisk_oneFactorLossFraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_valueAtRisk_oneFactorLossFraction

/-- info: 'MathFin.trackingErrorSq_ge_diff_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.trackingErrorSq_ge_diff_sq

/-- info: 'MathFin.trackingErrorSq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.trackingErrorSq_self

/-- info: 'MathFin.treynorRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.treynorRatio_scale_invariant

/-- info: 'MathFin.triangleNoArb_solve_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.triangleNoArb_solve_third

/-- info: 'MathFin.upCapture_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.upCapture_smul

/-- info: 'MathFin.valueAtRisk_add_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_add_affine

/-- info: 'MathFin.valueAtRisk_add_gt_of_paretoHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_add_gt_of_paretoHalf

/-- info: 'MathFin.valueAtRisk_add_le_iff_of_hasGaussianLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_add_le_iff_of_hasGaussianLaw

/-- info: 'MathFin.valueAtRisk_add_of_comonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_add_of_comonotone

/-- info: 'MathFin.valueAtRisk_gbm_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_gbm_loss

/-- info: 'MathFin.valueAtRisk_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_of_hasLaw_gaussianReal

/-- info: 'MathFin.valueAtRisk_portfolio_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_portfolio_add_le

/-- info: 'MathFin.valueAtRisk_sum_bernoulli_superadditive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueAtRisk_sum_bernoulli_superadditive_iff

/-- info: 'MathFin.valueFunction_satisfies_approxHJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.valueFunction_satisfies_approxHJ

/-- info: 'MathFin.varianceSwap_log_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.varianceSwap_log_contribution

/-- info: 'MathFin.varianceSwap_log_eq_QV_limit_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.varianceSwap_log_eq_QV_limit_value

/-- info: 'MathFin.variance_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.variance_terminal

/-- info: 'MathFin.vasicekBondPrice_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekBondPrice_affine

/-- info: 'MathFin.vasicekDeterministic_at_halfLife' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekDeterministic_at_halfLife

/-- info: 'MathFin.vasicekDeterministic_solves_ODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekDeterministic_solves_ODE

/-- info: 'MathFin.vasicekShortRate_hasLaw_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekShortRate_hasLaw_gaussian

/-- info: 'MathFin.worstCase_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.worstCase_isLUB

/-- info: 'MathFin.zcb_at_maturity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_at_maturity

/-- info: 'MathFin.zcb_convexity_eq_time_to_maturity_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_convexity_eq_time_to_maturity_sq

/-- info: 'MathFin.zcb_duration_eq_time_to_maturity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_duration_eq_time_to_maturity

/-- info: 'MathFin.zcb_yield_eq_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_yield_eq_rate

/-- info: 'MeasureTheory.maximal_ineq_Lp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.maximal_ineq_Lp

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.condExp_call_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsFilteredPreBrownian.condExp_call_eq_bsV

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.condExp_put_eq_bsPut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsFilteredPreBrownian.condExp_put_eq_bsPut

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.jumpDiffusionProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsFilteredPreBrownian.jumpDiffusionProcess

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.martingale_discounted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsFilteredPreBrownian.martingale_discounted_iff

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.squareSubTime_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsFilteredPreBrownian.squareSubTime_isMartingale

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.waldExponential_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsFilteredPreBrownian.waldExponential_isMartingale

/-! ## Upstream constants cited by `library_wrapper` entries

A `library_wrapper` entry re-exports a Mathlib or BrownianMotion theorem, and it
counts as delivered. BrownianMotion at the current pin has `sorry`s of its own,
so these are pinned here rather than left to upstream. -/

/-- info: 'ConvexOn.map_condExp_le_of_finiteDimensional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ConvexOn.map_condExp_le_of_finiteDimensional

/-- info: 'Eq.symm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Eq.symm

/-- info: 'LT.lt.ne'' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms LT.lt.ne'

/-- info: 'MeasureTheory.Integrable.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.Integrable.smul

/-- info: 'MeasureTheory.IsProbabilityMeasure.measure_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.IsProbabilityMeasure.measure_univ

/-- info: 'MeasureTheory.Martingale.stoppedProcess_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.Martingale.stoppedProcess_indicator

/-- info: 'MeasureTheory.Measure.trim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.Measure.trim

/-- info: 'MeasureTheory.MeasurePreserving.map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.MeasurePreserving.map_eq

/-- info: 'MeasureTheory.SigmaFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.SigmaFinite

/-- info: 'MeasureTheory.Submartingale.ae_tendsto_limitProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.Submartingale.ae_tendsto_limitProcess

/-- info: 'MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part

/-- info: 'MeasureTheory.condExp_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.condExp_add

/-- info: 'MeasureTheory.condExp_condExp_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.condExp_condExp_of_le

/-- info: 'MeasureTheory.condExp_indep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.condExp_indep_eq

/-- info: 'MeasureTheory.condExp_mul_of_stronglyMeasurable_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.condExp_mul_of_stronglyMeasurable_left

/-- info: 'MeasureTheory.condExp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.condExp_smul

/-- info: 'MeasureTheory.maximal_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.maximal_ineq

/-- info: 'MeasureTheory.measure_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.measure_empty

/-- info: 'Pi.add_apply' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Pi.add_apply

/-- info: 'ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance

/-- info: 'ProbabilityTheory.IsPreBrownianReal.isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsPreBrownianReal.isMartingale

/-- info: 'ProbabilityTheory.IsPreBrownianReal.memHolder_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsPreBrownianReal.memHolder_mk

/-- info: 'ProbabilityTheory.gaussianReal_add_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.gaussianReal_add_const

/-- info: 'ProbabilityTheory.gaussianReal_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.gaussianReal_const_mul

/-- info: 'ProbabilityTheory.maximal_ineq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.maximal_ineq_nonneg

/-- info: 'ProbabilityTheory.measurePreserving_eval_multivariateGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.measurePreserving_eval_multivariateGaussian

/-- info: 'Real.log_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Real.log_div

/-- info: 'inferInstance' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms inferInstance

/-- info: 'min_eq_left' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms min_eq_left

end MathFin.AxiomAuditGen
