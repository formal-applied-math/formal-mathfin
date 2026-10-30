/-
  GENERATED FILE — do not edit by hand.

  Exhaustive axiom audit: every constant declared in MathFin/ that a benchmark
  snippet's proof cites is #guard_msgs-pinned to its exact axiom set, so no
  benchmark-cited theorem can pick up `sorryAx` (a `sorry`) or a non-standard
  axiom without breaking `lake build`.

  The curated, storied audit is MathFin/AxiomAudit.lean (headliners + dated
  narrative); THIS file is its machine-written closure over the benchmark
  corpus (827 MathFin constants, 29 upstream). Citations
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

-- The `#guard_msgs` docstrings below are Lean's own output, matched as printed.
set_option linter.style.longLine false

namespace MathFin.AxiomAuditGen

/-- info: 'MathFin.AdaptedQuadraticVariation.tendsto_qv_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedQuadraticVariation.tendsto_qv_adapted

/-- info: 'MathFin.AdaptedQuadraticVariation.tendsto_weighted_qv_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedQuadraticVariation.tendsto_weighted_qv_adapted

/-- info: 'MathFin.AdaptedRiemannStieltjes.coeFn_mulLI_weightLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedRiemannStieltjes.coeFn_mulLI_weightLp

/-- info: 'MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_stepσ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_stepσ

/-- info: 'MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_weightLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedRiemannStieltjes.itoIntegralAgainst_weightLp

/-- info: 'MathFin.AdaptedRiemannStieltjes.tendsto_integral_sq_riemannStieltjes_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedRiemannStieltjes.tendsto_integral_sq_riemannStieltjes_sub

/-- info: 'MathFin.AdaptedRiemannStieltjes.tendsto_itoIntegralAgainst_stepσ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.AdaptedRiemannStieltjes.tendsto_itoIntegralAgainst_stepσ

/-- info: 'MathFin.BivariateGaussianHyp.conditional_expectation_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BivariateGaussianHyp.conditional_expectation_formula

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.aeAmericanPutValue_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.aeAmericanPutValue_eq

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.aeExerciseThreshold_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.aeExerciseThreshold_eq

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualLogBoundary_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualLogBoundary_convexOn

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualStockBoundary_strictConvexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualStockBoundary_strictConvexOn

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.bsPDiv_le_americanPutValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.bsPDiv_le_americanPutValue

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.bsPDiv_le_brownianUsualAmericanPut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.bsPDiv_le_brownianUsualAmericanPut

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.condExp_stoppedValue_le_finiteBellman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.condExp_stoppedValue_le_finiteBellman

/-- info: 'MathFin.BlackScholes.AmericanPut.Stopping.finiteBellman_doob_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BlackScholes.AmericanPut.Stopping.finiteBellman_doob_decomposition

/-- info: 'MathFin.Bootstrapping.boot_reprices_swapChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Bootstrapping.boot_reprices_swapChain

/-- info: 'MathFin.Bootstrapping.payerSwapValue_lastCoupon_eq_zero_iff_couponBond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Bootstrapping.payerSwapValue_lastCoupon_eq_zero_iff_couponBond

/-- info: 'MathFin.Bootstrapping.swapBootstrap_recovers_couponBondFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Bootstrapping.swapBootstrap_recovers_couponBondFactor

/-- info: 'MathFin.BracketCompensator.condExp_sq_sub_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BracketCompensator.condExp_sq_sub_bracket

/-- info: 'MathFin.BrownianQuadraticVariation.qv_equals_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.BrownianQuadraticVariation.qv_equals_t

/-- info: 'MathFin.Btheta_isQBrownianMotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Btheta_isQBrownianMotion

/-- info: 'MathFin.Btheta_isQBrownianMotion_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Btheta_isQBrownianMotion_adapted

/-- info: 'MathFin.Btheta_isQBrownianMotion_predictable_of_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Btheta_isQBrownianMotion_predictable_of_bdd

/-- info: 'MathFin.Btheta_map_eq_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Btheta_map_eq_gaussianReal

/-- info: 'MathFin.Btheta_simple_isQBrownianMotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Btheta_simple_isQBrownianMotion

/-- info: 'MathFin.CIRSquaredOU.cirVariance_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CIRSquaredOU.cirVariance_mean

/-- info: 'MathFin.CMS.cmsCurveRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CMS.cmsCurveRate

/-- info: 'MathFin.CMS.cmsCurveRate_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CMS.cmsCurveRate_convexOn

/-- info: 'MathFin.CMS.cmsCurveRate_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CMS.cmsCurveRate_spanning

/-- info: 'MathFin.CMS.parSwapRate_update_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CMS.parSwapRate_update_eq

/-- info: 'MathFin.CVA.collateralizedExposure_brownian_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.collateralizedExposure_brownian_gaussian

/-- info: 'MathFin.CVA.cva_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.cva_gaussian

/-- info: 'MathFin.CVA.dva_eq_integral_expectedNegativeExposure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.dva_eq_integral_expectedNegativeExposure

/-- info: 'MathFin.CVA.expectedExposure_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.expectedExposure_of_hasLaw_gaussianReal

/-- info: 'MathFin.CVA.expectedNegativeExposure_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.expectedNegativeExposure_gaussian

/-- info: 'MathFin.CVA.integral_posPart_finsetSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.integral_posPart_finsetSum_le

/-- info: 'MathFin.CVA.potentialFutureExposure_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.potentialFutureExposure_of_hasLaw_gaussianReal

/-- info: 'MathFin.CVA.protectionLeg_eq_integral_coxDefaultTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.CVA.protectionLeg_eq_integral_coxDefaultTime

/-- info: 'MathFin.ContinuousMarket.IsEMM.sampled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ContinuousMarket.IsEMM.sampled

/-- info: 'MathFin.ContinuousMarket.isEMM_noArbitrageSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ContinuousMarket.isEMM_noArbitrageSimple

/-- info: 'MathFin.ContinuousMarket.martingale_comp_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ContinuousMarket.martingale_comp_monotone

/-- info: 'MathFin.Contracts.Binomial.assets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Binomial.assets

/-- info: 'MathFin.Contracts.Binomial.discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Binomial.discount

/-- info: 'MathFin.Contracts.Binomial.pathPV_eq_value_add_gains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Binomial.pathPV_eq_value_add_gains

/-- info: 'MathFin.Contracts.Binomial.valueAtRisk_hedged_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Binomial.valueAtRisk_hedged_eq_zero

/-- info: 'MathFin.Contracts.Binomial.value_cappedCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Binomial.value_cappedCall

/-- info: 'MathFin.Contracts.Binomial.value_pay_eq_binomialPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Binomial.value_pay_eq_binomialPrice

/-- info: 'MathFin.Contracts.BlackScholes.value_cappedCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.BlackScholes.value_cappedCall

/-- info: 'MathFin.Contracts.BlackScholes.value_digitalCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.BlackScholes.value_digitalCall

/-- info: 'MathFin.Contracts.BlackScholes.value_europeanCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.BlackScholes.value_europeanCall

/-- info: 'MathFin.Contracts.BlackScholes.value_europeanPut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.BlackScholes.value_europeanPut

/-- info: 'MathFin.Contracts.Contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Contract

/-- info: 'MathFin.Contracts.Contract.integrable_pathPV_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Contract.integrable_pathPV_of_bounded

/-- info: 'MathFin.Contracts.Contract.pathPV_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Contract.pathPV_both

/-- info: 'MathFin.Contracts.Contract.value_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Contract.value_both

/-- info: 'MathFin.Contracts.Contract.value_deliverAsset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Contract.value_deliverAsset

/-- info: 'MathFin.Contracts.Contract.value_eq_of_pathPV_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Contract.value_eq_of_pathPV_eq

/-- info: 'MathFin.Contracts.Payoff.measurable_eval_of_obsTimes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.Payoff.measurable_eval_of_obsTimes_le

/-- info: 'MathFin.Contracts.cappedCall_payoff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.cappedCall_payoff_eq

/-- info: 'MathFin.Contracts.expectedShortfall_loss_both_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.expectedShortfall_loss_both_le

/-- info: 'MathFin.Contracts.pathPV_fixedFlows_yieldDiscount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.pathPV_fixedFlows_yieldDiscount

/-- info: 'MathFin.Contracts.pathPV_fixedFlows_zcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.pathPV_fixedFlows_zcb

/-- info: 'MathFin.Contracts.scenarioAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.scenarioAt

/-- info: 'MathFin.Contracts.tendsto_binomial_value_europeanCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.tendsto_binomial_value_europeanCall

/-- info: 'MathFin.Contracts.valueAtRisk_loss_europeanCall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.valueAtRisk_loss_europeanCall_le

/-- info: 'MathFin.Contracts.valueDisc_fixedFlows_eq_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.valueDisc_fixedFlows_eq_value

/-- info: 'MathFin.Contracts.valueDisc_fixedFlows_gsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.valueDisc_fixedFlows_gsr

/-- info: 'MathFin.Contracts.valueDisc_fixedFlows_hullWhite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.valueDisc_fixedFlows_hullWhite

/-- info: 'MathFin.Contracts.valueDisc_fixedFlows_vasicek' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.valueDisc_fixedFlows_vasicek

/-- info: 'MathFin.Contracts.value_europeanCall_sub_put_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.value_europeanCall_sub_put_of_martingale

/-- info: 'MathFin.Contracts.value_forward_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.value_forward_of_martingale

/-- info: 'MathFin.Contracts.value_payerSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.value_payerSwap

/-- info: 'MathFin.Contracts.value_payerSwap_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Contracts.value_payerSwap_eq_zero_iff

/-- info: 'MathFin.DeFi.Compound.borrowIndex_le_inv_zcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.Compound.borrowIndex_le_inv_zcb

/-- info: 'MathFin.DeFi.Compound.tendsto_borrowIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.Compound.tendsto_borrowIndex

/-- info: 'MathFin.DeFi.Dai.debt_mul_zcb_log_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.Dai.debt_mul_zcb_log_eq

/-- info: 'MathFin.DeFi.arbitragePresent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.arbitragePresent_iff

/-- info: 'MathFin.DeFi.coveredCall_sub_v3PositionValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.coveredCall_sub_v3PositionValue

/-- info: 'MathFin.DeFi.impermanentLoss_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.impermanentLoss_eq

/-- info: 'MathFin.DeFi.impermanentLoss_eq_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.impermanentLoss_eq_neg_sq

/-- info: 'MathFin.DeFi.impermanentLoss_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.impermanentLoss_eq_zero_iff

/-- info: 'MathFin.DeFi.impermanentLoss_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.impermanentLoss_nonpos

/-- info: 'MathFin.DeFi.v3PositionValue_at_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.v3PositionValue_at_lower

/-- info: 'MathFin.DeFi.v3PositionValue_at_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.v3PositionValue_at_upper

/-- info: 'MathFin.DeFi.v3PositionValue_eq_coveredCall_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.v3PositionValue_eq_coveredCall_of_le

/-- info: 'MathFin.DeFi.v3PositionValue_eq_coveredCall_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.v3PositionValue_eq_coveredCall_of_lt

/-- info: 'MathFin.DeFi.v3PositionValue_le_coveredCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DeFi.v3PositionValue_le_coveredCall

/-- info: 'MathFin.DiscreteVaR.condTailMean_one_bond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DiscreteVaR.condTailMean_one_bond

/-- info: 'MathFin.DiscreteVaR.finiteES_eq_expectedShortfall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DiscreteVaR.finiteES_eq_expectedShortfall

/-- info: 'MathFin.DiscreteVaR.finiteES_one_bond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DiscreteVaR.finiteES_one_bond

/-- info: 'MathFin.DiscreteVaR.oneQ_mem_simplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.DiscreteVaR.oneQ_mem_simplex

/-- info: 'MathFin.Dupire.dupire_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Dupire.dupire_pointwise

/-- info: 'MathFin.ErlangSum.sum_iidExp_law_gammaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ErlangSum.sum_iidExp_law_gammaMeasure

/-- info: 'MathFin.Execution.condExp_payoff_eq_quote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Execution.condExp_payoff_eq_quote

/-- info: 'MathFin.Execution.measureReal_mul_ask_add_measureReal_mul_bid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Execution.measureReal_mul_ask_add_measureReal_mul_bid

/-- info: 'MathFin.Execution.spread_pos_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Execution.spread_pos_of_model

/-- info: 'MathFin.Execution.spread_pos_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Execution.spread_pos_witness

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanKac_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.FeynmanKacHeatEquation.feynmanKac_boundary

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanU_eq_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.FeynmanKacHeatEquation.feynmanU_eq_expectation

/-- info: 'MathFin.ForwardSmile.dupireRatio_sqrt_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ForwardSmile.dupireRatio_sqrt_slope

/-- info: 'MathFin.ForwardSmile.dupireRatio_sqrt_slope_eq_mul_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ForwardSmile.dupireRatio_sqrt_slope_eq_mul_skew

/-- info: 'MathFin.ForwardSmile.tendsto_dupireRatio_sqrt_slope_nhdsGT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ForwardSmile.tendsto_dupireRatio_sqrt_slope_nhdsGT_zero

/-- info: 'MathFin.GammaPoissonMixturePgf.mgf_id_gammaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.GammaPoissonMixturePgf.mgf_id_gammaMeasure

/-- info: 'MathFin.Heston.hestonTransform_pde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Heston.hestonTransform_pde

/-- info: 'MathFin.HullWhite.forwardMeasure_shortRate_mean_eq_forwardCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.HullWhite.forwardMeasure_shortRate_mean_eq_forwardCurve

/-- info: 'MathFin.HullWhite.integral_shortRate_sub_forwardMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.HullWhite.integral_shortRate_sub_forwardMeasure

/-- info: 'MathFin.HullWhite.reprices_curve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.HullWhite.reprices_curve

/-- info: 'MathFin.Inflation.Convexity.integral_exp_hwD_forwardMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Inflation.Convexity.integral_exp_hwD_forwardMeasure

/-- info: 'MathFin.IsBLPosteriorMean.blLoss_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.IsBLPosteriorMean.blLoss_le

/-- info: 'MathFin.IsCopula.sum_sub_le_measureReal_Iic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.IsCopula.sum_sub_le_measureReal_Iic

/-- info: 'MathFin.IsL2SolutionPair.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.IsL2SolutionPair.uniqueness

/-- info: 'MathFin.ItoFormulaAdapted.adaptedItoProcess_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.adaptedItoProcess_ae_eq

/-- info: 'MathFin.ItoFormulaAdapted.ae_continuousOn_adaptedItoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ae_continuousOn_adaptedItoProcess

/-- info: 'MathFin.ItoFormulaAdapted.exists_localMartingale_ito_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.exists_localMartingale_ito_formula

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_local_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_local_le

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_td_against' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_td_against

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_td_local_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_td_local_le

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_C2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_C2_le

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_C2_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_C2_process

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_le

/-- info: 'MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_process

/-- info: 'MathFin.ItoFormulaAdapted.tendstoInMeasure_riemannStieltjes_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoFormulaAdapted.tendstoInMeasure_riemannStieltjes_itoIntegral

/-- info: 'MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_elementary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_elementary

/-- info: 'MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_eq_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralAgainstMartingale.itoIntegralAgainst_eq_itoIntegral

/-- info: 'MathFin.ItoIntegralCovariation.covariation_itoIntegralCLM_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralCovariation.covariation_itoIntegralCLM_T

/-- info: 'MathFin.ItoIntegralL2.itoIntegralL2_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralL2.itoIntegralL2_norm

/-- info: 'MathFin.ItoIntegralLocalised.ae_continuousOn_localItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.ae_continuousOn_localItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.ae_continuousOn_predItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.ae_continuousOn_predItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.ae_localItoIntegral_eq_itoContinuousMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.ae_localItoIntegral_eq_itoContinuousMod

/-- info: 'MathFin.ItoIntegralLocalised.ae_localItoIntegral_eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.ae_localItoIntegral_eq_of_le

/-- info: 'MathFin.ItoIntegralLocalised.ae_predItoIntegral_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.ae_predItoIntegral_congr

/-- info: 'MathFin.ItoIntegralLocalised.ae_predItoIntegral_eq_localItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.ae_predItoIntegral_eq_localItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.exists_continuous_localMartingale_localItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.exists_continuous_localMartingale_localItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.exists_continuous_localMartingale_predItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.exists_continuous_localMartingale_predItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.stronglyAdapted_localItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.stronglyAdapted_localItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.stronglyAdapted_predItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.stronglyAdapted_predItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.tendstoInMeasure_riemannStieltjes_localItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.tendstoInMeasure_riemannStieltjes_localItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.tendstoInMeasure_riemannσ_localItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.tendstoInMeasure_riemannσ_localItoIntegral

/-- info: 'MathFin.ItoIntegralLocalised.tendstoInMeasure_riemannσ_predItoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralLocalised.tendstoInMeasure_riemannσ_predItoIntegral

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcessLp_l2_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcess.itoSimpleProcessLp_l2_continuous

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isLocalMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isLocalMartingale

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isMartingale

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isometry_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isometry_time

/-- info: 'MathFin.ItoIntegralProcess.memLp_itoSimpleProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcess.memLp_itoSimpleProcess

/-- info: 'MathFin.ItoIntegralProcessContinuousModification.exists_continuous_modification_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcessContinuousModification.exists_continuous_modification_itoProcess

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_isMartingale

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_l2_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_l2_continuous

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_terminal

/-- info: 'MathFin.ItoIntegralProcessLocalMartingaleGeneral.exists_continuous_localMartingale_modification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoIntegralProcessLocalMartingaleGeneral.exists_continuous_localMartingale_modification

/-- info: 'MathFin.ItoLocalMartingaleInfinite.exists_continuous_localMartingale_modification_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoLocalMartingaleInfinite.exists_continuous_localMartingale_modification_infinite

/-- info: 'MathFin.ItoProcessQV.tendsto_qv_ito_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ItoProcessQV.tendsto_qv_ito_process

/-- info: 'MathFin.JumpDiffusionHyp.call_eq_integral_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.call_eq_integral_bsV

/-- info: 'MathFin.JumpDiffusionHyp.call_eq_integral_infinitePi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.call_eq_integral_infinitePi

/-- info: 'MathFin.JumpDiffusionHyp.call_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.call_eq_mertonCallPrice

/-- info: 'MathFin.JumpDiffusionHyp.call_poisson_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.call_poisson_mixture

/-- info: 'MathFin.JumpDiffusionHyp.discounted_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.discounted_terminal

/-- info: 'MathFin.JumpDiffusionHyp.discounted_terminal_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.discounted_terminal_eq_iff

/-- info: 'MathFin.JumpDiffusionHyp.impliedVol_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.impliedVol_gt

/-- info: 'MathFin.JumpDiffusionHyp.jumpCounts_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.jumpCounts_split

/-- info: 'MathFin.JumpDiffusionHyp.toMertonHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionHyp.toMertonHyp

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_call

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call_eq_merton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_call_eq_merton

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_call_eq_mertonCallPrice

/-- info: 'MathFin.JumpDiffusionProcess.condExp_call_impliedVol_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_call_impliedVol_gt

/-- info: 'MathFin.JumpDiffusionProcess.condExp_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_comp

/-- info: 'MathFin.JumpDiffusionProcess.condExp_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_put

/-- info: 'MathFin.JumpDiffusionProcess.condExp_put_eq_mertonPutPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_put_eq_mertonPutPrice

/-- info: 'MathFin.JumpDiffusionProcess.condExp_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.condExp_rpow

/-- info: 'MathFin.JumpDiffusionProcess.hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.hasLaw

/-- info: 'MathFin.JumpDiffusionProcess.integral_logContract_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.integral_logContract_of_martingale

/-- info: 'MathFin.JumpDiffusionProcess.integral_sum_sq_increment_equipartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.integral_sum_sq_increment_equipartition

/-- info: 'MathFin.JumpDiffusionProcess.logContract_le_realizedVariance_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.logContract_le_realizedVariance_of_martingale

/-- info: 'MathFin.JumpDiffusionProcess.logContract_lt_realizedVariance_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.logContract_lt_realizedVariance_of_martingale

/-- info: 'MathFin.JumpDiffusionProcess.logContract_sub_realizedVariance_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.logContract_sub_realizedVariance_of_martingale

/-- info: 'MathFin.JumpDiffusionProcess.martingale_exp_const_mul_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.martingale_exp_const_mul_sub

/-- info: 'MathFin.JumpDiffusionProcess.martingale_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.martingale_iff

/-- info: 'MathFin.JumpDiffusionProcess.tendsto_integral_sum_sq_increment_equipartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.tendsto_integral_sum_sq_increment_equipartition

/-- info: 'MathFin.JumpDiffusionProcess.tendsto_logContract_sub_realizedVariance_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.JumpDiffusionProcess.tendsto_logContract_sub_realizedVariance_of_martingale

/-- info: 'MathFin.LSV.cointossM_atm_lt_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.LSV.cointossM_atm_lt_uncond

/-- info: 'MathFin.LSV.cointossM_comp_ae_eq_condExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.LSV.cointossM_comp_ae_eq_condExp

/-- info: 'MathFin.LSV.cointossM_eq_strike_convexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.LSV.cointossM_eq_strike_convexity

/-- info: 'MathFin.LSV.cointossM_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.LSV.cointossM_nonconstant

/-- info: 'MathFin.LSV.cointossM_wing_limit_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.LSV.cointossM_wing_limit_atTop

/-- info: 'MathFin.MarketCompletenessInPrice.exists_replicating_strategy_in_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.MarketCompletenessInPrice.exists_replicating_strategy_in_price

/-- info: 'MathFin.MonteCarlo.consistency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.MonteCarlo.consistency_canonical

/-- info: 'MathFin.MonteCarlo.hasLaw_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.MonteCarlo.hasLaw_canonical

/-- info: 'MathFin.MonteCarlo.mc_call_clt_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.MonteCarlo.mc_call_clt_canonical

/-- info: 'MathFin.MonteCarlo.mc_call_consistency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.MonteCarlo.mc_call_consistency_canonical

/-- info: 'MathFin.MonteCarlo.mc_call_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.MonteCarlo.mc_call_variance

/-- info: 'MathFin.OnePeriod.ftap_one_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.OnePeriod.ftap_one_period

/-- info: 'MathFin.OnePeriodVector.ftap_one_period_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.OnePeriodVector.ftap_one_period_vector

/-- info: 'MathFin.Phi_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.Phi_le_one

/-- info: 'MathFin.PointwiseBracket.condExp_band_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PointwiseBracket.condExp_band_second_moment

/-- info: 'MathFin.PoissonCounting.map_count_eq_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonCounting.map_count_eq_poissonMeasure

/-- info: 'MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure

/-- info: 'MathFin.PoissonInterarrival.survival_factorizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonInterarrival.survival_factorizes

/-- info: 'MathFin.PoissonPgf.integral_pow_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonPgf.integral_pow_poissonMeasure

/-- info: 'MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure

/-- info: 'MathFin.PoissonSuperposition.map_add_count_eq_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonSuperposition.map_add_count_eq_poissonMeasure

/-- info: 'MathFin.PoissonThinning.thinned_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonThinning.thinned_streams

/-- info: 'MathFin.PoissonThinning.thinned_streams_of_iid_marks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PoissonThinning.thinned_streams_of_iid_marks

/-- info: 'MathFin.PredictableDensityGeneral.simpleAssembly_sqWeight_denseRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PredictableDensityGeneral.simpleAssembly_sqWeight_denseRange

/-- info: 'MathFin.PricePathDrift.gainsDrift_eq_setIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PricePathDrift.gainsDrift_eq_setIntegral

/-- info: 'MathFin.PricingMeasureL2Density.measure_eq_of_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.PricingMeasureL2Density.measure_eq_of_density

/-- info: 'MathFin.SDEExistence.picardMap_exists_unique_fixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SDEExistence.picardMap_exists_unique_fixedPoint

/-- info: 'MathFin.SDEExistence.sde_pathwise_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SDEExistence.sde_pathwise_decomposition

/-- info: 'MathFin.SDEExistence.sde_pathwise_drift_eq_setIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SDEExistence.sde_pathwise_drift_eq_setIntegral

/-- info: 'MathFin.SVI.bsSmile_calendar_free_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.bsSmile_calendar_free_iff

/-- info: 'MathFin.SVI.bsSmile_convex_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.bsSmile_convex_iff

/-- info: 'MathFin.SVI.butterflyFreeFormula_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.butterflyFreeFormula_iff

/-- info: 'MathFin.SVI.butterflyFreeFormula_iff_isNormalizedCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.butterflyFreeFormula_iff_isNormalizedCallPrice

/-- info: 'MathFin.SVI.extendedCertificateFormula_iff_bsSmile_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.extendedCertificateFormula_iff_bsSmile_convex

/-- info: 'MathFin.SVI.fullCertificateFormula_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.fullCertificateFormula_iff

/-- info: 'MathFin.SVI.tendsto_blackPlus_atBot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.tendsto_blackPlus_atBot_iff

/-- info: 'MathFin.SVI.tendsto_bsSmile_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SVI.tendsto_bsSmile_zero_iff

/-- info: 'MathFin.StochasticIntegralCharacterisation.isStochasticIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.StochasticIntegralCharacterisation.isStochasticIntegral

/-- info: 'MathFin.SurvivalModel.survivalFunction_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SurvivalModel.survivalFunction_zero

/-- info: 'MathFin.SurvivalModel.survive_eq_survivalFunction_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.SurvivalModel.survive_eq_survivalFunction_ratio

/-- info: 'MathFin.WienerIntegralL2.integral_exp_neg_add_mul_wienerIntegralLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.WienerIntegralL2.integral_exp_neg_add_mul_wienerIntegralLp

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_integral_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.WienerIntegralL2.wienerIntegralLp_integral_sq

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal

/-- info: 'MathFin.abcdForward_call_eq_black76' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.abcdForward_call_eq_black76

/-- info: 'MathFin.abcdWienerIntegral_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.abcdWienerIntegral_hasLaw

/-- info: 'MathFin.acceptableUnderUtility_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.acceptableUnderUtility_convex

/-- info: 'MathFin.acceptableUnderUtility_log_iff_kellyGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.acceptableUnderUtility_log_iff_kellyGrowth

/-- info: 'MathFin.affineBondPrice_solves_pde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.affineBondPrice_solves_pde

/-- info: 'MathFin.almgrenChrissPath_satisfies_EL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.almgrenChrissPath_satisfies_EL

/-- info: 'MathFin.am_gm_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.am_gm_two

/-- info: 'MathFin.americanCallPrice_eq_binomialPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.americanCallPrice_eq_binomialPrice

/-- info: 'MathFin.annuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.annuity

/-- info: 'MathFin.annuityDue_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.annuityDue_closed_form

/-- info: 'MathFin.annuityValue_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.annuityValue_closed_form

/-- info: 'MathFin.asianGeom_driver_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.asianGeom_driver_hasLaw

/-- info: 'MathFin.asian_payoff_geom_le_arith_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.asian_payoff_geom_le_arith_two

/-- info: 'MathFin.bachelier_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bachelier_call_formula

/-- info: 'MathFin.basketMomentMatchPrice_single_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.basketMomentMatchPrice_single_eq_integral

/-- info: 'MathFin.betSize_sqrt_mul_zScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.betSize_sqrt_mul_zScore

/-- info: 'MathFin.beta_linearity_finset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.beta_linearity_finset

/-- info: 'MathFin.beta_linearity_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.beta_linearity_two

/-- info: 'MathFin.beta_market' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.beta_market

/-- info: 'MathFin.beta_of_riskFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.beta_of_riskFree

/-- info: 'MathFin.beta_singleIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.beta_singleIndex

/-- info: 'MathFin.binomialOptionPriceOnePeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialOptionPriceOnePeriod

/-- info: 'MathFin.binomialPrice_call_tendsto_bs_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialPrice_call_tendsto_bs_closed

/-- info: 'MathFin.binomialPrice_eq_integral_coinFlipMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialPrice_eq_integral_coinFlipMeasure

/-- info: 'MathFin.binomialPrice_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialPrice_le_americanPrice

/-- info: 'MathFin.binomialPrice_le_bermudanPrice_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialPrice_le_bermudanPrice_le_americanPrice

/-- info: 'MathFin.binomialPrice_replication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialPrice_replication

/-- info: 'MathFin.binomialRN_expectation_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomialRN_expectation_one

/-- info: 'MathFin.binomial_martingale_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomial_martingale_representation

/-- info: 'MathFin.binomial_maximal_distribution_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomial_maximal_distribution_card

/-- info: 'MathFin.binomial_replicatingPortfolio_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomial_replicatingPortfolio_unique

/-- info: 'MathFin.binomial_replication_cost_eq_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomial_replication_cost_eq_price

/-- info: 'MathFin.binomial_replication_cost_eq_pricingKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.binomial_replication_cost_eq_pricingKernel

/-- info: 'MathFin.blackLitterman_mean_eq_precision_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.blackLitterman_mean_eq_precision_weighted

/-- info: 'MathFin.blackLitterman_var_eq_inv_sum_precision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.blackLitterman_var_eq_inv_sum_precision

/-- info: 'MathFin.black_futures_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.black_futures_formula

/-- info: 'MathFin.bondForwardPrice_from_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bondForwardPrice_from_no_arbitrage

/-- info: 'MathFin.bondPortfolio_immunization_first_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bondPortfolio_immunization_first_order

/-- info: 'MathFin.bondPortfolio_immunization_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bondPortfolio_immunization_second_order

/-- info: 'MathFin.bondPortfolio_single_bond_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bondPortfolio_single_bond_conv

/-- info: 'MathFin.bondPortfolio_single_bond_dur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bondPortfolio_single_bond_dur

/-- info: 'MathFin.bondPortfolio_single_bond_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bondPortfolio_single_bond_value

/-- info: 'MathFin.bootstrap_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bootstrap_consistency

/-- info: 'MathFin.bootstrap_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bootstrap_solve

/-- info: 'MathFin.bootstrap_solve_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bootstrap_solve_first

/-- info: 'MathFin.bootstrap_solve_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bootstrap_solve_second

/-- info: 'MathFin.box_spread_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.box_spread_identity

/-- info: 'MathFin.breedenLitzenberger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.breedenLitzenberger

/-- info: 'MathFin.breedenLitzenberger_jumpDiffusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.breedenLitzenberger_jumpDiffusion

/-- info: 'MathFin.brownian_markov_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.brownian_markov_property

/-- info: 'MathFin.bsLogReturn_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsLogReturn_hasLaw

/-- info: 'MathFin.bsP_le_K_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsP_le_K_disc

/-- info: 'MathFin.bsV_ge_forward_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_ge_forward_lower_bound

/-- info: 'MathFin.bsV_le_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_le_S

/-- info: 'MathFin.bsV_le_jumpDiffusion_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_le_jumpDiffusion_call

/-- info: 'MathFin.bsV_le_lookbackCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_le_lookbackCall

/-- info: 'MathFin.bsV_le_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_le_mertonCallPrice

/-- info: 'MathFin.bsV_lt_jumpDiffusion_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_lt_jumpDiffusion_call

/-- info: 'MathFin.bsV_satisfies_bs_pde_via_feynmanKac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_satisfies_bs_pde_via_feynmanKac

/-- info: 'MathFin.bsV_spot_strictConvexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_spot_strictConvexOn

/-- info: 'MathFin.bsV_spot_tangent_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_spot_tangent_lt

/-- info: 'MathFin.bsV_strict_gt_immediate_exercise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_strict_gt_immediate_exercise

/-- info: 'MathFin.bsV_strike_strictConvexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bsV_strike_strictConvexOn

/-- info: 'MathFin.bs_asset_or_nothing_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_asset_or_nothing_formula

/-- info: 'MathFin.bs_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_call_formula

/-- info: 'MathFin.bs_cash_or_nothing_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_cash_or_nothing_formula

/-- info: 'MathFin.bs_discounted_isQMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_discounted_isQMartingale

/-- info: 'MathFin.bs_dividends_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_dividends_call_formula

/-- info: 'MathFin.bs_pde_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_pde_holds

/-- info: 'MathFin.bs_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_put_call_parity

/-- info: 'MathFin.bs_put_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bs_put_formula

/-- info: 'MathFin.bull_call_spread_payoff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.bull_call_spread_payoff_le

/-- info: 'MathFin.butterfly_payoff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.butterfly_payoff_nonneg

/-- info: 'MathFin.calendar_free_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.calendar_free_iff

/-- info: 'MathFin.caplet_floorlet_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.caplet_floorlet_parity

/-- info: 'MathFin.cappedCall_eq_bull_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cappedCall_eq_bull_spread

/-- info: 'MathFin.carrMadan_log_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.carrMadan_log_spanning

/-- info: 'MathFin.carrMadan_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.carrMadan_spanning

/-- info: 'MathFin.cdf_expMeasure_inMDA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cdf_expMeasure_inMDA

/-- info: 'MathFin.cds_leg_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cds_leg_equality

/-- info: 'MathFin.changeOfMeasure_setIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.changeOfMeasure_setIntegral_eq

/-- info: 'MathFin.changeOfNumeraire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.changeOfNumeraire

/-- info: 'MathFin.chooser_price_eq_expected_payoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.chooser_price_eq_expected_payoff

/-- info: 'MathFin.chooser_via_pcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.chooser_via_pcp

/-- info: 'MathFin.cirBondA_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cirBondA_zero

/-- info: 'MathFin.cirBondB_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cirBondB_zero

/-- info: 'MathFin.cirBondPrice_solves_pde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cirBondPrice_solves_pde

/-- info: 'MathFin.cml_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cml_equation

/-- info: 'MathFin.cml_mean_at_stdev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cml_mean_at_stdev

/-- info: 'MathFin.cml_sharpeRatio_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cml_sharpeRatio_invariant

/-- info: 'MathFin.cml_weight_recovers_stdev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cml_weight_recovers_stdev

/-- info: 'MathFin.cml_weight_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.cml_weight_unique

/-- info: 'MathFin.coherentRisk_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.coherentRisk_isLUB

/-- info: 'MathFin.coinFlipMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.coinFlipMeasure

/-- info: 'MathFin.compensated_integral_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.compensated_integral_isometry

/-- info: 'MathFin.compensated_simple_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.compensated_simple_isometry

/-- info: 'MathFin.compoundPoisson_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.compoundPoisson_mgf

/-- info: 'MathFin.compoundPoisson_mgf_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.compoundPoisson_mgf_of_indepFun

/-- info: 'MathFin.condExp_comp_prodMk_of_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.condExp_comp_prodMk_of_indep

/-- info: 'MathFin.condExp_shift_eq_integral_gaussianLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.condExp_shift_eq_integral_gaussianLimit

/-- info: 'MathFin.continuous_jumpDiffusionDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.continuous_jumpDiffusionDensity

/-- info: 'MathFin.convexOn_integral_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.convexOn_integral_call

/-- info: 'MathFin.convexOn_jumpDiffusionCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.convexOn_jumpDiffusionCallPrice_strike

/-- info: 'MathFin.copulaOf_comp_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.copulaOf_comp_strictMono

/-- info: 'MathFin.couponBondPrice_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.couponBondPrice_strictAnti

/-- info: 'MathFin.covariance_eq_integral_cdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_eq_integral_cdf

/-- info: 'MathFin.covariance_gaussianPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_gaussianPair

/-- info: 'MathFin.covariance_indicator_default_gaussianThresholds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_indicator_default_gaussianThresholds

/-- info: 'MathFin.covariance_indicator_marshallOlkin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_indicator_marshallOlkin

/-- info: 'MathFin.covariance_indicator_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_indicator_one_le

/-- info: 'MathFin.covariance_le_covariance_of_cdf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_le_covariance_of_cdf_le

/-- info: 'MathFin.covariance_le_sqrt_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_le_sqrt_mul_sqrt

/-- info: 'MathFin.covariance_rollPriceChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covariance_rollPriceChange

/-- info: 'MathFin.covered_eq_uncovered_interest_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covered_eq_uncovered_interest_parity

/-- info: 'MathFin.covered_interest_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.covered_interest_parity

/-- info: 'MathFin.creditSpread_eq_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.creditSpread_eq_hazard

/-- info: 'MathFin.creditSpread_eq_time_avg_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.creditSpread_eq_time_avg_hazard

/-- info: 'MathFin.crrProb_tendsto_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crrProb_tendsto_half

/-- info: 'MathFin.crrRowLaw_moments_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crrRowLaw_moments_tendsto

/-- info: 'MathFin.crr_americanCall_tendsto_bs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crr_americanCall_tendsto_bs

/-- info: 'MathFin.crr_drift_limit_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crr_drift_limit_h

/-- info: 'MathFin.crr_drift_limit_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crr_drift_limit_n

/-- info: 'MathFin.crr_one_step_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crr_one_step_martingale

/-- info: 'MathFin.crr_tendsto_gaussian_inDistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crr_tendsto_gaussian_inDistribution

/-- info: 'MathFin.crr_variance_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.crr_variance_limit

/-- info: 'MathFin.defaultCorrelation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.defaultCorrelation_eq

/-- info: 'MathFin.differentiableAt_integral_call_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.differentiableAt_integral_call_iff

/-- info: 'MathFin.differentiableAt_jumpDiffusionCallPrice_strike_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.differentiableAt_jumpDiffusionCallPrice_strike_iff

/-- info: 'MathFin.discountedCallBrownian_heat_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discountedCallBrownian_heat_equation

/-- info: 'MathFin.discountedGBM_eq_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discountedGBM_eq_itoIntegral

/-- info: 'MathFin.discountedGBM_isEMM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discountedGBM_isEMM

/-- info: 'MathFin.discountedGBM_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discountedGBM_isMartingale

/-- info: 'MathFin.discountedGBM_noArbitrageSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discountedGBM_noArbitrageSimple

/-- info: 'MathFin.discountedSpot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discountedSpot

/-- info: 'MathFin.discounted_americanPrice_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discounted_americanPrice_supermartingale

/-- info: 'MathFin.discounted_intrinsic_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discounted_intrinsic_le_americanPrice

/-- info: 'MathFin.discrete_cubing_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.discrete_cubing_identity

/-- info: 'MathFin.doob_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.doob_decomposition

/-- info: 'MathFin.downsideMetrics_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.downsideMetrics_bundle

/-- info: 'MathFin.effNotionalIR_eq_sqrt_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.effNotionalIR_eq_sqrt_variance

/-- info: 'MathFin.effNotionalIR_le_abs_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.effNotionalIR_le_abs_add

/-- info: 'MathFin.effNotionalIR_radicand_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.effNotionalIR_radicand_nonneg

/-- info: 'MathFin.emm_implies_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.emm_implies_no_arbitrage

/-- info: 'MathFin.emm_le_superReplication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.emm_le_superReplication

/-- info: 'MathFin.eq_bivariateNormalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.eq_bivariateNormalLaw

/-- info: 'MathFin.eq_copulaOf_of_measureReal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.eq_copulaOf_of_measureReal_le

/-- info: 'MathFin.exchangeOption_numeraire_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exchangeOption_numeraire_price

/-- info: 'MathFin.existsUnique_esscher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.existsUnique_esscher

/-- info: 'MathFin.existsUnique_expectileGap_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.existsUnique_expectileGap_eq_zero

/-- info: 'MathFin.exists_call_esscher_ne_merton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_call_esscher_ne_merton

/-- info: 'MathFin.exists_gaussian_uncorrelated_not_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_gaussian_uncorrelated_not_indepFun

/-- info: 'MathFin.exists_impliedVol_gt_of_bsV_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_impliedVol_gt_of_bsV_lt

/-- info: 'MathFin.exists_isCopula_fgm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_isCopula_fgm_iff

/-- info: 'MathFin.exists_pos_price_le_superReplication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_pos_price_le_superReplication

/-- info: 'MathFin.exists_pos_separating_of_cone_disjoint_simplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_pos_separating_of_cone_disjoint_simplex

/-- info: 'MathFin.exists_replicating_strategy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.exists_replicating_strategy

/-- info: 'MathFin.expectedShortfall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall

/-- info: 'MathFin.expectedShortfall_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_add_le

/-- info: 'MathFin.expectedShortfall_eq_acerbiTasche' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_eq_acerbiTasche

/-- info: 'MathFin.expectedShortfall_eq_setIntegral_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_eq_setIntegral_tail

/-- info: 'MathFin.expectedShortfall_isCoherentRiskMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_isCoherentRiskMeasure

/-- info: 'MathFin.expectedShortfall_isLUB_representingSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_isLUB_representingSet

/-- info: 'MathFin.expectedShortfall_mono_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_mono_level

/-- info: 'MathFin.expectedShortfall_of_hasLaw_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_of_hasLaw_expMeasure

/-- info: 'MathFin.expectedShortfall_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_of_hasLaw_gaussianReal

/-- info: 'MathFin.expectedShortfall_of_hasLaw_lomaxMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_of_hasLaw_lomaxMeasure

/-- info: 'MathFin.expectedShortfall_of_hasLaw_studentTMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedShortfall_of_hasLaw_studentTMeasure

/-- info: 'MathFin.expectedUtility_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectedUtility_mix

/-- info: 'MathFin.expected_terminal_eq_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expected_terminal_eq_forward

/-- info: 'MathFin.expectile_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectile_half

/-- info: 'MathFin.expectile_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.expectile_mono

/-- info: 'MathFin.firstToDefault_spread_eq_sum_hazards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.firstToDefault_spread_eq_sum_hazards

/-- info: 'MathFin.forwardMeasure_bs_expected_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.forwardMeasure_bs_expected_terminal

/-- info: 'MathFin.forward_price_eq_spot_div_discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.forward_price_eq_spot_div_discount

/-- info: 'MathFin.fraValue_zcb_eq_discount_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.fraValue_zcb_eq_discount_difference

/-- info: 'MathFin.fraValue_zcb_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.fraValue_zcb_eq_zero_iff

/-- info: 'MathFin.ftap_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ftap_discrete

/-- info: 'MathFin.gainToPain_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gainToPain_nonneg

/-- info: 'MathFin.garman_kohlhagen_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.garman_kohlhagen_call_formula

/-- info: 'MathFin.gaussianCVaR_additive_at_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_additive_at_rho_one

/-- info: 'MathFin.gaussianCVaR_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_affine

/-- info: 'MathFin.gaussianCVaR_isLeast_ruObjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_isLeast_ruObjective

/-- info: 'MathFin.gaussianCVaR_monotone_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_monotone_mean

/-- info: 'MathFin.gaussianCVaR_positiveHomogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_positiveHomogeneity

/-- info: 'MathFin.gaussianCVaR_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_standard

/-- info: 'MathFin.gaussianCVaR_sub_VaR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_sub_VaR

/-- info: 'MathFin.gaussianCVaR_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_subadditive

/-- info: 'MathFin.gaussianCVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianCVaR_translation

/-- info: 'MathFin.gaussianPDFReal_zero_one_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianPDFReal_zero_one_neg

/-- info: 'MathFin.gaussianReal_tilted_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianReal_tilted_const_mul

/-- info: 'MathFin.gaussianVaR_additive_at_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_additive_at_rho_one

/-- info: 'MathFin.gaussianVaR_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_affine

/-- info: 'MathFin.gaussianVaR_monotone_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_monotone_mean

/-- info: 'MathFin.gaussianVaR_positiveHomogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_positiveHomogeneity

/-- info: 'MathFin.gaussianVaR_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_standard

/-- info: 'MathFin.gaussianVaR_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_subadditive

/-- info: 'MathFin.gaussianVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_translation

/-- info: 'MathFin.gaussianVaR_volatility_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gaussianVaR_volatility_scaling

/-- info: 'MathFin.geomAsianN_bsV_le_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.geomAsianN_bsV_le_arith

/-- info: 'MathFin.geomAsianN_call_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.geomAsianN_call_price

/-- info: 'MathFin.geomAsianN_driver_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.geomAsianN_driver_hasLaw

/-- info: 'MathFin.geom_mean_le_arith_mean_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.geom_mean_le_arith_mean_n

/-- info: 'MathFin.gevCDF_max_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gevCDF_max_stable

/-- info: 'MathFin.gompertz_cumulative_force' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gompertz_cumulative_force

/-- info: 'MathFin.gpdCDF_inMDA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gpdCDF_inMDA

/-- info: 'MathFin.gsrBondPrice_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.gsrBondPrice_eq

/-- info: 'MathFin.hasDerivAt_S_deriv_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_S_deriv_bsV_sigma

/-- info: 'MathFin.hasDerivAt_T_mul_spotRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_T_mul_spotRate

/-- info: 'MathFin.hasDerivAt_bachelierV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bachelierV_S

/-- info: 'MathFin.hasDerivAt_bachelierV_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bachelierV_T

/-- info: 'MathFin.hasDerivAt_bachelierV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bachelierV_sigma

/-- info: 'MathFin.hasDerivAt_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_blackV_F

/-- info: 'MathFin.hasDerivAt_blackV_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_blackV_T

/-- info: 'MathFin.hasDerivAt_blackV_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_blackV_r

/-- info: 'MathFin.hasDerivAt_blackV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_blackV_sigma

/-- info: 'MathFin.hasDerivAt_bondPortfolioDur_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bondPortfolioDur_r

/-- info: 'MathFin.hasDerivAt_bondPortfolioValue_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bondPortfolioValue_r

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsAssetDigital_S

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsAssetDigital_r

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsAssetDigital_sigma

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsAssetDigital_tau

/-- info: 'MathFin.hasDerivAt_bsCashDigital_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsCashDigital_K

/-- info: 'MathFin.hasDerivAt_bsCashDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsCashDigital_S

/-- info: 'MathFin.hasDerivAt_bsCashDigital_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsCashDigital_r

/-- info: 'MathFin.hasDerivAt_bsCashDigital_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsCashDigital_sigma

/-- info: 'MathFin.hasDerivAt_bsCashDigital_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsCashDigital_tau

/-- info: 'MathFin.hasDerivAt_bsP_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsP_K

/-- info: 'MathFin.hasDerivAt_bsP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsP_S

/-- info: 'MathFin.hasDerivAt_bsP_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsP_r

/-- info: 'MathFin.hasDerivAt_bsP_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsP_sigma

/-- info: 'MathFin.hasDerivAt_bsP_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsP_tau

/-- info: 'MathFin.hasDerivAt_bsVDiv_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsVDiv_S

/-- info: 'MathFin.hasDerivAt_bsVDiv_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsVDiv_q

/-- info: 'MathFin.hasDerivAt_bsVDiv_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsVDiv_r

/-- info: 'MathFin.hasDerivAt_bsVDiv_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsVDiv_sigma

/-- info: 'MathFin.hasDerivAt_bsVDiv_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsVDiv_tau

/-- info: 'MathFin.hasDerivAt_bsV_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsV_K

/-- info: 'MathFin.hasDerivAt_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsV_S

/-- info: 'MathFin.hasDerivAt_bsV_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsV_r

/-- info: 'MathFin.hasDerivAt_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsV_sigma

/-- info: 'MathFin.hasDerivAt_bsV_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsV_t

/-- info: 'MathFin.hasDerivAt_bsd1_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsd1_K

/-- info: 'MathFin.hasDerivAt_bsd2_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_bsd2_K

/-- info: 'MathFin.hasDerivAt_cirBondA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_cirBondA

/-- info: 'MathFin.hasDerivAt_cirBondB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_cirBondB

/-- info: 'MathFin.hasDerivAt_deriv_bachelierV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bachelierV_S

/-- info: 'MathFin.hasDerivAt_deriv_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_blackV_F

/-- info: 'MathFin.hasDerivAt_deriv_bondPortfolioValue_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bondPortfolioValue_r

/-- info: 'MathFin.hasDerivAt_deriv_bsAssetDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsAssetDigital_S

/-- info: 'MathFin.hasDerivAt_deriv_bsCashDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsCashDigital_S

/-- info: 'MathFin.hasDerivAt_deriv_bsP_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsP_K

/-- info: 'MathFin.hasDerivAt_deriv_bsP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsP_S

/-- info: 'MathFin.hasDerivAt_deriv_bsVDiv_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsVDiv_S

/-- info: 'MathFin.hasDerivAt_deriv_bsV_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsV_K

/-- info: 'MathFin.hasDerivAt_deriv_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsV_S

/-- info: 'MathFin.hasDerivAt_deriv_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_bsV_sigma

/-- info: 'MathFin.hasDerivAt_deriv_deriv_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_deriv_blackV_F

/-- info: 'MathFin.hasDerivAt_deriv_deriv_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_deriv_bsV_S

/-- info: 'MathFin.hasDerivAt_deriv_mertonCallPrice_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_mertonCallPrice_spot

/-- info: 'MathFin.hasDerivAt_deriv_mertonCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_deriv_mertonCallPrice_strike

/-- info: 'MathFin.hasDerivAt_discountedCallBrownian_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_discountedCallBrownian_x

/-- info: 'MathFin.hasDerivAt_integral_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_integral_call

/-- info: 'MathFin.hasDerivAt_jumpDiffusionCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_jumpDiffusionCallPrice_strike

/-- info: 'MathFin.hasDerivAt_jumpDiffusionDigitalPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_jumpDiffusionDigitalPrice_strike

/-- info: 'MathFin.hasDerivAt_log_sabrBackbone_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_log_sabrBackbone_exp

/-- info: 'MathFin.hasDerivAt_matrixRiccatiCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_matrixRiccatiCoeff

/-- info: 'MathFin.hasDerivAt_mertonCallPrice_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_mertonCallPrice_sigma

/-- info: 'MathFin.hasDerivAt_mertonCallPrice_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_mertonCallPrice_spot

/-- info: 'MathFin.hasDerivAt_mertonCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_mertonCallPrice_strike

/-- info: 'MathFin.hasDerivAt_mertonDigitalPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_mertonDigitalPrice_strike

/-- info: 'MathFin.hasDerivAt_mmMatrixValueCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_mmMatrixValueCoeff

/-- info: 'MathFin.hasDerivAt_neg_log_zcb_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_neg_log_zcb_T

/-- info: 'MathFin.hasDerivAt_portfolioVaRN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_portfolioVaRN

/-- info: 'MathFin.hasDerivAt_riccatiCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_riccatiCoeff

/-- info: 'MathFin.hasDerivAt_tau_deriv_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasDerivAt_tau_deriv_bsV_S

/-- info: 'MathFin.hasEMM_multi_iff_not_hasArbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasEMM_multi_iff_not_hasArbitrage

/-- info: 'MathFin.hasEMM_multi_state_iff_exists_isEMM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasEMM_multi_state_iff_exists_isEMM

/-- info: 'MathFin.hasEMM_two_state_iff_not_hasArbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasEMM_two_state_iff_not_hasArbitrage

/-- info: 'MathFin.hasGaussianLaw_gaussianPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasGaussianLaw_gaussianPair

/-- info: 'MathFin.hasLaw_cdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasLaw_cdf

/-- info: 'MathFin.hasLaw_fracDiff_one_driftEstimator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasLaw_fracDiff_one_driftEstimator

/-- info: 'MathFin.hasLaw_quantile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasLaw_quantile

/-- info: 'MathFin.hasSum_fracDiffWeight_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hasSum_fracDiffWeight_mul_pow

/-- info: 'MathFin.hazardSurvival_eq_const_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hazardSurvival_eq_const_survival

/-- info: 'MathFin.hazard_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.hazard_eq_neg_log_deriv_survival

/-- info: 'MathFin.herfindahl_card_inv_le_of_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.herfindahl_card_inv_le_of_sum_one

/-- info: 'MathFin.heynenKatA_call_rho_zero_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.heynenKatA_call_rho_zero_eq_bsV

/-- info: 'MathFin.impliedVol_bisection_converges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.impliedVol_bisection_converges

/-- info: 'MathFin.impliedVol_bracket_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.impliedVol_bracket_exists

/-- info: 'MathFin.implied_volatility_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.implied_volatility_unique

/-- info: 'MathFin.indepFun_of_purged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.indepFun_of_purged

/-- info: 'MathFin.informationRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.informationRatio_scale_invariant

/-- info: 'MathFin.integral_abs_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_abs_gaussianReal

/-- info: 'MathFin.integral_basket_eq_basketM1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_basket_eq_basketM1

/-- info: 'MathFin.integral_basket_sq_eq_basketM2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_basket_sq_eq_basketM2

/-- info: 'MathFin.integral_betterOfTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_betterOfTwo

/-- info: 'MathFin.integral_bilinear_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_bilinear_pairing

/-- info: 'MathFin.integral_bivariateNormalCDF_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_bivariateNormalCDF_sub_mul

/-- info: 'MathFin.integral_bsV_mul_exp_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_bsV_mul_exp_gaussianReal

/-- info: 'MathFin.integral_call_tilted_eq_merton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_call_tilted_eq_merton

/-- info: 'MathFin.integral_call_tilted_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_call_tilted_eq_mertonCallPrice

/-- info: 'MathFin.integral_call_tilted_zero_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_call_tilted_zero_eq_bsV

/-- info: 'MathFin.integral_comp_prodMk_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_comp_prodMk_of_indepFun

/-- info: 'MathFin.integral_compoundPoisson_mgf_gammaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_compoundPoisson_mgf_gammaMeasure

/-- info: 'MathFin.integral_discounted_v3PositionValue_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_discounted_v3PositionValue_le

/-- info: 'MathFin.integral_exp_const_mul_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_exp_const_mul_jumpDiffusionIncrementLaw

/-- info: 'MathFin.integral_exp_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_exp_gaussianReal

/-- info: 'MathFin.integral_exp_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_exp_jumpDiffusionIncrementLaw

/-- info: 'MathFin.integral_gaussianPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_gaussianPair

/-- info: 'MathFin.integral_id_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_id_jumpDiffusionIncrementLaw

/-- info: 'MathFin.integral_logContract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_logContract

/-- info: 'MathFin.integral_logContract_of_integral_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_logContract_of_integral_exp

/-- info: 'MathFin.integral_log_forward_div_bsTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_log_forward_div_bsTerminal_eq

/-- info: 'MathFin.integral_lpValue_eq_exp_mul_integral_hodlValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_lpValue_eq_exp_mul_integral_hodlValue

/-- info: 'MathFin.integral_mertonSpot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_mertonSpot

/-- info: 'MathFin.integral_posPart_oneFactorPD_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_posPart_oneFactorPD_sub

/-- info: 'MathFin.integral_posPart_sub_mono_of_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_posPart_sub_mono_of_martingale

/-- info: 'MathFin.integral_scaledHermite_vasicekShortRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_scaledHermite_vasicekShortRate

/-- info: 'MathFin.integral_sq_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_sq_jumpDiffusionIncrementLaw

/-- info: 'MathFin.integral_sub_cond_gpdMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.integral_sub_cond_gpdMeasure

/-- info: 'MathFin.isCoherentRiskMeasure_spectralRiskMeasure_sum_esSpectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isCoherentRiskMeasure_spectralRiskMeasure_sum_esSpectrum

/-- info: 'MathFin.isCopula_copulaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isCopula_copulaOf

/-- info: 'MathFin.isEMM_one_iff_onePeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isEMM_one_iff_onePeriod

/-- info: 'MathFin.isGreatest_integral_mul_expectedShortfall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isGreatest_integral_mul_expectedShortfall

/-- info: 'MathFin.isLeast_rockafellarUryasev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isLeast_rockafellarUryasev

/-- info: 'MathFin.isLocalizingSequence_exitTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isLocalizingSequence_exitTime

/-- info: 'MathFin.isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN

/-- info: 'MathFin.isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN

/-- info: 'MathFin.isRiskParity_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isRiskParity_two_iff

/-- info: 'MathFin.isStoppingTime_hittingAfter_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isStoppingTime_hittingAfter_of_open

/-- info: 'MathFin.isTangent_of_proportional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.isTangent_of_proportional

/-- info: 'MathFin.itoDrift_expectation_identity_adaptedItoProcess_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.itoDrift_expectation_identity_adaptedItoProcess_of_le

/-- info: 'MathFin.itoDrift_expectation_identity_adapted_at_adaptedItoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.itoDrift_expectation_identity_adapted_at_adaptedItoProcess

/-- info: 'MathFin.itoIntegralCLM_T_surjective_onto_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.itoIntegralCLM_T_surjective_onto_centered

/-- info: 'MathFin.itoLevyIntegralL2_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.itoLevyIntegralL2_norm

/-- info: 'MathFin.ito_formula_L2_bddDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_L2_bddDeriv

/-- info: 'MathFin.ito_formula_gbm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_gbm

/-- info: 'MathFin.ito_formula_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_itoProcess

/-- info: 'MathFin.ito_formula_td_L2_bddDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_td_L2_bddDeriv

/-- info: 'MathFin.ito_formula_td_localized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_td_localized

/-- info: 'MathFin.ito_formula_td_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_td_process

/-- info: 'MathFin.ito_formula_unrestricted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_unrestricted

/-- info: 'MathFin.ito_formula_unrestricted_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ito_formula_unrestricted_local

/-- info: 'MathFin.joint_stdev_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.joint_stdev_le

/-- info: 'MathFin.jumpDiffusionCallPrice_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionCallPrice_eq

/-- info: 'MathFin.jumpDiffusionCallPrice_eq_of_compensated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionCallPrice_eq_of_compensated

/-- info: 'MathFin.jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice

/-- info: 'MathFin.jumpDiffusionCallPrice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionCallPrice_zero

/-- info: 'MathFin.jumpDiffusionDensity_div_eq_lognormalTerminalPDF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionDensity_div_eq_lognormalTerminalPDF

/-- info: 'MathFin.jumpDiffusionDensity_gaussian_div_eq_mertonTerminalPDF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionDensity_gaussian_div_eq_mertonTerminalPDF

/-- info: 'MathFin.jumpDiffusionDensity_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionDensity_pos

/-- info: 'MathFin.jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice

/-- info: 'MathFin.jumpDiffusionDigitalPrice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionDigitalPrice_zero

/-- info: 'MathFin.jumpDiffusionExponent_zero_esscher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionExponent_zero_esscher

/-- info: 'MathFin.jumpDiffusionHyp_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionHyp_canonical

/-- info: 'MathFin.jumpDiffusionIncrementLaw_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_eq_iff

/-- info: 'MathFin.jumpDiffusionIncrementLaw_eq_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_eq_withDensity

/-- info: 'MathFin.jumpDiffusionIncrementLaw_gaussian_map_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_gaussian_map_mul_exp

/-- info: 'MathFin.jumpDiffusionIncrementLaw_map_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_map_const_mul

/-- info: 'MathFin.jumpDiffusionIncrementLaw_map_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_map_mul_exp

/-- info: 'MathFin.jumpDiffusionIncrementLaw_price_mem_Ioo_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_price_mem_Ioo_ne_zero

/-- info: 'MathFin.jumpDiffusionIncrementLaw_tilted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_tilted

/-- info: 'MathFin.jumpDiffusionIncrementLaw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_zero

/-- info: 'MathFin.jumpDiffusionIncrementLaw_zero_map_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionIncrementLaw_zero_map_mul_exp

/-- info: 'MathFin.jumpDiffusionProcess_brownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionProcess_brownian

/-- info: 'MathFin.jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice

/-- info: 'MathFin.jumpDiffusionPutPrice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusionPutPrice_zero

/-- info: 'MathFin.jumpDiffusion_call_eq_integral_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_call_eq_integral_bsV

/-- info: 'MathFin.jumpDiffusion_call_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_call_le

/-- info: 'MathFin.jumpDiffusion_call_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_call_lt

/-- info: 'MathFin.jumpDiffusion_impliedVol_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_impliedVol_gt

/-- info: 'MathFin.jumpDiffusion_logContract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_logContract

/-- info: 'MathFin.jumpDiffusion_logContract_le_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_logContract_le_variance

/-- info: 'MathFin.jumpDiffusion_logContract_lt_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_logContract_lt_variance

/-- info: 'MathFin.jumpDiffusion_logContract_sub_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.jumpDiffusion_logContract_sub_variance

/-- info: 'MathFin.kellyFraction_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kellyFraction_eq_zero_iff

/-- info: 'MathFin.kellyFraction_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kellyFraction_lt_one

/-- info: 'MathFin.kellyFraction_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kellyFraction_pos_iff

/-- info: 'MathFin.kellyGrowth_deriv_at_kelly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kellyGrowth_deriv_at_kelly

/-- info: 'MathFin.kellyGrowth_n_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kellyGrowth_n_periods

/-- info: 'MathFin.kellyNumeraire_isRiskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kellyNumeraire_isRiskNeutral

/-- info: 'MathFin.kelly_n_periods_deriv_at_kelly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kelly_n_periods_deriv_at_kelly

/-- info: 'MathFin.kirkSpreadPrice_zero_eq_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kirkSpreadPrice_zero_eq_expected

/-- info: 'MathFin.kmvPD_eq_one_sub_survival_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.kmvPD_eq_one_sub_survival_probability

/-- info: 'MathFin.knockIn_add_knockOut_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.knockIn_add_knockOut_eq_bsV

/-- info: 'MathFin.knockIn_add_knockOut_eq_vanilla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.knockIn_add_knockOut_eq_vanilla

/-- info: 'MathFin.levelPaymentBalance_eq_annuityValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.levelPaymentBalance_eq_annuityValue

/-- info: 'MathFin.lifeAnnuityDue_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lifeAnnuityDue_const

/-- info: 'MathFin.lintegral_lognormalTerminalPDF_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lintegral_lognormalTerminalPDF_eq_one

/-- info: 'MathFin.lintegral_mertonTerminalPDF_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lintegral_mertonTerminalPDF_eq_one

/-- info: 'MathFin.log_forward_div_bsTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.log_forward_div_bsTerminal_eq

/-- info: 'MathFin.lognormalTerminalPDF_change_of_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lognormalTerminalPDF_change_of_variables

/-- info: 'MathFin.lognormalTerminalPDF_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lognormalTerminalPDF_nonneg

/-- info: 'MathFin.lookback_payoff_ge_vanilla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lookback_payoff_ge_vanilla

/-- info: 'MathFin.lp_continuous_martingale_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.lp_continuous_martingale_full

/-- info: 'MathFin.map_mul_exp_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.map_mul_exp_withDensity

/-- info: 'MathFin.map_pair_gaussianFactorVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.map_pair_gaussianFactorVec

/-- info: 'MathFin.marginalVariance_minVarWeightTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.marginalVariance_minVarWeightTwo

/-- info: 'MathFin.margrabe_exchange_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.margrabe_exchange_price

/-- info: 'MathFin.markovPathMeasure_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.markovPathMeasure_cylinder

/-- info: 'MathFin.marshallOlkin_firstToDefault_spread_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.marshallOlkin_firstToDefault_spread_lt

/-- info: 'MathFin.marshallOlkin_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.marshallOlkin_survival

/-- info: 'MathFin.martingalePrice_eq_of_replicates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.martingalePrice_eq_of_replicates

/-- info: 'MathFin.martingaleTransform_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.martingaleTransform_isMartingale

/-- info: 'MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto

/-- info: 'MathFin.martingale_exp_sub_of_indep_increments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.martingale_exp_sub_of_indep_increments

/-- info: 'MathFin.martingale_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.martingale_representation

/-- info: 'MathFin.maxRelativeDrawdown_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.maxRelativeDrawdown_const_mul

/-- info: 'MathFin.maximumDrawdown_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.maximumDrawdown_scale

/-- info: 'MathFin.measureReal_iInter_default_eq_integral_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.measureReal_iInter_default_eq_integral_pow

/-- info: 'MathFin.measureReal_le_eq_copulaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.measureReal_le_eq_copulaOf

/-- info: 'MathFin.measureReal_poisson_max_gpd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.measureReal_poisson_max_gpd

/-- info: 'MathFin.measureReal_valueAtRisk_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.measureReal_valueAtRisk_lt

/-- info: 'MathFin.measure_eq_of_integral_call_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.measure_eq_of_integral_call_eq

/-- info: 'MathFin.measure_eq_of_pricesGainsAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.measure_eq_of_pricesGainsAtZero

/-- info: 'MathFin.medianShortfall_eq_valueAtRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.medianShortfall_eq_valueAtRisk

/-- info: 'MathFin.mertonCallPrice_eq_classic_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonCallPrice_eq_classic_tsum

/-- info: 'MathFin.mertonCallPrice_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonCallPrice_eq_tsum

/-- info: 'MathFin.mertonCallPrice_strictConvexOn_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonCallPrice_strictConvexOn_spot

/-- info: 'MathFin.mertonCallPrice_strictConvexOn_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonCallPrice_strictConvexOn_strike

/-- info: 'MathFin.mertonCallPrice_strictMonoOn_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonCallPrice_strictMonoOn_sigma

/-- info: 'MathFin.mertonCallPrice_strictMonoOn_spot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonCallPrice_strictMonoOn_spot

/-- info: 'MathFin.mertonDelta_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonDelta_lt_one

/-- info: 'MathFin.mertonDelta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonDelta_pos

/-- info: 'MathFin.mertonGamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonGamma_pos

/-- info: 'MathFin.mertonHyp_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonHyp_canonical

/-- info: 'MathFin.mertonJump_logContract_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonJump_logContract_variance

/-- info: 'MathFin.mertonTerminalPDF_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonTerminalPDF_nonneg

/-- info: 'MathFin.mertonVega_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mertonVega_pos

/-- info: 'MathFin.merton_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.merton_call_formula

/-- info: 'MathFin.merton_discounted_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.merton_discounted_terminal

/-- info: 'MathFin.merton_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.merton_put_call_parity

/-- info: 'MathFin.merton_put_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.merton_put_formula

/-- info: 'MathFin.minPortfolioVarTwo_perfect_anticorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.minPortfolioVarTwo_perfect_anticorr

/-- info: 'MathFin.minimum_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.minimum_survival

/-- info: 'MathFin.mmHalfSpread_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mmHalfSpread_const

/-- info: 'MathFin.mmSkew_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mmSkew_linear

/-- info: 'MathFin.modifiedNumerator_eq_macaulayNumerator_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.modifiedNumerator_eq_macaulayNumerator_div

/-- info: 'MathFin.monotone_pow_apply_absorbing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.monotone_pow_apply_absorbing

/-- info: 'MathFin.mul_le_portfolioVarN_equicorrelated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.mul_le_portfolioVarN_equicorrelated

/-- info: 'MathFin.newtonSeq_tendsto_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.newtonSeq_tendsto_root

/-- info: 'MathFin.newtonStep_quadratic_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.newtonStep_quadratic_error

/-- info: 'MathFin.noArbitrage_of_emm_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.noArbitrage_of_emm_multi

/-- info: 'MathFin.normalizedSpread_hasLaw_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.normalizedSpread_hasLaw_std

/-- info: 'MathFin.not_differentiableAt_jumpDiffusionCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.not_differentiableAt_jumpDiffusionCallPrice_strike

/-- info: 'MathFin.not_exists_isCoherentRisk_log_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.not_exists_isCoherentRisk_log_acceptance

/-- info: 'MathFin.not_exists_isCopula_frechetLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.not_exists_isCopula_frechetLower

/-- info: 'MathFin.not_isElicitable_expectedShortfall_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.not_isElicitable_expectedShortfall_integrable

/-- info: 'MathFin.nthMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.nthMoment_terminal

/-- info: 'MathFin.nullSingletonClass_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.nullSingletonClass_jumpDiffusionIncrementLaw

/-- info: 'MathFin.ofReal_exp_le_jumpDiffusionIncrementLaw_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ofReal_exp_le_jumpDiffusionIncrementLaw_singleton

/-- info: 'MathFin.oneFactor_measureReal_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.oneFactor_measureReal_default

/-- info: 'MathFin.oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula

/-- info: 'MathFin.oneFactor_measureReal_inter_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.oneFactor_measureReal_inter_default

/-- info: 'MathFin.oneFactor_measureReal_inter_default_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.oneFactor_measureReal_inter_default_sub_mul

/-- info: 'MathFin.ouSigmaSqFromVar_variance_ouStepResidual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ouSigmaSqFromVar_variance_ouStepResidual

/-- info: 'MathFin.ouStepResidual_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.ouStepResidual_hasLaw

/-- info: 'MathFin.parSwapRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.parSwapRate

/-- info: 'MathFin.payerSwapValue_zcb_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.payerSwapValue_zcb_eq_zero_iff

/-- info: 'MathFin.portfolioVarN_covariance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarN_covariance_nonneg

/-- info: 'MathFin.portfolioVarN_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarN_diag

/-- info: 'MathFin.portfolioVarN_equal_weights_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarN_equal_weights_iid

/-- info: 'MathFin.portfolioVarN_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarN_smul

/-- info: 'MathFin.portfolioVarN_two_asset_compat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarN_two_asset_compat

/-- info: 'MathFin.portfolioVarTwo_at_minVarWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarTwo_at_minVarWeight

/-- info: 'MathFin.portfolioVarTwo_eq_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarTwo_eq_quad

/-- info: 'MathFin.portfolioVarTwo_eq_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarTwo_eq_variance

/-- info: 'MathFin.portfolioVarTwo_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVarTwo_ge_min

/-- info: 'MathFin.portfolioVariance_le_of_lagrangian_FOC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.portfolioVariance_le_of_lagrangian_FOC

/-- info: 'MathFin.posSemidef_equicorrelationMatrix_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.posSemidef_equicorrelationMatrix_iff

/-- info: 'MathFin.powerForward_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.powerForward_price

/-- info: 'MathFin.prefersEU_affine_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.prefersEU_affine_invariant

/-- info: 'MathFin.prefersEU_continuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.prefersEU_continuity

/-- info: 'MathFin.prefersEU_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.prefersEU_independence

/-- info: 'MathFin.premium_ge_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.premium_ge_mean

/-- info: 'MathFin.pricedReturn_le_of_kkt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.pricedReturn_le_of_kkt

/-- info: 'MathFin.prob_healthFactorV1_lt_one_eq_kmvPD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.prob_healthFactorV1_lt_one_eq_kmvPD

/-- info: 'MathFin.processToLpPredictable_coeFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.processToLpPredictable_coeFn

/-- info: 'MathFin.putCall_parity_from_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.putCall_parity_from_no_arbitrage

/-- info: 'MathFin.quantile_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quantile_gaussianReal

/-- info: 'MathFin.quantile_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quantile_le_iff

/-- info: 'MathFin.quantile_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quantile_map

/-- info: 'MathFin.quantoForward_of_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quantoForward_of_gaussian

/-- info: 'MathFin.quanto_correction_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quanto_correction_factor

/-- info: 'MathFin.quoteConstA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quoteConstA

/-- info: 'MathFin.quoteConstB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.quoteConstB

/-- info: 'MathFin.reflectionPrincipleEquiv_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.reflectionPrincipleEquiv_below

/-- info: 'MathFin.reflection_principle_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.reflection_principle_card

/-- info: 'MathFin.relativeDrawdown_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.relativeDrawdown_const_mul

/-- info: 'MathFin.replicating_payoff_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.replicating_payoff_down

/-- info: 'MathFin.replicating_payoff_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.replicating_payoff_up

/-- info: 'MathFin.replicating_portfolio_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.replicating_portfolio_cost

/-- info: 'MathFin.riskParityWeightTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.riskParityWeightTwo

/-- info: 'MathFin.risk_parity_equal_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.risk_parity_equal_contribution

/-- info: 'MathFin.rollSpread_eq_two_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.rollSpread_eq_two_mul_sqrt

/-- info: 'MathFin.sabrATMVol_black_futures_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sabrATMVol_black_futures_price

/-- info: 'MathFin.saccrEAD_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.saccrEAD_mono

/-- info: 'MathFin.schwartzFuturesPrice_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.schwartzFuturesPrice_eq_integral

/-- info: 'MathFin.secondMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.secondMoment_terminal

/-- info: 'MathFin.second_FTAP_single_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.second_FTAP_single_period

/-- info: 'MathFin.sharpeRatio_scaleT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sharpeRatio_scaleT

/-- info: 'MathFin.sharpeRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sharpeRatio_scale_invariant

/-- info: 'MathFin.sharpeSqTwo_critical_iff_crossProduct_FOC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sharpeSqTwo_critical_iff_crossProduct_FOC

/-- info: 'MathFin.sortinoRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sortinoRatio_scale_invariant

/-- info: 'MathFin.sortinoRatio_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sortinoRatio_translation

/-- info: 'MathFin.spearmanRho_fgmCopula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.spearmanRho_fgmCopula

/-- info: 'MathFin.spectralRiskMeasure_sum_esSpectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.spectralRiskMeasure_sum_esSpectrum

/-- info: 'MathFin.spectralRisk_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.spectralRisk_translation

/-- info: 'MathFin.sraffaOwnRate_eq_of_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sraffaOwnRate_eq_of_no_arbitrage

/-- info: 'MathFin.statePricePricing_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.statePricePricing_add

/-- info: 'MathFin.statePricePricing_eq_riskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.statePricePricing_eq_riskNeutral

/-- info: 'MathFin.stateprice_call_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.stateprice_call_butterfly_nonneg

/-- info: 'MathFin.stdDevPrinciple_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.stdDevPrinciple_add_le

/-- info: 'MathFin.stdDevPrinciple_eq_expectedShortfall_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.stdDevPrinciple_eq_expectedShortfall_of_hasLaw_gaussianReal

/-- info: 'MathFin.stdDevPrinciple_eq_valueAtRisk_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.stdDevPrinciple_eq_valueAtRisk_of_hasLaw_gaussianReal

/-- info: 'MathFin.stdDevPrinciple_not_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.stdDevPrinciple_not_monotone

/-- info: 'MathFin.storageForward_at_availability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.storageForward_at_availability

/-- info: 'MathFin.storageForward_from_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.storageForward_from_no_arbitrage

/-- info: 'MathFin.strictConvexOn_integral_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.strictConvexOn_integral_call

/-- info: 'MathFin.strictConvexOn_jumpDiffusionCallPrice_strike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.strictConvexOn_jumpDiffusionCallPrice_strike

/-- info: 'MathFin.strictlyElicits_expectileLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.strictlyElicits_expectileLoss

/-- info: 'MathFin.strictlyElicits_fisslerZiegelExpScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.strictlyElicits_fisslerZiegelExpScore

/-- info: 'MathFin.strictlyElicits_pinballLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.strictlyElicits_pinballLoss

/-- info: 'MathFin.studentTMeasure_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.studentTMeasure_one

/-- info: 'MathFin.studentTPDFReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.studentTPDFReal_eq

/-- info: 'MathFin.submartingale_optional_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.submartingale_optional_sampling

/-- info: 'MathFin.sum_componentVaR_eq_valueAtRisk_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sum_componentVaR_eq_valueAtRisk_sub

/-- info: 'MathFin.sum_deriv_keyRate_eq_deriv_bondPriceDisc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.sum_deriv_keyRate_eq_deriv_bondPriceDisc

/-- info: 'MathFin.survival_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.survival_at_zero

/-- info: 'MathFin.survival_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.survival_pos

/-- info: 'MathFin.survival_probability_eq_Phi_distanceToDefault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.survival_probability_eq_Phi_distanceToDefault

/-- info: 'MathFin.survival_strictAnti_of_pos_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.survival_strictAnti_of_pos_hazard

/-- info: 'MathFin.survive_eq_exp_neg_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.survive_eq_exp_neg_integral

/-- info: 'MathFin.swaption_payer_receiver_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.swaption_payer_receiver_parity

/-- info: 'MathFin.tendsto_bisectMid_valueAtRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_bisectMid_valueAtRisk

/-- info: 'MathFin.tendsto_bsV_sigma_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_bsV_sigma_atTop

/-- info: 'MathFin.tendsto_call_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_call_spread

/-- info: 'MathFin.tendsto_call_spread_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_call_spread_left

/-- info: 'MathFin.tendsto_claytonCopulaFun_diag_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_claytonCopulaFun_diag_div

/-- info: 'MathFin.tendsto_cleanPrice_coupon_date' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_cleanPrice_coupon_date

/-- info: 'MathFin.tendsto_dirtyPrice_coupon_date' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_dirtyPrice_coupon_date

/-- info: 'MathFin.tendsto_expectedShortfall_div_valueAtRisk_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_expectedShortfall_div_valueAtRisk_expMeasure

/-- info: 'MathFin.tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure

/-- info: 'MathFin.tendsto_integral_tranchePayoff_oneFactorLossFraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_integral_tranchePayoff_oneFactorLossFraction

/-- info: 'MathFin.tendsto_oneFactorLossFraction_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_oneFactorLossFraction_ae

/-- info: 'MathFin.tendsto_pow_iff_tendsto_nat_mul_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_pow_iff_tendsto_nat_mul_tail

/-- info: 'MathFin.tendsto_quantile_of_tendsto_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_quantile_of_tendsto_ae

/-- info: 'MathFin.tendsto_realizedVariance_gbm_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_realizedVariance_gbm_L2

/-- info: 'MathFin.tendsto_sabrImpliedVol_atm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_sabrImpliedVol_atm

/-- info: 'MathFin.tendsto_stulzCallMax_zero_strike_betterOfTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_stulzCallMax_zero_strike_betterOfTwo

/-- info: 'MathFin.tendsto_valueAtRisk_oneFactorLossFraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_valueAtRisk_oneFactorLossFraction

/-- info: 'MathFin.tendsto_vasicekYield_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_vasicekYield_atTop

/-- info: 'MathFin.tendsto_vasicekYield_nhdsGT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.tendsto_vasicekYield_nhdsGT_zero

/-- info: 'MathFin.thresholdMatrix_gaussianThresholds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.thresholdMatrix_gaussianThresholds

/-- info: 'MathFin.thresholdMatrix_mem_rowStochastic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.thresholdMatrix_mem_rowStochastic

/-- info: 'MathFin.trackingErrorSq_ge_diff_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.trackingErrorSq_ge_diff_sq

/-- info: 'MathFin.trackingErrorSq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.trackingErrorSq_self

/-- info: 'MathFin.treynorRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.treynorRatio_scale_invariant

/-- info: 'MathFin.triangleNoArb_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.triangleNoArb_iff

/-- info: 'MathFin.triangleNoArb_solve_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.triangleNoArb_solve_third

/-- info: 'MathFin.upCapture_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.upCapture_smul

/-- info: 'MathFin.valueAtRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk

/-- info: 'MathFin.valueAtRisk_add_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_add_affine

/-- info: 'MathFin.valueAtRisk_add_gt_of_paretoHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_add_gt_of_paretoHalf

/-- info: 'MathFin.valueAtRisk_add_le_iff_of_hasGaussianLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_add_le_iff_of_hasGaussianLaw

/-- info: 'MathFin.valueAtRisk_add_of_comonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_add_of_comonotone

/-- info: 'MathFin.valueAtRisk_gbm_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_gbm_loss

/-- info: 'MathFin.valueAtRisk_le_expectedShortfall_of_hasLaw_studentTMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_le_expectedShortfall_of_hasLaw_studentTMeasure

/-- info: 'MathFin.valueAtRisk_of_hasLaw_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_of_hasLaw_gaussianReal

/-- info: 'MathFin.valueAtRisk_of_hasLaw_studentTMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_of_hasLaw_studentTMeasure

/-- info: 'MathFin.valueAtRisk_portfolio_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_portfolio_add_le

/-- info: 'MathFin.valueAtRisk_portfolio_gaussian_eq_portfolioVaRN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_portfolio_gaussian_eq_portfolioVaRN

/-- info: 'MathFin.valueAtRisk_portfolio_gaussian_uncorrelated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_portfolio_gaussian_uncorrelated

/-- info: 'MathFin.valueAtRisk_sum_bernoulli_superadditive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueAtRisk_sum_bernoulli_superadditive_iff

/-- info: 'MathFin.valueFunction_satisfies_approxHJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.valueFunction_satisfies_approxHJ

/-- info: 'MathFin.varianceSwap_log_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.varianceSwap_log_contribution

/-- info: 'MathFin.varianceSwap_log_eq_QV_limit_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.varianceSwap_log_eq_QV_limit_value

/-- info: 'MathFin.variance_gaussianPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.variance_gaussianPair

/-- info: 'MathFin.variance_id_jumpDiffusionIncrementLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.variance_id_jumpDiffusionIncrementLaw

/-- info: 'MathFin.variance_le_of_lagrangian_FOC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.variance_le_of_lagrangian_FOC

/-- info: 'MathFin.variance_singleIndex_portfolio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.variance_singleIndex_portfolio

/-- info: 'MathFin.variance_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.variance_terminal

/-- info: 'MathFin.vasicekBondPrice_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekBondPrice_affine

/-- info: 'MathFin.vasicekBondPrice_girsanov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekBondPrice_girsanov

/-- info: 'MathFin.vasicekBondPrice_solves_pde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekBondPrice_solves_pde

/-- info: 'MathFin.vasicekDeterministic_at_halfLife' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekDeterministic_at_halfLife

/-- info: 'MathFin.vasicekDeterministic_solves_ODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekDeterministic_solves_ODE

/-- info: 'MathFin.vasicekShortRate_hasLaw_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekShortRate_hasLaw_gaussian

/-- info: 'MathFin.vasicekShortRate_hasLaw_girsanov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekShortRate_hasLaw_girsanov

/-- info: 'MathFin.vasicekYield_eq_nssSlope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.vasicekYield_eq_nssSlope

/-- info: 'MathFin.worstCase_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.worstCase_isLUB

/-- info: 'MathFin.zcb_at_maturity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.zcb_at_maturity

/-- info: 'MathFin.zcb_convexity_eq_time_to_maturity_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.zcb_convexity_eq_time_to_maturity_sq

/-- info: 'MathFin.zcb_duration_eq_time_to_maturity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.zcb_duration_eq_time_to_maturity

/-- info: 'MathFin.zcb_yield_eq_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.zcb_yield_eq_rate

/-- info: 'MeasureTheory.maximal_ineq_Lp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.maximal_ineq_Lp

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.condExp_call_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.condExp_call_eq_bsV

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.condExp_put_eq_bsPut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.condExp_put_eq_bsPut

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.jumpDiffusionProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.jumpDiffusionProcess

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.logContract_realizedVariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.logContract_realizedVariance

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.martingale_discounted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.martingale_discounted_iff

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.squareSubTime_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.squareSubTime_isMartingale

/-- info: 'ProbabilityTheory.IsFilteredPreBrownian.waldExponential_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsFilteredPreBrownian.waldExponential_isMartingale

/-! ## Upstream constants cited by `library_wrapper` entries

A `library_wrapper` entry re-exports a Mathlib or BrownianMotion theorem, and it
counts as delivered. BrownianMotion at the current pin has `sorry`s of its own,
so these are pinned here rather than left to upstream. -/

/-- info: 'ConvexOn.map_condExp_le_of_finiteDimensional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConvexOn.map_condExp_le_of_finiteDimensional

/-- info: 'Eq.symm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Eq.symm

/-- info: 'LT.lt.ne'' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LT.lt.ne'

/-- info: 'MeasureTheory.Integrable.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.Integrable.smul

/-- info: 'MeasureTheory.IsProbabilityMeasure.measure_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.IsProbabilityMeasure.measure_univ

/-- info: 'MeasureTheory.Martingale.stoppedProcess_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.Martingale.stoppedProcess_indicator

/-- info: 'MeasureTheory.Measure.trim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.Measure.trim

/-- info: 'MeasureTheory.MeasurePreserving.map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.MeasurePreserving.map_eq

/-- info: 'MeasureTheory.SigmaFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.SigmaFinite

/-- info: 'MeasureTheory.Submartingale.ae_tendsto_limitProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.Submartingale.ae_tendsto_limitProcess

/-- info: 'MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part

/-- info: 'MeasureTheory.condExp_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condExp_add

/-- info: 'MeasureTheory.condExp_condExp_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condExp_condExp_of_le

/-- info: 'MeasureTheory.condExp_indep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condExp_indep_eq

/-- info: 'MeasureTheory.condExp_mul_of_stronglyMeasurable_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condExp_mul_of_stronglyMeasurable_left

/-- info: 'MeasureTheory.condExp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condExp_smul

/-- info: 'MeasureTheory.maximal_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.maximal_ineq

/-- info: 'MeasureTheory.measure_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measure_empty

/-- info: 'Pi.add_apply' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Pi.add_apply

/-- info: 'ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance

/-- info: 'ProbabilityTheory.IsPreBrownianReal.isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsPreBrownianReal.isMartingale

/-- info: 'ProbabilityTheory.IsPreBrownianReal.memHolder_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.IsPreBrownianReal.memHolder_mk

/-- info: 'ProbabilityTheory.gaussianReal_add_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.gaussianReal_add_const

/-- info: 'ProbabilityTheory.gaussianReal_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.gaussianReal_const_mul

/-- info: 'ProbabilityTheory.maximal_ineq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.maximal_ineq_nonneg

/-- info: 'ProbabilityTheory.measurePreserving_eval_multivariateGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measurePreserving_eval_multivariateGaussian

/-- info: 'Real.log_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Real.log_div

/-- info: 'inferInstance' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms inferInstance

/-- info: 'min_eq_left' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms min_eq_left

end MathFin.AxiomAuditGen
