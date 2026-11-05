/- Axiom checks for the twisted small-volume groundwork. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection
import UnifiedTheory.Clay.YangMills.Twisted.TwistedRectangle
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat
import UnifiedTheory.Clay.YangMills.Twisted.RateFilter
import UnifiedTheory.Clay.YangMills.Twisted.TwistedActionJet
import UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum
import UnifiedTheory.Clay.YangMills.Twisted.TwistedStability
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau
import UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw
import UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice
import UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat
import UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianCompare
import UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCollatz
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay
import UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaDomain
import UnifiedTheory.Clay.YangMills.Twisted.TwistedVMFLyapunov

#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection.reflection_positive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection.temporalFlux_eq_one
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection.not_invariant_of_temporalFlux
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection.spatialTwist_invariant
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedRectangle.winding
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat.central_of_anticommuting
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat.wind_classification
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat.wind_classification_of_action_zero
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat.action_flatConfiguration
#print axioms UnifiedTheory.Clay.YangMills.Twisted.RateFilter.energyBound_tendsto_zero
#print axioms UnifiedTheory.Clay.YangMills.Twisted.RateFilter.volume_deficit_filtered

/- Second batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.CommutingShifts.weitzenbock
#print axioms UnifiedTheory.Clay.YangMills.Twisted.CommutingShifts.D_lower_bound
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessian.hessian_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessian.no_zero_modes
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessian.ad_flatLink
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedActionJet.second_derivative
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer.twistedKernel_eq
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer.transfer_positive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer.transfer_flipOp
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer.physical_energy
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum.neutral_vacuum
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedStability.near_central
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedStability.holonomy_stability
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedStability.action_stability

/- Third batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField.product_expansion
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField.action_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField.action_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField.action_coercive_coulomb
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization.actionOne_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization.partition_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization.action_tail
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization.localization
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization.linkCount_eq

/- Fourth batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau.defect_act
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau.div_imPart
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau.exp_logQ
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau.landau_quadratic
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau.actionL_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau.orbit_quadratic

/- Fifth batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedAxial.exists_axial
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFrame.exact_frame
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFrame.exists_frame_pair
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFrame.align
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams.line
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams.rel12
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams.reduce0
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat.actionL_shift
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat.axial_near_flat
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat.near_flat
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat.measure_near_flat

/- Sixth batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianCompare.action_two_sided
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianCompare.gaussian_comparison
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler.eigen_ground
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler.eigen_excited
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler.dispersion
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler.window
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedCollatz.collatz_wielandt

/- Seventh batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge.treeMap_preserving
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge.gauge_tree
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge.sliceMap_preserving
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge.integral_invariant
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge.form_reduction
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge.inner_reduction

/- Eighth batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift.holo_gauge
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift.holo_lipschitz
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift.holo_flip
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift.holo_sq_of_small
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNormLower.potential_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNormLower.temporal_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedNormLower.norm_lower'
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector.top_flip
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector.rayleigh
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector.flux_near_degenerate
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector.flux_near_degenerate_explicit
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector.flux_gap_vanishes

/- Ninth batch. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap.rankOne_compact
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap.gap_of_simple
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap.finite_gap
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare.ground_state_identity
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare.eigenvalue_of_poincare
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare.invariant_bound
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare.gap_of_poincare
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare.exp_of_poincare
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField.second_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField.second_derivative_field
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField.hessian_field_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField.hessian_field_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField.near_flat_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.weitzenbock_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.block_poincare
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.block_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant.cov_comm
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant.hessian_cov_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant.cov_block_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant.cov_block_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant.measure_smallDefects
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.block_coercive_of_cross
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet.card_badLinks_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet.card_badPlaq_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet.cross_local
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet.hessian_avoids
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet.block_coercive_avoids
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet.measure_bad_density
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.proj_close
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.blockLink_close
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.blockLink_flat
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.blockLink_act
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.line_loop
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.blocked_defect
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.D_savg_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.D_savg_move
#print axioms UnifiedTheory.Clay.YangMills.Twisted.BlockShifts.smooth_grad
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap.cov_split
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw.card_notGood_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw.measure_blocked_links
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw.close_of_not_notGood
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.ibp_first
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.ibp_second
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.flow_pres
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.flow_flow
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.action_jet
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.ibp_reference
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.law_integral
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.gibbs_ibp
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.force_bound
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.ibp_mixed
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.term_jet
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.Ap_Bp_measurable
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.plaquette_ibp
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP.own_le_of_cross
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.reflected_nonneg
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.Ap_reflect
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.flow_reflect
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.Tup_reflected_nonneg
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.slice_le_force
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.force_sq
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.force_sq_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.slice_bound
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.opposite_nonneg
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.Tup_single
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice.single_link_bound

/- Slow observable: the lower half of the neutral window. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.neutral_embed
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.slow_lower
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.window_of_two_sided
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.neutral_pow
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.orth_pow
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.inner_pow_pow
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.slow_lower_lag
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable.slow_lower_corr

/- One RG step as a Schur complement: the linear algebra. -/
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep.complete_square
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep.schur_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep.schur_attained
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep.schur_mono
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep.Q_combo
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep.schur_concave
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.norm_pow_sq
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.norm_pow_sq_le
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.norm_pow_two_pow
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.contraction_of_decay
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.contraction_of_corr
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.fast_upper_corr
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay.window_of_correlators
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.gaussian_marginal
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.gaussian_integrable
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.gaussian_Z_pos
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.isUnit_det_of_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.schur_coercive
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.Ueff_eq
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.Ueff_second_diff
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep.gaussian_rg_step
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.bm_compact
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.vol_eq_iSup_sub
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.sup_helper
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.sum_subset_level
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.level_ineq
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.pl_linear
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.ennreal_amgm
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.lintegral_scale
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.prekopa_leindler
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.prekopa_marginal
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.prekopa_convex
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa.prekopa_rg_step
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.pl_ennreal
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.prekopaSpace_real
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.PrekopaSpace.prod
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.PrekopaSpace.of_equiv
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.prekopaSpace_pi
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.convex_neg_log
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.logConcave_exp_neg
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.prekopa_rg_step_multi
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.prekopa_pi
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti.prekopa_rg_step_pi
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb.quad_sym
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb.quad_convex
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb.brascamp_lieb_linear
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaDomain.logConcave_indicator
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaDomain.convex_neg_log_on
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaDomain.prekopa_rg_step_domain
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedVMFLyapunov.g_le_neg_three
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedVMFLyapunov.drift
#print axioms UnifiedTheory.Clay.YangMills.Twisted.TwistedVMFLyapunov.lemmaV_constant
