/- Fresh physical-overlap axioms; the runner checks the retained certificate chain. -/
import UnifiedTheory.Clay.YangMills.CompactPairedDensity
import UnifiedTheory.Clay.YangMills.WilsonCenterContrast
import UnifiedTheory.Clay.YangMills.WilsonContrastMoment
import UnifiedTheory.Clay.YangMills.WilsonOverlapContraction
import UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit

#print axioms UnifiedTheory.Clay.YangMills.CompactPairedDensity.weighted_product_sq
#print axioms UnifiedTheory.Clay.YangMills.CompactPairedDensity.contrast_pairing
#print axioms UnifiedTheory.Clay.YangMills.CompactPairedDensity.mixture_even
#print axioms UnifiedTheory.Clay.YangMills.CompactPairedDensity.odd_response
#print axioms UnifiedTheory.Clay.YangMills.CompactPairedDensity.overlap_identity
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.full_kernel_twist
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.full_kernel_cross
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.full_transition_twist
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.full_transition_cross
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_continuous
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.source
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_gauge_left
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_gauge_right
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_odd_left
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_odd_right
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_abs_lt_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_kernel
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.contrast_symmetric
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.twisted_integral
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.odd_integral
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterContrast.even_integral
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment_nonneg
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment_mixture
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment_gauge
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment_even
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.source_square_step
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.source_step
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.odd_square
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.row_bound_iff
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment_le_profile
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.moment_lt_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.overlap_identity
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.harmonicKernel
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.harmonicKernel_pos
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.harmonicKernel_symmetric
#print axioms UnifiedTheory.Clay.YangMills.WilsonContrastMoment.overlap_kernel
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.averaged
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.averaged_full
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.averaged_le_previous
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.exists_maximizer
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.maximizer
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.averaged_le_rate
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate_nonneg
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate_le_previous
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate_lt_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.row_margin
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate_margin_le_row
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate_margin_overlap
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.rate_margin_kernel
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.odd_source_bound
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.odd_contraction
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.partial_contraction
#print axioms UnifiedTheory.Clay.YangMills.WilsonOverlapContraction.odd_iterate
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.axisI
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.axisJ
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.conjugate_axis
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.fixed
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.fixed_flat
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.fixed_twist_gauge
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.contrast_zero
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.moment_zero
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.small_moment_positive
#print axioms UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit.moment_below_base
