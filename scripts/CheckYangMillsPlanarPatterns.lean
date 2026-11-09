import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail
import UnifiedTheory.Clay.YangMills.WilsonPatchCover
import UnifiedTheory.Clay.YangMills.WilsonPatchCountTail
import UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry
import UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover
import UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts
import UnifiedTheory.Clay.YangMills.WilsonPatchWitness

#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.Aligned
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.omitted
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.patchDefect
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.patchDefect_nonneg
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.patchDefect_continuous
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.omitted_nonneg
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.reflection_mem
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.omitted_reflection
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.omitted_half
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.action_restore
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.weight_restore
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights.weight_restore_product
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.halfHistoryBorel
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.path
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.path_continuous
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.density_restore
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.density_assemble_restore
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.cutKernel
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.cutKernel_continuous
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.augmented_value
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.cut_form
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.augmented_form
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.patch_floor
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.patch_removal
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory.partition_floor
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm.patch_partition_floor
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm.mass_norm_lower
#print axioms UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm.polynomial_norm
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.boundary_restore
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.raw_factor
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.raw_high
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.input_bound
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.mass_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.patchDefect_lower
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.rate_cardinality
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.intersection_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay.intersection_loss
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.cutoff
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.cutoff_range
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.cutoff_supported
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.cutoff_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.cutoff_output
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.source_cutoff
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.hard
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.hard_measurable
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail.source_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.cover
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.bad
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.bad_measurable
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.cover_range
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.cover_supported
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.cover_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.joint_output
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.weighted_union
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.union_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCover.same_size_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.large
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.event
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.event_eq_union
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.event_measurable
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.binomial_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.binomial_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.binomial_entropy
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.density_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.density_loss
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchCountTail.weak_coupling_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.law_integral
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.event_integral
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.patch_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.count_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.count_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.intersection_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.cutoff_output
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.affine
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry.affine_defect
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.seed
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.cover
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.bad
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.bad_measurable
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.seed_range
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.cover_range
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.cover_supported
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.cover_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.joint_output
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.weighted_union
#print axioms UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover.union_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.Index
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.frame
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.marked
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.index_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.marked_aligned
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.marked_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.allBad
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.mem_allBad
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.all_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.all_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.density_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.weak_coupling_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.density_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.volume_price
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.entropy_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts.entropy_loss
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.defect_large
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.defect_flat
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.factor
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump_large
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump_flat
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump_supported
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump_physical
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump_mass_positive
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.bump_coercivity
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.large_field_event
#print axioms UnifiedTheory.Clay.YangMills.WilsonPatchWitness.flat_not_event
