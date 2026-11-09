import UnifiedTheory.Clay.YangMills.DyadicCellCoordinates
import UnifiedTheory.Clay.YangMills.WilsonCubeCells
import UnifiedTheory.Clay.YangMills.WilsonCubeReflection
import UnifiedTheory.Clay.YangMills.WilsonCubeTransport
import UnifiedTheory.Clay.YangMills.WilsonCubeChessboard
import UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds
import UnifiedTheory.Clay.YangMills.WilsonCubeNormBound
import UnifiedTheory.Clay.YangMills.WilsonCubeCover
import UnifiedTheory.Clay.YangMills.WilsonClusterNorm
import UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay
import UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail
import UnifiedTheory.Clay.YangMills.WilsonClusterCover
import UnifiedTheory.Clay.YangMills.WilsonClusterActivity
import UnifiedTheory.Clay.YangMills.WilsonClusterCountTail

#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.bit
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.join
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse_val
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.join_val
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse_join
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.bit_join
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.join_split
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.equiv
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.lift
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.join_add
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse_add_lift
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.bit_add_lift
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse_reflect
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.bit_reflect_val
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.succ_val
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.bit_succ_val
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.succ_even_val
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse_succ_even
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.bit_reflect_succ
#print axioms UnifiedTheory.Clay.YangMills.DyadicCellCoordinates.coarse_reflect_succ_even
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.Offsets
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.Pattern
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.pattern_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.coarseVertex
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.offsets
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.joinVertex
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.coarse_joinVertex
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.offsets_joinVertex
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.joinVertex_split
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.encode
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.encode_injective
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.embedding
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.Internal
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.encode_internal
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.cellSet
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.cellSet_mem
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.cellSet_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.marked
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.deleted
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.deleted_mem
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.deleted_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.deleted_false
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.deleted_true
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.full_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.label
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.marked_label
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCells.deleted_label
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeReflection.internal_reflect
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeReflection.coarse_reflect
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeReflection.half_side
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeReflection.internal_not_crossing
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeReflection.positive_deleted
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeReflection.negative_deleted
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeTransport.liftVertex
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeTransport.offsets_affine
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeTransport.coarse_affine
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeTransport.internal_affine
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeTransport.deleted_pull
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeChessboard.score
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeChessboard.score_nonneg
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeChessboard.score_affine
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeChessboard.score_schwarz
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeChessboard.binary_bound
#print axioms UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds.boundary_le_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds.kinetic_le_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds.kernel_le_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds.norm_le_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds.raw_full_le_original
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.full_price
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.full_score_le
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.empty_score_le
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.score_le_original
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.deletion_norm
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.cell_norm
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeNormBound.cellSet_norm
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.offsetVertex
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.bit_shift
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.internal_shift
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.offsets_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.matching_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.retained
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.retained_subset
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.retained_sum
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.retained_quarter
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.cells
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.cells_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.cover
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.retained_cover
#print axioms UnifiedTheory.Clay.YangMills.WilsonCubeCover.cover_card
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterNorm.envelope_nonneg
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterNorm.cover_norm
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterNorm.exists_cover
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.rate
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.rate_pos
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.rate_le_one
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.patchDefect_mono
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.covered_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.intersection_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay.intersection_loss
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail.cutoff_output
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail.source_cutoff
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail.source_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCover.joint_output
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCover.weighted_union
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCover.union_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCover.same_size_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.threshold
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.threshold_pos
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.threshold_margin
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.threshold_tendsto
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.rate_threshold
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.exponent_threshold
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.rate_bound
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterActivity.rate_tendsto
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCountTail.binomial_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCountTail.binomial_decay
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCountTail.density_tail
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCountTail.density_loss
#print axioms UnifiedTheory.Clay.YangMills.WilsonClusterCountTail.weak_coupling_tail
