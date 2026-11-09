/- Exact matching of six-plaquette cell deletion and coarse label reflection.
The fine reflection seams lie between the cells and retain their couplings. -/
import UnifiedTheory.Clay.YangMills.WilsonCubeCells
import UnifiedTheory.Clay.YangMills.BlockReflectionVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCubeReflection
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialPlaquetteCutGeometry
open SpatialWilsonPlaquetteKernels DyadicCellCoordinates WilsonCubeCells

variable (m : ℕ) [NeZero m]

theorem internal_reflect (p : Plaquette m) : Internal m (reflectPlaquette m p) ↔ Internal m p := by
  have hj : p.2.val.2 ≠ 0 := by
    intro h
    have hp := p.2.property
    rw [h] at hp
    exact (not_lt_of_ge (Fin.zero_le _)) hp
  by_cases hi : p.2.val.1 = 0
  · have he : (-1 : ZMod (2 * m)) + (-1 + -p.1 0) = -(p.1 0 + 1 + 1) := by ring
    have hb : bit m (-1 + (-1 + -p.1 0)) = bit m (p.1 0) := by
      rw [he]
      exact bit_reflect_succ m (p.1 0)
    simp [Internal, offsets, reflectPlaquette, reflectLink, reflectVertex, spatialStep, hi, hj, hb]
  · simp [Internal, offsets, reflectPlaquette, reflectLink, reflectVertex, hi, hj]

theorem coarse_reflect (p : Plaquette m) (hp : Internal m p) :
    coarseVertex m (reflectPlaquette m p).1 = reflectVertex m (coarseVertex m p.1) := by
  funext j
  by_cases hi : p.2.val.1 = 0
  · have hb : bit m (p.1 0) = 0 := by simpa only [Internal, offsets, hi] using hp.1
    by_cases hj : j = 0
    · subst j
      simpa [coarseVertex, reflectPlaquette, reflectLink, reflectVertex, spatialStep, hi] using
        coarse_reflect_succ_even m (p.1 0) hb
    · simp [coarseVertex, reflectPlaquette, reflectLink, reflectVertex, spatialStep, hi, hj]
  · by_cases hj : j = 0
    · subst j
      simpa [coarseVertex, reflectPlaquette, reflectLink, reflectVertex, hi] using
        DyadicCellCoordinates.coarse_reflect m (p.1 0)
    · simp [coarseVertex, reflectPlaquette, reflectLink, reflectVertex, hi, hj]

variable (n : ℕ) [NeZero n]

omit m [NeZero m] in
theorem half_side (x : SpatialVertex (2 * (2 * n))) :
    VertexPositive (2 * n) x ↔ VertexPositive n (coarseVertex (2 * n) x) := by
  unfold VertexPositive coarseVertex
  rw [coarse_val]
  omega

omit m [NeZero m] in
theorem internal_not_crossing (p : Plaquette (2 * n)) (hp : Internal (2 * n) p) :
    ¬ Crossing (2 * n) p := by
  intro hc
  have hb : bit (2 * n) (p.1 0) = 0 := by simpa only [Internal, offsets, hc.1] using hp.1
  have hv := congrArg (fun x : SpatialVertex (2 * (2 * n)) => (x 0).val) hc.2
  change (-(p.1 0 + 1)).val = (p.1 0 + 1).val at hv
  rw [PeriodicHalfGeometry.val_neg_add_one, succ_even_val (2 * n) (p.1 0) hb] at hv
  have he : (p.1 0).val % 2 = 0 := congrArg Fin.val hb
  have ht := (p.1 0).val_lt
  omega

omit m [NeZero m] in
theorem positive_deleted (f : SpatialVertex (2 * n) → Bool) :
    WilsonDeletionReflection.positiveSet (2 * n) (deleted (2 * n) f) =
      deleted (2 * n) (BlockReflectionVariation.positiveCopy n f) := by
  classical
  ext p
  rw [WilsonDeletionReflection.positiveSet_mem, deleted_mem, deleted_mem]
  by_cases hp : Internal (2 * n) p
  · have hc := internal_not_crossing n p hp
    by_cases hx : VertexPositive (2 * n) p.1
    · have hs := (half_side n p.1).mp hx
      simp only [WilsonDeletionReflection.positiveIndex, if_neg hc, if_pos hx,
        BlockReflectionVariation.positiveCopy, if_pos hs]
    · have hs : ¬ VertexPositive n (coarseVertex (2 * n) p.1) := mt (half_side n p.1).mpr hx
      simp only [WilsonDeletionReflection.positiveIndex, if_neg hc, if_neg hx,
        internal_reflect, coarse_reflect (2 * n) p hp,
        BlockReflectionVariation.positiveCopy, if_neg hs]
  · have hr : ¬ Internal (2 * n) (reflectPlaquette (2 * n) p) := mt (internal_reflect _ p).mp hp
    unfold WilsonDeletionReflection.positiveIndex
    split_ifs <;> simp only [hp, hr, false_and]

omit m [NeZero m] in
theorem negative_deleted (f : SpatialVertex (2 * n) → Bool) :
    WilsonDeletionReflection.negativeSet (2 * n) (deleted (2 * n) f) =
      deleted (2 * n) (BlockReflectionVariation.negativeCopy n f) := by
  classical
  ext p
  rw [WilsonDeletionReflection.negativeSet_mem, deleted_mem, deleted_mem]
  by_cases hp : Internal (2 * n) p
  · have hc := internal_not_crossing n p hp
    by_cases hx : VertexPositive (2 * n) p.1
    · have hs := (half_side n p.1).mp hx
      simp only [WilsonDeletionReflection.negativeIndex, if_neg hc, if_pos hx,
        internal_reflect, coarse_reflect (2 * n) p hp,
        BlockReflectionVariation.negativeCopy, if_pos hs]
    · have hs : ¬ VertexPositive n (coarseVertex (2 * n) p.1) := mt (half_side n p.1).mpr hx
      simp only [WilsonDeletionReflection.negativeIndex, if_neg hc, if_neg hx,
        BlockReflectionVariation.negativeCopy, if_neg hs]
  · have hr : ¬ Internal (2 * n) (reflectPlaquette (2 * n) p) := mt (internal_reflect _ p).mp hp
    unfold WilsonDeletionReflection.negativeIndex
    split_ifs <;> simp only [hp, hr, false_and]

end
end UnifiedTheory.Clay.YangMills.WilsonCubeReflection
