/- Exact affine transport of the entire six-plaquette cell family. Coarse
translations lift by two fine sites, and every coordinate permutation is
allowed because all three internal plaquette orientations are retained. -/
import UnifiedTheory.Clay.YangMills.WilsonCubeCells
import UnifiedTheory.Clay.YangMills.BlockLabelSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCubeTransport
noncomputable section
open WilsonTimeSlab SpatialPlaquetteCutGeometry WilsonSpatialRotations WilsonPlaquetteFrames
open DyadicCellCoordinates WilsonCubeCells WilsonProfileTransport

variable (m : ℕ) [NeZero m]

def liftVertex (s : SpatialVertex m) : SpatialVertex (2 * m) := fun j => lift m (s j)

theorem offsets_affine (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex m)
    (x : SpatialVertex (2 * m)) (j : Fin 3) :
    offsets m (vertexEquiv (2 * m) σ x + liftVertex m s) (σ j) = offsets m x j := by
  change bit m (x (σ.symm (σ j)) + lift m (s (σ j))) = bit m (x j)
  rw [Equiv.symm_apply_apply, bit_add_lift]

theorem coarse_affine (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex m) (p : Plaquette m) :
    coarseVertex m ((affine m σ (liftVertex m s)).plaquettes p).1 =
      vertexEquiv m σ (coarseVertex m p.1) + s := by
  rw [affine_plaquette]
  funext j
  exact coarse_add_lift m (p.1 (σ.symm j)) (s j)

theorem internal_affine (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex m) (p : Plaquette m) :
    Internal m ((affine m σ (liftVertex m s)).plaquettes p) ↔ Internal m p := by
  rw [affine_plaquette]
  change (offsets m (vertexEquiv (2 * m) σ p.1 + liftVertex m s) (planeMap σ p.2).val.1 = 0 ∧
    offsets m (vertexEquiv (2 * m) σ p.1 + liftVertex m s) (planeMap σ p.2).val.2 = 0) ↔ _
  unfold planeMap
  split_ifs
  · simp only [offsets_affine]
    rfl
  · simp only [offsets_affine]
    exact and_comm

variable (n : ℕ) [NeZero n]

omit m [NeZero m] in
theorem deleted_pull (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n))
    (f : SpatialVertex (2 * n) → Bool) :
    deleted (2 * n) (BlockLabelSymmetry.pull n σ s f) =
      pushSet (2 * n) (inverse (2 * n) (affine (2 * n) σ (liftVertex (2 * n) s)))
        (deleted (2 * n) f) := by
  classical
  ext p
  rw [pushSet_mem, deleted_mem, deleted_mem]
  change (Internal (2 * n) p ∧ BlockLabelSymmetry.pull n σ s f (coarseVertex (2 * n) p.1) = true) ↔
    (Internal (2 * n) ((affine (2 * n) σ (liftVertex (2 * n) s)).plaquettes p) ∧
      f (coarseVertex (2 * n) ((affine (2 * n) σ (liftVertex (2 * n) s)).plaquettes p).1) = true)
  rw [internal_affine, coarse_affine]
  rfl

end
end UnifiedTheory.Clay.YangMills.WilsonCubeTransport
