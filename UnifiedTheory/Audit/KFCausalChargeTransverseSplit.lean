/- Reorder the actual mixed coordinates into five transverse coordinates
and one untouched clock coordinate. The permutation is an explicit volume-
preserving isometry, so its L2 pullback introduces no normalization factor. -/
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction
import UnifiedTheory.Audit.KFCausalPartialFourierTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalChargeTransverseSplit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)

def repack (x : Joint 2 4) : Joint 5 1 := WithLp.toLp 2 fun
  | .inl i => ![x (.inl 0),x (.inl 1),x (.inr 1),x (.inr 2),x (.inr 3)] i
  | .inr _ => x (.inr 0)

def unpack (x : Joint 5 1) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl i => ![x (.inl 0),x (.inl 1)] i
  | .inr i => ![x (.inr 0),x (.inl 2),x (.inl 3),x (.inl 4)] i

theorem unpack_repack (x : Joint 2 4) : unpack (repack x) = x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [repack,unpack]

theorem repack_unpack (x : Joint 5 1) : repack (unpack x) = x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [repack,unpack]

def repackEquiv : Joint 2 4 ≃ₗ[ℝ] Joint 5 1 where
  toFun := repack
  invFun := unpack
  left_inv := unpack_repack
  right_inv := repack_unpack
  map_add' x y := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [repack]
  map_smul' c x := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [repack]

theorem repack_inner (x y : Joint 2 4) : inner ℝ (repackEquiv x) (repackEquiv y) = inner ℝ x y := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type,Fin.sum_univ_succ]
  simp [repackEquiv,repack,RCLike.inner_apply]
  ring

def repackIsometry : Joint 2 4 ≃ₗᵢ[ℝ] Joint 5 1 where
  toLinearEquiv := repackEquiv
  norm_map' := (repackEquiv.toLinearMap.isometryOfInner repack_inner).norm_map

theorem repack_clock (x : Joint 2 4) : repackIsometry x (.inr 0) = x (.inr 0) := rfl

theorem repack_preserves : MeasurePreserving repackIsometry := repackIsometry.measurePreserving

def repackPullback : JointHilbert 5 1 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  unitaryPullback repackIsometry.toMeasurableEquiv repack_preserves

theorem repackPullback_coe (f : JointHilbert 5 1) :
    repackPullback f =ᵐ[volume] f ∘ repackIsometry :=
  unitaryPullback_coe _ _ _

def transverseCoordinates : JointHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 5 1 :=
  repackPullback.symm.trans (coordinates 5 1).symm

theorem transverseCoordinates_inverse (f : JointHilbert 2 4) :
    repackPullback (coordinates 5 1 (transverseCoordinates f)) = f := by
  simp only [transverseCoordinates,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply]

def dualMixed : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 5 1 :=
  transverseCoordinates.trans ((leftFourier 5 1).trans (coordinates 5 1))

def dualPhysical : KFCausalConfigurationTestSpace.Hilbert ≃ₗᵢ[ℂ] JointHilbert 5 1 :=
  chargeCoordinates.trans dualMixed

#print axioms unpack_repack
#print axioms repack_unpack
#print axioms repack_inner
#print axioms repack_clock
#print axioms repack_preserves
#print axioms repackPullback_coe
#print axioms transverseCoordinates_inverse

end
end UnifiedTheory.Audit.KFCausalChargeTransverseSplit
