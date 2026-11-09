/- The optional clock-floor straightening map is an actual complex-linear
unitary equivalence on physical L2, obtained from the proved dense test
space and exact model-specific norm identity. -/
import UnifiedTheory.Audit.KFCausalClockFloorTestPullback
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

def coordinates (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  extension embedding embedding_dense (testPullback ε hε) (testPullback_physical_norm ε hε)

theorem coordinates_embedding (ε : ℝ) (hε : 0 < ε) (f : Test) :
    coordinates ε hε (embedding f) = embedding (testPullback ε hε f) :=
  extension_embedding _ _ _ _ f

theorem coordinates_symm_embedding (ε : ℝ) (hε : 0 < ε) (f : Test) :
    (coordinates ε hε).symm (embedding f) = embedding ((testPullback ε hε).symm f) := by
  apply (coordinates ε hε).injective
  rw [LinearIsometryEquiv.apply_symm_apply,coordinates_embedding,LinearEquiv.apply_symm_apply]

theorem coordinates_test_representative (ε : ℝ) (hε : 0 < ε) (f : Test) :
    (coordinates ε hε (embedding f) : Configuration → ℂ) =ᵐ[volume]
      fun x => weight ε x*f (KFCausalClockFloorFlow.coordinateHomeomorph ε hε x) := by
  rw [coordinates_embedding]
  exact embedding_coe (testPullback ε hε f)

theorem coordinates_unitary (ε : ℝ) (hε : 0 < ε) :
    (coordinates ε hε : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  extension_unitary _ _ _ _

theorem coordinates_norm (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    ‖coordinates ε hε f‖ = ‖f‖ := (coordinates ε hε).norm_map f

theorem coordinates_inner (ε : ℝ) (hε : 0 < ε) (f g : Hilbert) :
    inner ℂ (coordinates ε hε f) (coordinates ε hε g) = inner ℂ f g :=
  (coordinates ε hε).inner_map_map f g

theorem coordinates_surjective (ε : ℝ) (hε : 0 < ε) : Function.Surjective (coordinates ε hε) :=
  (coordinates ε hε).surjective

#print axioms coordinates
#print axioms coordinates_embedding
#print axioms coordinates_symm_embedding
#print axioms coordinates_test_representative
#print axioms coordinates_unitary
#print axioms coordinates_inner
#print axioms coordinates_surjective

end
end UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
