/- A constructed strongly continuous unitary group for the optional clock-floor
longitudinal transport, by conjugating clock translation through the
actual six-coordinate unitary map. This is not the full Hamiltonian
propagator, and no finite-to-infinite identification is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
import UnifiedTheory.Audit.KFCausalConfigurationTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalConfigurationTranslation

def transport (ε : ℝ) (hε : 0 < ε) (t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  (coordinates ε hε).symm.trans ((translation t).trans (coordinates ε hε))

theorem transport_apply (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    transport ε hε t f = coordinates ε hε (translation t ((coordinates ε hε).symm f)) := rfl

theorem transport_initial (ε : ℝ) (hε : 0 < ε) (f : Hilbert) : transport ε hε 0 f = f := by
  rw [transport_apply,translation_initial,LinearIsometryEquiv.apply_symm_apply]

theorem transport_compose (ε : ℝ) (hε : 0 < ε) (t u : ℝ) (f : Hilbert) :
    transport ε hε u (transport ε hε t f) = transport ε hε (t+u) f := by
  simp only [transport_apply,LinearIsometryEquiv.symm_apply_apply,translation_compose]

theorem transport_reverse (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    transport ε hε (-t) (transport ε hε t f) = f := by
  rw [transport_compose,add_neg_cancel,transport_initial]

theorem transport_unitary (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    (transport ε hε t : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (Unitary.linearIsometryEquiv.symm (transport ε hε t)).property

theorem transport_inner (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f g : Hilbert) :
    inner ℂ (transport ε hε t f) (transport ε hε t g) = inner ℂ f g :=
  (transport ε hε t).inner_map_map f g

theorem transport_strong_continuous (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    Continuous (fun t : ℝ => transport ε hε t f) :=
  (coordinates ε hε).continuous.comp (translation_strong_continuous ((coordinates ε hε).symm f))

def testTransport (ε : ℝ) (hε : 0 < ε) (t : ℝ) : Test ≃ₗ[ℂ] Test :=
  (testPullback ε hε).symm.trans ((translationTests t).trans (testPullback ε hε))

theorem transport_embedding (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) :
    transport ε hε t (embedding f) = embedding (testTransport ε hε t f) := by
  rw [transport_apply,coordinates_symm_embedding,translation_embedding,coordinates_embedding]
  rfl

theorem inverse_shift_coordinates (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    (coordinateHomeomorph ε hε).symm (clockShift t (coordinateHomeomorph ε hε x)) =
      coupledFlow ε hε t x := by
  apply (coordinateHomeomorph ε hε).injective
  rw [Homeomorph.apply_symm_apply,clockShift_apply]
  exact (straightening_flow ε hε t x).symm

theorem testTransport_apply (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) (x : Configuration) :
    testTransport ε hε t f x =
      weight ε x*(weight ε (coupledFlow ε hε t x))⁻¹*f (coupledFlow ε hε t x) := by
  change testPullback ε hε (translationTests t ((testPullback ε hε).symm f)) x = _
  simp only [testPullback,weightedEquiv_apply,translationTests_apply,weightedEquiv_symm_apply,
    inverse_shift_coordinates,mul_assoc]

theorem transport_test_representative (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) :
    (transport ε hε t (embedding f) : Configuration → ℂ) =ᵐ[volume]
      fun x => weight ε x*(weight ε (coupledFlow ε hε t x))⁻¹*f (coupledFlow ε hε t x) := by
  rw [transport_embedding]
  filter_upwards [embedding_coe (testTransport ε hε t f)] with x hx
  rw [hx,testTransport_apply]

#print axioms transport
#print axioms transport_initial
#print axioms transport_compose
#print axioms transport_reverse
#print axioms transport_unitary
#print axioms transport_inner
#print axioms transport_strong_continuous
#print axioms transport_embedding
#print axioms inverse_shift_coordinates
#print axioms testTransport_apply
#print axioms transport_test_representative

end
end UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
