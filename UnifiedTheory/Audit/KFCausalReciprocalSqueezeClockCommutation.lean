/- Exact all-L2 commutation of reciprocal squeeze with both clock transports and
bounded clock multiplication. No infinitesimal commutator is assumed. -/
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeTransport
import UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
import UnifiedTheory.Audit.KFCausalClockFloorLpTransport
import UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalReciprocalSqueezeClockCommutation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (flow)
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeFlow (squeeze squeeze_shear)
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeTransport

variable (ε : ℝ) (hε : 0 < ε)

theorem pure_coordinates (t : ℝ) (f : Hilbert) :
    transport t (KFCausalClockFloorPureClockCoordinates.coordinates ε hε f) =
      KFCausalClockFloorPureClockCoordinates.coordinates ε hε (transport t f) := by
  apply Lp.ext
  filter_upwards [transport_coe t (KFCausalClockFloorPureClockCoordinates.coordinates ε hε f),
    KFCausalClockFloorPureClockLpCoordinates.coordinates_coe ε hε (transport t f),
    (squeezeFlow_quasiMeasurePreserving t).ae (KFCausalClockFloorPureClockLpCoordinates.coordinates_coe ε hε f),
    (KFCausalClockFloorPureClockLpCoordinates.coordinate_quasiMeasurePreserving ε hε).ae
      (transport_coe t f)] with x hs hu hf hg
  simp only [KFCausalClockFloorPureClockLpCoordinates.weightedFunction] at hu hf
  rw [hs,hu,hf,hg]
  change (Real.exp (-t/2):ℂ)*((Real.sqrt (Real.exp x.1+ε):ℂ)*
    f (KFCausalRegularizedLongitudinalChart.chart ε x.1,squeeze (-t) x.2)) =
    (Real.sqrt (Real.exp x.1+ε):ℂ)*((Real.exp (-t/2):ℂ)*
    f (KFCausalRegularizedLongitudinalChart.chart ε x.1,squeeze (-t) x.2))
  ring

theorem coupled_coordinates (t : ℝ) (f : Hilbert) :
    transport t (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε f) =
      KFCausalClockFloorUnitaryCoordinates.coordinates ε hε (transport t f) := by
  apply Lp.ext
  filter_upwards [transport_coe t (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε f),
    KFCausalClockFloorLpCoordinates.coordinates_coe ε hε (transport t f),
    (squeezeFlow_quasiMeasurePreserving t).ae (KFCausalClockFloorLpCoordinates.coordinates_coe ε hε f),
    (KFCausalClockFloorLpCoordinates.coordinate_quasiMeasurePreserving ε hε).ae
      (transport_coe t f)] with x hs hu hf hg
  simp only [KFCausalClockFloorLpCoordinates.weightedFunction] at hu hf
  rw [hs,hu,hf,hg]
  change (Real.exp (-t/2):ℂ)*(KFCausalClockFloorTestPullback.weight ε x*
    f (KFCausalRegularizedLongitudinalChart.chart ε x.1,flow (-x.1) (squeeze (-t) x.2))) =
    KFCausalClockFloorTestPullback.weight ε x*((Real.exp (-t/2):ℂ)*
    f (KFCausalRegularizedLongitudinalChart.chart ε x.1,squeeze (-t) (flow (-x.1) x.2)))
  rw [squeeze_shear]
  ring

theorem pure_inverse_coordinates (t : ℝ) (f : Hilbert) :
    transport t ((KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm f) =
      (KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm (transport t f) := by
  apply (KFCausalClockFloorPureClockCoordinates.coordinates ε hε).injective
  rw [← pure_coordinates,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]

theorem coupled_inverse_coordinates (t : ℝ) (f : Hilbert) :
    transport t ((KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).symm f) =
      (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).symm (transport t f) := by
  apply (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).injective
  rw [← coupled_coordinates,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]

theorem pure_transport (t u : ℝ) (f : Hilbert) :
    transport t (KFCausalClockFloorPureClockTransport.transport ε hε u f) =
      KFCausalClockFloorPureClockTransport.transport ε hε u (transport t f) := by
  simp only [KFCausalClockFloorPureClockTransport.transport_apply,pure_coordinates,
    transport_translation,pure_inverse_coordinates]

theorem coupled_transport (t u : ℝ) (f : Hilbert) :
    transport t (KFCausalClockFloorUnitaryTransport.transport ε hε u f) =
      KFCausalClockFloorUnitaryTransport.transport ε hε u (transport t f) := by
  simp only [KFCausalClockFloorUnitaryTransport.transport_apply,coupled_coordinates,
    transport_translation,coupled_inverse_coordinates]

theorem clock_multiplier (Q : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hq : ∀ f : Hilbert, Q f =ᵐ[volume] fun x => w x.1*f x) (t : ℝ) (f : Hilbert) :
    transport t (Q f) = Q (transport t f) := by
  apply Lp.ext
  filter_upwards [transport_coe t (Q f),hq (transport t f),
    (squeezeFlow_quasiMeasurePreserving t).ae (hq f),transport_coe t f] with x hs hq' hf hg
  rw [hs,hq',hf,hg]
  change (Real.exp (-t/2):ℂ)*(w x.1*f (squeezeFlow t x)) = w x.1*((Real.exp (-t/2):ℂ)*f (squeezeFlow t x))
  ring

theorem defect_commutes (t : ℝ) (f : Hilbert) :
    transport t (KFCausalClockFloorDefectOperator.defectOperator ε hε f) =
      KFCausalClockFloorDefectOperator.defectOperator ε hε (transport t f) :=
  clock_multiplier _ (fun s => (KFCausalClockFloorCanonicalDefect.defect ε s:ℂ))
    (KFCausalClockFloorDefectOperator.defectOperator_coe ε hε) t f

theorem inverse_half_commutes (t : ℝ) (f : Hilbert) :
    transport t (KFCausalClockFloorBoundedInverse.inverseL ε hε f) =
      KFCausalClockFloorBoundedInverse.inverseL ε hε (transport t f) :=
  clock_multiplier _ (fun s => (KFCausalClockFloorInverseHalfTransportScalar.value ε s:ℂ))
    (KFCausalClockFloorInverseHalfTransportOperator.inverseL_coe ε hε) t f

#print axioms pure_coordinates
#print axioms coupled_coordinates
#print axioms pure_inverse_coordinates
#print axioms coupled_inverse_coordinates
#print axioms pure_transport
#print axioms coupled_transport
#print axioms clock_multiplier
#print axioms defect_commutes
#print axioms inverse_half_commutes
end
end UnifiedTheory.Audit.KFCausalReciprocalSqueezeClockCommutation
