/- The optional clock-floor transport has its explicit half-density formula
on every L2 vector. The parameter remains longitudinal transport time. -/
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorLpTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalWeightedLpRepresentative

theorem flow_quasiMeasurePreserving (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Measure.QuasiMeasurePreserving (coupledFlow ε hε t) volume volume := by
  have he := (coordinate_inverse_quasiMeasurePreserving ε hε).comp
    ((clockShift_measurePreserving t).quasiMeasurePreserving.comp (coordinate_quasiMeasurePreserving ε hε))
  simpa only [Function.comp_def,inverse_shift_coordinates] using he

def transportFunction (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  weight ε x*(weight ε (coupledFlow ε hε t x))⁻¹*f (coupledFlow ε hε t x)

theorem transport_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    transport ε hε t f =ᵐ[volume] transportFunction ε hε t f := by
  apply dense_weighted_representative embedding embedding_dense (transport ε hε t)
    (transport ε hε t).continuous (coupledFlow ε hε t) (flow_quasiMeasurePreserving ε hε t)
    (fun x => weight ε x*(weight ε (coupledFlow ε hε t x))⁻¹) _ f
  intro d
  filter_upwards [transport_test_representative ε hε t d,
    (flow_quasiMeasurePreserving ε hε t).ae (embedding_coe d)] with x hx hd
  rw [hx,hd]

theorem transport_toLp_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    transport ε hε t (hf.toLp f) =ᵐ[volume] transportFunction ε hε t f := by
  filter_upwards [transport_coe ε hε t (hf.toLp f),
    (flow_quasiMeasurePreserving ε hε t).ae hf.coeFn_toLp] with x hx hf'
  rw [hx]
  simp only [transportFunction,hf']

theorem transportFunction_memLp (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2) : MemLp (transportFunction ε hε t f) 2 :=
  (Lp.memLp (transport ε hε t (hf.toLp f))).ae_eq (transport_toLp_coe ε hε t f hf)

theorem transport_toLp (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    transport ε hε t (hf.toLp f) =
      (transportFunction_memLp ε hε t f hf).toLp (transportFunction ε hε t f) := by
  apply Lp.ext
  exact (transport_toLp_coe ε hε t f hf).trans (transportFunction_memLp ε hε t f hf).coeFn_toLp.symm

theorem transportFunction_norm (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    ‖(transportFunction_memLp ε hε t f hf).toLp (transportFunction ε hε t f)‖ = ‖hf.toLp f‖ := by
  rw [← transport_toLp]
  exact (transport ε hε t).norm_map _

#print axioms flow_quasiMeasurePreserving
#print axioms transport_coe
#print axioms transport_toLp_coe
#print axioms transportFunction_memLp
#print axioms transport_toLp
#print axioms transportFunction_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorLpTransport
