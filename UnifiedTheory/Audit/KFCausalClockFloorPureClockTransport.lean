/- Constructed pure-clock transport. Its exact all-L2 half-density
formula leaves all transverse coordinates fixed. This is observable
transport time, not the Hamiltonian evolution parameter. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates
import UnifiedTheory.Audit.KFCausalConfigurationTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates
open UnifiedTheory.Audit.KFCausalConfigurationTranslation

open UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates

def pureFlow (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) : Configuration :=
  (logFlow ε hε x.1 t,x.2)

theorem pureFlow_initial (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    pureFlow ε hε 0 x = x := by simp only [pureFlow,logFlow_initial,Prod.mk.eta]

theorem pureFlow_derivative (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u => pureFlow ε hε u x)
      ((1/(Real.exp (logFlow ε hε x.1 t)+ε),0):Configuration) t := by
  simpa only [pureFlow,clockFlow] using
    (logFlow_derivative ε hε x.1 t).prodMk (hasDerivAt_const t x.2)

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
  (testCoordinates ε hε).symm.trans ((translationTests t).trans (testCoordinates ε hε))

theorem transport_embedding (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) :
    transport ε hε t (embedding f) = embedding (testTransport ε hε t f) := by
  rw [transport_apply,coordinates_symm_embedding,translation_embedding,coordinates_embedding]
  rfl

theorem inverse_shift_coordinates (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    (chartHomeomorph ε hε).symm (clockShift t (chartHomeomorph ε hε x)) =
      pureFlow ε hε t x := by
  apply (chartHomeomorph ε hε).injective
  rw [Homeomorph.apply_symm_apply,clockShift_apply]
  change (chart ε x.1+t,x.2) = (chart ε (logFlow ε hε x.1 t),x.2)
  rw [chart_logFlow]

theorem testTransport_apply (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) (x : Configuration) :
    testTransport ε hε t f x =
      weight ε x*(weight ε (pureFlow ε hε t x))⁻¹*f (pureFlow ε hε t x) := by
  change testCoordinates ε hε (translationTests t ((testCoordinates ε hε).symm f)) x = _
  simp only [testCoordinates,weightedEquiv_apply,translationTests_apply,weightedEquiv_symm_apply,
    inverse_shift_coordinates,mul_assoc]

theorem transport_test_representative (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Test) :
    (transport ε hε t (embedding f) : Configuration → ℂ) =ᵐ[volume]
      fun x => weight ε x*(weight ε (pureFlow ε hε t x))⁻¹*f (pureFlow ε hε t x) := by
  rw [transport_embedding]
  filter_upwards [embedding_coe (testTransport ε hε t f)] with x hx
  rw [hx,testTransport_apply]

open UnifiedTheory.Audit.KFCausalWeightedLpRepresentative

theorem flow_quasiMeasurePreserving (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Measure.QuasiMeasurePreserving (pureFlow ε hε t) volume volume := by
  have he := (coordinate_inverse_quasiMeasurePreserving ε hε).comp
    ((clockShift_measurePreserving t).quasiMeasurePreserving.comp (coordinate_quasiMeasurePreserving ε hε))
  simpa only [Function.comp_def,inverse_shift_coordinates] using he

def transportFunction (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  weight ε x*(weight ε (pureFlow ε hε t x))⁻¹*f (pureFlow ε hε t x)

theorem transport_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    transport ε hε t f =ᵐ[volume] transportFunction ε hε t f := by
  apply dense_weighted_representative embedding embedding_dense (transport ε hε t)
    (transport ε hε t).continuous (pureFlow ε hε t) (flow_quasiMeasurePreserving ε hε t)
    (fun x => weight ε x*(weight ε (pureFlow ε hε t x))⁻¹) _ f
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


#print axioms pureFlow_initial
#print axioms pureFlow_derivative
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
end UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
