/- Exact drift pairings in the straightened coordinates. The physical
bounded drift multiplier is transported through the actual coordinate
unitary; it is not inferred from convergence of unweighted energies. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
import UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorDriftCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realDefect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator driftOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity (recenter)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale)

def realDrift (ε : ℝ) (hε : 0 < ε) (u : ℝ) : ℝ := drift ε (realDefect ε hε u)

theorem realDrift_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (realDrift ε hε) :=
  (drift_clock_continuous ε hε).comp
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm.toHomeomorph.continuous

theorem realDrift_bound (ε : ℝ) (hε : 0 < ε) (u : ℝ) : |realDrift ε hε u| ≤ 1/ε :=
  drift_clock_bound ε hε _

theorem inverse_coordinates_drift_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (coordinates ε hε).symm (driftOperator ε hε f) =ᵐ[volume]
      fun x => (realDrift ε hε x.1:ℂ)*((coordinates ε hε).symm f) x := by
  filter_upwards [coordinates_inverse_coe ε hε (driftOperator ε hε f),
    coordinates_inverse_coe ε hε f,
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae (driftOperator_coe ε hε f)] with x hx hy hd
  rw [hx,hy]
  unfold inverseFunction
  rw [hd]
  change _ * ((realDrift ε hε x.1:ℂ)*_) = (realDrift ε hε x.1:ℂ)*(_*_)
  ring

theorem coordinates_pairing (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (inner ℂ (coordinates ε hε f) (driftOperator ε hε (coordinates ε hε f))).re =
      ∫ x : Configuration, realDrift ε hε x.1*‖f x‖^2 := by
  rw [← (coordinates ε hε).symm.inner_map_map,
    real_multiplier_pairing volume _ _ _ (inverse_coordinates_drift_coe ε hε _)]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem coordinates_toLp_pairing (ε : ℝ) (hε : 0 < ε)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    (inner ℂ (coordinates ε hε (hf.toLp f))
      (driftOperator ε hε (coordinates ε hε (hf.toLp f)))).re =
        ∫ x : Configuration, realDrift ε hε x.1*‖f x‖^2 := by
  rw [coordinates_pairing]
  exact integral_congr_ae (hf.coeFn_toLp.mono (fun x hx => by dsimp only; rw [hx]))

theorem drift_mul_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ε : ℝ) (hε : 0 < ε) (u : X → ℝ) (hu : Measurable u)
    (f : X → ℝ) (hf : Integrable f μ) :
    Integrable (fun x => realDrift ε hε (u x)*f x) μ := by
  apply (hf.norm.const_mul (1/ε)).mono'
    (((realDrift_continuous ε hε).measurable.comp hu).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  dsimp only [Pi.mul_apply,Function.comp_def]
  rw [norm_mul,Real.norm_eq_abs (realDrift ε hε (u x))]
  exact mul_le_mul_of_nonneg_right (realDrift_bound ε hε (u x)) (norm_nonneg _)

theorem recentered_drift_integral (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (Q : Transverse) (f : ℝ × Grouped → ℂ) (hf : MemLp f 2) :
    (∫ z, realDrift ε hε z.1*‖f z‖^2) = (scale h)^5*
      ∫ u : ℝ, realDrift ε hε u*clockJacobian ε hε u*
        ∫ ξ : Transverse, ‖f (u,recenter ε hε u h Q ξ)‖^2 := by
  have hi := drift_mul_integrable volume ε hε Prod.fst measurable_fst _
    ((memLp_two_iff_integrable_sq_norm hf.1).mp hf)
  rw [Measure.volume_eq_prod ℝ Grouped] at hi ⊢
  rw [integral_prod _ hi,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [integral_const_mul,recenter_integral ε hε u h hh Q]
  ring

#print axioms realDrift_continuous
#print axioms realDrift_bound
#print axioms inverse_coordinates_drift_coe
#print axioms coordinates_pairing
#print axioms coordinates_toLp_pairing
#print axioms drift_mul_integrable
#print axioms recentered_drift_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorDriftCoordinates
