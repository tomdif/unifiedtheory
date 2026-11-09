/- The actual ordered transverse momentum outputs have continuous L2
orbits and finite integrated squared norm over the charge circle. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentMomentumOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

theorem momentumOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) (v : Transverse) :
    Continuous (fun θ => momentumOutput ε a hbar hε ha hh (parameter θ k) v) := by
  have hp : Continuous (fun θ : ℝ => parameter θ k) :=
    parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)
  have hd := derivative_curve_continuous (groundWidth hbar) (neutralWidth hbar) (4*Real.pi^2*‖k‖^2)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
    (fun θ => amplitudeConstant hbar (parameter θ k)) (fun θ => clockFrequency (parameter θ k))
    (fun θ => sourceCoefficients hbar (parameter θ k))
    (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha)
    ((amplitudeConstant_continuous hbar).comp hp) (clockFrequency_continuous.comp hp)
    ((sourceCoefficients_continuous hbar).comp hp) (fun θ => amplitudeConstant_bound hbar hh _)
    (fun θ => by rw [sourceCoefficients_parameter hbar hh]; exact sourceCoefficients_bound hbar hh k) v
  unfold momentumOutput
  simp_rw [dampedProfile_eq]
  exact continuous_const.smul hd

theorem momentumOutput_action_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (θ : ℝ) (k : Joint 2 4) (v : Transverse) :
    (KFCausalPhysicalCircleAction.action hbar hh θ (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k),
      momentumOutput ε a hbar hε ha hh (parameter θ k) v) ∈
        (KFCausalClockFloorTrialMomentum.clockMomentum ε hbar v).graph := by
  rw [KFCausalClockFloorCoherentStates.action_state]
  exact state_clockMomentum_graph ε a hbar hε ha hh _ v

theorem momentumOutput_orbit_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) (v : Transverse) :
    MemLp (fun θ => momentumOutput ε a hbar hε ha hh (parameter (2*Real.pi*θ) k) v) 2
      KFCausalUnitIntervalOrbit.angleMeasure :=
  continuous_angle_memLp _ ((momentumOutput_orbit_continuous ε a hbar hε ha hh k v).comp
    (continuous_const.mul continuous_id))

theorem momentumOutput_energy_integrable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) (v : Transverse) :
    Integrable (fun θ => ‖momentumOutput ε a hbar hε ha hh (parameter (2*Real.pi*θ) k) v‖^2)
      KFCausalUnitIntervalOrbit.angleMeasure :=
  (memLp_two_iff_integrable_sq_norm (momentumOutput_orbit_memLp ε a hbar hε ha hh k v).aestronglyMeasurable).mp
    (momentumOutput_orbit_memLp ε a hbar hε ha hh k v)

#print axioms momentumOutput_orbit_continuous
#print axioms momentumOutput_action_graph
#print axioms momentumOutput_orbit_memLp
#print axioms momentumOutput_energy_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentMomentumOrbit
