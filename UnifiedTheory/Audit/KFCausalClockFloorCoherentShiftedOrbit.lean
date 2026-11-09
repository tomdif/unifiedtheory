/- The exact ordered-exponential output has a continuous L2 orbit and
finite integrated energy. Scalar multiplication and the coordinate
unitary are identified with the uniform-majorant construction. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMultiplierOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMultiplierOrbit
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)

def scalarOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) : Hilbert :=
  outputState ε a hbar hε ha hh y hy (fun _ => 1) aestronglyMeasurable_const
    (by simpa only [one_mul] using baseLine_memLp ε a hbar hε ha hh y hy) k

theorem scalarOutput_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) :
    scalarOutput ε a hbar hε ha hh y hy k = amplitudeConstant hbar k •
      gaussianState ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k) (sourceCoefficients hbar k)
        y hε ha (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hy := by
  unfold scalarOutput outputState gaussianState
  rw [← map_smul]
  apply congrArg (coordinates ε hε)
  apply Lp.ext
  filter_upwards [(modifiedLine_memLp ε a hbar hε ha hh y hy (fun _ => 1) aestronglyMeasurable_const
      (by simpa only [one_mul] using baseLine_memLp ε a hbar hε ha hh y hy) k).coeFn_toLp,
    Lp.coeFn_smul (amplitudeConstant hbar k)
      ((configurationLine_memLp ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k)
        (sourceCoefficients hbar k) y hε ha (groundWidth_positive hbar hh)
        (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hy).toLp _),
    (configurationLine_memLp ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k)
      (sourceCoefficients hbar k) y hε ha (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hy).coeFn_toLp] with x hx hs hf
  rw [hx,hs]
  change _ = amplitudeConstant hbar k * _
  rw [hf]
  simp only [modifiedLine,one_mul]

theorem scalarOutput_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) :
    scalarOutput ε a hbar hε ha hh y hy k =ᵐ[volume]
      weightedFunction ε hε (modifiedLine ε a hbar y (fun _ => 1) k) :=
  outputState_coe ε a hbar hε ha hh y hy _ _ _ k

theorem shiftedOutput_eq_scalarOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    shiftedOutput ε a hbar hε ha hh hbound k =
      scalarOutput ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k :=
  (scalarOutput_eq ε a hbar hε ha hh _ _ k).symm

theorem shiftedOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    Continuous (fun θ => shiftedOutput ε a hbar hε ha hh hbound (parameter θ k)) := by
  have he := funext (fun θ => shiftedOutput_eq_scalarOutput ε a hbar hε ha hh hbound (parameter θ k))
  rw [he]
  exact outputState_orbit_continuous ε a hbar hε ha hh _ _ _ _ _ k

theorem shiftedOutput_action_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (θ : ℝ) (k : Joint 2 4) :
    (KFCausalPhysicalCircleAction.action hbar hh θ (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k),
      shiftedOutput ε a hbar hε ha hh hbound (parameter θ k)) ∈
        (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε hbar).graph := by
  rw [KFCausalClockFloorCoherentStates.action_state]
  exact state_ordered_graph ε a hbar hε ha hh hbound _

theorem shiftedOutput_orbit_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    MemLp (fun θ => shiftedOutput ε a hbar hε ha hh hbound (parameter (2*Real.pi*θ) k)) 2
      KFCausalUnitIntervalOrbit.angleMeasure :=
  continuous_angle_memLp _ ((shiftedOutput_orbit_continuous ε a hbar hε ha hh hbound k).comp
    (continuous_const.mul continuous_id))

theorem shiftedOutput_energy_integrable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    Integrable (fun θ => ‖shiftedOutput ε a hbar hε ha hh hbound (parameter (2*Real.pi*θ) k)‖^2)
      KFCausalUnitIntervalOrbit.angleMeasure :=
  (memLp_two_iff_integrable_sq_norm (shiftedOutput_orbit_memLp ε a hbar hε ha hh hbound k).aestronglyMeasurable).mp
    (shiftedOutput_orbit_memLp ε a hbar hε ha hh hbound k)

#print axioms scalarOutput_eq
#print axioms scalarOutput_coe
#print axioms shiftedOutput_eq_scalarOutput
#print axioms shiftedOutput_orbit_continuous
#print axioms shiftedOutput_action_graph
#print axioms shiftedOutput_orbit_memLp
#print axioms shiftedOutput_energy_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit
