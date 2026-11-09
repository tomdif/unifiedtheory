/- A normalized twelve-real-parameter family obtained by actual unitary
displacements and phases in mixed coordinates. It is closed under the
physical charge circle. Energy-domain claims require separate analysis. -/
import UnifiedTheory.Audit.KFCausalChargeDisplacementCovariance
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
import UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedRotation (Space)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalChargeDisplacementCovariance
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (trialState trialState_mem_zeroSector)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial unitTrial_norm)

def operator (h : ℝ) (q k : Space) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  chargeCoordinates.trans ((displacement (momentumScale h) q k).trans chargeCoordinates.symm)

theorem operator_coordinates (h : ℝ) (q k : Space) (f : Hilbert) :
    chargeCoordinates (operator h q k f) = displacement (momentumScale h) q k (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

theorem operator_zero (h : ℝ) (f : Hilbert) : operator h 0 0 f = f := by
  apply chargeCoordinates.injective
  rw [operator_coordinates,displacement_zero]

theorem action_operator (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (q k : Space) (f : Hilbert) :
    action h hh θ (operator h q k f) = operator h (parameter θ q) (parameter θ k) (action h hh θ f) := by
  apply chargeCoordinates.injective
  rw [action_coordinates,operator_coordinates,operator_coordinates,action_coordinates,
    action_displacement]

def rawState (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Space) : Hilbert :=
  operator h q k (trialState ε a h hε ha hh)

def state (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Space) : Hilbert :=
  operator h q k (unitTrial ε a h hε ha hh)

theorem state_normalization (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Space) :
    state ε a h hε ha hh q k =
      (‖trialState ε a h hε ha hh‖⁻¹ : ℝ) • rawState ε a h hε ha hh q k :=
  (operator h q k : Hilbert →L[ℂ] Hilbert).map_smul_of_tower _ _

theorem state_norm (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Space) :
    ‖state ε a h hε ha hh q k‖ = 1 :=
  ((operator h q k).norm_map _).trans (unitTrial_norm ε a h hε ha hh)

theorem rawState_zero_displacement (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (k : Space) :
    rawState ε a h hε ha hh 0 k = KFCausalClockFloorCoherentStates.state ε a h hε ha hh k := by
  apply chargeCoordinates.injective
  rw [rawState,operator_coordinates,KFCausalClockFloorCoherentStates.state_coordinates]
  apply Lp.ext
  filter_upwards [displacement_coe (momentumScale h) 0 k
      (chargeCoordinates (trialState ε a h hε ha hh)),
    KFCausalClockFloorCoherentStates.weight_coe ε a h hε ha hh,
    KFCausalClockFloorCoherentStates.mixedState_coe ε a h hε ha hh k] with x hx hy hz
  have hzero : dilate (momentumScale h)⁻¹ (0 : Space) = 0 :=
    (dilationEquiv _ (inv_ne_zero (momentumScale_ne_zero h hh))).map_zero
  rw [hx,hzero,add_zero,hy,hz]
  unfold KFCausalEuclideanFourierUniqueness.modulate KFCausalFourierTranslation.phase
  rw [real_inner_comm]

theorem action_rawState (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (θ : ℝ) (q k : Space) :
    action h hh θ (rawState ε a h hε ha hh q k) =
      rawState ε a h hε ha hh (parameter θ q) (parameter θ k) := by
  unfold rawState
  rw [action_operator]
  exact congrArg (operator h (parameter θ q) (parameter θ k))
    (trialState_mem_zeroSector ε a h hε ha hh θ)

theorem action_state (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (θ : ℝ) (q k : Space) :
    action h hh θ (state ε a h hε ha hh q k) =
      state ε a h hε ha hh (parameter θ q) (parameter θ k) := by
  unfold state
  rw [action_operator]
  exact congrArg (operator h (parameter θ q) (parameter θ k))
    (KFCausalClockFloorSemiclassicalStates.unitTrial_zeroSector ε a h hε ha hh θ)

theorem orbit_continuous (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Space) :
    Continuous (fun θ => state ε a h hε ha hh (parameter θ q) (parameter θ k)) := by
  simp_rw [← action_state ε a h hε ha hh]
  exact action_strong_continuous h hh _

#print axioms operator_coordinates
#print axioms operator_zero
#print axioms action_operator
#print axioms state_normalization
#print axioms state_norm
#print axioms rawState_zero_displacement
#print axioms action_rawState
#print axioms action_state
#print axioms orbit_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates
