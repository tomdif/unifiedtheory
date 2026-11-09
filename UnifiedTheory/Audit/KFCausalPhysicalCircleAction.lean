/- A concrete, frequency-normalized circle representation on physical L2.
This transports the constructed standing-wave rotation through the actual
mixed-coordinate unitary. Finite occupation-space identification and
invariance of the Hamiltonian energy domain remain separate obligations. -/
import UnifiedTheory.Audit.KFCausalMixedCircleAction
import UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
import UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalCircleAction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage

def chargeCoordinates : Hilbert ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  mixedCoordinates.trans (coordinates 2 4)

def action (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  chargeCoordinates.trans
    ((KFCausalMixedCircleAction.action (momentumScale hbar) (momentumScale_ne_zero hbar hh) θ).trans
      chargeCoordinates.symm)

theorem action_coordinates (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    chargeCoordinates (action hbar hh θ f) =
      KFCausalMixedCircleAction.action (momentumScale hbar) (momentumScale_ne_zero hbar hh) θ
        (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

theorem action_zero (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) : action hbar hh 0 f = f := by
  apply chargeCoordinates.injective
  rw [action_coordinates, KFCausalMixedCircleAction.action_zero]

theorem action_compose (hbar : ℝ) (hh : hbar ≠ 0) (θ φ : ℝ) (f : Hilbert) :
    action hbar hh φ (action hbar hh θ f) = action hbar hh (θ+φ) f := by
  apply chargeCoordinates.injective
  rw [action_coordinates, action_coordinates, action_coordinates,
    KFCausalMixedCircleAction.action_compose]

theorem action_period (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    action hbar hh (θ+2*Real.pi) f = action hbar hh θ f := by
  apply chargeCoordinates.injective
  rw [action_coordinates, action_coordinates, KFCausalMixedCircleAction.action_period]

theorem action_full_period (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    action hbar hh (2*Real.pi) f = f := by
  simpa only [zero_add, action_zero] using action_period hbar hh 0 f

theorem action_reverse (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    action hbar hh (-θ) (action hbar hh θ f) = f := by
  rw [action_compose, add_neg_cancel, action_zero]

theorem action_strong_continuous (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    Continuous (fun θ => action hbar hh θ f) :=
  chargeCoordinates.symm.continuous.comp
    (KFCausalMixedCircleAction.action_strong_continuous _ _ (chargeCoordinates f))

theorem action_joint_continuous (hbar : ℝ) (hh : hbar ≠ 0) :
    Continuous (fun p : ℝ × Hilbert => action hbar hh p.1 p.2) :=
  KFCausalStrongUnitaryContinuity.joint_evaluation_continuous _ (action_strong_continuous hbar hh)

theorem action_unitary (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) :
    (action hbar hh θ : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (Unitary.linearIsometryEquiv.symm (action hbar hh θ)).property

def group (hbar : ℝ) (hh : hbar ≠ 0) : StrongUnitaryGroup Hilbert where
  action := action hbar hh
  initial := action_zero hbar hh
  compose := action_compose hbar hh
  continuous_orbit := action_strong_continuous hbar hh

#print axioms chargeCoordinates
#print axioms action
#print axioms action_coordinates
#print axioms action_zero
#print axioms action_compose
#print axioms action_period
#print axioms action_full_period
#print axioms action_reverse
#print axioms action_strong_continuous
#print axioms action_joint_continuous
#print axioms action_unitary
#print axioms group

end
end UnifiedTheory.Audit.KFCausalPhysicalCircleAction
