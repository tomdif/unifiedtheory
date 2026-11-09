/- Positive shifted resolvents of the actual homogeneous Hamiltonian.
The inverse on the fixed reference form space is constructed from
coercivity, and both physical resolvent identities are proved. -/
import UnifiedTheory.Audit.KFCausalShiftedForm
import UnifiedTheory.Audit.KFCausalInverseCurve
import UnifiedTheory.Audit.KFCausalRegularizedHamiltonianFormBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalCoerciveInverse
open UnifiedTheory.Audit.KFCausalInverseCurve
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedHamiltonian
open UnifiedTheory.Audit.KFCausalRegularizedHamiltonianFormBridge

theorem reference_decomposition (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    ‖u‖^2 = ‖embedding ε hε hbar coupling 0 u‖^2 + ‖clockMap ε hε hbar coupling u‖^2 +
      ‖momentumMap ε hε hbar coupling u‖^2 := reference_norm_identity ε hε hbar coupling u

def referenceShift (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  shiftForm (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0) (clockMap ε hε hbar coupling)
    (momentumMap ε hε hbar coupling) a t

theorem referenceShift_isUnit (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    IsUnit (referenceShift ε hε hbar coupling a t) :=
  shiftForm_isUnit _ _ _ a t ha (reference_decomposition ε hε hbar coupling)

theorem referenceShift_pairing (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ)
    (u v : FormSpace ε hε hbar coupling 0) :
    inner ℂ (referenceShift ε hε hbar coupling a t u) v =
      (a:ℂ)*inner ℂ (embedding ε hε hbar coupling 0 u) (embedding ε hε hbar coupling 0 v) +
      inner ℂ u (referenceFormOperator ε hε hbar coupling t v) := by
  have hs : inner ℂ (referenceShift ε hε hbar coupling a t u) v =
      inner ℂ u (referenceShift ε hε hbar coupling a t v) := shiftForm_inner_symm _ _ _ a t u v
  exact hs.trans (shiftForm_pairing _ _ _ a t u v)

theorem referenceShift_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    HasDerivAt (referenceShift ε hε hbar coupling a)
      (referenceFormDerivative ε hε hbar coupling t) t :=
  (referenceForm_derivative ε hε hbar coupling t).const_add
    (a • gram (E := FormSpace ε hε hbar coupling 0) (H := Hilbert) (embedding ε hε hbar coupling 0))

theorem referenceShift_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) :
    Continuous (referenceShift ε hε hbar coupling a) :=
  continuous_iff_continuousAt.mpr fun t => (referenceShift_derivative ε hε hbar coupling a t).continuousAt

def referenceInverse (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  Ring.inverse (referenceShift ε hε hbar coupling a t)

theorem referenceInverse_left (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (u : FormSpace ε hε hbar coupling 0) :
    referenceInverse ε hε hbar coupling a t (referenceShift ε hε hbar coupling a t u) = u :=
  inverse_apply_left _ (referenceShift_isUnit ε hε hbar coupling a t ha) u

theorem referenceInverse_right (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (u : FormSpace ε hε hbar coupling 0) :
    referenceShift ε hε hbar coupling a t (referenceInverse ε hε hbar coupling a t u) = u :=
  inverse_apply_right _ (referenceShift_isUnit ε hε hbar coupling a t ha) u

theorem referenceInverse_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    ‖referenceInverse ε hε hbar coupling a t‖ ≤ (lowerConstant a t)⁻¹ :=
  shiftForm_inverse_norm _ _ _ a t ha (reference_decomposition ε hε hbar coupling)

def referenceInverseDerivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  -(referenceInverse ε hε hbar coupling a t * referenceFormDerivative ε hε hbar coupling t *
    referenceInverse ε hε hbar coupling a t)

theorem referenceInverse_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    HasDerivAt (referenceInverse ε hε hbar coupling a)
      (referenceInverseDerivative ε hε hbar coupling a t) t :=
  inverseCurve_hasDerivAt _ _ t (referenceShift_derivative ε hε hbar coupling a t)
    (referenceShift_isUnit ε hε hbar coupling a t ha)

theorem referenceInverse_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (referenceInverse ε hε hbar coupling a) :=
  inverseCurve_continuous _ (referenceShift_continuous ε hε hbar coupling a)
    (fun t => referenceShift_isUnit ε hε hbar coupling a t ha)

theorem referenceInverse_derivative_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (referenceInverseDerivative ε hε hbar coupling a) :=
  inverseCurve_derivative_continuous _ _ (referenceShift_continuous ε hε hbar coupling a)
    (referenceForm_derivative_continuous ε hε hbar coupling)
    (fun t => referenceShift_isUnit ε hε hbar coupling a t ha)

def referenceAdjoint (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    Hilbert →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := FormSpace ε hε hbar coupling 0) (F := Hilbert)
    (embedding ε hε hbar coupling 0)

def resolventFormLift (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (f : Hilbert) :
    FormSpace ε hε hbar coupling 0 :=
  referenceInverse ε hε hbar coupling a t ((referenceAdjoint ε hε hbar coupling) f)

def shiftedResolvent (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (embedding ε hε hbar coupling 0).comp ((referenceInverse ε hε hbar coupling a t).comp
    (referenceAdjoint ε hε hbar coupling))

theorem shiftedResolvent_apply (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (f : Hilbert) :
    shiftedResolvent ε hε hbar coupling a t f =
      embedding ε hε hbar coupling 0 (resolventFormLift ε hε hbar coupling a t f) := rfl

theorem shiftedResolvent_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (shiftedResolvent ε hε hbar coupling a) :=
  continuous_const.clm_comp ((referenceInverse_continuous ε hε hbar coupling a ha).clm_comp continuous_const)

theorem shiftedResolvent_variational (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ)
    (ha : 0 < a) (f : Hilbert) (v : FormSpace ε hε hbar coupling 0) :
    inner ℂ (resolventFormLift ε hε hbar coupling a t f) (referenceFormOperator ε hε hbar coupling t v) =
      inner ℂ (f-a • shiftedResolvent ε hε hbar coupling a t f) (embedding ε hε hbar coupling 0 v) := by
  have hu : referenceShift ε hε hbar coupling a t (resolventFormLift ε hε hbar coupling a t f) =
      (referenceAdjoint ε hε hbar coupling) f := referenceInverse_right ε hε hbar coupling a t ha _
  exact shifted_variational _ _ _ a t _ f hu v

theorem shiftedResolvent_equation (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ)
    (ha : 0 < a) (f : Hilbert) :
    ∃ hx : shiftedResolvent ε hε hbar coupling a t f ∈ (homogeneousHamiltonian ε hε hbar coupling t).domain,
      homogeneousHamiltonian ε hε hbar coupling t ⟨shiftedResolvent ε hε hbar coupling a t f,hx⟩ =
        f-a • shiftedResolvent ε hε hbar coupling a t f :=
  (reference_domain_characterization ε hε hbar coupling t (resolventFormLift ε hε hbar coupling a t f)
    (f-a • shiftedResolvent ε hε hbar coupling a t f)).mpr
      (shiftedResolvent_variational ε hε hbar coupling a t ha f)

def resolventVector (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    (homogeneousHamiltonian ε hε hbar coupling t).domain :=
  ⟨shiftedResolvent ε hε hbar coupling a t f,(shiftedResolvent_equation ε hε hbar coupling a t ha f).choose⟩

theorem hamiltonian_resolvent (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    homogeneousHamiltonian ε hε hbar coupling t (resolventVector ε hε hbar coupling a t ha f) =
      f-a • shiftedResolvent ε hε hbar coupling a t f :=
  (shiftedResolvent_equation ε hε hbar coupling a t ha f).choose_spec

theorem shiftedResolvent_right (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    homogeneousHamiltonian ε hε hbar coupling t (resolventVector ε hε hbar coupling a t ha f) +
      a • shiftedResolvent ε hε hbar coupling a t f = f := by
  rw [hamiltonian_resolvent,sub_add_cancel]

theorem referenceShift_hamiltonian_lift (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    referenceShift ε hε hbar coupling a t (referenceLift ε hε hbar coupling t x) =
      (referenceAdjoint ε hε hbar coupling) (homogeneousHamiltonian ε hε hbar coupling t x + a • (x:Hilbert)) := by
  apply ext_inner_right ℂ
  intro v
  rw [referenceShift_pairing,referenceLift_embedding,reference_hamiltonian_pairing,
    referenceAdjoint,ContinuousLinearMap.adjoint_inner_left,inner_add_left,inner_smul_left_eq_smul]
  change (a:ℂ)*inner ℂ (x:Hilbert) (embedding ε hε hbar coupling 0 v) +
    inner ℂ (homogeneousHamiltonian ε hε hbar coupling t x) (embedding ε hε hbar coupling 0 v) = _
  exact add_comm _ _

theorem shiftedResolvent_left (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    shiftedResolvent ε hε hbar coupling a t
      (homogeneousHamiltonian ε hε hbar coupling t x + a • (x:Hilbert)) = x := by
  rw [shiftedResolvent_apply]
  unfold resolventFormLift
  rw [← referenceShift_hamiltonian_lift ε hε hbar coupling a t x,
    referenceInverse_left ε hε hbar coupling a t ha]
  exact referenceLift_embedding ε hε hbar coupling t x

#print axioms referenceShift_isUnit
#print axioms referenceShift_derivative
#print axioms referenceInverse_norm
#print axioms referenceInverse_derivative
#print axioms referenceInverse_derivative_continuous
#print axioms shiftedResolvent_continuous
#print axioms shiftedResolvent_equation
#print axioms shiftedResolvent_right
#print axioms referenceShift_hamiltonian_lift
#print axioms shiftedResolvent_left

end
end UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
