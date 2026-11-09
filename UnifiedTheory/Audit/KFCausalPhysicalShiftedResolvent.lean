/- Positive shifted resolvents for the actual eight-factor Hamiltonian.
The reference-form inverse is constructed from coercivity; its physical
compression satisfies both unbounded resolvent identities. -/
import UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
import UnifiedTheory.Audit.KFCausalInverseCurve
import UnifiedTheory.Audit.KFCausalPhysicalHamiltonianFormBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalShiftedResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalCoerciveInverse
open UnifiedTheory.Audit.KFCausalInverseCurve
open UnifiedTheory.Audit.KFCausalShiftedForm (lowerConstant)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl
open UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
open UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian
open UnifiedTheory.Audit.KFCausalPhysicalHamiltonianFormBridge

theorem reference_decomposition (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖u‖^2 = ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖^2 + ‖staticMap ε hε hbar hh mass2 quartic vacuum u‖^2 +
      ‖growingMap ε hε hbar hh mass2 quartic vacuum u‖^2 := reference_norm_identity ε hε hbar hh mass2 quartic vacuum u

def referenceShift (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  shiftForm (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert) (K := Output (Fin 8) Hilbert)
    (embedding ε hε hbar hh mass2 quartic vacuum 0) (staticMap ε hε hbar hh mass2 quartic vacuum)
    (growingMap ε hε hbar hh mass2 quartic vacuum) a t

theorem referenceShift_isUnit (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    IsUnit (referenceShift ε hε hbar hh mass2 quartic vacuum a t) :=
  shiftForm_isUnit _ _ _ a t ha (reference_decomposition ε hε hbar hh mass2 quartic vacuum)

theorem referenceShift_pairing (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ)
    (u v : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    inner ℂ (referenceShift ε hε hbar hh mass2 quartic vacuum a t u) v =
      (a:ℂ)*inner ℂ (embedding ε hε hbar hh mass2 quartic vacuum 0 u) (embedding ε hε hbar hh mass2 quartic vacuum 0 v) +
      inner ℂ u (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v) := by
  have hs : inner ℂ (referenceShift ε hε hbar hh mass2 quartic vacuum a t u) v =
      inner ℂ u (referenceShift ε hε hbar hh mass2 quartic vacuum a t v) := shiftForm_inner_symm _ _ _ a t u v
  exact hs.trans (shiftForm_pairing _ _ _ a t u v)

theorem referenceShift_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) :
    HasDerivAt (referenceShift ε hε hbar hh mass2 quartic vacuum a)
      (referenceFormDerivative ε hε hbar hh mass2 quartic vacuum t) t :=
  (referenceForm_derivative ε hε hbar hh mass2 quartic vacuum t).const_add
    (a • gram (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert) (embedding ε hε hbar hh mass2 quartic vacuum 0))

theorem referenceShift_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) :
    Continuous (referenceShift ε hε hbar hh mass2 quartic vacuum a) :=
  continuous_iff_continuousAt.mpr fun t => (referenceShift_derivative ε hε hbar hh mass2 quartic vacuum a t).continuousAt

def referenceInverse (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  Ring.inverse (referenceShift ε hε hbar hh mass2 quartic vacuum a t)

theorem referenceInverse_left (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    referenceInverse ε hε hbar hh mass2 quartic vacuum a t (referenceShift ε hε hbar hh mass2 quartic vacuum a t u) = u :=
  inverse_apply_left _ (referenceShift_isUnit ε hε hbar hh mass2 quartic vacuum a t ha) u

theorem referenceInverse_right (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    referenceShift ε hε hbar hh mass2 quartic vacuum a t (referenceInverse ε hε hbar hh mass2 quartic vacuum a t u) = u :=
  inverse_apply_right _ (referenceShift_isUnit ε hε hbar hh mass2 quartic vacuum a t ha) u

theorem referenceInverse_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    ‖referenceInverse ε hε hbar hh mass2 quartic vacuum a t‖ ≤ (lowerConstant a t)⁻¹ :=
  shiftForm_inverse_norm _ _ _ a t ha (reference_decomposition ε hε hbar hh mass2 quartic vacuum)

def referenceInverseDerivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  -(referenceInverse ε hε hbar hh mass2 quartic vacuum a t * referenceFormDerivative ε hε hbar hh mass2 quartic vacuum t *
    referenceInverse ε hε hbar hh mass2 quartic vacuum a t)

theorem referenceInverse_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    HasDerivAt (referenceInverse ε hε hbar hh mass2 quartic vacuum a)
      (referenceInverseDerivative ε hε hbar hh mass2 quartic vacuum a t) t :=
  inverseCurve_hasDerivAt _ _ t (referenceShift_derivative ε hε hbar hh mass2 quartic vacuum a t)
    (referenceShift_isUnit ε hε hbar hh mass2 quartic vacuum a t ha)

theorem referenceInverse_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a) :
    Continuous (referenceInverse ε hε hbar hh mass2 quartic vacuum a) :=
  inverseCurve_continuous _ (referenceShift_continuous ε hε hbar hh mass2 quartic vacuum a)
    (fun t => referenceShift_isUnit ε hε hbar hh mass2 quartic vacuum a t ha)

theorem referenceInverse_derivative_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a) :
    Continuous (referenceInverseDerivative ε hε hbar hh mass2 quartic vacuum a) :=
  inverseCurve_derivative_continuous _ _ (referenceShift_continuous ε hε hbar hh mass2 quartic vacuum a)
    (referenceForm_derivative_continuous ε hε hbar hh mass2 quartic vacuum)
    (fun t => referenceShift_isUnit ε hε hbar hh mass2 quartic vacuum a t ha)

def referenceAdjoint (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ) :
    Hilbert →L[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (F := Hilbert)
    (embedding ε hε hbar hh mass2 quartic vacuum 0)

def resolventFormLift (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (f : Hilbert) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  referenceInverse ε hε hbar hh mass2 quartic vacuum a t ((referenceAdjoint ε hε hbar hh mass2 quartic vacuum) f)

def shiftedResolvent (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (embedding ε hε hbar hh mass2 quartic vacuum 0).comp ((referenceInverse ε hε hbar hh mass2 quartic vacuum a t).comp
    (referenceAdjoint ε hε hbar hh mass2 quartic vacuum))

theorem shiftedResolvent_apply (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (f : Hilbert) :
    shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f =
      embedding ε hε hbar hh mass2 quartic vacuum 0 (resolventFormLift ε hε hbar hh mass2 quartic vacuum a t f) := rfl

theorem shiftedResolvent_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a) :
    Continuous (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a) :=
  continuous_const.clm_comp ((referenceInverse_continuous ε hε hbar hh mass2 quartic vacuum a ha).clm_comp continuous_const)

theorem shiftedResolvent_variational (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ)
    (ha : 0 < a) (f : Hilbert) (v : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    inner ℂ (resolventFormLift ε hε hbar hh mass2 quartic vacuum a t f) (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v) =
      inner ℂ (f-a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f) (embedding ε hε hbar hh mass2 quartic vacuum 0 v) := by
  have hu : referenceShift ε hε hbar hh mass2 quartic vacuum a t (resolventFormLift ε hε hbar hh mass2 quartic vacuum a t f) =
      (referenceAdjoint ε hε hbar hh mass2 quartic vacuum) f := referenceInverse_right ε hε hbar hh mass2 quartic vacuum a t ha _
  exact shifted_variational _ _ _ a t _ f hu v

theorem shiftedResolvent_equation (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ)
    (ha : 0 < a) (f : Hilbert) :
    ∃ hx : shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f ∈ (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain,
      hamiltonian ε hε hbar hh mass2 quartic vacuum t ⟨shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f,hx⟩ =
        f-a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f :=
  (hamiltonian_reference_domain ε hε hbar hh mass2 quartic vacuum t (resolventFormLift ε hε hbar hh mass2 quartic vacuum a t f)
    (f-a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f)).mpr
      (shiftedResolvent_variational ε hε hbar hh mass2 quartic vacuum a t ha f)

def resolventVector (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain :=
  ⟨shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f,(shiftedResolvent_equation ε hε hbar hh mass2 quartic vacuum a t ha f).choose⟩

theorem hamiltonian_resolvent (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    hamiltonian ε hε hbar hh mass2 quartic vacuum t (resolventVector ε hε hbar hh mass2 quartic vacuum a t ha f) =
      f-a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f :=
  (shiftedResolvent_equation ε hε hbar hh mass2 quartic vacuum a t ha f).choose_spec

theorem shiftedResolvent_right (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    hamiltonian ε hε hbar hh mass2 quartic vacuum t (resolventVector ε hε hbar hh mass2 quartic vacuum a t ha f) +
      a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f = f := by
  rw [hamiltonian_resolvent,sub_add_cancel]

theorem referenceShift_hamiltonian_lift (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ)
    (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    referenceShift ε hε hbar hh mass2 quartic vacuum a t (referenceLift ε hε hbar hh mass2 quartic vacuum t x) =
      (referenceAdjoint ε hε hbar hh mass2 quartic vacuum) (hamiltonian ε hε hbar hh mass2 quartic vacuum t x + a • (x:Hilbert)) := by
  apply ext_inner_right ℂ
  intro v
  rw [referenceShift_pairing,embedding_referenceLift,hamiltonian_reference_pairing,
    referenceAdjoint,ContinuousLinearMap.adjoint_inner_left,inner_add_left,inner_smul_left_eq_smul]
  change (a:ℂ)*inner ℂ (x:Hilbert) (embedding ε hε hbar hh mass2 quartic vacuum 0 v) +
    inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) (embedding ε hε hbar hh mass2 quartic vacuum 0 v) = _
  exact add_comm _ _

theorem shiftedResolvent_left (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t
      (hamiltonian ε hε hbar hh mass2 quartic vacuum t x + a • (x:Hilbert)) = x := by
  rw [shiftedResolvent_apply]
  unfold resolventFormLift
  rw [← referenceShift_hamiltonian_lift ε hε hbar hh mass2 quartic vacuum a t x,
    referenceInverse_left ε hε hbar hh mass2 quartic vacuum a t ha]
  exact embedding_referenceLift ε hε hbar hh mass2 quartic vacuum t x

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
end UnifiedTheory.Audit.KFCausalPhysicalShiftedResolvent
