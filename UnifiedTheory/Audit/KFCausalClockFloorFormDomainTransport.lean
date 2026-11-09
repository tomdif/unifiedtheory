/- An actual differentiable form-space identification of Hamiltonian
domains. It preserves shifted Hamiltonian outputs, not physical evolution. -/
import UnifiedTheory.Audit.KFCausalInverseDomainTransport
import UnifiedTheory.Audit.KFCausalClockFloorFormSecondDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "A" => referenceShift ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k

def transport (a s t : ℝ) : V →L[ℂ] V := P a t*A a s

def transportDerivative (a s t : ℝ) : V →L[ℂ] V :=
  -(P a t*D t*transport ε hε h hne hh m g k a s t)

theorem inverse_left (a : ℝ) (ha : 0 < a) (t : ℝ) : P a t*A a t = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  exact referenceInverse_left ε hε h hne hh m g k a t ha w

theorem inverse_right (a : ℝ) (ha : 0 < a) (t : ℝ) : A a t*P a t = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  exact referenceInverse_right ε hε h hne hh m g k a t ha w

theorem transport_initial (a s : ℝ) (ha : 0 < a) : transport ε hε h hne hh m g k a s s = 1 :=
  inverse_left ε hε h hne hh m g k a ha s

theorem transport_intertwines (a s t : ℝ) (ha : 0 < a) :
    A a t*transport ε hε h hne hh m g k a s t = A a s :=
  KFCausalInverseDomainTransport.transport_intertwines (P a) (A a)
    (inverse_right ε hε h hne hh m g k a ha) s t

theorem transport_compose (a s r t : ℝ) (ha : 0 < a) :
    transport ε hε h hne hh m g k a r t*transport ε hε h hne hh m g k a s r =
      transport ε hε h hne hh m g k a s t :=
  KFCausalInverseDomainTransport.transport_compose (P a) (A a)
    (inverse_right ε hε h hne hh m g k a ha) s r t

theorem transport_derivative (a s t : ℝ) (ha : 0 < a) :
    HasDerivAt (transport ε hε h hne hh m g k a s)
      (transportDerivative ε hε h hne hh m g k a s t) t :=
  KFCausalInverseDomainTransport.transport_derivative (P a) (A a) D
    (fun t => referenceInverse_derivative ε hε h hne hh m g k a t ha) s t

theorem transport_reverse_derivative (a s t : ℝ) :
    HasDerivAt (fun r => transport ε hε h hne hh m g k a r s) (P a s*D t) t :=
  KFCausalInverseDomainTransport.transport_reverse_derivative (P a) (A a) D
    (referenceShift_derivative ε hε h hne hh m g k a) s t

theorem transport_norm_bound (a s t : ℝ) (ha : 0 < a) :
    ‖transport ε hε h hne hh m g k a s t‖ ≤
      (KFCausalShiftedForm.lowerConstant a t)⁻¹*‖A a s‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (referenceInverse_norm ε hε h hne hh m g k a t ha) (norm_nonneg _))

def domainTransport (a s t : ℝ) (ha : 0 < a) (x : (H s).domain) : (H t).domain :=
  resolventVector ε hε h hne hh m g k a t ha (H s x+a • (x:Hilbert))

theorem domainTransport_embedding (a s t : ℝ) (ha : 0 < a) (x : (H s).domain) :
    J (transport ε hε h hne hh m g k a s t (referenceLift ε hε h hne hh m g k s x)) =
      (domainTransport ε hε h hne hh m g k a s t ha x : Hilbert) := by
  change J (P a t (A a s (referenceLift ε hε h hne hh m g k s x))) = _
  rw [referenceShift_hamiltonian_lift]
  rfl

theorem domainTransport_shifted (a s t : ℝ) (ha : 0 < a) (x : (H s).domain) :
    H t (domainTransport ε hε h hne hh m g k a s t ha x)+
      a • (domainTransport ε hε h hne hh m g k a s t ha x : Hilbert) =
        H s x+a • (x:Hilbert) :=
  shiftedResolvent_right ε hε h hne hh m g k a t ha _

theorem domainTransport_inverse (a s t : ℝ) (ha : 0 < a) (x : (H s).domain) :
    domainTransport ε hε h hne hh m g k a t s ha
      (domainTransport ε hε h hne hh m g k a s t ha x) = x := by
  apply Subtype.ext
  change R a s (H t (domainTransport ε hε h hne hh m g k a s t ha x)+
    a • (domainTransport ε hε h hne hh m g k a s t ha x : Hilbert)) = (x:Hilbert)
  rw [domainTransport_shifted]
  exact shiftedResolvent_left ε hε h hne hh m g k a s ha x

def domainEquiv (a s t : ℝ) (ha : 0 < a) : (H s).domain ≃ (H t).domain where
  toFun := domainTransport ε hε h hne hh m g k a s t ha
  invFun := domainTransport ε hε h hne hh m g k a t s ha
  left_inv := domainTransport_inverse ε hε h hne hh m g k a s t ha
  right_inv := domainTransport_inverse ε hε h hne hh m g k a t s ha

theorem domainTransport_bijective (a s t : ℝ) (ha : 0 < a) :
    Function.Bijective (domainTransport ε hε h hne hh m g k a s t ha) :=
  (domainEquiv ε hε h hne hh m g k a s t ha).bijective

#print axioms inverse_left
#print axioms inverse_right
#print axioms transport_initial
#print axioms transport_intertwines
#print axioms transport_compose
#print axioms transport_derivative
#print axioms transport_reverse_derivative
#print axioms transport_norm_bound
#print axioms domainTransport_embedding
#print axioms domainTransport_shifted
#print axioms domainTransport_inverse
#print axioms domainTransport_bijective
end
end UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
