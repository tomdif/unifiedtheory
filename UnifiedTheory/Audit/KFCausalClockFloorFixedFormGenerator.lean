/- The moving form-space Hamiltonian is converted to an explicit
closed-domain generator on a fixed domain, including the connection term.
This constructs the transformed equation, not its domain-preserving flow. -/
import UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
import UnifiedTheory.Audit.KFCausalHilbertStateEvolution
import UnifiedTheory.Audit.KFCausalClosedFixedDomainPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFormSecondDerivative
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

def connection (a s t : ℝ) : V →L[ℂ] V := P a s*D t*S a s t

def connectionDerivative (a s t : ℝ) : V →L[ℂ] V :=
  P a s*((2:ℝ) • D t)*S a s t+P a s*D t*S' a s t

def principal (a s t : ℝ) : V →L[ℂ] V := c • S a t s

def correction (a s t : ℝ) : V →L[ℂ] V :=
  c • (a • (S a t s-1))+connection ε hε h hne hh m g k a s t

def fixedGenerator (a s t : ℝ) : V →ₗ.[ℂ] V where
  domain := (L s).domain
  toFun := (principal ε hε h hne hh m g k a s t).toLinearMap.comp (L s).toFun+
    (correction ε hε h hne hh m g k a s t).toLinearMap.comp (L s).domain.subtype

theorem fixed_domain (a s t : ℝ) :
    (fixedGenerator ε hε h hne hh m g k a s t).domain = (L s).domain := rfl

theorem fixed_dense (a s t : ℝ) :
    Dense ((fixedGenerator ε hε h hne hh m g k a s t).domain : Set V) :=
  lifted_dense ε hε h hne hh m g k s

theorem fixed_closed (a s t : ℝ) (ha : 0 < a) :
    (fixedGenerator ε hε h hne hh m g k a s t).IsClosed := by
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hne))
  have hi (r q : ℝ) (v : V) : S a r q (S a q r v) = v := by
    have he := congrArg (fun T : V →L[ℂ] V => T v)
      (transport_compose ε hε h hne hh m g k a q r q ha)
    simpa only [ContinuousLinearMap.mul_apply,transport_initial ε hε h hne hh m g k a q ha,
      ContinuousLinearMap.one_apply] using he
  exact KFCausalClosedFixedDomainPerturbation.transform_closed (L s)
    (lifted_closed ε hε h hne hh m g k s)
    (principal ε hε h hne hh m g k a s t) (correction ε hε h hne hh m g k a s t)
    (c⁻¹ • S a s t)
    (fun v => by simp only [principal,ContinuousLinearMap.smul_apply,map_smul,
      hi,smul_smul,mul_inv_cancel₀ hc,one_smul])
    (fun v => by simp only [principal,ContinuousLinearMap.smul_apply,map_smul,
      hi,smul_smul,inv_mul_cancel₀ hc,one_smul])

theorem fixed_action (a s t : ℝ) (w : (L s).domain) :
    fixedGenerator ε hε h hne hh m g k a s t w =
      c • S a t s (L s w+a • (w:V))-c • (a • (w:V))+
        connection ε hε h hne hh m g k a s t w :=
  KFCausalClosedFixedDomainPerturbation.shifted_action (L s) (S a t s)
    (connection ε hε h hne hh m g k a s t) c a w

theorem connection_derivative (a s t : ℝ) (ha : 0 < a) :
    HasDerivAt (connection ε hε h hne hh m g k a s)
      (connectionDerivative ε hε h hne hh m g k a s t) t :=
  ((form_second_derivative ε hε h hne hh m g k t).const_mul (P a s)).mul
    (transport_derivative ε hε h hne hh m g k a s t ha)

theorem principal_derivative (a s t : ℝ) :
    HasDerivAt (principal ε hε h hne hh m g k a s) (c • (P a s*D t)) t :=
  (transport_reverse_derivative ε hε h hne hh m g k a s t).const_smul c

theorem correction_derivative (a s t : ℝ) (ha : 0 < a) :
    HasDerivAt (correction ε hε h hne hh m g k a s)
      (c • (a • (P a s*D t))+connectionDerivative ε hε h hne hh m g k a s t) t := by
  exact ((((transport_reverse_derivative ε hε h hne hh m g k a s t).sub_const 1).const_smul a).const_smul c).add
    (connection_derivative ε hε h hne hh m g k a s t ha)

theorem connection_cancels (a s t : ℝ) (ha : 0 < a) :
    S a s t*connection ε hε h hne hh m g k a s t = -(S' a s t) :=
  KFCausalInverseDomainTransport.inverse_connection_identity (P a)
    (referenceShift ε hε h hne hh m g k a) D
    (inverse_right ε hε h hne hh m g k a ha) s t

theorem transported_action (a s t : ℝ) (ha : 0 < a) (w : (L s).domain) :
    S a s t (fixedGenerator ε hε h hne hh m g k a s t w)+S' a s t w =
      c • (L s w+a • (w:V)-a • S a s t w) := by
  have hi (v : V) : S a s t (S a t s v) = v := by
    have he := congrArg (fun T : V →L[ℂ] V => T v)
      (transport_compose ε hε h hne hh m g k a t s t ha)
    simpa only [ContinuousLinearMap.mul_apply,transport_initial ε hε h hne hh m g k a t ha,
      ContinuousLinearMap.one_apply] using he
  have hc (v : V) : S a s t (connection ε hε h hne hh m g k a s t v) = -S' a s t v :=
    congrArg (fun T : V →L[ℂ] V => T v)
      (connection_cancels ε hε h hne hh m g k a s t ha)
  exact (congrArg (fun v : V => S a s t v+S' a s t w)
    (fixed_action ε hε h hne hh m g k a s t w)).trans
    (KFCausalClosedFixedDomainPerturbation.transported_shifted_action
      (S a s t) (S a t s) (connection ε hε h hne hh m g k a s t) (S' a s t)
      hi hc c a (w:V) (L s w))

theorem transported_mass_equation (a s t : ℝ) (ha : 0 < a) (w : (L s).domain) :
    M (S a s t (fixedGenerator ε hε h hne hh m g k a s t w)+S' a s t w) =
      c • Q t (S a s t w) := by
  have hg := transport_lifted_graph ε hε h hne hh m g k a s t ha (w:V) (L s w)
    ((L s).mem_graph w)
  exact (congrArg M (transported_action ε hε h hne hh m g k a s t ha w)).trans
    ((map_smul M c _).trans (congrArg (fun v : V => c • v)
      ((lifted_graph_iff ε hε h hne hh m g k t _ _).mp hg).symm))

theorem coefficient_derivatives_continuous (a s : ℝ) (ha : 0 < a) :
    Continuous (fun t => c • (P a s*D t)) ∧
    Continuous (fun t => c • (a • (P a s*D t))+
      connectionDerivative ε hε h hne hh m g k a s t) := by
  have hp := referenceInverse_continuous ε hε h hne hh m g k a ha
  have hd := referenceForm_derivative_continuous ε hε h hne hh m g k
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hsd : Continuous (S' a s) := ((hp.mul hd).mul hs).neg
  have hcd : Continuous (connectionDerivative ε hε h hne hh m g k a s) :=
    ((continuous_const.mul (hd.const_smul (2:ℝ))).mul hs).add
      ((continuous_const.mul hd).mul hsd)
  exact ⟨(continuous_const.mul hd).const_smul c,
    (((continuous_const.mul hd).const_smul a).const_smul c).add hcd⟩

theorem fixed_action_derivative (a s t : ℝ) (ha : 0 < a) (w : (L s).domain) :
    HasDerivAt (fun r => fixedGenerator ε hε h hne hh m g k a s r w)
      ((c • (P a s*D t)) (L s w)+
       (c • (a • (P a s*D t))+connectionDerivative ε hε h hne hh m g k a s t) w) t := by
  have h₁ := KFCausalHilbertStateEvolution.operator_apply_derivative
    (principal ε hε h hne hh m g k a s) (fun _ : ℝ => L s w)
    (c • (P a s*D t)) 0 t (principal_derivative ε hε h hne hh m g k a s t)
    (hasDerivAt_const t (L s w))
  have h₂ := KFCausalHilbertStateEvolution.operator_apply_derivative
    (correction ε hε h hne hh m g k a s) (fun _ : ℝ => (w:V))
    (c • (a • (P a s*D t))+connectionDerivative ε hε h hne hh m g k a s t) 0 t
    (correction_derivative ε hε h hne hh m g k a s t ha) (hasDerivAt_const t (w:V))
  simpa only [map_zero,add_zero] using h₁.add h₂

#print axioms fixed_domain
#print axioms fixed_dense
#print axioms fixed_closed
#print axioms fixed_action
#print axioms connection_derivative
#print axioms principal_derivative
#print axioms correction_derivative
#print axioms connection_cancels
#print axioms transported_action
#print axioms transported_mass_equation
#print axioms coefficient_derivatives_continuous
#print axioms fixed_action_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
