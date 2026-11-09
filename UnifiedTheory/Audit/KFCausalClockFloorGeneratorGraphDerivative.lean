/- The time derivative of the full generator, after a fixed resolvent,
is bounded. Its derived factorization supplies the graph-transport correction. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
import UnifiedTheory.Audit.KFCausalCommonDomainResolvent
import UnifiedTheory.Audit.KFCausalPartialResolventCommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
open UnifiedTheory.Audit.KFCausalComplexMassPencil (phase)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "T" => liftedHamiltonian ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "R'" => fullDerivative ε hε h hne hh m g k
local notation "A" => principal ε hε h hne hh m g k
local notation "B" => correction ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "C'" => connectionDerivative ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

def principalInverse (a s t : ℝ) : V →L[ℂ] V := (phase h)⁻¹ • S a s t
def principalDerivative (a s t : ℝ) : V →L[ℂ] V := phase h • (P a s*D t)
def correctionDerivative (a s t : ℝ) : V →L[ℂ] V := phase h • (a • (P a s*D t))+C' a s t
def referenceOutput (a lam s t : ℝ) : V →L[ℂ] V :=
  principalInverse ε hε h hne hh m g k a s t*((lam • R a lam s t-1)-B a s t*R a lam s t)
def graphCorrection (a lam s t : ℝ) : V →L[ℂ] V :=
  principalDerivative ε hε h hne hh m g k a s t*referenceOutput ε hε h hne hh m g k a lam s t+
    correctionDerivative ε hε h hne hh m g k a s t*R a lam s t

theorem principal_inverse_left (a s t : ℝ) (ha : 0 < a) (x : V) :
    principalInverse ε hε h hne hh m g k a s t (A a s t x) = x := by
  simp only [principalInverse,KFCausalClockFloorFixedFormGenerator.principal,ContinuousLinearMap.smul_apply,map_smul,
    transport_inverse ε hε h hne hh m g k a s t ha,smul_smul]
  change (phase h*(phase h)⁻¹) • x = x
  rw [mul_inv_cancel₀ (KFCausalComplexMassPencil.phase_ne_zero h hne),one_smul]

theorem principal_inverse_right (a s t : ℝ) (ha : 0 < a) (x : V) :
    A a s t (principalInverse ε hε h hne hh m g k a s t x) = x := by
  simp only [principalInverse,KFCausalClockFloorFixedFormGenerator.principal,ContinuousLinearMap.smul_apply,map_smul,
    transport_inverse ε hε h hne hh m g k a t s ha,smul_smul]
  change ((phase h)⁻¹*phase h) • x = x
  rw [inv_mul_cancel₀ (KFCausalComplexMassPencil.phase_ne_zero h hne),one_smul]

theorem reference_output_graph (a lam s t : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hq : q a s t < lam) (f : V) :
    (R a lam s t f,referenceOutput ε hε h hne hh m g k a lam s t f) ∈ (T s).graph :=
  KFCausalCommonDomainResolvent.graph_output (T s) (A a s t) (B a s t)
    (principalInverse ε hε h hne hh m g k a s t) (R a lam s t)
    (referenceOutput ε hε h hne hh m g k a lam s t) lam
    (principal_inverse_left ε hε h hne hh m g k a s t ha)
    (principal_inverse_right ε hε h hne hh m g k a s t ha) rfl
    (full_resolvent_graph ε hε h hne hh m g k a lam s t ha hlam hq) f

theorem reference_resolvent_left (a lam s t : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hq : q a s t < lam) (x y : V) (hxy : (x,y) ∈ (T s).graph) :
    R a lam s t (lam • x-(A a s t y+B a s t x)) = x :=
  KFCausalCommonDomainResolvent.reference_left (T s) (A a s t) (B a s t) (R a lam s t) lam
    (full_resolvent_left ε hε h hne hh m g k a lam s t ha hlam hq) x y hxy

theorem full_resolvent_difference (a lam s t u : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (ht : q a s t < lam) (hu : q a s u < lam) :
    R a lam s t-R a lam s u = R a lam s t*
      ((A a s t-A a s u)*referenceOutput ε hε h hne hh m g k a lam s u+
       (B a s t-B a s u)*R a lam s u) :=
  KFCausalCommonDomainResolvent.resolvent_difference (T s) (A a s t) (B a s t)
    (A a s u) (B a s u) (R a lam s t) (R a lam s u)
    (referenceOutput ε hε h hne hh m g k a lam s u) lam
    (reference_resolvent_left ε hε h hne hh m g k a lam s t ha hlam ht)
    (reference_output_graph ε hε h hne hh m g k a lam s u ha hlam hu)
    (full_resolvent_graph ε hε h hne hh m g k a lam s u ha hlam hu)

theorem full_derivative_factorization (a lam s t : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (ht : q a s t < lam) : R' a lam s t = R a lam s t*graphCorrection ε hε h hne hh m g k a lam s t := by
  apply KFCausalCommonDomainResolvent.derivative_factorization (R a lam s) (A a s) (B a s)
    (referenceOutput ε hε h hne hh m g k a lam s t) (R' a lam s t)
    (principalDerivative ε hε h hne hh m g k a s t)
    (correctionDerivative ε hε h hne hh m g k a s t) t
    (full_resolvent_derivative ε hε h hne hh m g k a lam s t ha hlam ht)
    (principal_derivative ε hε h hne hh m g k a s t)
    (correction_derivative ε hε h hne hh m g k a s t ha)
  filter_upwards [(admissible_open ε hε h hne hh m g k a lam s ha).mem_nhds ht] with u hu
  exact full_resolvent_difference ε hε h hne hh m g k a lam s u t ha hlam hu ht

theorem resolvent_factored_derivative (a lam s t : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (ht : q a s t < lam) :
    HasDerivAt (R a lam s) (R a lam s t*graphCorrection ε hε h hne hh m g k a lam s t) t :=
  KFCausalCommonDomainResolvent.factored_derivative (R a lam s) (R' a lam s t)
    (graphCorrection ε hε h hne hh m g k a lam s t) t
    (full_resolvent_derivative ε hε h hne hh m g k a lam s t ha hlam ht)
    (full_derivative_factorization ε hε h hne hh m g k a lam s t ha hlam ht)

theorem graph_correction_continuousOn (a lam s : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ContinuousOn (graphCorrection ε hε h hne hh m g k a lam s) {t | q a s t < lam} := by
  have hr : ContinuousOn (R a lam s) {t | q a s t < lam} := fun t ht =>
    (full_resolvent_derivative ε hε h hne hh m g k a lam s t ha hlam ht).continuousAt.continuousWithinAt
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hb : Continuous (B a s) := continuous_iff_continuousAt.mpr
    (fun t => (correction_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hd := coefficient_derivatives_continuous ε hε h hne hh m g k a s ha
  have hout : ContinuousOn (referenceOutput ε hε h hne hh m g k a lam s) {t | q a s t < lam} :=
    (hs.const_smul (phase h)⁻¹).continuousOn.mul
    (((hr.const_smul lam).sub continuousOn_const).sub (hb.continuousOn.mul hr))
  exact (hd.1.continuousOn.mul hout).add (hd.2.continuousOn.mul hr)

theorem full_resolvents_commute (a lam b s t : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hb : 0 < b)
    (hlq : q a s t < lam) (hbq : q a s t < b) : R a lam s t*R a b s t = R a b s t*R a lam s t :=
  KFCausalPartialResolventCommutation.resolvents_commute (G a s t) (R a lam s t) (R a b s t) lam b
    (full_resolvent_left ε hε h hne hh m g k a lam s t ha hlam hlq)
    (full_resolvent_graph ε hε h hne hh m g k a lam s t ha hlam hlq)
    (full_resolvent_left ε hε h hne hh m g k a b s t ha hb hbq)
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hbq)

theorem resolvent_approximation_commutes (a lam b s t : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hb : 0 < b)
    (hlq : q a s t < lam) (hbq : q a s t < b) :
    R a lam s t*fullApproximation ε hε h hne hh m g k a b s t =
      fullApproximation ε hε h hne hh m g k a b s t*R a lam s t :=
  KFCausalPartialResolventCommutation.regularization_commutes (R a lam s t) (R a b s t)
    (fullApproximation ε hε h hne hh m g k a b s t) b
    (full_resolvents_commute ε hε h hne hh m g k a lam b s t ha hlam hb hlq hbq) rfl

#print axioms principal_inverse_left
#print axioms principal_inverse_right
#print axioms reference_output_graph
#print axioms reference_resolvent_left
#print axioms full_resolvent_difference
#print axioms full_derivative_factorization
#print axioms resolvent_factored_derivative
#print axioms graph_correction_continuousOn
#print axioms full_resolvents_commute
#print axioms resolvent_approximation_commutes
end
end UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
