/- A resolvent of the full fixed-domain generator, including its
connection. The large spectral parameter is derived from explicit
bounded-operator norms; no domain preservation by the connection is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
import UnifiedTheory.Audit.KFCausalPartialResolventPerturbation
import UnifiedTheory.Audit.KFCausalConjugatedPartialResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
open UnifiedTheory.Audit.KFCausalComplexMassPencil (phase)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "C" => connection ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "R" => schrodingerResolvent ε hε h hne hh m g k

def baseResolvent (a b s t : ℝ) : V →L[ℂ] V :=
  KFCausalConjugatedPartialResolvent.conjugated (S a s t) (S a t s) (R b t)

def baseBound (a s t : ℝ) : ℝ :=
  ‖S a t s‖*Real.sqrt (‖F a t‖/KFCausalShiftedForm.lowerConstant a t)*‖S a s t‖

def connectionThreshold (a s t : ℝ) : ℝ := ‖C a s t‖*baseBound ε hε h hne hh m g k a s t

def fullResolvent (a b s t : ℝ) : V →L[ℂ] V :=
  KFCausalPartialResolventPerturbation.resolvent (baseResolvent ε hε h hne hh m g k a b s t) (C a s t)

theorem conjugated_action (a s t : ℝ) (ha : 0 < a) (w : (G a s t).domain) :
    ∃ z, (S a s t w,z) ∈ (L t).graph ∧ S a s t (G a s t w-C a s t w) = phase h • z := by
  refine ⟨L s w+a • (w:V)-a • S a s t w,
    transport_lifted_graph ε hε h hne hh m g k a s t ha (w:V) (L s w) ((L s).mem_graph w),?_⟩
  exact KFCausalConjugatedPartialResolvent.action_from_transport (S a s t) (C a s t)
    (transportDerivative ε hε h hne hh m g k a s t) (phase h) (w:V) (G a s t w) _
    (connection_cancels_apply ε hε h hne hh m g k a s t ha (w:V))
    (transported_action ε hε h hne hh m g k a s t ha w)

theorem base_resolvent_graph (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b) (f : V) :
    (baseResolvent ε hε h hne hh m g k a b s t f,
      b • baseResolvent ε hε h hne hh m g k a b s t f-f+
        C a s t (baseResolvent ε hε h hne hh m g k a b s t f)) ∈ (G a s t).graph := by
  apply KFCausalConjugatedPartialResolvent.conjugated_resolvent_graph (L t) (G a s t)
    (S a s t) (S a t s) (C a s t) (R b t) (phase h) b
    (resolvedOutput ε hε h hne hh m g k b t)
    (transport_inverse ε hε h hne hh m g k a s t ha)
    (transport_inverse ε hε h hne hh m g k a t s ha)
  · exact KFCausalConjugatedPartialResolvent.conjugated_graph (L t) (G a s t)
      (S a s t) (S a t s) (C a s t) (phase h)
      (transport_inverse ε hε h hne hh m g k a t s ha)
      (transport_lifted_domain_iff ε hε h hne hh m g k a s t ha)
      (conjugated_action ε hε h hne hh m g k a s t ha)
  · exact resolvent_graph ε hε h hne hh m g k b t hb
  · exact resolvent_right ε hε h hne hh m g k b t

theorem base_resolvent_left (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (w v : V) (hw : (w,v) ∈ (G a s t).graph) :
    baseResolvent ε hε h hne hh m g k a b s t (b • w-v+C a s t w) = w :=
  KFCausalConjugatedPartialResolvent.left_graph_of_eq (L t) (G a s t)
    (S a s t) (S a t s) (C a s t) (R b t)
    (baseResolvent ε hε h hne hh m g k a b s t) (phase h) b rfl
    (transport_inverse ε hε h hne hh m g k a t s ha)
    (conjugated_action ε hε h hne hh m g k a s t ha)
    (resolvent_left ε hε h hne hh m g k b t hb) w v hw

theorem base_bound_nonnegative (a s t : ℝ) : 0 ≤ baseBound ε hε h hne hh m g k a s t :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _)

theorem base_resolvent_bound (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b) (f : V) :
    ‖baseResolvent ε hε h hne hh m g k a b s t f‖ ≤ baseBound ε hε h hne hh m g k a s t/b*‖f‖ :=
  KFCausalConjugatedPartialResolvent.conjugated_norm_bound (S a s t) (S a t s) (R b t) b
    (Real.sqrt (‖F a t‖/KFCausalShiftedForm.lowerConstant a t)) hb (Real.sqrt_nonneg _)
    (scaled_norm_bound ε hε h hne hh m g k a b t ha hb) f

theorem connection_factor_isUnit (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbC : connectionThreshold ε hε h hne hh m g k a s t < b) :
    IsUnit (1-C a s t*baseResolvent ε hε h hne hh m g k a b s t) :=
  KFCausalPartialResolventPerturbation.factor_isUnit _ _
    (KFCausalPartialResolventPerturbation.factor_small _ _ b (baseBound ε hε h hne hh m g k a s t)
      hb (base_bound_nonnegative ε hε h hne hh m g k a s t)
      (base_resolvent_bound ε hε h hne hh m g k a b s t ha hb) hbC)

theorem full_resolvent_graph (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbC : connectionThreshold ε hε h hne hh m g k a s t < b) (f : V) :
    (fullResolvent ε hε h hne hh m g k a b s t f,
      b • fullResolvent ε hε h hne hh m g k a b s t f-f) ∈ (G a s t).graph :=
  KFCausalPartialResolventPerturbation.graph_of_eq (G a s t)
    (baseResolvent ε hε h hne hh m g k a b s t) (C a s t)
    (fullResolvent ε hε h hne hh m g k a b s t) b rfl
    (connection_factor_isUnit ε hε h hne hh m g k a b s t ha hb hbC)
    (base_resolvent_graph ε hε h hne hh m g k a b s t ha hb) f

theorem full_resolvent_left (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbC : connectionThreshold ε hε h hne hh m g k a s t < b)
    (w v : V) (hw : (w,v) ∈ (G a s t).graph) :
    fullResolvent ε hε h hne hh m g k a b s t (b • w-v) = w :=
  KFCausalPartialResolventPerturbation.left_graph_of_eq (G a s t)
    (baseResolvent ε hε h hne hh m g k a b s t) (C a s t)
    (fullResolvent ε hε h hne hh m g k a b s t) b rfl
    (connection_factor_isUnit ε hε h hne hh m g k a b s t ha hb hbC)
    (base_resolvent_left ε hε h hne hh m g k a b s t ha hb) w v hw

theorem full_resolvent_bound (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbC : connectionThreshold ε hε h hne hh m g k a s t < b) (f : V) :
    ‖fullResolvent ε hε h hne hh m g k a b s t f‖ ≤
      baseBound ε hε h hne hh m g k a s t/(b-connectionThreshold ε hε h hne hh m g k a s t)*‖f‖ :=
  KFCausalPartialResolventPerturbation.norm_bound_of_eq
    (baseResolvent ε hε h hne hh m g k a b s t) (C a s t)
    (fullResolvent ε hε h hne hh m g k a b s t) b
    (baseBound ε hε h hne hh m g k a s t) (connectionThreshold ε hε h hne hh m g k a s t) rfl rfl hb
    (base_bound_nonnegative ε hε h hne hh m g k a s t)
    (base_resolvent_bound ε hε h hne hh m g k a b s t ha hb) hbC f

#print axioms conjugated_action
#print axioms base_resolvent_graph
#print axioms base_resolvent_left
#print axioms base_bound_nonnegative
#print axioms base_resolvent_bound
#print axioms connection_factor_isUnit
#print axioms full_resolvent_graph
#print axioms full_resolvent_left
#print axioms full_resolvent_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
