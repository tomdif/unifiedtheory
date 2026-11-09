/- Exact longitudinal-momentum commutator of T=exp(L/2) C^(-1/2).
Both composition domains agree within Dom(L) intersect Dom(T), and the
commutator has a bounded relative output. This is not yet a statement
about charge-averaged Hamiltonian evolution or canonical clock momentum. -/
import UnifiedTheory.Audit.KFCausalClockFloorInverseHalfMomentum
import UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumGraph
import UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain
import UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumGraph
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfMomentum
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "L" => longitudinalMomentum ε hε h
local notation "E" => longitudinalExponential ε hε h (1/2)
local notation "T" => orderedExponential ε hε h
local notation "R" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "Q" => responseOperator ε hε
local notation "Z" => shiftedDefect ε hε h hh
local notation "S" => shiftedResponse ε hε h hh
local notation "c" => Complex.I*(h:ℂ)/(2*(ε:ℂ))

def correction : Hilbert →L[ℂ] Hilbert := c • (Z).comp S

theorem exponential_response_graph (f ef : Hilbert) (he : (f,ef) ∈ (E).graph) :
    (D (Q f),Z (S ef)) ∈ (E).graph := by
  have hd := KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh f ef he
  have hq : (Q f,S ef) ∈ (E).graph := by
    simpa only [responseOperator,shiftedResponse,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply,Prod.sub_def] using (E).graph.sub_mem he hd
  exact KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh _ _ hq

include hne in
theorem ordered_momentum_graph (f lf tf tlf : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (ht : (f,tf) ∈ (T).graph) (htl : (lf,tlf) ∈ (T).graph) :
    (tf,tlf+correction ε hε h hh tf) ∈ (L).graph := by
  have he := (ordered_graph_iff ε hε h f tf).mp ht
  have hel := (ordered_graph_iff ε hε h lf tlf).mp htl
  have hr := inverse_momentum_graph ε hε h hne f lf hl
  apply (graph_interchange ε hε h hne (1/2) (R f) _ tf _ hr he).mp
  exact (E).graph.add_mem hel ((E).graph.smul_mem c (exponential_response_graph ε hε h hh _ _ he))

include hne in
theorem momentum_ordered_graph (f lf tf ltf : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (ht : (f,tf) ∈ (T).graph) (hlt : (tf,ltf) ∈ (L).graph) :
    (lf,ltf-correction ε hε h hh tf) ∈ (T).graph := by
  have he := (ordered_graph_iff ε hε h f tf).mp ht
  have hr := inverse_momentum_graph ε hε h hne f lf hl
  have hel := (graph_interchange ε hε h hne (1/2) (R f) _ tf ltf hr he).mpr hlt
  apply (ordered_graph_iff ε hε h _ _).mpr
  have hz := (E).graph.sub_mem hel ((E).graph.smul_mem c (exponential_response_graph ε hε h hh _ _ he))
  simpa only [Prod.sub_def,Prod.smul_mk,add_sub_cancel_right] using hz

include hne hh in
theorem composition_domain_iff (f lf tf : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (ht : (f,tf) ∈ (T).graph) :
    lf ∈ (T).domain ↔ tf ∈ (L).domain := by
  constructor
  · intro hz
    exact LinearPMap.mem_domain_of_mem_graph
      (ordered_momentum_graph ε hε h hne hh f lf tf _ hl ht ((T).mem_graph ⟨lf,hz⟩))
  · intro hz
    exact LinearPMap.mem_domain_of_mem_graph
      (momentum_ordered_graph ε hε h hne hh f lf tf _ hl ht ((L).mem_graph ⟨tf,hz⟩))

theorem correction_bound (f : Hilbert) : ‖correction ε hε h hh f‖ ≤ (|h|/ε)*‖f‖ := by
  have hb : ‖Z (S f)‖ ≤ 2*‖f‖ :=
    (shiftedDefect_norm_bound ε hε h hh _).trans
      (mul_le_mul_of_nonneg_left ((defectOperator_norm_le ε hε _).trans
        (shiftedResponse_norm ε hε h hh f)) (by norm_num))
  change ‖c • Z (S f)‖ ≤ _
  rw [norm_smul,norm_div,norm_mul,Complex.norm_I,one_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  norm_num only [Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ |h|/(2*ε))).trans_eq (by ring)

include hne in
theorem commutator_graph (f lf tf tlf ltf : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (ht : (f,tf) ∈ (T).graph)
    (htl : (lf,tlf) ∈ (T).graph) (hlt : (tf,ltf) ∈ (L).graph) :
    ltf-tlf = correction ε hε h hh tf ∧ ‖ltf-tlf‖ ≤ (|h|/ε)*‖tf‖ := by
  have he := (L).mem_graph_snd_inj' hlt (ordered_momentum_graph ε hε h hne hh f lf tf tlf hl ht htl) rfl
  change ltf = tlf+correction ε hε h hh tf at he
  rw [he,add_sub_cancel_left]
  exact ⟨rfl,correction_bound ε hε h hh tf⟩

#print axioms exponential_response_graph
#print axioms ordered_momentum_graph
#print axioms momentum_ordered_graph
#print axioms composition_domain_iff
#print axioms correction_bound
#print axioms commutator_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
