/- The existing coherent energy states have both actual shear/vacuum
compositions, with equal outputs. Their exponentially shifted outputs also
lie in the natural weighted shear domain. The all-angle common domain is
Hilbert-dense; no Hamiltonian graph-core or integrated force bound follows. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain
import UnifiedTheory.Audit.KFCausalCoherentShearDomain
import UnifiedTheory.Audit.KFCausalClockFloorShearVacuumGraph
import UnifiedTheory.Audit.KFCausalClockFloorWeightedShearDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalCoherentShearCompositions
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition composition_graph composition_domain)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalCoherentShearDomain (shearOutput state_shear_graph state_shear_domain)
open UnifiedTheory.Audit.KFCausalClockFloorWeightedShearDomain (weightedMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hbound : |h| ≤ 2*Real.pi*ε/3)
local notation "J" => shearMomentum h
local notation "T" => orderedExponential ε hε h
local notation "M" => weightedMomentum ε hε h hbound hh

def shiftedShearOutput (k : Joint 2 4) : Hilbert := amplitudeConstant h k •
  KFCausalShiftedGaussianShearDomain.shearOutput ε a (groundWidth h) (neutralWidth h)
    (clockFrequency k) (-h/2) (sourceCoefficients h k) hε ha
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (shift_bound ε h hbound) h

theorem shiftedOutput_shear_graph (k : Joint 2 4) :
    (shiftedOutput ε a h hε ha hh hbound k,shiftedShearOutput ε a h hε ha hh hbound k) ∈ (J).graph :=
  (J).graph.smul_mem (amplitudeConstant h k)
    (KFCausalShiftedGaussianShearDomain.gaussianState_shear_graph ε a (groundWidth h) (neutralWidth h)
      (clockFrequency k) (-h/2) (sourceCoefficients h k) hε ha
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (shift_bound ε h hbound) h hh)

theorem shiftedOutput_shear_domain (k : Joint 2 4) :
    shiftedOutput ε a h hε ha hh hbound k ∈ (J).domain :=
  LinearPMap.mem_domain_of_mem_graph (shiftedOutput_shear_graph ε a h hε ha hh hbound k)

theorem shearOutput_ordered_graph (k : Joint 2 4) :
    (shearOutput ε a h hε ha hh k,shiftedShearOutput ε a h hε ha hh hbound k) ∈ (T).graph :=
  (KFCausalClockFloorShearVacuumGraph.ordered_graph_interchange ε hε h hh _ _ _ _
    (state_ordered_graph ε a h hε ha hh hbound k) (state_shear_graph ε a h hε ha hh k)).mpr
      (shiftedOutput_shear_graph ε a h hε ha hh hbound k)

theorem state_composition_graphs (k : Joint 2 4) :
    (state ε a h hε ha hh k,shiftedShearOutput ε a h hε ha hh hbound k) ∈ (composition (J) (T)).graph ∧
    (state ε a h hε ha hh k,shiftedShearOutput ε a h hε ha hh hbound k) ∈ (composition (T) (J)).graph :=
  ⟨(composition_graph _ _ _ _).mpr ⟨_,state_ordered_graph ε a h hε ha hh hbound k,
    shiftedOutput_shear_graph ε a h hε ha hh hbound k⟩,
   (composition_graph _ _ _ _).mpr ⟨_,state_shear_graph ε a h hε ha hh k,
    shearOutput_ordered_graph ε a h hε ha hh hbound k⟩⟩

theorem action_state_composition_graphs (θ : ℝ) (k : Joint 2 4) :
    (action h hh θ (state ε a h hε ha hh k),shiftedShearOutput ε a h hε ha hh hbound
      (KFCausalChargeModulationFlow.parameter θ k)) ∈ (composition (J) (T)).graph ∧
    (action h hh θ (state ε a h hε ha hh k),shiftedShearOutput ε a h hε ha hh hbound
      (KFCausalChargeModulationFlow.parameter θ k)) ∈ (composition (T) (J)).graph := by
  rw [action_state]
  exact state_composition_graphs ε a h hε ha hh hbound _

theorem shiftedOutput_weighted_domain (k : Joint 2 4) :
    shiftedOutput ε a h hε ha hh hbound k ∈ (M).domain :=
  KFCausalClockFloorWeightedShearDomain.shear_domain_included ε hε h hbound hh _
    (shiftedOutput_shear_domain ε a h hε ha hh hbound k)

theorem state_weighted_composition_domain (k : Joint 2 4) :
    state ε a h hε ha hh k ∈ (composition (M) (T)).domain :=
  (composition_domain _ _ _).mpr ⟨_,state_ordered_graph ε a h hε ha hh hbound k,
    shiftedOutput_weighted_domain ε a h hε ha hh hbound k⟩

def compositionDomains : Submodule ℂ Hilbert :=
  (J).domain ⊓ ((composition (J) (T)).domain ⊓
    ((composition (T) (J)).domain ⊓ (composition (M) (T)).domain))

theorem coherentSpan_le_compositionDomains :
    coherentSpan ε a h hε ha hh ≤ compositionDomains ε h hε hh hbound := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  have hg := state_composition_graphs ε a h hε ha hh hbound k
  exact ⟨state_shear_domain ε a h hε ha hh k,
    LinearPMap.mem_domain_of_mem_graph hg.1,LinearPMap.mem_domain_of_mem_graph hg.2,
    state_weighted_composition_domain ε a h hε ha hh hbound k⟩

include ha in
theorem all_angle_energy_compositions_dense (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    Dense {f : Hilbert | ∀ θ : ℝ, action h hh θ f ∈ commonEnergyDomain ε hε h v l ∧
      action h hh θ f ∈ compositionDomains ε h hε hh hbound} := by
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε a h hε ha hh)
  apply hd.mono
  intro f hf θ
  have hr := action_coherentSpan ε a h hε ha hh θ f hf
  exact ⟨coherentSpan_le_commonEnergyDomain ε a h hε ha hh hbound v l hr,
    coherentSpan_le_compositionDomains ε a h hε ha hh hbound hr⟩

#print axioms shiftedOutput_shear_graph
#print axioms shiftedOutput_shear_domain
#print axioms shearOutput_ordered_graph
#print axioms state_composition_graphs
#print axioms action_state_composition_graphs
#print axioms shiftedOutput_weighted_domain
#print axioms state_weighted_composition_domain
#print axioms coherentSpan_le_compositionDomains
#print axioms all_angle_energy_compositions_dense
end
end UnifiedTheory.Audit.KFCausalCoherentShearCompositions
