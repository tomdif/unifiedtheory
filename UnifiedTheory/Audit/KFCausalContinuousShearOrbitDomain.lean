/- Finite superpositions of coherent states have continuous actual T and
JT output orbits. This is a linear domain statement, retaining all
interference terms; no Hamiltonian-domain invariance is assumed. -/
import UnifiedTheory.Audit.KFCausalCoherentShearOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalContinuousShearOrbitDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput shiftedOutput_shear_graph)
open UnifiedTheory.Audit.KFCausalCoherentShearOrbit (shiftedShearOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit
  (shiftedOutput_orbit_continuous shiftedOutput_action_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
local notation "J" => shearMomentum h
local notation "T" => orderedExponential ε hε h

def orbitDomain : Submodule ℂ Hilbert where
  carrier := {f | ∃ g j : ℝ → Hilbert, Continuous g ∧ Continuous j ∧ ∀ θ,
    (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph}
  zero_mem' := by
    refine ⟨fun _ => 0,fun _ => 0,continuous_const,continuous_const,?_⟩
    intro θ
    rw [map_zero]
    exact ⟨(T).graph.zero_mem,(J).graph.zero_mem⟩
  add_mem' := by
    rintro f k ⟨g,j,hg,hj,hf⟩ ⟨u,v,hu,hv,hk⟩
    refine ⟨fun θ => g θ+u θ,fun θ => j θ+v θ,hg.add hu,hj.add hv,?_⟩
    intro θ
    rw [map_add]
    exact ⟨(T).graph.add_mem (hf θ).1 (hk θ).1,(J).graph.add_mem (hf θ).2 (hk θ).2⟩
  smul_mem' := by
    rintro c f ⟨g,j,hg,hj,hf⟩
    refine ⟨fun θ => c • g θ,fun θ => c • j θ,hg.const_smul c,hj.const_smul c,?_⟩
    intro θ
    rw [map_smul]
    exact ⟨(T).graph.smul_mem c (hf θ).1,(J).graph.smul_mem c (hf θ).2⟩

theorem orbit_outputs_unique (f : Hilbert) (g j u v : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph)
    (hu : ∀ θ, (action h hh (2*Real.pi*θ) f,u θ) ∈ (T).graph ∧ (u θ,v θ) ∈ (J).graph) :
    g=u ∧ j=v := by
  have he (θ : ℝ) : g θ=u θ := (T).mem_graph_snd_inj (hg θ).1 (hu θ).1 rfl
  exact ⟨funext he,funext (fun θ => (J).mem_graph_snd_inj (hg θ).2 (hu θ).2 (he θ))⟩

theorem state_mem_orbitDomain (a : ℝ) (ha : 0 < a) (hbound : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    state ε a h hε ha hh k ∈ orbitDomain ε h hε hh := by
  refine ⟨fun θ => shiftedOutput ε a h hε ha hh hbound (parameter (2*Real.pi*θ) k),
    fun θ => shiftedShearOutput ε a h hε ha hh hbound (parameter (2*Real.pi*θ) k),
    (shiftedOutput_orbit_continuous ε a h hε ha hh hbound k).comp (continuous_const.mul continuous_id),
    (shiftedShearOutput_orbit_continuous ε a h hε ha hh hbound k).comp (continuous_const.mul continuous_id),?_⟩
  intro θ
  exact ⟨shiftedOutput_action_graph ε a h hε ha hh hbound (2*Real.pi*θ) k,
    shiftedOutput_shear_graph ε a h hε ha hh hbound _⟩

theorem coherentSpan_le_orbitDomain (a : ℝ) (ha : 0 < a) (hbound : |h| ≤ 2*Real.pi*ε/3) :
    coherentSpan ε a h hε ha hh ≤ orbitDomain ε h hε hh := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact state_mem_orbitDomain ε h hε hh a ha hbound k

theorem orbitDomain_dense (a : ℝ) (ha : 0 < a) (hbound : |h| ≤ 2*Real.pi*ε/3) :
    Dense (orbitDomain ε h hε hh : Set Hilbert) :=
  (Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε a h hε ha hh)).mono
    (coherentSpan_le_orbitDomain ε h hε hh a ha hbound)

theorem energy_orbitDomain_dense (a : ℝ) (ha : 0 < a) (hbound : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    Dense {f : Hilbert | f ∈ orbitDomain ε h hε hh ∧
      ∀ θ, action h hh θ f ∈ commonEnergyDomain ε hε h v l} := by
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε a h hε ha hh)).mono
  intro f hf
  exact ⟨coherentSpan_le_orbitDomain ε h hε hh a ha hbound hf,fun θ =>
    coherentSpan_le_commonEnergyDomain ε a h hε ha hh hbound v l
      (action_coherentSpan ε a h hε ha hh θ f hf)⟩

#print axioms orbit_outputs_unique
#print axioms state_mem_orbitDomain
#print axioms coherentSpan_le_orbitDomain
#print axioms orbitDomain_dense
#print axioms energy_orbitDomain_dense
end
end UnifiedTheory.Audit.KFCausalContinuousShearOrbitDomain
