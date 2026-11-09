/- All eight actual energy-factor outputs of coherent-span momentum,
with continuous square-integrable charge orbits. No Hamiltonian evolution
or form-core invariance is inferred from this common domain. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumMatterOrbit
import UnifiedTheory.Audit.KFCausalCoherentMomentumFactorL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumFullOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalCoherentMomentumFactorOrbit
open UnifiedTheory.Audit.KFCausalCoherentMomentumMatterOrbit
open UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit
  (orderedMomentumOutput orderedMomentumOutput_graph orderedMomentumOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)

def factorOutput (k : Joint 2 4) : Fin 8 → Hilbert :=
  ![clockMomentumOutput ε a h hε ha hh k,
    kineticMomentumOutput ε a h hε ha hh k (v 0),kineticMomentumOutput ε a h hε ha hh k (v 1),
    kineticMomentumOutput ε a h hε ha hh k (v 2),kineticMomentumOutput ε a h hε ha hh k (v 3),
    linearMomentumOutput ε a h hε ha hh hb k l,quadraticMomentumOutput ε a h hε ha hh hb k l,
    orderedMomentumOutput ε a h hε ha hh hb k]

theorem factorOutput_graph (k : Joint 2 4) (i : Fin 8) :
    (pureOutput ε a h hε ha hh k,factorOutput ε a h hε ha hh hb v l k i) ∈
      (energyFactor ε hε h v l i).graph := by
  fin_cases i
  · exact clockMomentumOutput_graph ε a h hε ha hh k
  · exact kineticMomentumOutput_graph ε a h hε ha hh k (v 0)
  · exact kineticMomentumOutput_graph ε a h hε ha hh k (v 1)
  · exact kineticMomentumOutput_graph ε a h hε ha hh k (v 2)
  · exact kineticMomentumOutput_graph ε a h hε ha hh k (v 3)
  · exact linearMomentumOutput_matter_graph ε a h hε ha hh hb k l _ (pureOutput_graph ε a h hε ha hh k)
  · exact quadraticMomentumOutput_matter_graph ε a h hε ha hh hb k l _ (pureOutput_graph ε a h hε ha hh k)
  · exact orderedMomentumOutput_graph ε a h hε ha hh hb k _ (pureOutput_graph ε a h hε ha hh k)

theorem factorOutput_orbit_continuous (k : Joint 2 4) (i : Fin 8) :
    Continuous (fun θ => factorOutput ε a h hε ha hh hb v l (parameter θ k) i) := by
  fin_cases i
  · exact clockMomentumOutput_orbit_continuous ε a h hε ha hh k
  · exact kineticMomentumOutput_orbit_continuous ε a h hε ha hh k (v 0)
  · exact kineticMomentumOutput_orbit_continuous ε a h hε ha hh k (v 1)
  · exact kineticMomentumOutput_orbit_continuous ε a h hε ha hh k (v 2)
  · exact kineticMomentumOutput_orbit_continuous ε a h hε ha hh k (v 3)
  · exact linearMomentumOutput_orbit_continuous ε a h hε ha hh hb k l
  · exact quadraticMomentumOutput_orbit_continuous ε a h hε ha hh hb k l
  · exact orderedMomentumOutput_orbit_continuous ε a h hε ha hh hb k

theorem factorOutput_action_graph (θ : ℝ) (k : Joint 2 4) (i : Fin 8) :
    (action h hh θ (pureOutput ε a h hε ha hh k),factorOutput ε a h hε ha hh hb v l (parameter θ k) i) ∈
      (energyFactor ε hε h v l i).graph := by
  rw [← pureOutput_action]
  exact factorOutput_graph ε a h hε ha hh hb v l _ i

include hb in
theorem actual_outputs (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph) :
    ∃ g : Fin 8 → ℝ → Hilbert, (∀ i, Continuous (g i)) ∧ (∀ i, MemLp (g i) 2 angleMeasure) ∧
      ∀ θ i, (action h hh (2*Real.pi*θ) b,g i θ) ∈ (energyFactor ε hε h v l i).graph := by
  obtain ⟨n,q,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hs : (∑ j, z j • state ε a h hε ha hh (q j),
      ∑ j, z j • pureOutput ε a h hε ha hh (q j)) ∈ (pureMomentum ε hε h).graph := by
    have hs := (pureMomentum ε hε h).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      (pureMomentum ε hε h).graph.smul_mem (z j) (pureOutput_graph ε a h hε ha hh (q j)))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have eb : b = ∑ j, z j • pureOutput ε a h hε ha hh (q j) :=
    (pureMomentum ε hε h).mem_graph_snd_inj' hB hs rfl
  let g : Fin 8 → ℝ → Hilbert := fun i θ =>
    ∑ j, z j • factorOutput ε a h hε ha hh hb v l (parameter (2*Real.pi*θ) (q j)) i
  have hc (i : Fin 8) : Continuous (g i) := continuous_finset_sum Finset.univ (fun j _ =>
    ((factorOutput_orbit_continuous ε a h hε ha hh hb v l (q j) i).comp
      (continuous_const.mul continuous_id)).const_smul (z j))
  refine ⟨g,hc,fun i => continuous_angle_memLp _ (hc i),?_⟩
  intro θ i
  rw [eb,map_sum]
  simp only [map_smul]
  have hs := (energyFactor ε hε h v l i).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    (energyFactor ε hε h v l i).graph.smul_mem (z j)
      (factorOutput_action_graph ε a h hε ha hh hb v l (2*Real.pi*θ) (q j) i))
  simpa only [g,Prod.smul_mk,← prod_mk_sum] using hs

include hb in
theorem actual_common_domains (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph) (θ : ℝ) :
    action h hh (2*Real.pi*θ) b ∈ commonEnergyDomain ε hε h v l := by
  obtain ⟨g,_,_,hg⟩ := actual_outputs ε a h hε ha hh hb v l f hf b hB
  exact (commonEnergyDomain_iff ε hε h v l _).mpr
    (fun i => LinearPMap.mem_domain_of_mem_graph (hg θ i))

#print axioms factorOutput_graph
#print axioms factorOutput_orbit_continuous
#print axioms factorOutput_action_graph
#print axioms actual_outputs
#print axioms actual_common_domains
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumFullOrbit
