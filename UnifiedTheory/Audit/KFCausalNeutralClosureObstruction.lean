/- The proved neutral response class is not dense in the actual zero-charge
sector, even in Hilbert norm. Some actual projected coherent packet and
its momentum have full completed-form lifts outside that class. This
is a density obstruction, not a proof of evolution out of the class. -/
import UnifiedTheory.Audit.KFCausalNeutralSwapConstraint
import UnifiedTheory.Audit.KFCausalChargeZeroSwapWitness
import UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection
import UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralClosureObstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargedPlaneSwap
open UnifiedTheory.Audit.KFCausalChargeZeroSwapWitness
open UnifiedTheory.Audit.KFCausalNeutralSwapConstraint
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector zeroProjection zeroProjection_mem)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

include ε a hε ha in
theorem zeroSector_not_subset_fixed : ¬ (zeroSector h hh ≤ fixedSpace) := by
  intro hs
  exact witness_not_fixed ε a h hε ha hh (hs (witness_zeroSector ε a h hε ha hh))

include a ha in
theorem exists_zeroSector_outside_neutralClosure :
    ∃ f : Hilbert, f ∈ zeroSector h hh ∧ f ∉ closure (neutralStates ε h hε hh) :=
  ⟨witness ε a h hε ha hh,witness_zeroSector ε a h hε ha hh,
    fun hf => witness_not_fixed ε a h hε ha hh (closure_subset_fixed ε h hε hh hf)⟩

theorem exists_projected_outside_fixed :
    ∃ k : Joint 2 4, projectedState ε a h hε ha hh k ∉ fixedSpace := by
  by_contra hn
  push_neg at hn
  have hs : Submodule.span ℂ (Set.range (projectedState ε a h hε ha hh)) ≤ fixedSpace := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact hn k
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_projected_span,(fixedSpace_closed).submodule_topologicalClosure_eq] at hc
  exact zeroSector_not_subset_fixed ε a h hε ha hh hc

variable (hb : |h| ≤ 2*Real.pi*ε/3)

include ha in
theorem projected_completed_momentum_pair (k : Joint 2 4) (m g v t : ℝ) :
    ∃ u w : FormSpace ε hε h hh hb m g v t,
      embedding ε hε h hh hb m g v t u = projectedState ε a h hε ha hh k ∧
      (embedding ε hε h hh hb m g v t u,embedding ε hε h hh hb m g v t w) ∈
        (pureMomentum ε hε h).graph ∧
      embedding ε hε h hh hb m g v t w ∈ zeroSector h hh := by
  let f := KFCausalClockFloorCoherentStates.state ε a h hε ha hh k
  have hf : f ∈ KFCausalClockFloorCoherentCommonDomain.coherentSpan ε a h hε ha hh :=
    Submodule.subset_span ⟨k,rfl⟩
  obtain ⟨b,u,w,hB,hu,hw⟩ :=
    KFCausalCoherentMomentumEnergyLift.coherent_momentum_lifts ε h hε hh hb m g v t a ha f hf
  let hp := KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb
  have hfu := (KFCausalClockFloorAveragedEnergy.energy_domain ε hε h hp hh m g v t f).mpr ⟨u,hu⟩
  have hbw := (KFCausalClockFloorAveragedEnergy.energy_domain ε hε h hp hh m g v t b).mpr ⟨w,hw⟩
  obtain ⟨u',hu'⟩ := (KFCausalClockFloorAveragedEnergy.energy_domain ε hε h hp hh m g v t _).mp
    (KFCausalClockFloorAveragedEnergy.zeroProjection_mem_energy_domain ε hε h hp hh m g v t f hfu)
  obtain ⟨w',hw'⟩ := (KFCausalClockFloorAveragedEnergy.energy_domain ε hε h hp hh m g v t _).mp
    (KFCausalClockFloorAveragedEnergy.zeroProjection_mem_energy_domain ε hε h hp hh m g v t b hbw)
  let up := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g v t u'
  let wp := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g v t w'
  have hup : embedding ε hε h hh hb m g v t up = zeroProjection h hh f :=
    (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb m g v t u').trans hu'
  have hwp : embedding ε hε h hh hb m g v t wp = zeroProjection h hh b :=
    (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb m g v t w').trans hw'
  refine ⟨up,wp,hup,?_,?_⟩
  · rw [hup,hwp]
    exact KFCausalPureClockZeroProjection.projected_graph ε hε h hh f b hB
  · rw [hwp]
    exact zeroProjection_mem h hh b

theorem exists_regular_pair_outside_neutralClosure :
    ∃ k : Joint 2 4, projectedState ε a h hε ha hh k ∉ closure (neutralStates ε h hε hh) ∧
      ∀ t : ℝ, ∃ u w : FormSpace ε hε h hh hb 1 1 1 t,
        embedding ε hε h hh hb 1 1 1 t u = projectedState ε a h hε ha hh k ∧
        (embedding ε hε h hh hb 1 1 1 t u,embedding ε hε h hh hb 1 1 1 t w) ∈
          (pureMomentum ε hε h).graph ∧
        (u,w) ∉ KFCausalNeutralResponseGraphClosure.completedPairs ε h hε hh hb t := by
  obtain ⟨k,hk⟩ := exists_projected_outside_fixed ε a h hε ha hh
  refine ⟨k,fun hf => hk (closure_subset_fixed ε h hε hh hf),?_⟩
  intro t
  obtain ⟨u,w,hu,hB,_⟩ := projected_completed_momentum_pair ε a h hε ha hh hb k 1 1 1 t
  refine ⟨u,w,hu,hB,?_⟩
  intro hz
  have hf := completedPairs_input_fixed ε h hε hh hb t (u,w) hz
  rw [hu] at hf
  exact hk hf

#print axioms zeroSector_not_subset_fixed
#print axioms exists_zeroSector_outside_neutralClosure
#print axioms exists_projected_outside_fixed
#print axioms projected_completed_momentum_pair
#print axioms exists_regular_pair_outside_neutralClosure
end
end UnifiedTheory.Audit.KFCausalNeutralClosureObstruction
