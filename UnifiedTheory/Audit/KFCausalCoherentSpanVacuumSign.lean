/- Transfer the finite-family vacuum sign to every vector in the actual
coherent span and any actual exponential/shear output representatives.
This is a domain-specific sign, not a Hamiltonian evolution identity. -/
import UnifiedTheory.Audit.KFCausalCoherentVacuumShearSign
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalCoherentSpanVacuumSign
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalAveragedShearPairing (meanShear)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

theorem finite_representation (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (n : ℕ) (k : Fin n → Joint 2 4) (z : Fin n → ℂ), f = ∑ i, z i • state ε a h hε ha hh (k i) := by
  classical
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  let e := Fintype.equivFin c.support
  refine ⟨Fintype.card c.support,fun i => (e.symm i).val,fun i => c (e.symm i).val,?_⟩
  calc
    f = ∑ i ∈ c.support, c i • state ε a h hε ha hh i := hc.symm
    _ = ∑ i : c.support, c i • state ε a h hε ha hh i := by
      exact (Finset.sum_attach c.support (fun i => c i • state ε a h hε ha hh i)).symm
    _ = _ := (e.symm.sum_comp (fun i : c.support => c i • state ε a h hε ha hh i)).symm

theorem meanShear_nonnegative (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph ∧
      (g θ,j θ) ∈ (shearMomentum h).graph) : 0 ≤ meanShear ε h hε hh hb g j := by
  obtain ⟨n,k,z,rfl⟩ := finite_representation ε a h hε ha hh f hf
  exact KFCausalCoherentVacuumShearSign.meanShear_nonnegative_actual_outputs ε a h hε ha hh hb k z g j hg

theorem vacuum_response_nonnegative (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph ∧
      (g θ,j θ) ∈ (shearMomentum h).graph) :
    0 ≤ ∫ θ, KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb (g θ) (j θ) ∂angleMeasure := by
  obtain ⟨n,k,z,rfl⟩ := finite_representation ε a h hε ha hh f hf
  obtain ⟨rfl,rfl⟩ := KFCausalContinuousShearOrbitDomain.orbit_outputs_unique ε h hε hh
    (∑ i, z i • state ε a h hε ha hh (k i))
    (KFCausalCoherentVacuumShearSign.orbitInput ε a h hε ha hh hb k z)
    (KFCausalCoherentVacuumShearSign.orbitShear ε a h hε ha hh hb k z) g j
    (fun θ => ⟨KFCausalCoherentVacuumShearSign.ordered_graph ε a h hε ha hh hb k z θ,
      KFCausalCoherentVacuumShearSign.shear_graph ε a h hε ha hh hb k z θ⟩) hg
  exact KFCausalCoherentVacuumShearSign.vacuum_response_nonnegative ε a h hε ha hh hb k z

theorem vacuum_response_lower_bound (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph ∧
      (g θ,j θ) ∈ (shearMomentum h).graph) :
    (∫ θ, KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (g θ) ∂angleMeasure) ≤
      ∫ θ, KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb (g θ) (j θ) ∂angleMeasure := by
  obtain ⟨n,k,z,rfl⟩ := finite_representation ε a h hε ha hh f hf
  obtain ⟨rfl,rfl⟩ := KFCausalContinuousShearOrbitDomain.orbit_outputs_unique ε h hε hh
    (∑ i, z i • state ε a h hε ha hh (k i))
    (KFCausalCoherentVacuumShearSign.orbitInput ε a h hε ha hh hb k z)
    (KFCausalCoherentVacuumShearSign.orbitShear ε a h hε ha hh hb k z) g j
    (fun θ => ⟨KFCausalCoherentVacuumShearSign.ordered_graph ε a h hε ha hh hb k z θ,
      KFCausalCoherentVacuumShearSign.shear_graph ε a h hε ha hh hb k z θ⟩) hg
  exact KFCausalCoherentVacuumShearSign.vacuum_response_lower_bound ε a h hε ha hh hb k z

theorem exists_nonnegative_actual_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ g j : ℝ → Hilbert, Continuous g ∧ Continuous j ∧
      (∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph ∧
        (g θ,j θ) ∈ (shearMomentum h).graph) ∧
      0 ≤ meanShear ε h hε hh hb g j ∧
      0 ≤ ∫ θ, KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb (g θ) (j θ) ∂angleMeasure := by
  obtain ⟨n,k,z,rfl⟩ := finite_representation ε a h hε ha hh f hf
  refine ⟨KFCausalCoherentVacuumShearSign.orbitInput ε a h hε ha hh hb k z,
    KFCausalCoherentVacuumShearSign.orbitShear ε a h hε ha hh hb k z,
    KFCausalCoherentVacuumShearSign.input_continuous ε a h hε ha hh hb k z,
    KFCausalCoherentVacuumShearSign.shear_continuous ε a h hε ha hh hb k z,
    fun θ => ⟨KFCausalCoherentVacuumShearSign.ordered_graph ε a h hε ha hh hb k z θ,
      KFCausalCoherentVacuumShearSign.shear_graph ε a h hε ha hh hb k z θ⟩,
    KFCausalCoherentVacuumShearSign.meanShear_nonnegative ε a h hε ha hh hb k z,
    KFCausalCoherentVacuumShearSign.vacuum_response_nonnegative ε a h hε ha hh hb k z⟩

#print axioms finite_representation
#print axioms meanShear_nonnegative
#print axioms vacuum_response_nonnegative
#print axioms vacuum_response_lower_bound
#print axioms exists_nonnegative_actual_response
end
end UnifiedTheory.Audit.KFCausalCoherentSpanVacuumSign
