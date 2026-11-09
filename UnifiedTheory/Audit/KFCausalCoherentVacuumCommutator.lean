/- The actual coherent span meets the joint regular-graph conditions
of the pure-clock vacuum commutator. Both operator orders and the weak
response identity are constructed on this same family. -/
import UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain
import UnifiedTheory.Audit.KFCausalCoherentSpanVacuumSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalCoherentVacuumCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore (regularGraph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "T" => orderedExponential ε hε h
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h

theorem state_regular (k : Joint 2 4) :
    (state ε a h hε ha hh k,shiftedOutput ε a h hε ha hh hb k) ∈ regularGraph ε hε h :=
  ⟨⟨state_ordered_graph ε a h hε ha hh hb k,
    KFCausalCoherentLongitudinalDomain.state_domain ε a h hε ha hh k,
    KFCausalShiftedGaussianLongitudinalDomain.shiftedOutput_domain ε a hε ha h hh hb k⟩,
    KFCausalCoherentShearDomain.state_shear_domain ε a h hε ha hh k,
    KFCausalCoherentShearCompositions.shiftedOutput_shear_domain ε a h hε ha hh hb k⟩

theorem finite_regular {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) :
    (∑ i, z i • state ε a h hε ha hh (k i),
      ∑ i, z i • shiftedOutput ε a h hε ha hh hb (k i)) ∈ regularGraph ε hε h := by
  have hs := (regularGraph ε hε h).sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    (regularGraph ε hε h).smul_mem (z i) (state_regular ε a h hε ha hh hb (k i)))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

include hb in
theorem span_regular (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : Hilbert) (hg : (f,g) ∈ (T).graph) : (f,g) ∈ regularGraph ε hε h := by
  obtain ⟨n,k,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hs := finite_regular ε a h hε ha hh hb k z
  have he := (T).mem_graph_snd_inj' hg hs.1.1 rfl
  dsimp only at he
  rw [he]
  exact hs

theorem span_compositions (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : Hilbert) (hg : (f,g) ∈ (T).graph) :
    ∃ b tb bg jg : Hilbert, (f,b) ∈ (B).graph ∧ (b,tb) ∈ (T).graph ∧
      (g,bg) ∈ (B).graph ∧ (g,jg) ∈ (J).graph ∧
      bg-tb = pureCorrection ε hε h hb g jg :=
  KFCausalClockFloorPureClockVacuumCommutator.core_compositions ε hε h hb hh f g
    (span_regular ε a h hε ha hh hb f hf g hg)

theorem span_weak_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g jg b tb : Hilbert) (hg : (f,g) ∈ (T).graph) (hj : (g,jg) ∈ (J).graph)
    (hB : (f,b) ∈ (B).graph) (hT : (b,tb) ∈ (T).graph) :
    (-2/h)*(inner ℂ g tb).im = KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb g jg := by
  obtain ⟨b',tb',bg,jg',hb',htb',hbg,hjg',he⟩ := span_compositions ε a h hε ha hh hb f hf g hg
  exact KFCausalClockFloorPureClockVacuumResponse.weak_response ε hε h hb hh f g b tb bg jg
    (span_regular ε a h hε ha hh hb f hf g hg) hB hT hbg hj

#print axioms state_regular
#print axioms finite_regular
#print axioms span_regular
#print axioms span_compositions
#print axioms span_weak_response
end
end UnifiedTheory.Audit.KFCausalCoherentVacuumCommutator
