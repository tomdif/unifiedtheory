/- The total physical modulation family lies in all eight natural energy
domains. Its finite linear span is dense and invariant under the actual
charge circle. Pointwise form lifts are constructed; integrable orbit
lifts and density of the averaged energy domain remain separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (state_ordered_domain)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

theorem state_commonEnergyDomain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (k : Joint 2 4) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    state ε a hbar hε ha hh k ∈ commonEnergyDomain ε hε hbar v l := by
  apply (commonEnergyDomain_iff ε hε hbar v l _).mpr
  intro i
  fin_cases i
  · exact state_clockHalf_domain ε a hbar hε ha hh k
  · exact state_clockMomentum_domain ε a hbar hε ha hh k (v 0)
  · exact state_clockMomentum_domain ε a hbar hε ha hh k (v 1)
  · exact state_clockMomentum_domain ε a hbar hε ha hh k (v 2)
  · exact state_clockMomentum_domain ε a hbar hε ha hh k (v 3)
  · exact state_linearMatter_domain ε a hbar hε ha hh hbound k l
  · exact state_quadraticMatter_domain ε a hbar hε ha hh hbound k l
  · exact state_ordered_domain ε a hbar hε ha hh hbound k

theorem action_state_commonEnergyDomain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (θ : ℝ) (k : Joint 2 4) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    action hbar hh θ (state ε a hbar hε ha hh k) ∈ commonEnergyDomain ε hε hbar v l := by
  rw [action_state]
  exact state_commonEnergyDomain ε a hbar hε ha hh hbound _ v l

def coherentSpan (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) : Submodule ℂ Hilbert :=
  Submodule.span ℂ (Set.range (state ε a hbar hε ha hh))

theorem coherentSpan_le_commonEnergyDomain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    coherentSpan ε a hbar hε ha hh ≤ commonEnergyDomain ε hε hbar v l := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact state_commonEnergyDomain ε a hbar hε ha hh hbound k v l

theorem coherentSpan_dense (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (coherentSpan ε a hbar hε ha hh).topologicalClosure = ⊤ :=
  dense_span ε a hbar hε ha hh

theorem action_coherentSpan (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (θ : ℝ) (f : Hilbert) (hf : f ∈ coherentSpan ε a hbar hε ha hh) :
    action hbar hh θ f ∈ coherentSpan ε a hbar hε ha hh := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k,rfl⟩
      rw [action_state]
      exact Submodule.subset_span (Set.mem_range_self _)
  | zero => simp only [map_zero,Submodule.zero_mem]
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (coherentSpan ε a hbar hε ha hh).add_mem hx hy
  | smul c x _ hx =>
      rw [map_smul]
      exact (coherentSpan ε a hbar hε ha hh).smul_mem c hx

theorem hamiltonian_bound (ε hbar : ℝ) (hbound : |hbar| ≤ 2*Real.pi*ε/3) : |hbar| ≤ Real.pi*ε := by
  nlinarith [abs_nonneg hbar]

def formVector (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) (k : Joint 2 4) :
    KFCausalClosedGraphForm.FormSpace
      (formData ε hε hbar (hamiltonian_bound ε hbar hbound) mass2 quartic vacuum t) :=
  commonFormVector ε hε hbar (hamiltonian_bound ε hbar hbound) mass2 quartic vacuum t
    ⟨state ε a hbar hε ha hh k,state_commonEnergyDomain ε a hbar hε ha hh hbound k modelDirections pointField⟩

theorem formVector_embedding (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) (k : Joint 2 4) :
    KFCausalClosedGraphForm.embedding _ (formVector ε a hbar hε ha hh hbound mass2 quartic vacuum t k) =
      state ε a hbar hε ha hh k := rfl

theorem orbit_formVector_embedding (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t θ : ℝ) (k : Joint 2 4) :
    KFCausalClosedGraphForm.embedding _
      (formVector ε a hbar hε ha hh hbound mass2 quartic vacuum t
        (KFCausalChargeModulationFlow.parameter θ k)) = action hbar hh θ (state ε a hbar hε ha hh k) := by
  rw [formVector_embedding,action_state]

theorem formVector_energy (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (k : Joint 2 4) :
    ‖KFCausalClosedGraphForm.energyOutput _
      (formVector ε a hbar hε ha hh hbound mass2 quartic vacuum t k)‖^2 =
      KFCausalClockFloorJointEnergy.seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t
        ⟨state ε a hbar hε ha hh k,state_commonEnergyDomain ε a hbar hε ha hh hbound k modelDirections pointField⟩ :=
  commonFormVector_energy ε hε hbar (hamiltonian_bound ε hbar hbound) mass2 quartic vacuum t hm hq hv _

#print axioms state_commonEnergyDomain
#print axioms action_state_commonEnergyDomain
#print axioms coherentSpan_le_commonEnergyDomain
#print axioms coherentSpan_dense
#print axioms action_coherentSpan
#print axioms hamiltonian_bound
#print axioms formVector_embedding
#print axioms orbit_formVector_embedding
#print axioms formVector_energy

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
