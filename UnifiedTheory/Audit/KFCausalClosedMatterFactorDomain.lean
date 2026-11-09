/- The closed clock, momentum, exponential and both matter factors
have a common dense physical domain. This is a Hilbert-density statement,
not a graph-core or joint-form-closure identification. -/
import UnifiedTheory.Audit.KFCausalMatterFactorClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedMatterFactorDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalMomentumMatterDomain
open UnifiedTheory.Audit.KFCausalClosedOrderedFactorDomain
open UnifiedTheory.Audit.KFCausalMatterFactorClosure

def closedMatterSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (l : Transverse →L[ℝ] ℝ) :
    Submodule ℂ Hilbert :=
  closedFactorSpace ε hε hbar ⊓
    ((closedMatterFactor ε hε hbar (physicalField l)).domain ⊓
      (closedMatterFactor ε hε hbar (fieldSquare l)).domain)

theorem orderedSpace_le_closedMatterSpace (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) : operatorOrderedSpace ε hε hbar l ≤ closedMatterSpace ε hε hbar l := by
  intro f hf
  refine ⟨orderedSpace_le_closedFactorSpace ε hbar hε l hf,?_,?_⟩
  · exact (matterFactor_le_closure ε hbar hε _).1
      (orderedSpace_le_matterFactor ε hbar hε l _ (fieldSquare_domain_le_physicalField l) hf)
  · exact (matterFactor_le_closure ε hbar hε _).1
      (orderedSpace_le_matterFactor ε hbar hε l _ le_rfl hf)

theorem closedMatterSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (closedMatterSpace ε hε hbar l).topologicalClosure=⊤ := by
  have hc := Submodule.topologicalClosure_mono (orderedSpace_le_closedMatterSpace ε hbar hε l)
  rw [operatorOrderedSpace_dense ε hbar hε hh l] at hc
  exact top_unique hc

#print axioms orderedSpace_le_closedMatterSpace
#print axioms closedMatterSpace_dense

end
end UnifiedTheory.Audit.KFCausalClosedMatterFactorDomain
