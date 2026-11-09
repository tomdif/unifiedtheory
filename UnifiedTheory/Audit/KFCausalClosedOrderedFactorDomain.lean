/- The previous dense physical ordered domain lies in the constructed
closed momentum/clock and exponential/clock factors. Their common domain
is dense; the full matter-weighted Hamiltonian form remains separate. -/
import UnifiedTheory.Audit.KFCausalClockMomentumClosure
import UnifiedTheory.Audit.KFCausalOrderedExponentialClosure
import UnifiedTheory.Audit.KFCausalMomentumMatterDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedOrderedFactorDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalClockMomentumClosure
open UnifiedTheory.Audit.KFCausalOrderedExponentialClosure
open UnifiedTheory.Audit.KFCausalMomentumMatterDomain
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain

theorem orderedSpace_le_clockMomentum (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) (v : Transverse) :
    operatorOrderedSpace ε hε hbar l ≤ (clockMomentum (-(1/2)) hbar v).domain := by
  rintro f ⟨_,g,hg,hj⟩
  have hp := ((operatorJointSpace_conditions ε hbar hε l g).mp hj).1 v
  exact (composition_domain _ _ _).mpr ⟨g,hg,hp⟩

theorem orderedSpace_le_closedClockMomentum (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) (v : Transverse) :
    operatorOrderedSpace ε hε hbar l ≤ (closedClockMomentum (-(1/2)) hbar v).domain :=
  (orderedSpace_le_clockMomentum ε hbar hε l v).trans (clockMomentum_le_closure (-(1/2)) hbar v).1

theorem orderedSpace_le_orderedExponential (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) :
    operatorOrderedSpace ε hε hbar l ≤ (orderedExponential ε hε hbar).domain := by
  rintro f ⟨_,g,hg,hj⟩
  obtain ⟨hE,_⟩ := ((operatorJointSpace_conditions ε hbar hε l g).mp hj).2
  exact (composition_domain _ _ _).mpr ⟨g,hg,hE⟩

theorem orderedSpace_le_closedOrderedExponential (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) :
    operatorOrderedSpace ε hε hbar l ≤ (closedOrderedExponential ε hε hbar).domain :=
  (orderedSpace_le_orderedExponential ε hbar hε l).trans (orderedExponential_le_closure ε hbar hε).1

def closedFactorSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ Hilbert :=
  (clockPower (1/2)).domain ⊓
    ((⨅ v : Transverse, (closedClockMomentum (-(1/2)) hbar v).domain) ⊓
      (closedOrderedExponential ε hε hbar).domain)

theorem orderedSpace_le_closedFactorSpace (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) : operatorOrderedSpace ε hε hbar l ≤ closedFactorSpace ε hε hbar := by
  intro f hf
  refine ⟨hf.1,?_,orderedSpace_le_closedOrderedExponential ε hbar hε l hf⟩
  exact (Submodule.mem_iInf _).mpr (fun v => orderedSpace_le_closedClockMomentum ε hbar hε l v hf)

theorem closedFactorSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    (closedFactorSpace ε hε hbar).topologicalClosure=⊤ := by
  have hc := Submodule.topologicalClosure_mono (orderedSpace_le_closedFactorSpace ε hbar hε pointField)
  rw [operatorOrderedSpace_dense ε hbar hε hh pointField] at hc
  exact top_unique hc

#print axioms orderedSpace_le_clockMomentum
#print axioms orderedSpace_le_closedClockMomentum
#print axioms orderedSpace_le_orderedExponential
#print axioms orderedSpace_le_closedOrderedExponential
#print axioms orderedSpace_le_closedFactorSpace
#print axioms closedFactorSpace_dense

end
end UnifiedTheory.Audit.KFCausalClosedOrderedFactorDomain
