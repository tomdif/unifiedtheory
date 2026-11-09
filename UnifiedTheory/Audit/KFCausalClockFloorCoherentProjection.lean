/- Projecting the explicit total modulation family gives a dense span
in the actual zero-charge sector. This theorem does not assert that the
projected family belongs to the averaged energy domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (trialState trialState_mem_zeroSector trialState_ne_zero)

def projectedState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : Hilbert := zeroProjection hbar hh (state ε a hbar hε ha hh k)

theorem projectedState_mem (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : projectedState ε a hbar hε ha hh k ∈ zeroSector hbar hh :=
  zeroProjection_mem hbar hh _

theorem projectedState_charge_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : (projectedState ε a hbar hε ha hh k,0) ∈ (standingCharge hbar hh).graph :=
  standingCharge_projection_zero hbar hh _

theorem projectedState_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    projectedState ε a hbar hε ha hh 0 = trialState ε a hbar hε ha hh := by
  rw [projectedState,state_zero]
  exact zeroProjection_fixes hbar hh _ (trialState_mem_zeroSector ε a hbar hε ha hh)

theorem projectedState_zero_ne_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    projectedState ε a hbar hε ha hh 0 ≠ 0 := by
  rw [projectedState_zero]
  exact trialState_ne_zero ε a hbar hε ha hh

theorem dense_projected_span (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (Submodule.span ℂ (Set.range (projectedState ε a hbar hε ha hh))).topologicalClosure =
      zeroSector hbar hh := by
  apply le_antisymm
  · have hs : Submodule.span ℂ (Set.range (projectedState ε a hbar hε ha hh)) ≤ zeroSector hbar hh := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k,rfl⟩
      exact projectedState_mem ε a hbar hε ha hh k
    have hc := Submodule.topologicalClosure_mono hs
    rwa [(zeroSector_closed hbar hh).submodule_topologicalClosure_eq] at hc
  · have hc := Submodule.topologicalClosure_map (zeroProjection hbar hh)
      (Submodule.span ℂ (Set.range (state ε a hbar hε ha hh)))
    rw [dense_span ε a hbar hε ha hh,Submodule.map_span,← Set.range_comp] at hc
    intro f hf
    exact hc ⟨f,Submodule.mem_top,zeroProjection_fixes hbar hh f hf⟩

#print axioms projectedState_mem
#print axioms projectedState_charge_zero
#print axioms projectedState_zero
#print axioms projectedState_zero_ne_zero
#print axioms dense_projected_span

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection
