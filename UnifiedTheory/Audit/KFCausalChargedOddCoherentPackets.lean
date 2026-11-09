/- A concrete two-packet construction of nonzero charge-zero excitations
orthogonal to the entire neutral response class. These excitations and
their actual clock momenta have full completed-form lifts at every time. -/
import UnifiedTheory.Audit.KFCausalNeutralClosureObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedOddCoherentPackets
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargedPlaneSwap
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection zeroProjection_integral zeroSector)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state mixedState mixedState_coe state_coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection (projectedState projectedState_mem)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)

theorem swap_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    swap (flowEquiv c hc θ x) = flowEquiv c hc θ (swap x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [swap,flow_apply,dilate,KFCausalPairedRotation.rotate]

theorem operator_action (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    operator (action h hh θ f) = action h hh θ (operator f) := by
  apply chargeCoordinates.injective
  rw [coordinates_operator,action_coordinates,action_coordinates,coordinates_operator]
  apply Lp.ext
  filter_upwards [mixed_coe (KFCausalMixedCircleAction.action _ (momentumScale_ne_zero h hh) θ (chargeCoordinates f)),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae
      (KFCausalMixedCircleAction.action_coe _ (momentumScale_ne_zero h hh) θ (chargeCoordinates f)),
    KFCausalMixedCircleAction.action_coe _ (momentumScale_ne_zero h hh) θ (mixed (chargeCoordinates f)),
    (flow_preserves_volume _ (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae
      (mixed_coe (chargeCoordinates f))] with x hx hy hz hw
  change KFCausalMixedCircleAction.action _ (momentumScale_ne_zero h hh) θ
    (chargeCoordinates f) (swap x) = chargeCoordinates f (flowEquiv _ _ θ (swap x)) at hy
  simp only [Function.comp_apply] at hz
  rw [hx,hy,hz,hw,swap_flow]

theorem operator_projection (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    operator (zeroProjection h hh f) = zeroProjection h hh (operator f) := by
  let L : Hilbert →L[ℂ] Hilbert := operator
  have hi := L.intervalIntegral_comp_comm
    ((KFCausalPhysicalCircleAction.action_strong_continuous h hh f).intervalIntegrable (μ := volume) 0 (2*Real.pi))
  change (∫ θ in (0:ℝ)..2*Real.pi, operator (action h hh θ f)) =
    operator (∫ θ in (0:ℝ)..2*Real.pi, action h hh θ f) at hi
  have hs (r : ℝ) (x : Hilbert) : operator (r • x) = r • operator x :=
    L.map_smul_of_tower r x
  rw [zeroProjection_integral,zeroProjection_integral,hs,← hi]
  simp_rw [operator_action]

theorem swap_phase_pairing (c : ℝ) (x k : Space) :
    inner ℝ (swap x) (dilate c k) = inner ℝ x (dilate c (swap k)) := by
  simp [PiLp.inner_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,RCLike.inner_apply,swap,dilate]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

theorem operator_state (k : Joint 2 4) :
    operator (state ε a h hε ha hh k) = state ε a h hε ha hh (swap k) := by
  apply chargeCoordinates.injective
  rw [coordinates_operator,state_coordinates,state_coordinates]
  apply Lp.ext
  filter_upwards [mixed_coe (mixedState ε a h hε ha hh k),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae (mixedState_coe ε a h hε ha hh k),
    mixedState_coe ε a h hε ha hh (swap k)] with x hx hy hz
  change mixedState ε a h hε ha hh k (swap x) =
    KFCausalEuclideanFourierUniqueness.modulate (dilate (momentumScale h) k)
      (KFCausalClockFloorCoherentStates.weight ε a h) (swap x) at hy
  rw [hx,hy,hz]
  simp only [KFCausalEuclideanFourierUniqueness.modulate,swap_phase_pairing,weight_swap]

theorem operator_projectedState (k : Joint 2 4) :
    operator (projectedState ε a h hε ha hh k) = projectedState ε a h hε ha hh (swap k) := by
  rw [projectedState,operator_projection,operator_state]
  rfl

def oddPacket (k : Joint 2 4) : Hilbert :=
  projectedState ε a h hε ha hh k-projectedState ε a h hε ha hh (swap k)

theorem oddPacket_odd (k : Joint 2 4) :
    operator (oddPacket ε a h hε ha hh k) = -oddPacket ε a h hε ha hh k := by
  rw [oddPacket,map_sub,operator_projectedState,operator_projectedState,swap_twice,neg_sub]

theorem oddPacket_zeroSector (k : Joint 2 4) : oddPacket ε a h hε ha hh k ∈ zeroSector h hh :=
  (zeroSector h hh).sub_mem (projectedState_mem ε a h hε ha hh k) (projectedState_mem ε a h hε ha hh (swap k))

theorem exists_nonzero_oddPacket : ∃ k : Joint 2 4, oddPacket ε a h hε ha hh k ≠ 0 := by
  obtain ⟨k,hk⟩ := KFCausalNeutralClosureObstruction.exists_projected_outside_fixed ε a h hε ha hh
  refine ⟨k,?_⟩
  intro hz
  have he := sub_eq_zero.mp hz
  apply hk
  change operator (projectedState ε a h hε ha hh k) = projectedState ε a h hε ha hh k
  rw [operator_projectedState]
  exact he.symm

theorem oddPacket_orthogonal (k : Joint 2 4) (f : Hilbert) (hf : f ∈ fixedSpace) :
    inner ℂ f (oddPacket ε a h hε ha hh k) = 0 := by
  have he := operator.inner_map_map f (oddPacket ε a h hε ha hh k)
  rw [show operator f = f from hf,oddPacket_odd,inner_neg_right] at he
  linear_combination -he/2

theorem oddPacket_neutralClosure_orthogonal (k : Joint 2 4) (f : Hilbert)
    (hf : f ∈ closure (KFCausalNeutralSwapConstraint.neutralStates ε h hε hh)) :
    inner ℂ f (oddPacket ε a h hε ha hh k) = 0 :=
  oddPacket_orthogonal ε a h hε ha hh k f (KFCausalNeutralSwapConstraint.closure_subset_fixed ε h hε hh hf)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem oddPacket_completed_pair (k : Joint 2 4) (m g v t : ℝ) :
    ∃ u w : FormSpace ε hε h hh hb m g v t,
      embedding ε hε h hh hb m g v t u = oddPacket ε a h hε ha hh k ∧
      (embedding ε hε h hh hb m g v t u,embedding ε hε h hh hb m g v t w) ∈
        (pureMomentum ε hε h).graph ∧
      embedding ε hε h hh hb m g v t w ∈ zeroSector h hh := by
  obtain ⟨u,w,hu,hB,hw⟩ :=
    KFCausalNeutralClosureObstruction.projected_completed_momentum_pair ε a h hε ha hh hb k m g v t
  obtain ⟨u',w',hu',hB',hw'⟩ :=
    KFCausalNeutralClosureObstruction.projected_completed_momentum_pair ε a h hε ha hh hb (swap k) m g v t
  refine ⟨u-u',w-w',?_,?_,?_⟩
  · rw [map_sub,hu,hu',oddPacket]
  · simpa only [map_sub] using (pureMomentum ε hε h).graph.sub_mem hB hB'
  · rw [map_sub]
    exact (zeroSector h hh).sub_mem hw hw'

#print axioms swap_flow
#print axioms operator_action
#print axioms operator_projection
#print axioms swap_phase_pairing
#print axioms operator_state
#print axioms operator_projectedState
#print axioms oddPacket_odd
#print axioms oddPacket_zeroSector
#print axioms exists_nonzero_oddPacket
#print axioms oddPacket_orthogonal
#print axioms oddPacket_neutralClosure_orthogonal
#print axioms oddPacket_completed_pair
end
end UnifiedTheory.Audit.KFCausalChargedOddCoherentPackets
