/- Exact complementary-coordinate outputs of the remaining weighted
kinetic factors along every actual charge orbit. Rotation of the natural
derivative graphs retains the neutral term and the inverse-clock order. -/
import UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
import UnifiedTheory.Audit.KFCausalClockFloorDualClock
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalClockFloorDualClock (inverseL_dual_coe)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf (inverseL_action)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (clockMomentum_graph_iff clockMomentum_closed)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (closedEnergy closedEnergy_component_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow

def symmetricEnergyIndex (i : Fin 2) : Fin 8 := ![1,2] i

theorem symmetricIndex_factor (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    energyFactor ε hε h modelDirections pointField (symmetricEnergyIndex i) = clockMomentum ε h (symmetricDirection i) := by
  fin_cases i <;> rfl

theorem symmetricIndex_weight (m g κ t : ℝ) (i : Fin 2) :
    energyWeight m g κ t (symmetricEnergyIndex i) = (Real.sqrt (1/2) : ℂ) := by
  fin_cases i <;> rfl

theorem closedEnergy_symmetric_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε)
    (m g κ t : ℝ) (i : Fin 2) (f : Hilbert) (y : Output (Fin 8) Hilbert)
    (hfy : (f,y) ∈ (closedEnergy ε hε h modelDirections pointField m g κ t).graph) :
    ((Real.sqrt (1/2) : ℂ) • f,y (symmetricEnergyIndex i)) ∈ (clockMomentum ε h (symmetricDirection i)).graph := by
  have hc := closedEnergy_component_graph ε hε h modelDirections pointField m g κ t hb f y hfy (symmetricEnergyIndex i)
  rw [symmetricIndex_factor,symmetricIndex_weight] at hc
  have hs := clockMomentum_closed ε hε h (symmetricDirection i)
  have he := hs.isClosable.graph_closure_eq_closure_graph.symm.trans hs.submodule_topologicalClosure_eq
  rw [he] at hc
  exact hc

theorem form_symmetric_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε)
    (m g κ t : ℝ) (i : Fin 2)
    (u : KFCausalClosedGraphForm.FormSpace (KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t)) :
    ((Real.sqrt (1/2) : ℂ) • KFCausalClosedGraphForm.embedding _ u,
      KFCausalClosedGraphForm.energyOutput _ u (symmetricEnergyIndex i)) ∈
        (clockMomentum ε h (symmetricDirection i)).graph :=
  closedEnergy_symmetric_graph ε hε h hb m g κ t i _ _ u.property

theorem rotated_clockMomentum_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (i : Fin 2) (f g : Hilbert)
    (hfg : (action h hh θ f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    dualPhysical (action h hh (-θ) g) =ᵐ[volume]
      fun x => (rotatedWeightedSymbol ε h hh θ i x : ℂ)*(dualPhysical f) x := by
  have hg := symmetric_graph h hh i _ _ ((clockMomentum_graph_iff ε hε h _ _ g).mp hfg)
  rw [inverseL_action ε hε h hh,action_coordinates] at hg
  have hr := KFCausalMixedRotationMomentumGraph.momentum_graph_reverse h hh
    (momentumScale h) (momentumScale_ne_zero h hh) θ (symmetricVector i) _ _ hg
  have he := dualMomentum_graph_coe h hh (rotatedVector h hh θ i)
    (rotatedVector_clock h hh θ i) _ _ hr
  have ho := congrArg dualMixed (action_coordinates h hh (-θ) g)
  change dualPhysical (action h hh (-θ) g) = _ at ho
  rw [← ho] at he
  change dualPhysical (action h hh (-θ) g) =ᵐ[volume] fun x =>
    (dualSymbol h (rotatedVector h hh θ i) x : ℂ)*(dualPhysical (inverseL ε hε f)) x at he
  filter_upwards [he,inverseL_dual_coe ε hε f] with x hx hf
  rw [hx,hf,rotatedWeightedSymbol,Complex.ofReal_div,div_eq_mul_inv,mul_assoc]

theorem rotated_scaled_clockMomentum_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ c : ℝ) (i : Fin 2) (f g : Hilbert)
    (hfg : ((c : ℂ) • action h hh θ f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    dualPhysical (action h hh (-θ) g) =ᵐ[volume]
      fun x => ((c*rotatedWeightedSymbol ε h hh θ i x : ℝ) : ℂ)*(dualPhysical f) x := by
  have hg : (action h hh θ ((c : ℂ) • f),g) ∈ (clockMomentum ε h (symmetricDirection i)).graph := by
    simpa only [map_smul] using hfg
  have he := rotated_clockMomentum_coe ε hε h hh θ i _ g hg
  rw [map_smul] at he
  filter_upwards [he,Lp.coeFn_smul (c : ℂ) (dualPhysical f)] with x hx hs
  rw [hx,hs,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]
  ring

#print axioms symmetricIndex_factor
#print axioms symmetricIndex_weight
#print axioms closedEnergy_symmetric_graph
#print axioms form_symmetric_graph
#print axioms rotated_clockMomentum_coe
#print axioms rotated_scaled_clockMomentum_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph
