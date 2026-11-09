/- Exact charge-coordinate representatives of the actual inverse-clock
weighted antisymmetric kinetic factors, including their retained outputs
on the simultaneous closed energy graph. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockChargeMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (inverseClockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_closed)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (closedEnergy closedEnergy_component_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)

theorem inverseL_charge_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    chargeCoordinates (inverseL ε hε f) =ᵐ[volume]
      fun x => (Real.sqrt (clock ε (x (.inr 0))) : ℂ)⁻¹*(chargeCoordinates f) x := by
  have he := chargeCoordinates_multiplier (normalizedInverse ε) (normalizedInverse_measurable ε)
    (normalizedInverse_bound ε hε) f
  rw [normalizedInverse_operator ε hε,map_smul] at he
  have hc : (Real.sqrt ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε).ne'
  filter_upwards [jointMultiplier_coe (normalizedInverse ε) (normalizedInverse_measurable ε)
    (normalizedInverse_bound ε hε) (chargeCoordinates f),
    Lp.coeFn_smul (Real.sqrt ε : ℂ) (chargeCoordinates (inverseL ε hε f))] with x hj hs
  have hx := congrArg (fun z : _ => z x) he
  dsimp only at hx
  rw [hs,hj] at hx
  simp only [Pi.smul_apply,smul_eq_mul,normalizedInverse] at hx
  apply mul_left_cancel₀ hc
  exact hx.trans (by unfold clock; ring)

theorem clockMomentum_graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Transverse) (f g : Hilbert) :
    (f,g) ∈ (clockMomentum ε h v).graph ↔ (inverseL ε hε f,g) ∈ (transverseMomentum h v).graph := by
  rw [clockMomentum,composition_graph]
  constructor
  · rintro ⟨y,hy,hg⟩
    rw [(inverseL_graph ε hε f y).mp hy] at hg
    exact hg
  · intro hg
    exact ⟨_,(inverseL_graph ε hε f _).mpr rfl,hg⟩

theorem clockMomentum_closed (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Transverse) :
    (clockMomentum ε h v).IsClosed := by
  let T := (inverseL ε hε).prodMap (ContinuousLinearMap.id ℂ Hilbert)
  have he : ((clockMomentum ε h v).graph : Set (Hilbert × Hilbert)) =
      T ⁻¹' ((transverseMomentum h v).graph : Set (Hilbert × Hilbert)) := by
    ext z
    exact clockMomentum_graph_iff ε hε h v z.1 z.2
  change IsClosed ((clockMomentum ε h v).graph : Set (Hilbert × Hilbert))
  rw [he]
  exact (transverseMomentum_closed h v).preimage T.continuous

def weightedAntiSymbol (ε h : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ :=
  antiSymbol h i x/Real.sqrt (clock ε (x (.inr 0)))

theorem weightedAnti_graph_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f g : Hilbert) (hfg : (f,g) ∈ (clockMomentum ε h (antiDirection i)).graph) :
    chargeCoordinates g =ᵐ[volume]
      fun x => (weightedAntiSymbol ε h i x : ℂ)*(chargeCoordinates f) x := by
  filter_upwards [antisymmetric_graph_coe h hh i _ _ ((clockMomentum_graph_iff ε hε h _ f g).mp hfg),
    inverseL_charge_coe ε hε f] with x hg hf
  rw [hg,hf,weightedAntiSymbol,Complex.ofReal_div,div_eq_mul_inv,mul_assoc]

def antiIndex (i : Fin 2) : Fin 8 := ![3,4] i

theorem antiIndex_factor (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    energyFactor ε hε h modelDirections pointField (antiIndex i) = clockMomentum ε h (antiDirection i) := by
  fin_cases i <;> rfl

theorem antiIndex_weight (m g κ t : ℝ) (i : Fin 2) :
    energyWeight m g κ t (antiIndex i) = (Real.exp t*Real.sqrt (1/2) : ℝ) := by
  fin_cases i <;> rfl

theorem closedEnergy_anti_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε)
    (m g κ t : ℝ) (i : Fin 2) (f : Hilbert) (y : Output (Fin 8) Hilbert)
    (hfy : (f,y) ∈ (closedEnergy ε hε h modelDirections pointField m g κ t).graph) :
    ((Real.exp t*Real.sqrt (1/2) : ℝ) • f,y (antiIndex i)) ∈ (clockMomentum ε h (antiDirection i)).graph := by
  have hc := closedEnergy_component_graph ε hε h modelDirections pointField m g κ t hb f y hfy (antiIndex i)
  rw [antiIndex_factor,antiIndex_weight] at hc
  have hs := clockMomentum_closed ε hε h (antiDirection i)
  have he := hs.isClosable.graph_closure_eq_closure_graph.symm.trans hs.submodule_topologicalClosure_eq
  rw [he] at hc
  exact hc

theorem form_anti_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε)
    (m g κ t : ℝ) (i : Fin 2)
    (u : KFCausalClosedGraphForm.FormSpace (KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t)) :
    ((Real.exp t*Real.sqrt (1/2) : ℝ) • KFCausalClosedGraphForm.embedding _ u,
      KFCausalClosedGraphForm.energyOutput _ u (antiIndex i)) ∈ (clockMomentum ε h (antiDirection i)).graph :=
  closedEnergy_anti_graph ε hε h hb m g κ t i _ _ u.property

#print axioms inverseL_charge_coe
#print axioms clockMomentum_graph_iff
#print axioms clockMomentum_closed
#print axioms weightedAnti_graph_coe
#print axioms antiIndex_factor
#print axioms antiIndex_weight
#print axioms closedEnergy_anti_graph
#print axioms form_anti_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
