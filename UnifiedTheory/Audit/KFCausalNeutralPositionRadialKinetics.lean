/- The actual charge-compatible radial cutoff preserves clock and all
four ordered kinetic graphs. The only nonzero correction is on the
second physical kinetic row, and its norm is derived explicitly. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionHeatMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (inverseL_charge_coe)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf half_inverse_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorKineticModulation (kinetic_graph_iff)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics (input zero_bound kineticCorrection kineticCorrection_norm)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)

theorem heat_inverseL (f : Hilbert) :
    inverseL ε hε (heat h δ hδ f) = heat h δ hδ (inverseL ε hε f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [inverseL_charge_coe ε hε (heat h δ hδ f),heat_coe h δ hδ f,
    heat_coe h δ hδ (inverseL ε hε f),inverseL_charge_coe ε hε f] with x hi hh hh' hi'
  rw [hi,hh,hh',hi']
  ring

include hε in
theorem heat_clock_graph (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (clockHalf ε).graph := by
  apply (half_inverse_graph ε hε _ _).mpr
  apply (inverseL_graph ε hε _ _).mpr
  have he := (inverseL_graph ε hε g f).mp ((half_inverse_graph ε hε f g).mp hfg)
  rw [heat_inverseL,← he]

include hε in
theorem heat_kinetic_graph (hne : h ≠ 0) (i : Fin 4) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h (modelDirections i)).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (clockMomentum ε h (modelDirections i)).graph := by
  rw [kinetic_graph_iff ε hε,heat_inverseL]
  exact KFCausalNeutralPositionHeatMomentum.model_graph h δ hδ hne i _ _
    ((kinetic_graph_iff ε hε h (modelDirections i) f g).mp hfg)

def correction (i : Fin 4) : Hilbert →L[ℂ] Hilbert :=
  (kineticCorrection ε δ v hε hδ h (modelDirections i)).comp (heat h δ hδ)

include hε in
theorem clock_graph (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (action h δ v hδ f,action h δ v hδ g) ∈ (clockHalf ε).graph := by
  rw [action_eq_input_heat ε h δ v hε hδ,action_eq_input_heat ε h δ v hε hδ]
  exact KFCausalNeutralPositionLocalizedMatter.clockHalf_graph_action ε δ v hε hδ
    0 (zero_bound ε hε) _ _ (heat_clock_graph ε hε h δ hδ f g hfg)

theorem kinetic_graph (hne : h ≠ 0) (i : Fin 4) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h (modelDirections i)).graph) :
    (action h δ v hδ f,action h δ v hδ g+correction ε hε h δ v hδ i f) ∈
      (clockMomentum ε h (modelDirections i)).graph := by
  rw [action_eq_input_heat ε h δ v hε hδ,action_eq_input_heat ε h δ v hε hδ]
  exact KFCausalNeutralPositionLocalizedKinetics.kinetic_graph_input ε δ v hε hδ h hne
    (modelDirections i) _ _ (heat_kinetic_graph ε hε h δ hδ hne i f g hfg)

theorem correction_norm (i : Fin 4) (f : Hilbert) :
    ‖correction ε hε h δ v hδ i f‖ ≤
      (|h| * (2*Real.sqrt δ*|(modelDirections i) 2+(modelDirections i) 3|+
        |v*(modelDirections i) 4|)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  apply (kineticCorrection_norm ε δ v hε hδ h (modelDirections i) (heat h δ hδ f)).trans
  exact mul_le_mul_of_nonneg_left (heat_norm h δ hδ f) (by positivity)

theorem correction_other (i : Fin 4) (hi : i ≠ 1) (f : Hilbert) :
    correction ε hε h δ v hδ i f = 0 := by
  have he := correction_norm ε hε h δ v hδ i f
  have hc : 2*Real.sqrt δ*|(modelDirections i) 2+(modelDirections i) 3|+
      |v*(modelDirections i) 4| = 0 := by
    fin_cases i
    · change 2*Real.sqrt δ*|(0:ℝ)+0|+|v*0| = 0
      simp
    · exact (hi rfl).elim
    · change 2*Real.sqrt δ*|(0:ℝ)+0|+|v*0| = 0
      simp
    · change 2*Real.sqrt δ*|(1:ℝ)+(-1)|+|v*0| = 0
      norm_num
  rw [hc,mul_zero,zero_mul,zero_mul] at he
  apply norm_eq_zero.mp
  exact le_antisymm he (norm_nonneg _)

theorem correction_second_bound (f : Hilbert) :
    ‖correction ε hε h δ v hδ 1 f‖ ≤
      |h| * ((4*Real.sqrt δ+|v|)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  have he := correction_norm ε hε h δ v hδ 1 f
  have hc : 2*Real.sqrt δ*|(modelDirections 1) 2+(modelDirections 1) 3|+
      |v*(modelDirections 1) 4| = 4*Real.sqrt δ+|v| := by
    change 2*Real.sqrt δ*|(1:ℝ)+1|+|v*1| = 4*Real.sqrt δ+|v|
    norm_num
    ring
  rw [hc] at he
  exact he.trans_eq (by ring)

#print axioms heat_inverseL
#print axioms heat_clock_graph
#print axioms heat_kinetic_graph
#print axioms clock_graph
#print axioms kinetic_graph
#print axioms correction_norm
#print axioms correction_other
#print axioms correction_second_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics
