/- The charge-compatible radial cutoff acts on the actual five-row kinetic
graph. Its bounded correction is supported on the second momentum row.
The estimate is independent of time and of all matter couplings. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics
import UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph
import UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph (Outputs factor weight graph)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action action_norm)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap outputMap_norm)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)

def outputAction : Outputs →L[ℂ] Outputs := outputMap (fun _ => action h δ v hδ)

def extra : Hilbert →L[ℂ] Outputs where
  toFun f := WithLp.toLp 2 (Pi.single 2 ((Real.sqrt (1/2):ℂ) • correction ε hε h δ v hδ 1 f))
  map_add' f g := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_add,smul_add]
  map_smul' c f := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_smul]
    module
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => by
    fin_cases i <;> simp <;> fun_prop))

def responseConstant (ε δ v : ℝ) : ℝ :=
  Real.sqrt (1/2)*(4*Real.sqrt δ+|v|)*(Real.sqrt ε)⁻¹

theorem responseConstant_nonneg : 0 ≤ responseConstant ε δ v := by
  unfold responseConstant
  positivity

theorem outputAction_norm (y : Outputs) : ‖outputAction h δ v hδ y‖ ≤ ‖y‖ := by
  exact (outputMap_norm (fun _ => action h δ v hδ) 1 (by norm_num)
    (fun _ f => by simpa only [one_mul] using action_norm h δ v hδ f) y).trans_eq (one_mul _)

theorem extra_norm (f : Hilbert) :
    ‖extra ε hε h δ v hδ f‖ = Real.sqrt (1/2)*‖correction ε hε h δ v hδ 1 f‖ := by
  change ‖(WithLp.toLp 2 (Pi.single 2 ((Real.sqrt (1/2):ℂ) • correction ε hε h δ v hδ 1 f)) : Outputs)‖ = _
  rw [PiLp.norm_toLp_single,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

theorem extra_bound (f : Hilbert) :
    ‖extra ε hε h δ v hδ f‖ ≤ |h| *responseConstant ε δ v*‖f‖ := by
  rw [extra_norm]
  exact (mul_le_mul_of_nonneg_left (correction_second_bound ε hε h δ v hδ f)
    (Real.sqrt_nonneg _)).trans_eq (by unfold responseConstant; ring)

theorem graph_action (hne : h ≠ 0) (t : ℝ) (f : Hilbert) (y : Outputs)
    (hfy : (f,y) ∈ graph ε h t) :
    (action h δ v hδ f,outputAction h δ v hδ y+extra ε hε h δ v hδ f) ∈ graph ε h t := by
  intro i
  fin_cases i
  · simpa [outputAction,outputMap,extra,map_smul] using
      clock_graph ε hε h δ v hδ (weight t 0 • f) (y 0) (hfy 0)
  · have he := kinetic_graph ε hε h δ v hδ hne 0 (weight t 1 • f) (y 1) (hfy 1)
    rw [correction_other ε hε h δ v hδ 0 (by decide),add_zero] at he
    simpa [outputAction,outputMap,extra,map_smul] using he
  · simpa [outputAction,outputMap,extra,map_smul,weight] using
      kinetic_graph ε hε h δ v hδ hne 1 (weight t 2 • f) (y 2) (hfy 2)
  · have he := kinetic_graph ε hε h δ v hδ hne 2 (weight t 3 • f) (y 3) (hfy 3)
    rw [correction_other ε hε h δ v hδ 2 (by decide),add_zero] at he
    simpa [outputAction,outputMap,extra,map_smul] using he
  · have he := kinetic_graph ε hε h δ v hδ hne 3 (weight t 4 • f) (y 4) (hfy 4)
    rw [correction_other ε hε h δ v hδ 3 (by decide),add_zero] at he
    simpa [outputAction,outputMap,extra,map_smul] using he

theorem output_bound (f : Hilbert) (y : Outputs) :
    ‖outputAction h δ v hδ y+extra ε hε h δ v hδ f‖ ≤
      ‖y‖+|h| *responseConstant ε δ v*‖f‖ := by
  exact (norm_add_le _ _).trans
    (add_le_add (outputAction_norm h δ v hδ y) (extra_bound ε hε h δ v hδ f))

#print axioms responseConstant_nonneg
#print axioms outputAction_norm
#print axioms extra_norm
#print axioms extra_bound
#print axioms graph_action
#print axioms output_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph
