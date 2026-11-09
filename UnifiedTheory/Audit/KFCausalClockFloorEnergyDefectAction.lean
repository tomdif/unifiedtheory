/- The bounded output action of the real clock defect on all eight actual
energy factors: D on clock/kinetic outputs and B on matter/exponential
outputs. The signed squared-defect pairing is summed in the actual L2 product. -/
import UnifiedTheory.Audit.KFCausalClockFloorMatterDefect
import UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_square_inner_im_zero)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorMatterDefect
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
open UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

def factorAction (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  if i.val < 5 then defectOperator ε hε else shiftedDefect ε hε hbar hh

theorem factorAction_bound (i : Fin 8) (g : Hilbert) : ‖factorAction ε hε hbar hh i g‖ ≤ 2*‖g‖ := by
  unfold factorAction
  split
  · exact (defectOperator_norm_le ε hε g).trans (by linarith [norm_nonneg g])
  · exact shiftedDefect_norm_le_two ε hε hbar hh g

theorem energyFactor_graph_defect (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (i : Fin 8) (f g : Hilbert) (hfg : (f,g) ∈ (energyFactor ε hε hbar v l i).graph) :
    (defectOperator ε hε f,factorAction ε hε hbar hh i g) ∈ (energyFactor ε hε hbar v l i).graph := by
  fin_cases i
  · exact clockHalf_graph_defect ε hε f g hfg
  · exact clockMomentum_graph_defect ε hε hbar (v 0) f g hfg
  · exact clockMomentum_graph_defect ε hε hbar (v 1) f g hfg
  · exact clockMomentum_graph_defect ε hε hbar (v 2) f g hfg
  · exact clockMomentum_graph_defect ε hε hbar (v 3) f g hfg
  · exact linear_matter_graph_defect ε hε hbar hh l f g hfg
  · exact quadratic_matter_graph_defect ε hε hbar hh l f g hfg
  · exact ordered_graph_defect ε hε hbar hh f g hfg

include hh in
theorem commonEnergyDomain_defect (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (f : Hilbert) (hf : f ∈ commonEnergyDomain ε hε hbar v l) :
    defectOperator ε hε f ∈ commonEnergyDomain ε hε hbar v l := by
  apply (commonEnergyDomain_iff ε hε hbar v l _).mpr
  intro i
  exact LinearPMap.mem_domain_of_mem_graph (energyFactor_graph_defect ε hε hbar hh v l i f _
    ((energyFactor ε hε hbar v l i).mem_graph ⟨f,(commonEnergyDomain_iff ε hε hbar v l f).mp hf i⟩))

def outputAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => factorAction ε hε hbar hh i (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (factorAction ε hε hbar hh i).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem outputAction_apply (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    outputAction ε hε hbar hh g i = factorAction ε hε hbar hh i (g i) := rfl

theorem outputAction_norm (g : Output (Fin 8) Hilbert) : ‖outputAction ε hε hbar hh g‖ ≤ 2*‖g‖ := by
  have hs : ‖outputAction ε hε hbar hh g‖^2 ≤ (2*‖g‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [outputAction_apply,mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (factorAction_bound ε hε hbar hh i (g i)) 2
  nlinarith [norm_nonneg (outputAction ε hε hbar hh g),norm_nonneg g]

theorem outputAction_square_sign (g : Output (Fin 8) Hilbert) :
    0 ≤ hbar*(inner ℂ g (outputAction ε hε hbar hh (outputAction ε hε hbar hh g))).im := by
  rw [PiLp.inner_apply,Complex.im_sum,Finset.mul_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : i.val < 5
  · simp only [outputAction_apply,factorAction,hi,if_true,defect_square_inner_im_zero ε hε,mul_zero,le_refl]
  · simpa only [outputAction_apply,factorAction,hi,if_false] using shiftedDefect_square_form_sign ε hε hbar hh (g i)

#print axioms factorAction_bound
#print axioms energyFactor_graph_defect
#print axioms commonEnergyDomain_defect
#print axioms outputAction_apply
#print axioms outputAction_norm
#print axioms outputAction_square_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
