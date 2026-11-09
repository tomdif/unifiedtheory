/- The actual localized neutral-position observable acts on the complete
unaveraged closed eight-factor energy graph. All product-rule hypotheses
are derived for the physical factors. Arbitrary weights, including zero,
are allowed. Charge averaging is a separate unresolved step. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics
import UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMatter
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (action)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap correctionMap)

variable (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
  (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3)

def factorOutput : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![input ε δ v hε hδ,input ε δ v hε hδ,input ε δ v hε hδ,
    input ε δ v hε hδ,input ε δ v hε hδ,
    action ε δ v hε hδ (-h/2) (shift_bound ε h hh),
    action ε δ v hε hδ (-h/2) (shift_bound ε h hh),
    action ε δ v hε hδ (-h/2) (shift_bound ε h hh)]

def factorCorrection (d : Fin 4 → Transverse) : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![0,kineticCorrection ε δ v hε hδ h (d 0),kineticCorrection ε δ v hε hδ h (d 1),
    kineticCorrection ε δ v hε hδ h (d 2),kineticCorrection ε δ v hε hδ h (d 3),0,0,0]

variable (hne : h ≠ 0) (d : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)

include hne in
theorem factor_graph (i : Fin 8) (f g : Hilbert)
    (hfg : (f,g) ∈ (energyFactor ε hε h d l i).graph) :
    (input ε δ v hε hδ f,
      factorOutput ε δ v hε hδ h hh i g+factorCorrection ε δ v hε hδ h d i f) ∈
        (energyFactor ε hε h d l i).graph := by
  fin_cases i
  · change (input ε δ v hε hδ f,input ε δ v hε hδ g+0) ∈ _
    rw [add_zero]
    exact clockHalf_graph_action ε δ v hε hδ 0 (zero_bound ε hε) f g hfg
  · exact kinetic_graph_input ε δ v hε hδ h hne (d 0) f g hfg
  · exact kinetic_graph_input ε δ v hε hδ h hne (d 1) f g hfg
  · exact kinetic_graph_input ε δ v hε hδ h hne (d 2) f g hfg
  · exact kinetic_graph_input ε δ v hε hδ h hne (d 3) f g hfg
  · change (input ε δ v hε hδ f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g+0) ∈ _
    rw [add_zero]
    exact linear_matter_graph_action ε δ v hε hδ h hh (zero_bound ε hε) l f g hfg
  · change (input ε δ v hε hδ f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g+0) ∈ _
    rw [add_zero]
    exact quadratic_matter_graph_action ε δ v hε hδ h hh (zero_bound ε hε) l f g hfg
  · change (input ε δ v hε hδ f,action ε δ v hε hδ (-h/2) (shift_bound ε h hh) g+0) ∈ _
    rw [add_zero]
    exact ordered_graph_action ε δ v hε hδ h hh (zero_bound ε hε) f g hfg

def transformedOutput (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert) :
    Output (Fin 8) Hilbert :=
  outputMap (factorOutput ε δ v hε hδ h hh) g+
    correctionMap (factorCorrection ε δ v hε hδ h d) c f

include hne in
theorem joint_graph (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h d l) c) :
    (input ε δ v hε hδ f,transformedOutput ε δ v hε hδ h hh d c f g) ∈
      jointGraph (energyFactor ε hε h d l) c :=
  KFCausalJointGraphBoundedCorrection.joint_graph _ _ _ _
    (factor_graph ε δ v hε hδ h hh hne d l) c f g hfg

include hne in
theorem joint_closure (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h d l) c).topologicalClosure) :
    (input ε δ v hε hδ f,transformedOutput ε δ v hε hδ h hh d c f g) ∈
      (jointGraph (energyFactor ε hε h d l) c).topologicalClosure :=
  KFCausalJointGraphBoundedCorrection.joint_closure _ _ _ _
    (factor_graph ε δ v hε hδ h hh hne d l) c f g hfg

include hε hh in
theorem energy_bound : |h| ≤ Real.pi*ε := by nlinarith [Real.pi_pos]

variable (mass2 quartic vacuum t : ℝ)

include hne in
theorem closed_graph (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h d l mass2 quartic vacuum t).graph) :
    (input ε δ v hε hδ f,
      transformedOutput ε δ v hε hδ h hh d (energyWeight mass2 quartic vacuum t) f g) ∈
        (closedEnergy ε hε h d l mass2 quartic vacuum t).graph := by
  rw [closedEnergy_graph ε hε h d l mass2 quartic vacuum t (energy_bound ε hε h hh)] at hfg ⊢
  exact joint_closure ε δ v hε hδ h hh hne d l _ f g hfg

include hh hne in
theorem closed_domain (f : Hilbert)
    (hf : f ∈ (closedEnergy ε hε h d l mass2 quartic vacuum t).domain) :
    input ε δ v hε hδ f ∈ (closedEnergy ε hε h d l mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (closed_graph ε δ v hε hδ h hh hne d l mass2 quartic vacuum t f _
      ((closedEnergy ε hε h d l mass2 quartic vacuum t).mem_graph ⟨f,hf⟩))

theorem closed_action (f : (closedEnergy ε hε h d l mass2 quartic vacuum t).domain) :
    closedEnergy ε hε h d l mass2 quartic vacuum t
      ⟨input ε δ v hε hδ f,closed_domain ε δ v hε hδ h hh hne d l mass2 quartic vacuum t f f.property⟩ =
        transformedOutput ε δ v hε hδ h hh d (energyWeight mass2 quartic vacuum t) f
          (closedEnergy ε hε h d l mass2 quartic vacuum t f) :=
  (closedEnergy ε hε h d l mass2 quartic vacuum t).mem_graph_snd_inj'
    ((closedEnergy ε hε h d l mass2 quartic vacuum t).mem_graph _)
    (closed_graph ε δ v hε hδ h hh hne d l mass2 quartic vacuum t f _
      ((closedEnergy ε hε h d l mass2 quartic vacuum t).mem_graph f)) rfl

#print axioms factor_graph
#print axioms joint_graph
#print axioms joint_closure
#print axioms energy_bound
#print axioms closed_graph
#print axioms closed_domain
#print axioms closed_action

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedEnergy
