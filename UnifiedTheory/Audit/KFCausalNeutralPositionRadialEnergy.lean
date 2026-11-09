/- The actual charge-compatible radial test preserves the simultaneous
closed eight-factor energy graph. All natural factor identities are derived
for the physical modelDirections and pointField, including the ordered
matter rows. No factor-domain preservation hypothesis is supplied. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialMatter
import UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialMatter
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (shifted)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialOrdered (ordered_graph_action)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap correctionMap)

variable (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
  (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3)

def factorOutput : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![action h δ v hδ,action h δ v hδ,action h δ v hδ,
    action h δ v hδ,action h δ v hδ,
    shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh),
    shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh),
    shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh)]

def factorCorrection : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![0,correction ε hε h δ v hδ 0,correction ε hε h δ v hδ 1,
    correction ε hε h δ v hδ 2,correction ε hε h δ v hδ 3,0,0,0]

variable (hne : h ≠ 0)

include hne in
theorem factor_graph (i : Fin 8) (f g : Hilbert)
    (hfg : (f,g) ∈ (energyFactor ε hε h modelDirections pointField i).graph) :
    (action h δ v hδ f,
      factorOutput ε δ v hε hδ h hh i g+factorCorrection ε δ v hε hδ h i f) ∈
        (energyFactor ε hε h modelDirections pointField i).graph := by
  fin_cases i
  · change (action h δ v hδ f,action h δ v hδ g+0) ∈ _
    rw [add_zero]
    exact clock_graph ε hε h δ v hδ f g hfg
  · exact kinetic_graph ε hε h δ v hδ hne 0 f g hfg
  · exact kinetic_graph ε hε h δ v hδ hne 1 f g hfg
  · exact kinetic_graph ε hε h δ v hδ hne 2 f g hfg
  · exact kinetic_graph ε hε h δ v hδ hne 3 f g hfg
  · change (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g+0) ∈ _
    rw [add_zero]
    exact linear_matter_graph_action ε h δ v hε hδ hh f g hfg
  · change (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g+0) ∈ _
    rw [add_zero]
    exact quadratic_matter_graph_action ε h δ v hε hδ hh f g hfg
  · change (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g+0) ∈ _
    rw [add_zero]
    exact ordered_graph_action ε h δ v hε hδ hh f g hfg

def transformedOutput (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert) :
    Output (Fin 8) Hilbert :=
  outputMap (factorOutput ε δ v hε hδ h hh) g+
    correctionMap (factorCorrection ε δ v hε hδ h) c f

include hne in
theorem joint_graph (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h modelDirections pointField) c) :
    (action h δ v hδ f,transformedOutput ε δ v hε hδ h hh c f g) ∈
      jointGraph (energyFactor ε hε h modelDirections pointField) c :=
  KFCausalJointGraphBoundedCorrection.joint_graph _ _ _ _
    (factor_graph ε δ v hε hδ h hh hne) c f g hfg

include hne in
theorem joint_closure (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h modelDirections pointField) c).topologicalClosure) :
    (action h δ v hδ f,transformedOutput ε δ v hε hδ h hh c f g) ∈
      (jointGraph (energyFactor ε hε h modelDirections pointField) c).topologicalClosure :=
  KFCausalJointGraphBoundedCorrection.joint_closure _ _ _ _
    (factor_graph ε δ v hε hδ h hh hne) c f g hfg

include hε hh in
theorem energy_bound : |h| ≤ Real.pi*ε := by nlinarith [Real.pi_pos]

variable (mass2 quartic vacuum t : ℝ)

include hne in
theorem closed_graph (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).graph) :
    (action h δ v hδ f,
      transformedOutput ε δ v hε hδ h hh (energyWeight mass2 quartic vacuum t) f g) ∈
        (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).graph := by
  rw [closedEnergy_graph ε hε h modelDirections pointField mass2 quartic vacuum t (energy_bound ε hε h hh)] at hfg ⊢
  exact joint_closure ε δ v hε hδ h hh hne _ f g hfg

include hh hne in
theorem closed_domain (f : Hilbert)
    (hf : f ∈ (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).domain) :
    action h δ v hδ f ∈ (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (closed_graph ε δ v hε hδ h hh hne mass2 quartic vacuum t f _
      ((closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph ⟨f,hf⟩))

theorem closed_action (f : (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).domain) :
    closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t
      ⟨action h δ v hδ f,closed_domain ε δ v hε hδ h hh hne mass2 quartic vacuum t f f.property⟩ =
        transformedOutput ε δ v hε hδ h hh (energyWeight mass2 quartic vacuum t) f
          (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t f) :=
  (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph_snd_inj'
    ((closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph _)
    (closed_graph ε δ v hε hδ h hh hne mass2 quartic vacuum t f _
      ((closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph f)) rfl

#print axioms factor_graph
#print axioms joint_graph
#print axioms joint_closure
#print axioms energy_bound
#print axioms closed_graph
#print axioms closed_domain
#print axioms closed_action

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy
