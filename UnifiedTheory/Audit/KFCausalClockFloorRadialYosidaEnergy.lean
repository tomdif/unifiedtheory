/- The rational radial Yosida action preserves the literal simultaneous
weighted eight-factor graph and its closure. The bounded correction is
confined to the two static symmetric rows; zero couplings require no
unweighted factor domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaKinetics
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOrderedTransport
import UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalClockFloorRadialYosidaKinetics
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaOrderedTransport (shifted shift_bound
  ordered_graph_action linear_matter_graph_action quadratic_matter_graph_action)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalJointGraphBoundedCorrection (outputMap correctionMap)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3)

def factorOutput : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![action ε hε h N hN,action ε hε h N hN,action ε hε h N hN,
    action ε hε h N hN,action ε hε h N hN,
    shifted ε hε h N hN (-h/2) (shift_bound ε h hb),
    shifted ε hε h N hN (-h/2) (shift_bound ε h hb),
    shifted ε hε h N hN (-h/2) (shift_bound ε h hb)]

def factorCorrection : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![0,correction ε hε h N hN 0,correction ε hε h N hN 1,
    correction ε hε h N hN 2,correction ε hε h N hN 3,0,0,0]

variable (hne : h ≠ 0)

include hne in
theorem factor_graph (i : Fin 8) (f g : Hilbert)
    (hfg : (f,g) ∈ (energyFactor ε hε h modelDirections pointField i).graph) :
    (action ε hε h N hN f,
      factorOutput ε hε h N hN hb i g+factorCorrection ε hε h N hN i f) ∈
        (energyFactor ε hε h modelDirections pointField i).graph := by
  fin_cases i
  · change (action ε hε h N hN f,action ε hε h N hN g+0) ∈ _
    rw [add_zero]
    exact clock_graph ε hε h N hN f g hfg
  · exact kinetic_graph ε hε h N hN hne 0 f g hfg
  · exact kinetic_graph ε hε h N hN hne 1 f g hfg
  · exact kinetic_graph ε hε h N hN hne 2 f g hfg
  · exact kinetic_graph ε hε h N hN hne 3 f g hfg
  · change (action ε hε h N hN f,shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g+0) ∈ _
    rw [add_zero]
    exact linear_matter_graph_action ε hε h N hN hb f g hfg
  · change (action ε hε h N hN f,shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g+0) ∈ _
    rw [add_zero]
    exact quadratic_matter_graph_action ε hε h N hN hb f g hfg
  · change (action ε hε h N hN f,shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g+0) ∈ _
    rw [add_zero]
    exact ordered_graph_action ε hε h N hN hb f g hfg

def transformedOutput (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert) :
    Output (Fin 8) Hilbert :=
  outputMap (factorOutput ε hε h N hN hb) g+
    correctionMap (factorCorrection ε hε h N hN) c f

include hne in
theorem joint_graph (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h modelDirections pointField) c) :
    (action ε hε h N hN f,transformedOutput ε hε h N hN hb c f g) ∈
      jointGraph (energyFactor ε hε h modelDirections pointField) c :=
  KFCausalJointGraphBoundedCorrection.joint_graph _ _ _ _
    (factor_graph ε hε h N hN hb hne) c f g hfg

include hne in
theorem joint_closure (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h modelDirections pointField) c).topologicalClosure) :
    (action ε hε h N hN f,transformedOutput ε hε h N hN hb c f g) ∈
      (jointGraph (energyFactor ε hε h modelDirections pointField) c).topologicalClosure :=
  KFCausalJointGraphBoundedCorrection.joint_closure _ _ _ _
    (factor_graph ε hε h N hN hb hne) c f g hfg

include hε hb in
theorem energy_bound : |h| ≤ Real.pi*ε := by nlinarith [Real.pi_pos]

variable (mass2 quartic vacuum t : ℝ)

include hne in
theorem closed_graph (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).graph) :
    (action ε hε h N hN f,
      transformedOutput ε hε h N hN hb (energyWeight mass2 quartic vacuum t) f g) ∈
        (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).graph := by
  rw [closedEnergy_graph ε hε h modelDirections pointField mass2 quartic vacuum t (energy_bound ε hε h hb)] at hfg ⊢
  exact joint_closure ε hε h N hN hb hne _ f g hfg

include hb hne in
theorem closed_domain (f : Hilbert)
    (hf : f ∈ (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).domain) :
    action ε hε h N hN f ∈ (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (closed_graph ε hε h N hN hb hne mass2 quartic vacuum t f _
      ((closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph ⟨f,hf⟩))

theorem closed_action (f : (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).domain) :
    closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t
      ⟨action ε hε h N hN f,closed_domain ε hε h N hN hb hne mass2 quartic vacuum t f f.property⟩ =
        transformedOutput ε hε h N hN hb (energyWeight mass2 quartic vacuum t) f
          (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t f) :=
  (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph_snd_inj'
    ((closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph _)
    (closed_graph ε hε h N hN hb hne mass2 quartic vacuum t f _
      ((closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).mem_graph f)) rfl

#print axioms factor_graph
#print axioms joint_graph
#print axioms joint_closure
#print axioms energy_bound
#print axioms closed_graph
#print axioms closed_domain
#print axioms closed_action

end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaEnergy
