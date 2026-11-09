/- For the revised clock-floor model, the natural weighted joint graph for the eight unaveraged factors.
Its closure is an actual densely defined closed operator. The explicit
energy identity retains the original order of every factor. -/
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
import UnifiedTheory.Audit.KFCausalClockFloorMatterClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight energyWeight_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDensity (commonEnergyDomain_dense)
open UnifiedTheory.Audit.KFCausalClockFloorMatterClosure (energyFactor_closable)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
  (mass2 quartic vacuum t : ℝ)

def initialEnergy : Hilbert →ₗ.[ℂ] Output (Fin 8) Hilbert :=
  jointInitial (energyFactor ε hε hbar v l) (energyWeight mass2 quartic vacuum t)

def closedEnergy : Hilbert →ₗ.[ℂ] Output (Fin 8) Hilbert :=
  jointClosed (energyFactor ε hε hbar v l) (energyWeight mass2 quartic vacuum t)

theorem initialEnergy_domain (f : Hilbert) :
    f ∈ (initialEnergy ε hε hbar v l mass2 quartic vacuum t).domain ↔
      ∀ i, energyWeight mass2 quartic vacuum t i • f ∈ (energyFactor ε hε hbar v l i).domain :=
  joint_domain _ _ f

theorem initialEnergy_dense (hh : |hbar| ≤ Real.pi*ε) :
    Dense ((initialEnergy ε hε hbar v l mass2 quartic vacuum t).domain : Set Hilbert) :=
  joint_dense _ _ (commonEnergyDomain_dense ε hbar hε hh v l)

theorem initialEnergy_closable (hh : |hbar| ≤ Real.pi*ε) :
    (initialEnergy ε hε hbar v l mass2 quartic vacuum t).IsClosable :=
  joint_closable _ _ (energyFactor_closable ε hbar hε hh v l)

theorem closedEnergy_graph (hh : |hbar| ≤ Real.pi*ε) :
    (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph =
      (jointGraph (energyFactor ε hε hbar v l) (energyWeight mass2 quartic vacuum t)).topologicalClosure :=
  joint_closed_graph _ _ (energyFactor_closable ε hbar hε hh v l)

theorem closedEnergy_closed (hh : |hbar| ≤ Real.pi*ε) :
    (closedEnergy ε hε hbar v l mass2 quartic vacuum t).IsClosed :=
  joint_closed _ _ (energyFactor_closable ε hbar hε hh v l)

theorem closedEnergy_dense (hh : |hbar| ≤ Real.pi*ε) :
    Dense ((closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain : Set Hilbert) :=
  joint_closed_dense _ _ (energyFactor_closable ε hbar hε hh v l)
    (commonEnergyDomain_dense ε hbar hε hh v l)

theorem initialEnergy_le_closedEnergy (hh : |hbar| ≤ Real.pi*ε) :
    initialEnergy ε hε hbar v l mass2 quartic vacuum t ≤ closedEnergy ε hε hbar v l mass2 quartic vacuum t :=
  joint_initial_le_closed _ _ (energyFactor_closable ε hbar hε hh v l)

theorem closedEnergy_component_graph (hh : |hbar| ≤ Real.pi*ε)
    (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph) (i : Fin 8) :
    (energyWeight mass2 quartic vacuum t i • f,g i) ∈ (energyFactor ε hε hbar v l i).closure.graph := by
  rw [closedEnergy_graph ε hε hbar v l mass2 quartic vacuum t hh] at hfg
  exact closure_component_graph _ _ (energyFactor_closable ε hbar hε hh v l) (f,g) hfg i

def jointOutput (f : commonEnergyDomain ε hε hbar v l) : Output (Fin 8) Hilbert :=
  commonOutput (energyFactor ε hε hbar v l) (energyWeight mass2 quartic vacuum t) f

theorem jointOutput_initial_graph (f : commonEnergyDomain ε hε hbar v l) :
    ((f:Hilbert),jointOutput ε hε hbar v l mass2 quartic vacuum t f) ∈
      (initialEnergy ε hε hbar v l mass2 quartic vacuum t).graph := commonOutput_graph _ _ f

theorem jointOutput_closed_graph (hh : |hbar| ≤ Real.pi*ε) (f : commonEnergyDomain ε hε hbar v l) :
    ((f:Hilbert),jointOutput ε hε hbar v l mass2 quartic vacuum t f) ∈
      (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph :=
  LinearPMap.le_graph_of_le (initialEnergy_le_closedEnergy ε hε hbar v l mass2 quartic vacuum t hh)
    (jointOutput_initial_graph ε hε hbar v l mass2 quartic vacuum t f)

def factorValue (f : commonEnergyDomain ε hε hbar v l) (i : Fin 8) : Hilbert :=
  energyFactor ε hε hbar v l i ⟨f,(Submodule.mem_iInf _).mp f.property i⟩

def seedEnergy (f : commonEnergyDomain ε hε hbar v l) : ℝ :=
  (‖factorValue ε hε hbar v l f 0‖^2+‖factorValue ε hε hbar v l f 1‖^2+
    ‖factorValue ε hε hbar v l f 2‖^2)/2 +
  Real.exp (2*t)*((‖factorValue ε hε hbar v l f 3‖^2+‖factorValue ε hε hbar v l f 4‖^2)/2+
    mass2/2*‖factorValue ε hε hbar v l f 5‖^2+
    quartic/4*‖factorValue ε hε hbar v l f 6‖^2+
    vacuum*‖factorValue ε hε hbar v l f 7‖^2)

theorem jointOutput_norm_seedEnergy (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (f : commonEnergyDomain ε hε hbar v l) :
    ‖jointOutput ε hε hbar v l mass2 quartic vacuum t f‖^2=seedEnergy ε hε hbar v l mass2 quartic vacuum t f := by
  rw [jointOutput,commonOutput_norm]
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  change (∑ i : Fin 8, _*‖factorValue ε hε hbar v l f i‖^2)=_
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,seedEnergy]
  generalize hF : factorValue ε hε hbar v l f = F
  ring!

#print axioms initialEnergy_domain
#print axioms initialEnergy_dense
#print axioms initialEnergy_closable
#print axioms closedEnergy_graph
#print axioms closedEnergy_closed
#print axioms closedEnergy_dense
#print axioms initialEnergy_le_closedEnergy
#print axioms closedEnergy_component_graph
#print axioms jointOutput_initial_graph
#print axioms jointOutput_closed_graph
#print axioms jointOutput_norm_seedEnergy

end
end UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
