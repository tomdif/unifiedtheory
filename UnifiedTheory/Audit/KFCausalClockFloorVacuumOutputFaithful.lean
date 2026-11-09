/- The vacuum output of the actual closed joint energy graph cannot vanish
on a nonzero physical vector when the vacuum coupling is positive. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (inverseAction_ne_zero)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε : ℝ) (hε : 0 < ε)

theorem inverseL_eq_zero (f : Hilbert) (hf : inverseL ε hε f = 0) : f = 0 := by
  by_contra hn
  exact inverseAction_ne_zero ε hε f hn hf

theorem longitudinal_graph_zero (hbar a : ℝ) (f : Hilbert)
    (hf : (f,0) ∈ (longitudinalExponential ε hε hbar a).graph) : f = 0 := by
  have hi := (longitudinal_exponential_inverse ε hε hbar a f 0).mp hf
  exact (longitudinalExponential ε hε hbar (-a)).graph_fst_eq_zero_snd hi rfl

theorem ordered_graph_zero (hbar : ℝ) (f : Hilbert)
    (hf : (f,0) ∈ (orderedExponential ε hε hbar).graph) : f = 0 := by
  apply inverseL_eq_zero ε hε f
  exact longitudinal_graph_zero ε hε hbar (1/2) _ ((ordered_graph_iff ε hε hbar f 0).mp hf)

theorem vacuum_weight_ne_zero (mass2 quartic vacuum t : ℝ) (hv : 0 < vacuum) :
    energyWeight mass2 quartic vacuum t 7 ≠ 0 := by
  change ((Real.exp t*Real.sqrt vacuum:ℝ):ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (Real.exp_ne_zero t) (Real.sqrt_pos.mpr hv).ne')

theorem closedEnergy_vacuum_graph (hbar : ℝ) (hb : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ)
    (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph) :
    (energyWeight mass2 quartic vacuum t 7 • f,g 7) ∈ (orderedExponential ε hε hbar).graph := by
  have hc := closedEnergy_component_graph ε hε hbar v l mass2 quartic vacuum t hb f g hfg 7
  change (energyWeight mass2 quartic vacuum t 7 • f,g 7) ∈ (orderedExponential ε hε hbar).closure.graph at hc
  rw [← (orderedExponential_closed ε hε hbar).isClosable.graph_closure_eq_closure_graph,
    (orderedExponential_closed ε hε hbar).submodule_topologicalClosure_eq] at hc
  exact hc

theorem closedEnergy_vacuum_ne_zero (hbar : ℝ) (hb : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ)
    (hv : 0 < vacuum) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph) (hf : f ≠ 0) : g 7 ≠ 0 := by
  intro hg
  have hc := closedEnergy_vacuum_graph ε hε hbar hb v l mass2 quartic vacuum t f g hfg
  rw [hg] at hc
  have hz := ordered_graph_zero ε hε hbar _ hc
  exact hf ((smul_eq_zero.mp hz).resolve_left (vacuum_weight_ne_zero mass2 quartic vacuum t hv))

theorem form_vacuum_ne_zero (hbar : ℝ) (hb : |hbar| ≤ Real.pi*ε)
    (mass2 quartic vacuum t : ℝ) (hv : 0 < vacuum)
    (u : KFCausalClosedGraphForm.FormSpace
      (KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t))
    (hu : KFCausalClosedGraphForm.embedding
      (KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t) u ≠ 0) :
    KFCausalClosedGraphForm.energyOutput
      (KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t) u 7 ≠ 0 :=
  closedEnergy_vacuum_ne_zero ε hε hbar hb modelDirections pointField mass2 quartic vacuum t hv _ _ u.property hu

#print axioms inverseL_eq_zero
#print axioms longitudinal_graph_zero
#print axioms ordered_graph_zero
#print axioms vacuum_weight_ne_zero
#print axioms closedEnergy_vacuum_graph
#print axioms closedEnergy_vacuum_ne_zero
#print axioms form_vacuum_ne_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful
