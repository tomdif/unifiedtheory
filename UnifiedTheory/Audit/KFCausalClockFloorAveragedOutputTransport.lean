/- Exact energy-output transport for the clock-floor circle average.
The map rescales the five time-dependent components pointwise in angle. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedTransport
import UnifiedTheory.Audit.KFCausalAveragedOutputTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (timeOutput)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTransport

def timeOutputLp (s t : ℝ) : Lp (Output (Fin 8) Hilbert) 2 angleMeasure →L[ℂ]
    Lp (Output (Fin 8) Hilbert) 2 angleMeasure := (timeOutput s t).compLpL 2 angleMeasure

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (hne : hbar ≠ 0)
  (mass2 quartic vacuum : ℝ)

local notation "D" t => KFCausalClockFloorFormHamiltonian.formData ε hε hbar hh mass2 quartic vacuum t
local notation "BaseSpace" t => KFCausalClosedGraphForm.FormSpace (D t)
local notation "J" t => KFCausalClosedGraphForm.embedding (D t)
local notation "A" t => KFCausalClosedGraphForm.energyOutput (D t)

theorem transfer_output (s t : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s) :
    energyOutput ε hε hbar hh hne mass2 quartic vacuum t
      (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u) =
        timeOutputLp s t (energyOutput ε hε hbar hh hne mass2 quartic vacuum s u) := by
  let R := KFCausalClockFloorFormTransport.formTransfer ε hε hbar hh mass2 quartic vacuum s t
  let v := sectionMap ε hε hbar hh hne mass2 quartic vacuum s u
  change (A t).compLp (sectionMap ε hε hbar hh hne mass2 quartic vacuum t
    (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u)) = (timeOutput s t).compLp ((A s).compLp v)
  rw [transfer_section]
  apply Lp.ext
  filter_upwards [(A t).coeFn_compLp (R.compLp v),R.coeFn_compLp v,
    (timeOutput s t).coeFn_compLp ((A s).compLp v),(A s).coeFn_compLp v] with θ h1 h2 h3 h4
  change (A t).compLp (R.compLp v) θ = (timeOutput s t).compLp ((A s).compLp v) θ
  rw [h1,h2,h3,h4]
  exact KFCausalClockFloorFormTransport.transfer_energyOutput ε hε hbar hh mass2 quartic vacuum s t (v θ)

theorem energy_form_graph (s : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s) :
    (embedding ε hε hbar hh hne mass2 quartic vacuum s u,
      energyOutput ε hε hbar hh hne mass2 quartic vacuum s u) ∈
        (energyOperator ε hε hbar hh hne mass2 quartic vacuum s).graph := by
  have h := KFCausalAveragedEnergyGraph.averagedOperator_form_graph
    (H := Hilbert) (E := BaseSpace s) (K := Output (Fin 8) Hilbert)
    (group hbar hne) (2*Real.pi) (J s) (A s)
  have hJ := KFCausalClosedGraphForm.embedding_injective (D s)
  exact h hJ u

theorem energy_graph_transport (s t : ℝ) (z : Hilbert × Lp (Output (Fin 8) Hilbert) 2 angleMeasure)
    (hz : z ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum s).graph) :
    (z.1,timeOutputLp s t z.2) ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).graph := by
  have hd := (energy_domain ε hε hbar hh hne mass2 quartic vacuum s z.1).mp
    (LinearPMap.mem_domain_of_mem_graph hz)
  rcases hd with ⟨u,hu⟩
  have ho := (energyOperator ε hε hbar hh hne mass2 quartic vacuum s).mem_graph_snd_inj'
    (energy_form_graph ε hε hbar hh hne mass2 quartic vacuum s u) hz hu
  have ht := energy_form_graph ε hε hbar hh hne mass2 quartic vacuum t
    (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u)
  have he := (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum s t u).trans hu
  have ho' := (transfer_output ε hε hbar hh hne mass2 quartic vacuum s t u).trans (congrArg (timeOutputLp s t) ho)
  exact (congrArg (fun w : Hilbert × Lp (Output (Fin 8) Hilbert) 2 angleMeasure =>
    w ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).graph) (Prod.ext he ho')).mp ht

#print axioms transfer_output
#print axioms energy_form_graph
#print axioms energy_graph_transport

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport
