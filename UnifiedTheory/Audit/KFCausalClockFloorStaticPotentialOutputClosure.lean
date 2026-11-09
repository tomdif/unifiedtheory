/- The literal original static and ordered-potential rows, with their
actual time weights, are closed on the original interacting reference
sources. The omitted rows are precisely the two radial kinetic rows.
Closed primitive orbit graphs prove that the closure is an operator. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialOutputClosure

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialOutputClosure
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorOrbitFactorGraphs
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalUnitIntervalOrbit (angleMeasure)

def retained (i : Fin 8) : Prop := (i.val < 3) ∨ (5 ≤ i.val)
instance (i : Fin 8) : Decidable (retained i) := inferInstanceAs (Decidable ((i.val < 3) ∨ (5 ≤ i.val)))
def selectedOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  KFCausalFiniteOutputRescaling.selected retained
def selectedOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  selectedOutput.compLpL 2 angleMeasure

theorem selected_coordinate (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (selectedOutputLp y)=if retained i then coordinateLp i y else 0 := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (selectedOutputLp y),
    selectedOutput.coeFn_compLp y,(coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (selectedOutputLp y) θ=_
  rw [h1]
  change selectedOutput.compLp y θ i=_
  rw [h2]
  by_cases hi : retained i
  · simpa only [selectedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,if_true] using h3.symm
  · simp only [selectedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,if_false,h0,Pi.zero_apply]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "V" => FormSpace ε hε h hh hb m g k 0
local notation "J" => embedding ε hε h hh hb m g k 0
local notation "A" => energyOutput ε hε h hh hb m g k 0
local notation "R" => physicalOrbit h hh

def sourceMap : V →L[ℂ] EnergyOutputSpace :=
  selectedOutputLp.comp ((timeOutputLp 0 t).comp A)
def initialGraph : Submodule ℂ (Hilbert × EnergyOutputSpace) :=
  ((J).prod (sourceMap ε hε h hh hb m g k t)).toLinearMap.range

private theorem source_component (u : V) (i : Fin 8) :
    (R ((if retained i then energyWeight m g k t i else 0) • J u),
      coordinateLp i (sourceMap ε hε h hh hb m g k t u)) ∈
        (factorOperator ε hε h i).graph := by
  have hg := factor_graph ε hε h hh hb m g k t
    (formTransfer ε hε h hh hb m g k 0 t u) i
  have hin := congrArg (fun f : Hilbert => R (energyWeight m g k t i • f))
    (transfer_embedding ε hε h hh hb m g k 0 t u)
  have hout := congrArg (coordinateLp i) (transfer_energyOutput ε hε h hh hb m g k 0 t u)
  have hg' := (congrArg₂ (fun f z => (f,z) ∈ (factorOperator ε hε h i).graph) hin hout).mp hg
  change (R ((if retained i then energyWeight m g k t i else 0) • J u),
    coordinateLp i (selectedOutputLp (timeOutputLp 0 t (A u)))) ∈ _
  rw [selected_coordinate]
  by_cases hi : retained i
  · simpa only [hi,if_true] using hg'
  · simpa only [hi,if_false,zero_smul,map_zero] using (factorOperator ε hε h i).graph.zero_mem

private theorem closure_component (z : Hilbert × EnergyOutputSpace)
    (hz : z ∈ (initialGraph ε hε h hh hb m g k t).topologicalClosure) (i : Fin 8) :
    (R ((if retained i then energyWeight m g k t i else 0) • z.1),coordinateLp i z.2) ∈
      (factorOperator ε hε h i).graph := by
  have hc : IsClosed {z : Hilbert × EnergyOutputSpace |
      (R ((if retained i then energyWeight m g k t i else 0) • z.1),coordinateLp i z.2) ∈
        (factorOperator ε hε h i).graph} :=
    (factorOperator_closed ε hε h (hamiltonian_bound ε h hb) i).preimage
      (((R).continuous.comp (continuous_const.smul continuous_fst)).prodMk
        ((coordinateLp i).continuous.comp continuous_snd))
  apply closure_minimal (t := {z : Hilbert × EnergyOutputSpace |
      (R ((if retained i then energyWeight m g k t i else 0) • z.1),coordinateLp i z.2) ∈
        (factorOperator ε hε h i).graph}) ?_ hc
    (by simpa only [Submodule.topologicalClosure_coe] using hz)
  rintro z ⟨u,rfl⟩
  exact source_component ε hε h hh hb m g k t u i

private theorem closure_vertical_zero (z : Hilbert × EnergyOutputSpace)
    (hz : z ∈ (initialGraph ε hε h hh hb m g k t).topologicalClosure) (hzero : z.1=0) : z.2=0 := by
  apply coordinates_detect_zero
  intro i
  exact (factorOperator ε hε h i).graph_fst_eq_zero_snd
    (closure_component ε hε h hh hb m g k t z hz i) (by simp only [hzero,smul_zero,map_zero])

def operator : Hilbert →ₗ.[ℂ] EnergyOutputSpace :=
  (initialGraph ε hε h hh hb m g k t).topologicalClosure.toLinearPMap

theorem operator_graph : (operator ε hε h hh hb m g k t).graph=
    (initialGraph ε hε h hh hb m g k t).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (closure_vertical_zero ε hε h hh hb m g k t)

theorem operator_closed : (operator ε hε h hh hb m g k t).IsClosed := by
  rw [LinearPMap.IsClosed,operator_graph]
  exact (initialGraph ε hε h hh hb m g k t).isClosed_topologicalClosure

theorem reference_graph (u : V) :
    (J u,sourceMap ε hε h hh hb m g k t u) ∈ (operator ε hε h hh hb m g k t).graph := by
  rw [operator_graph]
  exact (initialGraph ε hε h hh hb m g k t).le_topologicalClosure ⟨u,rfl⟩

theorem operator_dense : Dense ((operator ε hε h hh hb m g k t).domain : Set Hilbert) := by
  have hd := KFCausalClosedGraphForm.embedding_dense
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k 0)
  apply hd.mono
  rintro f ⟨u,rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (reference_graph ε hε h hh hb m g k t u)

#print axioms selected_coordinate
#print axioms operator_graph
#print axioms operator_closed
#print axioms reference_graph
#print axioms operator_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialOutputClosure
