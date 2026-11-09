/- Close the three ORIGINAL ordered-potential output rows on the actual
interacting reference form. The closed orbit-factor graphs exclude vertical
limits even at zero couplings. Projection of the actual growing closure
lands in this literal potential closure; no maximal-domain intersection
or independent potential moment is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorGrowingEnergySplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialOutputClosure
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity (growingMap)
open KFCausalClockFloorOrbitFactorGraphs
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem projection_closure {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (S : Submodule ℂ (X × Y)) (T : Submodule ℂ (X × Z))
    (L : Y →L[ℂ] Z) (hT : IsClosed (T : Set (X × Z)))
    (hS : ∀ z ∈ S, (z.1,L z.2) ∈ T) (z : X × Y) (hz : z ∈ S.topologicalClosure) :
    (z.1,L z.2) ∈ T := by
  let F : X × Y →L[ℂ] X × Z := (ContinuousLinearMap.id ℂ X).prodMap L
  have hs : S ≤ T.comap F.toLinearMap := hS
  exact S.topologicalClosure_minimal hs (hT.preimage F.continuous) hz

private theorem coordinate_ordered (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (orderedOutputLp y)=if i.val<5 then 0 else coordinateLp i y := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (orderedOutputLp y),
    orderedOutput.coeFn_compLp y,(coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (orderedOutputLp y) θ=_
  rw [h1]
  change orderedOutput.compLp y θ i=_
  rw [h2]
  by_cases hi : i.val<5
  · simp only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_true_eq_false,if_false,if_true,h0,Pi.zero_apply]
  · simpa only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_false_eq_true,if_true,if_false] using h3.symm

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hh hb m g k 0
local notation "J" => embedding ε hε h hh hb m g k 0
local notation "B" => growingMap ε hε h hh hb m g k
local notation "R" => physicalOrbit h hh

def potentialMap : V →L[ℂ] EnergyOutputSpace := orderedOutputLp.comp B
def initialGraph : Submodule ℂ (Hilbert × EnergyOutputSpace) :=
  ((J).prod (potentialMap ε hε h hh hb m g k)).toLinearMap.range

private theorem closure_component (z : Hilbert × EnergyOutputSpace)
    (hz : z ∈ (initialGraph ε hε h hh hb m g k).topologicalClosure) (i : Fin 8) :
    (R ((if i.val<5 then 0 else growingWeight m g k i) • z.1),coordinateLp i z.2) ∈
      (factorOperator ε hε h i).graph := by
  have hc : IsClosed {z : Hilbert × EnergyOutputSpace |
      (R ((if i.val<5 then 0 else growingWeight m g k i) • z.1),coordinateLp i z.2) ∈
        (factorOperator ε hε h i).graph} :=
    (factorOperator_closed ε hε h (hamiltonian_bound ε h hb) i).preimage
      (((R).continuous.comp (continuous_const.smul continuous_fst)).prodMk
        ((coordinateLp i).continuous.comp continuous_snd))
  apply closure_minimal (t := {z : Hilbert × EnergyOutputSpace |
      (R ((if i.val<5 then 0 else growingWeight m g k i) • z.1),coordinateLp i z.2) ∈
        (factorOperator ε hε h i).graph}) ?_ hc
    (by simpa only [Submodule.topologicalClosure_coe] using hz)
  rintro z ⟨u,rfl⟩
  change (R ((if i.val<5 then 0 else growingWeight m g k i) • J u),
    coordinateLp i (orderedOutputLp (B u))) ∈ (factorOperator ε hε h i).graph
  rw [coordinate_ordered]
  by_cases hi : i.val<5
  · simpa only [hi,if_true,zero_smul,map_zero] using (factorOperator ε hε h i).graph.zero_mem
  · simpa only [hi,if_false] using growing_factor_graph ε hε h hh hb m g k u i

private theorem closure_vertical_zero (z : Hilbert × EnergyOutputSpace)
    (hz : z ∈ (initialGraph ε hε h hh hb m g k).topologicalClosure) (hzero : z.1=0) : z.2=0 := by
  apply coordinates_detect_zero
  intro i
  exact (factorOperator ε hε h i).graph_fst_eq_zero_snd
    (closure_component ε hε h hh hb m g k z hz i) (by simp only [hzero,smul_zero,map_zero])

def operator : Hilbert →ₗ.[ℂ] EnergyOutputSpace :=
  (initialGraph ε hε h hh hb m g k).topologicalClosure.toLinearPMap

theorem operator_graph : (operator ε hε h hh hb m g k).graph=
    (initialGraph ε hε h hh hb m g k).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (closure_vertical_zero ε hε h hh hb m g k)

theorem operator_closed : (operator ε hε h hh hb m g k).IsClosed := by
  rw [LinearPMap.IsClosed,operator_graph]
  exact (initialGraph ε hε h hh hb m g k).isClosed_topologicalClosure

theorem reference_graph (u : V) :
    (J u,potentialMap ε hε h hh hb m g k u) ∈ (operator ε hε h hh hb m g k).graph := by
  rw [operator_graph]
  exact (initialGraph ε hε h hh hb m g k).le_topologicalClosure ⟨u,rfl⟩

theorem operator_dense : Dense ((operator ε hε h hh hb m g k).domain : Set Hilbert) := by
  have hd := KFCausalClosedGraphForm.embedding_dense
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k 0)
  apply hd.mono
  rintro f ⟨u,rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (reference_graph ε hε h hh hb m g k u)

theorem growing_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hb m g k).graph) :
    (f,orderedOutputLp z) ∈ (operator ε hε h hh hb m g k).graph := by
  have hs : ∀ z ∈ KFCausalClockFloorGrowingOutputClosure.initialGraph ε hε h hh hb m g k,
      (z.1,orderedOutputLp z.2) ∈ (operator ε hε h hh hb m g k).graph := by
    rintro z ⟨u,rfl⟩
    exact reference_graph ε hε h hh hb m g k u
  have hz' : (f,z) ∈ (KFCausalClockFloorGrowingOutputClosure.initialGraph ε hε h hh hb m g k).topologicalClosure := by
    rwa [← KFCausalClockFloorGrowingOutputClosure.operator_graph]
  exact projection_closure
    (KFCausalClockFloorGrowingOutputClosure.initialGraph ε hε h hh hb m g k)
    (operator ε hε h hh hb m g k).graph orderedOutputLp
    (operator_closed ε hε h hh hb m g k) hs (f,z) hz'

#print axioms operator_graph
#print axioms operator_closed
#print axioms reference_graph
#print axioms operator_dense
#print axioms growing_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialOutputClosure
