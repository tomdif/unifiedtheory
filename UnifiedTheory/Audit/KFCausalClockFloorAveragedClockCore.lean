/- Clock-composition cores for the actual charge-averaged form and energy
operator. Approximation is in the form or energy graph norm, not the
Hamiltonian operator graph norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedResponseDecay
import UnifiedTheory.Audit.KFCausalEmbeddedClockCore
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedClockCore
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
open UnifiedTheory.Audit.KFCausalClockFloorAveragedResponseDecay
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalInvariantRangeCore

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hb" => KFCausalClockFloorClosedEnergyDefect.energy_bound ε hε h hh
local notation "BaseData" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb mass2 quartic vacuum t
local notation "𝒱" => AveragedSpace ε hε h hb hne mass2 quartic vacuum t
local notation "J" => embedding ε hε h hb hne mass2 quartic vacuum t
local notation "A" => energyOutput ε hε h hb hne mass2 quartic vacuum t
local notation "𝒦" => energyOperator ε hε h hb hne mass2 quartic vacuum t
local notation "F" => formAction ε hε h hne hh mass2 quartic vacuum t
local notation "D" => defectOperator ε hε
local notation "R" => outputAction ε hε h hh
local notation "L" => ContinuousLinearMap.compLpL 2 angleMeasure R
local notation "Y" => Lp (Output (Fin 8) Hilbert) 2 angleMeasure

def formCore : Set 𝒱 := Set.range F

theorem formCore_iff (u : 𝒱) : u ∈ formCore ε hε h hne hh mass2 quartic vacuum t ↔
    ∃ v : 𝒱, (J u,J v) ∈ (clockOperator ε hε).graph :=
  KFCausalEmbeddedClockCore.clock_range_iff J F D (clockOperator ε hε) (ε:ℂ)
    (Complex.ofReal_ne_zero.mpr hε.ne') (embedding_injective ε hε h hb hne mass2 quartic vacuum t)
    (formAction_embedding ε hε h hne hh mass2 quartic vacuum t)
    (clock_defect_graph ε hε) (defect_clock ε hε) u

theorem formCore_dense : Dense (formCore ε hε h hne hh mass2 quartic vacuum t) :=
  KFCausalEmbeddedClockCore.range_dense F (form_residual_decay ε hε h hne hh mass2 quartic vacuum t)

theorem form_approximation (u : 𝒱) :
    (∀ n, F (geometricSum F u n) ∈ formCore ε hε h hne hh mass2 quartic vacuum t) ∧
      Tendsto (fun n => F (geometricSum F u n)) atTop (𝓝 u) :=
  KFCausalEmbeddedClockCore.approximation F (form_residual_decay ε hε h hne hh mass2 quartic vacuum t) u

theorem energy_graph_iff (f : Hilbert) (g : Y) :
    (f,g) ∈ (𝒦).graph ↔ ∃ u : 𝒱, J u = f ∧ A u = g := by
  have he := KFCausalAveragedEnergyGraph.averagedOperator_graph
    (H := Hilbert) (E := KFCausalClosedGraphForm.FormSpace BaseData) (K := Output (Fin 8) Hilbert)
    (KFCausalPhysicalCircleAction.group h hne) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding BaseData) (KFCausalClosedGraphForm.energyOutput BaseData)
    (KFCausalClosedGraphForm.embedding_injective BaseData)
  constructor
  · intro hfg
    have hi := he ▸ hfg
    rcases hi with ⟨u,hu⟩
    exact ⟨u,congrArg Prod.fst hu,congrArg Prod.snd hu⟩
  · rintro ⟨u,rfl,rfl⟩
    exact KFCausalAveragedEnergyGraph.averagedOperator_form_graph _ _ _ _
      (KFCausalClosedGraphForm.embedding_injective BaseData) u

theorem energy_graph_defect (f : Hilbert) (g : Y) (hfg : (f,g) ∈ (𝒦).graph) :
    (D f,L g) ∈ (𝒦).graph := by
  obtain ⟨u,rfl,rfl⟩ := (energy_graph_iff ε hε h hne hh mass2 quartic vacuum t f g).mp hfg
  exact (energy_graph_iff ε hε h hne hh mass2 quartic vacuum t _ _).mpr
    ⟨F u,formAction_embedding ε hε h hne hh mass2 quartic vacuum t u,
      formAction_output ε hε h hne hh mass2 quartic vacuum t u⟩

def graphAction : Hilbert × Y →L[ℂ] Hilbert × Y := (D).prodMap L

theorem graphAction_decay (z : Hilbert × Y) :
    Tendsto (fun n : ℕ => (residual (graphAction ε hε h hh) : Hilbert × Y → Hilbert × Y)^[n] z)
      atTop (𝓝 0) :=
  prod_residual_tendsto D L z.1 z.2 (KFCausalClockFloorDefectPowerDecay.real_response_decay ε hε z.1)
    (outputLp_residual_decay ε hε h hh z.2)

def clockDomain : Set Hilbert := D '' ((𝒦).domain : Set Hilbert)

theorem clockDomain_iff (f : Hilbert) : f ∈ clockDomain ε hε h hne hh mass2 quartic vacuum t ↔
    ∃ cf : Hilbert, (f,cf) ∈ (clockOperator ε hε).graph ∧ cf ∈ (𝒦).domain := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(ε:ℂ) • u,clock_defect_graph ε hε u,(𝒦).domain.smul_mem _ hu⟩
  · rintro ⟨cf,hc,hK⟩
    refine ⟨(ε:ℂ)⁻¹ • cf,(𝒦).domain.smul_mem _ hK,?_⟩
    rw [map_smul,defect_clock ε hε f cf hc,smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul]

theorem graph_image_iff (f : Hilbert) (g : Y) :
    (f,g) ∈ (𝒦).graph.map (graphAction ε hε h hh).toLinearMap ↔
      (f,g) ∈ (𝒦).graph ∧ f ∈ clockDomain ε hε h hne hh mass2 quartic vacuum t := by
  constructor
  · rintro ⟨⟨u,w⟩,hu,he⟩
    have h1 : D u = f := congrArg Prod.fst he
    have h2 : L w = g := congrArg Prod.snd he
    have hg := energy_graph_defect ε hε h hne hh mass2 quartic vacuum t u w hu
    rw [h1,h2] at hg
    exact ⟨hg,u,LinearPMap.mem_domain_of_mem_graph hu,h1⟩
  · rintro ⟨hfg,u,hu,he⟩
    let w := 𝒦 ⟨u,hu⟩
    have hw : (u,w) ∈ (𝒦).graph := (𝒦).mem_graph ⟨u,hu⟩
    have ht := energy_graph_defect ε hε h hne hh mass2 quartic vacuum t u w hw
    rw [he] at ht
    have hout : L w = g := (𝒦).mem_graph_snd_inj' ht hfg rfl
    exact ⟨(u,w),hw,Prod.ext he hout⟩

theorem clock_graph_core :
    ((𝒦).graph.map (graphAction ε hε h hh).toLinearMap).topologicalClosure = (𝒦).graph :=
  (range_core (graphAction ε hε h hh) (𝒦).graph
    (fun z hz => energy_graph_defect ε hε h hne hh mass2 quartic vacuum t z.1 z.2 hz)
    (fun z _ => graphAction_decay ε hε h hh z)).trans
      (energy_closed ε hε h hb hne mass2 quartic vacuum t).submodule_topologicalClosure_eq

theorem energy_approximation (f : Hilbert) (g : Y) (hfg : (f,g) ∈ (𝒦).graph) :
    ∃ z : ℕ → Hilbert × Y,
      (∀ n, z n ∈ (𝒦).graph ∧ (z n).1 ∈ clockDomain ε hε h hne hh mass2 quartic vacuum t) ∧
        Tendsto z atTop (𝓝 (f,g)) := by
  let P := graphAction ε hε h hh
  have hp : ∀ z ∈ (𝒦).graph, P z ∈ (𝒦).graph :=
    fun z hz => energy_graph_defect ε hε h hne hh mass2 quartic vacuum t z.1 z.2 hz
  refine ⟨fun n => P (geometricSum P (f,g) n),?_,
    approximation_tendsto P (f,g) (graphAction_decay ε hε h hh (f,g))⟩
  intro n
  apply (graph_image_iff ε hε h hne hh mass2 quartic vacuum t _ _).mp
  exact ⟨geometricSum P (f,g) n,geometricSum_mem P (𝒦).graph hp (f,g) hfg n,rfl⟩

#print axioms formCore_iff
#print axioms formCore_dense
#print axioms form_approximation
#print axioms energy_graph_iff
#print axioms energy_graph_defect
#print axioms graphAction_decay
#print axioms clockDomain_iff
#print axioms graph_image_iff
#print axioms clock_graph_core
#print axioms energy_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedClockCore
