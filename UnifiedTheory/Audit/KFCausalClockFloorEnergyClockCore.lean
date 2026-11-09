/- Clock-composition cores for the actual completed energy operator.
The natural weighted graph is treated without requiring nonzero weights.
Both state and energy output converge, and the completed forward clock
composition has the same explicit component commutator. This is not a
graph-core or dynamics theorem for the Hamiltonian K* K. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
import UnifiedTheory.Audit.KFCausalClockFloorClosedEnergyDefect
import UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorEnergyClockCore
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorClosedEnergyDefect
open UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator (factorDifference factorDifference_norm clock_factorAction_graph)
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
open UnifiedTheory.Audit.KFCausalInvariantRangeCore

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ)

def energyGraphAction : Hilbert × Output (Fin 8) Hilbert →L[ℂ] Hilbert × Output (Fin 8) Hilbert :=
  (defectOperator ε hε).prodMap (outputAction ε hε h hh)

theorem energyAction_decay (z : Hilbert × Output (Fin 8) Hilbert) :
    Tendsto (fun n : ℕ => (residual (energyGraphAction ε hε h hh) :
      Hilbert × Output (Fin 8) Hilbert → Hilbert × Output (Fin 8) Hilbert)^[n] z) atTop (𝓝 0) :=
  prod_residual_tendsto _ _ z.1 z.2 (real_response_decay ε hε z.1) (output_response_decay ε hε h hh z.2)

def naturalClockGraph (c : Fin 8 → ℂ) : Submodule ℂ (Hilbert × Output (Fin 8) Hilbert) :=
  (jointGraph (energyFactor ε hε h v l) c).map (energyGraphAction ε hε h hh).toLinearMap

theorem natural_clock_core (c : Fin 8 → ℂ) :
    (naturalClockGraph ε hε h hh v l c).topologicalClosure =
      (jointGraph (energyFactor ε hε h v l) c).topologicalClosure :=
  range_core (energyGraphAction ε hε h hh) (jointGraph (energyFactor ε hε h v l) c)
    (fun z hz => jointGraph_defect ε hε h hh v l c z.1 z.2 hz)
    (fun z _ => energyAction_decay ε hε h hh z)

/-- A common construction for either the natural or the completed graph. -/
theorem clock_graphs (K : Submodule ℂ (Hilbert × Output (Fin 8) Hilbert))
    (hK : ∀ z ∈ K, energyGraphAction ε hε h hh z ∈ K) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ K.map (energyGraphAction ε hε h hh).toLinearMap) :
    ∃ (cf : Hilbert) (tcf : Output (Fin 8) Hilbert) (ctf : Fin 8 → Hilbert),
      (f,cf) ∈ (clockOperator ε hε).graph ∧ (f,g) ∈ K ∧ (cf,tcf) ∈ K ∧
      ∀ i, (g i,ctf i) ∈ (clockOperator ε hε).graph ∧
        ctf i-tcf i = factorDifference ε hε h hh i (g i) ∧
        ‖ctf i-tcf i‖ ≤ |h| * ‖g i‖ := by
  rcases hfg with ⟨⟨u,w⟩,huw,he⟩
  have hf : defectOperator ε hε u = f := congrArg Prod.fst he
  have hg : outputAction ε hε h hh w = g := congrArg Prod.snd he
  subst f
  subst g
  refine ⟨(ε:ℂ) • u,(ε:ℂ) • w,
    (fun i => (ε:ℂ) • w i+factorDifference ε hε h hh i (factorAction ε hε h hh i (w i))),
    clock_defect_graph ε hε u,hK (u,w) huw,K.smul_mem (ε:ℂ) huw,?_⟩
  intro i
  refine ⟨clock_factorAction_graph ε hε h hh i (w i),?_,?_⟩
  · simp only [PiLp.smul_apply,add_sub_cancel_left,outputAction_apply]
  · simpa only [PiLp.smul_apply,add_sub_cancel_left,outputAction_apply] using
      factorDifference_norm ε hε h hh i (factorAction ε hε h hh i (w i))

theorem natural_clock_graphs (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ naturalClockGraph ε hε h hh v l c) :
    ∃ (cf : Hilbert) (tcf : Output (Fin 8) Hilbert) (ctf : Fin 8 → Hilbert),
      (f,cf) ∈ (clockOperator ε hε).graph ∧
      (f,g) ∈ jointGraph (energyFactor ε hε h v l) c ∧
      (cf,tcf) ∈ jointGraph (energyFactor ε hε h v l) c ∧
      ∀ i, (g i,ctf i) ∈ (clockOperator ε hε).graph ∧
        ctf i-tcf i = factorDifference ε hε h hh i (g i) ∧ ‖ctf i-tcf i‖ ≤ |h| * ‖g i‖ :=
  clock_graphs ε hε h hh _ (fun z hz => jointGraph_defect ε hε h hh v l c z.1 z.2 hz) f g hfg

theorem natural_clock_core_closedEnergy :
    (naturalClockGraph ε hε h hh v l (energyWeight mass2 quartic vacuum t)).topologicalClosure =
      (closedEnergy ε hε h v l mass2 quartic vacuum t).graph := by
  rw [closedEnergy_graph ε hε h v l mass2 quartic vacuum t (energy_bound ε hε h hh)]
  exact natural_clock_core ε hε h hh v l _

theorem natural_approximation (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph) :
    ∃ z : ℕ → Hilbert × Output (Fin 8) Hilbert,
      (∀ n, z n ∈ naturalClockGraph ε hε h hh v l (energyWeight mass2 quartic vacuum t)) ∧
      Tendsto z atTop (𝓝 (f,g)) := by
  have hz : (f,g) ∈
      (naturalClockGraph ε hε h hh v l (energyWeight mass2 quartic vacuum t)).topologicalClosure := by
    rw [natural_clock_core_closedEnergy ε hε h hh v l mass2 quartic vacuum t]
    exact hfg
  change (f,g) ∈ closure (naturalClockGraph ε hε h hh v l (energyWeight mass2 quartic vacuum t) :
    Set (Hilbert × Output (Fin 8) Hilbert)) at hz
  exact mem_closure_iff_seq_limit.mp hz

def completedClockDomain : Set Hilbert :=
  defectOperator ε hε '' ((closedEnergy ε hε h v l mass2 quartic vacuum t).domain : Set Hilbert)

theorem completedClockDomain_iff (f : Hilbert) :
    f ∈ completedClockDomain ε hε h v l mass2 quartic vacuum t ↔ ∃ cf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧ cf ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).domain := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(ε:ℂ) • u,clock_defect_graph ε hε u,
      (closedEnergy ε hε h v l mass2 quartic vacuum t).domain.smul_mem _ hu⟩
  · rintro ⟨cf,hc,hcK⟩
    refine ⟨(ε:ℂ)⁻¹ • cf,(closedEnergy ε hε h v l mass2 quartic vacuum t).domain.smul_mem _ hcK,?_⟩
    rw [map_smul,defect_clock ε hε f cf hc,smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul]

theorem completed_graph_image_iff (f : Hilbert) (g : Output (Fin 8) Hilbert) :
    (f,g) ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph.map
      (energyGraphAction ε hε h hh).toLinearMap ↔
      (f,g) ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph ∧
      f ∈ completedClockDomain ε hε h v l mass2 quartic vacuum t := by
  let K := closedEnergy ε hε h v l mass2 quartic vacuum t
  constructor
  · rintro ⟨⟨u,w⟩,hu,he⟩
    have h1 : defectOperator ε hε u = f := congrArg Prod.fst he
    have h2 : outputAction ε hε h hh w = g := congrArg Prod.snd he
    have hg := closedEnergy_graph_defect ε hε h hh v l mass2 quartic vacuum t u w hu
    rw [h1,h2] at hg
    exact ⟨hg,u,LinearPMap.mem_domain_of_mem_graph hu,h1⟩
  · rintro ⟨hfg,u,hu,he⟩
    let w := K ⟨u,hu⟩
    have hw : (u,w) ∈ K.graph := K.mem_graph ⟨u,hu⟩
    have ht := closedEnergy_graph_defect ε hε h hh v l mass2 quartic vacuum t u w hw
    rw [he] at ht
    have hb : outputAction ε hε h hh w = g := K.mem_graph_snd_inj' ht hfg rfl
    exact ⟨(u,w),hw,Prod.ext he hb⟩

theorem completed_clock_core :
    ((closedEnergy ε hε h v l mass2 quartic vacuum t).graph.map
      (energyGraphAction ε hε h hh).toLinearMap).topologicalClosure =
      (closedEnergy ε hε h v l mass2 quartic vacuum t).graph := by
  have he := range_core (energyGraphAction ε hε h hh)
    (closedEnergy ε hε h v l mass2 quartic vacuum t).graph
    (fun z hz => closedEnergy_graph_defect ε hε h hh v l mass2 quartic vacuum t z.1 z.2 hz)
    (fun z _ => energyAction_decay ε hε h hh z)
  rwa [(closedEnergy_closed ε hε h v l mass2 quartic vacuum t
    (energy_bound ε hε h hh)).submodule_topologicalClosure_eq] at he

include hh in
theorem completed_approximation (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph) :
    ∃ z : ℕ → Hilbert × Output (Fin 8) Hilbert,
      (∀ n, z n ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph ∧
        (z n).1 ∈ completedClockDomain ε hε h v l mass2 quartic vacuum t) ∧
      Tendsto z atTop (𝓝 (f,g)) := by
  let P := energyGraphAction ε hε h hh
  let K := closedEnergy ε hε h v l mass2 quartic vacuum t
  have hp : ∀ z ∈ K.graph, P z ∈ K.graph :=
    fun z hz => closedEnergy_graph_defect ε hε h hh v l mass2 quartic vacuum t z.1 z.2 hz
  refine ⟨fun n => P (geometricSum P (f,g) n),?_,
    approximation_tendsto P (f,g) (energyAction_decay ε hε h hh (f,g))⟩
  intro n
  apply (completed_graph_image_iff ε hε h hh v l mass2 quartic vacuum t _ _).mp
  exact ⟨geometricSum P (f,g) n,geometricSum_mem P K.graph hp (f,g) hfg n,rfl⟩

theorem completed_clock_graphs (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph)
    (hf : f ∈ completedClockDomain ε hε h v l mass2 quartic vacuum t) :
    ∃ (cf : Hilbert) (tcf : Output (Fin 8) Hilbert) (ctf : Fin 8 → Hilbert),
      (f,cf) ∈ (clockOperator ε hε).graph ∧
      (cf,tcf) ∈ (closedEnergy ε hε h v l mass2 quartic vacuum t).graph ∧
      ∀ i, (g i,ctf i) ∈ (clockOperator ε hε).graph ∧
        ctf i-tcf i = factorDifference ε hε h hh i (g i) ∧ ‖ctf i-tcf i‖ ≤ |h| * ‖g i‖ := by
  have hi := (completed_graph_image_iff ε hε h hh v l mass2 quartic vacuum t f g).mpr ⟨hfg,hf⟩
  obtain ⟨cf,tcf,ctf,hc,_,hK,hall⟩ := clock_graphs ε hε h hh _
    (fun z hz => closedEnergy_graph_defect ε hε h hh v l mass2 quartic vacuum t z.1 z.2 hz) f g hi
  exact ⟨cf,tcf,ctf,hc,hK,hall⟩

#print axioms energyAction_decay
#print axioms natural_clock_core
#print axioms clock_graphs
#print axioms natural_clock_graphs
#print axioms natural_clock_core_closedEnergy
#print axioms natural_approximation
#print axioms completedClockDomain_iff
#print axioms completed_graph_image_iff
#print axioms completed_clock_core
#print axioms completed_approximation
#print axioms completed_clock_graphs

end
end UnifiedTheory.Audit.KFCausalClockFloorEnergyClockCore
