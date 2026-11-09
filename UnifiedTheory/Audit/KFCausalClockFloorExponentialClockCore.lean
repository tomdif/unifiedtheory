/- The natural forward clock-composition domains are graph cores of the
actual half-exponential and ordered exponential. Explicit polynomial
approximants converge simultaneously in state and operator output. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
import UnifiedTheory.Audit.KFCausalClockFloorClockExponentialResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorExponentialClockCore
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
open UnifiedTheory.Audit.KFCausalInvariantRangeCore
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator (commonDomain)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain (graph_defect)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain (ordered_graph_defect)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (orderedExponential_closed)

def graphAction (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3) :
    Hilbert × Hilbert →L[ℂ] Hilbert × Hilbert :=
  (defectOperator ε hε).prodMap (shiftedDefect ε hε h hh)

theorem graphAction_decay (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (z : Hilbert × Hilbert) :
    Tendsto (fun n : ℕ => (residual (graphAction ε hε h hh) : Hilbert × Hilbert → Hilbert × Hilbert)^[n] z)
      atTop (𝓝 0) :=
  prod_residual_tendsto _ _ z.1 z.2 (real_response_decay ε hε z.1) (shifted_response_decay ε hε h hh z.2)

theorem graph_image_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (T : Hilbert →ₗ.[ℂ] Hilbert)
    (hT : ∀ u v : Hilbert, (u,v) ∈ T.graph →
      (defectOperator ε hε u,shiftedDefect ε hε h hh v) ∈ T.graph) (f g : Hilbert) :
    (f,g) ∈ T.graph.map (graphAction ε hε h hh).toLinearMap ↔
      (f,g) ∈ T.graph ∧ f ∈ commonDomain ε hε T := by
  constructor
  · rintro ⟨⟨u,v⟩,hu,he⟩
    have h1 : defectOperator ε hε u = f := congrArg Prod.fst he
    have h2 : shiftedDefect ε hε h hh v = g := congrArg Prod.snd he
    have hg := hT u v hu
    rw [h1,h2] at hg
    exact ⟨hg,u,LinearPMap.mem_domain_of_mem_graph hu,h1⟩
  · rintro ⟨hfg,u,hu,he⟩
    let v := T ⟨u,hu⟩
    have hv : (u,v) ∈ T.graph := T.mem_graph ⟨u,hu⟩
    have ht := hT u v hv
    rw [he] at ht
    have hb : shiftedDefect ε hε h hh v = g := T.mem_graph_snd_inj' ht hfg rfl
    exact ⟨(u,v),hv,Prod.ext he hb⟩

theorem operator_approximation (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (T : Hilbert →ₗ.[ℂ] Hilbert)
    (hT : ∀ u v : Hilbert, (u,v) ∈ T.graph →
      (defectOperator ε hε u,shiftedDefect ε hε h hh v) ∈ T.graph)
    (f g : Hilbert) (hfg : (f,g) ∈ T.graph) :
    ∃ z : ℕ → Hilbert × Hilbert,
      (∀ n, z n ∈ T.graph ∧ (z n).1 ∈ commonDomain ε hε T) ∧ Tendsto z atTop (𝓝 (f,g)) := by
  let P := graphAction ε hε h hh
  have hp : ∀ z ∈ T.graph, P z ∈ T.graph := fun z hz => hT z.1 z.2 hz
  refine ⟨fun n => P (geometricSum P (f,g) n),?_,
    approximation_tendsto P (f,g) (graphAction_decay ε hε h hh (f,g))⟩
  intro n
  apply (graph_image_iff ε hε h hh T hT _ _).mp
  exact ⟨geometricSum P (f,g) n,geometricSum_mem P T.graph hp (f,g) hfg n,rfl⟩

theorem exponential_core (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3) :
    ((longitudinalExponential ε hε h (1/2)).graph.map
      (graphAction ε hε h hh).toLinearMap).topologicalClosure =
      (longitudinalExponential ε hε h (1/2)).graph := by
  have he := range_core (graphAction ε hε h hh) (longitudinalExponential ε hε h (1/2)).graph
    (fun z hz => graph_defect ε hε h hh z.1 z.2 hz) (fun z _ => graphAction_decay ε hε h hh z)
  rwa [(longitudinal_exponential_closed ε hε h (1/2)).submodule_topologicalClosure_eq] at he

theorem ordered_core (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3) :
    ((orderedExponential ε hε h).graph.map (graphAction ε hε h hh).toLinearMap).topologicalClosure =
      (orderedExponential ε hε h).graph := by
  have he := range_core (graphAction ε hε h hh) (orderedExponential ε hε h).graph
    (fun z hz => ordered_graph_defect ε hε h hh z.1 z.2 hz) (fun z _ => graphAction_decay ε hε h hh z)
  rwa [(orderedExponential_closed ε hε h).submodule_topologicalClosure_eq] at he

theorem exponential_approximation (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    ∃ z : ℕ → Hilbert × Hilbert,
      (∀ n, z n ∈ (longitudinalExponential ε hε h (1/2)).graph ∧
        (z n).1 ∈ commonDomain ε hε (longitudinalExponential ε hε h (1/2))) ∧
      Tendsto z atTop (𝓝 (f,g)) :=
  operator_approximation ε hε h hh _ (graph_defect ε hε h hh) f g hfg

theorem ordered_approximation (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    ∃ z : ℕ → Hilbert × Hilbert,
      (∀ n, z n ∈ (orderedExponential ε hε h).graph ∧
        (z n).1 ∈ commonDomain ε hε (orderedExponential ε hε h)) ∧ Tendsto z atTop (𝓝 (f,g)) :=
  operator_approximation ε hε h hh _ (ordered_graph_defect ε hε h hh) f g hfg

#print axioms graphAction_decay
#print axioms graph_image_iff
#print axioms operator_approximation
#print axioms exponential_core
#print axioms ordered_core
#print axioms exponential_approximation
#print axioms ordered_approximation

end
end UnifiedTheory.Audit.KFCausalClockFloorExponentialClockCore
