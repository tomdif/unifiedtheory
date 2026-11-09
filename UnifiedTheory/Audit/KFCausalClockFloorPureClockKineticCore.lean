/- A constructed graph core for every actual kinetic factor P_v R.
Both input and output have pure-clock momentum. Bounded inverse-clock
maps and strongly decaying defect residuals transfer the transverse core. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic
import UnifiedTheory.Audit.KFCausalClockFloorPureClockDefectMomentum
import UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticCore
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pureGroup)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf (inverse_momentum_domain)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransverse (transverse_core)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDefectMomentum (defect_momentum_domain)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (clockMomentum_graph_iff clockMomentum_closed)
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_defect clockMomentum_graph_defect)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore (inverse_squared)
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay (real_response_decay)
open UnifiedTheory.Audit.KFCausalInvariantRangeCore

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Transverse)
local notation "B" => pureMomentum ε hε h
local notation "P" => transverseMomentum h v
local notation "K" => clockMomentum ε h v
local notation "R" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "G" => KFCausalClosedOperatorUnitaryCommutation.regularGraph (pureGroup ε hε) P h

def regularGraph : Submodule ℂ (Hilbert × Hilbert) := (K).graph ⊓ (B).domain.prod (B).domain
def coreMap : (Hilbert × Hilbert) →L[ℂ] (Hilbert × Hilbert) := (R).prodMap ((1/(ε:ℂ)) • D)

theorem coreMap_regular (hh : h ≠ 0) (z : Hilbert × Hilbert) (hz : z ∈ G) :
    coreMap ε hε z ∈ regularGraph ε hε h v := by
  refine ⟨?_,inverse_momentum_domain ε hε h hh z.1 hz.2.1,
    (B).domain.smul_mem _ (defect_momentum_domain ε hε h ⟨z.2,hz.2.2⟩)⟩
  apply (clockMomentum_graph_iff ε hε h v _ _).mpr
  change (R (R z.1),(1/(ε:ℂ)) • D z.2) ∈ (P).graph
  rw [inverse_squared]
  exact (P).graph.smul_mem (1/(ε:ℂ)) (transverse_graph_defect ε hε h v z.1 z.2 hz.1)

theorem regular_graph_core (hh : h ≠ 0) : (regularGraph ε hε h v).topologicalClosure = (K).graph := by
  let N := regularGraph ε hε h v
  let A := coreMap ε hε
  have hS : G ≤ N.topologicalClosure.comap A.toLinearMap := by
    intro z hz
    exact N.le_topologicalClosure (coreMap_regular ε hε h v hh z hz)
  have hc := Submodule.topologicalClosure_minimal _ hS
    (N.isClosed_topologicalClosure.preimage A.continuous)
  rw [transverse_core ε hε h hh v] at hc
  let M := (D).prodMap D
  have hM : ∀ z ∈ (K).graph, M z ∈ (K).graph := fun z hz =>
    clockMomentum_graph_defect ε hε h v z.1 z.2 hz
  have hdec (z : Hilbert × Hilbert) :
      Tendsto (fun n : ℕ => (residual M : Hilbert × Hilbert → Hilbert × Hilbert)^[n] z) atTop (𝓝 0) :=
    prod_residual_tendsto D D z.1 z.2 (real_response_decay ε hε z.1) (real_response_decay ε hε z.2)
  have hm : (K).graph.map M.toLinearMap ≤ N.topologicalClosure := by
    rintro _ ⟨⟨f,g⟩,hfg,rfl⟩
    have hp := (clockMomentum_graph_iff ε hε h v f g).mp hfg
    have hz := hc hp
    change (R (R f),(1/(ε:ℂ)) • D g) ∈ N.topologicalClosure at hz
    rw [inverse_squared] at hz
    have hs := N.topologicalClosure.smul_mem (ε:ℂ) hz
    simpa only [Prod.smul_mk,smul_smul,one_div,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul] using hs
  have hm' := Submodule.topologicalClosure_minimal _ hm N.isClosed_topologicalClosure
  rw [range_core M (K).graph hM (fun z _ => hdec z)] at hm'
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hz => hz.1) (clockMomentum_closed ε hε h v)
  · exact (K).graph.le_topologicalClosure.trans hm'

theorem common_compositions (hh : h ≠ 0) (f g : Hilbert) (hg : (f,g) ∈ regularGraph ε hε h v) :
    ∃ b k bg : Hilbert, (f,b) ∈ (B).graph ∧ (b,k) ∈ (K).graph ∧ (g,bg) ∈ (B).graph ∧
      bg-k = correction ε hε h g := by
  obtain ⟨b,hb⟩ := LinearPMap.mem_domain_iff.mp hg.2.1
  obtain ⟨bg,hbg⟩ := LinearPMap.mem_domain_iff.mp hg.2.2
  refine ⟨b,bg-correction ε hε h g,bg,hb,
    momentum_kinetic_graph ε hε h v hh f g b bg hg.1 hb hbg,hbg,?_⟩
  abel

theorem graph_approximation (hh : h ≠ 0) (f g : Hilbert) (hg : (f,g) ∈ (K).graph) :
    ∃ z : ℕ → Hilbert × Hilbert, (∀ n, z n ∈ regularGraph ε hε h v) ∧ Tendsto z atTop (𝓝 (f,g)) := by
  have hz : (f,g) ∈ (regularGraph ε hε h v).topologicalClosure := by
    rw [regular_graph_core ε hε h v hh]
    exact hg
  exact mem_closure_iff_seq_limit.mp hz

#print axioms coreMap_regular
#print axioms regular_graph_core
#print axioms common_compositions
#print axioms graph_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticCore
