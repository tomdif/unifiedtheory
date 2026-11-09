/- Time averages approximate every momentum-domain state in graph norm.
Their generated graph has closure equal to the full momentum graph.
This is a longitudinal core, not a common full Hamiltonian form domain. -/
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryMomentumCore
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : StrongUnitaryGroup H)

theorem momentum_average_commutes (hbar : ℝ) (f : (momentum U hbar).domain) (a : ℝ) :
    momentum U hbar (averageState U hbar (f:H) a) = average U (momentum U hbar f) a := by
  rw [average_momentum]
  have hh := generator_integral U f 0 a
  rw [U.initial] at hh
  rw [← hh]
  change (-Complex.I*(hbar:ℂ)) • (a⁻¹ • (∫ t in 0..a, U.action t (generator U f))) =
    a⁻¹ • (∫ t in 0..a, U.action t ((-Complex.I*(hbar:ℂ)) • generator U f))
  simp only [map_smul,intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem averaged_graph_tendsto (hbar : ℝ) (f : (momentum U hbar).domain) :
    Tendsto (fun a : ℝ => (average U (f:H) a,momentum U hbar (averageState U hbar (f:H) a)))
      (𝓝[≠] 0) (𝓝 ((f:H),momentum U hbar f)) := by
  simp only [momentum_average_commutes]
  exact (average_tendsto U (f:H)).prodMk_nhds (average_tendsto U (momentum U hbar f))

def averagedGraph (hbar : ℝ) : Set (H × H) :=
  Set.range (fun p : H × ℝ => (average U p.1 p.2,momentum U hbar (averageState U hbar p.1 p.2)))

theorem averagedGraph_subset (hbar : ℝ) : averagedGraph U hbar ⊆ (momentum U hbar).graph := by
  rintro _ ⟨⟨x,a⟩,rfl⟩
  exact (momentum U hbar).mem_graph (averageState U hbar x a)

theorem averagedGraph_closure (hbar : ℝ) (hh : hbar ≠ 0) :
    closure (averagedGraph U hbar) = ((momentum U hbar).graph : Set (H × H)) := by
  apply le_antisymm
  · exact closure_minimal (averagedGraph_subset U hbar) (momentum_closed U hbar hh)
  · intro p hp
    obtain ⟨f,hf,hg⟩ := (LinearPMap.mem_graph_iff _).mp hp
    have he : ((f:H),momentum U hbar f) = p := Prod.ext hf hg
    rw [← he]
    exact mem_closure_of_tendsto (averaged_graph_tendsto U hbar f)
      (Filter.Eventually.of_forall fun a => ⟨((f:H),a),rfl⟩)

theorem averagedGraph_span_closure (hbar : ℝ) (hh : hbar ≠ 0) :
    (Submodule.span ℂ (averagedGraph U hbar)).topologicalClosure = (momentum U hbar).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (averagedGraph_subset U hbar)) (momentum_closed U hbar hh)
  · intro p hp
    have hc : p ∈ closure (averagedGraph U hbar) := by rw [averagedGraph_closure U hbar hh];exact hp
    exact closure_mono (Submodule.subset_span) hc

#print axioms momentum_average_commutes
#print axioms averaged_graph_tendsto
#print axioms averagedGraph_subset
#print axioms averagedGraph_closure
#print axioms averagedGraph_span_closure

end
end UnifiedTheory.Audit.KFCausalUnitaryMomentumCore
