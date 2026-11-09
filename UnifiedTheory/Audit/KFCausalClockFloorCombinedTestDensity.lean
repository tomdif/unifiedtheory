/- A constructed dense common energy/chart/squeeze test class. Squeeze
averages preserve the closed chart graph; density of an intersection is
not inferred from separate density statements. -/
import UnifiedTheory.Audit.KFCausalSqueezeChartCommutation
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeTestDensity
import UnifiedTheory.Audit.KFCausalClockFloorGaugeTestDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorCombinedTestDensity
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport)
open UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity (transport_strong_continuous)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeGroup squeezeMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative (chartOperator chartOperator_selfAdjoint)
open UnifiedTheory.Audit.KFCausalSqueezeChartCommutation (chart_graph_squeeze)
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (average primitive)

private theorem integral_mem_closed_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (G : Submodule ℂ E) (hG : IsClosed (G : Set E)) (f : ℝ → E) (hf : Continuous f)
    (hm : ∀ t, f t ∈ G) (a b : ℝ) : (∫ t in a..b, f t) ∈ G := by
  letI : CompleteSpace G := hG.completeSpace_coe
  letI : SecondCountableTopologyEither ℝ G := ⟨Or.inl inferInstance⟩
  let lift : ℝ → G := fun t => ⟨f t,hm t⟩
  have hc : Continuous lift := hf.subtype_mk _
  have he : (∫ t in a..b, f t) = G.subtypeL (∫ t in a..b, lift t) :=
    G.subtypeL.intervalIntegral_comp_comm (hc.intervalIntegrable a b)
  rw [he]
  exact (∫ t in a..b, lift t).property

theorem chart_average_graph (ε a : ℝ) (f z : Hilbert) (hfz : (f,z) ∈ (chartOperator ε).graph) :
    (average squeezeGroup f a,average squeezeGroup z a) ∈ (chartOperator ε).graph := by
  let P : ℝ → Hilbert × Hilbert := fun b => (transport b f,transport b z)
  have hc : Continuous P := (transport_strong_continuous f).prodMk (transport_strong_continuous z)
  have hi := integral_mem_closed_submodule (chartOperator ε).graph
    (chartOperator_selfAdjoint ε).isClosed P hc (fun b => chart_graph_squeeze ε b f z hfz) 0 a
  have he : a⁻¹ • (∫ b in 0..a, P b) = (average squeezeGroup f a,average squeezeGroup z a) := by
    apply Prod.ext
    · exact congrArg (fun y : Hilbert => a⁻¹ • y)
        ((ContinuousLinearMap.fst ℂ Hilbert Hilbert).intervalIntegral_comp_comm
          (hc.intervalIntegrable 0 a)).symm
    · exact congrArg (fun y : Hilbert => a⁻¹ • y)
        ((ContinuousLinearMap.snd ℂ Hilbert Hilbert).intervalIntegral_comp_comm
          (hc.intervalIntegrable 0 a)).symm
  exact he ▸ ((chartOperator ε).graph.restrictScalars ℝ).smul_mem a⁻¹ hi

open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeTestDensity (formAverage formAverage_embedding formAverage_domain formAverage_tendsto)
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "J" => embedding ε hε h hne hh m q k 0

theorem formAverage_chart_graph (u : V) (z : Hilbert) (huz : (J u,z) ∈ (chartOperator ε).graph) (a : ℝ) :
    (J (formAverage ε hε h hne hh m q k 0 u a),average squeezeGroup z a) ∈ (chartOperator ε).graph := by
  rw [formAverage_embedding]
  exact chart_average_graph ε a (J u) z huz

theorem physical_test_dense : Dense {f : Hilbert | ∃ v : V, ∃ zQ zA : Hilbert,
    J v = f ∧ (f,zQ) ∈ (chartOperator ε).graph ∧ (f,zA) ∈ (squeezeMomentum h).graph} := by
  have hd := KFCausalClockFloorGaugeTestDensity.physical_test_dense ε hε h hne hh m q k
  intro f
  apply closure_minimal (s := {f : Hilbert | ∃ v : V, ∃ z : Hilbert,
    J v = f ∧ (f,z) ∈ (chartOperator ε).graph}) ?_ isClosed_closure (hd f)
  rintro _ ⟨u,z,rfl,huz⟩
  have hl := ((J).continuous.tendsto u).comp (formAverage_tendsto ε hε h hne hh m q k 0 u)
  apply mem_closure_of_tendsto hl
  apply Eventually.of_forall
  intro a
  obtain ⟨zA,hA⟩ := LinearPMap.mem_domain_iff.mp (formAverage_domain ε hε h hne hh m q k 0 u a)
  exact ⟨formAverage ε hε h hne hh m q k 0 u a,average squeezeGroup z a,zA,rfl,
    formAverage_chart_graph ε hε h hne hh m q k u z huz a,hA⟩

#print axioms chart_average_graph
#print axioms formAverage_chart_graph
#print axioms physical_test_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorCombinedTestDensity
