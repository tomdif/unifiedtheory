/- Transport an averaged output graph through a bounded base-form map.
Both the physical embedding and the energy-output relation are checked.
This transports the full averaged graph, not only a selected family. -/
import UnifiedTheory.Audit.KFCausalAveragedFormTransport
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedOutputTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection (averagedOutput)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
open UnifiedTheory.Audit.KFCausalAveragedFormTransport

variable {H E F K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H) (J' : F →L[ℂ] H)
  (A : E →L[ℂ] K) (A' : F →L[ℂ] K) (R : E →L[ℂ] F) (M : K →L[ℂ] K)
  (hR : ∀ v, J' (R v) = J v) (hA : ∀ v, A' (R v) = M (A v))

include hA in
theorem transfer_output (u : FormSpace U T J) :
    averagedOutput U T J' A' (transfer U T J J' R hR u) =
      M.compLp (averagedOutput U T J A u) := by
  apply Lp.ext
  filter_upwards [A'.coeFn_compLp (R.compLp (sectionMap U T J u)),
    R.coeFn_compLp (sectionMap U T J u),
    M.coeFn_compLp (A.compLp (sectionMap U T J u)),
    A.coeFn_compLp (sectionMap U T J u)] with θ h1 h2 h3 h4
  change A'.compLp (R.compLp (sectionMap U T J u)) θ = M.compLp (A.compLp (sectionMap U T J u)) θ
  rw [h1,h2,h3,h4,hA]

include hR hA in
theorem operator_graph_transport (hJ : Function.Injective J) (hJ' : Function.Injective J')
    (z : H × Lp K 2 angleMeasure) (hz : z ∈ (averagedOperator U T J A).graph) :
    (z.1,M.compLp z.2) ∈ (averagedOperator U T J' A').graph := by
  have hg := averagedOperator_graph U T J A hJ
  have hz' := (congrArg (fun S : Submodule ℂ (H × Lp K 2 angleMeasure) => z ∈ S) hg).mp hz
  rcases hz' with ⟨u,hu⟩
  have ht := averagedOperator_form_graph U T J' A' hJ' (transfer U T J J' R hR u)
  have he : embedding U T J' (transfer U T J J' R hR u) = z.1 :=
    (transfer_embedding U T J J' R hR u).trans (congrArg Prod.fst hu)
  have ho : averagedOutput U T J' A' (transfer U T J J' R hR u) = M.compLp z.2 :=
    (transfer_output U T J J' A A' R M hR hA u).trans (congrArg M.compLp (congrArg Prod.snd hu))
  exact (congrArg (fun w : H × Lp K 2 angleMeasure => w ∈ (averagedOperator U T J' A').graph)
    (Prod.ext he ho)).mp ht

#print axioms transfer_output
#print axioms operator_graph_transport

end
end UnifiedTheory.Audit.KFCausalAveragedOutputTransport
