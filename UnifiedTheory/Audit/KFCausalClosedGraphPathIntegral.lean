/- Integrating a continuous path in a closed operator graph. No group
equivariance or commutation of the operator with the path is required. -/
import UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedGraphPathIntegral
noncomputable section
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integral_graph (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (f g : ℝ → H) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, (f t,g t) ∈ T.graph) (a b : ℝ) :
    (∫ t in a..b, f t,∫ t in a..b, g t) ∈ T.graph := by
  letI : CompleteSpace T.graph := hT.completeSpace_coe
  let v : ℝ → T.graph := fun t => ⟨(f t,g t),hfg t⟩
  have hv : Continuous v := (hf.prodMk hg).subtype_mk _
  let z : T.graph := ∫ t in a..b, v t
  let p : T.graph →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H).comp T.graph.subtypeL
  let q : T.graph →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp T.graph.subtypeL
  have hp : (∫ t in a..b, f t) = p z :=
    p.intervalIntegral_comp_comm (hv.intervalIntegrable a b)
  have hq : (∫ t in a..b, g t) = q z :=
    q.intervalIntegral_comp_comm (hv.intervalIntegrable a b)
  rw [hp,hq]
  exact z.property

#print axioms integral_graph
end
end UnifiedTheory.Audit.KFCausalClosedGraphPathIntegral
