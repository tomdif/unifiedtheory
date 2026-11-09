/- A bounded output identity with a state correction passes to L2
sections. The concrete physical application must supply the identity. -/
import UnifiedTheory.Audit.KFCausalAveragedFormAction
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalLpOutputCorrection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem output_relation (J : E →L[ℂ] H) (A : E →L[ℂ] K)
    (F : E →L[ℂ] E) (R : K →L[ℂ] K) (C : H →L[ℂ] K)
    (hA : ∀ w, A (F w) = R (A w)+C (J w)) (z : Lp E 2 angleMeasure) :
    A.compLp (F.compLp z) = R.compLp (A.compLp z)+C.compLp (J.compLp z) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLp (F.compLp z),F.coeFn_compLp z,
    Lp.coeFn_add (R.compLp (A.compLp z)) (C.compLp (J.compLp z)),
    R.coeFn_compLp (A.compLp z),A.coeFn_compLp z,
    C.coeFn_compLp (J.compLp z),J.coeFn_compLp z] with θ ha hf hs hr hb hc hj
  rw [ha,hf,hs]
  simp only [Pi.add_apply,hr,hb,hc,hj]
  exact hA (z θ)

#print axioms output_relation

open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
open UnifiedTheory.Audit.KFCausalAveragedFormSpace (FormSpace embedding)
open UnifiedTheory.Audit.KFCausalAveragedFormProjection (averagedOutput)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (averagedOperator averagedOperator_graph graphMap)

theorem graph_action (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H)
    (A : E →L[ℂ] K) (hJ : Function.Injective J)
    (D : H →L[ℂ] H) (F : FormSpace U T J → FormSpace U T J)
    (B : H → Lp K 2 angleMeasure → Lp K 2 angleMeasure)
    (hF : ∀ u, embedding U T J (F u) = D (embedding U T J u))
    (hA : ∀ u, averagedOutput U T J A (F u) = B (embedding U T J u) (averagedOutput U T J A u))
    (f : H) (y : Lp K 2 angleMeasure) (hfy : (f,y) ∈ (averagedOperator U T J A).graph) :
    (D f,B f y) ∈ (averagedOperator U T J A).graph := by
  rw [averagedOperator_graph U T J A hJ] at hfy ⊢
  obtain ⟨u,hu⟩ := hfy
  change (embedding U T J u,averagedOutput U T J A u) = (f,y) at hu
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hu
  exact ⟨F u,Prod.ext (hF u) (hA u)⟩

#print axioms graph_action

end
end UnifiedTheory.Audit.KFCausalLpOutputCorrection
