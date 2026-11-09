/- Lift a pair of bounded maps preserving an actual closed energy graph
into a bounded action on its completed graph form space. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClosedGraphDiagonalAction
noncomputable section
open UnifiedTheory.Audit.KFCausalClosedGraphForm
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def graphMap (D : H →L[ℂ] H) (R : K →L[ℂ] K) : WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    ((D.prodMap R).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

def action (G : Data H K) (D : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hg : ∀ f g, (f,g) ∈ G.operator.graph → (D f,R g) ∈ G.operator.graph) :
    FormSpace G →L[ℂ] FormSpace G where
  toFun u := ⟨graphMap D R u.val,hg (embedding G u) (energyOutput G u) u.property⟩
  map_add' u v := by apply Subtype.ext; exact (graphMap D R).map_add u.val v.val
  map_smul' c u := by apply Subtype.ext; exact (graphMap D R).map_smul c u.val
  cont := ((graphMap D R).continuous.comp continuous_subtype_val).subtype_mk _

theorem action_embedding (G : Data H K) (D : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hg : ∀ f g, (f,g) ∈ G.operator.graph → (D f,R g) ∈ G.operator.graph) (u : FormSpace G) :
    embedding G (action G D R hg u) = D (embedding G u) := rfl

theorem action_output (G : Data H K) (D : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hg : ∀ f g, (f,g) ∈ G.operator.graph → (D f,R g) ∈ G.operator.graph) (u : FormSpace G) :
    energyOutput G (action G D R hg u) = R (energyOutput G u) := rfl

#print axioms action_embedding
#print axioms action_output
end
end UnifiedTheory.Audit.KFCausalClosedGraphDiagonalAction
