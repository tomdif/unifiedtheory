/- Transport completed graph forms using a bounded change of energy
output. The abstract proof avoids unfolding any physical operators. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedGraphTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalClosedGraphForm
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def graphMap (M : K →L[ℂ] K) : WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℂ H).prodMap M).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

def MapsGraph (D E : Data H K) (M : K →L[ℂ] K) : Prop :=
  ∀ z, z ∈ D.operator.graph → (z.1,M z.2) ∈ E.operator.graph

def transfer (D E : Data H K) (M : K →L[ℂ] K) (hM : MapsGraph D E M) :
    FormSpace D →L[ℂ] FormSpace E where
  toFun u := ⟨graphMap M u.val,hM (WithLp.ofLp u.val) u.property⟩
  map_add' := by
    intro u v
    apply Subtype.ext
    exact (graphMap M).map_add u.val v.val
  map_smul' := by
    intro a u
    apply Subtype.ext
    exact (graphMap M).map_smul a u.val
  cont := ((graphMap M).continuous.comp continuous_subtype_val).subtype_mk _

theorem embedding_transfer (D E : Data H K) (M : K →L[ℂ] K) (hM : MapsGraph D E M) (u : FormSpace D) :
    embedding E (transfer D E M hM u)=embedding D u := rfl

theorem output_transfer (D E : Data H K) (M : K →L[ℂ] K) (hM : MapsGraph D E M) (u : FormSpace D) :
    energyOutput E (transfer D E M hM u)=M (energyOutput D u) := rfl

theorem transfer_inverse (D E : Data H K) (M N : K →L[ℂ] K)
    (hM : MapsGraph D E M) (hN : MapsGraph E D N) (u : FormSpace D) :
    transfer E D N hN (transfer D E M hM u)=u :=
  embedding_injective D ((embedding_transfer E D N hN _).trans (embedding_transfer D E M hM u))

theorem transfer_comp (D E F : Data H K) (M N P : K →L[ℂ] K)
    (hM : MapsGraph D E M) (hN : MapsGraph E F N) (hP : MapsGraph D F P) (u : FormSpace D) :
    transfer E F N hN (transfer D E M hM u)=transfer D F P hP u :=
  embedding_injective F (((embedding_transfer E F N hN _).trans (embedding_transfer D E M hM u)).trans
    (embedding_transfer D F P hP u).symm)

theorem transfer_self (D : Data H K) (M : K →L[ℂ] K) (hM : MapsGraph D D M) (u : FormSpace D) :
    transfer D D M hM u=u := embedding_injective D (embedding_transfer D D M hM u)

def transferEquiv (D E : Data H K) (M N : K →L[ℂ] K)
    (hM : MapsGraph D E M) (hN : MapsGraph E D N) : FormSpace D ≃L[ℂ] FormSpace E where
  toLinearEquiv := {
    toLinearMap := (transfer D E M hM).toLinearMap
    invFun := transfer E D N hN
    left_inv := transfer_inverse D E M N hM hN
    right_inv := transfer_inverse E D N M hN hM }
  continuous_toFun := (transfer D E M hM).continuous
  continuous_invFun := (transfer E D N hN).continuous

#print axioms embedding_transfer
#print axioms output_transfer
#print axioms transfer_inverse
#print axioms transfer_comp
#print axioms transfer_self
#print axioms transferEquiv

end
end UnifiedTheory.Audit.KFCausalClosedGraphTransport
