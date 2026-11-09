/- A positive phase-space construction starts with a tensor state, a
volume-preserving shear, and an actual partial Fourier unitary. Its norm
is proved on all L2 states, without a pointwise Fourier-integral premise. -/
import UnifiedTheory.Audit.KFCausalPartialFourier
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped TensorProduct
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalPartialFourier

variable (n : ℕ)

def shear : (Block n × Block n) ≃ᵐ (Block n × Block n) where
  toFun z := (z.1+z.2,z.1)
  invFun z := (z.2,z.1-z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

theorem shear_preserves : MeasurePreserving (shear n) :=
  measurePreserving_swap.comp (measurePreserving_prod_add volume volume)

def shearUnitary : ProductHilbert n n ≃ₗᵢ[ℂ] ProductHilbert n n :=
  unitaryPullback (shear n) (shear_preserves n)

theorem shearUnitary_coe (f : ProductHilbert n n) :
    shearUnitary n f =ᵐ[volume] fun z => f (z.1+z.2,z.1) :=
  unitaryPullback_coe _ _ _

theorem shear_product_coe (f g : BlockHilbert n) :
    shearUnitary n (productState volume volume f g) =ᵐ[volume]
      fun z : Block n × Block n => f (z.1+z.2)*g z.1 := by
  filter_upwards [shearUnitary_coe n (productState volume volume f g),
    (shear_preserves n).quasiMeasurePreserving.ae (productState_coe volume volume f g)] with z hs hp
  exact hs.trans hp

def analysisUnitary : ProductHilbert n n ≃ₗᵢ[ℂ] ProductHilbert n n :=
  (shearUnitary n).trans (leftFourier n n)

def state (f g : BlockHilbert n) : ProductHilbert n n :=
  analysisUnitary n (productState volume volume f g)

theorem state_inner (f f' g g' : BlockHilbert n) :
    inner ℂ (state n f g) (state n f' g') = inner ℂ f f' * inner ℂ g g' := by
  rw [state,state,(analysisUnitary n).inner_map_map]
  exact productState_inner volume volume f f' g g'

theorem state_norm (f g : BlockHilbert n) : ‖state n f g‖ = ‖f‖*‖g‖ := by
  rw [state,(analysisUnitary n).norm_map]
  change ‖tensorEmbedding volume volume (f ⊗ₜ[ℂ] g)‖ = _
  rw [(tensorEmbedding volume volume).norm_map,TensorProduct.norm_tmul]

#print axioms shear_preserves
#print axioms shearUnitary_coe
#print axioms shear_product_coe
#print axioms state_inner
#print axioms state_norm

end
end UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
