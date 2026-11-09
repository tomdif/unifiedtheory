/- Two factor unitaries induce a unitary on the full product L2 space.
The actual dense tensor embedding supplies the extension and its uniqueness. -/
import UnifiedTheory.Audit.KFCausalEuclideanTensorDensity
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
noncomputable section
open MeasureTheory
open scoped TensorProduct
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanTensorDensity
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

variable (n m : ℕ)

def liftUnitary (U : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n)
    (V : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m) :
    ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m :=
  extension (tensorEmbedding volume volume).toLinearMap (tensorEmbedding_dense n m)
    (TensorProduct.congrIsometry U V).toLinearEquiv
    (fun w => by
      change ‖tensorEmbedding volume volume ((TensorProduct.congrIsometry U V) w)‖ =
        ‖tensorEmbedding volume volume w‖
      rw [(tensorEmbedding volume volume).norm_map, (tensorEmbedding volume volume).norm_map]
      exact (TensorProduct.congrIsometry U V).norm_map w)

theorem liftUnitary_product (U : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n)
    (V : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m) (f : BlockHilbert n) (g : BlockHilbert m) :
    liftUnitary n m U V (productState volume volume f g) =
      productState volume volume (U f) (V g) := by
  exact extension_embedding _ _ _ _ (f ⊗ₜ[ℂ] g)

theorem equal_on_products (P Q : ProductHilbert n m →L[ℂ] ProductHilbert n m)
    (he : ∀ (f : BlockHilbert n) (g : BlockHilbert m),
      P (productState volume volume f g) = Q (productState volume volume f g)) : P = Q := by
  apply equal_on_dense (tensorEmbedding volume volume).toLinearMap (tensorEmbedding_dense n m) P Q
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => exact he f g
  | add w w' hw hw' => simp only [map_add, hw, hw']

theorem unitary_eq_on_products
    (P Q : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m)
    (he : ∀ (f : BlockHilbert n) (g : BlockHilbert m),
      P (productState volume volume f g) = Q (productState volume volume f g)) : P = Q := by
  have h := equal_on_products n m P.toContinuousLinearEquiv.toContinuousLinearMap
    Q.toContinuousLinearEquiv.toContinuousLinearMap he
  apply LinearIsometryEquiv.ext
  exact fun f => congrArg (fun L : ProductHilbert n m →L[ℂ] ProductHilbert n m => L f) h

theorem liftUnitary_identity :
    liftUnitary n m (LinearIsometryEquiv.refl ℂ (BlockHilbert n))
      (LinearIsometryEquiv.refl ℂ (BlockHilbert m)) =
        LinearIsometryEquiv.refl ℂ (ProductHilbert n m) := by
  apply unitary_eq_on_products n m
  intro f g
  exact liftUnitary_product n m _ _ f g

theorem liftUnitary_compose
    (U₁ U₂ : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n)
    (V₁ V₂ : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m) :
    (liftUnitary n m U₁ V₁).trans (liftUnitary n m U₂ V₂) =
      liftUnitary n m (U₁.trans U₂) (V₁.trans V₂) := by
  apply unitary_eq_on_products n m
  intro f g
  simp only [LinearIsometryEquiv.trans_apply, liftUnitary_product]

theorem liftUnitary_inverse
    (U : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n)
    (V : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m) :
    (liftUnitary n m U V).symm = liftUnitary n m U.symm V.symm := by
  apply unitary_eq_on_products n m
  intro f g
  apply (liftUnitary n m U V).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, liftUnitary_product]

theorem liftUnitary_unitary
    (U : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n)
    (V : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m) :
    (liftUnitary n m U V : ProductHilbert n m →L[ℂ] ProductHilbert n m) ∈
      unitary (ProductHilbert n m →L[ℂ] ProductHilbert n m) :=
  (Unitary.linearIsometryEquiv.symm (liftUnitary n m U V)).property

theorem independent_actions_commute
    (U : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n)
    (V : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m) (f : ProductHilbert n m) :
    liftUnitary n m U (LinearIsometryEquiv.refl ℂ _) 
      (liftUnitary n m (LinearIsometryEquiv.refl ℂ _) V f) =
    liftUnitary n m (LinearIsometryEquiv.refl ℂ _) V
      (liftUnitary n m U (LinearIsometryEquiv.refl ℂ _) f) := by
  have h := liftUnitary_compose n m (LinearIsometryEquiv.refl ℂ _) U V
    (LinearIsometryEquiv.refl ℂ _)
  have h' := liftUnitary_compose n m U (LinearIsometryEquiv.refl ℂ _)
    (LinearIsometryEquiv.refl ℂ _) V
  have he : (liftUnitary n m (LinearIsometryEquiv.refl ℂ _) V).trans
      (liftUnitary n m U (LinearIsometryEquiv.refl ℂ _)) =
      (liftUnitary n m U (LinearIsometryEquiv.refl ℂ _)).trans
        (liftUnitary n m (LinearIsometryEquiv.refl ℂ _) V) := by
    simpa only [LinearIsometryEquiv.refl_trans, LinearIsometryEquiv.trans_refl] using h.trans h'.symm
  exact congrArg (fun W : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m => W f) he

#print axioms liftUnitary
#print axioms liftUnitary_product
#print axioms equal_on_products
#print axioms unitary_eq_on_products
#print axioms liftUnitary_identity
#print axioms liftUnitary_compose
#print axioms liftUnitary_inverse
#print axioms liftUnitary_unitary
#print axioms independent_actions_commute

end
end UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
