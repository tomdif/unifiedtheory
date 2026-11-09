/- Partial Fourier transforms on arbitrary Euclidean coordinate blocks.
These are actual onto L2 isometries, with the ordinary Fourier-integral
formula on product L1/L2 states. No charge identification is claimed here. -/
import UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
import UnifiedTheory.Audit.KFCausalL2FourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPartialFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

variable (n m : ℕ)

def leftFourier : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m :=
  liftUnitary n m (Lp.fourierTransformₗᵢ (Block n) ℂ) (LinearIsometryEquiv.refl ℂ _)

def rightFourier : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m :=
  liftUnitary n m (LinearIsometryEquiv.refl ℂ _) (Lp.fourierTransformₗᵢ (Block m) ℂ)

theorem leftFourier_product (f : BlockHilbert n) (g : BlockHilbert m) :
    leftFourier n m (productState volume volume f g) =
      productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ) f) g :=
  liftUnitary_product n m _ _ f g

theorem rightFourier_product (f : BlockHilbert n) (g : BlockHilbert m) :
    rightFourier n m (productState volume volume f g) =
      productState volume volume f ((Lp.fourierTransformₗᵢ (Block m) ℂ) g) :=
  liftUnitary_product n m _ _ f g

theorem leftFourier_inverse_product (f : BlockHilbert n) (g : BlockHilbert m) :
    (leftFourier n m).symm (productState volume volume f g) =
      productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ).symm f) g := by
  apply (leftFourier n m).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, leftFourier_product]

theorem rightFourier_inverse_product (f : BlockHilbert n) (g : BlockHilbert m) :
    (rightFourier n m).symm (productState volume volume f g) =
      productState volume volume f ((Lp.fourierTransformₗᵢ (Block m) ℂ).symm g) := by
  apply (rightFourier n m).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, rightFourier_product]

theorem partial_transforms_commute (f : ProductHilbert n m) :
    leftFourier n m (rightFourier n m f) = rightFourier n m (leftFourier n m f) :=
  independent_actions_commute n m _ _ f

theorem leftFourier_functions_coe (f : Block n → ℂ) (g : Block m → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg2 : MemLp g 2) :
    leftFourier n m (productState volume volume (hf2.toLp f) (hg2.toLp g)) =ᵐ[volume]
      fun z : Block n × Block m => (𝓕 f) z.1 * g z.2 := by
  rw [leftFourier_product, fourier_toLp_eq f hf1 hf2]
  exact productState_functions_coe n m _ _ (integralFourier_memLp f hf1 hf2) hg2

theorem rightFourier_functions_coe (f : Block n → ℂ) (g : Block m → ℂ)
    (hf2 : MemLp f 2) (hg1 : Integrable g) (hg2 : MemLp g 2) :
    rightFourier n m (productState volume volume (hf2.toLp f) (hg2.toLp g)) =ᵐ[volume]
      fun z : Block n × Block m => f z.1 * (𝓕 g) z.2 := by
  rw [rightFourier_product, fourier_toLp_eq g hg1 hg2]
  exact productState_functions_coe n m _ _ hf2 (integralFourier_memLp g hg1 hg2)

def jointLeftFourier : JointHilbert n m ≃ₗᵢ[ℂ] JointHilbert n m :=
  (coordinates n m).symm.trans ((leftFourier n m).trans (coordinates n m))

def jointRightFourier : JointHilbert n m ≃ₗᵢ[ℂ] JointHilbert n m :=
  (coordinates n m).symm.trans ((rightFourier n m).trans (coordinates n m))

theorem jointLeftFourier_product (f : BlockHilbert n) (g : BlockHilbert m) :
    jointLeftFourier n m (coordinates n m (productState volume volume f g)) =
      coordinates n m (productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ) f) g) := by
  simp only [jointLeftFourier, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, leftFourier_product]

theorem jointRightFourier_product (f : BlockHilbert n) (g : BlockHilbert m) :
    jointRightFourier n m (coordinates n m (productState volume volume f g)) =
      coordinates n m (productState volume volume f ((Lp.fourierTransformₗᵢ (Block m) ℂ) g)) := by
  simp only [jointRightFourier, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, rightFourier_product]

theorem joint_partial_transforms_commute (f : JointHilbert n m) :
    jointLeftFourier n m (jointRightFourier n m f) =
      jointRightFourier n m (jointLeftFourier n m f) := by
  simp only [jointLeftFourier, jointRightFourier, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, partial_transforms_commute]

#print axioms leftFourier
#print axioms rightFourier
#print axioms leftFourier_product
#print axioms rightFourier_product
#print axioms leftFourier_inverse_product
#print axioms rightFourier_inverse_product
#print axioms partial_transforms_commute
#print axioms leftFourier_functions_coe
#print axioms rightFourier_functions_coe
#print axioms jointLeftFourier
#print axioms jointRightFourier
#print axioms jointLeftFourier_product
#print axioms jointRightFourier_product
#print axioms joint_partial_transforms_commute

end
end UnifiedTheory.Audit.KFCausalPartialFourier
