/- The actual full Fourier transform in split Euclidean coordinates is
the product of the actual partial Fourier transforms. Integral factorization
on product states and density identify the operators on all L2 vectors. -/
import UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative
import UnifiedTheory.Audit.KFCausalPartialFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalFullFourierProduct
noncomputable section
open MeasureTheory
open scoped FourierTransform CompactlySupported
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanTensorDensity (pairFunction pair_memLp)
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding (productState)
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative (closed_submodule_total testState testState_dense)

variable (n m : ℕ)

theorem fourier_pair (f : Block n → ℂ) (g : Block m → ℂ) (k : Joint n m) :
    (𝓕 (pairFunction n m f g)) k = (𝓕 f) (split n m k).1*(𝓕 g) (split n m k).2 := by
  let a : Block n → ℂ := fun x => (Real.fourierChar (-inner ℝ x (split n m k).1):ℂ)*f x
  let b : Block m → ℂ := fun y => (Real.fourierChar (-inner ℝ y (split n m k).2):ℂ)*g y
  calc
    _ = ∫ x : Joint n m, a (split n m x).1*b (split n m x).2 := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [a,b,pairFunction,inner_split,neg_add,AddChar.map_add_eq_mul,Circle.coe_mul,
        Circle.smul_def,smul_eq_mul]
      ring
    _ = ∫ x : Block n × Block m, a x.1*b x.2 :=
      (split_preserves_volume n m).integral_comp (split n m).measurableEmbedding
        (fun x : Block n × Block m => a x.1*b x.2)
    _ = _ := integral_prod_mul a b

theorem pair_integrable (f : Block n → ℂ) (g : Block m → ℂ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (pairFunction n m f g) :=
  (split_preserves_volume n m).integrable_comp_of_integrable (hf.mul_prod hg)

theorem coordinates_product_toLp (f : Block n → ℂ) (g : Block m → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) :
    coordinates n m (productState volume volume (hf.toLp f) (hg.toLp g)) =
      (pair_memLp n m f g hf hg).toLp (pairFunction n m f g) := by
  apply Lp.ext
  exact (coordinates_product_coe n m f g hf hg).trans (pair_memLp n m f g hf hg).coeFn_toLp.symm

def fullFourier : ProductHilbert n m ≃ₗᵢ[ℂ] ProductHilbert n m :=
  (coordinates n m).trans ((Lp.fourierTransformₗᵢ (Joint n m) ℂ).trans (coordinates n m).symm)

theorem fullFourier_product_l1 (f : Block n → ℂ) (g : Block m → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg1 : Integrable g) (hg2 : MemLp g 2) :
    fullFourier n m (productState volume volume (hf2.toLp f) (hg2.toLp g)) =
      productState volume volume ((Lp.fourierTransformₗᵢ (Block n) ℂ) (hf2.toLp f))
        ((Lp.fourierTransformₗᵢ (Block m) ℂ) (hg2.toLp g)) := by
  apply (coordinates n m).injective
  change coordinates n m ((coordinates n m).symm (_)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (Lp.fourierTransformₗᵢ (Joint n m) ℂ)
    (coordinates n m (productState volume volume (hf2.toLp f) (hg2.toLp g))) = _
  rw [coordinates_product_toLp,
    fourier_toLp_eq (pairFunction n m f g) (pair_integrable n m f g hf1 hg1),
    fourier_toLp_eq f hf1 hf2,fourier_toLp_eq g hg1 hg2]
  apply Lp.ext
  filter_upwards [(integralFourier_memLp (pairFunction n m f g)
      (pair_integrable n m f g hf1 hg1) (pair_memLp n m f g hf2 hg2)).coeFn_toLp,
    coordinates_product_coe n m (𝓕 f) (𝓕 g) (integralFourier_memLp f hf1 hf2)
      (integralFourier_memLp g hg1 hg2)] with x hf hg
  rw [hf,hg]
  exact fourier_pair n m f g x

theorem fullFourier_eq_partials (f : ProductHilbert n m) :
    fullFourier n m f = leftFourier n m (rightFourier n m f) := by
  let U : ProductHilbert n m →L[ℂ] ProductHilbert n m := fullFourier n m
  let V : ProductHilbert n m →L[ℂ] ProductHilbert n m :=
    (leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp
      (rightFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m)
  have hs : LinearMap.ker (U-V).toLinearMap = ⊤ := by
    apply closed_submodule_total n m (testState n) (testState m) (testState_dense n) (testState_dense m)
    · exact (U-V).isClosed_ker
    · intro a b
      change U (productState volume volume (testState n a) (testState m b))-
        V (productState volume volume (testState n a) (testState m b)) = 0
      apply sub_eq_zero.mpr
      change fullFourier n m (productState volume volume (testState n a) (testState m b)) =
        leftFourier n m (rightFourier n m (productState volume volume (testState n a) (testState m b)))
      rw [rightFourier_product,leftFourier_product]
      exact fullFourier_product_l1 n m a b
        (a.continuous.integrable_of_hasCompactSupport a.hasCompactSupport)
        (a.continuous.memLp_of_hasCompactSupport a.hasCompactSupport)
        (b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport)
        (b.continuous.memLp_of_hasCompactSupport b.hasCompactSupport)
  have hf : f ∈ LinearMap.ker (U-V).toLinearMap := by rw [hs]; trivial
  exact sub_eq_zero.mp hf

theorem fullFourier_left_commutes (f : ProductHilbert n m) :
    fullFourier n m (leftFourier n m f) = leftFourier n m (fullFourier n m f) := by
  rw [fullFourier_eq_partials,← partial_transforms_commute,fullFourier_eq_partials]

#print axioms fourier_pair
#print axioms pair_integrable
#print axioms coordinates_product_toLp
#print axioms fullFourier_product_l1
#print axioms fullFourier_eq_partials
#print axioms fullFourier_left_commutes

end
end UnifiedTheory.Audit.KFCausalFullFourierProduct
