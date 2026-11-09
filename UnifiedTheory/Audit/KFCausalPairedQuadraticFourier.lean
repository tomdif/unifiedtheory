/- The two antisymmetric modes have an exact quadratic-difference Fourier
formula. The scalar moment constants cancel, leaving the required radial
imbalance coefficient. -/
import UnifiedTheory.Audit.KFCausalGaussianQuadraticFourier
import UnifiedTheory.Audit.KFCausalChargeGaussianProducts
import UnifiedTheory.Audit.KFCausalChargeGaussianIdentities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPairedQuadraticFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalGaussianQuadraticFourier (moment moment_continuous moment_integrable moment_memLp)
open KFCausalChargeGaussianProducts (gaussian)

theorem two_fourier (f g : ℝ → ℂ) (w : Block 2) :
    (𝓕 (fun u : Block 2 => f (u 0)*g (u 1))) w = (𝓕 f) (w 0)*(𝓕 g) (w 1) := by
  let A : ℝ → ℂ := fun x => (Real.fourierChar (-(x*w 0)):ℂ)*f x
  let B : ℝ → ℂ := fun x => (Real.fourierChar (-(x*w 1)):ℂ)*g x
  calc
    _ = ∫ u : Block 2, A (u 0)*B (u 1) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [A,B,PiLp.inner_apply,Fin.sum_univ_succ,RCLike.inner_apply,
        conj_trivial,Fin.sum_univ_zero,add_zero,neg_add,AddChar.map_add_eq_mul,
        Circle.coe_mul,Circle.smul_def,smul_eq_mul]
      change (Real.fourierChar (-(w 0*u 0)):ℂ)*(Real.fourierChar (-(w 1*u 1)):ℂ)*
        (f (u 0)*g (u 1)) = _
      rw [mul_comm (w 0) (u 0),mul_comm (w 1) (u 1)]
      ring
    _ = ∫ u : Fin 2 → ℝ, A (u 0)*B (u 1) :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding
        (fun u : Fin 2 → ℝ => A (u 0)*B (u 1))
    _ = (∫ x, A x)*(∫ x, B x) := by
      simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
        Matrix.cons_val_zero,Matrix.cons_val_succ] using
        integral_fintype_prod_volume_eq_prod (fun i : Fin 2 => ![A,B] i)
    _ = _ := by
      simp only [A,B,Real.fourier_eq,RCLike.inner_apply,conj_trivial,
        Circle.smul_def,smul_eq_mul]
      congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with x <;> congr 2 <;> ring

def product (α : ℝ) (n m : ℕ) (u : Block 2) : ℂ := moment α n (u 0)*moment α m (u 1)

theorem product_integrable (α : ℝ) (hα : 0 < α) (n m : ℕ) :
    Integrable (product α n m) volume := by
  have hi : ∀ i : Fin 2, Integrable (![moment α n,moment α m] i) volume := by
    intro i
    fin_cases i
    · exact moment_integrable α hα n
    · exact moment_integrable α hα m
  have hp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integrable_comp_of_integrable
    (Integrable.fintype_prod hi)
  simpa only [product,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Function.comp_apply] using hp

theorem product_memLp (α : ℝ) (hα : 0 < α) (n m : ℕ) :
    MemLp (product α n m) 2 volume := by
  have hc : ∀ i : Fin 2, Continuous (![moment α n,moment α m] i) := by
    intro i
    fin_cases i <;> exact moment_continuous α _
  have hm : ∀ i : Fin 2, MemLp (![moment α n,moment α m] i) 2 volume := by
    intro i
    fin_cases i <;> exact moment_memLp α hα _
  simpa only [product,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ] using
    KFCausalChargeGaussianProducts.block_product_memLp 2 _ hc hm

theorem product_gaussian (α : ℝ) (u : Block 2) :
    product α 0 0 u = gaussian 2 α u := by
  simp only [product,moment,pow_zero,one_mul,KFCausalGaussianSliceDomain.gaussian,
    gaussian,← Complex.exp_add,← Complex.ofReal_pow,
    KFCausalChargeGaussianIdentities.norm_two_square]
  congr 1
  push_cast
  ring

def difference (α : ℝ) (u : Block 2) : ℂ := product α 2 0 u-product α 0 2 u

theorem difference_polynomial (α : ℝ) (u : Block 2) :
    difference α u = ((u 0:ℂ)^2-(u 1:ℂ)^2)*gaussian 2 α u := by
  rw [← product_gaussian]
  simp only [difference,product,moment,pow_zero,one_mul]
  ring

theorem difference_integrable (α : ℝ) (hα : 0 < α) : Integrable (difference α) volume :=
  (product_integrable α hα 2 0).sub (product_integrable α hα 0 2)

theorem difference_memLp (α : ℝ) (hα : 0 < α) : MemLp (difference α) 2 volume :=
  (product_memLp α hα 2 0).sub (product_memLp α hα 0 2)

theorem difference_fourier (α : ℝ) (hα : 0 < α) (w : Block 2) :
    (𝓕 (difference α)) w =
      (-(Real.pi:ℂ)^2/(α:ℂ)^2)*((w 0:ℂ)^2-(w 1:ℂ)^2)*(𝓕 (gaussian 2 α)) w := by
  have hs : (𝓕 (difference α)) w =
      (𝓕 (product α 2 0)) w-(𝓕 (product α 0 2)) w := by
    simp only [Real.fourier_eq,difference,smul_sub]
    exact integral_sub
      ((Real.fourierIntegral_convergent_iff w).mpr (product_integrable α hα 2 0))
      ((Real.fourierIntegral_convergent_iff w).mpr (product_integrable α hα 0 2))
  have h0 : gaussian 2 α = product α 0 0 := funext (fun u => (product_gaussian α u).symm)
  rw [hs,h0]
  unfold product
  rw [two_fourier,two_fourier,two_fourier,
    KFCausalGaussianQuadraticFourier.second_moment_fourier α hα,
    KFCausalGaussianQuadraticFourier.second_moment_fourier α hα]
  ring

#print axioms two_fourier
#print axioms product_integrable
#print axioms product_memLp
#print axioms product_gaussian
#print axioms difference_polynomial
#print axioms difference_integrable
#print axioms difference_memLp
#print axioms difference_fourier
end
end UnifiedTheory.Audit.KFCausalPairedQuadraticFourier
