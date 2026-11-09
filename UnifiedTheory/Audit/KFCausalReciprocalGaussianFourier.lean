/- Reciprocal Gaussian widths in the two antisymmetric modes. Their
partial Fourier transform has a width-independent normalization and
exchanges the reciprocal widths at the physical oscillator scale. -/
import UnifiedTheory.Audit.KFCausalPairedQuadraticFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)
open KFCausalChargeGaussianProducts (block_product_memLp)

theorem scalar_fourier (a : ℝ) (ha : 0 < a) (x : ℝ) :
    (𝓕 (gaussian (a:ℂ))) x =
      (Real.sqrt (Real.pi/a):ℂ)*gaussian (Real.pi^2/a:ℝ) x := by
  have he : gaussian (a:ℂ) = fun u : ℝ => Complex.exp (-(a:ℂ)*(‖u‖:ℂ)^2) := by
    ext u
    simp [gaussian, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
  rw [he, fourier_gaussian_innerProductSpace (b := (a:ℂ)) ha]
  simp only [Module.finrank_self, Nat.cast_one]
  have hp : 0 ≤ Real.pi/a := (div_pos Real.pi_pos ha).le
  rw [← Complex.ofReal_div]
  have hs : (Real.sqrt (Real.pi/a):ℂ) = ((Real.pi/a:ℝ):ℂ)^((1/2:ℝ):ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hp]
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hs
  rw [← Complex.ofReal_div] at hs
  rw [← hs]
  congr 1
  simp only [gaussian, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
  congr 1
  push_cast
  ring

def product (a b : ℝ) (u : Block 2) : ℂ :=
  gaussian (a:ℂ) (u 0)*gaussian (b:ℂ) (u 1)

theorem product_continuous (a b : ℝ) : Continuous (product a b) := by
  unfold product gaussian
  fun_prop

theorem product_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (product a b) volume := by
  have hi : ∀ i : Fin 2, Integrable (![gaussian (a:ℂ),gaussian (b:ℂ)] i) volume := by
    intro i
    fin_cases i
    · change Integrable (gaussian (a:ℂ)) volume
      have he : KFCausalGaussianQuadraticFourier.moment a 0 = gaussian (a:ℂ) := by
        ext x
        simp [KFCausalGaussianQuadraticFourier.moment]
      rw [← he]
      exact KFCausalGaussianQuadraticFourier.moment_integrable a ha 0
    · change Integrable (gaussian (b:ℂ)) volume
      have he : KFCausalGaussianQuadraticFourier.moment b 0 = gaussian (b:ℂ) := by
        ext x
        simp [KFCausalGaussianQuadraticFourier.moment]
      rw [← he]
      exact KFCausalGaussianQuadraticFourier.moment_integrable b hb 0
  have hp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integrable_comp_of_integrable
    (Integrable.fintype_prod hi)
  simpa only [product, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Function.comp_apply] using hp

theorem product_memLp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    MemLp (product a b) 2 volume := by
  have hc : ∀ i : Fin 2, Continuous (![gaussian (a:ℂ),gaussian (b:ℂ)] i) := by
    intro i
    fin_cases i <;> exact gaussian_continuous _
  have hm : ∀ i : Fin 2, MemLp (![gaussian (a:ℂ),gaussian (b:ℂ)] i) 2 volume := by
    intro i
    fin_cases i
    · exact (gaussian_memLp_iff _).mpr ha
    · exact (gaussian_memLp_iff _).mpr hb
  simpa only [product, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ] using block_product_memLp 2 _ hc hm

theorem product_fourier (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u : Block 2) :
    (𝓕 (product a b)) u =
      (Real.sqrt (Real.pi/a)*Real.sqrt (Real.pi/b):ℝ)*
        product (Real.pi^2/a) (Real.pi^2/b) u := by
  unfold product
  rw [KFCausalPairedQuadraticFourier.two_fourier, scalar_fourier a ha, scalar_fourier b hb]
  push_cast
  ring

theorem reciprocal_normalization (α w : ℝ) (hα : 0 < α) (hw : 0 < w) :
    Real.sqrt (Real.pi/(α*w))*Real.sqrt (Real.pi/(α/w)) = Real.pi/α := by
  rw [← Real.sqrt_mul (div_pos Real.pi_pos (mul_pos hα hw)).le]
  have he : Real.pi/(α*w)*(Real.pi/(α/w)) = (Real.pi/α)^2 := by
    field_simp
  rw [he, Real.sqrt_sq (div_pos Real.pi_pos hα).le]

theorem reciprocal_fourier (α w c : ℝ) (hα : 0 < α) (hw : 0 < w)
    (hmatch : Real.pi^2/α = α*c^2) (u : Block 2) :
    (𝓕 (product (α*w) (α/w))) u =
      (Real.pi/α:ℝ)*product ((α/w)*c^2) ((α*w)*c^2) u := by
  rw [product_fourier _ _ (mul_pos hα hw) (div_pos hα hw),
    reciprocal_normalization α w hα hw]
  have h1 : Real.pi^2/(α*w) = (α/w)*c^2 := by
    rw [← div_div, hmatch]
    ring
  have h2 : Real.pi^2/(α/w) = (α*w)*c^2 := by
    calc
      _ = (Real.pi^2/α)*w := by field_simp
      _ = _ := by rw [hmatch]; ring
  rw [h1,h2]

#print axioms scalar_fourier
#print axioms product_continuous
#print axioms product_integrable
#print axioms product_memLp
#print axioms product_fourier
#print axioms reciprocal_normalization
#print axioms reciprocal_fourier
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianFourier
