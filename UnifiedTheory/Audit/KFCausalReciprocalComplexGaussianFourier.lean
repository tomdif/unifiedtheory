/- Exact complex Gaussian Fourier integrals for the physical antisymmetric
pair. Positive reciprocal real widths cancel in the principal half-power
normalization. This is a scalar integral identity, not a graph assertion. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierSlices
import UnifiedTheory.Audit.KFCausalPairedQuadraticFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalComplexGaussianFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalGaussianSliceDomain (gaussian)

theorem half_power_reciprocal (z : ℂ) (hz : z ≠ 0) (w : ℝ) (hw : 0 < w) :
    (z/(w:ℂ))^((1/2:ℝ):ℂ)*(z*(w:ℂ))^((1/2:ℝ):ℂ) = z := by
  have hwc : (w:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  rw [Complex.cpow_def_of_ne_zero (div_ne_zero hz hwc),
    Complex.cpow_def_of_ne_zero (mul_ne_zero hz hwc),← Complex.exp_add]
  rw [div_eq_mul_inv,← Complex.ofReal_inv,
    Complex.log_mul_ofReal (w⁻¹) (inv_pos.mpr hw) z hz,
    Complex.log_mul_ofReal w hw z hz,Real.log_inv,Complex.ofReal_neg]
  calc
    _ = Complex.exp (Complex.log z) := by congr 1; push_cast; ring
    _ = z := Complex.exp_log hz

theorem reciprocal_normalization (A : ℂ) (hA : A ≠ 0) (w : ℝ) (hw : 0 < w) :
    ((Real.pi:ℂ)/(A*(w:ℂ)))^((1/2:ℝ):ℂ)*
      ((Real.pi:ℂ)/(A/(w:ℂ)))^((1/2:ℝ):ℂ) = (Real.pi:ℂ)/A := by
  rw [← div_div,div_div_eq_mul_div]
  have hz : (Real.pi:ℂ)/A ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hA
  convert half_power_reciprocal ((Real.pi:ℂ)/A) hz w hw using 2
  ring

theorem scalar_fourier (A : ℂ) (hA : 0 < A.re) (x : ℝ) :
    (𝓕 (gaussian A)) x = ((Real.pi:ℂ)/A)^((1/2:ℝ):ℂ)*
      gaussian ((Real.pi:ℂ)^2/A) x := by
  have he : gaussian A = fun u : ℝ => Complex.exp (-A*(‖u‖:ℂ)^2) := by
    ext u
    simp [gaussian,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  rw [he,fourier_gaussian_innerProductSpace (b := A) hA]
  simp only [Module.finrank_self,Nat.cast_one,gaussian,Real.norm_eq_abs,
    ← Complex.ofReal_pow,sq_abs,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  congr 1
  congr 1
  push_cast
  ring

def product (A : ℂ) (w : ℝ) (u : Block 2) : ℂ :=
  gaussian (A*(w:ℂ)) (u 0)*gaussian (A/(w:ℂ)) (u 1)

theorem product_fourier (A : ℂ) (hA : 0 < A.re) (w : ℝ) (hw : 0 < w) (u : Block 2) :
    (𝓕 (product A w)) u = ((Real.pi:ℂ)/A)*
      gaussian ((Real.pi:ℂ)^2/(A*(w:ℂ))) (u 0)*
      gaussian ((Real.pi:ℂ)^2/(A/(w:ℂ))) (u 1) := by
  have hmul : 0 < (A*(w:ℂ)).re := by simpa using mul_pos hA hw
  have hdiv : 0 < (A/(w:ℂ)).re := by simpa using div_pos hA hw
  have hne : A ≠ 0 := by intro h; simp [h] at hA
  unfold product
  rw [KFCausalPairedQuadraticFourier.two_fourier,
    scalar_fourier _ hmul,scalar_fourier _ hdiv]
  calc
    _ = ((((Real.pi:ℂ)/(A*(w:ℂ)))^((1/2:ℝ):ℂ))*
      (((Real.pi:ℂ)/(A/(w:ℂ)))^((1/2:ℝ):ℂ)))*
      gaussian ((Real.pi:ℂ)^2/(A*(w:ℂ))) (u 0)*
      gaussian ((Real.pi:ℂ)^2/(A/(w:ℂ))) (u 1) := by ring
    _ = _ := by rw [reciprocal_normalization A hne w hw]

#print axioms half_power_reciprocal
#print axioms reciprocal_normalization
#print axioms scalar_fourier
#print axioms product_fourier
end
end UnifiedTheory.Audit.KFCausalReciprocalComplexGaussianFourier
