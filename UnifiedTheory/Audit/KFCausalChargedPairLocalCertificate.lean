/- A nonzero complex transverse cross integral with the actual ordered
shift and the physical Gaussian widths. The quadratic multiplier is
transported by the same complex position map as the base Gaussian.
This certificate does not supply the excited state's operator graphs,
charge identification, full clock integral, or kinetic cross terms. -/
import UnifiedTheory.Audit.KFCausalChargedPairTransverseCoupling
import UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalChargedPairLocalCertificate
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (exponent position)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargedPairCoordinates (pairPolynomial shifted_pair)
open KFCausalChargedPairTransverseCoupling
open KFCausalQuarticPlaneDomination (potential)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

def orderedDensity (α β : ℝ) (r : ℂ) (q : Transverse) : ℂ :=
  conj (Complex.exp (exponent α β 0 r q)) *
    ((position r q 0*position r q 1-position r q 2*position r q 3)*
      Complex.exp (exponent α β 0 r q)) * (potential (pointField q):ℂ)

theorem orderedDensity_identity (α β : ℝ) (r : ℂ) (q : Transverse) :
    orderedDensity α β r q = r^2*(transverseDensity α β r q:ℂ) := by
  rw [orderedDensity,shifted_pair]
  rw [show conj (Complex.exp (exponent α β 0 r q)) *
      (r^2*(pairPolynomial q:ℂ)*Complex.exp (exponent α β 0 r q)) *
      (potential (pointField q):ℂ) =
    r^2*(pairPolynomial q:ℂ)*(potential (pointField q):ℂ)*
      (conj (Complex.exp (exponent α β 0 r q))*Complex.exp (exponent α β 0 r q)) by ring,
    Complex.conj_mul']
  simp only [transverseDensity,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

theorem ordered_integral (α β : ℝ) (r : ℂ) :
    (∫ q, orderedDensity α β r q) = r^2*(∫ q, transverseDensity α β r q:ℝ) := by
  simp_rw [orderedDensity_identity]
  rw [integral_const_mul,integral_complex_ofReal]

theorem actual_transverse_integrable (α β ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    Integrable (transverseDensity α β (scale ε y s)) volume := by
  have hn := actual_transverse_integral_negative α β ε y s hα hβ hw hε hy hy0
  by_contra hi
  rw [integral_undef hi] at hn
  exact (lt_irrefl 0) hn

theorem actual_ordered_integrable (α β ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    Integrable (orderedDensity α β (scale ε y s)) volume := by
  have hi := actual_transverse_integrable α β ε y s hα hβ hw hε hy hy0
  have hic : Integrable (fun q => (transverseDensity α β (scale ε y s) q:ℂ)) volume := hi.ofReal
  convert hic.const_mul ((scale ε y s)^2) using 1
  funext q
  exact orderedDensity_identity α β (scale ε y s) q

theorem actual_ordered_integral_re_negative (α β ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    (∫ q, orderedDensity α β (scale ε y s) q).re < 0 := by
  rw [ordered_integral]
  have hn := actual_transverse_integral_negative α β ε y s hα hβ hw hε hy hy0
  have hp := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy
  simpa only [pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using mul_neg_of_pos_of_neg hp hn

theorem actual_ordered_integral_ne_zero (α β ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    (∫ q, orderedDensity α β (scale ε y s) q) ≠ 0 := by
  intro hz
  have hn := actual_ordered_integral_re_negative α β ε y s hα hβ hw hε hy hy0
  rw [hz,Complex.zero_re] at hn
  exact (lt_irrefl 0) hn

theorem physical_integral_re_negative (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    (∫ q, orderedDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) s) q).re < 0 := by
  exact actual_ordered_integral_re_negative _ _ ε (-h/2) s
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    hε (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
    (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num))

theorem physical_integral_ne_zero (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    (∫ q, orderedDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) s) q) ≠ 0 := by
  intro hz
  have hn := physical_integral_re_negative ε h s hε hh hb
  rw [hz,Complex.zero_re] at hn
  exact (lt_irrefl 0) hn

#print axioms orderedDensity_identity
#print axioms ordered_integral
#print axioms actual_transverse_integrable
#print axioms actual_ordered_integrable
#print axioms actual_ordered_integral_re_negative
#print axioms actual_ordered_integral_ne_zero
#print axioms physical_integral_re_negative
#print axioms physical_integral_ne_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairLocalCertificate
