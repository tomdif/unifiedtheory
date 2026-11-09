/- Real polarization identifies the exact transverse response integral.
The mixed density is an inner product of two whole profiles. -/
import UnifiedTheory.Audit.KFCausalPairedSpanCoefficientDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanCrossKernel
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedSpanMoments (Coefficients value mixedCoefficient density density_integrable value_integral)
open KFCausalPairedSpanKernel (physicalDensity density_reconstruct)
open KFCausalPairedSpanCoefficientDifferential (coefficientRate crossValue)
open KFCausalChargedPairCoordinates
open KFCausalQuarticPlaneDomination (potential)
open KFCausalRelativeGaussianDifferential (exponent)
open KFCausalMatterOrderedDomain (pointField)

def profile (α β : ℝ) (r : ℂ) (c : Coefficients) (q : Transverse) : ℂ :=
  (c.1+c.2*r^2*(pairPolynomial q:ℂ))*Complex.exp (exponent α β 0 r q)
def crossDensity (α β : ℝ) (r : ℂ) (c d : Coefficients) (q : Transverse) : ℝ :=
  2*potential (pointField q)*(conj (profile α β r c q)*profile α β r d q).re

theorem real_polarization (u v : ℂ) :
    (‖u+v‖^2-‖u-v‖^2)/2 = 2*(conj u*v).re := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem coefficientRate_polarization (α β : ℝ) (r : ℂ) (c d : Coefficients) :
    coefficientRate α β r c d = (value α β r (c+d)-value α β r (c-d))/2 := by
  simp only [coefficientRate,crossValue,value,mixedCoefficient,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub,Complex.normSq_apply,Complex.div_ofNat_re,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem crossDensity_polarization (α β : ℝ) (r : ℂ) (c d : Coefficients) (q : Transverse) :
    crossDensity α β r c d q =
      (physicalDensity α β r (c+d) q-physicalDensity α β r (c-d) q)/2 := by
  have hp : profile α β r (c+d) q = profile α β r c q+profile α β r d q := by
    simp only [profile,Prod.fst_add,Prod.snd_add]
    ring
  have hm : profile α β r (c-d) q = profile α β r c q-profile α β r d q := by
    simp only [profile,Prod.fst_sub,Prod.snd_sub]
    ring
  change _ = (potential (pointField q)*‖profile α β r (c+d) q‖^2-
    potential (pointField q)*‖profile α β r (c-d) q‖^2)/2
  rw [hp,hm]
  have he := real_polarization (profile α β r c q) (profile α β r d q)
  unfold crossDensity
  calc
    _ = potential (pointField q)*(2*(conj (profile α β r c q)*profile α β r d q).re) := by ring
    _ = _ := by rw [← he]; ring

theorem crossDensity_integral (α β : ℝ) (r : ℂ) (c d : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    (∫ q, crossDensity α β r c d q) = coefficientRate α β r c d := by
  rw [integral_coordinates r]
  simp_rw [crossDensity_polarization,density_reconstruct]
  rw [integral_div,integral_sub (density_integrable α β (c+d) r hA hB hβ)
    (density_integrable α β (c-d) r hA hB hβ),coefficientRate_polarization,
    value_integral α β (c+d) r hA hB hβ,value_integral α β (c-d) r hA hB hβ]
  ring

#print axioms real_polarization
#print axioms coefficientRate_polarization
#print axioms crossDensity_polarization
#print axioms crossDensity_integral
end
end UnifiedTheory.Audit.KFCausalPairedSpanCrossKernel
