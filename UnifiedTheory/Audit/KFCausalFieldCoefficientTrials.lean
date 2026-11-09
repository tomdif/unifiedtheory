/- The nonnegative powers of the straightened field dilation coefficient
preserve Gaussian strip bounds after multiplying the repaired scalar.
The Fourier shift is proved from a contour on the analytic strip. -/
import UnifiedTheory.Audit.KFCausalComplexClockWeights
import UnifiedTheory.Audit.KFCausalDampedGaussianStrip
import UnifiedTheory.Audit.KFCausalLocalStripContour
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldCoefficientTrials
noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockWeights
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalDampedGaussianStrip
open UnifiedTheory.Audit.KFCausalGaussianContourShift
open UnifiedTheory.Audit.KFCausalLocalStripContour

def weightedTrial (ε a j : ℝ) (z : ℂ) : ℂ := fieldCoefficient ε j z*entire ε a z
def weightedLine (ε a j y : ℝ) : ℝ → ℂ := horizontal (weightedTrial ε a j) y
def stripConstant (ε a j d : ℝ) : ℝ := Real.exp ((a/2)*d^2+(j/(2*ε))^2/a)

theorem fieldCoefficient_real (ε j : ℝ) (hε : 0 < ε) (q : ℝ) :
    fieldCoefficient ε j (q:ℂ) =
      (Real.exp ((j/2)*phase ε ((chartIso ε hε).symm q)):ℂ) := by
  rw [fieldCoefficient,complexInverse_real ε hε]
  simp [complexPhase,phase,Complex.ofReal_exp]

theorem weightedLine_real (ε a j : ℝ) (hε : 0 < ε) (q : ℝ) :
    weightedLine ε a j 0 q =
      (Real.exp ((j/2)*phase ε ((chartIso ε hε).symm q)):ℂ)*
        (KFCausalCoupledDampedGaussian.dampedGaussian ε a q:ℂ) := by
  simp only [weightedLine,horizontal,Complex.ofReal_zero,zero_mul,add_zero,weightedTrial,
    fieldCoefficient_real ε j hε,entire_real]

theorem weightedTrial_differentiableAt (ε a j : ℝ) (hε : 0 < ε) (z : ℂ)
    (hz : z ∈ targetStrip ε) : DifferentiableAt ℂ (weightedTrial ε a j) z :=
  (fieldCoefficient_analytic ε j hε z hz).differentiableAt.mul
    (entire_differentiable ε a z)

theorem linear_gaussian_absorption (a b x : ℝ) (ha : 0 < a) :
    b*x ≤ (a/4)*x^2+b^2/a := by
  have hd : (b^2/a)*a=b^2 := div_mul_cancel₀ _ ha.ne'
  nlinarith [sq_nonneg ((a/2)*x-b)]

theorem weightedLine_gaussian_bound (ε a j d : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hd : d ≤ Real.pi*ε/2) (y x : ℝ) (hy : |y| ≤ d) :
    ‖weightedLine ε a j y x‖ ≤ stripConstant ε a j d*Real.exp (-(a/4)*x^2) := by
  have hz : (x:ℂ)+(y:ℂ)*Complex.I ∈ targetStrip ε := by
    change |((x:ℂ)+(y:ℂ)*Complex.I).im| ≤ Real.pi*ε/2
    simpa using hy.trans hd
  have hc := fieldCoefficient_norm_bound ε j hε hj _ hz
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hc
  have hg := strip_gaussian_bound ε a d hε ha.le hd y x hy
  change ‖fieldCoefficient ε j ((x:ℂ)+(y:ℂ)*Complex.I)*line ε a y x‖ ≤ _
  rw [norm_mul]
  apply (mul_le_mul hc hg (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [stripConstant,← Real.exp_add,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := linear_gaussian_absorption a (j/(2*ε)) x ha
  rw [show j*x/(2*ε)=(j/(2*ε))*x by ring]
  nlinarith

theorem weightedLine_continuous (ε a j y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/2) : Continuous (weightedLine ε a j y) := by
  apply KFCausalLocalStripContour.horizontal_continuous (weightedTrial ε a j) y y _ le_rfl
  intro z hz
  exact weightedTrial_differentiableAt ε a j hε z (hz.trans hy)

theorem weightedLine_integrable (ε a j y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) : Integrable (weightedLine ε a j y) := by
  apply ((integrable_exp_neg_mul_sq (by positivity : 0 < a/4)).const_mul
    (stripConstant ε a j (Real.pi*ε/2))).mono'
      (weightedLine_continuous ε a j y hε hy).aestronglyMeasurable
  exact Eventually.of_forall (fun x => weightedLine_gaussian_bound ε a j _ hε ha hj le_rfl y x hy)

theorem weightedLine_memLp (ε a j y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) : MemLp (weightedLine ε a j y) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (weightedLine_continuous ε a j y hε hy).aestronglyMeasurable).mpr
  apply ((integrable_exp_neg_mul_sq (by positivity : 0 < a/2)).const_mul
    ((stripConstant ε a j (Real.pi*ε/2))^2)).mono'
      ((weightedLine_continuous ε a j y hε hy).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := weightedLine_gaussian_bound ε a j _ hε ha hj le_rfl y x hy
  have hs := (sq_le_sq₀ (norm_nonneg _) (by unfold stripConstant; positivity)).mpr hb
  convert hs using 1
  rw [mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

theorem weightedLine_fourier (ε a j y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) (k : ℝ) :
    (𝓕 (weightedLine ε a j y)) k =
      (Real.exp (-2*Real.pi*k*y):ℂ)*(𝓕 (weightedLine ε a j 0)) k := by
  have h := fourier_shift_strip (weightedTrial ε a j) (a/4)
    (stripConstant ε a j (Real.pi*ε/2)) y
    (fun z hz => weightedTrial_differentiableAt ε a j hε z (hz.trans hy)) (by positivity)
    (fun x r hr => weightedLine_gaussian_bound ε a j _ hε ha hj le_rfl r x (hr.trans hy)) k
  change (𝓕 (weightedLine ε a j 0)) k =
    (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (weightedLine ε a j y)) k at h
  rw [h,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show -2*Real.pi*k*y+2*Real.pi*k*y=0 by ring]
  simp

#print axioms weightedTrial_differentiableAt
#print axioms fieldCoefficient_real
#print axioms weightedLine_real
#print axioms linear_gaussian_absorption
#print axioms weightedLine_gaussian_bound
#print axioms weightedLine_continuous
#print axioms weightedLine_integrable
#print axioms weightedLine_memLp
#print axioms weightedLine_fourier

end
end UnifiedTheory.Audit.KFCausalFieldCoefficientTrials
