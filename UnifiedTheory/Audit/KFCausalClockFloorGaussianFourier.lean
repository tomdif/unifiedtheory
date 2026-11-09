/- Contour translation for each clock fibre of the full sheared Gaussian.
The bound is derived from its positive transverse quadratic form. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
import UnifiedTheory.Audit.KFCausalLocalStripContour
import UnifiedTheory.Audit.KFCausalL2FourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianFourier
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalGaussianContourShift (horizontal)
open UnifiedTheory.Audit.KFCausalLocalStripContour (fourier_shift_strip)

def clockSlice (ε a α β y : ℝ) (x : Grouped) (q : ℝ) : ℂ := line ε a α β y (q,x)

theorem clockSlice_continuous (ε a α β y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (x : Grouped) : Continuous (clockSlice ε a α β y x) :=
  (line_continuous ε a α β y hε hy).comp (continuous_id.prodMk continuous_const)

theorem clockSlice_bound (ε a α β d : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hd : d ≤ Real.pi*ε/3)
    (y q : ℝ) (hy : |y| ≤ d) (x : Grouped) :
    ‖clockSlice ε a α β y x q‖ ≤ Real.exp (a*d^2)*Real.exp (-a*q^2) := by
  have hz : |(((q:ℂ)+(y:ℂ)*Complex.I):ℂ).im| ≤ Real.pi*ε/3 := by
    simpa using hy.trans hd
  have hp := packet_norm_le_one α β hα hβ hw _ (inverse_im_third_strip ε hε _ hz) x
  have hs : y^2 ≤ d^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) ((abs_nonneg y).trans hy)).mpr hy
  rw [clockSlice,line,trial,norm_mul]
  calc
    _ ≤ ‖clockFactor a ((q:ℂ)+(y:ℂ)*Complex.I)‖ * 1 :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_one,clockFactor_norm,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hs ha]

theorem clockSlice_integrable (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (x : Grouped) : Integrable (clockSlice ε a α β y x) := by
  apply ((integrable_exp_neg_mul_sq ha).const_mul (Real.exp (a*y^2))).mono'
    (clockSlice_continuous ε a α β y hε hy x).aestronglyMeasurable
  filter_upwards [] with q
  simpa only [sq_abs] using clockSlice_bound ε a α β |y| hε ha.le hα hβ hw hy y q le_rfl x

theorem clockSlice_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (x : Grouped) : MemLp (clockSlice ε a α β y x) 2 volume := by
  have hm : AEStronglyMeasurable (clockSlice ε a α β y x) volume :=
    (clockSlice_continuous ε a α β y hε hy x).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply ((integrable_exp_neg_mul_sq (by positivity : 0 < 2*a)).const_mul
    (Real.exp (2*a*y^2))).mono' (hm.norm.pow 2)
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := clockSlice_bound ε a α β |y| hε ha.le hα hβ hw hy y q le_rfl x
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  convert hs using 1
  rw [mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  simp only [sq_abs,Nat.cast_ofNat]
  congr 1 <;> congr 1 <;> ring

theorem clockSlice_fourier_shift (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (x : Grouped) (k : ℝ) :
    (𝓕 (clockSlice ε a α β 0 x)) k =
      (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (clockSlice ε a α β y x)) k := by
  apply fourier_shift_strip (fun q => trial ε a α β q x) a (Real.exp (a*|y|^2)) y _ ha _ k
  · intro q hq
    exact (trial_analytic ε a α β hε x q (third_strip_subset ε hε q (hq.trans hy))).differentiableAt
  · intro q r hr
    exact clockSlice_bound ε a α β |y| hε ha.le hα hβ hw hy r q hr x

theorem exponential_fourier_identity (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (x : Grouped) (k : ℝ) :
    (Real.exp (Real.pi*hbar*k):ℂ)*(𝓕 (clockSlice ε a α β 0 x)) k =
      (𝓕 (clockSlice ε a α β (-hbar/2) x)) k := by
  have hy : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  rw [clockSlice_fourier_shift ε a α β (-hbar/2) hε ha hα hβ hw hy x k,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  have he : Real.pi*hbar*k+2*Real.pi*k*(-hbar/2)=0 := by ring
  rw [he,Real.exp_zero,Complex.ofReal_one,one_mul]

#print axioms clockSlice_continuous
#print axioms clockSlice_bound
#print axioms clockSlice_integrable
#print axioms clockSlice_memLp
#print axioms clockSlice_fourier_shift
#print axioms exponential_fourier_identity

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianFourier
