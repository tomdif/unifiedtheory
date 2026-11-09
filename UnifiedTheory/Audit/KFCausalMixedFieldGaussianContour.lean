/- The mixed field/Gaussian line has an actual clock Fourier shift.
Both complex clock arguments stay inside the proved strip; polynomial
absorption supplies the contour envelope rather than an assumed domain. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianStrip
import UnifiedTheory.Audit.KFCausalClockFloorGaussianFourier
import UnifiedTheory.Audit.KFCausalLocalStripContour

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldGaussianContour
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalClockFloorShearBounds (Grouped)
open KFCausalMixedFieldGaussianStrip
open KFCausalClockFloorFullGaussian (third_strip_subset)
open KFCausalLocalStripContour (fourier_shift_strip)

theorem strip_pair (ε δ d y : ℝ) (hd : d+|δ| ≤ Real.pi*ε/3) (hy : |y| ≤ d) :
    |y| ≤ Real.pi*ε/3 ∧ |y+δ| ≤ Real.pi*ε/3 := by
  constructor
  · linarith [abs_nonneg δ]
  · exact (abs_add_le y δ).trans (by linarith)

def clockSlice (ε a α β δ y : ℝ) (j : Fin 2) (x : Grouped) (q : ℝ) : ℂ :=
  line ε a α β δ y j (q,x)

theorem clockSlice_bound (ε a α β δ d : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hd : d+|δ| ≤ Real.pi*ε/3) (y q : ℝ) (hy : |y| ≤ d) (j : Fin 2) (x : Grouped) :
    ‖clockSlice ε a α β δ y j x q‖ ≤
      (boundConstant α β (ratioBound ε δ) j*Real.exp (a*(d+|δ|)^2))*Real.exp (-a*q^2) := by
  have hs := strip_pair ε δ d y hd hy
  have hl := line_bound ε a α β δ y hε hα hβ hw hs.1 hs.2 j (q,x)
  have hg := KFCausalClockFloorGaussianFourier.clockSlice_bound ε a
    (reducedWidth α j) (reducedWidth β j) (d+|δ|) hε ha
    (reduced_positive α hα j).le (reduced_positive β hβ j).le
    (reduced_width_bound α β hw j) hd (y+δ) q
    ((abs_add_le y δ).trans (by linarith)) x
  have hC := boundConstant_nonnegative α β (ratioBound ε δ) hα hβ (Real.exp_pos _).le j
  exact hl.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg hC)

theorem clockSlice_fourier_shift (ε a α β δ y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y|+|δ| ≤ Real.pi*ε/3) (j : Fin 2) (x : Grouped) (k : ℝ) :
    (𝓕 (clockSlice ε a α β δ 0 j x)) k =
      (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (clockSlice ε a α β δ y j x)) k := by
  apply fourier_shift_strip (fun q => trial ε a α β δ j q x) a
    (boundConstant α β (ratioBound ε δ) j*Real.exp (a*(|y|+|δ|)^2)) y _ ha _ k
  · intro q hq
    have hs := strip_pair ε δ |y| q.im hy hq
    have hr : |(q+(δ:ℂ)*Complex.I).im| ≤ Real.pi*ε/3 := by simpa using hs.2
    exact (trial_analytic ε a α β δ hε j x q
      (third_strip_subset ε hε q hs.1) (third_strip_subset ε hε _ hr)).differentiableAt
  · intro q r hr
    exact clockSlice_bound ε a α β δ |y| hε ha.le hα hβ hw hy r q hr j x

theorem exponential_fourier_identity (ε a α β δ h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hb : |-h/2|+|δ| ≤ Real.pi*ε/3) (j : Fin 2) (x : Grouped) (k : ℝ) :
    (Real.exp (Real.pi*h*k):ℂ)*(𝓕 (clockSlice ε a α β δ 0 j x)) k =
      (𝓕 (clockSlice ε a α β δ (-h/2) j x)) k := by
  rw [clockSlice_fourier_shift ε a α β δ (-h/2) hε ha hα hβ hw hb j x k,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show Real.pi*h*k+2*Real.pi*k*(-h/2)=0 by ring]
  simp

theorem double_shift_bound (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) :
    |-h/2|+|-h/2| ≤ Real.pi*ε/3 := by
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

#print axioms strip_pair
#print axioms clockSlice_bound
#print axioms clockSlice_fourier_shift
#print axioms exponential_fourier_identity
#print axioms double_shift_bound
end
end UnifiedTheory.Audit.KFCausalMixedFieldGaussianContour
