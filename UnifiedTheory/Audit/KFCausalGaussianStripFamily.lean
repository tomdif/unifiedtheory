/- Bounded analytic multipliers may also depend on the transverse
coordinate. The full Fourier shift follows by scalar contour shifting on
each transverse fiber and Fubini. All bounds are uniform in that fiber. -/
import UnifiedTheory.Audit.KFCausalGaussianStrip
import UnifiedTheory.Audit.KFCausalClockFourierFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalGaussianStripFamily
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalClockFourierFubini

def trial (F : ℂ → TailSpace → ℂ) (v : Space) (q : ℂ) (z : TailSpace) : ℂ :=
  F q z*clockFactor Real.pi (q+(v 0:ℂ))*gaussian (z+tail v)
def line (F : ℂ → TailSpace → ℂ) (v : Space) (y : ℝ) (w : ℝ × TailSpace) : ℂ :=
  trial F v ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2
def spectralLine (F : ℂ → TailSpace → ℂ) (v : Space) (y : ℝ) : Space → ℂ :=
  line F v y ∘ euclideanSplit

variable (F : ℂ → TailSpace → ℂ) (v : Space) (d M : ℝ)
  (hF : ∀ z q, |q.im| ≤ d → AnalyticAt ℂ (fun q => F q z) q)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖F q z‖ ≤ M)

include hC in
theorem line_continuous (y : ℝ) (hy : |y| ≤ d) : Continuous (line F v y) :=
  ((hC y hy).mul (show Continuous (fun w : ℝ × TailSpace =>
    clockFactor Real.pi ((w.1:ℂ)+(y:ℂ)*Complex.I+(v 0:ℂ))) by unfold clockFactor; fun_prop)).mul
      (gaussian_continuous.comp (by fun_prop))

include hC in
theorem spectralLine_continuous (y : ℝ) (hy : |y| ≤ d) : Continuous (spectralLine F v y) :=
  (line_continuous F v d hC y hy).comp
    ((by fun_prop : Continuous (fun x : Space => x 0)).prodMk KFCausalGaussianStrip.tail_continuous)

include hB in
theorem spectralLine_bound (y : ℝ) (hy : |y| ≤ d) (x : Space) :
    ‖spectralLine F v y x‖ ≤ (M*Real.exp (Real.pi*y^2))*‖gaussian (x+v)‖ :=
  KFCausalGaussianStrip.spectralLine_bound (fun q => F q (tail x)) v d M
    (fun q hq => hB q hq (tail x)) y hy x

include hC hB in
theorem spectralLine_integrable (y : ℝ) (hy : |y| ≤ d) : Integrable (spectralLine F v y) := by
  have hi : Integrable (fun x : Space => gaussian (x+v)) :=
    (measurePreserving_add_right volume v).integrable_comp_of_integrable gaussian_integrable
  apply (hi.norm.const_mul (M*Real.exp (Real.pi*y^2))).mono'
    (spectralLine_continuous F v d hC y hy).aestronglyMeasurable
  exact Filter.Eventually.of_forall (spectralLine_bound F v d M hB y hy)

include hC hM hB in
theorem spectralLine_memLp (y : ℝ) (hy : |y| ≤ d) : MemLp (spectralLine F v y) 2 := by
  have hi : MemLp (fun x : Space => gaussian (x+v)) 2 :=
    gaussian_memLp.comp_measurePreserving (measurePreserving_add_right volume v)
  apply (hi.const_mul (M*Real.exp (Real.pi*y^2):ℂ)).of_le
    (spectralLine_continuous F v d hC y hy).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hM,abs_of_pos (Real.exp_pos _)] using spectralLine_bound F v d M hB y hy x

include hC hB in
theorem line_integrable (y : ℝ) (hy : |y| ≤ d) : Integrable (line F v y) := by
  have h := euclideanSplit_preserves_volume.symm.integrable_comp_of_integrable
    (spectralLine_integrable F v d M hC hB y hy)
  simpa only [spectralLine,Function.comp_def,MeasurableEquiv.apply_symm_apply] using h

include hF hM hB in
theorem clock_fourier_shift (y : ℝ) (hy : |y| ≤ d) (z : TailSpace) (k : ℝ) :
    (𝓕 (fun q : ℝ => line F v 0 (q,z))) k =
      (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (fun q : ℝ => line F v y (q,z))) k :=
  KFCausalGaussianStrip.clock_fourier_shift (fun q => F q z) v d M
    (hF z) hM (fun q hq => hB q hq z) y hy z k

include hF hC hM hB in
theorem full_fourier_shift (hbar : ℝ) (hs : |-hbar/2| ≤ d) (k : Space) :
    (exponentialWeight hbar k:ℂ)*(𝓕 (spectralLine F v 0)) k =
      (𝓕 (spectralLine F v (-hbar/2))) k := by
  have h0 : |(0:ℝ)| ≤ d := by simpa only [abs_zero] using (abs_nonneg (-hbar/2)).trans hs
  have hpoint (q : ℝ) (z : TailSpace) :
      (Real.exp (Real.pi*hbar*q):ℂ)*clockFourier (line F v 0) (q,z) =
        clockFourier (line F v (-hbar/2)) (q,z) := by
    change (Real.exp (Real.pi*hbar*q):ℂ)*(𝓕 (fun r : ℝ => line F v 0 (r,z))) q = _
    rw [clock_fourier_shift F v d M hF hM hB (-hbar/2) hs z q,
      ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    have he : Real.pi*hbar*q+2*Real.pi*q*(-hbar/2)=0 := by ring
    rw [he,Real.exp_zero,Complex.ofReal_one,one_mul]
    rfl
  unfold spectralLine
  rw [fourier_iterated _ (line_continuous F v d hC 0 h0) (line_integrable F v d M hC hB 0 h0),
    fourier_iterated _ (line_continuous F v d hC (-hbar/2) hs) (line_integrable F v d M hC hB (-hbar/2) hs)]
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul,exponentialWeight]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← hpoint]
  ring

#print axioms line_continuous
#print axioms spectralLine_continuous
#print axioms spectralLine_bound
#print axioms spectralLine_integrable
#print axioms spectralLine_memLp
#print axioms line_integrable
#print axioms clock_fourier_shift
#print axioms full_fourier_shift

end
end UnifiedTheory.Audit.KFCausalGaussianStripFamily
