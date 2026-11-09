/- Exact Fourier transforms of the complex-shifted repaired scalar trials.
The Gaussian strip includes its boundary. These are integral identities;
the actual unbounded operator graph is identified in a separate module. -/
import UnifiedTheory.Audit.KFCausalDampedGaussianTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedDampedScalar
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalDampedGaussianStrip
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalFourierStripDecay
open UnifiedTheory.Audit.KFCausalGaussianContourShift

theorem line_fourier (ε a y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (k : ℝ) :
    (𝓕 (line ε a y)) k = (Real.exp (-2*Real.pi*k*y):ℂ)*(𝓕 (realTrial ε a)) k := by
  have h := fourier_shift (entire ε a) (entire_differentiable ε a)
    (a/2) (Real.exp ((a/2)*(Real.pi*ε/2)^2)) y (by positivity)
    (fun x r hr => strip_gaussian_bound ε a (Real.pi*ε/2) hε ha.le le_rfl r x (hr.trans hy)) k
  change (𝓕 (line ε a 0)) k = _ at h
  rw [line_zero] at h
  change (𝓕 (realTrial ε a)) k = (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (line ε a y)) k at h
  rw [h,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  have he : -2*Real.pi*k*y+2*Real.pi*k*y=0 := by ring
  rw [he,Real.exp_zero,Complex.ofReal_one,one_mul]

def shiftedScalar (ε a p y : ℝ) (q : ℝ) : ℂ :=
  (Real.exp (-2*Real.pi*p*y):ℂ)*modulate p (line ε a y) q

theorem shiftedScalar_continuous (ε a p y : ℝ) : Continuous (shiftedScalar ε a p y) :=
  continuous_const.mul (modulate_continuous p _ (line_continuous ε a y))

theorem shiftedScalar_integrable (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) : Integrable (shiftedScalar ε a p y) :=
  (modulate_integrable p _ (line_integrable ε a y hε.le ha
    (cosine_nonnegative ε (Real.pi*ε/2) y hε le_rfl hy))).const_mul _

theorem shiftedScalar_square (ε a p y q : ℝ) :
    ‖shiftedScalar ε a p y q‖^2 = Real.exp (-4*Real.pi*p*y)*‖line ε a y q‖^2 := by
  rw [shiftedScalar,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),modulate_norm,← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem shiftedScalar_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) : MemLp (shiftedScalar ε a p y) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (shiftedScalar_continuous ε a p y).aestronglyMeasurable).mpr
  simp_rw [shiftedScalar_square]
  exact (line_square_integrable ε a y hε.le ha
    (cosine_nonnegative ε (Real.pi*ε/2) y hε le_rfl hy)).const_mul _

theorem shiftedScalar_fourier (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (k : ℝ) :
    (𝓕 (shiftedScalar ε a p y)) k =
      (Real.exp (-2*Real.pi*k*y):ℂ)*(𝓕 (modulate p (realTrial ε a))) k := by
  have hc (c : ℂ) (f : ℝ → ℂ) : (𝓕 (fun q => c*f q)) k = c*(𝓕 f) k := by
    simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext q
    ring
  change (𝓕 (fun q => (Real.exp (-2*Real.pi*p*y):ℂ)*modulate p (line ε a y) q)) k = _
  rw [hc,fourier_modulate,fourier_modulate,line_fourier ε a y hε ha hy,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show -2*Real.pi*p*y+-2*Real.pi*(k-p)*y = -2*Real.pi*k*y by ring]

theorem shiftedScalar_zero (ε a p : ℝ) : shiftedScalar ε a p 0=modulate p (realTrial ε a) := by
  funext q
  simp [shiftedScalar,line_zero]

#print axioms line_fourier
#print axioms shiftedScalar_continuous
#print axioms shiftedScalar_integrable
#print axioms shiftedScalar_square
#print axioms shiftedScalar_memLp
#print axioms shiftedScalar_fourier
#print axioms shiftedScalar_zero

end
end UnifiedTheory.Audit.KFCausalShiftedDampedScalar
