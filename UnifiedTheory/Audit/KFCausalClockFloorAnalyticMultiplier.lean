/- Bounded analytic clock multipliers preserve the coherent strip estimates
and its exact clock Fourier shift. All hypotheses concern the multiplier;
no operator-domain preservation is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorAnalyticMultiplier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorCoherentFourier
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (third_strip_subset)
open UnifiedTheory.Audit.KFCausalLocalStripContour (fourier_shift_strip)

def line (F : ℂ → ℂ) (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ)
    (w : ℝ × Grouped) : ℂ :=
  F ((w.1:ℂ)+(y:ℂ)*Complex.I) * KFCausalClockFloorCoherentStrip.line ε a α β p b y w

def clockSlice (F : ℂ → ℂ) (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ)
    (x : Grouped) (q : ℝ) : ℂ := line F ε a α β p b y (q,x)

variable (F : ℂ → ℂ) (ε a α β p M : ℝ) (b : Fin 5 → ℂ)
  (hε : 0 < ε)
  (hF : ∀ q : ℂ, |q.im| ≤ Real.pi*ε/3 → AnalyticAt ℂ F q)
  (hM : 0 ≤ M) (hB : ∀ q : ℂ, |q.im| ≤ Real.pi*ε/3 → ‖F q‖ ≤ M)

include hε hF in
theorem line_continuous (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (line F ε a α β p b y) := by
  have hc : Continuous (fun w : ℝ × Grouped => F ((w.1:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (hF _ (by simpa using hy)).continuousAt.comp (by fun_prop)
  exact hc.mul (KFCausalClockFloorCoherentStrip.line_continuous ε a α β p b y hε hy)

include hB in
theorem line_bound (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (w : ℝ × Grouped) :
    ‖line F ε a α β p b y w‖ ≤ M * ‖KFCausalClockFloorCoherentStrip.line ε a α β p b y w‖ := by
  rw [line,norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _ (by simpa using hy)) (norm_nonneg _)

include hε hF hM hB in
theorem line_memLp (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : MemLp (line F ε a α β p b y) 2 := by
  apply ((KFCausalClockFloorCoherentStrip.line_memLp ε a α β p b y hε ha hα hβ hw hy).const_mul (M:ℂ)).of_le
    (line_continuous F ε a α β p b hε hF y hy).aestronglyMeasurable
  filter_upwards [] with w
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM] using
    line_bound F ε a α β p M b hB y hy w

include hε hF hB in
theorem line_integrable (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Integrable (line F ε a α β p b y) := by
  apply ((KFCausalClockFloorCoherentStrip.line_integrable ε a α β p b y hε ha hα hβ hw hy).norm.const_mul M).mono'
    (line_continuous F ε a α β p b hε hF y hy).aestronglyMeasurable
  exact Filter.Eventually.of_forall (line_bound F ε a α β p M b hB y hy)

include hε hM hB in
theorem clockSlice_bound (ha : 0 ≤ a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (d : ℝ) (hd : d ≤ Real.pi*ε/3) (y q : ℝ) (hy : |y| ≤ d) (x : Grouped) :
    ‖clockSlice F ε a α β p b y x q‖ ≤
      (M*(envelopeConstant α β p b*Real.exp (a*d^2)))*Real.exp (-a*q^2) := by
  exact (line_bound F ε a α β p M b hB y (hy.trans hd) (q,x)).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (KFCausalClockFloorCoherentFourier.clockSlice_bound ε a α β p b d hε ha hα hβ hw hd y q hy x) hM))

include hε hF hM hB in
theorem clockSlice_fourier_shift (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (x : Grouped) (k : ℝ) :
    (𝓕 (clockSlice F ε a α β p b 0 x)) k =
      (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (clockSlice F ε a α β p b y x)) k := by
  apply fourier_shift_strip (fun q => F q * trial ε a α β p b q x) a
    (M*(envelopeConstant α β p b*Real.exp (a*|y|^2))) y _ ha _ k
  · intro q hq
    exact ((hF q (hq.trans hy)).mul
      (trial_analytic ε a α β p b hε x q (third_strip_subset ε hε q (hq.trans hy)))).differentiableAt
  · intro q r hr
    exact clockSlice_bound F ε a α β p M b hε hM hB ha.le hα hβ hw |y| hy r q hr x

include hε hF hM hB in
theorem exponential_fourier_identity (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3) (x : Grouped) (k : ℝ) :
    (Real.exp (Real.pi*hbar*k):ℂ)*(𝓕 (clockSlice F ε a α β p b 0 x)) k =
      (𝓕 (clockSlice F ε a α β p b (-hbar/2) x)) k := by
  have hy : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  rw [clockSlice_fourier_shift F ε a α β p M b hε hF hM hB ha hα hβ hw (-hbar/2) hy x k,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  have he : Real.pi*hbar*k+2*Real.pi*k*(-hbar/2)=0 := by ring
  rw [he,Real.exp_zero,Complex.ofReal_one,one_mul]

#print axioms line_continuous
#print axioms line_bound
#print axioms line_memLp
#print axioms line_integrable
#print axioms clockSlice_bound
#print axioms clockSlice_fourier_shift
#print axioms exponential_fourier_identity

end
end UnifiedTheory.Audit.KFCausalClockFloorAnalyticMultiplier
