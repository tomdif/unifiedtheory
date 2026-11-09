/- Translated Euclidean Gaussians with bounded analytic clock multipliers.
The strip estimates are derived from explicit Gaussian norms. -/
import UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
import UnifiedTheory.Audit.KFCausalEuclideanClockSplit
import UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
import UnifiedTheory.Audit.KFCausalLocalStripContour

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianStrip
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor clockFactor_norm)
open UnifiedTheory.Audit.KFCausalLocalStripContour (fourier_shift_strip)

theorem tail_continuous : Continuous tail := by unfold tail; fun_prop

theorem tail_add (x v : Space) : tail (x+v) = tail x+tail v := rfl

theorem norm_square_split (x : Space) : ‖x‖^2 = (x 0)^2+‖tail x‖^2 := by
  simpa only [real_inner_self_eq_norm_sq,pow_two] using inner_split x x

theorem gaussian_split (x : Space) :
    gaussian x = clockFactor Real.pi (x 0:ℂ)*gaussian (tail x) := by
  unfold gaussian clockFactor
  rw [← Complex.exp_add,← Complex.ofReal_pow,norm_square_split]
  push_cast
  congr 1
  ring

def trial (F : ℂ → ℂ) (v : Space) (q : ℂ) (z : TailSpace) : ℂ :=
  F q*clockFactor Real.pi (q+(v 0:ℂ))*gaussian (z+tail v)

def line (F : ℂ → ℂ) (v : Space) (y : ℝ) (w : ℝ × TailSpace) : ℂ :=
  trial F v ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2

def spectralLine (F : ℂ → ℂ) (v : Space) (y : ℝ) : Space → ℂ :=
  line F v y ∘ euclideanSplit

theorem spectralLine_one_zero (v x : Space) :
    spectralLine (fun _ => 1) v 0 x = gaussian (x+v) := by
  rw [gaussian_split,tail_add]
  simp [spectralLine,line,trial,euclideanSplit_apply,Complex.ofReal_add]

theorem spectralLine_norm (F : ℂ → ℂ) (v : Space) (y : ℝ) (x : Space) :
    ‖spectralLine F v y x‖ =
      ‖F ((x 0:ℂ)+(y:ℂ)*Complex.I)‖*Real.exp (Real.pi*y^2)*‖gaussian (x+v)‖ := by
  have he : (x 0:ℂ)+(y:ℂ)*Complex.I+(v 0:ℂ) = ((x 0+v 0:ℝ):ℂ)+(y:ℂ)*Complex.I := by
    push_cast
    ring
  simp only [spectralLine,Function.comp_apply,euclideanSplit_apply,line,trial,norm_mul,he]
  rw [clockFactor_norm,gaussian_split,tail_add,norm_mul]
  have hr : ((x+v) 0:ℂ) = ((x 0+v 0:ℝ):ℂ)+((0:ℝ):ℂ)*Complex.I := by simp
  rw [hr,clockFactor_norm]
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero]
  have hexp : Real.exp (-Real.pi*((x 0+v 0)^2-y^2)) =
      Real.exp (Real.pi*y^2)*Real.exp (-Real.pi*(x 0+v 0)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

variable (F : ℂ → ℂ) (v : Space) (d M : ℝ)
  (hF : ∀ q : ℂ, |q.im| ≤ d → AnalyticAt ℂ F q)
  (hM : 0 ≤ M) (hB : ∀ q : ℂ, |q.im| ≤ d → ‖F q‖ ≤ M)

include hF in
theorem line_continuous (y : ℝ) (hy : |y| ≤ d) : Continuous (line F v y) := by
  have hc : Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (hF _ (by simpa using hy)).continuousAt.comp (by fun_prop)
  exact (hc.mul (show Continuous (fun w : ℝ × TailSpace =>
    clockFactor Real.pi ((w.1:ℂ)+(y:ℂ)*Complex.I+(v 0:ℂ))) by unfold clockFactor; fun_prop)).mul
      (gaussian_continuous.comp (by fun_prop))

include hF in
theorem spectralLine_continuous (y : ℝ) (hy : |y| ≤ d) : Continuous (spectralLine F v y) := by
  exact (line_continuous F v d hF y hy).comp
    ((by fun_prop : Continuous (fun x : Space => x 0)).prodMk tail_continuous)

include hB in
theorem spectralLine_bound (y : ℝ) (hy : |y| ≤ d) (x : Space) :
    ‖spectralLine F v y x‖ ≤ (M*Real.exp (Real.pi*y^2))*‖gaussian (x+v)‖ := by
  rw [spectralLine_norm]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hB _ (by simpa using hy)) (Real.exp_pos _).le) (norm_nonneg _)

include hF hB in
theorem spectralLine_integrable (y : ℝ) (hy : |y| ≤ d) : Integrable (spectralLine F v y) := by
  have hi : Integrable (fun x : Space => gaussian (x+v)) :=
    (measurePreserving_add_right volume v).integrable_comp_of_integrable gaussian_integrable
  apply (hi.norm.const_mul (M*Real.exp (Real.pi*y^2))).mono'
    (spectralLine_continuous F v d hF y hy).aestronglyMeasurable
  exact Filter.Eventually.of_forall (spectralLine_bound F v d M hB y hy)

include hF hM hB in
theorem spectralLine_memLp (y : ℝ) (hy : |y| ≤ d) : MemLp (spectralLine F v y) 2 := by
  have hi : MemLp (fun x : Space => gaussian (x+v)) 2 :=
    gaussian_memLp.comp_measurePreserving (measurePreserving_add_right volume v)
  apply (hi.const_mul (M*Real.exp (Real.pi*y^2):ℂ)).of_le
    (spectralLine_continuous F v d hF y hy).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hM,abs_of_pos (Real.exp_pos _)] using spectralLine_bound F v d M hB y hy x

include hF hB in
theorem line_integrable (y : ℝ) (hy : |y| ≤ d) : Integrable (line F v y) := by
  have h := euclideanSplit_preserves_volume.symm.integrable_comp_of_integrable
    (spectralLine_integrable F v d M hF hB y hy)
  simpa only [spectralLine,Function.comp_def,MeasurableEquiv.apply_symm_apply] using h

include hM hB in
theorem clockSlice_bound (y q : ℝ) (hy : |y| ≤ d) (z : TailSpace) :
    ‖line F v y (q,z)‖ ≤
      (M*‖gaussian (z+tail v)‖*Real.exp (Real.pi*(d^2+(v 0)^2)))*Real.exp (-(Real.pi/2)*q^2) := by
  have he : (q:ℂ)+(y:ℂ)*Complex.I+(v 0:ℂ) = ((q+v 0:ℝ):ℂ)+(y:ℂ)*Complex.I := by
    push_cast
    ring
  have hy2 : y^2 ≤ d^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) (le_trans (abs_nonneg y) hy)).mpr hy
  have hq : q^2/2-(v 0)^2 ≤ (q+v 0)^2 := by nlinarith [sq_nonneg (q+2*v 0)]
  have hb : Real.exp (-Real.pi*((q+v 0)^2-y^2)) ≤
      Real.exp (Real.pi*(d^2+(v 0)^2))*Real.exp (-(Real.pi/2)*q^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  simp only [line,trial,norm_mul,he,clockFactor_norm]
  calc
    _ ≤ M*(Real.exp (Real.pi*(d^2+(v 0)^2))*Real.exp (-(Real.pi/2)*q^2))*‖gaussian (z+tail v)‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hB _ (by simpa using hy)) hb (Real.exp_pos _).le hM) (norm_nonneg _)
    _ = _ := by ring

include hF hM hB in
theorem clock_fourier_shift (y : ℝ) (hy : |y| ≤ d) (z : TailSpace) (k : ℝ) :
    (𝓕 (fun q : ℝ => line F v 0 (q,z))) k =
      (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (fun q : ℝ => line F v y (q,z))) k := by
  apply fourier_shift_strip (fun q => trial F v q z) (Real.pi/2)
    (M*‖gaussian (z+tail v)‖*Real.exp (Real.pi*(d^2+(v 0)^2))) y _ (by positivity) _ k
  · intro q hq
    have hg : AnalyticAt ℂ (fun q => clockFactor Real.pi (q+(v 0:ℂ))) q := by
      unfold clockFactor
      fun_prop
    exact (((hF q (hq.trans hy)).mul hg).mul analyticAt_const).differentiableAt
  · intro q r hr
    exact clockSlice_bound F v d M hM hB r q (hr.trans hy) z

#print axioms norm_square_split
#print axioms gaussian_split
#print axioms spectralLine_one_zero
#print axioms spectralLine_norm
#print axioms line_continuous
#print axioms spectralLine_continuous
#print axioms spectralLine_bound
#print axioms spectralLine_integrable
#print axioms spectralLine_memLp
#print axioms line_integrable
#print axioms clockSlice_bound
#print axioms clock_fourier_shift

end
end UnifiedTheory.Audit.KFCausalGaussianStrip
