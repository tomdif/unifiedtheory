/- Uniform physical-coordinate bounds for the concrete imaginary-shear
path. Its clock factor and transverse Gaussian are controlled separately;
their product supplies L2 states and quadratic moments at every time in
the closed interpolation interval. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
import UnifiedTheory.Audit.KFCausalShiftedClockAmplitude
import UnifiedTheory.Audit.KFCausalUniformShearGaussian
import UnifiedTheory.Audit.KFCausalGaussianQuadraticMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (complexScale physicalGaussian)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceConstant coherentPacket)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (grouped)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile exponent)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalUniformShearGaussian (confinement confinement_positive)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (physicalGaussian_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)

def width (α β : ℝ) : ℝ := confinement α β (Real.pi/3)/2
def constant (α β : ℝ) (b : Fin 5 → ℂ) : ℝ :=
  Real.exp (Real.pi/3)*Real.exp (sourceConstant α β b/2)
def envelope (A : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  (constant α β b:ℂ)*(A x.1*physicalGaussian (width α β) (width α β) x.2)

theorem width_positive (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : 0 < width α β :=
  div_pos (confinement_positive α β _ hα hβ) (by norm_num)

theorem scaled_bound (z : ℂ) (hz : ‖z‖ ≤ Real.pi/3) (t : ℝ) (ht : |t| ≤ 1) :
    ‖(t:ℂ)*z‖ ≤ Real.pi/3 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right ht (norm_nonneg z)).trans (by simpa using hz)

theorem timeAmplitude_bound (A D : ℝ → ℂ) (hD : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
    ‖timeAmplitude A D t s‖ ≤ Real.exp (Real.pi/3)*‖A s‖ := by
  have ht' : |t-1| ≤ 1 := abs_le.mpr (by constructor <;> linarith [ht.1,ht.2])
  have hb := scaled_bound (D s) (hD s) (t-1) ht'
  rw [Complex.ofReal_sub,Complex.ofReal_one] at hb
  have he := Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)
  simpa only [timeAmplitude,norm_mul,Complex.norm_exp] using
    mul_le_mul_of_nonneg_right he (norm_nonneg (A s))

theorem transverse_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (z : ℂ) (hz : ‖z‖ ≤ Real.pi/3) (q : Transverse) :
    ‖Complex.exp (exponent α β b (complexScale z) q)‖ ≤
      Real.exp (sourceConstant α β b/2)*‖physicalGaussian (width α β) (width α β) q‖ := by
  have he := KFCausalShiftedGaussianPhysicalProfile.recentered_packet α β b z 0 q
  simp only [neg_zero,flow_initial,Complex.ofReal_zero,sub_zero] at he
  rw [← he]
  have hb := KFCausalUniformShearGaussian.coherent_isotropic_bound α β (Real.pi/3)
    hα hβ hw b z ((Complex.abs_re_le_norm z).trans hz) ((Complex.abs_im_le_norm z).trans hz) (grouped q)
  convert hb using 1
  rw [physicalGaussian,Complex.norm_exp]
  congr 2
  simp [Complex.neg_re,Complex.ofReal_re,width,KFCausalClockFloorShearBounds.squared,
    grouped,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re]
  ring

theorem path_bound (A D : ℝ → ℂ) (hD : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Configuration) :
    ‖path A D α β b t x‖ ≤ ‖envelope A α β b x‖ := by
  have hz := scaled_bound (D x.1) (hD x.1) t (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hq := transverse_bound α β hα hβ hw b ((t:ℂ)*D x.1) hz x.2
  have hp := mul_le_mul (timeAmplitude_bound A D hD t ht x.1) hq
    (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg (A x.1)))
  simpa only [path,profile,timeScale,complexScale,envelope,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,constant,abs_mul,abs_of_pos (Real.exp_pos _),
    mul_assoc,mul_left_comm,mul_comm] using hp

theorem envelope_memLp (A : ℝ → ℂ) (hA : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) : MemLp (envelope A α β b) 2 volume :=
  (configuration_product_memLp A _ hA
    (physicalGaussian_memLp _ _ (width_positive α β hα hβ) (width_positive α β hα hβ))).const_mul _

theorem envelope_quadratic_memLp (A : ℝ → ℂ) (hA : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) (i : Fin 5) :
    MemLp (fun x : Configuration => (x.2 i:ℂ)^2*envelope A α β b x) 2 volume := by
  convert (configuration_product_memLp A _ hA
    (KFCausalGaussianQuadraticMoments.gaussian_quadratic_memLp _ _
      (width_positive α β hα hβ) (width_positive α β hα hβ) i)).const_mul (constant α β b:ℂ) using 1
  funext x
  unfold envelope
  ring

theorem path_memLp (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : MemLp (path A D α β b t) 2 volume :=
  (envelope_memLp A hAm α β hα hβ b).of_le
    (path_smooth A D hA hD α β b t).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (path_bound A D hDb α β hα hβ hw b t ht))

theorem path_quadratic_memLp (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (i : Fin 5) :
    MemLp (fun x : Configuration => (x.2 i:ℂ)^2*path A D α β b t x) 2 volume := by
  have hc : Continuous (fun x : Configuration => (x.2 i:ℂ)^2*path A D α β b t x) :=
    ((Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).pow 2).mul
      (path_smooth A D hA hD α β b t).continuous
  apply (envelope_quadratic_memLp A hAm α β hα hβ b i).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_mul] using mul_le_mul_of_nonneg_left
    (path_bound A D hDb α β hα hβ hw b t ht x) (norm_nonneg ((x.2 i:ℂ)^2))

#print axioms width_positive
#print axioms scaled_bound
#print axioms timeAmplitude_bound
#print axioms transverse_bound
#print axioms path_bound
#print axioms envelope_memLp
#print axioms envelope_quadratic_memLp
#print axioms path_memLp
#print axioms path_quadratic_memLp
end
end UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
