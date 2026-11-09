/- Strong imaginary-shear derivatives with an unbounded polynomial field
factor. The L2 domination is derived from the Gaussian envelope. Both
physical powers and their field derivatives instantiate the multiplier. -/
import UnifiedTheory.Audit.KFCausalFieldInterpolationBounds
import UnifiedTheory.Audit.KFCausalStrongImaginaryShearCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalShearRadius (radius)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential
open UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalIntervalL2Derivative (curve curve_coe clip clip_eq)
open UnifiedTheory.Audit.KFCausalFieldInterpolationBounds

structure Weight where
  value : Configuration → ℂ
  smooth : ContDiff ℝ 1 value
  bound : ℝ
  nonnegative : 0 ≤ bound
  estimate : ∀ x, ‖value x‖ ≤ bound*radius x.2

def fieldWeight (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : Weight where
  value := KFCausalFieldShearDifferential.powerValue l i
  smooth := KFCausalFieldShearDifferential.powerValue_smooth l i
  bound := valueConstant l
  nonnegative := (constants_nonnegative l).1
  estimate := value_bound l i

def slopeWeight (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : Weight where
  value := KFCausalFieldShearDifferential.powerSlope l i
  smooth := KFCausalFieldShearDifferential.powerSlope_smooth l i
  bound := KFCausalFieldInterpolationBounds.slopeConstant l
  nonnegative := (constants_nonnegative l).2
  estimate := KFCausalFieldInterpolationBounds.slope_bound l i

variable (P : Weight) (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
  (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
  (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
local notation "G" => path A D α β b
local notation "F" => fun t => first (timeAmplitude A D t) (timeScale D t) α β b
local notation "S" => fun t => second (timeAmplitude A D t) (timeScale D t) α β b

include hAm hα hβ in
theorem envelope0_memLp : MemLp (fun x => P.value x*envelope A α β b x) 2 volume := by
  simpa only [pow_zero,Complex.ofReal_one,mul_one] using
    weighted_envelope_memLp P.value P.smooth.continuous P.bound P.nonnegative P.estimate A hAm α β hα hβ b 0

include hAm hα hβ in
theorem envelope1_memLp : MemLp (fun x => P.value x*firstEnvelope A α β b x) 2 volume := by
  have hm := (weighted_envelope_memLp P.value P.smooth.continuous P.bound P.nonnegative P.estimate
    A hAm α β hα hβ b 1).const_mul
    ((KFCausalGaussianShearSlopeBounds.slopeConstant scaleBound α β b+1:ℝ):ℂ)
  convert hm using 1
  funext x
  simp only [firstEnvelope,pow_one]
  ring

include hAm hα hβ in
theorem envelope2_memLp : MemLp (fun x => P.value x*secondEnvelope A α β b x) 2 volume := by
  have hm := (weighted_envelope_memLp P.value P.smooth.continuous P.bound P.nonnegative P.estimate
    A hAm α β hα hβ b 2).const_mul
    ((curvatureConstant scaleBound α β b+(KFCausalGaussianShearSlopeBounds.slopeConstant scaleBound α β b+1)^2:ℝ):ℂ)
  convert hm using 1
  funext x
  unfold secondEnvelope
  ring

include hA hAm hD hDb hα hβ hw in
theorem input_memLp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    MemLp (fun x => P.value x*G t x) 2 volume := by
  apply (envelope0_memLp P A hAm α β hα hβ b).of_le
    (P.smooth.continuous.mul (path_smooth A D hA hD α β b t).continuous).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_left
    (path_bound A D hDb α β hα hβ hw b t ht x) (norm_nonneg (P.value x))

include hA hAm hD hDb hα hβ hw in
theorem first_memLp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    MemLp (fun x => P.value x*F t x) 2 volume := by
  apply (envelope1_memLp P A hAm α β hα hβ b).of_le
    (P.smooth.continuous.mul (first_smooth _ _ (timeAmplitude_smooth A D hA hD t)
      (timeScale_smooth D hD t) α β b).continuous).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_left
    (first_path_bound A D hDb α β hα hβ hw b t ht x) (norm_nonneg (P.value x))

include hA hAm hD hDb hα hβ hw in
theorem second_memLp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    MemLp (fun x => P.value x*S t x) 2 volume := by
  apply (envelope2_memLp P A hAm α β hα hβ b).of_le
    (P.smooth.continuous.mul (second_continuous _ _ (timeAmplitude_smooth A D hA hD t)
      (timeScale_smooth D hD t) α β b)).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_left
    (second_path_bound A D hDb α β hα hβ hw b t ht x) (norm_nonneg (P.value x))

def input : ℝ → Hilbert := curve (fun t x => P.value x*G t x)
  (input_memLp P A D hA hAm hD hDb α β hα hβ hw b)
def firstState : ℝ → Hilbert := curve (fun t x => P.value x*F t x)
  (first_memLp P A D hA hAm hD hDb α β hα hβ hw b)
def secondState (t : Interval) : Hilbert :=
  (second_memLp P A D hA hAm hD hDb α β hα hβ hw b t t.property).toLp _

theorem input_coe (t : Interval) : input P A D hA hAm hD hDb α β hα hβ hw b t =ᵐ[volume]
    fun x => P.value x*G t x := by
  simpa only [clip_eq t t.property] using curve_coe _
    (input_memLp P A D hA hAm hD hDb α β hα hβ hw b) t

theorem first_coe (t : Interval) : firstState P A D hA hAm hD hDb α β hα hβ hw b t =ᵐ[volume]
    fun x => P.value x*F t x := by
  simpa only [clip_eq t t.property] using curve_coe _
    (first_memLp P A D hA hAm hD hDb α β hα hβ hw b) t

theorem second_coe (t : Interval) : secondState P A D hA hAm hD hDb α β hα hβ hw b t =ᵐ[volume]
    fun x => P.value x*S t x :=
  (second_memLp P A D hA hAm hD hDb α β hα hβ hw b t t.property).coeFn_toLp

theorem input_continuous : Continuous (input P A D hA hAm hD hDb α β hα hβ hw b) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun t : ℝ => fun x => P.value x*G (clip t) x)
    (fun t => input_memLp P A D hA hAm hD hDb α β hα hβ hw b (clip t) (clip t).property)
    (fun x => P.value x*envelope A α β b x) (envelope0_memLp P A hAm α β hα hβ b)
  · intro t
    filter_upwards [] with x
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left
      (path_bound A D hDb α β hα hβ hw b (clip t) (clip t).property x) (norm_nonneg (P.value x))
  · filter_upwards [] with x
    have hc : Continuous (fun t : ℝ => G t x) :=
      (show Differentiable ℝ (fun t : ℝ => G t x) from
        fun t => (path_time_derivative A D α β b t x).differentiableAt).continuous
    exact continuous_const.mul (hc.comp (continuous_subtype_val.comp (continuous_projIcc (h := zero_le_one))))

theorem first_continuous : Continuous (firstState P A D hA hAm hD hDb α β hα hβ hw b) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun t : ℝ => fun x => P.value x*F (clip t) x)
    (fun t => first_memLp P A D hA hAm hD hDb α β hα hβ hw b (clip t) (clip t).property)
    (fun x => P.value x*firstEnvelope A α β b x) (envelope1_memLp P A hAm α β hα hβ b)
  · intro t
    filter_upwards [] with x
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left
      (first_path_bound A D hDb α β hα hβ hw b (clip t) (clip t).property x) (norm_nonneg (P.value x))
  · filter_upwards [] with x
    have hc : Continuous (fun t : ℝ => F t x) :=
      (show Differentiable ℝ (fun t : ℝ => F t x) from
        fun t => (first_time_derivative A D α β b t x).differentiableAt).continuous
    exact continuous_const.mul (hc.comp (continuous_subtype_val.comp (continuous_projIcc (h := zero_le_one))))

include hA hAm hD hDb hα hβ hw in
theorem inputDerivative_memLp (t : Interval) :
    MemLp (fun x => D x.1*(P.value x*F t x)) 2 volume :=
  KFCausalShearPolynomialMoments.clock_mul_memLp D hD.continuous (Real.pi/3)
    (by positivity) hDb _ (first_memLp P A D hA hAm hD hDb α β hα hβ hw b t t.property)

include hA hAm hD hDb hα hβ hw in
theorem firstDerivative_memLp (t : Interval) :
    MemLp (fun x => D x.1*(P.value x*S t x)) 2 volume :=
  KFCausalShearPolynomialMoments.clock_mul_memLp D hD.continuous (Real.pi/3)
    (by positivity) hDb _ (second_memLp P A D hA hAm hD hDb α β hα hβ hw b t t.property)

def inputDerivative (t : Interval) : Hilbert :=
  (inputDerivative_memLp P A D hA hAm hD hDb α β hα hβ hw b t).toLp _
def firstDerivative (t : Interval) : Hilbert :=
  (firstDerivative_memLp P A D hA hAm hD hDb α β hα hβ hw b t).toLp _

theorem input_strong_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (input P A D hA hAm hD hDb α β hα hβ hw b)
      (inputDerivative P A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩) t := by
  apply KFCausalIntervalL2Derivative.strong_derivative
    (fun t x => P.value x*G t x) (fun t x => D x.1*(P.value x*F t x))
    (input_memLp P A D hA hAm hD hDb α β hα hβ hw b)
    (fun x => (Real.pi/3:ℝ)*(P.value x*firstEnvelope A α β b x))
    ((envelope1_memLp P A hAm α β hα hβ b).const_mul (Real.pi/3:ℝ))
    _ _ t ht (inputDerivative_memLp P A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩)
  · intro t _ x
    convert (path_time_derivative A D α β b t x).const_mul (P.value x) using 1
    unfold first path
    ring
  · intro t ht x
    have hp := mul_le_mul_of_nonneg_left (first_path_bound A D hDb α β hα hβ hw b t ht x)
      (norm_nonneg (P.value x))
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi/3)] using
      mul_le_mul (hDb x.1) hp (by positivity) (by positivity : 0 ≤ Real.pi/3)

theorem first_strong_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (firstState P A D hA hAm hD hDb α β hα hβ hw b)
      (firstDerivative P A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩) t := by
  apply KFCausalIntervalL2Derivative.strong_derivative
    (fun t x => P.value x*F t x) (fun t x => D x.1*(P.value x*S t x))
    (first_memLp P A D hA hAm hD hDb α β hα hβ hw b)
    (fun x => (Real.pi/3:ℝ)*(P.value x*secondEnvelope A α β b x))
    ((envelope2_memLp P A hAm α β hα hβ b).const_mul (Real.pi/3:ℝ))
    _ _ t ht (firstDerivative_memLp P A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩)
  · intro t _ x
    convert (first_time_derivative A D α β b t x).const_mul (P.value x) using 1
    ring
  · intro t ht x
    have hp := mul_le_mul_of_nonneg_left (second_path_bound A D hDb α β hα hβ hw b t ht x)
      (norm_nonneg (P.value x))
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi/3)] using
      mul_le_mul (hDb x.1) hp (by positivity) (by positivity : 0 ≤ Real.pi/3)

#print axioms envelope0_memLp
#print axioms envelope1_memLp
#print axioms envelope2_memLp
#print axioms input_memLp
#print axioms first_memLp
#print axioms second_memLp
#print axioms input_coe
#print axioms first_coe
#print axioms second_coe
#print axioms input_continuous
#print axioms first_continuous
#print axioms inputDerivative_memLp
#print axioms firstDerivative_memLp
#print axioms input_strong_derivative
#print axioms first_strong_derivative
end
end UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve
