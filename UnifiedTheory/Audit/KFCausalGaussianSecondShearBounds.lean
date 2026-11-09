/- Uniform first- and second-shear Gaussian majorants. Fourth coordinate
moments of the previously proved envelope provide the full L2 control
needed for second-shear graphs and for strong interpolation derivatives. -/
import UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile direction)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential
open UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds
open UnifiedTheory.Audit.KFCausalShearRadius
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalGaussianFourthMoments

def curvatureConstant (M α β : ℝ) (b : Fin 5 → ℂ) : ℝ :=
  slopeConstant M α β b/2+2*∑ i, |widths α β i| *(4*M^2)

theorem curvatureConstant_nonnegative (M α β : ℝ) (hM : 0 ≤ M) (b : Fin 5 → ℂ) :
    0 ≤ curvatureConstant M α β b := by
  have hs := slopeConstant_nonnegative M α β hM b
  unfold curvatureConstant
  positivity

theorem curvature_bound (r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ∀ s, ‖r s‖ ≤ M)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    ‖curvature r α β b x‖ ≤ curvatureConstant M α β b*radius x.2 := by
  have hq : ‖∑ i, (widths α β i:ℂ)*(direction (r x.1) x.2 i)^2‖ ≤
      (∑ i, |widths α β i| *(4*M^2))*radius x.2 := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left (direction_square_bound _ M hM (hr x.1) x.2 i)
      (abs_nonneg (widths α β i))
    nlinarith
  have hs := slope_bound r M hM hr α β b x
  unfold curvature
  apply (norm_sub_le _ _).trans
  simp only [norm_div,norm_mul,Complex.norm_ofNat]
  unfold curvatureConstant
  nlinarith

theorem first_bound (A r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ∀ s, ‖r s‖ ≤ M)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    ‖first A r α β b x‖ ≤ (slopeConstant M α β b+1)*radius x.2*‖profile A r α β b x‖ := by
  have hs := slope_bound r M hM hr α β b x
  have hn := norm_add_le (KFCausalRelativeGaussianDifferential.slope r α β b x) 1
  rw [norm_one] at hn
  have hb : ‖KFCausalRelativeGaussianDifferential.slope r α β b x+1‖ ≤
      (slopeConstant M α β b+1)*radius x.2 := by nlinarith [radius_one_le x.2]
  simpa only [first,norm_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (profile A r α β b x))

theorem second_bound (A r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ∀ s, ‖r s‖ ≤ M)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    ‖second A r α β b x‖ ≤ (curvatureConstant M α β b+(slopeConstant M α β b+1)^2)*
      (radius x.2)^2*‖profile A r α β b x‖ := by
  have hs := slope_bound r M hM hr α β b x
  have hn := norm_add_le (KFCausalRelativeGaussianDifferential.slope r α β b x) 1
  rw [norm_one] at hn
  have hb : ‖KFCausalRelativeGaussianDifferential.slope r α β b x+1‖ ≤
      (slopeConstant M α β b+1)*radius x.2 := by nlinarith [radius_one_le x.2]
  have hp := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hc := curvature_bound r M hM hr α β b x
  have hR : radius x.2 ≤ (radius x.2)^2 := by nlinarith [radius_one_le x.2]
  have hcc := mul_le_mul_of_nonneg_left hR (curvatureConstant_nonnegative M α β hM b)
  have hsum := norm_add_le (curvature r α β b x)
    ((KFCausalRelativeGaussianDifferential.slope r α β b x+1)^2)
  rw [norm_pow] at hsum
  have htotal : ‖curvature r α β b x+(KFCausalRelativeGaussianDifferential.slope r α β b x+1)^2‖ ≤
      (curvatureConstant M α β b+(slopeConstant M α β b+1)^2)*(radius x.2)^2 := by nlinarith
  simpa only [second,norm_mul] using mul_le_mul_of_nonneg_right htotal (norm_nonneg (profile A r α β b x))

def scaleBound : ℝ := Real.exp ((Real.pi/3)/2)
def firstEnvelope (A : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  (slopeConstant scaleBound α β b+1:ℝ)*((radius x.2:ℂ)*envelope A α β b x)
def secondEnvelope (A : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  (curvatureConstant scaleBound α β b+(slopeConstant scaleBound α β b+1)^2:ℝ)*
    (((radius x.2)^2:ℝ)*envelope A α β b x)

theorem firstEnvelope_memLp (A : ℝ → ℂ) (hAm : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) : MemLp (firstEnvelope A α β b) 2 volume :=
  (radius_memLp _ (envelope_memLp A hAm α β hα hβ b)
    (envelope_quadratic_memLp A hAm α β hα hβ b)).const_mul _

theorem secondEnvelope_memLp (A : ℝ → ℂ) (hAm : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) : MemLp (secondEnvelope A α β b) 2 volume :=
  (radius_square_memLp _ (envelope_memLp A hAm α β hα hβ b)
    (envelope_fourth_memLp A hAm α β hα hβ b)).const_mul _

theorem first_path_bound (A D : ℝ → ℂ) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (x : Configuration) :
    ‖first (timeAmplitude A D t) (timeScale D t) α β b x‖ ≤ ‖firstEnvelope A α β b x‖ := by
  have hs := first_bound (timeAmplitude A D t) (timeScale D t) scaleBound (Real.exp_pos _).le
    (KFCausalImaginaryShearPathDomain.timeScale_bound D hDb ⟨t,ht⟩) α β b x
  have hc := slopeConstant_nonnegative scaleBound α β (Real.exp_pos _).le b
  have hp := mul_le_mul_of_nonneg_left (path_bound A D hDb α β hα hβ hw b t ht x)
    (mul_nonneg (by linarith : 0 ≤ slopeConstant scaleBound α β b+1) (radius_positive x.2).le)
  apply hs.trans
  simpa only [path,firstEnvelope,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ slopeConstant scaleBound α β b+1),
    abs_of_nonneg (radius_positive x.2).le,mul_assoc] using hp

theorem second_path_bound (A D : ℝ → ℂ) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (x : Configuration) :
    ‖second (timeAmplitude A D t) (timeScale D t) α β b x‖ ≤ ‖secondEnvelope A α β b x‖ := by
  have hs := second_bound (timeAmplitude A D t) (timeScale D t) scaleBound (Real.exp_pos _).le
    (KFCausalImaginaryShearPathDomain.timeScale_bound D hDb ⟨t,ht⟩) α β b x
  have hc := curvatureConstant_nonnegative scaleBound α β (Real.exp_pos _).le b
  have hC : 0 ≤ curvatureConstant scaleBound α β b+(slopeConstant scaleBound α β b+1)^2 := by positivity
  have hp := mul_le_mul_of_nonneg_left (path_bound A D hDb α β hα hβ hw b t ht x)
    (mul_nonneg hC (sq_nonneg (radius x.2)))
  apply hs.trans
  simpa only [path,secondEnvelope,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hC,abs_of_nonneg (sq_nonneg (radius x.2)),mul_assoc] using hp

theorem second_continuous (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) : Continuous (second A r α β b) := by
  have hs := first_smooth A r hA hr α β b
  have hv : Continuous (fun x : Configuration => ((0,KFCausalTransverseDilationFlow.velocity x.2):Configuration)) := by
    apply continuous_const.prodMk
    apply continuous_pi
    intro i
    unfold KFCausalTransverseDilationFlow.velocity
    split_ifs <;> fun_prop
  have hc := ((hs.continuous_fderiv (by norm_num)).clm_apply hv).add hs.continuous
  change Continuous (KFCausalClockFloorCanonicalReconstruction.shearDerivative (first A r α β b)) at hc
  rwa [first_shear A r hA hr α β b] at hc

theorem first_path_memLp (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    MemLp (first (timeAmplitude A D t) (timeScale D t) α β b) 2 volume :=
  (firstEnvelope_memLp A hAm α β hα hβ b).of_le
    (first_smooth _ _ (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) α β b).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (first_path_bound A D hDb α β hα hβ hw b t ht))

theorem second_path_memLp (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    MemLp (second (timeAmplitude A D t) (timeScale D t) α β b) 2 volume :=
  (secondEnvelope_memLp A hAm α β hα hβ b).of_le
    (second_continuous _ _ (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) α β b).aestronglyMeasurable
    (Filter.Eventually.of_forall (second_path_bound A D hDb α β hα hβ hw b t ht))

#print axioms curvatureConstant_nonnegative
#print axioms curvature_bound
#print axioms first_bound
#print axioms second_bound
#print axioms firstEnvelope_memLp
#print axioms secondEnvelope_memLp
#print axioms first_path_bound
#print axioms second_path_bound
#print axioms second_continuous
#print axioms first_path_memLp
#print axioms second_path_memLp
end
end UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
