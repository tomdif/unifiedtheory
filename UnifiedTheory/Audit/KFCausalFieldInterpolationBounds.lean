/- Polynomial domination for both physical field powers and their shear
derivatives along the imaginary-shear path. All weighted envelopes are
integrable, with no extra moment assumption on the path. -/
import UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments
import UnifiedTheory.Audit.KFCausalFieldShearDifferential
import UnifiedTheory.Audit.KFCausalFieldWeightedShearMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldInterpolationBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalShearRadius
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerValue powerSlope fieldSlope)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds (envelope envelope_memLp)
open UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments (radius_envelope_memLp)

theorem weighted_envelope_memLp (P : Configuration → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖P x‖ ≤ M*radius x.2)
    (A : ℝ → ℂ) (hA : MemLp A 2 volume) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b : Fin 5 → ℂ) (n : ℕ) :
    MemLp (fun x => P x*((radius x.2)^n:ℝ)*envelope A α β b x) 2 volume := by
  have hc : Continuous (fun x : Configuration => (((radius x.2)^n:ℝ):ℂ)) := by
    unfold radius
    fun_prop
  apply ((radius_envelope_memLp A hA α β hα hβ b (n+1)).const_mul (M:ℂ)).of_le
    ((hP.aestronglyMeasurable.mul hc.aestronglyMeasurable).mul
      (envelope_memLp A hA α β hα hβ b).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hM,abs_of_pos (radius_positive x.2)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hb x) (pow_nonneg (radius_positive x.2).le n))
    (norm_nonneg (envelope A α β b x))
  convert hh using 1
  rw [pow_succ]
  ring

theorem linear_bound (l : Transverse →L[ℝ] ℝ) (q : Transverse) : |l q| ≤ ‖l‖*radius q := by
  have hn : ‖q‖ ≤ radius q := (pi_norm_le_iff_of_nonneg (radius_positive q).le).mpr
    (fun i => by rw [Real.norm_eq_abs]; exact coordinate_abs_le q i)
  simpa only [Real.norm_eq_abs] using (l.le_opNorm q).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg l))

theorem linear_product_bound (l m : Transverse →L[ℝ] ℝ) (q : Transverse) :
    |l q| *|m q| ≤ ‖l‖*‖m‖*radius q := by
  have hn : ‖q‖ ≤ Real.sqrt (radius q) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => by
      rw [Real.norm_eq_abs]
      exact (Real.le_sqrt (abs_nonneg _) (radius_positive q).le).mpr
        (by simpa only [sq_abs] using coordinate_square_le q i))
  have hs : ‖q‖^2 ≤ radius q := by
    have hp := pow_le_pow_left₀ (norm_nonneg q) hn 2
    rwa [Real.sq_sqrt (radius_positive q).le] at hp
  have hp := mul_le_mul (l.le_opNorm q) (m.le_opNorm q) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at hp
  have hq := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg l) (norm_nonneg m))
  nlinarith only [hp,hq]

def valueConstant (l : Transverse →L[ℝ] ℝ) : ℝ := ‖l‖+‖l‖^2
def slopeConstant (l : Transverse →L[ℝ] ℝ) : ℝ := ‖fieldSlope l‖+2*‖l‖*‖fieldSlope l‖

theorem constants_nonnegative (l : Transverse →L[ℝ] ℝ) :
    0 ≤ valueConstant l ∧ 0 ≤ slopeConstant l := by
  unfold valueConstant slopeConstant
  constructor <;> positivity

theorem value_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    ‖powerValue l i x‖ ≤ valueConstant l*radius x.2 := by
  fin_cases i
  · have h := linear_bound l x.2
    simp only [powerValue,Nat.zero_add,pow_one,Complex.norm_real,Real.norm_eq_abs]
    unfold valueConstant
    nlinarith only [h,mul_nonneg (sq_nonneg ‖l‖) (radius_positive x.2).le]
  · have h := KFCausalFieldWeightedShearMoments.field_square_bound l x.2
    change ‖(l x.2:ℂ)^2‖ ≤ _
    unfold valueConstant
    nlinarith only [h,mul_nonneg (norm_nonneg l) (radius_positive x.2).le]

theorem slope_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    ‖powerSlope l i x‖ ≤ slopeConstant l*radius x.2 := by
  fin_cases i
  · have h := linear_bound (fieldSlope l) x.2
    simp only [powerSlope,Nat.zero_add,Nat.cast_one,pow_zero,one_mul,
      Complex.norm_real,Real.norm_eq_abs]
    unfold slopeConstant
    nlinarith only [h,mul_nonneg (mul_nonneg (norm_nonneg l) (norm_nonneg (fieldSlope l))) (radius_positive x.2).le]
  · have h := linear_product_bound l (fieldSlope l) x.2
    norm_num only [powerSlope,pow_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    unfold slopeConstant
    nlinarith only [h,mul_nonneg (norm_nonneg (fieldSlope l)) (radius_positive x.2).le]

#print axioms weighted_envelope_memLp
#print axioms linear_bound
#print axioms linear_product_bound
#print axioms constants_nonnegative
#print axioms value_bound
#print axioms slope_bound
end
end UnifiedTheory.Audit.KFCausalFieldInterpolationBounds
