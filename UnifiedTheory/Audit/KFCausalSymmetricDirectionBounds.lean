/- Uniform coordinate and angle bounds for the actual constant symmetric
Gaussian derivative directions and both source and half-field slopes. -/
import UnifiedTheory.Audit.KFCausalSymmetricInsertionAffine
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricDirectionBounds
noncomputable section
open KFCausalSymmetricNormalizedDirection (direction targetDirection)
open KFCausalSymmetricInsertionAffine (neutralSlope matterSlope)
open KFCausalPairedModeCoordinates (scale)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalPhysicalReciprocalNormalization (coupling coupling_bound)
open KFCausalComplexShearPerturbation (Space baseline_norm)
open KFCausalMatterInsertionCoordinate (halfScale)

def directionCap (α w : ℝ) (i : Fin 2) : ℝ := (20/17)*‖direction α w i‖
def neutralSlopeCap (α w : ℝ) (i : Fin 2) : ℝ := directionCap α w i/Real.sqrt (α/32)
def matterSlopeCap (ε h α w : ℝ) (i : Fin 2) : ℝ :=
  ‖direction α w i‖/Real.sqrt (α/32)+
    2*|scale| *(3*Real.exp (|h|/(4*ε))+2)*(‖direction α w i‖/Real.sqrt (α*w))

theorem caps_nonnegative (ε h α w : ℝ) (i : Fin 2) :
    0 ≤ directionCap α w i ∧ 0 ≤ neutralSlopeCap α w i ∧ 0 ≤ matterSlopeCap ε h α w i := by
  simp only [neutralSlopeCap,directionCap,matterSlopeCap]
  constructor
  · positivity
  constructor <;> positivity

theorem targetDirection_bound (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖targetDirection ε h α w θ i q‖ ≤ directionCap α w i := by
  have hd := KFCausalTwoShearClockQuotient.two_increment_bound ε h hε hh q hq
  have hz : ‖complexInverse ε (shift h q)-complexInverse ε q‖ ≤ 1/5 := by
    linarith [norm_nonneg (complexInverse ε q-complexInverse ε (q.re:ℂ))]
  exact baseline_norm (rotationIsometry θ) (coupling α w) (coupling_bound α w hα hw) _ hz _

theorem neutralSlope_bound (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖neutralSlope ε h α w θ i q‖ ≤ neutralSlopeCap α w i := by
  rw [neutralSlope,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    ((PiLp.norm_apply_le _ 4).trans (targetDirection_bound ε h α w θ i hε hh hα hw q hq))
    (Real.sqrt_nonneg _)

theorem matterSlope_bound (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖matterSlope ε h α w θ i q‖ ≤ matterSlopeCap ε h α w i := by
  have hβ : 0 ≤ Real.sqrt (α/32) := (Real.sqrt_pos.mpr (div_pos hα (by norm_num))).le
  have hσ : 0 ≤ Real.sqrt (α*w) := (Real.sqrt_pos.mpr (mul_pos hα (zero_lt_one.trans_le hw))).le
  have h0 : ‖direction α w i 4/(Real.sqrt (α/32):ℂ)‖ ≤ ‖direction α w i‖/Real.sqrt (α/32) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (PiLp.norm_apply_le _ 4) hβ
  have h1 : ‖(rotationIsometry θ (direction α w i)) 3/(Real.sqrt (α*w):ℂ)‖ ≤
      ‖direction α w i‖/Real.sqrt (α*w) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply div_le_div_of_nonneg_right _ hσ
    simpa only [LinearIsometryEquiv.norm_map] using PiLp.norm_apply_le (rotationIsometry θ (direction α w i)) 3
  have he : ‖3*halfScale ε h q-2‖ ≤ 3*Real.exp (|h|/(4*ε))+2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    norm_num only [Complex.norm_ofNat]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (KFCausalSourcedWidthMatterMultiplier.halfScale_bound ε h hε hh q hq) (by norm_num : (0:ℝ) ≤ 3)) le_rfl
  have hm : ‖2*(scale:ℂ)*(3*halfScale ε h q-2)‖ ≤
      2*|scale| *(3*Real.exp (|h|/(4*ε))+2) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    norm_num only [Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  unfold matterSlope matterSlopeCap
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add h0 (mul_le_mul hm h1 (norm_nonneg _) (by positivity))

#print axioms caps_nonnegative
#print axioms targetDirection_bound
#print axioms neutralSlope_bound
#print axioms matterSlope_bound
end
end UnifiedTheory.Audit.KFCausalSymmetricDirectionBounds
