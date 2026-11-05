/- The exact Haar mass of a quaternion chord Gaussian and a polynomial
inverse-mass bound. The scalar Haar formula is proved in the imported chain. -/
import UnifiedTheory.Clay.YangMills.SU2SemicircleSlice
import UnifiedTheory.Clay.YangMills.QuaternionSymmetricChange

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2GaussianMass
noncomputable section
open MeasureTheory WilsonSlabOperator SU2HaarTilt QuaternionSymmetricChange
open scoped Quaternion RealInnerProductSpace

def weight (s : ℝ) (q : Q) : ℝ := Real.exp (-s*‖(q : ℍ)-1‖^2)
def mass (s : ℝ) : ℝ := ∫ q, weight s q ∂haar

theorem weight_continuous (s : ℝ) : Continuous (weight s) := by
  unfold weight
  fun_prop

theorem mass_pos (s : ℝ) : 0 < mass s :=
  integral_exp_pos ((weight_continuous s).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

theorem mass_antitone : Antitone mass := by
  intro s t hst
  exact integral_mono
    ((weight_continuous t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((weight_continuous s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun q => Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖(q : ℍ)-1‖]))

theorem chord_square (q : Q) : ‖(q : ℍ)-1‖^2 = 2*(1-(q : ℍ).re) := by
  rw [norm_sub_sq_real, unit_norm, norm_one]
  simp only [Quaternion.inner_def, star_one, mul_one]
  ring

theorem mass_eq_axis (s : ℝ) : mass s = Real.exp (-2*s)*axisPartition (2*s) := by
  rw [mass, axisPartition, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  unfold weight axisWeight
  rw [chord_square, ← Real.exp_add]
  congr 1
  ring

/-- Its growth is exactly s*sqrt(s); no exponential coupling cost remains. -/
def cap (s : ℝ) : ℝ :=
  4*SU2ScalarTilt.partition 0*s*Real.sqrt s/Real.Gamma (3 / 2)

theorem cap_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ cap s := by
  unfold cap
  exact div_nonneg (by positivity [SU2ScalarTilt.partition_pos 0])
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).le

theorem mass_cap_identity (s : ℝ) (hs : 0 < s) :
    mass s*cap s = 2*SU2QuotientRemainder.denominator (2*s) := by
  rw [mass_eq_axis, SU2HaarScalarBridge.axisPartition_eq_scalar
    SU2SemicircleSlice.firstCoordinateFormula, SU2ScalarTilt.partition_transform (by positivity)]
  unfold SU2ScalarTilt.changeFactor cap SU2QuotientRemainder.denominator
    SqrtSourceRemainder.gammaAverage
  rw [show 2/(2*s) = 1/s by field_simp]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    show -2*s = -(2*s) by ring, Real.exp_neg]
  field_simp [(SU2ScalarTilt.partition_pos 0).ne', hs.ne',
    (Real.sqrt_pos.mpr hs).ne',
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).ne']
  ring

theorem mass_cap_lower (s : ℝ) (hs : 3 / 4 ≤ s) : 1 ≤ mass s*cap s := by
  rw [mass_cap_identity s (by linarith)]
  linarith [SU2QuotientRemainder.denominator_ge_half (κ := 2*s) (by linarith)]

end
end UnifiedTheory.Clay.YangMills.SU2GaussianMass
