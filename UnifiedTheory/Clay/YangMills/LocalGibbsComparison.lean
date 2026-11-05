/- Local reweighting comparison: an arbitrary external Gibbs weight cancels
from the estimate. Only the local weight ratio enters, so this lemma does not
replace a local estimate by a volume-dependent global action bound. -/
import UnifiedTheory.Clay.YangMills.GibbsFullSupport
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalGibbsComparison
noncomputable section
open MeasureTheory
open scoped ENNReal

section Weight
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def weightedLaw (w : X → ℝ) : Measure X :=
  (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (w x))

theorem weightedLaw_probability (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable w μ) (hn : ∀ x, 0 ≤ w x) (hz : 0 < ∫ x, w x ∂μ) :
    IsProbabilityMeasure (weightedLaw μ w) := by
  constructor
  unfold weightedLaw
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hz).ne' ENNReal.ofReal_ne_top

theorem weighted_integral (w : X → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    (hz : 0 < ∫ x, w x ∂μ) (f : X → ℝ) :
    ∫ x, f x ∂weightedLaw μ w = (∫ x, w x * f x ∂μ) / (∫ x, w x ∂μ) := by
  unfold weightedLaw
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hz.le, smul_eq_mul,
    ENNReal.toReal_ofReal (hn _)]
  rw [div_eq_mul_inv, mul_comm]
end Weight

section Local
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def localWeight (a : Y → ℝ) (b : Y × X → ℝ) (z : Y × X) : ℝ := a z.1 * b z

theorem local_partition_bounds (a : Y → ℝ) (ha : Continuous a) (han : ∀ y, 0 ≤ a y)
    (b : Y × X → ℝ) (hb : Continuous b) (l u : ℝ)
    (hl : ∀ z, l ≤ b z) (hu : ∀ z, b z ≤ u) :
    l * (∫ y, a y ∂ν) ≤ ∫ z, localWeight a b z ∂ν.prod μ ∧
    (∫ z, localWeight a b z ∂ν.prod μ) ≤ u * (∫ y, a y ∂ν) := by
  have hi : Integrable (localWeight a b) (ν.prod μ) :=
    ((ha.comp continuous_fst).mul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconst (c : ℝ) : Integrable (fun z : Y × X => c * a z.1) (ν.prod μ) :=
    (continuous_const.mul (ha.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (c : ℝ) : (∫ z : Y × X, c * a z.1 ∂ν.prod μ) = c * ∫ y, a y ∂ν := by
    rw [integral_const_mul, integral_fun_fst]
    simp
  constructor
  · rw [← he l]
    apply integral_mono (hconst l) hi
    intro z
    simpa only [localWeight, mul_comm] using mul_le_mul_of_nonneg_left (hl z) (han z.1)
  · rw [← he u]
    apply integral_mono hi (hconst u)
    intro z
    simpa only [localWeight, mul_comm] using mul_le_mul_of_nonneg_left (hu z) (han z.1)

theorem local_numerator_lower (a : Y → ℝ) (ha : Continuous a) (han : ∀ y, 0 ≤ a y)
    (b : Y × X → ℝ) (hb : Continuous b) (l : ℝ) (hl : 0 ≤ l) (hbl : ∀ z, l ≤ b z)
    (q : Y × X → ℝ) (hq : Continuous q) (hqn : ∀ z, 0 ≤ q z)
    (v : ℝ) (hv : ∀ y, v ≤ ∫ x, q (y, x) ∂μ) :
    l * v * (∫ y, a y ∂ν) ≤ ∫ z, localWeight a b z * q z ∂ν.prod μ := by
  have hleft : Continuous (fun z : Y × X => l * a z.1 * q z) :=
    (continuous_const.mul (ha.comp continuous_fst)).mul hq
  have hright : Continuous (fun z : Y × X => localWeight a b z * q z) :=
    ((ha.comp continuous_fst).mul hb).mul hq
  have hcomp : (∫ z : Y × X, l * a z.1 * q z ∂ν.prod μ) ≤
      ∫ z, localWeight a b z * q z ∂ν.prod μ := by
    apply integral_mono (hleft.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hright.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro z
    exact mul_le_mul_of_nonneg_right
      (by simpa only [localWeight, mul_comm] using mul_le_mul_of_nonneg_left (hbl z) (han z.1)) (hqn z)
  apply le_trans _ hcomp
  rw [integral_prod _ (hleft.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_const_mul]
  have hi : Integrable (fun y => l * a y * ∫ x, q (y, x) ∂μ) ν := by
    simpa only [integral_const_mul] using
      (hleft.integrable_of_hasCompactSupport (μ := ν.prod μ) (HasCompactSupport.of_compactSpace _)).integral_prod_left
  have hic : Integrable (fun y => l * a y * v) ν :=
    ((continuous_const.mul ha).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    l * v * (∫ y, a y ∂ν) = ∫ y, l * a y * v ∂ν := by
      rw [integral_mul_const, integral_const_mul]
      ring
    _ ≤ ∫ y, l * a y * (∫ x, q (y, x) ∂μ) ∂ν :=
      integral_mono hic hi (fun y => mul_le_mul_of_nonneg_left (hv y) (mul_nonneg hl (han y)))

theorem local_expectation_lower (a : Y → ℝ) (ha : Continuous a) (han : ∀ y, 0 ≤ a y)
    (haint : 0 < ∫ y, a y ∂ν) (b : Y × X → ℝ) (hb : Continuous b)
    (l u : ℝ) (hl : 0 < l) (hu : 0 < u) (hbl : ∀ z, l ≤ b z) (hbu : ∀ z, b z ≤ u)
    (q : Y × X → ℝ) (hq : Continuous q) (hqn : ∀ z, 0 ≤ q z)
    (v : ℝ) (hvn : 0 ≤ v) (hv : ∀ y, v ≤ ∫ x, q (y, x) ∂μ) :
    (l / u) * v ≤ ∫ z, q z ∂weightedLaw (ν.prod μ) (localWeight a b) := by
  have hp := local_partition_bounds μ ν a ha han b hb l u hbl hbu
  have hz : 0 < ∫ z, localWeight a b z ∂ν.prod μ := (mul_pos hl haint).trans_le hp.1
  rw [weighted_integral (ν.prod μ) (localWeight a b)
    (show Measurable (localWeight a b) from ((ha.comp continuous_fst).mul hb).measurable)
    (fun z => mul_nonneg (han z.1) (hl.le.trans (hbl z))) hz q]
  apply (le_div_iff₀ hz).mpr
  calc
    (l / u * v) * (∫ z, localWeight a b z ∂ν.prod μ) ≤
        (l / u * v) * (u * ∫ y, a y ∂ν) :=
      mul_le_mul_of_nonneg_left hp.2 (mul_nonneg (div_nonneg hl.le hu.le) hvn)
    _ = l * v * ∫ y, a y ∂ν := by field_simp
    _ ≤ ∫ z, localWeight a b z * q z ∂ν.prod μ :=
      local_numerator_lower μ ν a ha han b hb l hl.le hbl q hq hqn v hv

theorem local_variance_lower (a : Y → ℝ) (ha : Continuous a) (han : ∀ y, 0 ≤ a y)
    (haint : 0 < ∫ y, a y ∂ν) (b : Y × X → ℝ) (hb : Continuous b)
    (l u : ℝ) (hl : 0 < l) (hu : 0 < u) (hbl : ∀ z, l ≤ b z) (hbu : ∀ z, b z ≤ u)
    (F : Y × X → ℂ) (hF : Continuous F) (v : ℝ) (hvn : 0 ≤ v)
    (hv : ∀ y m, v ≤ ∫ x, ‖F (y, x) - m‖ ^ 2 ∂μ) :
    (l / u) * v ≤ ∫ z, ‖F z - ∫ t, F t ∂weightedLaw (ν.prod μ) (localWeight a b)‖ ^ 2
      ∂weightedLaw (ν.prod μ) (localWeight a b) :=
  local_expectation_lower μ ν a ha han haint b hb l u hl hu hbl hbu _
    ((hF.sub continuous_const).norm.pow 2) (fun z => sq_nonneg _) v hvn (fun y => hv y _)
end Local

end
end UnifiedTheory.Clay.YangMills.LocalGibbsComparison
