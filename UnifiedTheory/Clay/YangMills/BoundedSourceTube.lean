/- A positive finite measure gives a zero-free complex source tube controlled
by the range of the actual source observable. This is a finite-cutoff result:
no ultraviolet-uniform range or renormalized logarithm is assumed or proved. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BoundedSourceTube
noncomputable section
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def partition (F : X → ℝ) (z : ℂ) : ℂ := ∫ x, Complex.exp (z * (F x : ℂ)) ∂μ

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem exponential_real_positive (H : X → ℂ)
    (hH : ∀ x, |(H x).im| < Real.pi / 2) (x : X) :
    0 < (Complex.exp (H x)).re := by
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hH x)))

theorem integral_exponential_real_positive (H : X → ℂ) (hcH : Continuous H)
    (hH : ∀ x, |(H x).im| < Real.pi / 2) :
    0 < (∫ x, Complex.exp (H x) ∂μ).re := by
  have hc := Complex.continuous_exp.comp hcH
  have hi : Integrable (fun x => Complex.exp (H x)) μ :=
    hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  change 0 < RCLike.re (∫ x, Complex.exp (H x) ∂μ)
  rw [← integral_re hi]
  change 0 < ∫ x, (Complex.exp (H x)).re ∂μ
  rw [integral_pos_iff_support_of_nonneg
    (fun x => (exponential_real_positive H hH x).le) hi.re]
  have hs : Function.support (fun x => (Complex.exp (H x)).re) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (exponential_real_positive H hH x).ne'
  simp [hs]

/-- The raw, uncentered generating function is zero-free in the tube given
by its pointwise range. Arbitrary real parts of the source are allowed. -/
theorem partition_ne_zero (F : X → ℝ) (hF : Continuous F) (B : ℝ)
    (hB : ∀ x, |F x| ≤ B) (z : ℂ) (hz : |z.im| * B < Real.pi / 2) :
    partition μ F z ≠ 0 := by
  have hp : 0 < (partition μ F z).re := by
    apply integral_exponential_real_positive μ _ (continuous_const.mul
      (Complex.continuous_ofReal.comp hF))
    intro x
    change |(z * (F x : ℂ)).im| < Real.pi / 2
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      abs_mul]
    exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)).trans_lt hz
  intro he
  rw [he, Complex.zero_re] at hp
  exact (lt_irrefl _ hp)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem partition_shift (F : X → ℝ) (c : ℝ) (z : ℂ) :
    partition μ F z = Complex.exp (z * (c : ℂ)) *
      partition μ (fun x => F x - c) z := by
  unfold partition
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change Complex.exp (z * (F x : ℂ)) =
      Complex.exp (z * (c : ℂ)) * Complex.exp (z * ((F x - c : ℝ) : ℂ))
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring)

/-- Centering improves the controlling size to half the observable's range;
the nonvanishing conclusion is still for the original generating function. -/
theorem partition_ne_zero_of_centered_bound (F : X → ℝ) (hF : Continuous F)
    (c B : ℝ) (hB : ∀ x, |F x - c| ≤ B) (z : ℂ)
    (hz : |z.im| * B < Real.pi / 2) : partition μ F z ≠ 0 := by
  rw [partition_shift μ F c z]
  exact mul_ne_zero (Complex.exp_ne_zero _) (partition_ne_zero μ _
    (hF.sub continuous_const) B hB z hz)

/-- The normalized exponential sum for equal probability at the two points
`-B` and `B`. It exhibits the sharp endpoint of the range-only guarantee. -/
def twoPointPartition (B : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (z * (B : ℂ)) + Complex.exp (-(z * (B : ℂ)))) / 2

theorem twoPointPartition_zero (B : ℝ) (hB : B ≠ 0) :
    twoPointPartition B ((Real.pi / (2 * B) : ℝ) * Complex.I) = 0 := by
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  have he : ((Real.pi / (2 * B) : ℝ) : ℂ) * Complex.I * (B : ℂ) =
      (Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    field_simp
  rw [twoPointPartition, he, Complex.exp_pi_div_two_mul_I]
  have hn : -((Real.pi : ℂ) / 2 * Complex.I) = -(Real.pi : ℂ) / 2 * Complex.I := by ring
  rw [hn, Complex.exp_neg_pi_div_two_mul_I]
  simp

end
end UnifiedTheory.Clay.YangMills.BoundedSourceTube
