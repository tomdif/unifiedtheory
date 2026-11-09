/- A quadratic approximation to the genuine SU(2) six-staple Haar free energy
in every quaternion direction. The error is controlled by the exact staple
deficit, without a common rotation plane. This is a one-integration estimate;
it does not assert control of successive induced laws. -/
import UnifiedTheory.Clay.YangMills.SU2AlignedGaussianApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2GeneralStarApproximation
noncomputable section
open MeasureTheory SU2QuaternionEquivalence
open SU2InducedAction SU2HaarTilt SU2AlignedGaussianApproximation
open scoped Quaternion RealInnerProductSpace

/-- The exact quadratic disagreement energy of a six-staple vector. -/
def quadratic (β : ℝ) (A : ℍ) : ℝ := β * (36 - ‖A‖ ^ 2) / 6

/-- Vacuum-subtracted actual Haar potential minus the quadratic model. -/
def error (β : ℝ) (A : ℍ) : ℝ :=
  potential β A - potential β ((6 : ℝ) • (1 : ℍ)) - quadratic β A

theorem potential_continuous (β : ℝ) : Continuous (potential β) := by
  have hp : Continuous (tiltPartition β) := by
    unfold tiltPartition tiltWeight
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (show Continuous (fun z : ℍ × UnitQuaternion =>
          Real.exp (2 * β * ⟪(z.2 : ℍ), z.1⟫)) from by fun_prop)
        (isCompact_univ : IsCompact (Set.univ : Set UnitQuaternion))
  exact (hp.log (fun A => (tiltPartition_pos β A).ne')).neg

theorem error_continuous (β : ℝ) : Continuous (error β) := by
  unfold error quadratic
  exact ((potential_continuous β).sub continuous_const).sub (by fun_prop)

theorem potential_radial (β : ℝ) (A : ℍ) :
    12 * β + potential β A = radialPotential β ‖A‖ := by
  simp only [radialPotential, potential, tiltPartition_radial, norm_smul,
    Real.norm_eq_abs, norm_one, mul_one, abs_of_nonneg (norm_nonneg _)]

/-- No alignment assumption: only the norm of the actual staple sum enters. -/
theorem error_bound (β : ℝ) (A : ℍ) (hβ : 0 < β)
    (hA : 0 < ‖A‖) (hA₆ : ‖A‖ ≤ 6) :
    |error β A| ≤ β * (6 - ‖A‖) ^ 2 / 6 + 3 * (6 - ‖A‖) / (2 * ‖A‖) := by
  have h := radial_correction_bound β ‖A‖ hβ hA hA₆
  have hrad := potential_radial β A
  have hbase : radialPotential β 6 =
      12 * β + potential β ((6 : ℝ) • (1 : ℍ)) := rfl
  have he : error β A =
      (radialPotential β ‖A‖ - radialPotential β 6 - 2 * β * (6 - ‖A‖)) +
        β * (6 - ‖A‖) ^ 2 / 6 := by
    rw [← hrad, hbase]
    unfold error quadratic
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ β * (6 - ‖A‖) ^ 2 / 6)]
  linarith

/-- A uniform small-deficit estimate, valid in all directions. -/
theorem error_bound_of_deficit (β d : ℝ) (A : ℍ) (hβ : 0 < β)
    (hd : 0 ≤ d) (hd₃ : d ≤ 3) (hA₆ : ‖A‖ ≤ 6) (hdef : 6 - ‖A‖ ≤ d) :
    |error β A| ≤ β * d ^ 2 / 6 + d / 2 := by
  have hA₃ : 3 ≤ ‖A‖ := by linarith
  apply (error_bound β A hβ (by linarith) hA₆).trans
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : 0 ≤ 6 - ‖A‖) hdef 2) hβ.le) (by norm_num)
  · apply (div_le_iff₀ (by linarith : 0 < 2 * ‖A‖)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hA₃ hd]

/-- Uniform O(1/beta) control on every bounded fluctuation-energy region. -/
theorem error_bound_scaled_deficit (β K : ℝ) (A : ℍ) (hβ : 0 < β)
    (hK : 0 ≤ K) (hKβ : K ≤ β) (hA₆ : ‖A‖ ≤ 6)
    (hdef : β * (6 - ‖A‖) ≤ K) :
    |error β A| ≤ (K ^ 2 / 6 + K / 2) / β := by
  have hd : K / β ≤ 3 := (div_le_one hβ).mpr hKβ |>.trans (by norm_num)
  have h := error_bound_of_deficit β (K / β) A hβ (div_nonneg hK hβ.le) hd hA₆
    ((le_div_iff₀ hβ).mpr (by nlinarith [hdef]))
  convert h using 1
  field_simp

/-- The shrinking good region used for an actual-law probability estimate. -/
theorem error_bound_fourth_power (t : ℝ) (ht : 1 ≤ t) (A : ℍ)
    (hA₆ : ‖A‖ ≤ 6) (hdef : 6 - ‖A‖ ≤ 1 / t ^ 3) :
    |error (t ^ 4) A| ≤ 2 / (3 * t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have hd : 1 / t ^ 3 ≤ 3 := by
    apply (div_le_iff₀ (pow_pos ht0 3)).mpr
    linarith
  apply (error_bound_of_deficit (t ^ 4) (1 / t ^ 3) A (by positivity)
    (by positivity) hd hA₆ hdef).trans
  apply (le_of_sub_nonneg ?_)
  have he : 2 / (3 * t ^ 2) - (t ^ 4 * (1 / t ^ 3) ^ 2 / 6 + (1 / t ^ 3) / 2) =
      (t - 1) / (2 * t ^ 3) := by field_simp; ring
  rw [he]
  exact div_nonneg (sub_nonneg.mpr ht) (by positivity)

/-- All pairwise chord distances, counting each unordered pair once. -/
def disagreement {I : Type*} (s : Finset I) (u : I → ℍ) : ℝ :=
  (∑ i ∈ s, ∑ j ∈ s, ‖u i - u j‖ ^ 2) / 2

/-- Exact geometric identity for arbitrary six unit staples. -/
theorem disagreement_eq {I : Type*} (s : Finset I) (u : I → ℍ)
    (hs : s.card = 6) (hu : ∀ i ∈ s, ‖u i‖ = 1) :
    disagreement s u = 36 - ‖∑ i ∈ s, u i‖ ^ 2 := by
  have hn : (∑ j ∈ s, ‖u j‖ ^ 2) = 6 := by
    calc
      _ = ∑ _j ∈ s, (1 : ℝ) := Finset.sum_congr rfl (fun j hj => by rw [hu j hj]; norm_num)
      _ = 6 := by simp [hs]
  have hi (i : I) (h : i ∈ s) :
      (∑ j ∈ s, ‖u i - u j‖ ^ 2) = 12 - 2 * ⟪u i, ∑ j ∈ s, u j⟫ := by
    simp_rw [norm_sub_sq_real, hu i h]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hn]
    simp only [one_pow, Finset.sum_const, hs, nsmul_eq_mul, Nat.cast_ofNat,
      mul_one, ← Finset.mul_sum, ← inner_sum]
    ring
  unfold disagreement
  rw [Finset.sum_congr rfl hi]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, hs, nsmul_eq_mul,
    Nat.cast_ofNat, ← Finset.mul_sum, ← sum_inner, real_inner_self_eq_norm_sq]
  ring

theorem disagreement_nonneg {I : Type*} (s : Finset I) (u : I → ℍ) :
    0 ≤ disagreement s u := by
  unfold disagreement
  positivity

/-- The approximation is a quadratic form in actual staple differences. -/
theorem quadratic_eq_disagreement {I : Type*} (s : Finset I) (u : I → ℍ)
    (hs : s.card = 6) (hu : ∀ i ∈ s, ‖u i‖ = 1) (β : ℝ) :
    quadratic β (∑ i ∈ s, u i) = β * disagreement s u / 6 := by
  rw [disagreement_eq s u hs hu]
  rfl

end
end UnifiedTheory.Clay.YangMills.SU2GeneralStarApproximation
