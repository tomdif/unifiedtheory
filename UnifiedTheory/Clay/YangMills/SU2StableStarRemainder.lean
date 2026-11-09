/- Global one-sided stability of the actual SU(2) star remainder. Its negative
part is uniformly O(1/beta), including zero-staple configurations. Retaining
the positive remainder gives a stabilized quadratic potential with a uniformly
small nonnegative action change. The positive remainder is not discarded. -/
import UnifiedTheory.Clay.YangMills.SU2GeneralStarApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2StableStarRemainder
noncomputable section
open SU2InducedAction SU2HaarTilt SU2GeneralStarApproximation
open SU2AlignedGaussianApproximation SU2ConditionalInfluence
open scoped Quaternion RealInnerProductSpace

theorem radial_antitone (β : ℝ) (hβ : 0 ≤ β) :
    AntitoneOn (radialPotential β) (Set.Ici 0) := by
  have hd (r : ℝ) : HasDerivAt (radialPotential β)
      (-(2 * β * tiltMean β (r • (1 : ℍ)) 1)) r := by
    simpa only [radialPotential, zero_add] using
      (potential_direction_hasDerivAt β 0 1 r).const_add (12 * β)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    ((continuous_iff_continuousAt.mpr (fun r => (hd r).continuousAt)).continuousOn)
    (fun r _ => (hd r).hasDerivWithinAt)
  intro r hr
  have hr0 : 0 ≤ r := Set.mem_Ici.mp (interior_subset hr)
  exact neg_nonpos.mpr (mul_nonneg (by positivity) (radial_response_nonneg β r hβ hr0))

theorem error_radial (β : ℝ) (A : ℍ) :
    error β A = radialPotential β ‖A‖ - radialPotential β 6 - quadratic β A := by
  rw [← potential_radial]
  unfold error radialPotential
  ring

/-- The entropic correction lowers the radial classical cost. -/
theorem radial_classical_upper (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (hr₆ : r ≤ 6) :
    radialPotential β r - radialPotential β 6 ≤ 2 * β * (6 - r) := by
  have hd (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt (fun t => radialPotential β t + 2 * β * t)
        (2 * β * (1 - axisMean (2 * β * s))) s := by
    convert (radialPotential_hasDerivAt β s hs).add
      ((hasDerivAt_id s).const_mul (2 * β)) using 1
    ring
  have hc : ContinuousOn (fun t => radialPotential β t + 2 * β * t) (Set.Ici 0) := by
    intro s hs
    exact (hd s hs).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
    (fun s hs => by
      have hs0 : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      have hk : 0 < 2 * β * s := by positivity
      have he := (SU2WilsonLocalEquipartition.axisExcess_bounds (2 * β * s) hk.le).1
      rw [axisExcess_identity] at he
      exact mul_nonneg (by positivity) (nonneg_of_mul_nonneg_right he hk))
  have h := hm hr (by norm_num : (0 : ℝ) ≤ 6) hr₆
  linarith

theorem error_upper (β : ℝ) (hβ : 0 < β) (A : ℍ) (hA : ‖A‖ ≤ 6) :
    error β A ≤ β * (6 - ‖A‖) ^ 2 / 6 := by
  have h := radial_classical_upper β ‖A‖ hβ (norm_nonneg A) hA
  rw [error_radial]
  unfold quadratic
  nlinarith

/-- A square completion controls the negative error away from zero staple. -/
theorem error_lower_of_two_le (β : ℝ) (hβ : 0 < β) (A : ℍ)
    (hA : 2 ≤ ‖A‖) (hA₆ : ‖A‖ ≤ 6) :
    -(27 / (32 * β)) ≤ error β A := by
  have h := (abs_le.mp (radial_correction_bound β ‖A‖ hβ (by linarith) hA₆)).1
  have hc : 3 * (6 - ‖A‖) / (2 * ‖A‖) ≤ 3 * (6 - ‖A‖) / 4 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * ‖A‖)).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ 6 - ‖A‖) (by linarith : 0 ≤ ‖A‖ - 2)]
  have hs : -(β * (6 - ‖A‖) ^ 2 / 6 - 3 * (6 - ‖A‖) / 4) ≤ 27 / (32 * β) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * β)).mpr
    nlinarith [sq_nonneg (4 * β * (6 - ‖A‖) - 9)]
  rw [error_radial]
  unfold quadratic
  nlinarith

/-- At small staple the error is nonnegative once beta >= 3/2. -/
theorem error_nonneg_of_norm_le_two (β : ℝ) (hβ : 3 / 2 ≤ β) (A : ℍ)
    (hA : ‖A‖ ≤ 2) : 0 ≤ error β A := by
  have hb : 0 < β := by linarith
  have hm := radial_antitone β hb.le (norm_nonneg A) (by norm_num : (0 : ℝ) ≤ 2) hA
  have h := (abs_le.mp (radial_correction_bound β 2 hb (by norm_num) (by norm_num))).1
  rw [error_radial]
  unfold quadratic
  nlinarith [mul_nonneg hb.le (sq_nonneg ‖A‖)]

/-- Uniform global stability, including A=0; there is no exceptional event. -/
theorem error_lower (β : ℝ) (hβ : 3 / 2 ≤ β) (A : ℍ) (hA : ‖A‖ ≤ 6) :
    -(27 / (32 * β)) ≤ error β A := by
  by_cases htwo : 2 ≤ ‖A‖
  · exact error_lower_of_two_le β (by linarith) A htwo hA
  · exact (neg_nonpos.mpr (by positivity : 0 ≤ 27 / (32 * β))).trans
      (error_nonneg_of_norm_le_two β hβ A (le_of_not_ge htwo))

/-- Keep the positive error, which can suppress rare configurations strongly. -/
def positiveRemainder (β : ℝ) (A : ℍ) : ℝ := max 0 (error β A)

def penalty (β : ℝ) (A : ℍ) : ℝ := max 0 (-error β A)

def stabilizedPotential (β : ℝ) (A : ℍ) : ℝ :=
  potential β ((6 : ℝ) • (1 : ℍ)) + quadratic β A + positiveRemainder β A

theorem positiveRemainder_bounds (β : ℝ) (hβ : 0 < β) (A : ℍ) (hA : ‖A‖ ≤ 6) :
    0 ≤ positiveRemainder β A ∧ positiveRemainder β A ≤ β * (6 - ‖A‖) ^ 2 / 6 :=
  ⟨le_max_left _ _, max_le (by positivity) (error_upper β hβ A hA)⟩

theorem penalty_continuous (β : ℝ) : Continuous (penalty β) :=
  continuous_const.max (error_continuous β).neg

theorem stabilized_difference (β : ℝ) (A : ℍ) :
    stabilizedPotential β A - potential β A = penalty β A := by
  have h := le_total 0 (error β A)
  rcases h with h | h
  · simp only [stabilizedPotential, positiveRemainder, penalty, max_eq_right h,
      max_eq_left (neg_nonpos.mpr h)]
    unfold error
    ring
  · simp only [stabilizedPotential, positiveRemainder, penalty, max_eq_left h,
      max_eq_right (neg_nonneg.mpr h)]
    unfold error
    ring

/-- The retained positive remainder costs only a globally small nonnegative penalty. -/
theorem penalty_bounds (β : ℝ) (hβ : 3 / 2 ≤ β) (A : ℍ) (hA : ‖A‖ ≤ 6) :
    0 ≤ penalty β A ∧ penalty β A ≤ 27 / (32 * β) := by
  refine ⟨le_max_left _ _, max_le (by positivity) ?_⟩
  have h := error_lower β hβ A hA
  linarith

/-- No rare configuration acquires a large relative unnormalized weight. -/
theorem penalty_weight_bounds (β : ℝ) (hβ : 3 / 2 ≤ β) (A : ℍ) (hA : ‖A‖ ≤ 6) :
    Real.exp (-(27 / (32 * β))) ≤ Real.exp (-penalty β A) ∧
      Real.exp (-penalty β A) ≤ 1 := by
  have h := penalty_bounds β hβ A hA
  exact ⟨Real.exp_le_exp.mpr (neg_le_neg h.2), Real.exp_le_one_iff.mpr (neg_nonpos.mpr h.1)⟩

end
end UnifiedTheory.Clay.YangMills.SU2StableStarRemainder
