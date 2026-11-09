/- A necessary lower bound for every global one-link influence matrix of
the actual Wilson law. The margin to one vanishes at weak coupling. This
obstructs a microscopic comparison shortcut, not a physical mass gap. -/
import UnifiedTheory.Clay.YangMills.WilsonAlignedConditional
import UnifiedTheory.Clay.YangMills.WeightedMixedInfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMicroscopicMargin
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks
open WilsonSingleLinkStaples WilsonAlignedConditional SU2HaarTilt ParallelOscillation

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- The existing local-influence predicate applied to the literal Wilson conditional laws. -/
def Admissible (β : ℝ) (C : Link n → Link n → ℝ) : Prop :=
  LocalInfluence (fun i U => WilsonCoordinateInfluence.coordinateLaw n β U i) C

/-- Telescoping between two actual flat exteriors bounds every row from below. -/
theorem row_lower (β : ℝ) (C : Link n → Link n → ℝ) (hC : Admissible n β C)
    (a : Link n) : axisMean (12 * β) ≤ ∑ j, C a j := by
  let M : (Link n → Q) → ℝ := fun U =>
    ∫ q, probe q ∂WilsonCoordinateInfluence.coordinateLaw n β U a
  have hosc : FiniteProductInfluence.OscBound M (fun j => C a j * 2) := by
    intro j U V hUV
    exact hC a j U V hUV probe 2 probe_oscillation
  have h := global_difference M (fun j => C a j * 2) hosc
    (fun _ => (1 : Q)) (fun _ => (-1 : Q))
  change |(∫ q, probe q ∂WilsonCoordinateInfluence.coordinateLaw n β (fun _ => 1) a) -
    (∫ q, probe q ∂WilsonCoordinateInfluence.coordinateLaw n β (fun _ => -1) a)| ≤ _ at h
  rw [constant_coordinate_mean, constant_coordinate_mean] at h
  norm_num only [probe, ContinuousMap.coe_mk, OneMemClass.coe_one, Unitary.coe_neg,
    real_inner_self_eq_norm_sq, inner_neg_left, norm_one, one_pow, mul_one, mul_neg_one] at h
  rw [← Finset.sum_mul] at h
  linarith [le_abs_self (axisMean (12 * β) - -axisMean (12 * β))]

/-- Actual Haar concentration forces the global microscopic row budget toward one. -/
theorem row_lower_explicit (β : ℝ) (hβ : 0 < β) (C : Link n → Link n → ℝ)
    (hC : Admissible n β C) (a : Link n) :
    1 - 1 / (8 * β) ≤ ∑ j, C a j := by
  have h := SU2HaarCovariance.axis_concentration (κ := 12 * β) (by positivity)
  have he : 3 / (2 * (12 * β)) = 1 / (8 * β) := by ring
  rw [he] at h
  linarith [row_lower n β C hC a]

/-- Adding weights at least one cannot evade the necessary row lower bound. -/
theorem weighted_row_lower (β : ℝ) (hβ : 0 < β) (C w : Link n → Link n → ℝ)
    (hC : Admissible n β C) (hC0 : ∀ i j, 0 ≤ C i j) (hw : ∀ i j, 1 ≤ w i j)
    (a : Link n) : 1 - 1 / (8 * β) ≤ ∑ j, w a j * C a j := by
  apply (row_lower_explicit n β hβ C hC a).trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw a j) (hC0 a j)

/-- Any claimed margin is at most 1/(8 beta), independently of lattice volume. -/
theorem margin_bound (β α : ℝ) (hβ : 0 < β) (C : Link n → Link n → ℝ)
    (hC : Admissible n β C) (a : Link n) (hrow : ∑ j, C a j ≤ α) :
    (1 - α) * β ≤ 1 / 8 := by
  have h := (row_lower_explicit n β hβ C hC a).trans hrow
  have hp := mul_le_mul_of_nonneg_right h hβ.le
  have he : (1 - 1 / (8 * β)) * β = β - 1 / 8 := by field_simp
  rw [he] at hp
  nlinarith

/-- A fixed positive microscopic margin imposes a finite upper bound on beta. -/
theorem coupling_bound (β α : ℝ) (hβ : 0 < β) (hα : α < 1)
    (C : Link n → Link n → ℝ) (hC : Admissible n β C)
    (a : Link n) (hrow : ∑ j, C a j ≤ α) : β ≤ 1 / (8 * (1 - α)) := by
  have h := margin_bound n β α hβ C hC a hrow
  have hpos : 0 < 1 - α := sub_pos.mpr hα
  apply (le_div_iff₀ (by positivity : 0 < 8 * (1 - α))).mpr
  nlinarith

end

section Trajectory
open Filter WilsonIndependentBlocks
variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] [∀ k, Fact (1 < N k)]

/-- This rules out a common row margin along diverging couplings, even when volumes change. -/
theorem eventually_row_exceeds (β : ℕ → ℝ) (hβ : Tendsto β atTop atTop)
    (C : (k : ℕ) → Link (N k) → Link (N k) → ℝ)
    (hC : ∀ k, Admissible (N k) (β k) (C k)) (a : (k : ℕ) → Link (N k))
    (α : ℝ) (hα : α < 1) : ∀ᶠ k in atTop, α < ∑ j, C k (a k) j := by
  have hpos : 0 < 1 - α := sub_pos.mpr hα
  have hden : 0 < 8 * (1 - α) := by positivity
  filter_upwards [hβ.eventually_gt_atTop (1 / (8 * (1 - α)))] with k hk
  have hpos : 0 < β k := (div_pos (by norm_num) hden).trans hk
  by_contra hn
  exact (not_le_of_gt hk) (coupling_bound (N k) (β k) α hpos hα (C k) (hC k)
    (a k) (le_of_not_gt hn))

/-- The same obstruction applies to every nonnegative majorant with weights at least one. -/
theorem eventually_weighted_row_exceeds (β : ℕ → ℝ) (hβ : Tendsto β atTop atTop)
    (C w : (k : ℕ) → Link (N k) → Link (N k) → ℝ)
    (hC : ∀ k, Admissible (N k) (β k) (C k))
    (hC0 : ∀ k i j, 0 ≤ C k i j) (hw : ∀ k i j, 1 ≤ w k i j)
    (a : (k : ℕ) → Link (N k)) (α : ℝ) (hα : α < 1) :
    ∀ᶠ k in atTop, α < ∑ j, w k (a k) j * C k (a k) j := by
  filter_upwards [eventually_row_exceeds N β hβ C hC a α hα] with k hk
  apply hk.trans_le
  apply Finset.sum_le_sum
  intro j _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw k (a k) j) (hC0 k (a k) j)

end Trajectory
end UnifiedTheory.Clay.YangMills.WilsonMicroscopicMargin
