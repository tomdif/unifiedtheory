/- An actual two-neighbor obstruction to global microscopic Wilson contraction.
Each of two distinct coordinate influences approaches one from below. This
concerns raw-link conditional comparison, not physical-time mass-gap decay. -/
import UnifiedTheory.Clay.YangMills.SU2HaarSeparation
import UnifiedTheory.Clay.YangMills.WilsonTwoNeighborFields
import UnifiedTheory.Clay.YangMills.WilsonMicroscopicMargin

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonTwoNeighborObstruction
noncomputable section
open MeasureTheory Filter PeriodicLattice4 WilsonSingleLinkStaples WilsonIndependentBlocks
open SU2HaarTilt SU2HaarSeparation WilsonTwoNeighborFields WilsonMicroscopicMargin
open scoped Quaternion RealInnerProductSpace

/-- A fixed explicit constant determined by the two actual exterior fields. -/
def separationConstant : ℝ :=
  (3 / ‖fieldA‖ + 3 / ‖fieldB‖) /
    ‖(orientation fieldA fieldA_ne_zero : ℍ) -
      (orientation fieldB fieldB_ne_zero : ℍ)‖ ^ 2

theorem separationConstant_pos : 0 < separationConstant := by
  have hA : 0 < ‖fieldA‖ := norm_pos_iff.mpr fieldA_ne_zero
  have hB : 0 < ‖fieldB‖ := norm_pos_iff.mpr fieldB_ne_zero
  have hd := separation_sq_pos _ _ field_orientations_ne
  exact div_pos (add_pos (div_pos (by norm_num) hA) (div_pos (by norm_num) hB)) hd

def test : C(Q, ℝ) := separator _ _ field_orientations_ne

theorem test_oscillation (q r : Q) : |test q - test r| ≤ 1 :=
  separator_oscillation _ _ field_orientations_ne q r

theorem test_separation (β : ℝ) (hβ : 0 < β) :
    1 - separationConstant / β ≤
      (∫ q, test q ∂tiltLaw β fieldA) - (∫ q, test q ∂tiltLaw β fieldB) := by
  have h := tilt_separation β hβ fieldA fieldB fieldA_ne_zero fieldB_ne_zero
    field_orientations_ne
  change 1 - separationConstant / β ≤ _
  convert h using 1
  dsimp only [separationConstant]
  ring

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Nonnegativity follows from the actual influence predicate, without an extra hypothesis. -/
theorem influence_nonneg (β : ℝ) (C : Link n → Link n → ℝ)
    (hC : Admissible n β C) (i j : Link n) : 0 ≤ C i j := by
  have h := hC i j (fun _ => (1 : Q)) (fun _ => (1 : Q)) (by intros; rfl)
    0 1 (by intros; simp)
  simpa using h

/-- The first actual exterior coordinate is nearly fully distinguishable. -/
theorem first_coefficient_lower [Fact (1 < n)] (β : ℝ) (hβ : 0 < β)
    (C : Link n → Link n → ℝ) (hC : Admissible n β C) (x : Vertex n) :
    1 - separationConstant / β ≤ C (x, 0) (x, 1) := by
  have h := hC (x, 0) (x, 1) (alignedCoordinates n x 0 0)
    (alignedCoordinates n x (Real.pi / 2) 0) (change_first n x 0 (Real.pi / 2) 0)
    test 1 test_oscillation
  dsimp only at h
  rw [baseline_law, first_neighbor_law, mul_one] at h
  exact (test_separation β hβ).trans ((le_abs_self _).trans h)

/-- A different actual exterior coordinate has the same lower bound. -/
theorem second_coefficient_lower [Fact (1 < n)] (β : ℝ) (hβ : 0 < β)
    (C : Link n → Link n → ℝ) (hC : Admissible n β C) (x : Vertex n) :
    1 - separationConstant / β ≤ C (x, 0) (x, 2) := by
  have h := hC (x, 0) (x, 2) (alignedCoordinates n x 0 0)
    (alignedCoordinates n x 0 (Real.pi / 2)) (change_second n x 0 0 (Real.pi / 2))
    test 1 test_oscillation
  dsimp only at h
  rw [baseline_law, second_neighbor_law, mul_one] at h
  exact (test_separation β hβ).trans ((le_abs_self _).trans h)

/-- The full actual row approaches at least two, uniformly in the periodic volume. -/
theorem row_lower [Fact (1 < n)] (β : ℝ) (hβ : 0 < β)
    (C : Link n → Link n → ℝ) (hC : Admissible n β C) (x : Vertex n) :
    2 - 2 * separationConstant / β ≤ ∑ j, C (x, 0) j := by
  have h12 : (x, (1 : Fin 4)) ≠ (x, (2 : Fin 4)) := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 2) (congrArg Prod.snd h)
  have hs : C (x, 0) (x, 1) + C (x, 0) (x, 2) ≤ ∑ j, C (x, 0) j := by
    calc
      _ = ∑ j ∈ ({(x, 1), (x, 2)} : Finset (Link n)), C (x, 0) j := by
        rw [Finset.sum_pair h12]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => influence_nonneg n β C hC (x, 0) j)
  have h1 := first_coefficient_lower n β hβ C hC x
  have h2 := second_coefficient_lower n β hβ C hC x
  calc
    _ = (1 - separationConstant / β) + (1 - separationConstant / β) := by ring
    _ ≤ C (x, 0) (x, 1) + C (x, 0) (x, 2) := add_le_add h1 h2
    _ ≤ _ := hs

theorem row_gt_one [Fact (1 < n)] (β : ℝ) (hβ : 2 * separationConstant < β)
    (C : Link n → Link n → ℝ) (hC : Admissible n β C) (x : Vertex n) :
    1 < ∑ j, C (x, 0) j := by
  have hp : 0 < β := (mul_pos (by norm_num : (0 : ℝ) < 2) separationConstant_pos).trans hβ
  have hd : 2 * separationConstant / β < 1 := (div_lt_one hp).mpr hβ
  have h := row_lower n β hp C hC x
  linarith

/-- No global raw-link row budget at most one exists above a fixed finite coupling. -/
theorem no_unit_row_budget [Fact (1 < n)] (β : ℝ) (hβ : 2 * separationConstant < β) :
    ¬ ∃ C : Link n → Link n → ℝ, Admissible n β C ∧ ∀ i, (∑ j, C i j) ≤ 1 := by
  rintro ⟨C, hC, hrow⟩
  exact (not_le_of_gt (row_gt_one n β hβ C hC 0)) (hrow (0, 0))

theorem weighted_row_gt_one [Fact (1 < n)] (β : ℝ) (hβ : 2 * separationConstant < β)
    (C w : Link n → Link n → ℝ) (hC : Admissible n β C)
    (hw : ∀ i j, 1 ≤ w i j) (x : Vertex n) :
    1 < ∑ j, w (x, 0) j * C (x, 0) j := by
  apply (row_gt_one n β hβ C hC x).trans_le
  apply Finset.sum_le_sum
  intro j _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw (x, 0) j)
    (influence_nonneg n β C hC (x, 0) j)

end

section Trajectory
open Filter WilsonIndependentBlocks WilsonMicroscopicMargin

/-- The obstruction persists along any diverging trajectory, including changing volumes. -/
theorem eventually_no_unit_row_budget (N : ℕ → ℕ)
    [∀ k, NeZero (N k)] [∀ k, Fact (1 < N k)]
    (β : ℕ → ℝ) (hβ : Tendsto β atTop atTop) :
    ∀ᶠ k in atTop, ¬ ∃ C : Link (N k) → Link (N k) → ℝ,
      Admissible (N k) (β k) C ∧ ∀ i, (∑ j, C i j) ≤ 1 := by
  filter_upwards [hβ.eventually_gt_atTop (2 * separationConstant)] with k hk
  exact no_unit_row_budget (N k) (β k) hk

end Trajectory
end UnifiedTheory.Clay.YangMills.WilsonTwoNeighborObstruction
