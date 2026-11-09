/- Two distinct literal coordinate changes in the periodic SU(2) Wilson law.
The previously constructed aligned configurations identify the actual target
fields, without a neighbor-count proxy or a supplied conditional-law premise. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonAlignedRealization
import UnifiedTheory.Clay.YangMills.WilsonCoordinateInfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonTwoNeighborFields
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicTimeReflection
open WilsonSingleLinkStaples WilsonUniformVariance WilsonIndependentBlocks
open SU2StarEnergy SU2WilsonConditionalSource SU2HaarTilt SU2ConditionalInfluence
open SU2AlignedGaussianApproximation SU2WilsonAlignedRealization WilsonCoordinateInfluence
open scoped Quaternion RealInnerProductSpace

def fieldA : ℍ := (6 : ℝ) • (1 : ℍ)
def fieldB : ℍ := (5 : ℝ) • (1 : ℍ) + imaginaryUnit

theorem fieldA_ne_zero : fieldA ≠ 0 := by simp [fieldA]

theorem fieldB_ne_zero : fieldB ≠ 0 := by
  intro h
  have hh := congrArg (fun q : ℍ => q.re) h
  norm_num [fieldB, imaginaryUnit] at hh

theorem field_orientations_ne :
    orientation fieldA fieldA_ne_zero ≠ orientation fieldB fieldB_ne_zero := by
  intro h
  have hB := orientation_decomposition fieldB fieldB_ne_zero
  rw [← h] at hB
  have hi := congrArg (fun q : ℍ => q.imI) hB
  norm_num [fieldB, fieldA, orientation, imaginaryUnit] at hi

theorem aligned_zero_field : alignedSum 0 0 = fieldA := by
  simp only [alignedSum, rotor, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  unfold fieldA
  module

theorem aligned_first_field : alignedSum (Real.pi / 2) 0 = fieldB := by
  simp only [alignedSum, rotor, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, one_smul, zero_smul, add_zero, zero_add]
  unfold fieldB
  module

theorem aligned_second_field : alignedSum 0 (Real.pi / 2) = fieldB := by
  rw [show alignedSum 0 (Real.pi / 2) = alignedSum (Real.pi / 2) 0 by
    unfold alignedSum; abel]
  exact aligned_first_field

variable (n : ℕ)

/-- Positive-link coordinates of the actual edge configuration. -/
def coordinates (U : Configuration (Vertex n) Q) : Link n → Q :=
  fun a => U (selectedLink n a.1 a.2)

theorem toConfiguration_coordinates (U : Configuration (Vertex n) Q) :
    toConfiguration n (coordinates n U) = U := by
  funext e
  change U (selectedLink n (edgeCoord n e).1 (edgeCoord n e).2) = U e
  rw [selected_edgeCoord]

theorem coordinateLaw_coordinates [NeZero n] (β : ℝ)
    (U : Configuration (Vertex n) Q) (a : Link n) :
    coordinateLaw n β (coordinates n U) a =
      conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 U) := by
  rw [coordinateLaw, toConfiguration_coordinates]

def alignedCoordinates (x : Vertex n) (t s : ℝ) : Link n → Q :=
  coordinates n (alignedConfig n x t s)

/-- Varying the first rotor changes exactly the first designated exterior coordinate. -/
theorem change_first (x : Vertex n) (t t' s : ℝ) (a : Link n) (ha : a ≠ (x, 1)) :
    alignedCoordinates n x t s a = alignedCoordinates n x t' s a := by
  by_cases h2 : a = (x, 2)
  · subst a
    change linkValue n Q (alignedConfig n x t s) x 2 =
      linkValue n Q (alignedConfig n x t' s) x 2
    rw [alignedConfig_link_two, alignedConfig_link_two]
  · change linkValue n Q (alignedConfig n x t s) a.1 a.2 =
      linkValue n Q (alignedConfig n x t' s) a.1 a.2
    rw [alignedConfig_other n x a.1 a.2 t s ha h2,
      alignedConfig_other n x a.1 a.2 t' s ha h2]

/-- The second rotor changes a different actual coordinate, with the first rotor retained. -/
theorem change_second (x : Vertex n) (t s s' : ℝ) (a : Link n) (ha : a ≠ (x, 2)) :
    alignedCoordinates n x t s a = alignedCoordinates n x t s' a := by
  by_cases h1 : a = (x, 1)
  · subst a
    change linkValue n Q (alignedConfig n x t s) x 1 =
      linkValue n Q (alignedConfig n x t s') x 1
    rw [alignedConfig_link_one, alignedConfig_link_one]
  · change linkValue n Q (alignedConfig n x t s) a.1 a.2 =
      linkValue n Q (alignedConfig n x t s') a.1 a.2
    rw [alignedConfig_other n x a.1 a.2 t s h1 ha,
      alignedConfig_other n x a.1 a.2 t s' h1 ha]

theorem aligned_coordinate_law [NeZero n] [Fact (1 < n)]
    (β : ℝ) (x : Vertex n) (t s : ℝ) :
    coordinateLaw n β (alignedCoordinates n x t s) (x, 0) =
      tiltLaw β (alignedSum t s) := by
  unfold alignedCoordinates
  rw [coordinateLaw_coordinates, conditionalLaw_eq_tiltLaw]
  have he : exterior n x 0 (alignedConfig n x t s) = alignedExterior n x t s := rfl
  rw [he, alignedExterior_staple]

theorem baseline_law [NeZero n] [Fact (1 < n)] (β : ℝ) (x : Vertex n) :
    coordinateLaw n β (alignedCoordinates n x 0 0) (x, 0) = tiltLaw β fieldA := by
  rw [aligned_coordinate_law, aligned_zero_field]

theorem first_neighbor_law [NeZero n] [Fact (1 < n)] (β : ℝ) (x : Vertex n) :
    coordinateLaw n β (alignedCoordinates n x (Real.pi / 2) 0) (x, 0) =
      tiltLaw β fieldB := by
  rw [aligned_coordinate_law, aligned_first_field]

theorem second_neighbor_law [NeZero n] [Fact (1 < n)] (β : ℝ) (x : Vertex n) :
    coordinateLaw n β (alignedCoordinates n x 0 (Real.pi / 2)) (x, 0) =
      tiltLaw β fieldB := by
  rw [aligned_coordinate_law, aligned_second_field]

end
end UnifiedTheory.Clay.YangMills.WilsonTwoNeighborFields
