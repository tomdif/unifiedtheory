/-
  Audit/KFCausalHolonomyInterferenceLaw.lean

  CAUSAL HOLONOMY INTERFERENCE LAW

  This module records a parameter-free connection between two independently
  constructed parts of the repository:

    * native Boolean-CSpec continuation matching, whose permutation scores are
      18, 0, -9 on the three conjugacy classes of S3; and
    * the intrinsic trace-zero three-sheet carrier, whose normalized character
      is 1, 0, -1/2 on the same classes.

  The normalized continuation score is therefore exactly one half of the
  standard S3 character.  For histories with sheet holonomies g and h, the
  geometric visibility depends only on the relative holonomy h^-1 g.

  A flattened centered permutation carrier supplies an explicit Gram
  realization, hence Hermiticity and strong positivity for every finite family
  of histories.  The final section combines a relative three-cycle with the
  already formalized quadrature character.  The resulting two-history kernel is
  `balancedHistoryKernel (1/4)`: it has equal Born weights, nonzero purely
  imaginary interference, total measure one, and strict rank two.

  SCOPE.  This is an exact finite interference law and a normalized two-history
  completion.  It does not construct a projectively consistent operator-valued
  sequential-growth law over every causal-set depth.  That remains the
  microscopic promotion theorem.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBooleanCubeMargin
import UnifiedTheory.Audit.KFCubicSheetFrameRigidity
import UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalHolonomyInterferenceLaw

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecOverlapScore
open UnifiedTheory.Audit.KFCausalCSpecBooleanCubeMargin
open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
open UnifiedTheory.Audit.KFCubicSheetFrameRigidity
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

/-! ## 1. The normalized standard character forced by continuation geometry -/

/-- Real fixed-point count of a permutation of the three intrinsic directions. -/
def directionFixedPointCount (relabeling : Equiv.Perm Direction) : ℝ :=
  ∑ direction : Direction, if relabeling direction = direction then 1 else 0

/-- The character of the standard two-dimensional representation of `S3`,
written intrinsically as `fixed points - 1`. -/
def standardS3Character (relabeling : Equiv.Perm Direction) : ℝ :=
  directionFixedPointCount relabeling - 1

/-- Parameter-free geometric visibility associated with a relative sheet
holonomy. -/
def causalHolonomyVisibility (relabeling : Equiv.Perm Direction) : ℝ :=
  standardS3Character relabeling / 2

/-- The native Boolean-CSpec continuation score is exactly nine times the
standard `S3` character. -/
theorem booleanCube_permScore_eq_nine_standardCharacter
    (relabeling : Equiv.Perm Direction) :
    permScore cprof cprof relabeling = 9 * standardS3Character relabeling := by
  rw [permScore_closed]
  unfold standardS3Character directionFixedPointCount
  rw [Fin.sum_univ_three]
  by_cases h0 : relabeling 0 = 0 <;>
    by_cases h1 : relabeling 1 = 1 <;>
      by_cases h2 : relabeling 2 = 2 <;>
        simp [h0, h1, h2] <;> ring

/-- **CSpec/carrier identification.**  Normalizing the native continuation
score by its identity value `18` gives the causal holonomy visibility. -/
theorem causalHolonomyVisibility_eq_normalized_permScore
    (relabeling : Equiv.Perm Direction) :
    causalHolonomyVisibility relabeling =
      permScore cprof cprof relabeling / 18 := by
  rw [booleanCube_permScore_eq_nine_standardCharacter]
  unfold causalHolonomyVisibility
  ring

/-- Identity relative holonomy gives full constructive visibility. -/
theorem causalHolonomyVisibility_identity :
    causalHolonomyVisibility (1 : Equiv.Perm Direction) = 1 := by
  norm_num [causalHolonomyVisibility, standardS3Character,
    directionFixedPointCount, Fin.sum_univ_three]

/-- A relative transposition gives exact geometric decoherence. -/
theorem causalHolonomyVisibility_transposition :
    causalHolonomyVisibility (Equiv.swap (0 : Direction) 1) = 0 := by
  rw [causalHolonomyVisibility_eq_normalized_permScore]
  rw [booleanCube_permScores.2.1]
  norm_num

/-- A relative three-cycle gives the fixed destructive visibility `-1/2`. -/
theorem causalHolonomyVisibility_threeCycle :
    causalHolonomyVisibility
        (Equiv.swap (0 : Direction) 1 * Equiv.swap 1 2) = -1 / 2 := by
  rw [causalHolonomyVisibility_eq_normalized_permScore]
  rw [booleanCube_permScores.2.2]
  norm_num

/-- Character visibility is gauge invariant: simultaneous sheet relabeling
only conjugates the relative holonomy. -/
theorem causalHolonomyVisibility_conjugation
    (g relabeling : Equiv.Perm Direction) :
    causalHolonomyVisibility (g * relabeling * g.symm) =
      causalHolonomyVisibility relabeling := by
  have hFixed : directionFixedPointCount (g * relabeling * g.symm) =
      directionFixedPointCount relabeling := by
    unfold directionFixedPointCount
    rw [← Equiv.sum_comp g]
    apply Finset.sum_congr rfl
    intro direction _hDirection
    simp [Equiv.Perm.mul_apply]
  unfold causalHolonomyVisibility standardS3Character
  rw [hFixed]

/-! ## 2. Strong positivity for arbitrary history holonomies -/

/-- The centered permutation matrix, flattened as a finite carrier vector.
It is the standard representation embedded in the three-dimensional
permutation module. -/
def centeredPermutationAmplitude (relabeling : Equiv.Perm Direction) :
    Direction × Direction → ℂ :=
  fun coordinate =>
    (if coordinate.2 = relabeling coordinate.1 then (1 : ℂ) else 0) - 1 / 3

/-- One centered delta profile has overlap `2/3` with itself and `-1/3`
with either distinct profile. -/
theorem centeredDelta_inner (first second : Direction) :
    (∑ direction : Direction,
      ((if direction = first then (1 : ℂ) else 0) - 1 / 3) *
        star ((if direction = second then (1 : ℂ) else 0) - 1 / 3)) =
      if first = second then 2 / 3 else -1 / 3 := by
  have h01 : (0 : Direction) ≠ 1 := by decide
  have h02 : (0 : Direction) ≠ 2 := by decide
  have h12 : (1 : Direction) ≠ 2 := by decide
  fin_cases first <;> fin_cases second <;>
    simp [Fin.sum_univ_three, h01, h02, h12] <;> norm_num

/-- Relative holonomy of two histories in a common sheet frame. -/
def relativeHolonomy {History : Type*}
    (holonomy : History → Equiv.Perm Direction) (first second : History) :
    Equiv.Perm Direction :=
  (holonomy second).symm * holonomy first

/-- The centered permutation carriers have Hilbert-Schmidt overlap equal to
the standard character of the relative holonomy. -/
theorem centeredPermutationAmplitude_inner_eq_character
    (first second : Equiv.Perm Direction) :
    finiteVectorInner (centeredPermutationAmplitude first)
        (centeredPermutationAmplitude second) =
      (standardS3Character (second.symm * first) : ℂ) := by
  unfold finiteVectorInner centeredPermutationAmplitude
  rw [Fintype.sum_prod_type]
  simp_rw [centeredDelta_inner]
  have hFixed (direction : Direction) :
      (second.symm * first) direction = direction ↔
        first direction = second direction := by
    constructor
    · intro h
      apply second.injective
      simpa [Equiv.Perm.mul_apply] using congrArg second h
    · intro h
      apply second.injective
      simp [Equiv.Perm.mul_apply, h]
  unfold standardS3Character directionFixedPointCount
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp_rw [hFixed]
  by_cases h0 : first 0 = second 0 <;>
    by_cases h1 : first 1 = second 1 <;>
      by_cases h2 : first 2 = second 2 <;>
        simp [h0, h1, h2] <;> ring

/-- The visibility kernel on any history type, obtained from the explicit
centered permutation carrier and normalized by its squared dimension `2`. -/
def causalHolonomyVisibilityKernel {History : Type*}
    (holonomy : History → Equiv.Perm Direction) :
    GrowthDecoherenceFunctional History :=
  (1 / 2 : ℂ) • vectorAmplitudeKernel
    (fun history => centeredPermutationAmplitude (holonomy history))

/-- The abstract kernel is exactly the normalized character of relative
holonomy. -/
theorem causalHolonomyVisibilityKernel_eq
    {History : Type*} (holonomy : History → Equiv.Perm Direction)
    (first second : History) :
    causalHolonomyVisibilityKernel holonomy first second =
      (causalHolonomyVisibility
        (relativeHolonomy holonomy first second) : ℂ) := by
  rw [causalHolonomyVisibilityKernel]
  change (1 / 2 : ℂ) *
      finiteVectorInner (centeredPermutationAmplitude (holonomy first))
        (centeredPermutationAmplitude (holonomy second)) = _
  rw [centeredPermutationAmplitude_inner_eq_character]
  unfold causalHolonomyVisibility relativeHolonomy
  push_cast
  ring

/-- Every history has unit geometric visibility with itself. -/
theorem causalHolonomyVisibilityKernel_diagonal
    {History : Type*} (holonomy : History → Equiv.Perm Direction)
    (history : History) :
    causalHolonomyVisibilityKernel holonomy history history = 1 := by
  rw [causalHolonomyVisibilityKernel_eq]
  have hRelative : relativeHolonomy holonomy history history = 1 := by
    unfold relativeHolonomy
    exact Equiv.self_trans_symm _
  rw [hRelative, causalHolonomyVisibility_identity]
  norm_num

/-- The relative-holonomy visibility kernel is Hermitian. -/
theorem causalHolonomyVisibilityKernel_hermitian
    {History : Type*} (holonomy : History → Equiv.Perm Direction) :
    IsHermitianGrowthFunctional (causalHolonomyVisibilityKernel holonomy) := by
  intro first second
  unfold causalHolonomyVisibilityKernel
  change (1 / 2 : ℂ) *
      vectorAmplitudeKernel
        (fun history => centeredPermutationAmplitude (holonomy history))
        first second =
    star ((1 / 2 : ℂ) *
      vectorAmplitudeKernel
        (fun history => centeredPermutationAmplitude (holonomy history))
        second first)
  rw [(vectorAmplitudeKernel_hermitian
    (fun history => centeredPermutationAmplitude (holonomy history))) first second]
  rw [StarMul.star_mul]
  norm_num
  ring

/-- **Strong positivity.**  The normalized character law is a Gram kernel for
every finite family of histories, including repeated histories. -/
theorem causalHolonomyVisibilityKernel_stronglyPositive
    {History : Type*} (holonomy : History → Equiv.Perm Direction) :
    IsStronglyPositiveGrowthFunctional
      (causalHolonomyVisibilityKernel holonomy) := by
  intro n sample
  have hRaw := vectorAmplitudeKernel_stronglyPositive
    (fun history => centeredPermutationAmplitude (holonomy history)) n sample
  change Matrix.PosSemidef ((1 / 2 : ℂ) •
    (fun i j => vectorAmplitudeKernel
      (fun history => centeredPermutationAmplitude (holonomy history))
      (sample i) (sample j)))
  have hHalf : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    have hHalfCast : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hHalfCast]
    exact RCLike.ofReal_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact Matrix.PosSemidef.smul hRaw hHalf

/-! ## 3. The minimal normalized holonomy-chirality completion -/

/-- Equal Born weights in quadrature.  The relative scalar phase between the
two routes is `i`. -/
def equalBornQuadratureWeight (route : Fin 2) : ℂ :=
  if route = 0 then (1 / spinOneSqrtTwo : ℝ)
  else Complex.I * (1 / spinOneSqrtTwo : ℝ)

/-- The two routes differ by one three-cycle of the intrinsic directions. -/
def threeCycleHolonomy (route : Fin 2) : Equiv.Perm Direction :=
  if route = 0 then 1 else Equiv.swap 0 1 * Equiv.swap 1 2

/-- Weighting the geometric visibility by equal quadrature amplitudes. -/
def holonomyChiralityPairKernel : SquareMatrix 2 :=
  fun first second =>
    equalBornQuadratureWeight first * star (equalBornQuadratureWeight second) *
      causalHolonomyVisibilityKernel threeCycleHolonomy first second

/-- **Finite normalized completion.**  A relative three-cycle contributes
`-1/2`; the quadrature phase rotates that real destructive overlap into the
purely imaginary balanced coherence `i/4`. -/
theorem holonomyChiralityPairKernel_eq_balanced :
    holonomyChiralityPairKernel = balancedHistoryKernel (1 / 4) := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [holonomyChiralityPairKernel, equalBornQuadratureWeight,
      threeCycleHolonomy, causalHolonomyVisibilityKernel_eq,
      relativeHolonomy, causalHolonomyVisibility, standardS3Character,
      directionFixedPointCount, Equiv.swap_apply_def, Equiv.Perm.mul_apply,
      balancedHistoryKernel]
  all_goals
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

/-- The completed pair is a positive trace-one density kernel. -/
theorem holonomyChiralityPairKernel_isPathDensity :
    IsPathDensity holonomyChiralityPairKernel := by
  rw [holonomyChiralityPairKernel_eq_balanced]
  exact balancedHistoryKernel_isPathDensity (by norm_num)

/-- Its complete two-history event has total measure one. -/
theorem holonomyChiralityPairKernel_total_measure :
    pathHistoryMeasure holonomyChiralityPairKernel Finset.univ = 1 := by
  rw [holonomyChiralityPairKernel_eq_balanced]
  exact balancedHistoryKernel_total_measure (1 / 4)

/-- The two singleton Born weights add to one. -/
theorem holonomyChiralityPairKernel_born_diagonal_normalized :
    holonomyChiralityPairKernel 0 0 + holonomyChiralityPairKernel 1 1 = 1 := by
  rw [holonomyChiralityPairKernel_eq_balanced]
  norm_num [balancedHistoryKernel]

/-- Interference survives normalization and is exactly `i/4`. -/
theorem holonomyChiralityPairKernel_nonzero_interference :
    holonomyChiralityPairKernel 0 1 = Complex.I / 4
      ∧ holonomyChiralityPairKernel 0 1 ≠ 0 := by
  rw [holonomyChiralityPairKernel_eq_balanced]
  constructor
  · norm_num [balancedHistoryKernel]
    ring
  · norm_num [balancedHistoryKernel, Complex.I_ne_zero]

/-- The completion has strict latent rank two, so the scalar obstruction is
genuinely escaped rather than hidden by notation. -/
theorem holonomyChiralityPairKernel_minimal_rank_two :
    IsTwoComponentAmplitudeKernel holonomyChiralityPairKernel
      ∧ ¬ IsScalarAmplitudeKernel holonomyChiralityPairKernel := by
  rw [holonomyChiralityPairKernel_eq_balanced]
  exact balancedHistoryKernel_minimal_latent_rank (y := (1 / 4 : ℝ))
    (by norm_num) |>.imp_right (fun h => h (by norm_num))

/-! ## 4. Promotion boundary -/

/-- The exact finite package now obtained.  Projective sequential composition
is deliberately absent from this statement. -/
theorem causalHolonomyInterference_finite_package :
    causalHolonomyVisibility (1 : Equiv.Perm Direction) = 1
      ∧ causalHolonomyVisibility (Equiv.swap (0 : Direction) 1) = 0
      ∧ causalHolonomyVisibility
          (Equiv.swap (0 : Direction) 1 * Equiv.swap 1 2) = -1 / 2
      ∧ IsPathDensity holonomyChiralityPairKernel
      ∧ pathHistoryMeasure holonomyChiralityPairKernel Finset.univ = 1
      ∧ holonomyChiralityPairKernel 0 1 ≠ 0
      ∧ IsTwoComponentAmplitudeKernel holonomyChiralityPairKernel
      ∧ ¬ IsScalarAmplitudeKernel holonomyChiralityPairKernel := by
  exact ⟨causalHolonomyVisibility_identity,
    causalHolonomyVisibility_transposition,
    causalHolonomyVisibility_threeCycle,
    holonomyChiralityPairKernel_isPathDensity,
    holonomyChiralityPairKernel_total_measure,
    holonomyChiralityPairKernel_nonzero_interference.2,
    holonomyChiralityPairKernel_minimal_rank_two.1,
    holonomyChiralityPairKernel_minimal_rank_two.2⟩

#print axioms booleanCube_permScore_eq_nine_standardCharacter
#print axioms causalHolonomyVisibility_eq_normalized_permScore
#print axioms causalHolonomyVisibility_conjugation
#print axioms centeredPermutationAmplitude_inner_eq_character
#print axioms causalHolonomyVisibilityKernel_stronglyPositive
#print axioms holonomyChiralityPairKernel_eq_balanced
#print axioms causalHolonomyInterference_finite_package

end

end UnifiedTheory.Audit.KFCausalHolonomyInterferenceLaw
