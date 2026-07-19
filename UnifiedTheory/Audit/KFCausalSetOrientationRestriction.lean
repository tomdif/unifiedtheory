/-
  Audit/KFCausalSetOrientationRestriction.lean

  CAUSAL-GROWTH CYLINDERS TO THE BALANCED ORIENTATION KERNEL

  This file makes explicit the bridge that was implicit in the physical
  sequential-growth promotion.  A finite cylinder partition into two
  orientation sectors induces a literal `2 x 2` decoherence kernel.  Strong
  positivity, Hermiticity, and total-event normalization descend from the
  causal growth functional.  If the two diagonal sector weights are balanced,
  the existing rigidity theorem supplies a unique parameter

      y in [-1/2,1/2]

  and identifies the restriction exactly with `balancedHistoryKernel y`.

  The bridge is projectively natural: refining both sector cylinders leaves
  the induced matrix, and hence `y`, exactly unchanged.  More sharply, the
  scalar-amplitude growth construction makes every finite event kernel rank
  one.  Therefore a balanced restriction has zero determinant and must
  saturate `|y| = 1/2`.  Endpoint selection is already forced by the pure
  amplitude ansatz; Bell causality is needed to classify the microdynamics,
  not to exclude balanced interior kernels inside this ansatz.

  The final section records the zero-safe algebraic form of complex Bell
  causality by cross multiplication on the complete precursor-resolved
  transition slots, while the companion Bell-causality module supplies the
  canonical spectator deletion and proves its present underdetermination.
-/

import UnifiedTheory.Audit.KFCausalSetBellCausality
import UnifiedTheory.Audit.KFOrientationHistoryRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetOrientationRestriction

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality

/-! ## 1. A two-sector cylinder coarse-graining -/

/-- A complete two-sector partition of finite physical growth paths at one
rank.  The sectors are already events of unlabeled causal-set paths. -/
structure OrientationCylinderCoarseGraining where
  depth : ℕ
  sector : Fin 2 → Finset (RankedGrowthPath CausalSetGrowthBranch depth)
  disjoint : Disjoint (sector 0) (sector 1)
  exhaustive : sector 0 ∪ sector 1 = Finset.univ

/-- Restrict a causal growth decoherence functional to the two orientation
cylinder sectors. -/
def inducedOrientationKernel
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) : SquareMatrix 2 :=
  fun first second =>
    growthEventDecoherence
      (finiteRankedDepthDecoherence law coarse.depth)
      (coarse.sector first) (coarse.sector second)

/-- Strong positivity of the growth functional descends to the two-sector
kernel. -/
theorem inducedOrientationKernel_posSemidef
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    (inducedOrientationKernel law coarse).PosSemidef := by
  have hStrong := finiteRankedDepthDecoherence_stronglyPositive
    law coarse.depth
  exact hStrong 2 coarse.sector

theorem inducedOrientationKernel_isHermitian
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    (inducedOrientationKernel law coarse).IsHermitian :=
  (inducedOrientationKernel_posSemidef law coarse).isHermitian

/-- A complete sector partition inherits total-event normalization from the
finite-depth causal growth law. -/
theorem inducedOrientationKernel_total_measure
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    pathHistoryMeasure (inducedOrientationKernel law coarse) Finset.univ = 1 := by
  let D := finiteRankedDepthDecoherence law coarse.depth
  have hTotal : growthEventDecoherence D Finset.univ Finset.univ = 1 :=
    normalized_total_event D
      (finiteRankedDepthDecoherence_normalized law coarse.depth)
  rw [← coarse.exhaustive] at hTotal
  rw [growthEventDecoherence_union_left D _ _ _ coarse.disjoint,
    growthEventDecoherence_union_right D _ _ _ coarse.disjoint,
    growthEventDecoherence_union_right D _ _ _ coarse.disjoint] at hTotal
  have hReal := congrArg Complex.re hTotal
  norm_num [pathHistoryMeasure, pathHistoryKernel,
    inducedOrientationKernel, D, Fin.sum_univ_succ, Fin.ext_iff] at hReal ⊢
  linarith

/-- Balance is precisely equality of both singleton orientation-sector weights
to `1/2`. -/
def OrientationCylinderCoarseGraining.IsBalanced
    (coarse : OrientationCylinderCoarseGraining)
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch) : Prop :=
  inducedOrientationKernel law coarse 0 0 = 1 / 2
    ∧ inducedOrientationKernel law coarse 1 1 = 1 / 2

/-- A balanced causal-cylinder restriction satisfies the complete admissible
kernel contract used by the finite rigidity theorem. -/
theorem inducedOrientationKernel_isAdmissibleBalanced
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    IsAdmissibleBalancedKernel (inducedOrientationKernel law coarse) := by
  exact ⟨inducedOrientationKernel_posSemidef law coarse,
    hBalanced.1, hBalanced.2,
    inducedOrientationKernel_total_measure law coarse⟩

/-- The orientation coordinate read directly from the induced causal-growth
kernel. -/
def inducedOrientationParameter
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) : ℝ :=
  (inducedOrientationKernel law coarse 0 1).im

/-- **Explicit restriction bridge.**  Every balanced two-sector
coarse-graining of the causal growth cylinders induces exactly one member of
the classified `D_y` interval. -/
theorem inducedOrientationKernel_eq_balancedHistoryKernel
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    |inducedOrientationParameter law coarse| ≤ 1 / 2
      ∧ inducedOrientationKernel law coarse =
        balancedHistoryKernel (inducedOrientationParameter law coarse) := by
  obtain ⟨y, hy, hKernel⟩ := admissibleBalancedKernel_classification
    (inducedOrientationKernel_isAdmissibleBalanced law coarse hBalanced)
  have hParameter : inducedOrientationParameter law coarse = y := by
    unfold inducedOrientationParameter
    rw [hKernel]
    norm_num [balancedHistoryKernel, Fin.ext_iff]
  simpa [hParameter] using And.intro hy hKernel

/-- The balanced parameter induced by a causal cylinder partition is unique,
not merely a chosen witness. -/
theorem inducedOrientationKernel_unique_parameter
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    ∃! y : ℝ, |y| ≤ 1 / 2 ∧
      inducedOrientationKernel law coarse = balancedHistoryKernel y :=
  admissibleBalancedKernel_unique_parameter
    (inducedOrientationKernel_isAdmissibleBalanced law coarse hBalanced)

/-! ## 2. Rank-one growth forces endpoint saturation -/

/-- Every two-sector restriction of the repo's scalar-amplitude growth law
has determinant zero.  This is the exact finite statement that the event
decoherence kernel is an outer product, even after coarse-graining paths into
arbitrary disjoint sectors. -/
theorem inducedOrientationKernel_det_zero
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    Matrix.det (inducedOrientationKernel law coarse) = 0 := by
  rw [Matrix.det_fin_two]
  unfold inducedOrientationKernel finiteRankedDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq,
    amplitude_growthEventDecoherence_eq,
    amplitude_growthEventDecoherence_eq,
    amplitude_growthEventDecoherence_eq]
  ring

/-- **Endpoint selection from amplitude purity.**  Balance plus the
rank-one scalar-amplitude construction forces maximal orientation coherence.
No Bell axiom is required for this conclusion. -/
theorem balanced_inducedOrientationParameter_endpoint
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    |inducedOrientationParameter law coarse| = 1 / 2 := by
  let y := inducedOrientationParameter law coarse
  have hKernel : inducedOrientationKernel law coarse =
      balancedHistoryKernel y :=
    (inducedOrientationKernel_eq_balancedHistoryKernel
      law coarse hBalanced).2
  have hDet := inducedOrientationKernel_det_zero law coarse
  rw [hKernel, Matrix.det_fin_two] at hDet
  have hDetRe := congrArg Complex.re hDet
  norm_num [balancedHistoryKernel, Fin.ext_iff, Complex.I_sq] at hDetRe
  have hySq : y * y = (1 / 2 : ℝ) * (1 / 2) := by
    nlinarith
  change |y| = 1 / 2
  rcases (mul_self_eq_mul_self_iff.mp hySq) with hy | hy
  · simp [hy]
  · have hyNegative : y = -1 / 2 := by linarith
    rw [hyNegative]
    norm_num [abs_of_nonpos]

/-- Equivalently, the induced balanced kernel is one of the two orientation
projectors.  The amplitude law still has to decide *which* endpoint occurs. -/
theorem balanced_inducedOrientationKernel_is_endpoint
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    inducedOrientationKernel law coarse = positiveOrientationProjector ∨
      inducedOrientationKernel law coarse = negativeOrientationProjector := by
  let y := inducedOrientationParameter law coarse
  have hKernel : inducedOrientationKernel law coarse =
      balancedHistoryKernel y :=
    (inducedOrientationKernel_eq_balancedHistoryKernel
      law coarse hBalanced).2
  have hEndpoint : |y| = 1 / 2 := by
    simpa [y] using balanced_inducedOrientationParameter_endpoint
      law coarse hBalanced
  have hy : y = 1 / 2 ∨ y = -(1 / 2) := by
    exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hEndpoint
  rcases hy with hy | hy
  · right
    rw [hKernel, hy, balancedHistoryKernel_positiveEndpoint]
  · left
    have hyNegative : y = -1 / 2 := by linarith
    rw [hKernel, hyNegative, balancedHistoryKernel_negativeEndpoint]

/-! ## 3. Naturality under projective refinement -/

/-- Refine both orientation cylinder sectors by one complete causal branching
layer. -/
def OrientationCylinderCoarseGraining.refine
    (coarse : OrientationCylinderCoarseGraining) :
    OrientationCylinderCoarseGraining where
  depth := coarse.depth + 1
  sector := fun orientation =>
    refineRankedGrowthEvent (coarse.sector orientation)
  disjoint := by
    rw [Finset.disjoint_left]
    intro path hFirst hSecond
    rcases path with ⟨pathPrefix, branch⟩
    have hFirstPrefix : pathPrefix ∈ coarse.sector 0 :=
      (Finset.mem_product.mp hFirst).1
    have hSecondPrefix : pathPrefix ∈ coarse.sector 1 :=
      (Finset.mem_product.mp hSecond).1
    exact Finset.disjoint_left.mp coarse.disjoint
      hFirstPrefix hSecondPrefix
  exhaustive := by
    ext path
    rcases path with ⟨pathPrefix, branch⟩
    unfold refineRankedGrowthEvent
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product]
    simp only [Finset.mem_univ, and_true]
    rw [← Finset.mem_union, coarse.exhaustive]
    simp

/-- The explicit restriction commutes with one step of the projective system. -/
theorem inducedOrientationKernel_refine
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    inducedOrientationKernel law coarse.refine =
      inducedOrientationKernel law coarse := by
  ext first second
  exact finiteRankedDepthDecoherence_projective law coarse.depth
    (coarse.sector first) (coarse.sector second)

theorem OrientationCylinderCoarseGraining.isBalanced_refine_iff
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    coarse.refine.IsBalanced law ↔ coarse.IsBalanced law := by
  unfold OrientationCylinderCoarseGraining.IsBalanced
  rw [inducedOrientationKernel_refine]

/-- Exact projective refinement leaves the orientation coordinate unchanged.
Consequently projective consistency by itself cannot contract interior values
of `y` or select the extremal endpoints. -/
theorem inducedOrientationParameter_refine
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    inducedOrientationParameter law coarse.refine =
      inducedOrientationParameter law coarse := by
  unfold inducedOrientationParameter
  rw [inducedOrientationKernel_refine]

/-- Iterated refinement leaves the induced orientation kernel unchanged. -/
def OrientationCylinderCoarseGraining.refineBy
    (coarse : OrientationCylinderCoarseGraining) :
    ℕ → OrientationCylinderCoarseGraining
  | 0 => coarse
  | steps + 1 => (refineBy coarse steps).refine

theorem inducedOrientationKernel_refineBy
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    ∀ steps : ℕ,
      inducedOrientationKernel law (coarse.refineBy steps) =
        inducedOrientationKernel law coarse
  | 0 => rfl
  | steps + 1 => by
      rw [OrientationCylinderCoarseGraining.refineBy,
        inducedOrientationKernel_refine,
        inducedOrientationKernel_refineBy law coarse steps]

theorem inducedOrientationParameter_refineBy
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) :
    ∀ steps : ℕ,
      inducedOrientationParameter law (coarse.refineBy steps) =
        inducedOrientationParameter law coarse := by
  intro steps
  unfold inducedOrientationParameter
  rw [inducedOrientationKernel_refineBy]

/-! ## 4. The precursor-resolved zero-safe Bell-causality interface -/

/-- One raw precursor transition slot above an unlabeled growth prefix.  The
labeled representative is retained only to enumerate the distinct precursor
sets; `identifiesParent` connects it to the quotient state. -/
structure PhysicalCausalTransitionSlot where
  rank : ℕ
  pathPrefix : RankedGrowthPath CausalSetGrowthBranch rank
  parentRep : CardinalCausalOrder rank
  identifiesParent :
    (Quotient.mk _ parentRep : UnlabeledCardinalCausalOrder rank) =
      currentUnlabeledCausalOrder rank pathPrefix
  precursor : CausalPastSet parentRep

def PhysicalCausalTransitionSlot.child
    (slot : PhysicalCausalTransitionSlot) : CausalSetGrowthBranch slot.rank :=
  causalTransitionTarget slot.parentRep slot.precursor

theorem PhysicalCausalTransitionSlot.physical
    (slot : PhysicalCausalTransitionSlot) :
    IsPhysicalCausalGrowthStep slot.rank slot.pathPrefix slot.child := by
  unfold IsPhysicalCausalGrowthStep PhysicalCausalTransitionSlot.child
  rw [← slot.identifiesParent]
  exact isUnlabeledOneElementExtension_mk
    (precursor_is_oneElementExtension slot.parentRep slot.precursor)

/-- Two simultaneous raw precursor alternatives from the same labeled parent
and the same unlabeled growth prefix. -/
structure PhysicalCausalAlternativePair where
  rank : ℕ
  pathPrefix : RankedGrowthPath CausalSetGrowthBranch rank
  parentRep : CardinalCausalOrder rank
  identifiesParent :
    (Quotient.mk _ parentRep : UnlabeledCardinalCausalOrder rank) =
      currentUnlabeledCausalOrder rank pathPrefix
  firstPrecursor : CausalPastSet parentRep
  secondPrecursor : CausalPastSet parentRep

def PhysicalCausalAlternativePair.firstSlot
    (pair : PhysicalCausalAlternativePair) : PhysicalCausalTransitionSlot :=
  ⟨pair.rank, pair.pathPrefix, pair.parentRep, pair.identifiesParent,
    pair.firstPrecursor⟩

def PhysicalCausalAlternativePair.secondSlot
    (pair : PhysicalCausalAlternativePair) : PhysicalCausalTransitionSlot :=
  ⟨pair.rank, pair.pathPrefix, pair.parentRep, pair.identifiesParent,
    pair.secondPrecursor⟩

def PhysicalCausalAlternativePair.firstChild
    (pair : PhysicalCausalAlternativePair) : CausalSetGrowthBranch pair.rank :=
  pair.firstSlot.child

def PhysicalCausalAlternativePair.secondChild
    (pair : PhysicalCausalAlternativePair) : CausalSetGrowthBranch pair.rank :=
  pair.secondSlot.child

/-- An amplitude on raw, precursor-resolved transition slots. -/
abbrev ComplexCausalTransitionSlotAmplitude :=
  PhysicalCausalTransitionSlot → ℂ

/-- A child-state weight is the special case that is constant across every
precursor fiber landing at the same unlabeled child. -/
def childStateTransitionSlotAmplitude
    (weights : UnlabeledComplexCausalGrowthWeights) :
    ComplexCausalTransitionSlotAmplitude :=
  fun slot => weights.weight slot.rank slot.pathPrefix slot.child

/-- Generic compatibility interface for alternative spectator-reduction
relations.  `KFCausalSetBellCausality` supplies the canonical union reduction
directly at the precursor-edge level. -/
abbrev BellSpectatorReductionRelation :=
  PhysicalCausalAlternativePair → PhysicalCausalAlternativePair → Prop

/-- Division-free equality of two complex transition ratios.  Cross
multiplication remains meaningful when one or more amplitudes vanish. -/
def ZeroSafeComplexBellRatio
    (fullFirst fullSecond reducedFirst reducedSecond : ℂ) : Prop :=
  fullFirst * reducedSecond = fullSecond * reducedFirst

/-- Complex Bell causality relative to a certified spectator-reduction
relation.  The weights are evaluated before local partition normalization,
because their ratios are normalization-independent within a family. -/
def IsZeroSafeComplexBellCausal
    (amplitude : ComplexCausalTransitionSlotAmplitude)
    (isSpectatorReduction : BellSpectatorReductionRelation) : Prop :=
  ∀ full reduced,
    isSpectatorReduction full reduced →
      ZeroSafeComplexBellRatio
        (amplitude full.firstSlot)
        (amplitude full.secondSlot)
        (amplitude reduced.firstSlot)
        (amplitude reduced.secondSlot)

/-- Compatibility proposition connecting any slot-level Bell relation to the
balanced restriction.  The theorem below proves it unconditionally within the
current scalar-amplitude growth construction. -/
def BellCausalBalancedRestrictionSelectsEndpoint
    (weights : UnlabeledComplexCausalGrowthWeights)
    (isSpectatorReduction : BellSpectatorReductionRelation)
    (coarse : OrientationCylinderCoarseGraining) : Prop :=
  IsZeroSafeComplexBellCausal
      (childStateTransitionSlotAmplitude weights)
      isSpectatorReduction →
    coarse.IsBalanced (normalizedWeightedCausalSetGrowthLaw weights) →
      |inducedOrientationParameter
        (normalizedWeightedCausalSetGrowthLaw weights) coarse| = 1 / 2

/-- The previously open endpoint-selection proposition is now discharged for
every weighted causal-set growth law and every proposed spectator relation.
The Bell premise is logically unnecessary: scalar-amplitude purity already
forces the endpoint as soon as the two sectors are balanced. -/
theorem bellCausalBalancedRestrictionSelectsEndpoint
    (weights : UnlabeledComplexCausalGrowthWeights)
    (isSpectatorReduction : BellSpectatorReductionRelation)
    (coarse : OrientationCylinderCoarseGraining) :
    BellCausalBalancedRestrictionSelectsEndpoint
      weights isSpectatorReduction coarse := by
  intro _hBell hBalanced
  exact balanced_inducedOrientationParameter_endpoint
    (normalizedWeightedCausalSetGrowthLaw weights) coarse hBalanced

/-- Capstone: the causal restriction is a unique admissible `D_y`, and its
parameter is invariant under every finite projective refinement. -/
theorem causal_orientation_restriction_bridge
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    |inducedOrientationParameter law coarse| ≤ 1 / 2
      ∧ inducedOrientationKernel law coarse =
        balancedHistoryKernel (inducedOrientationParameter law coarse)
      ∧ (∀ steps, inducedOrientationParameter law (coarse.refineBy steps) =
          inducedOrientationParameter law coarse) := by
  exact ⟨(inducedOrientationKernel_eq_balancedHistoryKernel
      law coarse hBalanced).1,
    (inducedOrientationKernel_eq_balancedHistoryKernel
      law coarse hBalanced).2,
    inducedOrientationParameter_refineBy law coarse⟩

/-- Strengthened capstone.  Every balanced restriction of the projective
scalar-amplitude causal growth family is an exactly refinement-stable
orientation endpoint. -/
theorem causal_orientation_endpoint_promotion
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining)
    (hBalanced : coarse.IsBalanced law) :
    Matrix.det (inducedOrientationKernel law coarse) = 0
      ∧ |inducedOrientationParameter law coarse| = 1 / 2
      ∧ (inducedOrientationKernel law coarse = positiveOrientationProjector ∨
          inducedOrientationKernel law coarse = negativeOrientationProjector)
      ∧ (∀ steps, inducedOrientationParameter law (coarse.refineBy steps) =
          inducedOrientationParameter law coarse) := by
  exact ⟨inducedOrientationKernel_det_zero law coarse,
    balanced_inducedOrientationParameter_endpoint law coarse hBalanced,
    balanced_inducedOrientationKernel_is_endpoint law coarse hBalanced,
    inducedOrientationParameter_refineBy law coarse⟩

#print axioms inducedOrientationKernel_isAdmissibleBalanced
#print axioms inducedOrientationKernel_eq_balancedHistoryKernel
#print axioms inducedOrientationKernel_det_zero
#print axioms balanced_inducedOrientationParameter_endpoint
#print axioms inducedOrientationParameter_refineBy
#print axioms bellCausalBalancedRestrictionSelectsEndpoint
#print axioms causal_orientation_restriction_bridge
#print axioms causal_orientation_endpoint_promotion

end

end UnifiedTheory.Audit.KFCausalSetOrientationRestriction
