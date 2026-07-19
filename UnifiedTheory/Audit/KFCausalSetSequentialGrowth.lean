/-
  Audit/KFCausalSetSequentialGrowth.lean

  PHYSICAL UNLABELED CAUSAL-SET SEQUENTIAL GROWTH

  The fixed finite branch alphabet used by the first infinite-cylinder theorem
  is too small for genuine causal-set growth: the set of possible children
  changes with the cardinality and causal order of the current stage.  This
  file removes that restriction.

  First, a rank-dependent finite-branching theorem constructs normalized,
  strongly positive, exactly projective decoherence functionals and descends
  them to the quotient of infinite cylinder presentations.  Second, finite
  causal orders of each cardinality are quotiented by genuine order
  isomorphism.  The physical transition relation says that the child is
  obtained by adjoining one new maximal element.  It is finite, nonempty, and
  formulated entirely on isomorphism classes.

  A uniform transition amplitude gives an unconditional existence theorem for
  a normalized strongly positive decoherence functional supported on complete
  unlabeled causal-set growth trajectories.  This law is deliberately the
  real/classical baseline.  General complex covariant weights are normalized
  by their finite partition sum below; selecting a nontrivial physical phase
  remains dynamical input rather than a consequence of projectivity alone.
-/

import UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetSequentialGrowth

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence
open UnifiedTheory.LayerB.NoBackgroundSpace

universe u

/-! ## 1. Rank-dependent finite branching -/

/-- A rank-dependent path stores one branch at each rank below `n`.

The recursive product representation makes appending and deleting the final
branch definitional operations, while allowing the branch type to change at
every rank. -/
def RankedGrowthPath (Branch : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | Nat.succ n => RankedGrowthPath Branch n × Branch n

noncomputable instance rankedGrowthPathFintype
    {Branch : ℕ → Type*} [branchFinite : ∀ n, Fintype (Branch n)] :
    ∀ n, Fintype (RankedGrowthPath Branch n)
  | 0 => by
      simpa only [RankedGrowthPath] using (inferInstance : Fintype PUnit)
  | Nat.succ n => by
      letI : Fintype (RankedGrowthPath Branch n) :=
        rankedGrowthPathFintype n
      simpa only [RankedGrowthPath] using
        (inferInstance : Fintype (RankedGrowthPath Branch n × Branch n))

noncomputable instance rankedGrowthPathDecidableEq
    {Branch : ℕ → Type*} (n : ℕ) :
    DecidableEq (RankedGrowthPath Branch n) :=
  Classical.decEq _

/-- A state-dependent complex transition law on a rank-dependent finite tree.
Immediate transition amplitudes sum to one for every prefix. -/
structure RankedNormalizedComplexGrowthLaw
    (Branch : ℕ → Type*) [∀ n, Fintype (Branch n)] where
  transition : ∀ n : ℕ, RankedGrowthPath Branch n → Branch n → ℂ
  normalized : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
    ∑ branch, transition n pathPrefix branch = 1

/-- Append one ranked branch to a prefix. -/
def RankedGrowthPath.snoc {Branch : ℕ → Type*} {n : ℕ}
    (pathPrefix : RankedGrowthPath Branch n) (branch : Branch n) :
    RankedGrowthPath Branch (n + 1) :=
  (pathPrefix, branch)

/-- Refine a ranked event by every branch available at the next rank. -/
def refineRankedGrowthEvent {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)] {n : ℕ}
    (event : Finset (RankedGrowthPath Branch n)) :
    Finset (RankedGrowthPath Branch (n + 1)) :=
  event ×ˢ Finset.univ

theorem refineRankedGrowthEvent_univ {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)] (n : ℕ) :
    refineRankedGrowthEvent
        (Finset.univ : Finset (RankedGrowthPath Branch n)) =
      Finset.univ := by
  classical
  ext path
  rcases path with ⟨pathPrefix, branch⟩
  simp [refineRankedGrowthEvent]

/-- Product of transition amplitudes along a rank-dependent path. -/
def finiteRankedPathAmplitude {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    ∀ n : ℕ, RankedGrowthPath Branch n → ℂ
  | 0, _ => 1
  | n + 1, path =>
      finiteRankedPathAmplitude law n path.1 *
        law.transition n path.1 path.2

@[simp]
theorem finiteRankedPathAmplitude_zero {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch)
    (path : RankedGrowthPath Branch 0) :
    finiteRankedPathAmplitude law 0 path = 1 := rfl

@[simp]
theorem finiteRankedPathAmplitude_snoc {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (pathPrefix : RankedGrowthPath Branch n) (branch : Branch n) :
    finiteRankedPathAmplitude law (n + 1) (pathPrefix, branch) =
      finiteRankedPathAmplitude law n pathPrefix *
        law.transition n pathPrefix branch := rfl

/-- Summing all one-step continuations preserves the event amplitude. -/
theorem finiteRankedPathAmplitude_sum_refine {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    ∑ path ∈ refineRankedGrowthEvent event,
        finiteRankedPathAmplitude law (n + 1) path =
      ∑ pathPrefix ∈ event,
        finiteRankedPathAmplitude law n pathPrefix := by
  classical
  change ∑ path ∈ event ×ˢ (Finset.univ : Finset (Branch n)),
      finiteRankedPathAmplitude law n path.1 *
        law.transition n path.1 path.2 = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro pathPrefix _
  change ∑ branch, finiteRankedPathAmplitude law n pathPrefix *
      law.transition n pathPrefix branch =
    finiteRankedPathAmplitude law n pathPrefix
  rw [← Finset.mul_sum, law.normalized, mul_one]

/-- The total ranked path amplitude is one at every finite depth. -/
theorem finiteRankedPathAmplitude_sum_univ {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) : ∀ n : ℕ,
    ∑ path : RankedGrowthPath Branch n,
      finiteRankedPathAmplitude law n path = 1
  | 0 => by
      change ∑ _path : PUnit, (1 : ℂ) = 1
      simp
  | n + 1 => by
      classical
      rw [← refineRankedGrowthEvent_univ (Branch := Branch) n]
      rw [finiteRankedPathAmplitude_sum_refine]
      exact finiteRankedPathAmplitude_sum_univ law n

/-- Finite-depth decoherence kernel for the ranked tree. -/
def finiteRankedDepthDecoherence {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ) :
    GrowthDecoherenceFunctional (RankedGrowthPath Branch n) :=
  amplitudeDecoherence (finiteRankedPathAmplitude law n)

theorem finiteRankedDepthDecoherence_normalized
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsNormalizedGrowthFunctional (finiteRankedDepthDecoherence law n) := by
  unfold IsNormalizedGrowthFunctional
  change growthEventDecoherence (finiteRankedDepthDecoherence law n)
    Finset.univ Finset.univ = 1
  unfold finiteRankedDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq,
    finiteRankedPathAmplitude_sum_univ law n]
  simp

theorem finiteRankedDepthDecoherence_stronglyPositive
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsStronglyPositiveGrowthFunctional
      (growthEventDecoherence (finiteRankedDepthDecoherence law n)) := by
  exact amplitude_growthEventDecoherence_stronglyPositive _

/-- Exact one-step projective consistency for rank-dependent branching. -/
theorem finiteRankedDepthDecoherence_projective
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ : Finset (RankedGrowthPath Branch n)) :
    growthEventDecoherence (finiteRankedDepthDecoherence law (n + 1))
        (refineRankedGrowthEvent event₁) (refineRankedGrowthEvent event₂) =
      growthEventDecoherence (finiteRankedDepthDecoherence law n)
        event₁ event₂ := by
  unfold finiteRankedDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq,
    amplitude_growthEventDecoherence_eq,
    finiteRankedPathAmplitude_sum_refine,
    finiteRankedPathAmplitude_sum_refine]

/-- Refine a ranked event by any finite number of complete branching
layers. -/
def refineRankedGrowthEventBy {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)] {n : ℕ}
    (event : Finset (RankedGrowthPath Branch n)) :
    ∀ steps : ℕ, Finset (RankedGrowthPath Branch (n + steps))
  | 0 => event
  | steps + 1 => refineRankedGrowthEvent (refineRankedGrowthEventBy event steps)

/-- Exact projective consistency across every finite rank gap. -/
theorem finiteRankedDepthDecoherence_projective_by
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ : Finset (RankedGrowthPath Branch n)) :
    ∀ steps : ℕ,
      growthEventDecoherence
          (finiteRankedDepthDecoherence law (n + steps))
          (refineRankedGrowthEventBy event₁ steps)
          (refineRankedGrowthEventBy event₂ steps) =
        growthEventDecoherence (finiteRankedDepthDecoherence law n)
          event₁ event₂
  | 0 => rfl
  | steps + 1 => by
      change growthEventDecoherence
          (finiteRankedDepthDecoherence law ((n + steps) + 1))
          (refineRankedGrowthEvent
            (refineRankedGrowthEventBy event₁ steps))
          (refineRankedGrowthEvent
            (refineRankedGrowthEventBy event₂ steps)) = _
      rw [finiteRankedDepthDecoherence_projective law (n + steps)]
      exact finiteRankedDepthDecoherence_projective_by
        law n event₁ event₂ steps

/-! ## 2. Infinite ranked cylinder events -/

/-- A finite presentation of an event in the infinite ranked trajectory
space. -/
structure RankedCylinderPresentation (Branch : ℕ → Type*) where
  depth : ℕ
  event : Finset (RankedGrowthPath Branch depth)

def RankedCylinderPresentation.refine {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (cylinder : RankedCylinderPresentation Branch) :
    RankedCylinderPresentation Branch where
  depth := cylinder.depth + 1
  event := refineRankedGrowthEvent cylinder.event

def rankedCylinderRefinementRel {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (first second : RankedCylinderPresentation Branch) : Prop :=
  second = first.refine

/-- Infinite ranked cylinder events modulo finite refinement and inverse
refinement. -/
def InfiniteRankedCylinderEvent (Branch : ℕ → Type*)
    [∀ n, Fintype (Branch n)] :=
  Quotient (Relation.EqvGen.setoid
    (@rankedCylinderRefinementRel Branch _))

/-- A complete rank-dependent branch trajectory. -/
def InfiniteRankedGrowthTrajectory (Branch : ℕ → Type*) :=
  ∀ n : ℕ, Branch n

/-- The finite prefix of a complete ranked trajectory. -/
def rankedTrajectoryPrefix {Branch : ℕ → Type*}
    (trajectory : InfiniteRankedGrowthTrajectory Branch) :
    ∀ n : ℕ, RankedGrowthPath Branch n
  | 0 => PUnit.unit
  | n + 1 => (rankedTrajectoryPrefix trajectory n, trajectory n)

def RankedCylinderPresentation.Realizes {Branch : ℕ → Type*}
    (cylinder : RankedCylinderPresentation Branch)
    (trajectory : InfiniteRankedGrowthTrajectory Branch) : Prop :=
  rankedTrajectoryPrefix trajectory cylinder.depth ∈ cylinder.event

theorem RankedCylinderPresentation.realizes_refine_iff
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (cylinder : RankedCylinderPresentation Branch)
    (trajectory : InfiniteRankedGrowthTrajectory Branch) :
    cylinder.refine.Realizes trajectory ↔ cylinder.Realizes trajectory := by
  classical
  change
    (rankedTrajectoryPrefix trajectory cylinder.depth,
        trajectory cylinder.depth) ∈
        cylinder.event ×ˢ (Finset.univ : Finset (Branch cylinder.depth)) ↔
      rankedTrajectoryPrefix trajectory cylinder.depth ∈ cylinder.event
  rw [Finset.mem_product]
  simp

theorem RankedCylinderPresentation.realizes_iff_of_equivalent
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    {first second : RankedCylinderPresentation Branch}
    (hEquivalent : Relation.EqvGen rankedCylinderRefinementRel first second)
    (trajectory : InfiniteRankedGrowthTrajectory Branch) :
    first.Realizes trajectory ↔ second.Realizes trajectory := by
  induction hEquivalent with
  | rel first second hStep =>
      subst second
      exact (RankedCylinderPresentation.realizes_refine_iff
        first trajectory).symm
  | refl => rfl
  | symm first second _ ih => exact ih.symm
  | trans first second third _ _ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃

/-- Literal membership of a complete ranked trajectory in a quotient cylinder
event. -/
def InfiniteRankedCylinderEvent.Realizes {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (event : InfiniteRankedCylinderEvent Branch)
    (trajectory : InfiniteRankedGrowthTrajectory Branch) : Prop :=
  Quotient.lift
    (fun cylinder : RankedCylinderPresentation Branch =>
      cylinder.Realizes trajectory)
    (fun _ _ hEquivalent =>
      propext (RankedCylinderPresentation.realizes_iff_of_equivalent
        hEquivalent trajectory)) event

def rankedCylinderPresentationAmplitude {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch)
    (cylinder : RankedCylinderPresentation Branch) : ℂ :=
  ∑ path ∈ cylinder.event,
    finiteRankedPathAmplitude law cylinder.depth path

theorem rankedCylinderPresentationAmplitude_refine
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch)
    (cylinder : RankedCylinderPresentation Branch) :
    rankedCylinderPresentationAmplitude law cylinder.refine =
      rankedCylinderPresentationAmplitude law cylinder := by
  exact finiteRankedPathAmplitude_sum_refine law cylinder.depth cylinder.event

theorem rankedCylinderPresentationAmplitude_eq_of_equivalent
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch)
    {first second : RankedCylinderPresentation Branch}
    (hEquivalent : Relation.EqvGen rankedCylinderRefinementRel first second) :
    rankedCylinderPresentationAmplitude law first =
      rankedCylinderPresentationAmplitude law second := by
  induction hEquivalent with
  | rel first second hStep =>
      subst second
      exact (rankedCylinderPresentationAmplitude_refine law first).symm
  | refl => rfl
  | symm first second _ ih => exact ih.symm
  | trans first second third _ _ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃

def infiniteRankedCylinderAmplitude {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    InfiniteRankedCylinderEvent Branch → ℂ :=
  Quotient.lift (rankedCylinderPresentationAmplitude law)
    (fun _ _ hEquivalent =>
      rankedCylinderPresentationAmplitude_eq_of_equivalent law hEquivalent)

def infiniteRankedCylinderDecoherence {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    GrowthDecoherenceFunctional (InfiniteRankedCylinderEvent Branch) :=
  amplitudeDecoherence (infiniteRankedCylinderAmplitude law)

def totalInfiniteRankedCylinderEvent (Branch : ℕ → Type*)
    [∀ n, Fintype (Branch n)] : InfiniteRankedCylinderEvent Branch :=
  Quotient.mk _
    ({ depth := 0
       event := Finset.univ } : RankedCylinderPresentation Branch)

theorem infiniteRankedCylinderAmplitude_total
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    infiniteRankedCylinderAmplitude law
        (totalInfiniteRankedCylinderEvent Branch) = 1 := by
  change ∑ path : RankedGrowthPath Branch 0,
      finiteRankedPathAmplitude law 0 path = 1
  exact finiteRankedPathAmplitude_sum_univ law 0

theorem infiniteRankedCylinderDecoherence_normalized
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    infiniteRankedCylinderDecoherence law
        (totalInfiniteRankedCylinderEvent Branch)
        (totalInfiniteRankedCylinderEvent Branch) = 1 := by
  simp [infiniteRankedCylinderDecoherence, amplitudeDecoherence,
    infiniteRankedCylinderAmplitude_total law]

theorem infiniteRankedCylinderDecoherence_hermitian
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    IsHermitianGrowthFunctional
      (infiniteRankedCylinderDecoherence law) := by
  exact amplitudeDecoherence_hermitian _

theorem infiniteRankedCylinderDecoherence_stronglyPositive
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence law) := by
  exact amplitudeDecoherence_stronglyPositive _

/-- The infinite functional restricts exactly to the finite event functional
at every rank. -/
theorem infiniteRankedCylinderDecoherence_restricts_finite
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ : Finset (RankedGrowthPath Branch n)) :
    infiniteRankedCylinderDecoherence law
        (Quotient.mk _
          ({ depth := n, event := event₁ } :
            RankedCylinderPresentation Branch))
        (Quotient.mk _
          ({ depth := n, event := event₂ } :
            RankedCylinderPresentation Branch)) =
      growthEventDecoherence (finiteRankedDepthDecoherence law n)
        event₁ event₂ := by
  unfold infiniteRankedCylinderDecoherence infiniteRankedCylinderAmplitude
    rankedCylinderPresentationAmplitude finiteRankedDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq]
  rfl

/-- Canonical quotient event represented at rank `n`. -/
def finiteRankedCylinderEvent {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)] (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    InfiniteRankedCylinderEvent Branch :=
  Quotient.mk _
    ({ depth := n, event := event } : RankedCylinderPresentation Branch)

theorem finiteRankedCylinderEvent_refine_eq
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)] (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    finiteRankedCylinderEvent (n + 1) (refineRankedGrowthEvent event) =
      finiteRankedCylinderEvent n event := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ rfl)

/-- Finite additivity in the first event slot for disjoint same-rank cylinder
presentations. -/
theorem infiniteRankedCylinderDecoherence_union_left_sameRank
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ event₃ : Finset (RankedGrowthPath Branch n))
    (hDisjoint : Disjoint event₁ event₂) :
    infiniteRankedCylinderDecoherence law
        (finiteRankedCylinderEvent n (event₁ ∪ event₂))
        (finiteRankedCylinderEvent n event₃) =
      infiniteRankedCylinderDecoherence law
          (finiteRankedCylinderEvent n event₁)
          (finiteRankedCylinderEvent n event₃) +
        infiniteRankedCylinderDecoherence law
          (finiteRankedCylinderEvent n event₂)
          (finiteRankedCylinderEvent n event₃) := by
  unfold finiteRankedCylinderEvent
  rw [infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite]
  exact growthEventDecoherence_union_left _ _ _ _ hDisjoint

/-- Finite additivity in the second event slot. -/
theorem infiniteRankedCylinderDecoherence_union_right_sameRank
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ event₃ : Finset (RankedGrowthPath Branch n))
    (hDisjoint : Disjoint event₂ event₃) :
    infiniteRankedCylinderDecoherence law
        (finiteRankedCylinderEvent n event₁)
        (finiteRankedCylinderEvent n (event₂ ∪ event₃)) =
      infiniteRankedCylinderDecoherence law
          (finiteRankedCylinderEvent n event₁)
          (finiteRankedCylinderEvent n event₂) +
        infiniteRankedCylinderDecoherence law
          (finiteRankedCylinderEvent n event₁)
          (finiteRankedCylinderEvent n event₃) := by
  unfold finiteRankedCylinderEvent
  rw [infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite]
  exact growthEventDecoherence_union_right _ _ _ _ hDisjoint

/-- Diagonal quantum measure on ranked infinite-cylinder events. -/
def infiniteRankedCylinderQuantumMeasure {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch)
    (event : InfiniteRankedCylinderEvent Branch) : ℝ :=
  (infiniteRankedCylinderDecoherence law event event).re

theorem infiniteRankedCylinderQuantumMeasure_nonneg
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch)
    (event : InfiniteRankedCylinderEvent Branch) :
    0 ≤ infiniteRankedCylinderQuantumMeasure law event := by
  let amplitude : ℂ := infiniteRankedCylinderAmplitude law event
  change 0 ≤ (amplitude * star amplitude).re
  have hNorm : amplitude * star amplitude =
      ((Complex.normSq amplitude : ℝ) : ℂ) := by
    convert Complex.mul_conj amplitude using 1
  rw [hNorm]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg amplitude

/-- The ranked quantum measure has no irreducible third-order interference on
pairwise-disjoint same-rank cylinders. -/
theorem infiniteRankedCylinderQuantumMeasure_gradeTwo_sameRank
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ event₃ : Finset (RankedGrowthPath Branch n))
    (h₁₂ : Disjoint event₁ event₂)
    (h₁₃ : Disjoint event₁ event₃)
    (h₂₃ : Disjoint event₂ event₃) :
    infiniteRankedCylinderQuantumMeasure law
        (finiteRankedCylinderEvent n ((event₁ ∪ event₂) ∪ event₃)) =
      infiniteRankedCylinderQuantumMeasure law
          (finiteRankedCylinderEvent n (event₁ ∪ event₂)) +
        infiniteRankedCylinderQuantumMeasure law
          (finiteRankedCylinderEvent n (event₁ ∪ event₃)) +
        infiniteRankedCylinderQuantumMeasure law
          (finiteRankedCylinderEvent n (event₂ ∪ event₃)) -
        infiniteRankedCylinderQuantumMeasure law
          (finiteRankedCylinderEvent n event₁) -
        infiniteRankedCylinderQuantumMeasure law
          (finiteRankedCylinderEvent n event₂) -
        infiniteRankedCylinderQuantumMeasure law
          (finiteRankedCylinderEvent n event₃) := by
  unfold infiniteRankedCylinderQuantumMeasure finiteRankedCylinderEvent
  rw [infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite,
    infiniteRankedCylinderDecoherence_restricts_finite]
  exact amplitude_growthQuantumMeasure_gradeTwo
    (finiteRankedPathAmplitude law n) event₁ event₂ event₃ h₁₂ h₁₃ h₂₃

/-- Rank-dependent projective-limit capstone. -/
theorem normalized_stronglyPositive_infiniteRankedCylinder_family
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence law n))
      ∧ (∀ (n) (event₁ event₂ : Finset (RankedGrowthPath Branch n)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence law (n + 1))
              (refineRankedGrowthEvent event₁)
              (refineRankedGrowthEvent event₂) =
            growthEventDecoherence (finiteRankedDepthDecoherence law n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence law)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence law)
      ∧ infiniteRankedCylinderDecoherence law
          (totalInfiniteRankedCylinderEvent Branch)
          (totalInfiniteRankedCylinderEvent Branch) = 1 := by
  exact ⟨finiteRankedDepthDecoherence_normalized law,
    finiteRankedDepthDecoherence_projective law,
    infiniteRankedCylinderDecoherence_hermitian law,
    infiniteRankedCylinderDecoherence_stronglyPositive law,
    infiniteRankedCylinderDecoherence_normalized law⟩

/-! ## 3. Finite causal orders at fixed cardinality -/

/-- A finite causal order on exactly `n` events.  Unlike the older `FinPoset`
container, this fixed-cardinality version includes the empty order and is
therefore suitable for sequential growth from the empty causet. -/
structure CardinalCausalOrder (n : ℕ) where
  rel : Fin n → Fin n → Bool
  refl : ∀ i, rel i i = true
  antisymm : ∀ i j, rel i j = true → rel j i = true → i = j
  trans : ∀ i j k, rel i j = true → rel j k = true → rel i k = true

@[ext]
theorem CardinalCausalOrder.ext {n : ℕ} {P Q : CardinalCausalOrder n}
    (hRel : P.rel = Q.rel) : P = Q := by
  cases P
  cases Q
  cases hRel
  rfl

instance cardinalCausalOrderFinite (n : ℕ) :
    Finite (CardinalCausalOrder n) := by
  let encode : CardinalCausalOrder n → (Fin n → Fin n → Bool) :=
    CardinalCausalOrder.rel
  exact Finite.of_injective encode (fun _ _ h => CardinalCausalOrder.ext h)

noncomputable instance cardinalCausalOrderFintype (n : ℕ) :
    Fintype (CardinalCausalOrder n) :=
  Fintype.ofFinite _

noncomputable instance cardinalCausalOrderDecidableEq (n : ℕ) :
    DecidableEq (CardinalCausalOrder n) :=
  Classical.decEq _

/-- Genuine order isomorphism at a fixed cardinality. -/
def CardinalCausalOrderIsomorphic {n : ℕ}
    (P Q : CardinalCausalOrder n) : Prop :=
  ∃ equivalence : Equiv.Perm (Fin n),
    ∀ i j, P.rel i j = Q.rel (equivalence i) (equivalence j)

theorem cardinalCausalOrderIsomorphic_refl {n : ℕ}
    (P : CardinalCausalOrder n) : CardinalCausalOrderIsomorphic P P := by
  exact ⟨Equiv.refl _, fun _ _ => rfl⟩

theorem cardinalCausalOrderIsomorphic_symm {n : ℕ}
    {P Q : CardinalCausalOrder n}
    (h : CardinalCausalOrderIsomorphic P Q) :
    CardinalCausalOrderIsomorphic Q P := by
  obtain ⟨equivalence, hRel⟩ := h
  refine ⟨equivalence.symm, ?_⟩
  intro i j
  simpa using (hRel (equivalence.symm i) (equivalence.symm j)).symm

theorem cardinalCausalOrderIsomorphic_trans {n : ℕ}
    {P Q R : CardinalCausalOrder n}
    (hPQ : CardinalCausalOrderIsomorphic P Q)
    (hQR : CardinalCausalOrderIsomorphic Q R) :
    CardinalCausalOrderIsomorphic P R := by
  obtain ⟨equivalencePQ, hPQ⟩ := hPQ
  obtain ⟨equivalenceQR, hQR⟩ := hQR
  refine ⟨equivalencePQ.trans equivalenceQR, ?_⟩
  intro i j
  exact (hPQ i j).trans (hQR (equivalencePQ i) (equivalencePQ j))

instance cardinalCausalOrderSetoid (n : ℕ) :
    Setoid (CardinalCausalOrder n) where
  r := CardinalCausalOrderIsomorphic
  iseqv := {
    refl := cardinalCausalOrderIsomorphic_refl
    symm := cardinalCausalOrderIsomorphic_symm
    trans := cardinalCausalOrderIsomorphic_trans }

/-- An unlabeled causal set of exactly `n` elements. -/
abbrev UnlabeledCardinalCausalOrder (n : ℕ) :=
  Quotient (cardinalCausalOrderSetoid n)

noncomputable instance unlabeledCardinalCausalOrderFintype (n : ℕ) :
    Fintype (UnlabeledCardinalCausalOrder n) :=
  Fintype.ofFinite _

noncomputable instance unlabeledCardinalCausalOrderDecidableEq (n : ℕ) :
    DecidableEq (UnlabeledCardinalCausalOrder n) :=
  Classical.decEq _

theorem unlabeledCardinalOrder_eq_of_isomorphic {n : ℕ}
    {P Q : CardinalCausalOrder n}
    (h : CardinalCausalOrderIsomorphic P Q) :
    (Quotient.mk _ P : UnlabeledCardinalCausalOrder n) =
      Quotient.mk _ Q := by
  exact Quotient.sound h

/-- The empty causal order, the root of sequential growth. -/
def emptyCardinalCausalOrder : CardinalCausalOrder 0 where
  rel := fun i => Fin.elim0 i
  refl := fun i => Fin.elim0 i
  antisymm := fun i => Fin.elim0 i
  trans := fun i => Fin.elim0 i

def emptyUnlabeledCausalOrder : UnlabeledCardinalCausalOrder 0 :=
  Quotient.mk _ emptyCardinalCausalOrder

/-! ## 4. Physical one-element births -/

/-- Relation for adjoining one isolated maximal event.  This explicit child
is used only to prove that every finite causet has at least one successor. -/
def isolatedExtensionRel {n : ℕ} (P : CardinalCausalOrder n)
    (i j : Fin n ⊕ Fin 1) : Bool :=
  match i, j with
  | Sum.inl a, Sum.inl b => P.rel a b
  | Sum.inr _, Sum.inr _ => true
  | _, _ => false

/-- Adjoin a new isolated event in the final birth slot. -/
def isolatedOneElementExtension {n : ℕ}
    (P : CardinalCausalOrder n) : CardinalCausalOrder (n + 1) where
  rel := fun i j => isolatedExtensionRel P
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  refl := by
    intro i
    cases hi : finSumFinEquiv.symm i <;>
      simp [isolatedExtensionRel, P.refl]
  antisymm := by
    intro i j hij hji
    apply finSumFinEquiv.symm.injective
    cases hi : finSumFinEquiv.symm i with
    | inl a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            congr 1
            exact P.antisymm a b
              (by simpa [isolatedExtensionRel, hi, hj] using hij)
              (by simpa [isolatedExtensionRel, hi, hj] using hji)
        | inr b => simp [isolatedExtensionRel, hi, hj] at hij
    | inr a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b => simp [isolatedExtensionRel, hi, hj] at hij
        | inr b =>
            congr 1
            exact Subsingleton.elim a b
  trans := by
    intro i j k hij hjk
    cases hi : finSumFinEquiv.symm i with
    | inl a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c =>
                exact P.trans a b c
                  (by simpa [isolatedExtensionRel, hi, hj] using hij)
                  (by simpa [isolatedExtensionRel, hj, hk] using hjk)
            | inr c => simp [isolatedExtensionRel, hj, hk] at hjk
        | inr b => simp [isolatedExtensionRel, hi, hj] at hij
    | inr a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b => simp [isolatedExtensionRel, hi, hj] at hij
        | inr b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c => simp [isolatedExtensionRel, hj, hk] at hjk
            | inr c => simp [isolatedExtensionRel]

/-- A labeled child preserves the complete old order and has no relation from
the newly born final event into an old event.  Thus the new event is maximal;
its past may be any down-set allowed by transitivity. -/
def IsLabeledOneElementExtension {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : CardinalCausalOrder (n + 1)) : Prop :=
  (∀ i j : Fin n,
      child.rel i.castSucc j.castSucc = parent.rel i j)
    ∧ (∀ i : Fin n, child.rel (Fin.last n) i.castSucc = false)

theorem isolated_is_oneElementExtension {n : ℕ}
    (P : CardinalCausalOrder n) :
    IsLabeledOneElementExtension P (isolatedOneElementExtension P) := by
  constructor
  · intro i j
    simp [isolatedOneElementExtension, isolatedExtensionRel]
  · intro i
    simp [isolatedOneElementExtension, isolatedExtensionRel]

/-- The physical transition relation on unlabeled causal sets: some labeled
representatives realize the child by one maximal-element birth.  The
existential representative formulation makes label covariance intrinsic. -/
def IsUnlabeledOneElementExtension {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : Prop :=
  ∃ parentRep childRep,
    Quotient.mk _ parentRep = parent ∧
      Quotient.mk _ childRep = child ∧
      IsLabeledOneElementExtension parentRep childRep

theorem isUnlabeledOneElementExtension_mk {n : ℕ}
    {parent : CardinalCausalOrder n}
    {child : CardinalCausalOrder (n + 1)}
    (hExtension : IsLabeledOneElementExtension parent child) :
    IsUnlabeledOneElementExtension
      (Quotient.mk _ parent) (Quotient.mk _ child) := by
  exact ⟨parent, child, rfl, rfl, hExtension⟩

/-- Explicit representative independence of the physical birth relation.
Changing either labeled representative by an order isomorphism cannot change
the corresponding unlabeled transition. -/
theorem oneElementExtension_forgets_representatives {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    {child child' : CardinalCausalOrder (n + 1)}
    (hParent : CardinalCausalOrderIsomorphic parent parent')
    (hChild : CardinalCausalOrderIsomorphic child child')
    (hExtension : IsLabeledOneElementExtension parent child) :
    IsUnlabeledOneElementExtension
      (Quotient.mk _ parent') (Quotient.mk _ child') := by
  rw [← unlabeledCardinalOrder_eq_of_isomorphic hParent,
    ← unlabeledCardinalOrder_eq_of_isomorphic hChild]
  exact isUnlabeledOneElementExtension_mk hExtension

/-- Every unlabeled finite causal set has at least one physical child. -/
theorem unlabeled_oneElementExtension_exists {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∃ child : UnlabeledCardinalCausalOrder (n + 1),
      IsUnlabeledOneElementExtension parent child := by
  refine Quotient.inductionOn parent ?_
  intro parentRep
  refine ⟨Quotient.mk _ (isolatedOneElementExtension parentRep), ?_⟩
  exact isUnlabeledOneElementExtension_mk
    (isolated_is_oneElementExtension parentRep)

/-- The rank-`n` physical branch is an unlabeled causal order with `n+1`
events. -/
abbrev CausalSetGrowthBranch (n : ℕ) :=
  UnlabeledCardinalCausalOrder (n + 1)

/-- Current unlabeled causet carried by a path.  At depth zero it is the empty
root; afterward it is the final branch of the path. -/
def currentUnlabeledCausalOrder : ∀ n : ℕ,
    RankedGrowthPath CausalSetGrowthBranch n →
      UnlabeledCardinalCausalOrder n
  | 0, _ => emptyUnlabeledCausalOrder
  | _n + 1, path => path.2

/-- Physical admissibility of the next ranked branch. -/
def IsPhysicalCausalGrowthStep (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) : Prop :=
  IsUnlabeledOneElementExtension
    (currentUnlabeledCausalOrder n pathPrefix) child

/-- The finite set of every physical unlabeled child of a prefix. -/
def physicalCausalSuccessors (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    Finset (CausalSetGrowthBranch n) := by
  classical
  exact Finset.univ.filter (IsPhysicalCausalGrowthStep n pathPrefix)

theorem physicalCausalSuccessors_nonempty (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    (physicalCausalSuccessors n pathPrefix).Nonempty := by
  obtain ⟨child, hChild⟩ := unlabeled_oneElementExtension_exists
    (currentUnlabeledCausalOrder n pathPrefix)
  exact ⟨child, by
    simp [physicalCausalSuccessors, IsPhysicalCausalGrowthStep, hChild]⟩

theorem physicalCausalSuccessors_card_pos (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    0 < (physicalCausalSuccessors n pathPrefix).card :=
  Finset.card_pos.mpr (physicalCausalSuccessors_nonempty n pathPrefix)

/-! ## 5. An unconditional normalized physical growth law -/

/-- Equal amplitude on all admissible unlabeled one-element children and zero
amplitude off the physical transition graph. -/
def uniformCausalSetTransition (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) : ℂ :=
  if child ∈ physicalCausalSuccessors n pathPrefix then
    ((physicalCausalSuccessors n pathPrefix).card : ℂ)⁻¹
  else 0

theorem uniformCausalSetTransition_normalized (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ child, uniformCausalSetTransition n pathPrefix child = 1 := by
  classical
  let successors := physicalCausalSuccessors n pathPrefix
  have hCard : successors.card ≠ 0 :=
    Nat.ne_of_gt (physicalCausalSuccessors_card_pos n pathPrefix)
  change (∑ child, (if child ∈ successors then
      (successors.card : ℂ)⁻¹ else 0)) = 1
  rw [Finset.sum_ite]
  simp [hCard]

/-- Concrete normalized law on the actual unlabeled causal-set extension
graph. -/
def uniformUnlabeledCausalSetGrowthLaw :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := uniformCausalSetTransition
  normalized := uniformCausalSetTransition_normalized

theorem uniformCausalSetTransition_eq_zero_of_not_physical
    (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    uniformCausalSetTransition n pathPrefix child = 0 := by
  simp [uniformCausalSetTransition, physicalCausalSuccessors,
    hNotPhysical]

/-- A finite path is physical when every successive child is a genuine
one-element extension of its preceding unlabeled causet. -/
def IsPhysicalCausalGrowthPath : ∀ n : ℕ,
    RankedGrowthPath CausalSetGrowthBranch n → Prop
  | 0, _ => True
  | n + 1, path =>
      IsPhysicalCausalGrowthPath n path.1 ∧
        IsPhysicalCausalGrowthStep n path.1 path.2

/-- Every nonphysical finite history has exactly zero amplitude under the
uniform causal-set law. -/
theorem uniformCausalPathAmplitude_eq_zero_of_not_physical :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      ¬ IsPhysicalCausalGrowthPath n path →
        finiteRankedPathAmplitude uniformUnlabeledCausalSetGrowthLaw n path = 0
  | 0, path => by simp [IsPhysicalCausalGrowthPath]
  | n + 1, path => by
      intro hNotPhysical
      simp only [IsPhysicalCausalGrowthPath, not_and_or] at hNotPhysical
      rcases hNotPhysical with hEarlier | hStep
      · simp [finiteRankedPathAmplitude,
          uniformCausalPathAmplitude_eq_zero_of_not_physical n path.1 hEarlier]
      · simp [finiteRankedPathAmplitude,
          uniformUnlabeledCausalSetGrowthLaw,
          uniformCausalSetTransition_eq_zero_of_not_physical
            n path.1 path.2 hStep]

/-! ## 6. General complex covariant causal weights -/

/-- The remaining dynamical datum in its sharpest form.  A raw complex weight
is already a function of unlabeled paths and unlabeled children, must vanish
off the physical extension graph, and must have a nonzero finite partition
sum at every prefix. -/
structure UnlabeledComplexCausalGrowthWeights where
  weight : ∀ n : ℕ,
    RankedGrowthPath CausalSetGrowthBranch n →
      CausalSetGrowthBranch n → ℂ
  supported : ∀ (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n),
    ¬ IsPhysicalCausalGrowthStep n pathPrefix child →
      weight n pathPrefix child = 0
  partition_nonzero : ∀ (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
    (∑ child, weight n pathPrefix child) ≠ 0

def causalGrowthWeightPartition
    (weights : UnlabeledComplexCausalGrowthWeights) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) : ℂ :=
  ∑ child, weights.weight n pathPrefix child

/-- Normalize arbitrary physical complex weights by their finite local
partition sum. -/
def normalizedCausalGrowthTransition
    (weights : UnlabeledComplexCausalGrowthWeights) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) : ℂ :=
  weights.weight n pathPrefix child /
    causalGrowthWeightPartition weights n pathPrefix

theorem normalizedCausalGrowthTransition_sum
    (weights : UnlabeledComplexCausalGrowthWeights) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ child, normalizedCausalGrowthTransition weights n pathPrefix child =
      1 := by
  unfold normalizedCausalGrowthTransition causalGrowthWeightPartition
  rw [← Finset.sum_div]
  exact div_self (weights.partition_nonzero n pathPrefix)

def normalizedWeightedCausalSetGrowthLaw
    (weights : UnlabeledComplexCausalGrowthWeights) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := normalizedCausalGrowthTransition weights
  normalized := normalizedCausalGrowthTransition_sum weights

theorem normalizedCausalGrowthTransition_eq_zero_of_not_physical
    (weights : UnlabeledComplexCausalGrowthWeights) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    normalizedCausalGrowthTransition weights n pathPrefix child = 0 := by
  simp [normalizedCausalGrowthTransition,
    weights.supported n pathPrefix child hNotPhysical]

/-- Every admissible nonzero-partition complex causal dynamics automatically
inherits the all-depth projective and infinite strongly-positive theory. -/
theorem weighted_unlabeled_causalSet_infiniteCylinder_promotion
    (weights : UnlabeledComplexCausalGrowthWeights) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (normalizedWeightedCausalSetGrowthLaw weights) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          ∀ steps,
            growthEventDecoherence
                (finiteRankedDepthDecoherence
                  (normalizedWeightedCausalSetGrowthLaw weights)
                  (n + steps))
                (refineRankedGrowthEventBy event₁ steps)
                (refineRankedGrowthEventBy event₂ steps) =
              growthEventDecoherence
                (finiteRankedDepthDecoherence
                  (normalizedWeightedCausalSetGrowthLaw weights) n)
                event₁ event₂)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (normalizedWeightedCausalSetGrowthLaw weights))
      ∧ infiniteRankedCylinderDecoherence
          (normalizedWeightedCausalSetGrowthLaw weights)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 := by
  exact ⟨finiteRankedDepthDecoherence_normalized _,
    finiteRankedDepthDecoherence_projective_by _,
    infiniteRankedCylinderDecoherence_stronglyPositive _,
    infiniteRankedCylinderDecoherence_normalized _⟩

/-- Complete trajectories whose every prefix is a physical unlabeled causal
growth history. -/
def IsCompletePhysicalCausalGrowthTrajectory
    (trajectory : InfiniteRankedGrowthTrajectory CausalSetGrowthBranch) : Prop :=
  ∀ n, IsPhysicalCausalGrowthPath n (rankedTrajectoryPrefix trajectory n)

/-- **Physical sequential-growth promotion.**  Actual one-element unlabeled
causal-set extensions form a finite nonempty rank-dependent tree.  The uniform
law on that tree yields normalized strongly positive finite-depth kernels,
exact projective consistency, and a normalized strongly positive functional
on infinite cylinder histories; every nonphysical finite path has zero
amplitude. -/
theorem physical_unlabeled_causalSet_infiniteCylinder_promotion :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
        (physicalCausalSuccessors n pathPrefix).Nonempty)
      ∧ (∀ n, IsNormalizedGrowthFunctional
          (finiteRankedDepthDecoherence uniformUnlabeledCausalSetGrowthLaw n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          ∀ steps,
            growthEventDecoherence
                (finiteRankedDepthDecoherence
                  uniformUnlabeledCausalSetGrowthLaw (n + steps))
                (refineRankedGrowthEventBy event₁ steps)
                (refineRankedGrowthEventBy event₂ steps) =
              growthEventDecoherence
                (finiteRankedDepthDecoherence
                  uniformUnlabeledCausalSetGrowthLaw n) event₁ event₂)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            uniformUnlabeledCausalSetGrowthLaw)
      ∧ infiniteRankedCylinderDecoherence
          uniformUnlabeledCausalSetGrowthLaw
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1
      ∧ (∀ (n : ℕ)
            (path : RankedGrowthPath CausalSetGrowthBranch n),
          ¬ IsPhysicalCausalGrowthPath n path →
            finiteRankedPathAmplitude uniformUnlabeledCausalSetGrowthLaw
              n path = 0) := by
  exact ⟨physicalCausalSuccessors_nonempty,
    finiteRankedDepthDecoherence_normalized uniformUnlabeledCausalSetGrowthLaw,
    finiteRankedDepthDecoherence_projective_by
      uniformUnlabeledCausalSetGrowthLaw,
    infiniteRankedCylinderDecoherence_stronglyPositive
      uniformUnlabeledCausalSetGrowthLaw,
    infiniteRankedCylinderDecoherence_normalized
      uniformUnlabeledCausalSetGrowthLaw,
    uniformCausalPathAmplitude_eq_zero_of_not_physical⟩

#print axioms unlabeled_oneElementExtension_exists
#print axioms uniformCausalSetTransition_normalized
#print axioms weighted_unlabeled_causalSet_infiniteCylinder_promotion
#print axioms physical_unlabeled_causalSet_infiniteCylinder_promotion

end

end UnifiedTheory.Audit.KFCausalSetSequentialGrowth
