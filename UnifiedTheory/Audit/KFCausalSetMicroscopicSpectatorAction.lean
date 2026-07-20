/-
  Audit/KFCausalSetMicroscopicSpectatorAction.lean

  A VACUUM-NORMALIZED MICROSCOPIC ACTION FOR HARMONIC CAUSAL GROWTH

  The harmonic refinement module isolated two inputs that were not yet
  microscopic: additive charge sourcing and the rank-two boundary charge.
  This module replaces both by one action law on actual unlabeled sequential
  growth histories.

  After the birth taking a history from depth n to depth n+1, assign a rational
  action density to each of the n+1 event slots. Discrete general covariance is
  represented by invariance under every permutation of those slots, and the
  local action is normalized to unit total weight. Permutation transitivity
  derives exchangeability. The contribution of the birth is the density in the
  newborn slot; covariance makes this distinguished-slot evaluation independent
  of labeling, while normalization forces it to be

      1 / (n+1).

  The finite action is the sum of these local contributions from the empty
  causet. Consequently it is path independent and equals H_n on every depth-n
  history. In particular Q_0=0 and Q_2=H_2=3/2 are theorems, not boundary
  conditions. Reconstructing the pair coupling gives exactly the previously
  proved zero-free harmonic law.

  The remaining honest physical assumption is now a single one: the
  microscopic causal action has relabeling-invariant, unit-normalized event-slot
  density. This file proves all consequences of that law; it does not claim
  that the law follows from the Benincasa-Dowker action or continuum GR.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicRefinementLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction

noncomputable section

open scoped BigOperators ComplexConjugate
open Filter Topology
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetHarmonicRefinementLaw

/-! ## 1. The microscopic event-slot action -/

/-- Literal invariance of a finite event-slot source under every relabeling. -/
def IsEventSlotRelabelingInvariant {n : ℕ} (source : Fin n → ℚ) : Prop :=
  ∀ (relabeling : Equiv.Perm (Fin n)) (i : Fin n),
    source (relabeling i) = source i

/-- Permutation covariance implies exchangeability because the symmetric group
acts transitively on event slots. -/
theorem eventSlotRelabelingInvariant_implies_exchangeable {n : ℕ}
    {source : Fin n → ℚ} (hInvariant : IsEventSlotRelabelingInvariant source)
    (i j : Fin n) : source i = source j := by
  simpa only [Equiv.swap_apply_left] using
    (hInvariant (Equiv.swap i j) i).symm

/-- A local action density on each unlabeled sequential-growth history.

At a birth from depth `n` to `n+1`, the completed path supplies the causal
geometry and `Fin (n+1)` indexes the event slots after the birth. The source may
a priori depend on the whole history. Permutation invariance is the microscopic
general-covariance law; normalization fixes one unit of total local action. -/
@[ext]
structure VacuumSpectatorCausalAction where
  source : ∀ n : ℕ,
    RankedGrowthPath CausalSetGrowthBranch (n + 1) → Fin (n + 1) → ℚ
  relabelingInvariant : ∀ (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch (n + 1)),
    IsEventSlotRelabelingInvariant (source n path)
  normalized : ∀ (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch (n + 1)),
    ∑ i, source n path i = 1

/-- Every microscopic source is forced pointwise to the uniform density. This
also proves that any path dependence present in the structure is erased by the
two physical laws. -/
theorem source_eq_uniform (action : VacuumSpectatorCausalAction)
    (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch (n + 1))
    (i : Fin (n + 1)) :
    action.source n path i = uniformSpectatorSourceQ (n + 1) := by
  apply exchangeable_normalized_spectator_source_unique (Nat.succ_pos n)
  exact ⟨eventSlotRelabelingInvariant_implies_exchangeable
      (action.relabelingInvariant n path),
    action.normalized n path⟩

/-- The action law is consistent: the pointwise uniform source realizes it on
every unlabeled history. -/
def canonicalVacuumSpectatorCausalAction : VacuumSpectatorCausalAction where
  source := fun n _path _i => uniformSpectatorSourceQ (n + 1)
  relabelingInvariant := by
    intro n path
    unfold IsEventSlotRelabelingInvariant
    intros
    rfl
  normalized := by
    intro n path
    simp [uniformSpectatorSourceQ, div_eq_mul_inv]
    field_simp

/-- There is no hidden functional freedom in the action source. -/
theorem vacuumSpectatorCausalAction_unique
    (action : VacuumSpectatorCausalAction) :
    action = canonicalVacuumSpectatorCausalAction := by
  apply VacuumSpectatorCausalAction.ext
  funext n path i
  rw [source_eq_uniform]
  rfl

/-- The local birth contribution is evaluated in the newly born final slot.
The exchangeability theorem below proves that this does not introduce a label
choice into the value. -/
def birthActionDensityQ (action : VacuumSpectatorCausalAction) (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch (n + 1)) : ℚ :=
  action.source n path (Fin.last n)

theorem birthActionDensityQ_eq_uniform
    (action : VacuumSpectatorCausalAction) (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch (n + 1)) :
    birthActionDensityQ action n path =
      uniformSpectatorSourceQ (n + 1) :=
  source_eq_uniform action n path (Fin.last n)

/-- Any event slot gives the same local contribution as the newborn slot. -/
theorem birthActionDensityQ_label_independent
    (action : VacuumSpectatorCausalAction) (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch (n + 1))
    (i : Fin (n + 1)) :
    action.source n path i = birthActionDensityQ action n path := by
  exact eventSlotRelabelingInvariant_implies_exchangeable
    (action.relabelingInvariant n path) i (Fin.last n)

/-! ## 2. Vacuum-to-history action and the forced seed -/

/-- Sum the local action density along a finite growth history, beginning at
zero action on the empty causet. -/
def finiteSpectatorCausalActionQ (action : VacuumSpectatorCausalAction) :
    ∀ n : ℕ, RankedGrowthPath CausalSetGrowthBranch n → ℚ
  | 0, _path => 0
  | n + 1, path =>
      finiteSpectatorCausalActionQ action n path.1 +
        birthActionDensityQ action n path

@[simp]
theorem finiteSpectatorCausalActionQ_zero
    (action : VacuumSpectatorCausalAction)
    (path : RankedGrowthPath CausalSetGrowthBranch 0) :
    finiteSpectatorCausalActionQ action 0 path = 0 := rfl

@[simp]
theorem finiteSpectatorCausalActionQ_snoc
    (action : VacuumSpectatorCausalAction) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    finiteSpectatorCausalActionQ action (n + 1) (pathPrefix, child) =
      finiteSpectatorCausalActionQ action n pathPrefix +
        birthActionDensityQ action n (pathPrefix, child) := rfl

/-- Local microscopic equation of motion: adjoining one event adds exactly the
normalized rank density `1/(n+1)`. -/
theorem finiteSpectatorCausalActionQ_birth_increment
    (action : VacuumSpectatorCausalAction) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    finiteSpectatorCausalActionQ action (n + 1) (pathPrefix, child) =
      finiteSpectatorCausalActionQ action n pathPrefix +
        uniformSpectatorSourceQ (n + 1) := by
  rw [finiteSpectatorCausalActionQ_snoc,
    birthActionDensityQ_eq_uniform]

/-- The full discrete causal action is the harmonic number on every history.
Path independence is derived, not assumed. -/
theorem finiteSpectatorCausalActionQ_eq_harmonic
    (action : VacuumSpectatorCausalAction) :
  ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      finiteSpectatorCausalActionQ action n path = harmonic n
  | 0, path => by simp [harmonic]
  | n + 1, path => by
      rcases path with ⟨pathPrefix, child⟩
      rw [finiteSpectatorCausalActionQ_snoc,
        finiteSpectatorCausalActionQ_eq_harmonic action n pathPrefix,
        birthActionDensityQ_eq_uniform, harmonic_succ]
      simp [uniformSpectatorSourceQ, div_eq_mul_inv]

theorem finiteSpectatorCausalActionQ_path_independent
    (action : VacuumSpectatorCausalAction) (n : ℕ)
    (path₁ path₂ : RankedGrowthPath CausalSetGrowthBranch n) :
    finiteSpectatorCausalActionQ action n path₁ =
      finiteSpectatorCausalActionQ action n path₂ := by
  rw [finiteSpectatorCausalActionQ_eq_harmonic,
    finiteSpectatorCausalActionQ_eq_harmonic]

/-! ## 3. A canonical physical history and its rank charge -/

/-- Choose one genuine unlabeled one-element child of a physical prefix. The
choice is used only to expose a rank-indexed charge; path independence removes
it from every result. -/
def canonicalPhysicalChild (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    CausalSetGrowthBranch n :=
  Classical.choose (unlabeled_oneElementExtension_exists
    (currentUnlabeledCausalOrder n pathPrefix))

theorem canonicalPhysicalChild_isPhysical (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsPhysicalCausalGrowthStep n pathPrefix
      (canonicalPhysicalChild n pathPrefix) :=
  Classical.choose_spec (unlabeled_oneElementExtension_exists
    (currentUnlabeledCausalOrder n pathPrefix))

/-- A complete finite physical history obtained recursively from the empty
causet. -/
def canonicalPhysicalGrowthPath :
    ∀ n : ℕ, RankedGrowthPath CausalSetGrowthBranch n
  | 0 => PUnit.unit
  | n + 1 =>
      (canonicalPhysicalGrowthPath n,
        canonicalPhysicalChild n (canonicalPhysicalGrowthPath n))

theorem canonicalPhysicalGrowthPath_isPhysical : ∀ n : ℕ,
    IsPhysicalCausalGrowthPath n (canonicalPhysicalGrowthPath n)
  | 0 => trivial
  | n + 1 =>
      ⟨canonicalPhysicalGrowthPath_isPhysical n,
        canonicalPhysicalChild_isPhysical n (canonicalPhysicalGrowthPath n)⟩

/-- Rank charge read from a canonical physical history. -/
def microscopicCausalActionChargeQ
    (action : VacuumSpectatorCausalAction) (n : ℕ) : ℚ :=
  finiteSpectatorCausalActionQ action n (canonicalPhysicalGrowthPath n)

theorem microscopicCausalActionChargeQ_eq_harmonic
    (action : VacuumSpectatorCausalAction) :
    microscopicCausalActionChargeQ action = harmonic := by
  funext n
  exact finiteSpectatorCausalActionQ_eq_harmonic action n
    (canonicalPhysicalGrowthPath n)

theorem microscopicCausalActionChargeQ_vacuum
    (action : VacuumSpectatorCausalAction) :
    microscopicCausalActionChargeQ action 0 = 0 := by
  rw [microscopicCausalActionChargeQ_eq_harmonic]
  simp [harmonic]

/-- The former free boundary datum is fixed by growth from the vacuum. -/
theorem microscopicCausalActionChargeQ_rankTwo
    (action : VacuumSpectatorCausalAction) :
    microscopicCausalActionChargeQ action 2 = (3 : ℚ) / 2 := by
  rw [microscopicCausalActionChargeQ_eq_harmonic]
  norm_num [harmonic, Finset.sum_range_succ]

theorem microscopicCausalActionChargeQ_succ
    (action : VacuumSpectatorCausalAction) (n : ℕ) :
    microscopicCausalActionChargeQ action (n + 1) =
      microscopicCausalActionChargeQ action n +
        uniformSpectatorSourceQ (n + 1) := by
  rw [microscopicCausalActionChargeQ_eq_harmonic, harmonic_succ]
  simp [uniformSpectatorSourceQ, div_eq_mul_inv]

theorem microscopicCausalAction_isUniformSpectatorRefinementLaw
    (action : VacuumSpectatorCausalAction) :
    IsUniformSpectatorRefinementLaw
      (microscopicCausalActionChargeQ action) := by
  constructor
  · rw [microscopicCausalActionChargeQ_eq_harmonic,
      accumulatedUniformSpectatorSourceQ_eq_harmonic]
  · intro n hn
    exact microscopicCausalActionChargeQ_succ action n

/-! ## 4. Reconstruction of the physical coupling -/

def microscopicSpectatorPairCouplingQ
    (action : VacuumSpectatorCausalAction) : ℕ → ℚ :=
  pairCouplingFromChargeQ (microscopicCausalActionChargeQ action)

/-- The action-derived pair coupling is exactly the zero-free harmonic
critical coupling already used by the complete chiral growth law. -/
theorem microscopicSpectatorPairCouplingQ_eq_harmonic
    (action : VacuumSpectatorCausalAction) :
    microscopicSpectatorPairCouplingQ action =
      harmonicCriticalPairCouplingQ := by
  exact uniformSpectatorRefinementLaw_selects_harmonic
    (microscopicCausalAction_isUniformSpectatorRefinementLaw action)

def microscopicSpectatorPairCoupling
    (action : VacuumSpectatorCausalAction) (n : ℕ) : ℝ :=
  (microscopicSpectatorPairCouplingQ action n : ℝ)

theorem microscopicSpectatorPairCoupling_eq_harmonic
    (action : VacuumSpectatorCausalAction) :
    microscopicSpectatorPairCoupling action =
      harmonicCriticalPairCoupling := by
  funext n
  change (microscopicSpectatorPairCouplingQ action n : ℝ) =
    (harmonicCriticalPairCouplingQ n : ℝ)
  rw [microscopicSpectatorPairCouplingQ_eq_harmonic]

/-! ## 5. The action-selected chiral growth law -/

/-- The action-derived coupling avoids the partition zero of every finite
parent in either chirality. -/
theorem microscopicSpectator_interactingChiral_partition_ne_zero
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (microscopicSpectatorPairCoupling action n) chirality) parent ≠ 0 := by
  rw [microscopicSpectatorPairCoupling_eq_harmonic]
  exact harmonicCritical_interactingChiral_partition_ne_zero
    chirality parent

theorem microscopicSpectator_unlabeled_partition_ne_zero
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    {n : ℕ} (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (microscopicSpectatorPairCoupling action n) chirality) parent ≠ 0 := by
  rw [microscopicSpectatorPairCoupling_eq_harmonic]
  exact harmonicCritical_unlabeled_partition_ne_zero chirality parent

/-- Normalize the complete chiral transition edge with the coupling generated
by the microscopic action. -/
def microscopicSpectatorTransition
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  unlabeledAggregatedCausalEdgeAmplitude
      (interactingChiralCausalEdgeAmplitude
        (microscopicSpectatorPairCoupling action n) chirality) parent child /
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (microscopicSpectatorPairCoupling action n) chirality) parent

theorem microscopicSpectatorTransition_eq_harmonic
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    microscopicSpectatorTransition action chirality parent child =
      harmonicCriticalTransition chirality parent child := by
  unfold microscopicSpectatorTransition harmonicCriticalTransition
  rw [microscopicSpectatorPairCoupling_eq_harmonic]

theorem microscopicSpectatorTransition_sum_one
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      microscopicSpectatorTransition action chirality parent child = 1 := by
  classical
  simp_rw [microscopicSpectatorTransition_eq_harmonic]
  exact harmonicCriticalTransition_sum_one chirality parent

/-- Actual normalized sequential-growth law selected by the microscopic
action, on the complete unlabeled one-element extension graph. -/
def microscopicSpectatorCausalSetGrowthLaw
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    microscopicSpectatorTransition action chirality
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun _n pathPrefix =>
    microscopicSpectatorTransition_sum_one action chirality
      (currentUnlabeledCausalOrder _ pathPrefix)

theorem microscopicSpectatorGrowth_projective_stronglyPositive
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                (microscopicSpectatorCausalSetGrowthLaw action chirality)
                (n + 1))
              (refineRankedGrowthEvent event₁)
              (refineRankedGrowthEvent event₂) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                (microscopicSpectatorCausalSetGrowthLaw action chirality) n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (microscopicSpectatorCausalSetGrowthLaw action chirality))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (microscopicSpectatorCausalSetGrowthLaw action chirality))
      ∧ infiniteRankedCylinderDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 :=
  normalized_stronglyPositive_infiniteRankedCylinder_family
    (microscopicSpectatorCausalSetGrowthLaw action chirality)

/-! ## 6. Infrared observable and complete promotion -/

/-- Coherently aggregated one-missing/timid ratio predicted directly by the
action-derived pair coupling. -/
def microscopicSpectatorBornRatio
    (action : VacuumSpectatorCausalAction) : ℕ → ℝ :=
  coherentPairBornRatio (microscopicSpectatorPairCoupling action)

theorem microscopicSpectatorBornRatio_eq_harmonic
    (action : VacuumSpectatorCausalAction) :
    microscopicSpectatorBornRatio action = harmonicCriticalBornRatio := by
  funext n
  rw [microscopicSpectatorBornRatio,
    microscopicSpectatorPairCoupling_eq_harmonic]
  simp only [coherentPairBornRatio, harmonicCriticalBornRatio,
    harmonicCriticalEffectiveCoupling]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

theorem microscopicSpectatorPairCoupling_tendsto_one
    (action : VacuumSpectatorCausalAction) :
    Tendsto (microscopicSpectatorPairCoupling action) atTop (nhds 1) := by
  rw [microscopicSpectatorPairCoupling_eq_harmonic]
  exact harmonicCriticalPairCoupling_tendsto_one

theorem microscopicSpectatorBornRatio_tendsto
    (action : VacuumSpectatorCausalAction) :
    Tendsto (microscopicSpectatorBornRatio action) atTop
      (nhds (Real.exp (-2 * Real.eulerMascheroniConstant))) := by
  rw [microscopicSpectatorBornRatio_eq_harmonic]
  exact harmonicCriticalBornRatio_tendsto

/-- Capstone: a single local action law on histories fixes the rank-two seed,
derives the unique harmonic coupling, avoids every finite partition zero, and
promotes to a normalized projective strongly-positive infinite-cylinder
quantum dynamics with the exact coherent infrared constant. -/
theorem microscopicSpectatorAction_completeLaw
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    action = canonicalVacuumSpectatorCausalAction
      ∧ microscopicCausalActionChargeQ action 0 = 0
      ∧ microscopicCausalActionChargeQ action 2 = (3 : ℚ) / 2
      ∧ microscopicSpectatorPairCouplingQ action =
          harmonicCriticalPairCouplingQ
      ∧ (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
          causalEdgeAmplitudePartition
            (interactingChiralCausalEdgeAmplitude
              (microscopicSpectatorPairCoupling action n) chirality)
            parent ≠ 0)
      ∧ Tendsto (microscopicSpectatorPairCoupling action) atTop (nhds 1)
      ∧ Tendsto (microscopicSpectatorBornRatio action) atTop
          (nhds (Real.exp (-2 * Real.eulerMascheroniConstant)))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (microscopicSpectatorCausalSetGrowthLaw action chirality)) := by
  exact ⟨vacuumSpectatorCausalAction_unique action,
    microscopicCausalActionChargeQ_vacuum action,
    microscopicCausalActionChargeQ_rankTwo action,
    microscopicSpectatorPairCouplingQ_eq_harmonic action,
    fun _n parent =>
      microscopicSpectator_interactingChiral_partition_ne_zero
        action chirality parent,
    microscopicSpectatorPairCoupling_tendsto_one action,
    microscopicSpectatorBornRatio_tendsto action,
    (microscopicSpectatorGrowth_projective_stronglyPositive
      action chirality).2.2.2.1⟩

#print axioms source_eq_uniform
#print axioms vacuumSpectatorCausalAction_unique
#print axioms finiteSpectatorCausalActionQ_eq_harmonic
#print axioms finiteSpectatorCausalActionQ_path_independent
#print axioms canonicalPhysicalGrowthPath_isPhysical
#print axioms microscopicCausalActionChargeQ_rankTwo
#print axioms microscopicCausalAction_isUniformSpectatorRefinementLaw
#print axioms microscopicSpectatorPairCouplingQ_eq_harmonic
#print axioms microscopicSpectator_interactingChiral_partition_ne_zero
#print axioms microscopicSpectatorTransition_sum_one
#print axioms microscopicSpectatorGrowth_projective_stronglyPositive
#print axioms microscopicSpectatorBornRatio_tendsto
#print axioms microscopicSpectatorAction_completeLaw

end

end UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
