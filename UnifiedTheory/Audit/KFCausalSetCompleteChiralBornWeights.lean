/-
  Audit/KFCausalSetCompleteChiralBornWeights.lean

  STAGEWISE BORN WEIGHTS OF THE COMPLETE CHIRAL GROWTH LAW

  The complete chiral causal-set law is normalized coherently: its complex
  transition amplitudes sum to one.  That condition is not the same as Born
  normalization.  This module therefore does not claim that the original
  transitions already have squared moduli summing to one.

  Instead, at each finite parent, it divides the squared moduli by their
  strictly positive total Born mass.  The transition-fiber signature theorem
  supplies the key physical input: the complete chiral transition is nonzero
  exactly on physical one-element extensions.  Consequently the resulting
  real weights are nonnegative, sum to one, and have exactly the physical
  support.

  This closes the complex-law-to-normalized-stagewise-weight part of the
  microscopic adapter.  A further observation map is still needed to turn
  rank-dependent causal children into the fixed finite cell family used by
  the Hauptvermutung repair dynamics.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalTransitionFiberSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalTransitionFiberSignature

/-- Total squared-modulus mass of all complete-chiral transitions from one
finite causal parent.  It is not assumed to equal one. -/
def completeChiralStageBornMass
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) : ℝ :=
  ∑ child : CausalSetGrowthBranch n,
    Complex.normSq
      ((completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child)

/-- The stagewise Born weight obtained by normalizing the squared modulus of
one complete-chiral transition by the total squared-modulus mass. -/
def completeChiralStageBornWeight
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) : ℝ :=
  Complex.normSq
      ((completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child) /
    completeChiralStageBornMass chirality n pathPrefix

/-- Full physical transition support makes the stage Born mass strictly
positive at every parent. -/
theorem completeChiralStageBornMass_pos
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    0 < completeChiralStageBornMass chirality n pathPrefix := by
  classical
  obtain ⟨child, hChild⟩ :=
    physicalCausalSuccessors_nonempty n pathPrefix
  have hPhysical : IsPhysicalCausalGrowthStep n pathPrefix child := by
    simpa [physicalCausalSuccessors] using hChild
  have hTransition :
      (completeChiralCausalSetGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 :=
    completeChiralCausalSetGrowthLaw_transition_ne_zero_of_physical
      chirality n pathPrefix child hPhysical
  have hTerm :
      0 < Complex.normSq
        ((completeChiralCausalSetGrowthLaw chirality).transition
          n pathPrefix child) :=
    Complex.normSq_pos.mpr hTransition
  have hLe :
      Complex.normSq
          ((completeChiralCausalSetGrowthLaw chirality).transition
            n pathPrefix child) ≤
        completeChiralStageBornMass chirality n pathPrefix := by
    unfold completeChiralStageBornMass
    exact
      Finset.single_le_sum
        (fun other _ =>
          Complex.normSq_nonneg
            ((completeChiralCausalSetGrowthLaw chirality).transition
              n pathPrefix other))
        (Finset.mem_univ child)
  exact lt_of_lt_of_le hTerm hLe

/-- Every normalized complete-chiral stage weight is nonnegative. -/
theorem completeChiralStageBornWeight_nonneg
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    0 ≤ completeChiralStageBornWeight chirality n pathPrefix child := by
  exact div_nonneg (Complex.normSq_nonneg _)
    (le_of_lt (completeChiralStageBornMass_pos chirality n pathPrefix))

/-- The normalized squared-modulus weights sum to one at every finite
parent. -/
theorem completeChiralStageBornWeight_sum_one
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    (∑ child : CausalSetGrowthBranch n,
      completeChiralStageBornWeight chirality n pathPrefix child) = 1 := by
  classical
  unfold completeChiralStageBornWeight
  rw [← Finset.sum_div]
  change completeChiralStageBornMass chirality n pathPrefix /
      completeChiralStageBornMass chirality n pathPrefix = 1
  exact div_self
    (ne_of_gt (completeChiralStageBornMass_pos chirality n pathPrefix))

/-- A stage weight is strictly positive exactly on a physical one-element
extension. -/
theorem completeChiralStageBornWeight_pos_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    0 < completeChiralStageBornWeight chirality n pathPrefix child ↔
      IsPhysicalCausalGrowthStep n pathPrefix child := by
  constructor
  · intro hWeight
    have hTransition :
        (completeChiralCausalSetGrowthLaw chirality).transition
            n pathPrefix child ≠ 0 := by
      intro hZero
      simp [completeChiralStageBornWeight, hZero] at hWeight
    exact
      (completeChiralCausalSetGrowthLaw_transition_ne_zero_iff_physical
        chirality n pathPrefix child).mp hTransition
  · intro hPhysical
    exact div_pos
      (Complex.normSq_pos.mpr
        (completeChiralCausalSetGrowthLaw_transition_ne_zero_of_physical
          chirality n pathPrefix child hPhysical))
      (completeChiralStageBornMass_pos chirality n pathPrefix)

/-- Nonphysical children have exactly zero stagewise Born weight. -/
theorem completeChiralStageBornWeight_eq_zero_of_not_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    completeChiralStageBornWeight chirality n pathPrefix child = 0 := by
  have hTransition :
      (completeChiralCausalSetGrowthLaw chirality).transition
          n pathPrefix child = 0 :=
    completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
      chirality n pathPrefix child hNotPhysical
  simp [completeChiralStageBornWeight, hTransition]

/-- One reusable package for the normalized real weights derived from the
complete chiral complex law at a finite parent. -/
structure CompleteChiralStageBornWeights
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) : Prop where
  nonnegative :
    ∀ child, 0 ≤ completeChiralStageBornWeight chirality n pathPrefix child
  normalized :
    (∑ child : CausalSetGrowthBranch n,
      completeChiralStageBornWeight chirality n pathPrefix child) = 1
  exactPhysicalSupport :
    ∀ child,
      0 < completeChiralStageBornWeight chirality n pathPrefix child ↔
        IsPhysicalCausalGrowthStep n pathPrefix child

/-- The complete chiral law canonically supplies normalized real weights at
every finite parent. -/
theorem completeChiralStageBornWeights_closed
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    CompleteChiralStageBornWeights chirality n pathPrefix := by
  exact
    ⟨completeChiralStageBornWeight_nonneg chirality n pathPrefix,
      completeChiralStageBornWeight_sum_one chirality n pathPrefix,
      completeChiralStageBornWeight_pos_iff_physical chirality n pathPrefix⟩

/-! ## Pushforward to a fixed finite observation family -/

/-- Push the rank-dependent child weights forward along any finite observation
map.  The codomain `ι` is fixed across ranks, matching the type of the local
cell family consumed by the Hauptvermutung repair interfaces. -/
noncomputable def completeChiralObservedBornWeight
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) (i : ι) : ℝ := by
  classical
  exact
    ∑ child : CausalSetGrowthBranch n,
      if observe n child = i then
        completeChiralStageBornWeight chirality n (parentSchedule n) child
      else 0

/-- Pushforward weights remain nonnegative. -/
theorem completeChiralObservedBornWeight_nonneg
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ∀ n i,
      0 ≤ completeChiralObservedBornWeight
        chirality parentSchedule observe n i := by
  classical
  intro n i
  unfold completeChiralObservedBornWeight
  apply Finset.sum_nonneg
  intro child _
  split
  · exact completeChiralStageBornWeight_nonneg
      chirality n (parentSchedule n) child
  · exact le_rfl

/-- Pushforward along a total observation map preserves total probability. -/
theorem completeChiralObservedBornWeight_sum_one
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) :
    (∑ i : ι,
      completeChiralObservedBornWeight
        chirality parentSchedule observe n i) = 1 := by
  classical
  unfold completeChiralObservedBornWeight
  calc
    (∑ i : ι, ∑ child : CausalSetGrowthBranch n,
        if observe n child = i then
          completeChiralStageBornWeight
            chirality n (parentSchedule n) child
        else 0) =
      ∑ child : CausalSetGrowthBranch n, ∑ i : ι,
        if observe n child = i then
          completeChiralStageBornWeight
            chirality n (parentSchedule n) child
        else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ child : CausalSetGrowthBranch n,
        completeChiralStageBornWeight
          chirality n (parentSchedule n) child := by
          apply Finset.sum_congr rfl
          intro child _
          simp
    _ = 1 :=
      completeChiralStageBornWeight_sum_one
        chirality n (parentSchedule n)

/-- Fixed-family normalized-weight package obtained from a complete-chiral
parent schedule and finite observation maps. -/
structure CompleteChiralObservedBornWeights
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) : Prop where
  nonnegative :
    ∀ n i,
      0 ≤ completeChiralObservedBornWeight
        chirality parentSchedule observe n i
  normalized :
    ∀ n,
      (∑ i : ι,
        completeChiralObservedBornWeight
          chirality parentSchedule observe n i) = 1

/-- The complex complete-chiral law supplies normalized real weights on every
chosen fixed finite observation family. -/
theorem completeChiralObservedBornWeights_closed
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    CompleteChiralObservedBornWeights
      chirality parentSchedule observe := by
  exact
    ⟨completeChiralObservedBornWeight_nonneg
        chirality parentSchedule observe,
      completeChiralObservedBornWeight_sum_one
        chirality parentSchedule observe⟩

#print axioms completeChiralStageBornMass_pos
#print axioms completeChiralStageBornWeight_sum_one
#print axioms completeChiralStageBornWeight_pos_iff_physical
#print axioms completeChiralStageBornWeights_closed
#print axioms completeChiralObservedBornWeight_sum_one
#print axioms completeChiralObservedBornWeights_closed

end

end UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
