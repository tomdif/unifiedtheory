/-
  Audit/KFCausalCSpecPhysicalChiralGrowthRealization.lean

  Conditional physical CSpec realization under the complete chiral growth law.

  `KFCausalCSpecPhysicalGrowthRealization` proves that the native 140-event
  full-S3 CSpec atlas is reachable by ordinary one-element causal growth, and
  that the uniform growth law assigns the displayed atlas path nonzero
  amplitude.  `KFCausalSetCompleteChiralLaw` supplies the stronger zero-free
  complete chiral dynamics.

  This file isolates the exact remaining bridge between those two facts:
  if the complete chiral law has no coherent aggregate cancellation on the 140
  concrete atlas births, then the same atlas path has nonzero complete-chiral
  path amplitude and realizes the determinant weak sector under the actual
  complete chiral law.

  The new hypothesis is finite and explicit: one nonzero normalized transition
  condition for each atlas birth.  This is not yet a proof that the microscopic
  dynamics supplies the Hauptvermutung convergence certificate.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
import UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry

/-- Prefix of the physical atlas path immediately before the `n -> n+1`
birth. -/
def atlasStepPrefix (n : ℕ) (hnext : n + 1 ≤ 140) :
    RankedGrowthPath CausalSetGrowthBranch n :=
  globalAtlasPhysicalGrowthPath n
    (Nat.le_trans (Nat.le_succ n) hnext)

/-- Child produced by the `n -> n+1` atlas birth. -/
def atlasStepChild (n : ℕ) (hnext : n + 1 ≤ 140) :
    CausalSetGrowthBranch n :=
  Quotient.mk _ (globalAtlasPhysicalPrefix (n + 1) hnext)

/-- The actual complete-chiral normalized transition assigned to the `n`th
atlas birth. -/
def atlasCompleteChiralTransition
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) : ℂ :=
  (completeChiralCausalSetGrowthLaw chirality).transition n
    (atlasStepPrefix n hnext) (atlasStepChild n hnext)

/-- The finite noncancellation gate needed to promote the already-physical
atlas path from the uniform law to the complete chiral law. -/
def CompleteChiralAtlasTransitionNonzero (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    atlasCompleteChiralTransition chirality n hnext ≠ 0

/-- Every atlas birth used in the noncancellation gate is already physically
admissible as a one-element causal growth step. -/
theorem atlasStep_isPhysical
    (n : ℕ) (hnext : n + 1 ≤ 140) :
    IsPhysicalCausalGrowthStep n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext) := by
  exact (globalAtlasPhysicalGrowthPath_isPhysical (n + 1) hnext).2

/-- Outside the physical one-element extension graph, the complete chiral law
assigns zero transition amplitude.  Thus `CompleteChiralAtlasTransitionNonzero`
is precisely a coherent-aggregate noncancellation condition on physical atlas
births, not an additional support/admissibility assumption. -/
theorem completeChiral_atlasStep_support_gate
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    IsPhysicalCausalGrowthStep n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext) ∧
    (¬ IsPhysicalCausalGrowthStep n
        (atlasStepPrefix n hnext) (atlasStepChild n hnext) →
      atlasCompleteChiralTransition chirality n hnext = 0) := by
  exact
    ⟨atlasStep_isPhysical n hnext,
      fun hNotPhysical =>
        UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw.completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
          chirality n (atlasStepPrefix n hnext)
          (atlasStepChild n hnext) hNotPhysical⟩

/-- If none of the 140 complete-chiral atlas transitions cancels after
unlabeled aggregation, every finite prefix of the atlas path has nonzero
complete-chiral path amplitude. -/
theorem globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
    (chirality : Fin 2)
    (hNonzero : CompleteChiralAtlasTransitionNonzero chirality) :
    ∀ (n : ℕ) (h : n ≤ 140),
      finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) n
          (globalAtlasPhysicalGrowthPath n h) ≠ 0
  | 0, _ => by simp [finiteRankedPathAmplitude]
  | n + 1, h => by
      change
        finiteRankedPathAmplitude
            (completeChiralCausalSetGrowthLaw chirality) n
            (atlasStepPrefix n h) *
          atlasCompleteChiralTransition chirality n h ≠ 0
      exact mul_ne_zero
        (globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
          chirality hNonzero n (Nat.le_trans (Nat.le_succ n) h))
        (hNonzero n h)

/-- Conditional complete-chiral physical CSpec realization theorem.

The only remaining input is the finite noncancellation gate
`CompleteChiralAtlasTransitionNonzero chirality`; all order-theoretic
physicality and determinant-sector data are inherited from the already proved
physical atlas realization. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_transition_nonzero
    (chirality : Fin 2)
    (hNonzero : CompleteChiralAtlasTransitionNonzero chirality) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    ⟨globalAtlasPhysicalGrowthPath_isPhysical 140 le_rfl,
      globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
        chirality hNonzero 140 le_rfl,
      ⟨globalAtlasPhysicalEndpointOrderIso⟩,
      globalAtlasPhysicalEndpoint_containsBooleanCubeSeed,
      cSpecOddLoopHistory_orientation,
      cSpecOddLoop_derives_rightWeakMirror⟩

#print axioms atlasStep_isPhysical
#print axioms completeChiral_atlasStep_support_gate
#print axioms globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_transition_nonzero

end

end UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
