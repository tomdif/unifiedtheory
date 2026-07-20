/-
  Audit/KFCausalSetChiralityGenerationNoGo.lean

  NO PREFERRED CHIRALITY FROM A REFLECTION-FIXED VACUUM

  The complete harmonic sequential-growth law accepts a microscopic chirality
  argument.  It does not derive that argument from the vacuum-normalized
  spectator action.  This file proves that the missing derivation cannot be
  supplied while retaining all of the current reflection symmetry:

  * no reflection-equivariant selector can map a reflection-fixed input to the
    fixed-point-free two-element chirality space;
  * in particular, the parity-even vacuum spectator action cannot choose one
    absolute chirality;
  * the equal mixture of the reflected endpoint kernels is exactly `D_0`, so
    symmetric averaging erases rather than generates the sign.

  The complementary transport theorem is positive and exact.  The harmonic
  microscopic law agrees with the derived chiral law at the first branching
  depth.  Its two-sector cylinder kernel is therefore the pure endpoint chosen
  by the supplied nonzero relational chirality.  The induced sign

      Xi_cyl = -2 y

  remains unchanged under every finite projective refinement.  Thus transport
  is solved; generation from the present reflection-fixed vacuum is impossible.
  A preferred sign requires either a reflection-odd microscopic action term or
  an infinite-history symmetry-breaking boundary condition.
-/

import UnifiedTheory.Audit.KFCausalSetRelationalChiralitySelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo

noncomputable section

open scoped BigOperators ComplexConjugate
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetOrientationRestriction
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetRelationalChiralitySelection

/-! ## 1. Fixed-point obstruction to vacuum sign generation -/

/-- The two-element microscopic chirality reflection has no fixed point. -/
theorem microscopicChiralityReflection_ne_self (chirality : Fin 2) :
    reflectedMicroscopicChirality chirality ≠ chirality := by
  fin_cases chirality <;>
    norm_num [reflectedMicroscopicChirality]

/-- Abstract fixed-point obstruction: an equivariant map sends a fixed input to
a fixed output.  Since microscopic chirality reflection has no fixed point,
such a selector cannot exist. -/
theorem no_reflection_covariant_chirality_selector_from_fixed_input
    {Input : Type*} (reflection : Input → Input) (fixed : Input)
    (hFixed : reflection fixed = fixed) (select : Input → Fin 2)
    (hCovariant : ∀ input,
      select (reflection input) =
        reflectedMicroscopicChirality (select input)) : False := by
  have hSelectedFixed := hCovariant fixed
  rw [hFixed] at hSelectedFixed
  exact microscopicChiralityReflection_ne_self (select fixed)
    hSelectedFixed.symm

/-- The present spectator action has no reflection-odd field: reflection acts
trivially on it. -/
def vacuumSpectatorActionReflection
    (action : VacuumSpectatorCausalAction) : VacuumSpectatorCausalAction :=
  action

@[simp]
theorem vacuumSpectatorActionReflection_fixed
    (action : VacuumSpectatorCausalAction) :
    vacuumSpectatorActionReflection action = action := rfl

/-- **Finite-vacuum chirality-generation no-go.** No rule depending only on
the current parity-even vacuum spectator action can both choose a chirality and
transform covariantly under reflection. -/
theorem no_reflection_covariant_vacuum_chirality_selector
    (select : VacuumSpectatorCausalAction → Fin 2) :
    ¬(∀ action,
      select (vacuumSpectatorActionReflection action) =
        reflectedMicroscopicChirality (select action)) := by
  intro hCovariant
  exact no_reflection_covariant_chirality_selector_from_fixed_input
    vacuumSpectatorActionReflection canonicalVacuumSpectatorCausalAction
    (vacuumSpectatorActionReflection_fixed _)
    select hCovariant

/-- Equivalent one-point vacuum statement, independent of any implementation
of the spectator action. -/
theorem no_reflection_covariant_chirality_from_empty_vacuum
    (select : PUnit → Fin 2) :
    ¬(∀ vacuum,
      select vacuum = reflectedMicroscopicChirality (select vacuum)) := by
  intro hCovariant
  exact microscopicChiralityReflection_ne_self (select PUnit.unit)
    (hCovariant PUnit.unit).symm

/-! ## 2. Symmetric completion restores the mixed center, not a sign -/

/-- Equal classical mixing of the two reflected pure endpoints. -/
def reflectionSymmetricEndpointKernel : SquareMatrix 2 :=
  ((1 / 2 : ℝ) : ℂ) •
    (balancedHistoryKernel (1 / 2) +
      balancedHistoryKernel (-1 / 2))

theorem reflectionSymmetricEndpointKernel_eq_center :
    reflectionSymmetricEndpointKernel = balancedHistoryKernel 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [reflectionSymmetricEndpointKernel, balancedHistoryKernel,
      Fin.ext_iff]

theorem reflectionSymmetricEndpointKernel_parameter_zero :
    (reflectionSymmetricEndpointKernel 0 1).im = 0 := by
  rw [reflectionSymmetricEndpointKernel_eq_center]
  norm_num [balancedHistoryKernel, Fin.ext_iff]

/-- The symmetric completion is strongly positive but strictly mixed. -/
theorem reflectionSymmetricEndpointKernel_is_mixed :
    IsPathDensity reflectionSymmetricEndpointKernel
      ∧ Matrix.det reflectionSymmetricEndpointKernel = 1 / 4
      ∧ ¬IsScalarAmplitudeKernel reflectionSymmetricEndpointKernel := by
  rw [reflectionSymmetricEndpointKernel_eq_center]
  constructor
  · exact balancedHistoryKernel_isPathDensity (y := 0) (by norm_num)
  · constructor
    · rw [balancedHistoryKernel_det]
      norm_num
    · exact strictInterior_not_scalarAmplitudeKernel (by norm_num)

/-! ## 3. The harmonic law recovers the supplied endpoint at depth two -/

/-- The rank-one harmonic transition is independent of the pair coupling and
equals the elementary chiral transition. -/
theorem harmonicCritical_rankOne_transition_eq_chiral
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix child =
      (chiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child := by
  unfold harmonicCriticalCausalSetGrowthLaw
  change harmonicCriticalTransition chirality
      (currentUnlabeledCausalOrder 1 pathPrefix) child = _
  dsimp only [chiralCausalSetGrowthLaw, totalizedCausalEdgeGrowthLaw]
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  unfold harmonicCriticalTransition
  rw [unlabeledAggregatedCausalEdgeAmplitude_mk,
    unlabeledCausalEdgeAmplitudePartition_mk,
    interacting_rankOne_aggregate_eq_chiral
      (harmonicCriticalPairCoupling 1),
    interacting_rankOne_partition_eq_chiral
      (harmonicCriticalPairCoupling 1)]
  have hNonzero := chiral_rankOne_partition_ne_zero chirality
  simp [totalizedNormalizedCausalEdgeAmplitude, hNonzero]

theorem harmonicCritical_depthTwo_pathAmplitude_eq_chiral
    (chirality : Fin 2)
    (path : RankedGrowthPath CausalSetGrowthBranch 2) :
    finiteRankedPathAmplitude (harmonicCriticalCausalSetGrowthLaw chirality)
        2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path := by
  rcases path with ⟨pathPrefix, child⟩
  rw [finiteRankedPathAmplitude_snoc, finiteRankedPathAmplitude_snoc,
    causalGrowth_depthOne_path_amplitude_one,
    causalGrowth_depthOne_path_amplitude_one,
    one_mul, one_mul,
    harmonicCritical_rankOne_transition_eq_chiral]

/-- The action-derived microscopic law has the harmonic path amplitude at every
depth, not only at the first branch. -/
theorem microscopicSpectator_pathAmplitude_eq_harmonic
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      finiteRankedPathAmplitude
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n path =
        finiteRankedPathAmplitude
          (harmonicCriticalCausalSetGrowthLaw chirality) n path
  | 0, _path => rfl
  | n + 1, path => by
      rcases path with ⟨pathPrefix, child⟩
      rw [finiteRankedPathAmplitude_snoc,
        finiteRankedPathAmplitude_snoc,
        microscopicSpectator_pathAmplitude_eq_harmonic
          action chirality n pathPrefix]
      change _ * microscopicSpectatorTransition
          action chirality (currentUnlabeledCausalOrder n pathPrefix) child =
        _ * harmonicCriticalTransition
          chirality (currentUnlabeledCausalOrder n pathPrefix) child
      rw [microscopicSpectatorTransition_eq_harmonic]

theorem microscopicSpectator_depthTwo_pathAmplitude_eq_chiral
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (path : RankedGrowthPath CausalSetGrowthBranch 2) :
    finiteRankedPathAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action chirality) 2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path := by
  rw [microscopicSpectator_pathAmplitude_eq_harmonic,
    harmonicCritical_depthTwo_pathAmplitude_eq_chiral]

/-- The complete action-derived harmonic law induces the pure endpoint matching
its supplied microscopic chirality. -/
theorem microscopicSpectator_inducedOrientationKernel_exact
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    inducedOrientationKernel
        (microscopicSpectatorCausalSetGrowthLaw action chirality)
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel
        (chiralBoundaryOrientationParameter chirality) := by
  rw [← chiral_inducedOrientationKernel_exact chirality]
  ext first second
  unfold inducedOrientationKernel finiteRankedDepthDecoherence
  simp only [amplitude_growthEventDecoherence_eq]
  have hFirst :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector first,
          finiteRankedPathAmplitude
            (microscopicSpectatorCausalSetGrowthLaw action chirality)
            chiralRankTwoCoarseGraining.depth path) =
        ∑ path ∈ chiralRankTwoCoarseGraining.sector first,
          finiteRankedPathAmplitude
            (chiralCausalSetGrowthLaw chirality)
            chiralRankTwoCoarseGraining.depth path := by
    apply Finset.sum_congr rfl
    intro path _hPath
    exact microscopicSpectator_depthTwo_pathAmplitude_eq_chiral
      action chirality path
  have hSecond :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector second,
          finiteRankedPathAmplitude
            (microscopicSpectatorCausalSetGrowthLaw action chirality)
            chiralRankTwoCoarseGraining.depth path) =
        ∑ path ∈ chiralRankTwoCoarseGraining.sector second,
          finiteRankedPathAmplitude
            (chiralCausalSetGrowthLaw chirality)
            chiralRankTwoCoarseGraining.depth path := by
    apply Finset.sum_congr rfl
    intro path _hPath
    exact microscopicSpectator_depthTwo_pathAmplitude_eq_chiral
      action chirality path
  rw [hFirst, hSecond]

/-! ## 4. The cylinder sign is transported through every refinement -/

/-- Chirality sign read from an orientation cylinder kernel.  At a pure
endpoint this is `+1` for the positive relational witness and `-1` for its
reflection. -/
def inducedCylinderChiralitySign
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) : ℝ :=
  -2 * inducedOrientationParameter law coarse

theorem inducedCylinderChiralitySign_refineBy
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (coarse : OrientationCylinderCoarseGraining) (steps : ℕ) :
    inducedCylinderChiralitySign law (coarse.refineBy steps) =
      inducedCylinderChiralitySign law coarse := by
  unfold inducedCylinderChiralitySign
  rw [inducedOrientationParameter_refineBy]

theorem relationallySelected_inducedOrientationKernel_exact
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) :
    inducedOrientationKernel
        (relationallySelectedCausalSetGrowthLaw action data)
        chiralRankTwoCoarseGraining =
      relationallySelectedOrientationKernel data := by
  unfold relationallySelectedCausalSetGrowthLaw
    relationallySelectedOrientationKernel
    relationallySelectedOrientationParameter
  exact microscopicSpectator_inducedOrientationKernel_exact
    action (relationalChiralitySector data.chirality)

theorem relationallySelected_inducedOrientationParameter_exact
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) :
    inducedOrientationParameter
        (relationallySelectedCausalSetGrowthLaw action data)
        chiralRankTwoCoarseGraining =
      relationallySelectedOrientationParameter data := by
  unfold inducedOrientationParameter
  rw [relationallySelected_inducedOrientationKernel_exact]
  norm_num [relationallySelectedOrientationKernel,
    balancedHistoryKernel, Fin.ext_iff]

theorem relationallySelected_cylinderSign_of_pos
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hPositive : 0 < data.chirality) :
    inducedCylinderChiralitySign
        (relationallySelectedCausalSetGrowthLaw action data)
        chiralRankTwoCoarseGraining = 1 := by
  unfold inducedCylinderChiralitySign
  rw [relationallySelected_inducedOrientationParameter_exact,
    relationallySelectedOrientationParameter_of_pos hPositive]
  ring

theorem relationallySelected_cylinderSign_of_neg
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hNegative : data.chirality < 0) :
    inducedCylinderChiralitySign
        (relationallySelectedCausalSetGrowthLaw action data)
        chiralRankTwoCoarseGraining = -1 := by
  unfold inducedCylinderChiralitySign
  rw [relationallySelected_inducedOrientationParameter_exact,
    relationallySelectedOrientationParameter_of_neg hNegative]
  ring

/-- Exact all-rank transport of the sign supplied at the first branching
depth. -/
theorem relationallySelected_cylinderSign_transport
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (hNonzero : data.chirality ≠ 0) :
    ((0 < data.chirality ∧
        ∀ steps : ℕ,
          inducedCylinderChiralitySign
              (relationallySelectedCausalSetGrowthLaw action data)
              (chiralRankTwoCoarseGraining.refineBy steps) = 1)
      ∨ (data.chirality < 0 ∧
        ∀ steps : ℕ,
          inducedCylinderChiralitySign
              (relationallySelectedCausalSetGrowthLaw action data)
              (chiralRankTwoCoarseGraining.refineBy steps) = -1)) := by
  rcases lt_or_gt_of_ne hNonzero with hNegative | hPositive
  · exact Or.inr ⟨hNegative, fun steps => by
      rw [inducedCylinderChiralitySign_refineBy]
      exact relationallySelected_cylinderSign_of_neg action hNegative⟩
  · exact Or.inl ⟨hPositive, fun steps => by
      rw [inducedCylinderChiralitySign_refineBy]
      exact relationallySelected_cylinderSign_of_pos action hPositive⟩

/-- Final frontier theorem: refinement transports a supplied nonzero sign
exactly, but the present reflection-fixed vacuum action cannot generate a
preferred member of the pair. -/
theorem chirality_generation_and_transport_frontier :
    (∀ select : VacuumSpectatorCausalAction → Fin 2,
      ¬(∀ action,
        select (vacuumSpectatorActionReflection action) =
          reflectedMicroscopicChirality (select action)))
      ∧ (∀ (action : VacuumSpectatorCausalAction)
          (data : RelationalProfileTriple), data.chirality ≠ 0 →
        ((0 < data.chirality ∧
            ∀ steps : ℕ,
              inducedCylinderChiralitySign
                  (relationallySelectedCausalSetGrowthLaw action data)
                  (chiralRankTwoCoarseGraining.refineBy steps) = 1)
          ∨ (data.chirality < 0 ∧
            ∀ steps : ℕ,
              inducedCylinderChiralitySign
                  (relationallySelectedCausalSetGrowthLaw action data)
                  (chiralRankTwoCoarseGraining.refineBy steps) = -1))) := by
  exact ⟨no_reflection_covariant_vacuum_chirality_selector,
    relationallySelected_cylinderSign_transport⟩

#print axioms no_reflection_covariant_chirality_selector_from_fixed_input
#print axioms no_reflection_covariant_vacuum_chirality_selector
#print axioms reflectionSymmetricEndpointKernel_is_mixed
#print axioms microscopicSpectator_inducedOrientationKernel_exact
#print axioms inducedCylinderChiralitySign_refineBy
#print axioms relationallySelected_cylinderSign_transport
#print axioms chirality_generation_and_transport_frontier

end

end UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
