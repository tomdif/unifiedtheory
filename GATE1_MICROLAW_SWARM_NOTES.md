# Gate 1 Microlaw Swarm Notes

Scope: Gate 1 is the microscopic causal-growth law. This note records the
current strongest Lean artifacts, the exact missing theorem interfaces, and
one smallest next theorem. No build, commit, or push was performed.

## Current Strongest Candidate Artifacts

1. Scalar ranked-cylinder growth machinery:
   - `UnifiedTheory/Audit/KFCausalSetSequentialGrowth.lean`
   - `RankedNormalizedComplexGrowthLaw`
   - `finiteRankedPathAmplitude`
   - `finiteRankedDepthDecoherence_normalized`
   - `finiteRankedDepthDecoherence_projective`
   - `finiteRankedDepthDecoherence_projective_by`
   - `infiniteRankedCylinderDecoherence_normalized`
   - `infiniteRankedCylinderDecoherence_hermitian`
   - `infiniteRankedCylinderDecoherence_stronglyPositive`
   - `normalized_stronglyPositive_infiniteRankedCylinder_family`
   - `UnlabeledComplexCausalGrowthWeights`
   - `weighted_unlabeled_causalSet_infiniteCylinder_promotion`
   - `physical_unlabeled_causalSet_infiniteCylinder_promotion`

2. Label-invariant transition-edge kinematics:
   - `UnifiedTheory/Audit/KFCausalSetTransitionEdges.lean`
   - `CausalPastSet`
   - `causalPastSetEquivOfIsomorphism`
   - `causalPastSet_relabel_ancestorCount`
   - `causalPastSet_relabel_maximalCount`
   - `causalTransitionTarget_relabel`
   - `labeledCausalTransitionMultiplicity_eq_of_isomorphic`
   - `causalTransitionMultiplicity`
   - `causalTransitionMultiplicity_pos_iff`
   - `rideoutSorkin_multiplicity_weighted_sum`
   - `uniformRideoutSorkinAggregatedTransition_normalized`
   - `complete_rideoutSorkin_transition_edge_kinematics`

3. Covariant raw-edge amplitudes and Bell-causality interface:
   - `UnifiedTheory/Audit/KFCausalSetBellCausality.lean`
   - `CovariantComplexCausalEdgeAmplitude`
   - `rideoutSorkinSignatureAmplitude`
   - `labeledAggregatedCausalEdgeAmplitude_eq_of_isomorphic`
   - `causalEdgeAmplitudePartition_eq_of_isomorphic`
   - `unlabeledAggregatedCausalEdgeAmplitude`
   - `unlabeledCausalEdgeAmplitudePartition`
   - `totalizedCausalEdgeGrowthLaw`
   - `IsCanonicallyBellCausal`
   - `rideoutSorkinSignatureAmplitude_canonicalBellCausal`
   - `canonicalBellCausal_contains_injective_ancestor_family`

4. Strongest scalar physical candidate:
   - `UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean`
   - `interactingChiralSignatureWeight`
   - `interactingChiralCausalEdgeAmplitude`
   - `canonicalPairCoupling`
   - `canonical_interactingChiral_partition_ne_zero`
   - `canonicalInteractingChiralTransition`
   - `completeChiralCausalSetGrowthLaw`
   - `completeChiralLaw_projective_stronglyPositive`
   - `completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical`
   - `completeChiralCausalSetGrowthLaw_transition_eq_of_parent_isomorphic`
   - `completeChiralCausalSetGrowthLaw_gate1_projective`
   - `completeChiralCausalSetGrowthLaw_gate1_quantum_consistent`
   - `completeChiral_inducedOrientationKernel_exact`
   - `completeChiralLaw_recovers_endpoint_without_totalization`
   - `fullSupport_endpoint_consistency_does_not_select_pairCoupling`

5. Born/projective intersection and support-preserving repair:
   - `UnifiedTheory/Audit/KFCausalBornNormalizationTransfer.lean`
   - `RankedBornNormalizedComplexGrowthLaw`
   - `finiteBornPathWeight_sum_children`
   - `finiteBornEventProbability_refine`
   - `biNormalizedGrowthLaw_two_consistencies`
   - `canonicalHarmonicBornLaw_two_consistencies`
   - `UnifiedTheory/Audit/KFCausalBornShellGeneralLaw.lean`
   - `physicalBornShell_all_rank_capstone`
   - `physicalBornShell_infiniteCylinder_promotion`
   - `canonicalHarmonicCriticalBornShellGrowthLaw`
   - `canonicalHarmonicCriticalBornShell_all_rank`
   - `canonicalHarmonicCriticalBornShell_promotion`

6. Higher-rank/operator-valued replacement track:
   - `UnifiedTheory/Audit/KFCausalHolonomyBornProjectiveGrowth.lean`
   - `recordOperatorKernel_stronglyPositive`
   - `recordOperatorKernel_sum_cons`
   - `recordOperatorKernel_double_sum_cons_of_sum_eq_one`
   - `causalHolonomyBornKernel_stronglyPositive`
   - `causalHolonomyBornKernel_projective`
   - `causalHolonomyBornKernel_exhaustively_projective`
   - `causalHolonomyBorn_projective_growth_complete`
   - `UnifiedTheory/Audit/KFCausalNativeResolutionLaw.lean`
   - `causalResolution_unique_of_recordPrinciples`
   - `nativeCausalResolutionOperator_born_complete`
   - `causalNativeResolutionLaw_capstone`

## Integrated Since Swarm Round 1

The following local Gate 1 interfaces are now proved in
`UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean`:

```lean
theorem completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
    (chirality : Fin 2) (n : Nat)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    (completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child = 0

theorem completeChiralCausalSetGrowthLaw_transition_eq_of_parent_isomorphic

theorem completeChiralCausalSetGrowthLaw_gate1_projective

theorem completeChiralCausalSetGrowthLaw_gate1_quantum_consistent
```

The support proof factors through two numerator-zero lemmas for labeled and
unlabeled coherent edge aggregation.  Off the physical one-birth graph, the
transition fiber is empty, so the canonical normalized transition has zero
numerator.  The projective and quantum-consistency wrappers package the
existing generic cylinder theorem under the concrete candidate-law name.

## Missing Gate 1 Theorem Interfaces

Label invariance / covariance: integrated.

```lean
theorem completeChiralCausalSetGrowthLaw_transition_eq_of_parent_isomorphic
    (chirality : Fin 2) {n : Nat}
    {parent parent' : CardinalCausalOrder n}
    (hIso : CardinalCausalOrderIsomorphic parent parent')
    (pathPrefix pathPrefix' : RankedGrowthPath CausalSetGrowthBranch n)
    (hCurrent :
      currentUnlabeledCausalOrder n pathPrefix = Quotient.mk _ parent)
    (hCurrent' :
      currentUnlabeledCausalOrder n pathPrefix' = Quotient.mk _ parent')
    (child : CausalSetGrowthBranch n) :
    (completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child =
      (completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix' child
```

Support / physical graph: integrated.

```lean
theorem completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
    (chirality : Fin 2) (n : Nat)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    (completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child = 0
```

Normalization and projective consistency, packaged for the concrete law:
integrated.

```lean
theorem completeChiralCausalSetGrowthLaw_gate1_projective
    (chirality : Fin 2) :
    (∀ n,
      IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) n))
      ∧
    (∀ n e1 e2 steps,
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) (n + steps))
        (refineRankedGrowthEventBy e1 steps)
        (refineRankedGrowthEventBy e2 steps)
      =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) n)
        e1 e2)
```

Quantum consistency / strong positivity: integrated.

```lean
theorem completeChiralCausalSetGrowthLaw_gate1_quantum_consistent
    (chirality : Fin 2) :
    IsHermitianGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (completeChiralCausalSetGrowthLaw chirality))
      ∧
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (completeChiralCausalSetGrowthLaw chirality))
      ∧
    infiniteRankedCylinderDecoherence
      (completeChiralCausalSetGrowthLaw chirality)
      (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
      (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1
```

Operator-valued replacement, if scalar coherent projectivity is not the final
physical law:

```lean
structure PhysicalCausalGrowthInstrumentLaw where
  carrierDimension : Nat
  outcomeCount : Nat -> Nat
  instrument :
    ∀ n, RankedGrowthPath CausalSetGrowthBranch n ->
      KrausRepresentation carrierDimension carrierDimension (outcomeCount n)
  -- Needed fields, following the existing `recordOperatorKernel_*` theorems:
  -- born completeness, optional coherent exhaustivity, physical support, and
  -- relabel covariance of the instrument family.
```

Downstream bridge into the current Hauptvermutung pipeline:

```lean
theorem completeChiralCausalSetGrowthLaw_yields_exactRecoveryCertificate
    (chirality : Fin 2) :
    exists w J source countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap,
      PhysicalHauptvermutungExactRecoveryCertificate
        w J source countWindow curvatureBias spectralLocality
        scale c step descentRate remainder total edge candidate
        stepFloor weightBase sourceBase residualGap
```

This final theorem is not currently close: it requires deriving the
`stepFloor`, `weightBase`, `sourceBase`, centered-source floor, residual gaps,
and `total_eq` identity from the actual microscopic law.

## Next Theorem Targets

1. Build the downstream certificate interface only after the physical
   aggregate-rate and residual-gap hypotheses are derived from the microscopic
   dynamics.
2. Identify or formalize the extra microscopic selection principle needed to
   pick `canonicalPairCoupling`; current all-rank support and endpoint
   consistency still do not select it.
