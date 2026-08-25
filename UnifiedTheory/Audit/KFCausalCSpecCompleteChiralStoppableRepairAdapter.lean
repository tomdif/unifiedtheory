/-
  Audit/KFCausalCSpecCompleteChiralStoppableRepairAdapter.lean

  COMPLETE CHIRAL GROWTH -> STOPPABLE GATE 3 ADAPTER

  This file makes the available microscopic link explicit.  The complete
  chiral causal-set law canonically supplies nonnegative normalized Born
  weights after pushforward to a fixed finite observation family.  With those
  weights, the Gate 3 repair source is defined—not assumed—as the corrected
  horizon-invisible descent source for the stage physical Hauptvermutung
  distortion and a supplied corrector channel.

  What remains physical input is recorded exactly: nonzero horizon variance,
  a second-order leakage-null condition, a descent margin for the corrector,
  the physical total-update estimate, the Taylor remainder estimate, and a
  nonnegative step.  Quantization, positive gaps, a positive step floor, and
  the aggregate rate are then the separate hypotheses needed by the exact
  stoppable Gate 3 theorem.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw
import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecCompleteChiralStoppableRepairAdapter

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

/-- The Gate 3 weight is the fixed-family pushforward of the complete chiral
stagewise Born distribution. -/
noncomputable def completeChiralGate3Weight
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ℕ → ι → ℝ :=
  completeChiralObservedBornWeight chirality parentSchedule observe

/-- The raw defect observable repaired at a stage is the full physical
Hauptvermutung distortion, including residual and bridge terms. -/
noncomputable def completeChiralPhysicalDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) :
    ℕ → ι → ℝ :=
  fun n =>
    physicalHauptvermutungDistortion
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (edge n) (candidate n)

/-- The source is canonical once the stage law, horizon observable, physical
distortion, corrector channel, and corrector coefficient are fixed. -/
noncomputable def completeChiralCorrectedRepairSource
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ)
    (scale correctorCoeff : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) :
    ℕ → ι → ℝ :=
  fun n =>
    correctedCanonicalHorizonInvisibleDescentSource
      (completeChiralGate3Weight chirality parentSchedule observe n)
      (J n)
      (completeChiralPhysicalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate n)
      (corrector n) (correctorCoeff n)

/-- Normalization is a theorem of the complete chiral Born construction, not
an assumption of the adapter. -/
theorem completeChiralGate3Weight_sum_one
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) :
    (∑ i,
      completeChiralGate3Weight chirality parentSchedule observe n i) = 1 := by
  exact
    completeChiralObservedBornWeight_sum_one
      chirality parentSchedule observe n

/-- The same derived weights are nonnegative. -/
theorem completeChiralGate3Weight_nonneg
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ∀ n i,
      0 ≤ completeChiralGate3Weight chirality parentSchedule observe n i := by
  exact
    completeChiralObservedBornWeight_nonneg
      chirality parentSchedule observe

/-! ## Canonical coherent-parent specialization

Only the parent schedule is now canonical.  The finite observation map into
the Gate 3 cell family remains supplied externally, as do all repair premises
recorded below in `CompleteChiralStoppableRepairAssumptions`. -/

/-- Gate 3 weights obtained by observing the prefix-coherent physical parent
schedule constructed by the complete-chiral Born path law. -/
noncomputable def completeChiralCanonicalScheduleGate3Weight
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ℕ → ι → ℝ :=
  completeChiralGate3Weight
    chirality canonicalPhysicalParentSchedule observe

/-- The canonical-schedule Gate 3 weights remain normalized. -/
theorem completeChiralCanonicalScheduleGate3Weight_sum_one
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) :
    (∑ i,
      completeChiralCanonicalScheduleGate3Weight chirality observe n i) = 1 := by
  exact completeChiralGate3Weight_sum_one
    chirality canonicalPhysicalParentSchedule observe n

/-- The canonical-schedule Gate 3 weights remain nonnegative. -/
theorem completeChiralCanonicalScheduleGate3Weight_nonneg
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ∀ n i,
      0 ≤ completeChiralCanonicalScheduleGate3Weight
        chirality observe n i := by
  exact completeChiralGate3Weight_nonneg
    chirality canonicalPhysicalParentSchedule observe

/-- The parents used by this specialization are physical finite growth paths
at every rank. -/
theorem completeChiralCanonicalParentSchedule_isPhysical (n : ℕ) :
    IsPhysicalCausalGrowthPath n (canonicalPhysicalParentSchedule n) :=
  canonicalPhysicalParentSchedule_isPhysical n

/-- Exactly the still-unproved step-level inputs needed to turn the chosen
complete-chiral weight/source pair into certified stoppable repair steps.

This is not the complete Gate 3 assumption list: the observation map,
quantization, gaps, total identity, step floor, and aggregate rate enter
outside this low-level refinement record.

No weight normalization or source choice occurs among these fields. -/
structure CompleteChiralStoppableRepairAssumptions
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ)
    (scale c step descentRate remainder total correctorCoeff : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) : Prop where
  horizon_variance_ne_zero :
    ∀ n,
      variance
        (completeChiralGate3Weight chirality parentSchedule observe n)
        (J n) ≠ 0
  leakage_null_cone :
    ∀ n,
      horizonSecondOrderLeakageQuadratic
        (completeChiralGate3Weight chirality parentSchedule observe n)
        (J n)
        (horizonOrthogonalResidual
          (completeChiralGate3Weight chirality parentSchedule observe n)
          (J n)
          (completeChiralPhysicalDistortion
            countWindow curvatureBias spectralLocality
            scale edge candidate n))
        (horizonOrthogonalResidual
          (completeChiralGate3Weight chirality parentSchedule observe n)
          (J n) (corrector n))
        (-1) (correctorCoeff n) = 0
  descent_margin :
    ∀ n,
      correctorCoeff n *
          linearResponse
            (completeChiralGate3Weight chirality parentSchedule observe n)
            (horizonOrthogonalResidual
              (completeChiralGate3Weight chirality parentSchedule observe n)
              (J n) (corrector n))
            (completeChiralPhysicalDistortion
              countWindow curvatureBias spectralLocality
              scale edge candidate n) ≤
        variance
            (completeChiralGate3Weight chirality parentSchedule observe n)
            (horizonOrthogonalResidual
              (completeChiralGate3Weight chirality parentSchedule observe n)
              (J n)
              (completeChiralPhysicalDistortion
                countWindow curvatureBias spectralLocality
                scale edge candidate n)) -
          descentRate n
  physical_update_bound :
    ∀ n,
      total (n + 1) ≤ total n +
        step n *
          linearResponse
            (completeChiralGate3Weight chirality parentSchedule observe n)
            (completeChiralCorrectedRepairSource
              chirality parentSchedule observe J
              countWindow curvatureBias spectralLocality corrector
              scale correctorCoeff edge candidate n)
            (completeChiralPhysicalDistortion
              countWindow curvatureBias spectralLocality
              scale edge candidate n) +
        remainder n
  remainder_bound :
    ∀ n, remainder n ≤ step n * descentRate n / 2
  step_nonneg : ∀ n, 0 ≤ step n

namespace CompleteChiralStoppableRepairAssumptions

variable {ι : Type*} [Fintype ι]
variable {chirality : Fin 2}
variable
  {parentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n}
variable {observe : (n : ℕ) → CausalSetGrowthBranch n → ι}
variable
  {J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ}
variable
  {scale c step descentRate remainder total correctorCoeff : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}

variable
  (A : CompleteChiralStoppableRepairAssumptions
    chirality parentSchedule observe J
    countWindow curvatureBias spectralLocality corrector
    scale c step descentRate remainder total correctorCoeff edge candidate)

include A

/-- The complete chiral normalized weights and canonical corrected source,
together with the six recorded physical assumptions, construct the corrected
stoppable refinement. -/
theorem toStoppablePhysicalGrowthRepairRefinement :
    StoppablePhysicalGrowthRepairRefinement
      (completeChiralGate3Weight chirality parentSchedule observe)
      J
      (completeChiralCorrectedRepairSource
        chirality parentSchedule observe J
        countWindow curvatureBias spectralLocality corrector
        scale correctorCoeff edge candidate)
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate := by
  refine
    { certified_step := ?_
      step_nonneg := A.step_nonneg }
  intro n
  have hbridge :=
    correctedCanonicalHorizonInvisibleDescentSource_protected_bridge
      (completeChiralGate3Weight chirality parentSchedule observe n)
      (J n)
      (completeChiralPhysicalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate n)
      (corrector n) (c n) (correctorCoeff n) (descentRate n)
      (completeChiralGate3Weight_sum_one
        chirality parentSchedule observe n)
      (A.horizon_variance_ne_zero n)
      (A.leakage_null_cone n)
      (A.descent_margin n)
  exact
    { first_horizon_area_zero := hbridge.1.1
      second_horizon_area_zero := hbridge.1.2
      descends_aggregate := hbridge.2
      update_bound := A.physical_update_bound n
      remainder_bound := A.remainder_bound n }

/-- Add the explicit discrete and uniform-rate hypotheses required by the
stoppable exact-recovery theorem.  The refinement, weights, and source are
constructed by the adapter rather than supplied independently. -/
theorem toMicroscopicGate3StoppableDirectRateQuantizedData
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (rateBase stepFloor countGap curvatureGap spectralGap : ℝ)
    (countGap_pos : 0 < countGap)
    (curvatureGap_pos : 0 < curvatureGap)
    (spectralGap_pos : 0 < spectralGap)
    (count_eq :
      ∀ n i, countWindow n i = countGap * (countQuantum n i : ℝ))
    (curvature_eq :
      ∀ n i,
        curvatureBias n i = curvatureGap * (curvatureQuantum n i : ℝ))
    (spectral_eq :
      ∀ n i,
        spectralLocality n i = spectralGap * (spectralQuantum n i : ℝ))
    (rateBase_pos : 0 < rateBase)
    (stepFloor_pos : 0 < stepFloor)
    (total_eq :
      ∀ n,
        total n =
          physicalHauptvermutungTotalDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n))
    (step_floor : ∀ n, stepFloor ≤ step n)
    (aggregate_rate : ∀ n, rateBase * total n ≤ descentRate n) :
    MicroscopicGate3StoppableDirectRateQuantizedData
      (completeChiralGate3Weight chirality parentSchedule observe)
      J
      (completeChiralCorrectedRepairSource
        chirality parentSchedule observe J
        countWindow curvatureBias spectralLocality corrector
        scale correctorCoeff edge candidate)
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap := by
  exact
    { refinement := A.toStoppablePhysicalGrowthRepairRefinement
      countGap_pos := countGap_pos
      curvatureGap_pos := curvatureGap_pos
      spectralGap_pos := spectralGap_pos
      count_eq := count_eq
      curvature_eq := curvature_eq
      spectral_eq := spectral_eq
      rateBase_pos := rateBase_pos
      stepFloor_pos := stepFloor_pos
      total_eq := total_eq
      step_floor := step_floor
      aggregate_rate := aggregate_rate }

#print axioms completeChiralGate3Weight_sum_one
#print axioms completeChiralGate3Weight_nonneg
#print axioms completeChiralCanonicalScheduleGate3Weight_sum_one
#print axioms completeChiralCanonicalScheduleGate3Weight_nonneg
#print axioms completeChiralCanonicalParentSchedule_isPhysical
#print axioms toStoppablePhysicalGrowthRepairRefinement
#print axioms toMicroscopicGate3StoppableDirectRateQuantizedData

end CompleteChiralStoppableRepairAssumptions

end

end UnifiedTheory.Audit.KFCausalCSpecCompleteChiralStoppableRepairAdapter
