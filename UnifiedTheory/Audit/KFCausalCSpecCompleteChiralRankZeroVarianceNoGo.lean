/-
  Audit/KFCausalCSpecCompleteChiralRankZeroVarianceNoGo.lean

  RANK-ZERO NO-GO FOR THE COMPLETE-CHIRAL GATE 3 ADAPTER

  There is exactly one unlabeled causal set on one event.  Consequently every
  observation of the rank-zero complete-chiral Born distribution is a Dirac
  distribution, and every observable has zero variance there.  The existing
  stoppable adapter asks for nonzero horizon variance at every natural-number
  stage, including zero, so its assumption record is uninhabited.

  This identifies an interface bug rather than a failure of the later repair
  argument: the nonzero-variance dynamics must start after the deterministic
  root stage (or use an explicitly shifted time index).

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecCompleteChiralStoppableRepairAdapter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecCompleteChiralRankZeroVarianceNoGo

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecCompleteChiralStoppableRepairAdapter

/-- The unique rank-zero causal branch. -/
def rankZeroCausalBranch : CausalSetGrowthBranch 0 :=
  Quotient.mk _ (cardinalCausalAntichain 1)

private noncomputable instance rankZeroCausalBranchUnique :
    Unique (CausalSetGrowthBranch 0) where
  default := rankZeroCausalBranch
  uniq child := unlabeledCardinalCausalOrder_one_unique child

/-- Any finite observation of the rank-zero Born law is the point mass at the
observation of the unique one-event causal set. -/
theorem completeChiralGate3Weight_zero_eq_indicator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (i : ι) :
    completeChiralGate3Weight chirality parentSchedule observe 0 i =
      if observe 0 rankZeroCausalBranch = i then 1 else 0 := by
  classical
  have hWeight :
      completeChiralStageBornWeight chirality 0 (parentSchedule 0)
          rankZeroCausalBranch = 1 := by
    have hSum := completeChiralStageBornWeight_sum_one
      chirality 0 (parentSchedule 0)
    simpa only [Fintype.sum_unique] using hSum
  unfold completeChiralGate3Weight completeChiralObservedBornWeight
  rw [Fintype.sum_unique]
  have hDefault : (default : CausalSetGrowthBranch 0) =
      rankZeroCausalBranch := Subsingleton.elim _ _
  rw [hDefault, hWeight]
  by_cases hObserved : observe 0 rankZeroCausalBranch = i <;>
    simp [hObserved]

/-- Every rank-zero observable has zero variance after any finite observation
map, independently of chirality and of the chosen parent schedule. -/
theorem completeChiralGate3Weight_zero_variance
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J : ι → ℝ) :
    variance
      (completeChiralGate3Weight chirality parentSchedule observe 0) J = 0 := by
  classical
  unfold variance covariance expectation
  simp_rw [completeChiralGate3Weight_zero_eq_indicator]
  simp

/-- The current complete-chiral stoppable-repair assumption package cannot be
instantiated: its all-stage nonzero-variance field contradicts the
deterministic rank-zero causal branch. -/
theorem not_completeChiralStoppableRepairAssumptions
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ)
    (scale c step descentRate remainder total correctorCoeff : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) :
    ¬ CompleteChiralStoppableRepairAssumptions chirality parentSchedule observe
      J countWindow curvatureBias spectralLocality corrector
      scale c step descentRate remainder total correctorCoeff edge candidate := by
  classical
  intro A
  exact A.horizon_variance_ne_zero 0
    (completeChiralGate3Weight_zero_variance
      chirality parentSchedule observe (J 0))

#print axioms completeChiralGate3Weight_zero_eq_indicator
#print axioms completeChiralGate3Weight_zero_variance
#print axioms not_completeChiralStoppableRepairAssumptions

end

end UnifiedTheory.Audit.KFCausalCSpecCompleteChiralRankZeroVarianceNoGo
