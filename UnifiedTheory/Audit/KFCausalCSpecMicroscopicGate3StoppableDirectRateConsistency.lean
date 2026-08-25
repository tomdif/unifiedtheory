/-
  Audit/KFCausalCSpecMicroscopicGate3StoppableDirectRateConsistency.lean

  A concrete consistency witness for the stoppable direct-rate Gate 3 record.

  On a nonempty one-point index type, take the unique weight to be one and all
  local residuals, sources, rates, remainders, and tracked totals to be zero;
  use the canonical bridge candidate; and take the step and every positive
  gap/base constant to be one.  This is a genuine inhabitant of the stoppable
  record, with normalized weights.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRateConsistency

open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate
open scoped BigOperators

def zeroLocalReal : ℕ → Unit → ℝ := fun _ _ => 0

def oneLocalReal : ℕ → Unit → ℝ := fun _ _ => 1

def zeroLocalNat : ℕ → Unit → ℕ := fun _ _ => 0

def zeroScalar : ℕ → ℝ := fun _ => 0

def oneScalar : ℕ → ℝ := fun _ => 1

def unitEdge : ℕ → Unit → E4 := fun _ _ => .e01

noncomputable def unitCanonicalCandidate :
    ℕ → Unit → Equiv.Perm Direction :=
  fun n => canonicalCSpecBridgeCandidate (unitEdge n)

/-- The concrete one-cell weight is normalized at every stage. -/
theorem oneLocalReal_normalized (n : ℕ) :
    (∑ i : Unit, oneLocalReal n i) = 1 := by
  simp [oneLocalReal]

/-- A nonempty-index concrete inhabitant of the stoppable direct-rate record.
It represents an already-recovered state which remains fixed forever. -/
theorem unit_zero_model :
    MicroscopicGate3StoppableDirectRateQuantizedData
      oneLocalReal zeroLocalReal zeroLocalReal
      zeroLocalReal zeroLocalReal zeroLocalReal
      zeroScalar zeroScalar oneScalar zeroScalar zeroScalar zeroScalar
      unitEdge unitCanonicalCandidate
      zeroLocalNat zeroLocalNat zeroLocalNat
      1 1 1 1 1 := by
  refine
    { refinement := ?_
      countGap_pos := by norm_num
      curvatureGap_pos := by norm_num
      spectralGap_pos := by norm_num
      count_eq := ?_
      curvature_eq := ?_
      spectral_eq := ?_
      rateBase_pos := by norm_num
      stepFloor_pos := by norm_num
      total_eq := ?_
      step_floor := ?_
      aggregate_rate := ?_ }
  · refine
      { certified_step := ?_
        step_nonneg := ?_ }
    · intro n
      refine
        { first_horizon_area_zero := ?_
          second_horizon_area_zero := ?_
          descends_aggregate := ?_
          update_bound := ?_
          remainder_bound := ?_ }
      · simp [linearResponse, expectation, centeredSource, oneLocalReal,
          zeroLocalReal, zeroScalar]
      · simp [quadraticResponse, covariance, expectation, centeredSource,
          oneLocalReal, zeroLocalReal, zeroScalar]
      · simp [linearResponse, expectation, centeredSource, oneLocalReal,
          zeroLocalReal, zeroScalar]
      · simp [linearResponse, expectation, centeredSource, oneLocalReal,
          zeroLocalReal, zeroScalar, oneScalar]
      · simp [zeroScalar, oneScalar]
    · intro n
      simp [oneScalar]
  · intro n i
    simp [zeroLocalReal, zeroLocalNat]
  · intro n i
    simp [zeroLocalReal, zeroLocalNat]
  · intro n i
    simp [zeroLocalReal, zeroLocalNat]
  · intro n
    change 0 =
      physicalHauptvermutungTotalDistortion
        (zeroLocalReal n) (zeroLocalReal n) (zeroLocalReal n)
        (zeroScalar n) (unitEdge n) (unitCanonicalCandidate n)
    symm
    exact
      (physicalHauptvermutungTotalDistortion_eq_zero_iff
        (zeroLocalReal n) (zeroLocalReal n) (zeroLocalReal n)
        (zeroScalar n) (unitEdge n) (unitCanonicalCandidate n)
        (by simp [zeroLocalReal])
        (by simp [zeroLocalReal])
        (by simp [zeroLocalReal])).2
        ⟨by simp [zeroLocalReal], by simp [zeroLocalReal],
          by simp [zeroLocalReal], rfl⟩
  · intro n
    simp [oneScalar]
  · intro n
    simp [zeroScalar]

#print axioms oneLocalReal_normalized
#print axioms unit_zero_model
#print axioms
  MicroscopicGate3StoppableDirectRateQuantizedData.horizonProtection_and_total_tendsto_zero
#print axioms MicroscopicGate3StoppableDirectRateQuantizedData.descentRate_eq_zero_of_total_eq_zero
#print axioms MicroscopicGate3StoppableDirectRateQuantizedData.total_next_eq_zero_of_total_eq_zero
#print axioms MicroscopicGate3StoppableDirectRateQuantizedData.eventually_exact_zero

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRateConsistency
