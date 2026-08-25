/-
  Audit/KFCausalCSpecMicroscopicGate3DirectRateStrictNoGo.lean

  Consistency audit for the strict direct-rate Gate 3 record.

  The current refinement contract strictly decreases the tracked total at
  every natural-number step.  The direct-rate quantization theorem, however,
  makes that same nonnegative total exactly zero at every sufficiently late
  step.  Strict decrease from any such zero step would make the next total
  negative, contradicting nonnegativity.  Consequently the record is empty.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRateStrictNoGo

open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRate
open Filter Topology

/-- The current direct-rate Gate 3 package is uninhabited: eventual exact
zero is incompatible with unconditional strict contraction of a nonnegative
total at the following step. -/
theorem not_microscopicGate3DirectRateQuantizedData
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ} :
    ¬ MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap := by
  intro D
  have heventual := D.eventually_exact_zero
  rw [eventually_atTop] at heventual
  obtain ⟨N, hzero_after⟩ := heventual
  have hzero : total N = 0 := (hzero_after N le_rfl).1
  have hstrict : total (N + 1) < total N :=
    physicalGrowthRepairRefinement_step_strictly_contracts D.refinement N
  have hnonneg : 0 ≤ total (N + 1) := D.total_nonneg (N + 1)
  rw [hzero] at hstrict
  exact (not_lt_of_ge hnonneg) hstrict

#print axioms not_microscopicGate3DirectRateQuantizedData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRateStrictNoGo
