/-
  Audit/KFCausalCSpecMicroscopicGate3LegacyStrictNoGo.lean

  Strict-stopping consistency audit for the legacy microscopic Gate 3 and
  scheduled-kernel Gate 4 supplier records.

  The legacy quantized Gate 3 record proves that its nonnegative tracked total
  is exactly zero at every sufficiently late stage.  Its embedded
  `PhysicalGrowthRepairRefinement`, however, demands strict contraction at
  every natural-number step.  Strict contraction from any such zero stage
  makes the next total negative, contradicting nonnegativity.  Consequently
  the legacy Gate 3 record, and every Gate 4 record containing it, are empty.

  This no-go does not use normalized weights.  The independent normalized
  component-floor audit remains useful because it identifies a second,
  earlier obstruction in the legacy convergence-certificate interface.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3LegacyStrictNoGo

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier

/-- The legacy named quantized Gate 3 supplier is uninhabited.  Its own
eventual exact-zero theorem is incompatible with strict contraction at the
following step and nonnegativity of the physical total distortion. -/
theorem not_microscopicGate3QuantizedConvergenceData
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ} :
    ¬ MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap := by
  intro D
  have heventual :=
    microscopicGate3QuantizedConvergenceData_eventually_exact_zero D
  rw [eventually_atTop] at heventual
  obtain ⟨N, hzero_after⟩ := heventual
  have hzero : total N = 0 := (hzero_after N le_rfl).1
  have hstrict : total (N + 1) < total N :=
    physicalGrowthRepairRefinement_step_strictly_contracts D.refinement N
  have htotal_nonneg : ∀ n, 0 ≤ total n :=
    physicalHauptvermutungTotalDistortion_sequence_nonneg
      (quantizedGate3Residuals_count_nonneg D.quantizedResiduals)
      (quantizedGate3Residuals_curvature_nonneg D.quantizedResiduals)
      (quantizedGate3Residuals_spectral_nonneg D.quantizedResiduals)
      D.total_eq
  rw [hzero] at hstrict
  exact (not_lt_of_ge (htotal_nonneg (N + 1))) hstrict

/-- The legacy scheduled-kernel Gate 4 supplier is also uninhabited because it
contains the impossible legacy quantized Gate 3 supplier. -/
theorem not_microscopicGate4ScheduledKernelData
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ} :
    ¬ MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale := by
  intro G
  exact not_microscopicGate3QuantizedConvergenceData G.gate3

#print axioms not_microscopicGate3QuantizedConvergenceData
#print axioms not_microscopicGate4ScheduledKernelData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3LegacyStrictNoGo
