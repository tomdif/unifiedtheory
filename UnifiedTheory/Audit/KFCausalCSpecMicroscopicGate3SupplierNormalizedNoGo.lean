/-
  Audit/KFCausalCSpecMicroscopicGate3SupplierNormalizedNoGo.lean

  Normalized-weight consequences for the legacy named Gate 3 and Gate 4
  supplier records.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3NormalizedWeightNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3SupplierNormalizedNoGo

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3NormalizedWeightNoGo

/-- The legacy named quantized Gate 3 target is impossible for normalized
weights: it produces the component-floor convergence certificate ruled out by
the centered-source expectation identity. -/
theorem microscopicGate3QuantizedConvergenceData_not_of_normalizedWeights
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (hweight_sum : ∀ n, (∑ i, w n i) = 1) :
    ¬ MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap := by
  intro D
  exact
    physicalHauptvermutungConvergenceCertificate_not_of_normalizedWeights
      hweight_sum
      (microscopicGate3QuantizedConvergenceData_convergenceCertificate D)

/-- Because the legacy scheduled-kernel Gate 4 record contains the legacy
Gate 3 target, it too has no normalized-weight inhabitant.  The corrected
Gate 3-to-Gate 4 handoff must use the stoppable aggregate-rate supplier. -/
theorem microscopicGate4ScheduledKernelData_not_of_normalizedWeights
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
    {errorScale : ℝ}
    (hweight_sum : ∀ n, (∑ i, w n i) = 1) :
    ¬ MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale := by
  intro G
  exact
    microscopicGate3QuantizedConvergenceData_not_of_normalizedWeights
      hweight_sum G.gate3

#print axioms microscopicGate3QuantizedConvergenceData_not_of_normalizedWeights
#print axioms microscopicGate4ScheduledKernelData_not_of_normalizedWeights

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3SupplierNormalizedNoGo
