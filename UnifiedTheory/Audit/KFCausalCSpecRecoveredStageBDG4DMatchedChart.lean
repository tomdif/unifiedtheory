/-
  Audit/KFCausalCSpecRecoveredStageBDG4DMatchedChart.lean

  Matched residual channels for the physical-chart recovered 4D BDG bridge.

  The physical-chart supplier interface still required the scalar chart
  certificate channels `countWindow`, `curvatureBias`, and `pairConsistency`
  to tend to zero.  Exact recovered CSpec stages already prove cellwise
  convergence of the recovered count, curvature, and spectral/locality
  residuals.  This file connects those two facts.

  If the physical chart certificate's scalar channels are the finite sums of
  the corresponding recovered residual families, their vanishing follows from
  the exact recovery certificate.  The remaining Gate 4 analytic obligation is
  therefore narrowed again: build the physical chart certificates and the
  reduced 4D BDG operator profile package with these matched residual
  identities.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DPhysicalChart

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

namespace RecoveredStageExactCSpecSequence

theorem countWindow_sum_tendsto_zero
    {cell : Type*} [Fintype cell]
    (S : RecoveredStageExactCSpecSequence cell) :
    Tendsto (fun n => ∑ i, S.countWindow n i) atTop (𝓝 0) := by
  simpa using
    tendsto_finset_sum Finset.univ
      (fun i _ =>
        physicalHauptvermutungConvergenceCertificate_countWindow_tendsto_zero
          S.exact_recovery.convergence i)

theorem curvatureBias_sum_tendsto_zero
    {cell : Type*} [Fintype cell]
    (S : RecoveredStageExactCSpecSequence cell) :
    Tendsto (fun n => ∑ i, S.curvatureBias n i) atTop (𝓝 0) := by
  simpa using
    tendsto_finset_sum Finset.univ
      (fun i _ =>
        physicalHauptvermutungConvergenceCertificate_curvatureBias_tendsto_zero
          S.exact_recovery.convergence i)

theorem spectralLocality_sum_tendsto_zero
    {cell : Type*} [Fintype cell]
    (S : RecoveredStageExactCSpecSequence cell) :
    Tendsto (fun n => ∑ i, S.spectralLocality n i) atTop (𝓝 0) := by
  simpa using
    tendsto_finset_sum Finset.univ
      (fun i _ =>
        physicalHauptvermutungConvergenceCertificate_spectralLocality_tendsto_zero
          S.exact_recovery.convergence i)

end RecoveredStageExactCSpecSequence

/-- A physical chart supplier whose scalar chart-certificate residual channels
are matched to the finite sums of exact recovered CSpec residuals. -/
structure RecoveredStageBDG4DMatchedPhysicalChartInterface
    (cell X Y chart : Type*) [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart] where
  recovered : RecoveredStageExactCSpecSequence cell
  chartCertificate :
    ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart
  fixedScale : ℝ
  scale_eq : ∀ n, (chartCertificate n).scale = fixedScale
  countWindow_eq_sum :
    ∀ n, (chartCertificate n).countWindow = ∑ i, recovered.countWindow n i
  curvatureBias_eq_sum :
    ∀ n, (chartCertificate n).curvatureBias = ∑ i, recovered.curvatureBias n i
  pairConsistency_eq_spectral_sum :
    ∀ n, (chartCertificate n).pairConsistency =
      ∑ i, recovered.spectralLocality n i
  density_tendsto_atTop :
    Tendsto (fun n => (chartCertificate n).density) atTop atTop
  coord : Y → Fin 4 → ℝ
  chartOfCell : cell → chart
  sampleEvent : ℕ → cell → X
  phiAtPoint : ℝ
  curvaturePhi : ℝ
  operatorData : BDG4DOperatorProfileData

namespace RecoveredStageBDG4DMatchedPhysicalChartInterface

theorem countWindow_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).countWindow) atTop (𝓝 0) := by
  have hsum := I.recovered.countWindow_sum_tendsto_zero
  have heq :
      (fun n => ∑ i, I.recovered.countWindow n i) =ᶠ[atTop]
        fun n => (I.chartCertificate n).countWindow :=
    Filter.Eventually.of_forall (fun n => (I.countWindow_eq_sum n).symm)
  exact hsum.congr' heq

theorem curvatureBias_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).curvatureBias) atTop (𝓝 0) := by
  have hsum := I.recovered.curvatureBias_sum_tendsto_zero
  have heq :
      (fun n => ∑ i, I.recovered.curvatureBias n i) =ᶠ[atTop]
        fun n => (I.chartCertificate n).curvatureBias :=
    Filter.Eventually.of_forall (fun n => (I.curvatureBias_eq_sum n).symm)
  exact hsum.congr' heq

theorem pairConsistency_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).pairConsistency) atTop (𝓝 0) := by
  have hsum := I.recovered.spectralLocality_sum_tendsto_zero
  have heq :
      (fun n => ∑ i, I.recovered.spectralLocality n i) =ᶠ[atTop]
        fun n => (I.chartCertificate n).pairConsistency :=
    Filter.Eventually.of_forall
      (fun n => (I.pairConsistency_eq_spectral_sum n).symm)
  exact hsum.congr' heq

/-- The matched residual identities instantiate the physical-chart supplier
interface without separate chart-channel convergence assumptions. -/
noncomputable def toPhysicalChartInterface
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart) :
    RecoveredStageBDG4DPhysicalChartInterface cell X Y chart where
  recovered := I.recovered
  chartCertificate := I.chartCertificate
  fixedScale := I.fixedScale
  scale_eq := I.scale_eq
  countWindow_tendsto_zero := I.countWindow_tendsto_zero
  curvatureBias_tendsto_zero := I.curvatureBias_tendsto_zero
  pairConsistency_tendsto_zero := I.pairConsistency_tendsto_zero
  density_tendsto_atTop := I.density_tendsto_atTop
  coord := I.coord
  chartOfCell := I.chartOfCell
  sampleEvent := I.sampleEvent
  phiAtPoint := I.phiAtPoint
  curvaturePhi := I.curvaturePhi
  operatorData := I.operatorData

theorem distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (𝓝 0) := by
  exact I.toPhysicalChartInterface.distortionBound_tendsto_zero

theorem rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.recovered.countWindow n i)
          (I.recovered.curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.operatorData ((I.chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) ∧
      Tendsto (fun n => (I.chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa [toPhysicalChartInterface]
    using
      RecoveredStageBDG4DPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
        I.toPhysicalChartInterface errorScale

theorem recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.recovered.countWindow n) (I.recovered.curvatureBias n)
        (I.recovered.spectralLocality n)
        (I.recovered.scale n) (I.recovered.total n)
        (I.recovered.edge n) (I.recovered.candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.operatorData ((I.chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) ∧
      Tendsto (fun n => (I.chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa [toPhysicalChartInterface]
    using
      RecoveredStageBDG4DPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
        I.toPhysicalChartInterface

#print axioms RecoveredStageExactCSpecSequence.countWindow_sum_tendsto_zero
#print axioms RecoveredStageExactCSpecSequence.curvatureBias_sum_tendsto_zero
#print axioms RecoveredStageExactCSpecSequence.spectralLocality_sum_tendsto_zero
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.countWindow_tendsto_zero
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.curvatureBias_tendsto_zero
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.pairConsistency_tendsto_zero
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.toPhysicalChartInterface
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DMatchedPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero

end RecoveredStageBDG4DMatchedPhysicalChartInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
