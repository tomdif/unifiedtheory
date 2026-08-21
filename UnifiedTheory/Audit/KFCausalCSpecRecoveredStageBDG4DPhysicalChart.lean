/-
  Audit/KFCausalCSpecRecoveredStageBDG4DPhysicalChart.lean

  Physical-Hauptvermutung chart supplier for the recovered-stage 4D BDG bridge.

  `KFCausalCSpecHauptvermutungPhysicalBridge` already packages finite local
  chart/count/volume hypotheses as `PhysicalGrowthHauptvermutungCertificate`
  and proves that its displayed distortion bound tends to zero when the count,
  curvature, and pair-consistency channels vanish.  The previous recovered BDG
  chart bridge then consumes a density sequence, local chart coordinates, and a
  reduced 4D BDG operator profile bundle.

  This file connects those two interfaces.  A sequence of physical
  Hauptvermutung certificates now supplies the density and coordinate source for
  `RecoveredStageBDG4DChartData`; the remaining analytic obligation is narrowed
  to the `BDG4DOperatorProfileData` support/regularity/cone-bound package.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DChart
import UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

/-- A point sampled from a stage-indexed physical Hauptvermutung chart family.
The stage index lets the coordinate map use the chart certificate available at
that refinement level. -/
structure PhysicalGrowthStagePoint (X : Type*) where
  stage : ℕ
  event : X

/-- Exact recovered CSpec stages plus a sequence of physical Hauptvermutung
chart certificates feeding the recovered 4D BDG chart interface.

The fields `countWindow_tendsto_zero`, `curvatureBias_tendsto_zero`, and
`pairConsistency_tendsto_zero` are exactly the hypotheses consumed by the
existing physical-Hauptvermutung bridge.  The field `operatorData` is still the
reduced 4D BDG analytic profile package; proving that the physical law supplies
that package remains the next analytic task. -/
structure RecoveredStageBDG4DPhysicalChartInterface
    (cell X Y chart : Type*) [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart] where
  recovered : RecoveredStageExactCSpecSequence cell
  chartCertificate :
    ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart
  fixedScale : ℝ
  scale_eq : ∀ n, (chartCertificate n).scale = fixedScale
  countWindow_tendsto_zero :
    Tendsto (fun n => (chartCertificate n).countWindow) atTop (𝓝 0)
  curvatureBias_tendsto_zero :
    Tendsto (fun n => (chartCertificate n).curvatureBias) atTop (𝓝 0)
  pairConsistency_tendsto_zero :
    Tendsto (fun n => (chartCertificate n).pairConsistency) atTop (𝓝 0)
  density_tendsto_atTop :
    Tendsto (fun n => (chartCertificate n).density) atTop atTop
  coord : Y → Fin 4 → ℝ
  chartOfCell : cell → chart
  sampleEvent : ℕ → cell → X
  phiAtPoint : ℝ
  curvaturePhi : ℝ
  operatorData : BDG4DOperatorProfileData

namespace RecoveredStageBDG4DPhysicalChartInterface

/-- The physical Hauptvermutung certificate sequence supplies the chart data
shape required by the recovered 4D BDG chart bridge. -/
noncomputable def toChartData
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart) :
    RecoveredStageBDG4DChartData cell chart (PhysicalGrowthStagePoint X) where
  chartOfCell := I.chartOfCell
  samplePoint := fun n i => ⟨n, I.sampleEvent n i⟩
  coordinate := fun localChart point k =>
    I.coord ((I.chartCertificate point.stage).chart localChart point.event) k
  density := fun n => (I.chartCertificate n).density
  density_tendsto_atTop := I.density_tendsto_atTop
  phiAtPoint := I.phiAtPoint
  curvaturePhi := I.curvaturePhi
  operatorData := I.operatorData

/-- The physical chart supplier instantiates the recovered-stage BDG chart
interface. -/
noncomputable def toChartInterface
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart) :
    RecoveredStageBDG4DChartInterface cell chart (PhysicalGrowthStagePoint X) where
  recovered := I.recovered
  chartData := I.toChartData

/-- Each finite physical Hauptvermutung chart certificate supplies the checked
global approximate-isometry bridge at that stage. -/
theorem applies_quantitative_hauptvermutung_at
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart)
    (n : ℕ) :
    (I.chartCertificate n).QuantitativeHauptvermutungAppliesToPhysicalGrowth := by
  exact
    PhysicalGrowthHauptvermutungCertificate.applies_quantitative_hauptvermutung
      (I.chartCertificate n)

/-- The displayed physical-Hauptvermutung distortion bound tends to zero along
the recovered chart sequence. -/
theorem distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (𝓝 0) := by
  exact
    PhysicalGrowthHauptvermutungCertificate.certificate_distortionBound_tendsto_zero
      I.chartCertificate I.fixedScale I.scale_eq
      I.countWindow_tendsto_zero I.curvatureBias_tendsto_zero
      I.pairConsistency_tendsto_zero

/-- The physical chart supplier gives the sampled reduced 4D operator limit. -/
theorem chart_operator_tendsto
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart) :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorData ((I.chartCertificate n).density))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) := by
  simpa [toChartInterface, toChartData]
    using I.toChartInterface.chart_operator_tendsto

/-- Exact recovered CSpec stages, physical chart distortion collapse, and the
sampled reduced 4D BDG operator limit in one package. -/
theorem rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart)
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
  exact
    ⟨I.recovered.eventually_rssPoissonError_zero errorScale,
      I.chart_operator_tendsto,
      I.distortionBound_tendsto_zero⟩

/-- Eventual recovered finite stages, physical chart distortion collapse, and
the sampled reduced 4D BDG operator limit. -/
theorem recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DPhysicalChartInterface cell X Y chart) :
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
  exact
    ⟨I.recovered.eventually_recoveredStage,
      I.chart_operator_tendsto,
      I.distortionBound_tendsto_zero⟩

#print axioms RecoveredStageBDG4DPhysicalChartInterface.toChartData
#print axioms RecoveredStageBDG4DPhysicalChartInterface.toChartInterface
#print axioms RecoveredStageBDG4DPhysicalChartInterface.applies_quantitative_hauptvermutung_at
#print axioms RecoveredStageBDG4DPhysicalChartInterface.distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DPhysicalChartInterface.chart_operator_tendsto
#print axioms RecoveredStageBDG4DPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero

end RecoveredStageBDG4DPhysicalChartInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
