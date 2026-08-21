/-
  Audit/KFCausalCSpecRecoveredStageBDG4DChart.lean

  Local-chart supplier interface for the recovered-stage 4D BDG bridge.

  Previous modules show that exact recovered CSpec stages plus a supplied
  `BDG4DOperatorProfileData` object imply zero finite RSS/Poisson horizon error
  and convergence of the sampled reduced 4D BDG operator.  This file names the
  next physical obligation more sharply: recovered local charts must supply the
  density sequence, sampled point data, and reduced 4D operator profile bundle.

  The theorems here are intentionally conditional.  They do not assert that the
  physical growth law has already produced the chart regularity/support/cone
  estimates; they prove that once those chart estimates are supplied, the
  recovered finite stages feed the concrete 4D operator theorem with no further
  BDG layer assumption.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DRecovered

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-- Exact recovered finite CSpec sequence data, separated from the analytic 4D
BDG profile data.  This is the finite side of the chart-supplier interface. -/
structure RecoveredStageExactCSpecSequence
    (cell : Type*) [Fintype cell] where
  cSpecWeight : ℕ → cell → ℝ
  horizonSource : ℕ → cell → ℝ
  repairSource : ℕ → cell → ℝ
  countWindow : ℕ → cell → ℝ
  curvatureBias : ℕ → cell → ℝ
  spectralLocality : ℕ → cell → ℝ
  scale : ℕ → ℝ
  areaCoeff : ℕ → ℝ
  step : ℕ → ℝ
  descentRate : ℕ → ℝ
  remainder : ℕ → ℝ
  total : ℕ → ℝ
  edge : ℕ → cell → E4
  candidate : ℕ → cell → Equiv.Perm Direction
  stepFloor : ℝ
  weightBase : ℝ
  sourceBase : ℝ
  residualGap : ℝ
  exact_recovery :
    PhysicalHauptvermutungExactRecoveryCertificate
      cSpecWeight horizonSource repairSource
      countWindow curvatureBias spectralLocality
      scale areaCoeff step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap

namespace RecoveredStageExactCSpecSequence

theorem eventually_recoveredStage
    {cell : Type*} [Fintype cell]
    (S : RecoveredStageExactCSpecSequence cell) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (S.countWindow n) (S.curvatureBias n) (S.spectralLocality n)
        (S.scale n) (S.total n) (S.edge n) (S.candidate n) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage
      S.exact_recovery

theorem eventually_rssPoissonError_zero
    {cell : Type*} [Fintype cell]
    (S : RecoveredStageExactCSpecSequence cell)
    (errorScale : ℝ) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (S.countWindow n i) (S.curvatureBias n i) errorScale = 0 := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
      S.exact_recovery

theorem exists_rssPoissonError_zero_after
    {cell : Type*} [Fintype cell]
    (S : RecoveredStageExactCSpecSequence cell)
    (errorScale : ℝ) :
    ∃ N, ∀ n, N ≤ n →
      ∀ i,
        rssPoissonError
          (S.countWindow n i) (S.curvatureBias n i) errorScale = 0 := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_exists_rssPoissonError_zero_after
      S.exact_recovery

end RecoveredStageExactCSpecSequence

/-- Recovered local 4D chart data that supplies the reduced BDG operator
profile bundle.  The geometric work hidden behind this record is exactly the
support, regularity, and cone-bound stack inside `BDG4DOperatorProfileData`.

The `chartOfCell`, `samplePoint`, and `coordinate` fields keep the data tied to
the recovered finite cells; the downstream theorem only needs the density and
operator profile once those chart estimates are established. -/
structure RecoveredStageBDG4DChartData
    (cell chart point : Type*) where
  chartOfCell : cell → chart
  samplePoint : ℕ → cell → point
  coordinate : chart → point → Fin 4 → ℝ
  density : ℕ → ℝ
  density_tendsto_atTop : Tendsto density atTop atTop
  phiAtPoint : ℝ
  curvaturePhi : ℝ
  operatorData : BDG4DOperatorProfileData

/-- Exact recovered finite CSpec stages together with local 4D chart data that
supplies the reduced BDG operator profile. -/
structure RecoveredStageBDG4DChartInterface
    (cell chart point : Type*) [Fintype cell] where
  recovered : RecoveredStageExactCSpecSequence cell
  chartData : RecoveredStageBDG4DChartData cell chart point

namespace RecoveredStageBDG4DChartInterface

/-- The chart-supplied profile data instantiates the concrete recovered-stage
4D operator interface. -/
noncomputable def toOperatorInterface
    {cell chart point : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DChartInterface cell chart point) :
    RecoveredStageBDG4DOperatorInterface cell where
  cSpecWeight := I.recovered.cSpecWeight
  horizonSource := I.recovered.horizonSource
  repairSource := I.recovered.repairSource
  countWindow := I.recovered.countWindow
  curvatureBias := I.recovered.curvatureBias
  spectralLocality := I.recovered.spectralLocality
  scale := I.recovered.scale
  areaCoeff := I.recovered.areaCoeff
  step := I.recovered.step
  descentRate := I.recovered.descentRate
  remainder := I.recovered.remainder
  total := I.recovered.total
  edge := I.recovered.edge
  candidate := I.recovered.candidate
  stepFloor := I.recovered.stepFloor
  weightBase := I.recovered.weightBase
  sourceBase := I.recovered.sourceBase
  residualGap := I.recovered.residualGap
  density := I.chartData.density
  density_tendsto_atTop := I.chartData.density_tendsto_atTop
  phiAtPoint := I.chartData.phiAtPoint
  curvaturePhi := I.chartData.curvaturePhi
  operatorData := I.chartData.operatorData
  exact_recovery := I.recovered.exact_recovery

theorem eventually_recoveredStage
    {cell chart point : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DChartInterface cell chart point) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.recovered.countWindow n) (I.recovered.curvatureBias n)
        (I.recovered.spectralLocality n)
        (I.recovered.scale n) (I.recovered.total n)
        (I.recovered.edge n) (I.recovered.candidate n) := by
  exact I.recovered.eventually_recoveredStage

theorem chart_operator_tendsto
    {cell chart point : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DChartInterface cell chart point) :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.chartData.operatorData (I.chartData.density n))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.chartData.operatorData)) := by
  exact
    I.chartData.operatorData.sampled_tendsto
      I.chartData.density I.chartData.density_tendsto_atTop

theorem rssPoissonError_zero_and_chart_operator_tendsto
    {cell chart point : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DChartInterface cell chart point)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.recovered.countWindow n i)
          (I.recovered.curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.chartData.operatorData (I.chartData.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.chartData.operatorData)) := by
  exact
    ⟨I.recovered.eventually_rssPoissonError_zero errorScale,
      I.chart_operator_tendsto⟩

theorem recoveredStage_and_chart_operator_tendsto
    {cell chart point : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DChartInterface cell chart point) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.recovered.countWindow n) (I.recovered.curvatureBias n)
        (I.recovered.spectralLocality n)
        (I.recovered.scale n) (I.recovered.total n)
        (I.recovered.edge n) (I.recovered.candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.chartData.operatorData (I.chartData.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.chartData.operatorData)) := by
  exact ⟨I.eventually_recoveredStage, I.chart_operator_tendsto⟩

theorem operator_interface_rssPoissonError_zero_and_operator_tendsto
    {cell chart point : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DChartInterface cell chart point)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.recovered.countWindow n i)
          (I.recovered.curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            (I.toOperatorInterface.operatorData)
            (I.toOperatorInterface.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.toOperatorInterface.operatorData)) := by
  simpa [toOperatorInterface]
    using I.toOperatorInterface.rssPoissonError_zero_and_operator_tendsto errorScale

#print axioms RecoveredStageExactCSpecSequence.eventually_recoveredStage
#print axioms RecoveredStageExactCSpecSequence.eventually_rssPoissonError_zero
#print axioms RecoveredStageExactCSpecSequence.exists_rssPoissonError_zero_after
#print axioms RecoveredStageBDG4DChartInterface.toOperatorInterface
#print axioms RecoveredStageBDG4DChartInterface.eventually_recoveredStage
#print axioms RecoveredStageBDG4DChartInterface.chart_operator_tendsto
#print axioms RecoveredStageBDG4DChartInterface.rssPoissonError_zero_and_chart_operator_tendsto
#print axioms RecoveredStageBDG4DChartInterface.recoveredStage_and_chart_operator_tendsto
#print axioms RecoveredStageBDG4DChartInterface.operator_interface_rssPoissonError_zero_and_operator_tendsto

end RecoveredStageBDG4DChartInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
