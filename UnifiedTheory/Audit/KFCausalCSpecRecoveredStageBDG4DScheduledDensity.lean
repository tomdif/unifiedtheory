/-
  Audit/KFCausalCSpecRecoveredStageBDG4DScheduledDensity.lean

  Scheduled-density bridge for the recovered-stage 4D BDG physical chart.

  The matched physical-chart interface still required the chart-certificate
  density sequence to tend to infinity.  This file replaces that bare
  convergence input with an explicit affine refinement schedule:

      density_n = densityBase + densityStep * n,   densityStep > 0.

  Lean proves that this schedule tends to `atTop`, then feeds the result into
  the matched residual chart bridge.  The remaining Gate 4 analytic obligation
  is therefore narrowed again: build the finite physical chart certificates,
  prove their residual matching identities, and supply the
  `BDG4DOperatorProfileData` support/regularity/cone-bound package.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DMatchedChart

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

/-- A positive affine density schedule tends to infinite sprinkling density. -/
theorem affineDensity_tendsto_atTop (densityBase densityStep : ℝ)
    (hdensityStep : 0 < densityStep) :
    Tendsto
      (fun n : ℕ => densityBase + densityStep * (n : ℝ))
      atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  rcases exists_nat_gt ((b - densityBase) / densityStep) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hN' : (b - densityBase) / densityStep < (N : ℝ) := hN
  have hbN_raw : b - densityBase < (N : ℝ) * densityStep :=
    (div_lt_iff₀ hdensityStep).mp hN'
  have hbN : b - densityBase < densityStep * (N : ℝ) := by
    simpa [mul_comm] using hbN_raw
  have hNn : densityStep * (N : ℝ) ≤ densityStep * (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hdensityStep.le
  linarith

/-- A matched physical chart supplier whose density is fixed by a positive
affine refinement schedule. -/
structure RecoveredStageBDG4DScheduledDensityInterface
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
  densityBase : ℝ
  densityStep : ℝ
  densityStep_pos : 0 < densityStep
  density_eq_affine :
    ∀ n, (chartCertificate n).density =
      densityBase + densityStep * (n : ℝ)
  coord : Y → Fin 4 → ℝ
  chartOfCell : cell → chart
  sampleEvent : ℕ → cell → X
  phiAtPoint : ℝ
  curvaturePhi : ℝ
  operatorData : BDG4DOperatorProfileData

namespace RecoveredStageBDG4DScheduledDensityInterface

theorem density_tendsto_atTop
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop := by
  have h :=
    affineDensity_tendsto_atTop
      I.densityBase I.densityStep I.densityStep_pos
  have heq :
      (fun n : ℕ => I.densityBase + I.densityStep * (n : ℝ))
        =ᶠ[atTop] fun n => (I.chartCertificate n).density :=
    Filter.Eventually.of_forall (fun n => (I.density_eq_affine n).symm)
  exact h.congr' heq

/-- The scheduled-density supplier instantiates the matched physical-chart
interface without a separate density convergence assumption. -/
noncomputable def toMatchedPhysicalChartInterface
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityInterface cell X Y chart) :
    RecoveredStageBDG4DMatchedPhysicalChartInterface cell X Y chart where
  recovered := I.recovered
  chartCertificate := I.chartCertificate
  fixedScale := I.fixedScale
  scale_eq := I.scale_eq
  countWindow_eq_sum := I.countWindow_eq_sum
  curvatureBias_eq_sum := I.curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := I.pairConsistency_eq_spectral_sum
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
    (I : RecoveredStageBDG4DScheduledDensityInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (𝓝 0) := by
  exact I.toMatchedPhysicalChartInterface.distortionBound_tendsto_zero

theorem chart_operator_tendsto
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityInterface cell X Y chart) :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorData ((I.chartCertificate n).density))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) := by
  exact I.toMatchedPhysicalChartInterface.toPhysicalChartInterface.chart_operator_tendsto

theorem rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityInterface cell X Y chart)
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
  simpa [toMatchedPhysicalChartInterface]
    using
      RecoveredStageBDG4DMatchedPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
        I.toMatchedPhysicalChartInterface errorScale

theorem recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityInterface cell X Y chart) :
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
  simpa [toMatchedPhysicalChartInterface]
    using
      RecoveredStageBDG4DMatchedPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
        I.toMatchedPhysicalChartInterface

#print axioms affineDensity_tendsto_atTop
#print axioms RecoveredStageBDG4DScheduledDensityInterface.density_tendsto_atTop
#print axioms RecoveredStageBDG4DScheduledDensityInterface.toMatchedPhysicalChartInterface
#print axioms RecoveredStageBDG4DScheduledDensityInterface.distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DScheduledDensityInterface.chart_operator_tendsto
#print axioms RecoveredStageBDG4DScheduledDensityInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DScheduledDensityInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero

end RecoveredStageBDG4DScheduledDensityInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
