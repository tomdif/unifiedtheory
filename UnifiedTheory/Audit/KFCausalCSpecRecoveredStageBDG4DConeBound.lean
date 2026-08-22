/-
  Audit/KFCausalCSpecRecoveredStageBDG4DConeBound.lean

  Kernel/profile split for the reduced 4D BDG cone-bound certificate.

  The split operator profile package still contained one combined cone estimate
  over the product of the 4D BDG kernel profile and the supplied chart profile.
  This file factors that estimate into:

  * a kernel-only weighted bound for `(v - u)^2 * f4D (a*u^2*v^2)`;
  * the existing uniform bound for the chart profile;
  * one scale calibration inequality saying the chosen cone constant dominates
    the product of those two bounds.

  This does not prove the analytic kernel estimate yet.  It makes the remaining
  analytic obligation sharper and reusable, and proves that once supplied it
  instantiates the scheduled-density recovered-chart bridge.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DOperatorSplit

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

/-- A profile-independent weighted bound for the 4D BDG kernel factor that
appears in the reduced cone estimate. -/
structure BDG4DWeightedKernelBound where
  weightedConeBound : ℝ
  weightedConeBound_nonneg : 0 ≤ weightedConeBound
  weighted_f4D_bound : ∀ (a : ℝ), 0 < a → ∀ u v,
    |(v - u)^2 * f4D (a * u^2 * v^2)| ≤ weightedConeBound

namespace BDG4DOperatorProfileConeBound

/-- A weighted kernel bound and a uniform chart-profile bound imply the combined
cone estimate, provided the chosen cone scale dominates the product of the two
component bounds. -/
theorem of_weightedKernelBound
    {S : BDG4DOperatorProfileScales}
    {F : BDG4DOperatorProfileFunctions}
    (U : BDG4DOperatorProfileUniformBounds S F)
    (K : BDG4DWeightedKernelBound)
    (hcone : K.weightedConeBound * S.profileBound ≤ S.coneBound) :
    BDG4DOperatorProfileConeBound S F where
  hCcone := by
    intro a ha u v
    set z : ℝ := a * u^2 * v^2
    set k : ℝ := (v - u)^2 * f4D z
    have hk : |k| ≤ K.weightedConeBound := by
      simpa [k, z] using K.weighted_f4D_bound a ha u v
    have hp : |F.profile u v| ≤ S.profileBound := U.profile_bound u v
    have hprod :
        |k| * |F.profile u v| ≤ K.weightedConeBound * S.profileBound :=
      mul_le_mul hk hp (abs_nonneg _) K.weightedConeBound_nonneg
    calc
      |a * (v - u)^2 * f4D (a * u^2 * v^2) * F.profile u v|
          = |a * k * F.profile u v| := by
              simp [k, z, mul_assoc]
      _ = a * (|k| * |F.profile u v|) := by
              rw [abs_mul, abs_mul, abs_of_pos ha]
              ring
      _ ≤ a * (K.weightedConeBound * S.profileBound) :=
              mul_le_mul_of_nonneg_left hprod ha.le
      _ ≤ a * S.coneBound :=
              mul_le_mul_of_nonneg_left hcone ha.le
      _ = S.coneBound * a := by
              ring

end BDG4DOperatorProfileConeBound

/-- Split analytic supplier where the cone-bound certificate is replaced by a
kernel-only weighted estimate plus the profile sup bound. -/
structure BDG4DOperatorProfileKernelSplitData where
  scales : BDG4DOperatorProfileScales
  functions : BDG4DOperatorProfileFunctions
  regularity : BDG4DOperatorProfileRegularity functions
  uniformBounds : BDG4DOperatorProfileUniformBounds scales functions
  support : BDG4DOperatorProfileSupport scales functions
  kernelBound : BDG4DWeightedKernelBound
  coneBound_ge :
    kernelBound.weightedConeBound * scales.profileBound ≤ scales.coneBound

namespace BDG4DOperatorProfileKernelSplitData

/-- The kernel/profile split supplies the cone certificate required by the
previous operator split. -/
noncomputable def coneBound
    (D : BDG4DOperatorProfileKernelSplitData) :
    BDG4DOperatorProfileConeBound D.scales D.functions :=
  BDG4DOperatorProfileConeBound.of_weightedKernelBound
    D.uniformBounds D.kernelBound D.coneBound_ge

/-- Assemble the kernel/profile split into the prior split profile package. -/
noncomputable def toSplitData
    (D : BDG4DOperatorProfileKernelSplitData) :
    BDG4DOperatorProfileSplitData where
  scales := D.scales
  functions := D.functions
  regularity := D.regularity
  uniformBounds := D.uniformBounds
  support := D.support
  coneBound := D.coneBound

/-- The kernel/profile split assembles into the monolithic operator-profile
data consumed by the reduced 4D BDG theorem. -/
noncomputable def toProfileData
    (D : BDG4DOperatorProfileKernelSplitData) : BDG4DOperatorProfileData :=
  D.toSplitData.toProfileData

theorem tendsto (D : BDG4DOperatorProfileKernelSplitData) :
    Tendsto
      (BDG4DOperatorProfileData.mean D.toProfileData)
      atTop
      (𝓝 (BDG4DOperatorProfileData.target D.toProfileData)) := by
  exact D.toSplitData.tendsto

theorem sampled_tendsto
    (D : BDG4DOperatorProfileKernelSplitData)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop) :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean D.toProfileData (density n))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target D.toProfileData)) := by
  exact D.toSplitData.sampled_tendsto density hdensity

theorem sequenceAsymptotics_layer_asymptotics
    (D : BDG4DOperatorProfileKernelSplitData)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ) :
    ∀ i ∈
      (D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layers,
      Tendsto
        ((D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layerMean i)
        atTop
        (𝓝
          ((D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layerConstant i *
              (D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).phiAtPoint +
            (D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layerSecond i *
              ((D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).boxPhi +
                (D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).curvatureCoeff *
                  (D.toProfileData.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).curvaturePhi))) := by
  exact
    D.toSplitData.sequenceAsymptotics_layer_asymptotics
      density hdensity phiAtPoint curvaturePhi

end BDG4DOperatorProfileKernelSplitData

/-- A scheduled-density recovered chart supplier whose operator package is
reduced to function/support/regularity data plus a kernel-only cone estimate. -/
structure RecoveredStageBDG4DScheduledDensityKernelOperatorInterface
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
  operatorKernelData : BDG4DOperatorProfileKernelSplitData

namespace RecoveredStageBDG4DScheduledDensityKernelOperatorInterface

/-- Assemble the kernel/profile split into the previous scheduled-density split
operator interface. -/
noncomputable def toSplitOperatorInterface
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface cell X Y chart) :
    RecoveredStageBDG4DScheduledDensitySplitOperatorInterface cell X Y chart where
  recovered := I.recovered
  chartCertificate := I.chartCertificate
  fixedScale := I.fixedScale
  scale_eq := I.scale_eq
  countWindow_eq_sum := I.countWindow_eq_sum
  curvatureBias_eq_sum := I.curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := I.pairConsistency_eq_spectral_sum
  densityBase := I.densityBase
  densityStep := I.densityStep
  densityStep_pos := I.densityStep_pos
  density_eq_affine := I.density_eq_affine
  coord := I.coord
  chartOfCell := I.chartOfCell
  sampleEvent := I.sampleEvent
  phiAtPoint := I.phiAtPoint
  curvaturePhi := I.curvaturePhi
  operatorSplitData := I.operatorKernelData.toSplitData

/-- The affine scheduled density still tends to infinity after the kernel/profile
operator split. -/
theorem density_tendsto_atTop
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop := by
  exact I.toSplitOperatorInterface.density_tendsto_atTop

/-- The recovered chart samples the reduced 4D operator at the scheduled
density and converges to the profile target. -/
theorem chart_operator_tendsto
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface cell X Y chart) :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorKernelData.toProfileData ((I.chartCertificate n).density))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorKernelData.toProfileData)) := by
  exact I.toSplitOperatorInterface.chart_operator_tendsto

theorem rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface cell X Y chart)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.recovered.countWindow n i)
          (I.recovered.curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.operatorKernelData.toProfileData ((I.chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorKernelData.toProfileData)) ∧
      Tendsto (fun n => (I.chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  exact
    RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
      I.toSplitOperatorInterface errorScale

theorem recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface cell X Y chart) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.recovered.countWindow n) (I.recovered.curvatureBias n)
        (I.recovered.spectralLocality n)
        (I.recovered.scale n) (I.recovered.total n)
        (I.recovered.edge n) (I.recovered.candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.operatorKernelData.toProfileData ((I.chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorKernelData.toProfileData)) ∧
      Tendsto (fun n => (I.chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  exact
    RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
      I.toSplitOperatorInterface

#print axioms BDG4DOperatorProfileConeBound.of_weightedKernelBound
#print axioms BDG4DOperatorProfileKernelSplitData.coneBound
#print axioms BDG4DOperatorProfileKernelSplitData.toSplitData
#print axioms BDG4DOperatorProfileKernelSplitData.toProfileData
#print axioms BDG4DOperatorProfileKernelSplitData.sampled_tendsto
#print axioms RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.toSplitOperatorInterface
#print axioms RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.chart_operator_tendsto
#print axioms RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero

end RecoveredStageBDG4DScheduledDensityKernelOperatorInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
