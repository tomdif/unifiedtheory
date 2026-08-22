/-
  Audit/KFCausalCSpecRecoveredStageBDG4DOperatorSplit.lean

  Split supplier for the recovered-stage 4D BDG operator profile package.

  `BDG4DOperatorProfileData` is the exact hypothesis stack consumed by the
  reduced 4D BDG operator theorem.  It is intentionally concrete, but it is
  too monolithic as a physical target: support bounds, derivative regularity,
  uniform estimates, and the cone bound are different analytic obligations.

  This file factors that monolithic record into smaller certificates and proves
  that they assemble back into `BDG4DOperatorProfileData`.  It also provides a
  scheduled-density recovered-chart interface that consumes the split analytic
  package.  The mathematical content is still conditional; the gain is that the
  remaining physical-law proof can now attack the operator stack component by
  component.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DScheduledDensity

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

/-- Function-level data for the reduced 4D operator profile. -/
structure BDG4DOperatorProfileFunctions where
  mbar : ℝ → ℝ → ℝ
  profile : ℝ → ℝ → ℝ
  profileU : ℝ → ℝ → ℝ
  profileUV : ℝ → ℝ → ℝ
  profileUVU : ℝ → ℝ → ℝ
  profileUVV : ℝ → ℝ → ℝ
  profileUU : ℝ → ℝ
  profileVV : ℝ → ℝ
  profile_def :
    ∀ u v, profile u v = mbar (-(u + v) / 2) ((v - u) / 2)
  even_mbar : ∀ t r, mbar t (-r) = mbar t r

/-- Scale and constant bounds for the reduced 4D operator profile. -/
structure BDG4DOperatorProfileScales where
  uSupport : ℝ
  vSupport : ℝ
  profileBound : ℝ
  profileDerivBound : ℝ
  mixedBound : ℝ
  mixedUDerivBound : ℝ
  mixedVDerivBound : ℝ
  coneBound : ℝ
  huSupport_pos : 0 < uSupport
  hvSupport_pos : 0 < vSupport

/-- Continuity and derivative regularity for the reduced 4D operator profile. -/
structure BDG4DOperatorProfileRegularity
    (F : BDG4DOperatorProfileFunctions) where
  profile_cont : Continuous (Function.uncurry F.profile)
  profileU_cont : Continuous (Function.uncurry F.profileU)
  profileUV_cont : Continuous (Function.uncurry F.profileUV)
  profile_deriv_u :
    ∀ v u, HasDerivAt (fun u' => F.profile u' v) (F.profileU u v) u
  profileU_deriv_v :
    ∀ u v, HasDerivAt (fun v' => F.profileU u v') (F.profileUV u v) v
  profileUV_deriv_u :
    ∀ v u, HasDerivAt (fun u' => F.profileUV u' v) (F.profileUVU u v) u
  profileUV_deriv_v :
    ∀ u v, HasDerivAt (fun v' => F.profileUV u v') (F.profileUVV u v) v
  profileVV_deriv :
    ∀ u, HasDerivAt F.profileVV (F.profileUVV u 0) u
  profileUU_deriv :
    ∀ v, HasDerivAt F.profileUU (F.profileUVU 0 v) v
  profileUVV_axis_cont : Continuous (fun u => F.profileUVV u 0)
  profileUVU_axis_cont : Continuous (fun v => F.profileUVU 0 v)

/-- Uniform profile, derivative, and mixed-derivative bounds. -/
structure BDG4DOperatorProfileUniformBounds
    (S : BDG4DOperatorProfileScales)
    (F : BDG4DOperatorProfileFunctions) where
  profile_bound : ∀ u v, |F.profile u v| ≤ S.profileBound
  profileU_bound : ∀ u v, |F.profileU u v| ≤ S.profileDerivBound
  profileUV_bound : ∀ u v, |F.profileUV u v| ≤ S.mixedBound
  profileUVU_bound : ∀ u v, |F.profileUVU u v| ≤ S.mixedUDerivBound
  profileUVV_bound : ∀ u v, |F.profileUVV u v| ≤ S.mixedVDerivBound

/-- Compact-support certificates for the profile and its relevant derivatives. -/
structure BDG4DOperatorProfileSupport
    (S : BDG4DOperatorProfileScales)
    (F : BDG4DOperatorProfileFunctions) where
  profile_support_u : ∀ u v, S.uSupport ≤ u → F.profile u v = 0
  profile_support_v : ∀ u v, S.vSupport ≤ v → F.profile u v = 0
  profileU_support_u : ∀ u v, S.uSupport ≤ u → F.profileU u v = 0
  profileU_support_v : ∀ u v, S.vSupport ≤ v → F.profileU u v = 0
  profileUV_support_u : ∀ u v, S.uSupport ≤ u → F.profileUV u v = 0
  profileUV_support_v : ∀ u v, S.vSupport ≤ v → F.profileUV u v = 0
  profileVV_support : ∀ u, S.uSupport ≤ u → F.profileVV u = 0
  profileUU_support : ∀ v, S.vSupport ≤ v → F.profileUU v = 0

/-- The cone-dominated-integrand estimate required by the reduced 4D theorem. -/
structure BDG4DOperatorProfileConeBound
    (S : BDG4DOperatorProfileScales)
    (F : BDG4DOperatorProfileFunctions) where
  hCcone : ∀ (a : ℝ), 0 < a → ∀ u v,
    |a * (v - u)^2 * f4D (a * u^2 * v^2) * F.profile u v| ≤
      S.coneBound * a

/-- Split analytic supplier for the reduced 4D BDG operator profile. -/
structure BDG4DOperatorProfileSplitData where
  scales : BDG4DOperatorProfileScales
  functions : BDG4DOperatorProfileFunctions
  regularity : BDG4DOperatorProfileRegularity functions
  uniformBounds : BDG4DOperatorProfileUniformBounds scales functions
  support : BDG4DOperatorProfileSupport scales functions
  coneBound : BDG4DOperatorProfileConeBound scales functions

namespace BDG4DOperatorProfileSplitData

/-- The split analytic supplier assembles into the monolithic operator-profile
data consumed by the existing 4D BDG theorem. -/
noncomputable def toProfileData
    (D : BDG4DOperatorProfileSplitData) : BDG4DOperatorProfileData where
  uSupport := D.scales.uSupport
  vSupport := D.scales.vSupport
  profileBound := D.scales.profileBound
  profileDerivBound := D.scales.profileDerivBound
  mixedBound := D.scales.mixedBound
  mixedUDerivBound := D.scales.mixedUDerivBound
  mixedVDerivBound := D.scales.mixedVDerivBound
  coneBound := D.scales.coneBound
  huSupport_pos := D.scales.huSupport_pos
  hvSupport_pos := D.scales.hvSupport_pos
  mbar := D.functions.mbar
  profile := D.functions.profile
  profileU := D.functions.profileU
  profileUV := D.functions.profileUV
  profileUVU := D.functions.profileUVU
  profileUVV := D.functions.profileUVV
  profileUU := D.functions.profileUU
  profileVV := D.functions.profileVV
  profile_def := D.functions.profile_def
  even_mbar := D.functions.even_mbar
  profile_cont := D.regularity.profile_cont
  profileU_cont := D.regularity.profileU_cont
  profileUV_cont := D.regularity.profileUV_cont
  profile_deriv_u := D.regularity.profile_deriv_u
  profileU_deriv_v := D.regularity.profileU_deriv_v
  profileUV_deriv_u := D.regularity.profileUV_deriv_u
  profileUV_deriv_v := D.regularity.profileUV_deriv_v
  profile_bound := D.uniformBounds.profile_bound
  profileU_bound := D.uniformBounds.profileU_bound
  profileUV_bound := D.uniformBounds.profileUV_bound
  profileUVU_bound := D.uniformBounds.profileUVU_bound
  profileUVV_bound := D.uniformBounds.profileUVV_bound
  hCcone := D.coneBound.hCcone
  profile_support_u := D.support.profile_support_u
  profile_support_v := D.support.profile_support_v
  profileU_support_u := D.support.profileU_support_u
  profileU_support_v := D.support.profileU_support_v
  profileUV_support_u := D.support.profileUV_support_u
  profileUV_support_v := D.support.profileUV_support_v
  profileVV_deriv := D.regularity.profileVV_deriv
  profileUU_deriv := D.regularity.profileUU_deriv
  profileUVV_axis_cont := D.regularity.profileUVV_axis_cont
  profileUVU_axis_cont := D.regularity.profileUVU_axis_cont
  profileVV_support := D.support.profileVV_support
  profileUU_support := D.support.profileUU_support

theorem tendsto (D : BDG4DOperatorProfileSplitData) :
    Tendsto
      (BDG4DOperatorProfileData.mean D.toProfileData)
      atTop
      (𝓝 (BDG4DOperatorProfileData.target D.toProfileData)) := by
  exact D.toProfileData.tendsto

theorem sampled_tendsto
    (D : BDG4DOperatorProfileSplitData)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop) :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean D.toProfileData (density n))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target D.toProfileData)) := by
  exact D.toProfileData.sampled_tendsto density hdensity

theorem sequenceAsymptotics_layer_asymptotics
    (D : BDG4DOperatorProfileSplitData)
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
    D.toProfileData.sequenceAsymptotics_layer_asymptotics
      density hdensity phiAtPoint curvaturePhi

end BDG4DOperatorProfileSplitData

/-- A scheduled-density recovered chart supplier whose 4D operator profile is
given by split support, regularity, bounds, and cone certificates. -/
structure RecoveredStageBDG4DScheduledDensitySplitOperatorInterface
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
  operatorSplitData : BDG4DOperatorProfileSplitData

namespace RecoveredStageBDG4DScheduledDensitySplitOperatorInterface

/-- The split-operator supplier instantiates the scheduled-density bridge by
assembling its analytic profile certificates. -/
noncomputable def toScheduledDensityInterface
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensitySplitOperatorInterface cell X Y chart) :
    RecoveredStageBDG4DScheduledDensityInterface cell X Y chart where
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
  operatorData := I.operatorSplitData.toProfileData

theorem density_tendsto_atTop
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensitySplitOperatorInterface cell X Y chart) :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop := by
  exact I.toScheduledDensityInterface.density_tendsto_atTop

theorem chart_operator_tendsto
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensitySplitOperatorInterface cell X Y chart) :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorSplitData.toProfileData ((I.chartCertificate n).density))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorSplitData.toProfileData)) := by
  exact I.toScheduledDensityInterface.chart_operator_tendsto

theorem rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensitySplitOperatorInterface cell X Y chart)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.recovered.countWindow n i)
          (I.recovered.curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.operatorSplitData.toProfileData ((I.chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorSplitData.toProfileData)) ∧
      Tendsto (fun n => (I.chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  exact
    RecoveredStageBDG4DScheduledDensityInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
      I.toScheduledDensityInterface errorScale

theorem recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensitySplitOperatorInterface cell X Y chart) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.recovered.countWindow n) (I.recovered.curvatureBias n)
        (I.recovered.spectralLocality n)
        (I.recovered.scale n) (I.recovered.total n)
        (I.recovered.edge n) (I.recovered.candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            I.operatorSplitData.toProfileData ((I.chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorSplitData.toProfileData)) ∧
      Tendsto (fun n => (I.chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  exact
    RecoveredStageBDG4DScheduledDensityInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
      I.toScheduledDensityInterface

#print axioms BDG4DOperatorProfileSplitData.toProfileData
#print axioms BDG4DOperatorProfileSplitData.tendsto
#print axioms BDG4DOperatorProfileSplitData.sampled_tendsto
#print axioms BDG4DOperatorProfileSplitData.sequenceAsymptotics_layer_asymptotics
#print axioms RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.toScheduledDensityInterface
#print axioms RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.density_tendsto_atTop
#print axioms RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.chart_operator_tendsto
#print axioms RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
#print axioms RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero

end RecoveredStageBDG4DScheduledDensitySplitOperatorInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
