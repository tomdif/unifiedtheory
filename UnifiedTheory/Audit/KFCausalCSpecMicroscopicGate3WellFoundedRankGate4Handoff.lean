/-
  Audit/KFCausalCSpecMicroscopicGate3WellFoundedRankGate4Handoff.lean

  Well-founded finite-rank Gate 3 to scheduled-kernel Gate 4 handoff.

  The Gate 3 input reaches exact recovery at the explicit stage equal to its
  initial natural-valued defect rank.  This file transfers that bounded result
  to exact chart-residual zero, exact chart-distortion zero, RSS/Poisson zero,
  and the existing eventual forms.  The affine density schedule and active
  BDG kernel/profile supplier independently provide the density and operator
  limits required by Gate 4.

  No real contraction factor, asymptotic Gate 3 convergence, or legacy exact-
  recovery certificate is used.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRankGate4Handoff

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank

/-- Well-founded finite-rank Gate 3 data together with the scheduled physical
chart, affine density, and active kernel/profile data consumed by Gate 4. -/
structure MicroscopicGate3WellFoundedRankGate4ScheduledKernelData
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (countGap curvatureGap spectralGap : ℝ) where
  gate3 :
    MicroscopicGate3WellFoundedRankData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap
  chartCertificate :
    ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart
  fixedScale : ℝ
  scale_eq : ∀ n, (chartCertificate n).scale = fixedScale
  countWindow_eq_sum :
    ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i
  curvatureBias_eq_sum :
    ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i
  pairConsistency_eq_spectral_sum :
    ∀ n, (chartCertificate n).pairConsistency =
      ∑ i, spectralLocality n i
  densityBase : ℝ
  densityStep : ℝ
  densityStep_pos : 0 < densityStep
  density_eq_affine :
    ∀ n, (chartCertificate n).density =
      densityBase + densityStep * (n : ℝ)
  operatorKernelData : BDG4DOperatorProfileKernelSplitData

namespace MicroscopicGate3WellFoundedRankGate4ScheduledKernelData

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

variable
  (I : MicroscopicGate3WellFoundedRankGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    w J source countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

include I

/-- The concrete Gate 3 recovery bound consumed by this handoff. -/
noncomputable def recoveryBound : ℕ := I.gate3.defectRank 0

/-- All physical residual channels and bridge transport are exactly recovered
from the explicit finite rank bound onward. -/
theorem exact_zero_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  exact I.gate3.exact_zero_after_initial_defectRank

/-- The operational recovered-stage predicate holds from the same explicit
bound onward. -/
theorem recoveredStage_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact I.gate3.recoveredStage_after_initial_defectRank

/-- The three matched chart-certificate residuals are literally zero after
the initial-rank recovery time. -/
theorem chartResiduals_zero_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      (I.chartCertificate n).countWindow = 0 ∧
        (I.chartCertificate n).curvatureBias = 0 ∧
          (I.chartCertificate n).pairConsistency = 0 := by
  intro n hn
  rcases I.exact_zero_after_recoveryBound n hn with
    ⟨_, hcount, hcurvature, hspectral, _⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [I.countWindow_eq_sum n]
    exact Finset.sum_eq_zero (fun i _ => hcount i)
  · rw [I.curvatureBias_eq_sum n]
    exact Finset.sum_eq_zero (fun i _ => hcurvature i)
  · rw [I.pairConsistency_eq_spectral_sum n]
    exact Finset.sum_eq_zero (fun i _ => hspectral i)

/-- The displayed quantitative-Hauptvermutung chart distortion is exactly
zero after the finite recovery time, not merely convergent to zero. -/
theorem chartDistortion_zero_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      (I.chartCertificate n).distortionBound = 0 := by
  intro n hn
  rcases I.chartResiduals_zero_after_recoveryBound n hn with
    ⟨hcount, hcurvature, hpair⟩
  simp [PhysicalGrowthHauptvermutungCertificate.distortionBound,
    hcount, hcurvature, hpair]

/-- Exact recovery kills the RSS/Poisson horizon-error channel from the same
explicit finite stage onward. -/
theorem rssPoissonError_zero_after_recoveryBound (errorScale : ℝ) :
    ∀ n, I.recoveryBound ≤ n →
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  intro n hn i
  exact
    PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero
      (I.recoveredStage_after_recoveryBound n hn)
      (I.gate3.count_nonneg n) (I.gate3.curvature_nonneg n)
      (I.gate3.spectral_nonneg n) i

/-- Explicitly bounded recovery implies the filter-form operational recovery
consumed by existing Gate 4 interfaces. -/
theorem eventually_recoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  rw [eventually_atTop]
  exact ⟨I.recoveryBound, I.recoveredStage_after_recoveryBound⟩

/-- Filter-form exact residual and bridge recovery with the explicit rank bound
as witness. -/
theorem eventually_exact_zero :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  rw [eventually_atTop]
  exact ⟨I.recoveryBound, I.exact_zero_after_recoveryBound⟩

/-- The RSS/Poisson error is eventually zero, with the initial defect rank as
an explicit valid threshold. -/
theorem eventually_rssPoissonError_zero (errorScale : ℝ) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  rw [eventually_atTop]
  exact ⟨I.recoveryBound, I.rssPoissonError_zero_after_recoveryBound errorScale⟩

/-- The chart count residual is eventually exactly zero, hence tends to zero. -/
theorem countWindow_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).countWindow) atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).countWindow := by
    filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
    exact (I.chartResiduals_zero_after_recoveryBound n hn).1.symm
  exact tendsto_const_nhds.congr' heq

/-- The chart curvature residual is eventually exactly zero, hence tends to
zero. -/
theorem curvatureBias_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).curvatureBias) atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).curvatureBias := by
    filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
    exact (I.chartResiduals_zero_after_recoveryBound n hn).2.1.symm
  exact tendsto_const_nhds.congr' heq

/-- The chart pair-consistency residual is eventually exactly zero, hence
tends to zero. -/
theorem pairConsistency_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).pairConsistency) atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).pairConsistency := by
    filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
    exact (I.chartResiduals_zero_after_recoveryBound n hn).2.2.symm
  exact tendsto_const_nhds.congr' heq

/-- Exact post-bound chart distortion supplies its zero limit directly. -/
theorem chartDistortion_tendsto_zero :
    Tendsto
      (fun n => (I.chartCertificate n).distortionBound)
      atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).distortionBound := by
    filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
    exact (I.chartDistortion_zero_after_recoveryBound n hn).symm
  exact tendsto_const_nhds.congr' heq

/-- The positive affine physical-chart density schedule diverges. -/
theorem density_tendsto_atTop :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop := by
  have h :=
    affineDensity_tendsto_atTop
      I.densityBase I.densityStep I.densityStep_pos
  have heq :
      (fun n : ℕ => I.densityBase + I.densityStep * (n : ℝ))
        =ᶠ[atTop] fun n => (I.chartCertificate n).density :=
    Filter.Eventually.of_forall (fun n => (I.density_eq_affine n).symm)
  exact h.congr' heq

/-- The active kernel/profile supplier converges when sampled at the scheduled
physical-chart density. -/
theorem chart_operator_tendsto :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorKernelData.toProfileData
          ((I.chartCertificate n).density))
      atTop
      (𝓝
        (BDG4DOperatorProfileData.target
          I.operatorKernelData.toProfileData)) := by
  exact
    I.operatorKernelData.sampled_tendsto
      (fun n => (I.chartCertificate n).density) I.density_tendsto_atTop

/-- Closure package retaining both the explicit finite recovery bound and the
standard eventual/limit outputs used downstream. -/
structure Closed (errorScale : ℝ) : Prop where
  exactZeroAfterRecoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n)
  recoveredStageAfterRecoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  chartResidualsZeroAfterRecoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      (I.chartCertificate n).countWindow = 0 ∧
        (I.chartCertificate n).curvatureBias = 0 ∧
          (I.chartCertificate n).pairConsistency = 0
  chartDistortionZeroAfterRecoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      (I.chartCertificate n).distortionBound = 0
  rssPoissonErrorZeroAfterRecoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0
  eventualRecoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  rssPoissonErrorZero :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0
  chartOperatorLimit :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorKernelData.toProfileData
          ((I.chartCertificate n).density))
      atTop
      (𝓝
        (BDG4DOperatorProfileData.target
          I.operatorKernelData.toProfileData))
  chartDistortionTendsToZero :
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (𝓝 0)
  scheduledDensityTendsToInfinity :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop

theorem closed (errorScale : ℝ) : I.Closed errorScale where
  exactZeroAfterRecoveryBound := I.exact_zero_after_recoveryBound
  recoveredStageAfterRecoveryBound := I.recoveredStage_after_recoveryBound
  chartResidualsZeroAfterRecoveryBound :=
    I.chartResiduals_zero_after_recoveryBound
  chartDistortionZeroAfterRecoveryBound :=
    I.chartDistortion_zero_after_recoveryBound
  rssPoissonErrorZeroAfterRecoveryBound :=
    I.rssPoissonError_zero_after_recoveryBound errorScale
  eventualRecoveredStage := I.eventually_recoveredStage
  rssPoissonErrorZero := I.eventually_rssPoissonError_zero errorScale
  chartOperatorLimit := I.chart_operator_tendsto
  chartDistortionTendsToZero := I.chartDistortion_tendsto_zero
  scheduledDensityTendsToInfinity := I.density_tendsto_atTop

/-- Standard downstream observable outputs, matching the existing Gate 4
handoff shape. -/
theorem outputs (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      (∀ᶠ n in atTop,
        ∀ i,
          rssPoissonError
            (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
        Tendsto
          (fun n =>
            BDG4DOperatorProfileData.mean
              I.operatorKernelData.toProfileData
              ((I.chartCertificate n).density))
          atTop
          (𝓝
            (BDG4DOperatorProfileData.target
              I.operatorKernelData.toProfileData)) ∧
          Tendsto (fun n => (I.chartCertificate n).distortionBound)
            atTop (𝓝 0) ∧
            Tendsto (fun n => (I.chartCertificate n).density) atTop atTop := by
  have H := I.closed errorScale
  exact
    ⟨H.eventualRecoveredStage, H.rssPoissonErrorZero,
      H.chartOperatorLimit, H.chartDistortionTendsToZero,
      H.scheduledDensityTendsToInfinity⟩

#print axioms exact_zero_after_recoveryBound
#print axioms recoveredStage_after_recoveryBound
#print axioms chartResiduals_zero_after_recoveryBound
#print axioms chartDistortion_zero_after_recoveryBound
#print axioms rssPoissonError_zero_after_recoveryBound
#print axioms eventually_recoveredStage
#print axioms eventually_rssPoissonError_zero
#print axioms chartDistortion_tendsto_zero
#print axioms density_tendsto_atTop
#print axioms chart_operator_tendsto
#print axioms closed
#print axioms outputs

end MicroscopicGate3WellFoundedRankGate4ScheduledKernelData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRankGate4Handoff
