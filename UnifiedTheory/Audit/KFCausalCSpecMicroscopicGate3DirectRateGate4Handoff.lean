/-
  Audit/KFCausalCSpecMicroscopicGate3DirectRateGate4Handoff.lean

  Normalized-compatible Gate 3 to Gate 4 handoff.

  The existing recovered-chart interfaces store a
  `PhysicalHauptvermutungExactRecoveryCertificate`, whose convergence field
  uses the componentwise positive centered-source floor ruled out for
  nonnegative normalized weights.  This module does not construct that
  certificate.  It combines the direct aggregate-rate Gate 3 supplier with
  the same matched physical-chart, affine-density, and kernel/profile data,
  and proves the Gate 4 outputs directly from eventual exact recovery.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRateGate4Handoff

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

/-- Direct aggregate-rate Gate 3 data together with the strongest scheduled
physical-chart/kernel supplier currently consumed by Gate 4.

Unlike `RecoveredStageBDG4DScheduledDensityKernelOperatorInterface`, this
record stores no `RecoveredStageExactCSpecSequence` and therefore no
`PhysicalHauptvermutungConvergenceCertificate`. -/
structure MicroscopicGate3DirectRateGate4ScheduledKernelData
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (rateBase stepFloor countGap curvatureGap spectralGap : ℝ) where
  gate3 :
    MicroscopicGate3StoppableDirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap
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

namespace MicroscopicGate3DirectRateGate4ScheduledKernelData

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}

variable
  (I : MicroscopicGate3DirectRateGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    w J source countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    rateBase stepFloor countGap curvatureGap spectralGap)

include I

/-- The direct-rate supplier reaches the operational recovered-stage predicate
without passing through the impossible normalized component-floor
certificate. -/
theorem eventually_recoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact
    MicroscopicGate3StoppableDirectRateQuantizedData.eventually_recoveredStage
      I.gate3

/-- Exact direct-rate recovery kills the RSS/Poisson horizon-error channel. -/
theorem eventually_rssPoissonError_zero (errorScale : ℝ) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  filter_upwards [eventually_recoveredStage I] with n hn
  intro i
  exact
    PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero hn
      (I.gate3.count_nonneg n) (I.gate3.curvature_nonneg n)
      (I.gate3.spectral_nonneg n) i

/-- Matched count residuals vanish along the direct-rate recovered tail. -/
theorem countWindow_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).countWindow) atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).countWindow := by
    filter_upwards [I.gate3.eventually_exact_zero] with n hn
    rcases hn with ⟨_, hcount, _, _, _⟩
    rw [I.countWindow_eq_sum n]
    symm
    exact Finset.sum_eq_zero (fun i _ => hcount i)
  exact tendsto_const_nhds.congr' heq

/-- Matched curvature residuals vanish along the direct-rate recovered tail. -/
theorem curvatureBias_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).curvatureBias) atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).curvatureBias := by
    filter_upwards [I.gate3.eventually_exact_zero] with n hn
    rcases hn with ⟨_, _, hcurvature, _, _⟩
    rw [I.curvatureBias_eq_sum n]
    symm
    exact Finset.sum_eq_zero (fun i _ => hcurvature i)
  exact tendsto_const_nhds.congr' heq

/-- The matched spectral residual supplies the chart pair-consistency tail. -/
theorem pairConsistency_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).pairConsistency) atTop (𝓝 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).pairConsistency := by
    filter_upwards [I.gate3.eventually_exact_zero] with n hn
    rcases hn with ⟨_, _, _, hspectral, _⟩
    rw [I.pairConsistency_eq_spectral_sum n]
    symm
    exact Finset.sum_eq_zero (fun i _ => hspectral i)
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

/-- Matched direct-rate residuals make the physical chart distortion collapse. -/
theorem chartDistortion_tendsto_zero :
    Tendsto
      (fun n => (I.chartCertificate n).distortionBound)
      atTop (𝓝 0) := by
  exact
    PhysicalGrowthHauptvermutungCertificate.certificate_distortionBound_tendsto_zero
      I.chartCertificate I.fixedScale I.scale_eq
      I.countWindow_tendsto_zero I.curvatureBias_tendsto_zero
      I.pairConsistency_tendsto_zero

/-- Named closure package for the normalized-compatible direct-rate Gate 3 to
scheduled-kernel Gate 4 handoff. -/
structure Closed (errorScale : ℝ) : Prop where
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

/-- The direct-rate Gate 3 data and scheduled chart/kernel supplier close the
finite Gate 3 to Gate 4 handoff without constructing a strong convergence
certificate. -/
theorem closed (errorScale : ℝ) : I.Closed errorScale where
  eventualRecoveredStage := eventually_recoveredStage I
  rssPoissonErrorZero := eventually_rssPoissonError_zero I errorScale
  chartOperatorLimit := I.chart_operator_tendsto
  chartDistortionTendsToZero := I.chartDistortion_tendsto_zero
  scheduledDensityTendsToInfinity := I.density_tendsto_atTop

/-- All observable handoff outputs in one theorem. -/
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

#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.eventually_recoveredStage
#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.eventually_rssPoissonError_zero
#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.density_tendsto_atTop
#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.chart_operator_tendsto
#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.chartDistortion_tendsto_zero
#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.closed
#print axioms MicroscopicGate3DirectRateGate4ScheduledKernelData.outputs

end MicroscopicGate3DirectRateGate4ScheduledKernelData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRateGate4Handoff
