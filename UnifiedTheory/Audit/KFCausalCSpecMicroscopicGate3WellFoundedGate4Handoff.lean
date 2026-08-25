/-
  Audit/KFCausalCSpecMicroscopicGate3WellFoundedGate4Handoff.lean

  Finite-time Gate 3 to Gate 4 handoff driven by a natural-valued defect rank.

  This is the viable counterpart of the direct-rate handoff.  It assumes only
  the certified horizon-preserving repair refinement, positive quantization
  gaps, exact counter representations, and strict descent of the discrete
  defect rank away from zero.  Exact recovery and every limiting statement
  below are conclusions.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedGate4Handoff

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank

/-- Well-founded Gate 3 data bundled with the scheduled physical-chart and
kernel supplier consumed by Gate 4.  In contrast with the legacy supplier,
this record contains no real-convergence certificate and no recovery field. -/
structure MicroscopicGate3WellFoundedGate4ScheduledKernelData
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
    ∀ n, (chartCertificate n).pairConsistency = ∑ i, spectralLocality n i
  densityBase : ℝ
  densityStep : ℝ
  densityStep_pos : 0 < densityStep
  density_eq_affine :
    ∀ n, (chartCertificate n).density =
      densityBase + densityStep * (n : ℝ)
  operatorKernelData : BDG4DOperatorProfileKernelSplitData

namespace MicroscopicGate3WellFoundedGate4ScheduledKernelData

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

variable
  (I : MicroscopicGate3WellFoundedGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    w J source countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

include I

/-- Gate 3 recovery occurs permanently after the explicit natural-number
bound given by the initial defect rank. -/
theorem recoveredStage_after_initial_defectRank :
    ∀ n, I.gate3.defectRank 0 ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact I.gate3.recoveredStage_after_initial_defectRank

/-- The same finite bound supplies the filter-form tail expected by Gate 4. -/
theorem eventually_recoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact I.gate3.eventually_recoveredStage

/-- Exact recovery kills the RSS/Poisson error channel after the explicit
rank bound. -/
theorem rssPoissonError_zero_after_initial_defectRank (errorScale : ℝ) :
    ∀ n, I.gate3.defectRank 0 ≤ n → ∀ i,
      rssPoissonError
        (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  intro n hn i
  exact
    (I.recoveredStage_after_initial_defectRank n hn).rssPoissonError_zero
      (I.gate3.count_nonneg n) (I.gate3.curvature_nonneg n)
      (I.gate3.spectral_nonneg n) i

theorem eventually_rssPoissonError_zero (errorScale : ℝ) :
    ∀ᶠ n in atTop, ∀ i,
      rssPoissonError
        (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  rw [eventually_atTop]
  exact
    ⟨I.gate3.defectRank 0,
      I.rssPoissonError_zero_after_initial_defectRank errorScale⟩

theorem countWindow_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).countWindow) atTop (nhds 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).countWindow := by
    filter_upwards [I.gate3.eventually_exact_zero] with n hn
    rcases hn with ⟨_, hcount, _, _, _⟩
    rw [I.countWindow_eq_sum n]
    symm
    exact Finset.sum_eq_zero (fun i _ => hcount i)
  exact tendsto_const_nhds.congr' heq

theorem curvatureBias_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).curvatureBias) atTop (nhds 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).curvatureBias := by
    filter_upwards [I.gate3.eventually_exact_zero] with n hn
    rcases hn with ⟨_, _, hcurvature, _, _⟩
    rw [I.curvatureBias_eq_sum n]
    symm
    exact Finset.sum_eq_zero (fun i _ => hcurvature i)
  exact tendsto_const_nhds.congr' heq

theorem pairConsistency_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).pairConsistency) atTop (nhds 0) := by
  have heq :
      (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).pairConsistency := by
    filter_upwards [I.gate3.eventually_exact_zero] with n hn
    rcases hn with ⟨_, _, _, hspectral, _⟩
    rw [I.pairConsistency_eq_spectral_sum n]
    symm
    exact Finset.sum_eq_zero (fun i _ => hspectral i)
  exact tendsto_const_nhds.congr' heq

theorem density_tendsto_atTop :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop := by
  have h := affineDensity_tendsto_atTop
    I.densityBase I.densityStep I.densityStep_pos
  have heq :
      (fun n : ℕ => I.densityBase + I.densityStep * (n : ℝ)) =ᶠ[atTop]
        fun n => (I.chartCertificate n).density :=
    Filter.Eventually.of_forall (fun n => (I.density_eq_affine n).symm)
  exact h.congr' heq

theorem chart_operator_tendsto :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean I.operatorKernelData.toProfileData
          ((I.chartCertificate n).density))
      atTop
      (nhds (BDG4DOperatorProfileData.target
        I.operatorKernelData.toProfileData)) := by
  exact I.operatorKernelData.sampled_tendsto
    (fun n => (I.chartCertificate n).density) I.density_tendsto_atTop

theorem chartDistortion_tendsto_zero :
    Tendsto (fun n => (I.chartCertificate n).distortionBound)
      atTop (nhds 0) := by
  exact
    PhysicalGrowthHauptvermutungCertificate.certificate_distortionBound_tendsto_zero
      I.chartCertificate I.fixedScale I.scale_eq
      I.countWindow_tendsto_zero I.curvatureBias_tendsto_zero
      I.pairConsistency_tendsto_zero

/-- Complete derived handoff.  The concrete bound `I.gate3.defectRank 0`
makes the finite-time content visible instead of weakening everything to
eventuality. -/
structure Closed (errorScale : ℝ) : Prop where
  recoveredAfter :
    ∀ n, I.gate3.defectRank 0 ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  rssPoissonErrorZeroAfter :
    ∀ n, I.gate3.defectRank 0 ≤ n → ∀ i,
      rssPoissonError
        (countWindow n i) (curvatureBias n i) errorScale = 0
  chartOperatorLimit :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean
        I.operatorKernelData.toProfileData ((I.chartCertificate n).density))
      atTop
      (nhds (BDG4DOperatorProfileData.target
        I.operatorKernelData.toProfileData))
  chartDistortionTendsToZero :
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (nhds 0)
  scheduledDensityTendsToInfinity :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop

theorem closed (errorScale : ℝ) : I.Closed errorScale where
  recoveredAfter := I.recoveredStage_after_initial_defectRank
  rssPoissonErrorZeroAfter :=
    I.rssPoissonError_zero_after_initial_defectRank errorScale
  chartOperatorLimit := I.chart_operator_tendsto
  chartDistortionTendsToZero := I.chartDistortion_tendsto_zero
  scheduledDensityTendsToInfinity := I.density_tendsto_atTop

#print axioms MicroscopicGate3WellFoundedGate4ScheduledKernelData.closed
#print axioms MicroscopicGate3WellFoundedGate4ScheduledKernelData.chartDistortion_tendsto_zero

end MicroscopicGate3WellFoundedGate4ScheduledKernelData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedGate4Handoff
