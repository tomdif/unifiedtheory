/-
  Audit/KFCausalCSpecHarmonicBornWellFoundedGate4Handoff.lean

  ACTION-SELECTED RAW HARMONIC SCHEDULE -> GATE 3 -> GATE 4

  This handoff keeps one probability law from microscopic causal growth into
  defect repair: the canonical Born-shell completion of the raw harmonic
  schedule selected by the vacuum spectator action.  Gate 3 reaches exact
  recovery by well-founded descent of a finite
  natural defect rank.  Supplied residual-to-chart identities transfer that
  recovered tail to exact chart and RSS/Poisson zero.  A separately supplied
  affine density schedule and analytic BDG kernel package then give the Gate 4
  density and operator limits.

  No legacy real contraction rate, remainder bound, step floor, or assumed
  asymptotic Gate 3 convergence appears in this interface.  The chart and
  kernel inputs are not claimed to be derived from the harmonic growth law.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff

noncomputable section

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3

/-- Harmonic well-founded Gate 3 data plus independently supplied physical-chart
matching and active-kernel data needed for the quantitative Gate 4 handoff. -/
structure HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ)
    (scale c total correctorCoeff : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (countGap curvatureGap spectralGap : ℝ) where
  gate3 :
    HarmonicBornProtectedWellFoundedGate3Data
      chirality parentSchedule observe J
      countWindow curvatureBias spectralLocality corrector
      scale c total correctorCoeff edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap
  chartCertificate :
    ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart
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

namespace HarmonicBornProtectedWellFoundedGate4ScheduledKernelData

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {chirality : Fin 2}
variable
  {parentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n}
variable {observe : (n : ℕ) → CausalSetGrowthBranch n → ι}
variable
  {J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ}
variable {scale c total correctorCoeff : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

variable
  (I : HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    chirality parentSchedule observe J
    countWindow curvatureBias spectralLocality corrector
    scale c total correctorCoeff edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

include I

/-- The initial finite defect rank is a concrete recovery-time bound. -/
noncomputable def recoveryBound : ℕ := I.gate3.defectRank 0

/-- All residual channels and bridge transport are exactly recovered after
the explicit finite rank budget is exhausted. -/
theorem exact_zero_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  exact I.gate3.exact_zero_after_initial_defectRank

/-- The exact recovered-stage predicate used by Gate 4 holds from the same
finite bound onward. -/
theorem recoveredStage_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact I.gate3.recoveredStage_after_initial_defectRank

/-- Matched chart-certificate residuals become literally zero at recovery. -/
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

/-- The displayed quantitative-Hauptvermutung distortion is exactly zero on
the recovered tail. -/
theorem chartDistortion_zero_after_recoveryBound :
    ∀ n, I.recoveryBound ≤ n →
      (I.chartCertificate n).distortionBound = 0 := by
  intro n hn
  rcases I.chartResiduals_zero_after_recoveryBound n hn with
    ⟨hcount, hcurvature, hpair⟩
  simp [PhysicalGrowthHauptvermutungCertificate.distortionBound,
    hcount, hcurvature, hpair]

/-- Exact recovery kills the RSS/Poisson horizon-error channel. -/
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

/-- Bounded recovery implies the standard filter-form Gate 4 predicate. -/
theorem eventually_recoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
  exact I.recoveredStage_after_recoveryBound n hn

/-- The RSS/Poisson channel is eventually exactly zero. -/
theorem eventually_rssPoissonError_zero (errorScale : ℝ) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
  exact I.rssPoissonError_zero_after_recoveryBound errorScale n hn

/-- Exact post-bound chart distortion supplies its zero limit directly. -/
theorem chartDistortion_tendsto_zero :
    Tendsto
      (fun n => (I.chartCertificate n).distortionBound)
      atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop I.recoveryBound] with n hn
  exact (I.chartDistortion_zero_after_recoveryBound n hn).symm

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

/-- The active kernel/profile supplier converges along the scheduled physical
chart density. -/
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

/-- Conditional handoff package: the Born law built on the action-selected raw
harmonic schedule is normalized and horizon-protected at Gate 3 and reaches
exact finite-rank recovery.  The matched chart identities and independent
analytic kernel data supply the displayed Gate 4 limits. -/
structure Closed (errorScale : ℝ) : Prop where
  gate3Closed : I.gate3.Closed
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
    Tendsto (fun n => (I.chartCertificate n).distortionBound)
      atTop (𝓝 0)
  scheduledDensityTendsToInfinity :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop

theorem closed (errorScale : ℝ) : I.Closed errorScale where
  gate3Closed := I.gate3.closed
  exactZeroAfterRecoveryBound := I.exact_zero_after_recoveryBound
  recoveredStageAfterRecoveryBound := I.recoveredStage_after_recoveryBound
  rssPoissonErrorZero := I.eventually_rssPoissonError_zero errorScale
  chartOperatorLimit := I.chart_operator_tendsto
  chartDistortionTendsToZero := I.chartDistortion_tendsto_zero
  scheduledDensityTendsToInfinity := I.density_tendsto_atTop

#print axioms exact_zero_after_recoveryBound
#print axioms recoveredStage_after_recoveryBound
#print axioms chartDistortion_zero_after_recoveryBound
#print axioms eventually_rssPoissonError_zero
#print axioms chartDistortion_tendsto_zero
#print axioms chart_operator_tendsto
#print axioms closed

end HarmonicBornProtectedWellFoundedGate4ScheduledKernelData

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
