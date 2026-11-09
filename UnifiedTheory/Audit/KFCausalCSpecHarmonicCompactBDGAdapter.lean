/- Reuse the actual harmonic handoff's chart, density, and finite recovery
with a general proved compact-profile supplier.  The analytic readout is
explicitly separate from its legacy one-sided-support kernel field.  No
claim that the microscopic history generates this test field is made. -/
import UnifiedTheory.Audit.KFCausalBDG4DNonzeroCompactKernel
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicCompactBDGAdapter
noncomputable section
open Filter Topology
open KFCausalSetSequentialGrowth
open KFCausalCSpecBridgeDefectObservable
open KFCausalCSpecContinuationProfile
open KFCausalCSpecEntropyFluxLimit
open KFCausalCSpecGlobalization
open KFCausalCSpecHauptvermutungPhysicalBridge
open KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open KFCausalCSpecHarmonicBornWellFoundedGate4Handoff

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {chirality : Fin 2}
variable {parentSchedule : (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n}
variable {observe : (n : ℕ) → CausalSetGrowthBranch n → ι}
variable {J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ}
variable {scale c total correctorCoeff : ℕ → ℝ}
variable {edge : ℕ → ι → E4} {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}
variable (I : HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
  (ι:=ι) (X:=X) (Y:=Y) (chart:=chart) chirality parentSchedule observe J
  countWindow curvatureBias spectralLocality corrector scale c total correctorCoeff edge candidate
  countQuantum curvatureQuantum spectralQuantum countGap curvatureGap spectralGap)

def profileMean (D : BDG4DOperatorProfileSplitData) (n : ℕ) : ℝ :=
  BDG4DOperatorProfileData.mean D.toProfileData ((I.chartCertificate n).density)

theorem profile_tendsto (D : BDG4DOperatorProfileSplitData) :
    Tendsto (profileMean I D) atTop (𝓝 (BDG4DOperatorProfileData.target D.toProfileData)) :=
  D.sampled_tendsto (fun n => (I.chartCertificate n).density) I.density_tendsto_atTop

theorem recovered_with_profile (D : BDG4DOperatorProfileSplitData) (errorScale : ℝ) :
    (∀ n, I.recoveryBound ≤ n →
      PhysicalHauptvermutungRecoveredStage (countWindow n) (curvatureBias n)
        (spectralLocality n) (scale n) (total n) (edge n) (candidate n)) ∧
    (∀ᶠ n in atTop, ∀ i, rssPoissonError (countWindow n i) (curvatureBias n i) errorScale=0) ∧
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (𝓝 0) ∧
    Tendsto (profileMean I D) atTop (𝓝 (BDG4DOperatorProfileData.target D.toProfileData)) :=
  ⟨I.recoveredStage_after_recoveryBound,I.eventually_rssPoissonError_zero errorScale,
    I.chartDistortion_tendsto_zero,profile_tendsto I D⟩

theorem compact_nonzero_tendsto :
    Tendsto (profileMean I KFCausalBDG4DNonzeroCompactKernel.data) atTop
      (𝓝 (Real.sqrt Real.pi/6)) ∧
    BDG4DOperatorProfileData.target KFCausalBDG4DNonzeroCompactKernel.data.toProfileData ≠ 0 := by
  refine ⟨?_,KFCausalBDG4DNonzeroCompactKernel.target_ne_zero⟩
  simpa only [KFCausalBDG4DNonzeroCompactKernel.target_eq] using
    profile_tendsto I KFCausalBDG4DNonzeroCompactKernel.data

theorem compact_normalized_tendsto :
    Tendsto (fun n => (48/Real.sqrt Real.pi)*profileMean I KFCausalBDG4DNonzeroCompactKernel.data n)
      atTop (𝓝 (8:ℝ)) :=
  KFCausalBDG4DNonzeroCompactKernel.sampled_tendsto
    (fun n => (I.chartCertificate n).density) I.density_tendsto_atTop

#print axioms profile_tendsto
#print axioms recovered_with_profile
#print axioms compact_nonzero_tendsto
#print axioms compact_normalized_tendsto
end
end UnifiedTheory.Audit.KFCausalCSpecHarmonicCompactBDGAdapter
