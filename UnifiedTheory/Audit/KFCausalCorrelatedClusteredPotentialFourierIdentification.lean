/- The three actual potential spectral endpoints, finite and limiting,
are identified with the proved joint Fourier vectors under the original
unitary. The field powers are 0, 2 and 4 with the two physical shifts. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierOperatorBridge
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMatterSecondLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredDoubleVacuumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialFourierIdentification
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredFourierOperatorBridge
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowFourierGeneralCoordinates (frequencyCoordinates)
open KFCausalCorrelatedClusteredJointFourierL2Limit (finiteInput limitingInput)
open KFCausalCorrelatedClusteredNeutralPowers (fieldProfile)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalMixedFieldGaussianStrip (degree)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hy" => le_trans (le_of_eq (abs_neg h)) hb
local notation "hz" => KFCausalCorrelatedClusteredPhysicalClockLimit.shift_bound ε h
  (KFCausalGaussianVacuumSquare.original_strip ε h hε hb)

def fourierFinite (k : ℕ) (δ : ℝ) : Hilbert :=
  finiteInput f α β ε (-h) (-h/2) a p k (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε hy hz ha δ

def fourierLimit (k : ℕ) : Hilbert :=
  limitingInput f α β ε (-h) (-h/2) a p k (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε hy hz ha

theorem finite_vacuum_identification (δ : ℝ) (hδ : 0 < δ) :
    mixedCoordinates (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb δ) =
      frequencyCoordinates (fourierFinite f ε h a p hε hh ha hb 0 δ) := by
  apply mixedCoordinates_finite f α β ε (-h) (-h/2) a p 0
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha δ hδ
  filter_upwards [KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_coe f ε h a p hε hh ha hb δ hδ]
    with x hx
  simpa only [fieldProfile,pow_zero,one_mul] using hx

theorem finite_matter_identification (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    mixedCoordinates (KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSpectral f ε h a p hε hh ha hb δ j) =
      frequencyCoordinates (fourierFinite f ε h a p hε hh ha hb (degree j) δ) :=
  mixedCoordinates_finite f α β ε (-h) (-h/2) a p (degree j)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha δ hδ _
      (KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSpectral_coe f ε h a p hε hh ha hb δ hδ j)

theorem vacuum_identification :
    mixedCoordinates (KFCausalCorrelatedClusteredDoubleVacuumLimit.limitingOutput f ε h a p hε hh ha hb) =
      frequencyCoordinates (fourierLimit f ε h a p hε hh ha hb 0) := by
  apply mixedCoordinates_limit f α β ε (-h) (-h/2) a p 0
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha
    (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb)
  · intro δ hδ
    filter_upwards [KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_coe f ε h a p hε hh ha hb δ hδ]
      with x hx
    simpa only [fieldProfile,pow_zero,one_mul] using hx
  · exact KFCausalCorrelatedClusteredDoubleVacuumLimit.output_tendsto f ε h a p hε hh ha hb

theorem matter_identification (j : Fin 2) :
    mixedCoordinates (KFCausalCorrelatedClusteredMatterSecondLimit.limitingSpectral f ε h a p hε hh ha hb j) =
      frequencyCoordinates (fourierLimit f ε h a p hε hh ha hb (degree j)) :=
  mixedCoordinates_limit f α β ε (-h) (-h/2) a p (degree j)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha
    (fun δ => KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSpectral f ε h a p hε hh ha hb δ j) _
    (fun δ hδ => KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSpectral_coe f ε h a p hε hh ha hb δ hδ j)
    (KFCausalCorrelatedClusteredMatterSecondLimit.spectral_tendsto f ε h a p hε hh ha hb j)

theorem vacuum_norm :
    ‖KFCausalCorrelatedClusteredDoubleVacuumLimit.limitingOutput f ε h a p hε hh ha hb‖ =
      ‖fourierLimit f ε h a p hε hh ha hb 0‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using congrArg norm (vacuum_identification f ε h a p hε hh ha hb)

theorem matter_norm (j : Fin 2) :
    ‖KFCausalCorrelatedClusteredMatterSecondLimit.limitingSpectral f ε h a p hε hh ha hb j‖ =
      ‖fourierLimit f ε h a p hε hh ha hb (degree j)‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using congrArg norm (matter_identification f ε h a p hε hh ha hb j)

#print axioms finite_vacuum_identification
#print axioms finite_matter_identification
#print axioms vacuum_identification
#print axioms matter_identification
#print axioms vacuum_norm
#print axioms matter_norm
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialFourierIdentification
