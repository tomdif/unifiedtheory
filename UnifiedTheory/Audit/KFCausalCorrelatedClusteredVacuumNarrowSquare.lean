/- Exact narrow-coordinate representatives of the existing vacuum-square
outputs, for the original finite clustered vectors and their actual limit.
The physical half-clock and complex Gaussian Fourier prefactors cancel
before the surviving correlated sum is evaluated. These narrow coordinates
are not silently identified with the different physical charge chart. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierInverseHalf
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierOperatorBridge
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumSecondLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumNarrowSquare
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierGeneralCoordinates (Product frequencyCoordinates frequencyCoordinates_coe
  frequencyChart_preserves_volume frequencyChart_symm frequencyUnpack)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredShiftedNarrowProfiles (coefficient transformed limitTransformed)
open KFCausalCorrelatedClusteredPotentialFourierClock (fourierProfile fourierLimit)
open KFCausalShiftedNarrowFourierGeometry (radius)
open KFCausalShiftedNarrowFourierSlices (neutralPacket)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalVacuumMixedClockNormalization (inverseHalf normalizedClock fourier_normalization)
open KFCausalClockFloorBoundedInverse (inverseL)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "r" => scale ε (-h)
local notation "c" => amplitudes ε (-h) a p

def normalizedCoefficient (i : Fin m) (v : Block 4) : ℂ :=
  ((Real.pi:ℂ)/(α:ℂ))*f.amplitude i*normalizedClock ε (a i) (p i) (-h) (v 0)*
    neutralPacket β (r (v 0)) (f.source i) (f.polynomial i) v

def finiteProfile (δ : ℝ) (z : Product) : ℂ :=
  ∑ i, normalizedCoefficient f ε h a p i z.2*
    KFCausalReciprocalWedgeLaplace.laplaceSum (f.degree i+1)
      (KFCausalClusteredWidthProfiles.widths (f.degree i) δ)
      (KFCausalClusteredWidthProfiles.coefficients (f.degree i) δ)
      (radius ((α:ℂ)*(r (z.2 0))^2) z.1 z.2)

def limitProfile (z : Product) : ℂ :=
  ∑ i, normalizedCoefficient f ε h a p i z.2*
    (Complex.exp (-radius ((α:ℂ)*(r (z.2 0))^2) z.1 z.2)*
      radius ((α:ℂ)*(r (z.2 0))^2) z.1 z.2^(f.degree i))

variable (hε : 0 < ε)

include hε in
theorem coefficient_normalization (i : Fin m) (v : Block 4) :
    inverseHalf ε (v 0)*coefficient f (c (v 0)) α β (r (v 0)) (r (v 0)) 0 i v =
      normalizedCoefficient f ε h a p i v := by
  unfold coefficient normalizedCoefficient amplitudes
  simp only [pow_zero,mul_one]
  calc
    _ = (inverseHalf ε (v 0)*
      KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a i) (p i) (-h) (v 0)*
      ((Real.pi:ℂ)/((α:ℂ)*(r (v 0))^2)))*f.amplitude i*
      neutralPacket β (r (v 0)) (f.source i) (f.polynomial i) v := by ring
    _ = _ := by rw [fourier_normalization ε (a i) (p i) (-h) (v 0) α hε]; ring

include hε in
theorem finite_normalization (δ : ℝ) (z : Product) :
    inverseHalf ε (z.2 0)*transformed f (c (z.2 0)) α β
      (r (z.2 0)) (r (z.2 0)) 0 δ z.1 z.2 = finiteProfile f ε h a p δ z := by
  unfold transformed finiteProfile
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc,coefficient_normalization f ε h a p hε]

include hε in
theorem limit_normalization (z : Product) :
    inverseHalf ε (z.2 0)*fourierLimit f α β ε (-h) (-h) a p 0 (z.2 0) z.1 z.2 =
      limitProfile f ε h a p z := by
  unfold fourierLimit limitTransformed limitProfile
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc,coefficient_normalization f ε h a p hε]

theorem profile_tendsto (z : Product) : Tendsto (fun δ => finiteProfile f ε h a p δ z)
    (𝓝[>] 0) (𝓝 (limitProfile f ε h a p z)) :=
  tendsto_finset_sum _ (fun i _ =>
    (KFCausalClusteredWidthProfiles.laplaceSum_tendsto (f.degree i)
      (radius ((α:ℂ)*(r (z.2 0))^2) z.1 z.2)).const_mul _)

variable (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hy" => le_trans (le_of_eq (abs_neg h)) hb
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "U" => KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb
local notation "L" => KFCausalCorrelatedClusteredDoubleVacuumLimit.limitingOutput f ε h a p hε hh ha hb
local notation "Q" => KFCausalCorrelatedClusteredVacuumSecondLimit.inputSecond f ε h a p hε hh ha hb

theorem finite_double_mixed (δ : ℝ) (hδ : 0 < δ) : mixedCoordinates (U δ) =ᵐ[volume]
    fun z : Product => transformed f (c (z.2 0)) α β (r (z.2 0)) (r (z.2 0)) 0 δ z.1 z.2 := by
  have hu : U δ =ᵐ[volume]
      KFCausalCorrelatedClusteredNeutralPowers.fieldProfile f c α β ε (-h) (-h) 0 δ := by
    filter_upwards [KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_coe
      f ε h a p hε hh ha hb δ hδ] with x hx
    simpa only [KFCausalCorrelatedClusteredNeutralPowers.fieldProfile,pow_zero,one_mul,
      KFCausalCorrelatedClusteredDoubleVacuumProfiles.inputAmplitudes,amplitudes] using hx
  rw [KFCausalCorrelatedClusteredFourierOperatorBridge.mixedCoordinates_finite
    f α β ε (-h) (-h) a p 0 hα hβ hw hε hy hy ha δ hδ (U δ) hu]
  have he := KFCausalCorrelatedClusteredFourierOperatorBridge.finiteInput_frequency_coe
    f α β ε (-h) (-h) a p 0 hα hβ hw hε hy hy ha δ hδ
  filter_upwards [he] with z hz
  exact hz.trans (KFCausalCorrelatedClusteredPotentialFourierClock.fourierProfile_eq
    f α β ε (-h) (-h) a p 0 hα hε hy δ (z.2 0) hδ z.1 z.2)

theorem limit_double_mixed : mixedCoordinates L =ᵐ[volume]
    fun z : Product => fourierLimit f α β ε (-h) (-h) a p 0 (z.2 0) z.1 z.2 := by
  have hu : ∀ δ, 0 < δ → U δ =ᵐ[volume]
      KFCausalCorrelatedClusteredNeutralPowers.fieldProfile f c α β ε (-h) (-h) 0 δ := by
    intro δ hδ
    filter_upwards [KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_coe
      f ε h a p hε hh ha hb δ hδ] with x hx
    simpa only [KFCausalCorrelatedClusteredNeutralPowers.fieldProfile,pow_zero,one_mul,
      KFCausalCorrelatedClusteredDoubleVacuumProfiles.inputAmplitudes,amplitudes] using hx
  rw [KFCausalCorrelatedClusteredFourierOperatorBridge.mixedCoordinates_limit
    f α β ε (-h) (-h) a p 0 hα hβ hw hε hy hy ha U L hu
      (KFCausalCorrelatedClusteredDoubleVacuumLimit.output_tendsto f ε h a p hε hh ha hb)]
  let V := KFCausalCorrelatedClusteredJointFourierL2Limit.limitingInput
    f α β ε (-h) (-h) a p 0 hα hβ hw hε hy hy ha
  have hp := frequencyChart_preserves_volume.symm.quasiMeasurePreserving.ae
    (KFCausalCorrelatedClusteredJointFourierL2Limit.limitingInput_coe
      f α β ε (-h) (-h) a p 0 hα hβ hw hε hy hy ha)
  filter_upwards [frequencyCoordinates_coe V,hp] with z hz hp
  rw [hz]
  have hpair := KFCausalNarrowFourierGeneralCoordinates.frequencyChart.apply_symm_apply z
  rw [KFCausalNarrowFourierGeneralCoordinates.frequencyChart_apply,frequencyChart_symm] at hpair
  have hn := congrArg Prod.fst hpair
  have hs := congrArg Prod.snd hpair
  change KFCausalShiftedNarrowJointGaussian.narrow (frequencyUnpack z) = z.1 at hn
  change KFCausalShiftedNarrowJointGaussian.spectator (frequencyUnpack z) = z.2 at hs
  simpa only [Function.comp_apply,frequencyChart_symm,hn,hs] using hp

theorem finite_second_mixed (δ : ℝ) (hδ : 0 < δ) :
    mixedCoordinates (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds
      f ε h a p hε hh ha hb δ 7) =ᵐ[volume] finiteProfile f ε h a p δ := by
  rw [KFCausalCorrelatedClusteredVacuumSecondLimit.finiteSeconds_eq f ε h a p hε hh ha hb δ hδ]
  filter_upwards [KFCausalNarrowFourierInverseHalf.mixed_inverse_coe ε hε (U δ),
    finite_double_mixed f ε h a p hε hh ha hb δ hδ] with z hz hu
  rw [hz,hu]
  exact finite_normalization f ε h a p hε δ z

theorem limiting_second_mixed : mixedCoordinates Q =ᵐ[volume] limitProfile f ε h a p := by
  change mixedCoordinates (inverseL ε hε L) =ᵐ[volume] _
  filter_upwards [KFCausalNarrowFourierInverseHalf.mixed_inverse_coe ε hε L,
    limit_double_mixed f ε h a p hε hh ha hb] with z hz hu
  rw [hz,hu]
  exact limit_normalization f ε h a p hε z

#print axioms coefficient_normalization
#print axioms finite_normalization
#print axioms limit_normalization
#print axioms profile_tendsto
#print axioms finite_double_mixed
#print axioms limit_double_mixed
#print axioms finite_second_mixed
#print axioms limiting_second_mixed
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumNarrowSquare
