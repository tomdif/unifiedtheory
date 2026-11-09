/- Actual arbitrary reciprocal-width Gaussian states and their first
vacuum-square outputs, with the physical partial Fourier representative. -/
import UnifiedTheory.Audit.KFCausalChargeRotatedSecondInput
import UnifiedTheory.Audit.KFCausalReciprocalNeutralDoubleVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalSourcedWidthSecondInput
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalFourierGeneralCoordinates (Product pairedChart_preserves_volume
  pairedChart_symm pairedCoordinates_coe mixed_inverse_coe)
open KFCausalPhysicalMixedCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action)
open KFCausalChargeRotatedSecondInput (rotatedPoint)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalShiftedPhysicalFourierSlices (physicalSlice physicalSlice_fourier
  physicalSlice_integrable reconstruct radius)
open KFCausalShiftedNarrowFourierSlices (neutralPacket)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedNarrowFourierGeometry (shifted_coefficient_positive)
open KFCausalPartialFourierFiberFormula (sliceFourier)
open KFCausalVacuumMixedClockNormalization (inverseHalf normalizedClock fourier_normalization)

def density (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : Product) : ℂ :=
  C*normalizedClock ε a p (-h) (x.2 0)*((Real.pi:ℂ)/(groundWidth h:ℂ))*
    Complex.exp (-radius ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) w x.1 x.2)*
    neutralPacket (neutralWidth h) (scale ε (-h) (x.2 0)) b P x.2

def pairedProfile (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : Product) : ℂ :=
  C*clockAmplitude ε a p (-h) (x.2 0)*physicalSlice (groundWidth h) (neutralWidth h) w
    (scale ε (-h) (x.2 0)) (scale ε (-h) (x.2 0)) b P 0 x.2 x.1

def frequencyProfile (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : Product) : ℂ :=
  C*clockAmplitude ε a p (-h) (x.2 0)*
    (((Real.pi:ℂ)/((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2))*
      Complex.exp (-radius ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) w x.1 x.2)*
      neutralPacket (neutralWidth h) (scale ε (-h) (x.2 0)) b P x.2)

variable (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)

def state : Hilbert := KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P
def doubledOutput : Hilbert :=
  KFCausalReciprocalNeutralDoubleVacuum.output ε a h w hε ha hh hw C p b P hb
def firstOutput : Hilbert := inverseL ε hε (doubledOutput ε h a w C p b P hε hh ha hw hb)

theorem first_graph : (state ε h a w C p b P hε hh ha hw,firstOutput ε h a w C p b P hε hh ha hw hb) ∈
    (KFCausalClockFloorVacuumSquare.square ε hε h).graph :=
  KFCausalVacuumParameterRescale.doubled_square_graph ε hε h _ _
    (KFCausalReciprocalNeutralDoubleVacuum.output_graph ε a h w hε ha hh hw C p b P hb)

theorem paired_output_coe : pairedCoordinates (doubledOutput ε h a w C p b P hε hh ha hw hb) =ᵐ[volume]
    pairedProfile ε h a w C p b P := by
  have hu := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae
    (KFCausalReciprocalNeutralDoubleVacuum.output_coe ε a h w hε ha hh hw C p b P hb)
  filter_upwards [pairedCoordinates_coe (doubledOutput ε h a w C p b P hε hh ha hw hb),hu] with x hx hu
  rw [hx]
  simp only [pairedChart_symm] at hu
  rw [doubledOutput,hu]
  simp only [KFCausalReciprocalNeutralOrderedProfile.shiftedProfile,
    pairedProfile,physicalSlice,KFCausalReciprocalNeutralSliceIntegrability.factor,
    KFCausalNeutralExponentialProfiles.exponentialProfile,
    show -(2*h)/2=-h by ring,pow_zero,one_mul]
  ring

include hε hh hw hb in
theorem sliceFourier_eq : sliceFourier 2 4 (pairedProfile ε h a w C p b P)=frequencyProfile ε h a w C p b P := by
  have hy : |-h| ≤ Real.pi*ε/3 := by simpa only [abs_neg] using hb
  funext x
  unfold sliceFourier pairedProfile frequencyProfile
  dsimp only
  rw [KFCausalCorrelatedClusteredShiftedNarrowProfiles.fourier_mul_left]
  rw [physicalSlice_fourier _ _ _ _ _ _ _ _
    (shifted_coefficient_positive _ _ _ _ (groundWidth_positive h hh) hε hy)
    (lt_of_lt_of_le zero_lt_one hw)]
  simp only [pow_zero,mul_one]

include hε hh hb in
theorem frequencyProfile_continuous : Continuous (frequencyProfile ε h a w C p b P) := by
  have hy : |-h| ≤ Real.pi*ε/3 := by simpa only [abs_neg] using hb
  have hv : Continuous (fun x : Product => x.2 0) := by fun_prop
  have hc := (clockAmplitude_smooth ε a p (-h) hε hy).continuous.comp hv
  have hr := (scale_smooth ε (-h) hε hy).continuous.comp hv
  have hn (x : Product) : (groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2 ≠ 0 := by
    have hp := shifted_coefficient_positive (groundWidth h) ε (-h) (x.2 0)
      (groundWidth_positive h hh) hε hy
    intro he
    simp only [he,Complex.zero_re,lt_self_iff_false] at hp
  unfold frequencyProfile radius neutralPacket KFCausalShiftedNarrowFourierGeometry.neutral
  fun_prop (disch := exact hn)

theorem doubled_mixed : mixedCoordinates (doubledOutput ε h a w C p b P hε hh ha hw hb) =ᵐ[volume]
    frequencyProfile ε h a w C p b P := by
  have he := paired_output_coe ε h a w C p b P hε hh ha hw hb
  let hF : MemLp (pairedProfile ε h a w C p b P) 2 volume :=
    (Lp.memLp (pairedCoordinates (doubledOutput ε h a w C p b P hε hh ha hw hb))).ae_eq he
  have hU : pairedCoordinates (doubledOutput ε h a w C p b P hε hh ha hw hb)=hF.toLp _ :=
    Lp.ext (he.trans hF.coeFn_toLp.symm)
  have hy : |-h| ≤ Real.pi*ε/3 := by simpa only [abs_neg] using hb
  have hi (v : Block 4) : Integrable (fun u => pairedProfile ε h a w C p b P (u,v)) :=
    (physicalSlice_integrable (groundWidth h) (neutralWidth h) w
      (scale ε (-h) (v 0)) (scale ε (-h) (v 0)) b P 0
      (shifted_coefficient_positive (groundWidth h) ε (-h) (v 0)
        (groundWidth_positive h hh) hε hy)
      (lt_of_lt_of_le zero_lt_one hw) v).const_mul (C*clockAmplitude ε a p (-h) (v 0))
  have hG : AEStronglyMeasurable (sliceFourier 2 4 (pairedProfile ε h a w C p b P)) volume := by
    rw [sliceFourier_eq ε h a w C p b P hε hh hw hb]
    exact (frequencyProfile_continuous ε h a w C p b P hε hh hb).aestronglyMeasurable
  change KFCausalPartialFourier.leftFourier 2 4
    (pairedCoordinates (doubledOutput ε h a w C p b P hε hh ha hw hb)) =ᵐ[volume] _
  rw [hU]
  have hp := KFCausalPartialFourierFiberPlancherel.leftFourier_toLp_coe 2 4 _ hF
    (Eventually.of_forall hi) hG
  rwa [sliceFourier_eq ε h a w C p b P hε hh hw hb] at hp

include hε in
theorem fourier_normalized (x : Product) :
    inverseHalf ε (x.2 0)*frequencyProfile ε h a w C p b P x=density ε h a w C p b P x := by
  unfold frequencyProfile density
  calc
    _ = (inverseHalf ε (x.2 0)*clockAmplitude ε a p (-h) (x.2 0)*
      ((Real.pi:ℂ)/((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2)))*C*
      Complex.exp (-radius ((groundWidth h:ℂ)*(scale ε (-h) (x.2 0))^2) w x.1 x.2)*
      neutralPacket (neutralWidth h) (scale ε (-h) (x.2 0)) b P x.2 := by ring
    _ = _ := by rw [fourier_normalization _ _ _ _ _ _ hε]; ring

theorem first_mixed : mixedCoordinates (firstOutput ε h a w C p b P hε hh ha hw hb) =ᵐ[volume]
    density ε h a w C p b P := by
  filter_upwards [mixed_inverse_coe ε hε (doubledOutput ε h a w C p b P hε hh ha hw hb),
    doubled_mixed ε h a w C p b P hε hh ha hw hb] with x hx he
  rw [firstOutput,hx,he]
  exact fourier_normalized ε h a w C p b P hε x

theorem rotated_second_input (θ : ℝ) :
    clockMixed ε hε (inverseL ε hε (action h hh θ (firstOutput ε h a w C p b P hε hh ha hw hb))) =ᵐ[volume]
      fun x => ((Real.exp (KFCausalClockFloorPairedStraightening.clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
        density ε h a w C p b P (rotatedPoint h hh θ (KFCausalClockFloorMixedChart.mixedMap ε hε x)) :=
  KFCausalChargeRotatedSecondInput.rotated_second_input ε hε h hh θ _ _
    (first_mixed ε h a w C p b P hε hh ha hw hb)

#print axioms first_graph
#print axioms paired_output_coe
#print axioms sliceFourier_eq
#print axioms frequencyProfile_continuous
#print axioms doubled_mixed
#print axioms fourier_normalized
#print axioms first_mixed
#print axioms rotated_second_input
end
end UnifiedTheory.Audit.KFCausalSourcedWidthSecondInput
