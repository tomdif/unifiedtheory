/- The actual quadratic and quartic Hamiltonian second outputs in mixed
coordinates and at the next rotated spectral input. The field shift is
-h/2 while the Gaussian shift is -h; both are retained exactly. -/
import UnifiedTheory.Audit.KFCausalComplexSpectatorFourier
import UnifiedTheory.Audit.KFCausalMatterInsertionCoordinate
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSourcedWidthMatterSecondInput
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product pairedChart_preserves_volume
  pairedChart_symm pairedCoordinates_coe mixed_inverse_coe)
open KFCausalEuclideanProductCoordinates (Block split)
open KFCausalPhysicalMixedCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalShiftedNarrowFourierGeometry (mixedField)
open KFCausalReciprocalNeutralMatterSpectral (spectral matterIndex second_eq spectral_coe)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalReciprocalNeutralSecondFactors (second)
open KFCausalSourcedWidthSecondInput (doubledOutput firstOutput density first_mixed)
open KFCausalChargeRotatedSecondInput (rotatedPoint)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action)
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)

def spectator (ε h : ℝ) (j : Fin 2) (v : Block 4) : ℂ :=
  mixedField (scale ε (-h/2) (v 0)) v^degree j

variable (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "S" => spectral ε a h w hε ha hh hw hb C p b P
local notation "V" => doubledOutput ε h a w C p b P hε hh ha hw hb
local notation "T" => second ε a h w hε ha hh hw hb C p b P

include hε hb in
theorem spectator_continuous (j : Fin 2) : Continuous (spectator ε h j) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
    linarith [show 0 ≤ Real.pi*ε/3 by positivity]
  have hs := (scale_smooth ε (-h/2) hε hy).continuous.comp
    (show Continuous (fun v : Block 4 => v 0) by fun_prop)
  unfold spectator mixedField
  fun_prop

theorem paired_relation (j : Fin 2) :
    pairedCoordinates (S j) =ᵐ[volume]
      fun z : Product => spectator ε h j z.2*(pairedCoordinates V) z := by
  have hS := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae
    (spectral_coe ε a h w hε ha hh hw hb C p b P j)
  have hV := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae
    (KFCausalReciprocalNeutralDoubleVacuum.output_coe ε a h w hε ha hh hw C p b P hb)
  filter_upwards [pairedCoordinates_coe (S j),pairedCoordinates_coe V,hS,hV] with z hs hv hS hV
  simp only [pairedChart_symm] at hS hV
  rw [hs,hv,hS]
  change _ = spectator ε h j z.2*
    KFCausalReciprocalNeutralDoubleVacuum.output ε a h w hε ha hh hw C p b P hb
      (z.2 0,KFCausalShiftedPhysicalFourierSlices.reconstruct z.1 z.2)
  rw [hV]
  unfold KFCausalCoherentMatterSpectralProfile.multiplier spectator
  rw [KFCausalCoherentMatterSpectralProfile.field_eq,KFCausalShiftedPhysicalFourierSlices.reconstruct_field]

theorem mixed_relation (j : Fin 2) :
    mixedCoordinates (S j) =ᵐ[volume]
      fun z : Product => spectator ε h j z.2*(mixedCoordinates V) z :=
  (KFCausalComplexSpectatorFourier.leftFourier_relation_iff 2 4 (spectator ε h j)
    (spectator_continuous ε h hε hb j).measurable (pairedCoordinates V) (pairedCoordinates (S j))).mpr
      (paired_relation ε h a w C p b P hε hh ha hw hb j)

theorem second_mixed (j : Fin 2) :
    mixedCoordinates (T (matterIndex j)) =ᵐ[volume]
      fun z : Product => spectator ε h j z.2*density ε h a w C p b P z := by
  rw [second_eq ε a h w hε ha hh hw hb C p b P j]
  filter_upwards [mixed_inverse_coe ε hε (S j),mixed_relation ε h a w C p b P hε hh ha hw hb j,
    mixed_inverse_coe ε hε V,first_mixed ε h a w C p b P hε hh ha hw hb] with z hi hs hv hf
  change mixedCoordinates (firstOutput ε h a w C p b P hε hh ha hw hb) z = _ at hv
  rw [hi,hs]
  calc
    _ = spectator ε h j z.2*(KFCausalVacuumMixedClockNormalization.inverseHalf ε (z.2 0)*
      (mixedCoordinates V) z) := by ring
    _ = spectator ε h j z.2*(mixedCoordinates (firstOutput ε h a w C p b P hε hh ha hw hb)) z := by rw [hv]
    _ = _ := by rw [hf]

include hw in
theorem spectator_eq_coefficient (θ : ℝ) (j : Fin 2) (x : Product) :
    spectator ε h j (rotatedPoint h hh θ (mixedMap ε hε x)).2 =
      KFCausalMatterInsertionCoordinate.coefficient ε h (groundWidth h) w (momentumScale h) θ
        (x.2 0:ℂ) ((split 2 4).symm x)^degree j := by
  rw [spectator,KFCausalSingleGaussianNormalizedDensity.rotated_clock ε hε h hh θ x,
    ← KFCausalMatterInsertionCoordinate.coefficient_real ε hε h (groundWidth h) w hh
      (groundWidth_positive h hh) (lt_of_lt_of_le zero_lt_one hw) θ x]

include hw in
theorem inserted_density_numerator (θ : ℝ) (j : Fin 2) (x : Product) :
    ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
      (spectator ε h j (rotatedPoint h hh θ (mixedMap ε hε x)).2*
        density ε h a w C p b P (rotatedPoint h hh θ (mixedMap ε hε x))) =
      KFCausalMatterInsertionCoordinate.coefficient ε h (groundWidth h) w (momentumScale h) θ
        (x.2 0:ℂ) ((split 2 4).symm x)^degree j*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w (momentumScale h) θ
          C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  rw [spectator_eq_coefficient ε h w hε hh hw θ j x,
    ← KFCausalSourcedWidthNormalizedDensity.density_numerator ε hε h a w C p b P hh hw θ x]
  ring

theorem rotated_second_input_coe (θ : ℝ) (j : Fin 2) :
    clockMixed ε hε (inverseL ε hε (action h hh θ (T (matterIndex j)))) =ᵐ[volume]
      fun x => KFCausalMatterInsertionCoordinate.coefficient ε h (groundWidth h) w (momentumScale h) θ
        (x.2 0:ℂ) ((split 2 4).symm x)^degree j*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w (momentumScale h) θ
          C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  have he := KFCausalChargeRotatedSecondInput.rotated_second_input ε hε h hh θ _ _
    (second_mixed ε h a w C p b P hε hh ha hw hb j)
  filter_upwards [he] with x hx
  exact hx.trans (inserted_density_numerator ε h a w C p b P hε hh hw θ j x)

#print axioms spectator_continuous
#print axioms paired_relation
#print axioms mixed_relation
#print axioms second_mixed
#print axioms spectator_eq_coefficient
#print axioms inserted_density_numerator
#print axioms rotated_second_input_coe
end
end UnifiedTheory.Audit.KFCausalSourcedWidthMatterSecondInput
