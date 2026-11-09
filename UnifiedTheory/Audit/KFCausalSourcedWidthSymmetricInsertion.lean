/- Exact second-input representative of a symmetric charged position
inserted after the first vacuum square. The physical field output is
the already constructed Hilbert vector, with the original source data. -/
import UnifiedTheory.Audit.KFCausalSymmetricInsertionCoordinate
import UnifiedTheory.Audit.KFCausalSourcedWidthFirstField
import UnifiedTheory.Audit.KFCausalSourcedWidthNormalizedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricInsertion
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalReciprocalNormalization (normalize)
open KFCausalNormalizedComplexRotation (rotationIsometry physical_rotation)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalChargeRotatedSecondInput (rotatedPoint)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalBroadPairedGaussianSecondInput (normalize_mixedMap)
open KFCausalComplexClockInverse (complexInverse_real)
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalSymmetricInsertionCoordinate
  (coefficient coefficient_eq_baseline coordinateIndex coordinateScale coordinateScale_positive)
open KFCausalPhysicalSpectatorGraph (symmetricPosition symmetricIndex)
open KFCausalSourcedWidthSecondInput (density)
open KFCausalSourcedWidthFirstField (fieldOutput symmetric_first_mixed)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action)

theorem normalized_rotatedPoint (ε : ℝ) (hε : 0 < ε) (h α w : ℝ)
    (hh : h ≠ 0) (hα : 0 < α) (hw : 0 < w) (θ : ℝ) (x : Product) :
    normalize α w (momentumScale h)
      ((split 2 4).symm (rotatedPoint h hh θ (mixedMap ε hε x))) =
      rotationIsometry θ (baselineVector ε α w (momentumScale h) (x.2 0:ℂ)
        ((split 2 4).symm x)) := by
  rw [rotatedPoint,MeasurableEquiv.symm_apply_apply,physical_rotation,
    normalize_mixedMap ε hε α w (momentumScale h) hα hw]
  simp only [baselineVector,complexInverse_real ε hε]
  rfl

theorem coefficient_real (ε : ℝ) (hε : 0 < ε) (h α w : ℝ)
    (hh : h ≠ 0) (hα : 0 < α) (hw : 0 < w) (θ : ℝ) (i : Fin 2) (x : Product) :
    coefficient ε h α w (momentumScale h) θ i (x.2 0:ℂ) ((split 2 4).symm x) =
      ((rotatedPoint h hh θ (mixedMap ε hε x)).2 (symmetricIndex i) : ℂ) := by
  rw [coefficient_eq_baseline,← normalized_rotatedPoint ε hε h α w hh hα hw θ x]
  have hn : (coordinateScale α w i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (coordinateScale_positive α w hα hw i).ne'
  have hp : normalize α w (momentumScale h)
      ((split 2 4).symm (rotatedPoint h hh θ (mixedMap ε hε x))) (coordinateIndex i) =
      (coordinateScale α w i : ℂ)*
        ((rotatedPoint h hh θ (mixedMap ε hε x)).2 (symmetricIndex i) : ℂ) := by
    fin_cases i <;> simp [KFCausalPhysicalReciprocalNormalization.normalize,coordinateIndex,coordinateScale,symmetricIndex,
      KFCausalEuclideanProductCoordinates.split]
    all_goals exact Or.inl rfl
  rw [hp,mul_div_cancel_left₀ _ hn]

theorem inserted_density_numerator (ε : ℝ) (hε : 0 < ε) (h a w : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hh : h ≠ 0) (hw : 1 ≤ w)
    (θ : ℝ) (i : Fin 2) (x : Product) :
    ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
      (((rotatedPoint h hh θ (mixedMap ε hε x)).2 (symmetricIndex i) : ℂ)*
        density ε h a w C p b P (rotatedPoint h hh θ (mixedMap ε hε x))) =
      coefficient ε h (groundWidth h) w (momentumScale h) θ i (x.2 0:ℂ) ((split 2 4).symm x)*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w (momentumScale h) θ
          C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  rw [coefficient_real ε hε h (groundWidth h) w hh (groundWidth_positive h hh)
    (lt_of_lt_of_le zero_lt_one hw) θ i x,
    ← KFCausalSourcedWidthNormalizedDensity.density_numerator ε hε h a w C p b P hh hw θ x]
  ring

theorem rotated_second_input_coe (ε : ℝ) (hε : 0 < ε) (h a w : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hh : h ≠ 0) (hw : 1 ≤ w)
    (ha : 0 < a) (hb : |h| ≤ Real.pi*ε/3) (θ : ℝ) (i : Fin 2) :
    clockMixed ε hε (inverseL ε hε (action h hh θ
      (fieldOutput ε h a w C p b P hε hh ha hw hb (symmetricPosition i)))) =ᵐ[volume]
      fun x => coefficient ε h (groundWidth h) w (momentumScale h) θ i
        (x.2 0:ℂ) ((split 2 4).symm x)*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w (momentumScale h) θ
          C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  have he := KFCausalChargeRotatedSecondInput.rotated_second_input ε hε h hh θ _ _
    (symmetric_first_mixed ε h a w C p b P hε hh ha hw hb i)
  filter_upwards [he] with x hx
  exact hx.trans (inserted_density_numerator ε hε h a w C p b P hh hw θ i x)

#print axioms normalized_rotatedPoint
#print axioms coefficient_real
#print axioms inserted_density_numerator
#print axioms rotated_second_input_coe
end
end UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricInsertion
