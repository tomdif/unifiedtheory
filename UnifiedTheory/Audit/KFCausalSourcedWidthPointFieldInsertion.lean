/- Actual second input with the full physical point field inserted after
the first vacuum square. The neutral coordinate and both symmetric
charged positions retain their original physical normalization. -/
import UnifiedTheory.Audit.KFCausalPointFieldInsertionCoordinate
import UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldInsertion
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product pairedChart pairedChart_symm)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalReciprocalNormalization (normalize)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalChargeRotatedSecondInput (rotatedPoint)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalPointFieldInsertionCoordinate
  (coefficient neutralCoefficient neutralScale neutralScale_positive neutralCoefficient_eq_baseline)
open KFCausalSourcedWidthSymmetricInsertion (normalized_rotatedPoint)
open KFCausalPairedModeCoordinates (scale)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalSourcedWidthSecondInput (density first_mixed)
open KFCausalSourcedWidthFirstField (fieldOutput first_field_graph)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)

theorem neutralCoefficient_real (ε : ℝ) (hε : 0 < ε) (h α w : ℝ)
    (hh : h ≠ 0) (hα : 0 < α) (hw : 0 < w) (θ : ℝ) (x : Product) :
    neutralCoefficient ε h α w (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x) =
      ((rotatedPoint h hh θ (mixedMap ε hε x)).2 3 : ℂ) := by
  rw [neutralCoefficient_eq_baseline]
  have hn : (neutralScale α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (neutralScale_positive α hα).ne'
  have hp := congrArg (fun z : KFCausalComplexShearPerturbation.Space => z 4)
    (normalized_rotatedPoint ε hε h α w hh hα hw θ x)
  have hp' : (neutralScale α:ℂ)*((rotatedPoint h hh θ (mixedMap ε hε x)).2 3:ℂ) =
      baselineVector ε α w (momentumScale h) (x.2 0:ℂ) ((split 2 4).symm x) 4 := by
    change (((Real.sqrt (α/32)*(rotatedPoint h hh θ (mixedMap ε hε x)).2 3:ℝ):ℂ)) = _ at hp
    simpa only [neutralScale,Complex.ofReal_mul] using hp
  rw [← hp',mul_div_cancel_left₀ _ hn]

theorem coefficient_real (ε : ℝ) (hε : 0 < ε) (h α w : ℝ)
    (hh : h ≠ 0) (hα : 0 < α) (hw : 0 < w) (θ : ℝ) (x : Product) :
    coefficient ε h α w (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x) =
      ((2*scale*(rotatedPoint h hh θ (mixedMap ε hε x)).2 2+
        (rotatedPoint h hh θ (mixedMap ε hε x)).2 3 : ℝ):ℂ) := by
  rw [coefficient,KFCausalSourcedWidthSymmetricInsertion.coefficient_real ε hε h α w hh hα hw θ 1 x,
    neutralCoefficient_real ε hε h α w hh hα hw θ x]
  simp only [KFCausalPhysicalSpectatorGraph.symmetricIndex,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  rfl

theorem first_mixed (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
    (hb : |h| ≤ Real.pi*ε/3) :
    mixedCoordinates (fieldOutput ε h a w C p b P hε hh ha hw hb pointField) =ᵐ[volume]
      fun z : Product => ((2*scale*z.2 2+z.2 3:ℝ):ℂ)*density ε h a w C p b P z := by
  have hl (z : Product) : pointField (pairedChart.symm z).2 = 2*scale*z.2 2+z.2 3 := by
    rw [pairedChart_symm]
    change scale*(z.1 1+z.2 2)+scale*(z.2 2-z.1 1)+z.2 3 = _
    ring
  have hg := (KFCausalPhysicalSpectatorGraph.mixed_field_graph_iff pointField
    (fun z => 2*scale*z 2+z 3) (by fun_prop) hl _ _).mp
    (first_field_graph ε h a w C p b P hε hh ha hw hb pointField)
  filter_upwards [hg,KFCausalSourcedWidthSecondInput.first_mixed ε h a w C p b P hε hh ha hw hb]
    with z hg hf
  rw [hg,hf]

theorem inserted_density_numerator (ε : ℝ) (hε : 0 < ε) (h a w : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hh : h ≠ 0) (hw : 1 ≤ w)
    (θ : ℝ) (x : Product) :
    ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
      (((2*scale*(rotatedPoint h hh θ (mixedMap ε hε x)).2 2+
        (rotatedPoint h hh θ (mixedMap ε hε x)).2 3:ℝ):ℂ)*
        density ε h a w C p b P (rotatedPoint h hh θ (mixedMap ε hε x))) =
      coefficient ε h (groundWidth h) w (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x)*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w (momentumScale h) θ
          C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  rw [coefficient_real ε hε h (groundWidth h) w hh (groundWidth_positive h hh)
    (lt_of_lt_of_le zero_lt_one hw) θ x,
    ← KFCausalSourcedWidthNormalizedDensity.density_numerator ε hε h a w C p b P hh hw θ x]
  ring

theorem rotated_second_input_coe (ε : ℝ) (hε : 0 < ε) (h a w : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hh : h ≠ 0) (hw : 1 ≤ w)
    (ha : 0 < a) (hb : |h| ≤ Real.pi*ε/3) (θ : ℝ) :
    clockMixed ε hε (inverseL ε hε (action h hh θ
      (fieldOutput ε h a w C p b P hε hh ha hw hb pointField))) =ᵐ[volume]
      fun x => coefficient ε h (groundWidth h) w (momentumScale h) θ
        (x.2 0:ℂ) ((split 2 4).symm x)*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w (momentumScale h) θ
          C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  have he := KFCausalChargeRotatedSecondInput.rotated_second_input ε hε h hh θ _ _
    (first_mixed ε h a w C p b P hε hh ha hw hb)
  filter_upwards [he] with x hx
  exact hx.trans (inserted_density_numerator ε hε h a w C p b P hh hw θ x)

#print axioms neutralCoefficient_real
#print axioms coefficient_real
#print axioms first_mixed
#print axioms inserted_density_numerator
#print axioms rotated_second_input_coe
end
end UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldInsertion
