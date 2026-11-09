/- The actual mixed-shift spectral state in physical coordinates. The
field and the Gaussian retain their distinct relative clock scales. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianPhysical
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMixedFieldPhysicalProfile
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse flow)
open KFCausalClockFloorRelativeShift (scale inverse relative)
open KFCausalClockFloorShearBounds (complexScale)
open KFCausalClockFloorDisplacedShiftPhase (grouped complexScale_sub_real)
open KFCausalClockFloorGroupedCoordinates (grouping transverseGrouping transverseGrouping_apply)
open KFCausalClockFloorLpCoordinates (weightedFunction)
open KFCausalClockFloorFlow (coordinateHomeomorph)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalMixedFieldGaussianSpectral (configurationLine state)
open KFCausalMixedFieldGaussianStrip (degree fieldLine)

def field (r : ℂ) (q : Transverse) : ℂ := (q 4:ℂ)+(3*r-2)*((q 2:ℂ)+(q 3:ℂ))
def profile (ε a α β δ y : ℝ) (k : ℕ) (x : Configuration) : ℂ :=
  field (scale ε y x.1) x.2^k * KFCausalRelativeGaussianDifferential.profile
    (clockAmplitude ε a 0 (y+δ)) (scale ε (y+δ)) α β 0 x

theorem grouping_eq (q : Transverse) : transverseGrouping q = grouped q := by
  rw [transverseGrouping_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem field_recenter (z : ℂ) (s : ℝ) (q : Transverse) :
    KFCausalMixedFieldGaussianBounds.field z (transverseGrouping (flow (-s) q)) =
      field (complexScale (z-(s:ℂ))) q := by
  rw [grouping_eq,complexScale_sub_real]
  simp only [KFCausalMixedFieldGaussianBounds.field,field,grouped,flow,
    KFCausalClockFloorShearBounds.mix]
  push_cast
  ring

theorem fieldLine_at_coordinate (ε y : ℝ) (hε : 0 < ε) (x : Configuration) :
    fieldLine ε y (grouping (coordinateHomeomorph ε hε x)) = field (scale ε y x.1) x.2 := by
  change KFCausalMixedFieldGaussianBounds.field (inverse ε y x.1)
    (transverseGrouping (flow (-x.1) x.2)) = _
  exact field_recenter _ _ _

theorem configuration_formula (ε a α β δ y : ℝ) (j : Fin 2) (x : Configuration) :
    configurationLine ε a α β δ y j x = fieldLine ε y (grouping x)^degree j *
      KFCausalClockFloorCoherentSpectral.configurationLine ε a α β 0 0 (y+δ) x := by
  rw [configurationLine,KFCausalMixedFieldGaussianStrip.line_formula,
    KFCausalMixedFieldGaussianPhysical.coherent_zero_line]

theorem weighted_profile (ε a α β δ y : ℝ) (j : Fin 2) (hε : 0 < ε) (x : Configuration) :
    weightedFunction ε hε (configurationLine ε a α β δ y j) x = profile ε a α β δ y (degree j) x := by
  have hg := KFCausalShiftedGaussianPhysicalProfile.physical_profile ε a α β 0 (y+δ) 0 hε x
  unfold weightedFunction at hg ⊢
  rw [configuration_formula,fieldLine_at_coordinate]
  unfold profile
  rw [← hg]
  ring

theorem state_profile (ε a α β δ y : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    state ε a α β δ y j hε ha hα hβ hw hy hyr =ᵐ[volume] profile ε a α β δ y (degree j) := by
  filter_upwards [KFCausalMixedFieldGaussianSpectral.state_coe ε a α β δ y j hε ha hα hβ hw hy hyr] with x hx
  exact hx.trans (weighted_profile ε a α β δ y j hε x)

theorem field_smooth (r : ℝ → ℂ) (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (fun x : Configuration => field (r x.1) x.2) := by
  have hq (i : Fin 5) : ContDiff ℝ 1 (fun x : Configuration => (x.2 i:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop)
  exact (hq 4).add (((contDiff_const.mul (hr.comp contDiff_fst)).sub contDiff_const).mul
    ((hq 2).add (hq 3)))

theorem profile_smooth (ε a α β δ y : ℝ) (k : ℕ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    ContDiff ℝ 1 (profile ε a α β δ y k) := by
  have hf := field_smooth (scale ε y) (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy)
  exact (hf.pow k).mul (KFCausalRelativeGaussianDifferential.profile_smooth _ _
    (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a 0 (y+δ) hε hyr)
    (KFCausalClockFloorRelativeShift.scale_smooth ε (y+δ) hε hyr) α β 0)

#print axioms grouping_eq
#print axioms field_recenter
#print axioms fieldLine_at_coordinate
#print axioms configuration_formula
#print axioms weighted_profile
#print axioms state_profile
#print axioms field_smooth
#print axioms profile_smooth
end
end UnifiedTheory.Audit.KFCausalMixedFieldPhysicalProfile
