/- The quantitative radial derivative bound applies to the exact
absorbed joint Laplace profile at each fixed charged coordinate. No
diagonal truncation or separation of charged widths is used. -/
import UnifiedTheory.Audit.KFCausalNeutralUniformRadialDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalJointNeutralRadialEstimate
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalReciprocalNeutralHolomorphic (weightedProfile)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalNeutralJointCurvatureForm (coefficients joint_profile_family)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalClockFloorRelativeShift (scale)

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r z : ℂ)

def jointSlice (v x : ℝ) : ℝ := potential (x+fieldSlope r*v)*
  ‖profileSum n w c (fun i => weightedProfile β (exponentialProfile (b i) 1 (P i))) z (neutral r v x)‖^2
def jointArea (X : ℝ) : ℝ := KFCausalCorrectedAngularComparison.angular
  (fun v => ∫ x, jointSlice n β w b c P r z v x) (Real.sqrt X)

theorem jointSlice_eq (v x : ℝ) :
    jointSlice n β w b c P r z v x =
      KFCausalNeutralTranslatedMarginal.slice n β b (coefficients n w c z) P 0 (2*r.im) (fieldSlope r) v x := by
  unfold jointSlice KFCausalNeutralTranslatedMarginal.slice
  rw [joint_profile_family]
  simp only [neutral,add_zero,Complex.ofReal_mul,Complex.ofReal_ofNat]

theorem jointSlice_integrable (hβ : 0 < β) (v : ℝ) :
    Integrable (jointSlice n β w b c P r z v) := by
  change Integrable (fun x => jointSlice n β w b c P r z v x)
  simp_rw [jointSlice_eq]
  exact KFCausalNeutralTranslatedMarginal.slice_integrable n β b (coefficients n w c z) P 0 (2*r.im) (fieldSlope r) hβ v

theorem jointArea_eq (X : ℝ) :
    jointArea n β w b c P r z X =
      KFCausalNeutralUniformRadialDefect.areaMean n β b (coefficients n w c z) P 0 (2*r.im) (fieldSlope r) X := by
  unfold jointArea KFCausalNeutralUniformRadialDefect.areaMean KFCausalNeutralUniformRadialDefect.physicalAngular
    KFCausalCorrectedAngularComparison.angular KFCausalNeutralTranslatedMarginal.marginal
  simp_rw [jointSlice_eq]

omit r in
theorem actual_uniform_joint_area_lower (hβ : 0 < β) (ε h s : ℝ)
    (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (X : ℝ) (hX : 0 < X) :
    let r := scale ε (-h/2) s
    (-KFCausalNeutralUniformDefect.defectConstant/2)*jointArea n β w b c P r z X ≤
      deriv (jointArea n β w b c P r z) X := by
  have he : jointArea n β w b c P (scale ε (-h/2) s) z =
      KFCausalNeutralUniformRadialDefect.areaMean n β b (coefficients n w c z) P 0
        (2*(scale ε (-h/2) s).im) (fieldSlope (scale ε (-h/2) s)) :=
    funext (jointArea_eq n β w b c P (scale ε (-h/2) s) z)
  dsimp only
  rw [he]
  exact KFCausalNeutralUniformRadialDefect.actual_uniform_area_lower n β b (coefficients n w c z) P 0 hβ ε h s hε hb X hX

#print axioms jointSlice_eq
#print axioms jointSlice_integrable
#print axioms jointArea_eq
#print axioms actual_uniform_joint_area_lower
end
end UnifiedTheory.Audit.KFCausalJointNeutralRadialEstimate
