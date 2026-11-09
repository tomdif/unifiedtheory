/- Quantitative radius comparison and derivative lower bounds for the
actual quartic neutral angular average. The comparison fixes the clock
geometry; charged transport is still needed for the full clock bound. -/
import UnifiedTheory.Audit.KFCausalCorrectedAngularComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralUniformRadialDefect
noncomputable section
open Set
open KFCausalNeutralIntegralDerivatives
open KFCausalCorrectedAngularComparison
open KFCausalNeutralTranslatedMarginal (marginal marginal_eq_total)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
  (z : ℂ) (η L : ℝ)

def physicalAngular (ρ : ℝ) : ℝ := angular (marginal n β b c P z η L) ρ
def areaMean (X : ℝ) : ℝ := physicalAngular n β b c P z η L (Real.sqrt X)

theorem physicalAngular_eq (ρ : ℝ) :
    physicalAngular n β b c P z η L ρ = angular (total n β b c P z η L) ρ := by
  unfold physicalAngular angular
  simp_rw [marginal_eq_total]

theorem total_continuous (hβ : 0 < β) : Continuous (total n β b c P z η L) :=
  (show Differentiable ℝ _ from fun v => (first_derivative_data n β b c P z η L hβ v).2.differentiableAt).continuous

theorem totalSlope_continuous (hβ : 0 < β) : Continuous (totalSlope n β b c P z η L) :=
  (show Differentiable ℝ _ from fun v => (second_derivative_data n β b c P z η L hβ v).2.differentiableAt).continuous

theorem evenCorrected_identity (a v : ℝ) :
    evenCorrected (total n β b c P z η L) a v =
      KFCausalNeutralCorrectedConvexity.symmetric n β b c P z η L a v := by
  unfold evenCorrected KFCausalNeutralCorrectedConvexity.symmetric KFCausalNeutralCorrectedConvexity.corrected
  rw [neg_sq]
  ring

theorem family_corrected_monotone (hβ : 0 < β) (a : ℝ) (ha : 2*(L^2+η^2) ≤ a) :
    MonotoneOn (fun ρ => Real.exp (a*ρ^2)*physicalAngular n β b c P z η L ρ) (Ici 0) := by
  simp_rw [physicalAngular_eq]
  apply angular_corrected_monotone _ (total_continuous n β b c P z η L hβ) a
    (by nlinarith [sq_nonneg L,sq_nonneg η])
  · intro v
    rw [total_form]
    exact KFCausalNeutralQuarticFormBound.energy_nonnegative _
  · have he : evenCorrected (total n β b c P z η L) a =
        KFCausalNeutralCorrectedConvexity.symmetric n β b c P z η L a := funext (evenCorrected_identity n β b c P z η L a)
    rw [he]
    exact KFCausalNeutralCorrectedConvexity.symmetric_monotone n β b c P z η L a hβ ha

theorem physicalAngular_derivative (hβ : 0 < β) (ρ : ℝ) :
    HasDerivAt (physicalAngular n β b c P z η L)
      (angularSlope (totalSlope n β b c P z η L) ρ) ρ := by
  have he : physicalAngular n β b c P z η L = angular (total n β b c P z η L) := funext (physicalAngular_eq n β b c P z η L)
  rw [he]
  exact angular_derivative _ _ (total_continuous n β b c P z η L hβ)
    (totalSlope_continuous n β b c P z η L hβ) (fun v => (first_derivative_data n β b c P z η L hβ v).2) ρ

theorem family_radial_lower (hβ : 0 < β) (a : ℝ) (ha : 2*(L^2+η^2) ≤ a) (ρ : ℝ) (hρ : 0 < ρ) :
    -2*a*ρ*physicalAngular n β b c P z η L ρ ≤ deriv (physicalAngular n β b c P z η L) ρ := by
  have he : physicalAngular n β b c P z η L = angular (total n β b c P z η L) := funext (physicalAngular_eq n β b c P z η L)
  have hm := family_corrected_monotone n β b c P z η L hβ a ha
  rw [he] at hm ⊢
  exact radial_derivative_lower _ _ (total_continuous n β b c P z η L hβ)
    (totalSlope_continuous n β b c P z η L hβ) (fun v => (first_derivative_data n β b c P z η L hβ v).2)
    a hm ρ hρ

theorem areaMean_derivative (hβ : 0 < β) (X : ℝ) (hX : 0 < X) :
    HasDerivAt (areaMean n β b c P z η L)
      (deriv (physicalAngular n β b c P z η L) (Real.sqrt X)/(2*Real.sqrt X)) X := by
  have he := (physicalAngular_derivative n β b c P z η L hβ (Real.sqrt X)).comp X (Real.hasDerivAt_sqrt hX.ne')
  change HasDerivAt (fun x => physicalAngular n β b c P z η L (Real.sqrt x)) _ X
  simpa only [Function.comp_apply,(physicalAngular_derivative n β b c P z η L hβ (Real.sqrt X)).deriv,
    div_eq_mul_inv,one_mul] using he

theorem family_area_lower (hβ : 0 < β) (a : ℝ) (ha : 2*(L^2+η^2) ≤ a) (X : ℝ) (hX : 0 < X) :
    -a*areaMean n β b c P z η L X ≤ deriv (areaMean n β b c P z η L) X := by
  rw [(areaMean_derivative n β b c P z η L hβ X hX).deriv]
  apply (le_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hX))).mpr
  have he := family_radial_lower n β b c P z η L hβ a ha (Real.sqrt X) (Real.sqrt_pos.mpr hX)
  convert he using 1
  unfold areaMean
  ring

omit η L in
theorem actual_uniform_area_lower (hβ : 0 < β) (ε h s : ℝ)
    (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (X : ℝ) (hX : 0 < X) :
    let r := KFCausalClockFloorRelativeShift.scale ε (-h/2) s
    (-KFCausalNeutralUniformDefect.defectConstant/2)*
        areaMean n β b c P z (2*r.im) (KFCausalChargedPairCoordinates.fieldSlope r) X ≤
      deriv (areaMean n β b c P z (2*r.im) (KFCausalChargedPairCoordinates.fieldSlope r)) X := by
  have he := KFCausalNeutralUniformDefect.geometry_bound ε (-h/2) s hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
  have hc : 2*((KFCausalChargedPairCoordinates.fieldSlope (KFCausalClockFloorRelativeShift.scale ε (-h/2) s))^2+
      (2*(KFCausalClockFloorRelativeShift.scale ε (-h/2) s).im)^2) ≤ KFCausalNeutralUniformDefect.defectConstant/2 := by linarith
  simpa only [neg_div] using family_area_lower n β b c P z _ _ hβ
    (KFCausalNeutralUniformDefect.defectConstant/2) hc X hX

#print axioms physicalAngular_eq
#print axioms total_continuous
#print axioms totalSlope_continuous
#print axioms evenCorrected_identity
#print axioms family_corrected_monotone
#print axioms physicalAngular_derivative
#print axioms family_radial_lower
#print axioms areaMean_derivative
#print axioms family_area_lower
#print axioms actual_uniform_area_lower
end
end UnifiedTheory.Audit.KFCausalNeutralUniformRadialDefect
