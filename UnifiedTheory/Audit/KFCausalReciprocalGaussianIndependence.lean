/- Every nontrivial reciprocal-width packet lies outside the existing
centered/paired/corrected-quartic span. Three balanced radial evaluations
detect the exponential profile against the old affine radial profile. -/
import UnifiedTheory.Audit.KFCausalChargedGeneratingProfile
import UnifiedTheory.Audit.KFCausalPairedQuarticIndependence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianIndependence
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (trialState clockFunction neutralWidth)
open KFCausalClockFloorCoherentStates (weight weight_coe weight_ne_zero)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalChargeZeroSwapWitness (imbalance)
open KFCausalQuarticChargeProfiles (correctedWeight)
open KFCausalPairedQuarticIndependence (radialPoint radial_values)
open KFCausalReciprocalGaussianStates (coordinateDensity coordinateQuadratic)
open KFCausalReciprocalGaussianCharge (state state_coordinates_coe)

theorem width_gap_positive (α w : ℝ) (hα : 0 < α) (hw : 0 < w) (hne : w ≠ 1) :
    0 < α*(w+1/w-2) := by
  have he : w+1/w-2 = (w-1)^2/w := by
    field_simp
    ring
  rw [he]
  exact mul_pos hα (div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) hw)

theorem exponential_not_affine (γ : ℝ) (hγ : 0 < γ) (b d : ℂ) :
    ¬ ∀ t : ℝ, (Real.exp (-γ*t^2):ℂ) = b+d*(t^2:ℝ) := by
  intro he
  have h0 := congrArg Complex.re (he 0)
  have h1 : Real.exp (-γ) = b.re+d.re := by
    simpa only [one_pow,mul_one,Complex.ofReal_one,
      Complex.add_re,Complex.ofReal_re] using congrArg Complex.re (he 1)
  have h2 := congrArg Complex.re (he (Real.sqrt 2))
  have hexp : Real.exp (-γ*2) = (Real.exp (-γ))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  norm_num at h0
  simp only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,hexp] at h2
  have hs : (Real.exp (-γ)-1)^2 = 0 := by nlinarith
  have hz : Real.exp (-γ)-1 = 0 := eq_zero_of_pow_eq_zero hs
  have hl : Real.exp (-γ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem radial_density (ε a h w t : ℝ) :
    coordinateDensity (groundWidth h) (neutralWidth h) w (momentumScale h)
        (clockFunction ε a) (radialPoint t) =
      (Real.exp (-(groundWidth h)*(w+1/w-2)*t^2):ℂ)*weight ε a h (radialPoint t) := by
  simp only [coordinateDensity,KFCausalReciprocalGaussianStates.coordinateQuadratic_coordinates,
    weight,KFCausalChargeGaussianGeometry.profile,
    KFCausalChargeGaussianGeometry.radius_coordinates,radialPoint]
  norm_num
  have he (A B C p z : ℂ) (hAB : A = B+C) :
      p*z*Complex.exp A = Complex.exp B*(p*(z*Complex.exp C)) := by
    rw [hAB,Complex.exp_add]
    ring
  apply he
  push_cast
  ring

theorem state_not_quartic_combination (ε a h w : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 0 < w) (hne : w ≠ 1)
    (b d e : ℂ) :
    state ε a h w hε ha hh hw ≠
      b • trialState ε a h hε ha hh+
        d • KFCausalChargedPairDomain.state ε a h hε ha hh+
        e • KFCausalPairedQuarticCharge.correctedState ε a h hε ha hh := by
  intro hstate
  have hmap := congrArg chargeCoordinates hstate
  rw [map_add,map_add,map_smul,map_smul,map_smul] at hmap
  let V : Fin 3 → Hilbert := ![trialState ε a h hε ha hh,
    KFCausalChargedPairDomain.state ε a h hε ha hh,
    KFCausalPairedQuarticCharge.correctedState ε a h hε ha hh]
  let C : Fin 3 → ℂ := ![b,d,e]
  let F : Fin 3 → Joint 2 4 → ℂ := ![weight ε a h,
    (fun x => ((imbalance (momentumScale h) x:ℂ)/2)*weight ε a h x),
    KFCausalPairedQuarticCharge.correctedDensity ε a h]
  have hF (i : Fin 3) : chargeCoordinates (V i) =ᵐ[volume] F i := by
    fin_cases i
    · exact weight_coe ε a h hε ha hh
    · exact KFCausalChargedPairCharge.state_chargeCoordinates ε a h hε ha hh
    · exact KFCausalPairedQuarticCharge.corrected_coordinates_coe ε a h hε ha hh
  have hsum := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume C
    (fun i => chargeCoordinates (V i)) F hF
  have hm : chargeCoordinates (state ε a h w hε ha hh hw) =
      ∑ i, C i • chargeCoordinates (V i) := by
    rw [hmap]
    simp [V,C,Fin.sum_univ_succ,add_assoc]
  have he : coordinateDensity (groundWidth h) (neutralWidth h) w (momentumScale h)
      (clockFunction ε a) =ᵐ[volume] fun x =>
      (b+(d/2)*(imbalance (momentumScale h) x:ℂ)+e*(correctedWeight (groundWidth h)
        (momentumScale h) x:ℂ))*weight ε a h x := by
    filter_upwards [state_coordinates_coe ε a h w hε ha hh hw,hsum] with x hx hs
    rw [hm,hs] at hx
    rw [← hx]
    simp only [C,F,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,KFCausalPairedQuarticCharge.correctedDensity]
    ring
  have hcont : Continuous (fun x : Joint 2 4 =>
      (b+(d/2)*(imbalance (momentumScale h) x:ℂ)+e*(correctedWeight (groundWidth h)
        (momentumScale h) x:ℂ))*weight ε a h x) := by
    have hi : Continuous (imbalance (momentumScale h)) := by
      unfold imbalance KFCausalChargeZeroSwapWitness.imbalanceRaw KFCausalNormalizedChargeFlow.dilate
      fun_prop
    have hq := KFCausalQuarticChargeProfiles.correctedWeight_continuous (groundWidth h) (momentumScale h)
    have hwc := KFCausalPairedQuarticCharge.weight_continuous ε a h
    fun_prop
  have hpoint := Measure.eq_of_ae_eq he
    (KFCausalReciprocalGaussianStates.coordinateDensity_continuous _ _ _ _ _
      (KFCausalClockFloorInvariantTrial.clockFunction_continuous ε a)) hcont
  apply exponential_not_affine ((groundWidth h)*(w+1/w-2))
    (width_gap_positive _ _ (groundWidth_positive h hh) hw hne)
    (b+e/(8*(groundWidth h:ℂ)^2)) (-e/(2*(groundWidth h:ℂ)))
  intro t
  have hr := congrFun hpoint (radialPoint t)
  rw [radial_density] at hr
  have he' := mul_right_cancel₀ (weight_ne_zero ε a h hε hh (radialPoint t)) hr
  rw [(radial_values (groundWidth h) (momentumScale h) t).1,
    (radial_values (groundWidth h) (momentumScale h) t).2] at he'
  convert he' using 1 <;> push_cast <;> ring

#print axioms width_gap_positive
#print axioms exponential_not_affine
#print axioms radial_density
#print axioms state_not_quartic_combination
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianIndependence
