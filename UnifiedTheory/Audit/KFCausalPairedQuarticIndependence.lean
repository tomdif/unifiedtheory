/- The corrected quartic is a genuinely additional state direction:
it is not a complex combination of the centered and paired packets
with the same clock profile. No closure or dynamical invariance is asserted. -/
import UnifiedTheory.Audit.KFCausalPairedQuarticCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalPairedQuarticIndependence
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPairedQuarticCharge
open KFCausalQuarticChargeProfiles (correctedWeight)
open KFCausalChargeZeroSwapWitness (imbalance imbalanceRaw)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive radius_coordinates)
open KFCausalNormalizedChargeFlow (momentumScale dilate)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorCoherentStates (weight weight_coe weight_ne_zero)
open KFCausalClockFloorInvariantTrial (trialState)

def radialPoint (t : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr j => if j = 1 ∨ j = 2 then t else 0

theorem radial_values (α c t : ℝ) :
    imbalance c (radialPoint t) = 0 ∧
      correctedWeight α c (radialPoint t) = -t^2/(2*α)+1/(8*α^2) := by
  constructor
  · norm_num [imbalance,imbalanceRaw,dilate,radialPoint,Fin.reduceEq]
  · simp [correctedWeight,imbalance,imbalanceRaw,dilate,radialPoint,radius_coordinates]
    ring

theorem not_affine_imbalance (α c : ℝ) (hα : 0 < α) (b d : ℂ) :
    ¬ ∀ x : Joint 2 4, (correctedWeight α c x:ℂ) = b+d*(imbalance c x:ℂ) := by
  intro hf
  have h0 := hf (radialPoint 0)
  have h1 := hf (radialPoint 1)
  rw [(radial_values α c 0).1,Complex.ofReal_zero,mul_zero,add_zero] at h0
  rw [(radial_values α c 1).1,Complex.ofReal_zero,mul_zero,add_zero] at h1
  have he := Complex.ofReal_injective (h1.trans h0.symm)
  rw [(radial_values α c 0).2,(radial_values α c 1).2] at he
  norm_num at he
  have hn : (1:ℝ)/(2*α) ≠ 0 := one_div_ne_zero (mul_ne_zero (by norm_num) hα.ne')
  apply hn
  linarith

theorem state_not_centered_paired_combination (ε a h : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (b d : ℂ) :
    correctedState ε a h hε ha hh ≠
      b • trialState ε a h hε ha hh+d • KFCausalChargedPairDomain.state ε a h hε ha hh := by
  intro hstate
  have hmap := congrArg chargeCoordinates hstate
  rw [map_add,map_smul,map_smul] at hmap
  have he : correctedDensity ε a h =ᵐ[volume] fun x =>
      (b+(d/2)*(imbalance (momentumScale h) x:ℂ))*weight ε a h x := by
    filter_upwards [corrected_coordinates_coe ε a h hε ha hh,
      Lp.coeFn_add (b • chargeCoordinates (trialState ε a h hε ha hh))
        (d • chargeCoordinates (KFCausalChargedPairDomain.state ε a h hε ha hh)),
      Lp.coeFn_smul b (chargeCoordinates (trialState ε a h hε ha hh)),
      Lp.coeFn_smul d (chargeCoordinates (KFCausalChargedPairDomain.state ε a h hε ha hh)),
      weight_coe ε a h hε ha hh,
      KFCausalChargedPairCharge.state_chargeCoordinates ε a h hε ha hh] with x hq hs hb hd h0 h1
    rw [hmap,hs,Pi.add_apply,hb,hd,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,h0,h1] at hq
    rw [← hq]
    ring
  have hI : Continuous (imbalance (momentumScale h)) := by
    unfold imbalance imbalanceRaw dilate
    fun_prop
  have hcont : Continuous (fun x : Joint 2 4 =>
      (b+(d/2)*(imbalance (momentumScale h) x:ℂ))*weight ε a h x) :=
    (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp hI))).mul
      (weight_continuous ε a h)
  have hpoint := Measure.eq_of_ae_eq he (correctedDensity_continuous ε a h) hcont
  apply not_affine_imbalance (groundWidth h) (momentumScale h) (groundWidth_positive h hh) b (d/2)
  intro x
  exact mul_right_cancel₀ (weight_ne_zero ε a h hε hh x) (congrFun hpoint x)

#print axioms radial_values
#print axioms not_affine_imbalance
#print axioms state_not_centered_paired_combination
end
end UnifiedTheory.Audit.KFCausalPairedQuarticIndependence
