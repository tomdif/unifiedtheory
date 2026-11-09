/- An exact obstruction to radius monotonicity in the quartic neutral
slice of the joint positive formula. The chosen geometry has positive
charged Gaussian widths. No assertion identifies this geometry with a
particular physical clock value or refutes the integrated response bound. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialObstruction
noncomputable section
open MeasureTheory Set
open KFCausalNeutralRadialCoherentKernel (mass source profile slice)
open KFCausalNeutralRadialCurvature (angular angularSlope angularSecond)
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity profileSum)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalChargedPairCoordinates (fieldSlope)

def geometry : ℂ := 1+(1/200:ℂ)*Complex.I
def physicalAngular (ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, ∫ x, slice (ρ*Real.sin θ) x)/(2*Real.pi)

theorem geometry_neutral (v x : ℝ) :
    neutral geometry v x = (x:ℂ)+(v/100:ℝ)*Complex.I := by
  simp [neutral,geometry]
  ring

theorem geometry_widths :
    0 < (KFCausalReciprocalCrossGeometry.A 64 1 1 geometry).re ∧
      0 < (KFCausalReciprocalCrossGeometry.B 64 1 1 geometry).re ∧
      0 < (KFCausalReciprocalCrossGeometry.C 64 1 1 1 geometry).re := by
  norm_num [KFCausalReciprocalCrossGeometry.A,KFCausalReciprocalCrossGeometry.B,
    KFCausalReciprocalCrossGeometry.C,geometry,Complex.mul_re,Complex.mul_im,pow_two]

theorem positiveDensity_slice (α : ℝ) (p : Joint) :
    positiveDensity 1 α 1 (fun _ => 1) geometry (fun _ => 1)
      (fun _ => exponentialProfile source 1 1) p =
        ‖Complex.exp (-chart α geometry (p.1.1^2+(p.1.2 0)^2) p.2)‖^2*
          slice (p.1.2 0) (p.1.2 1) := by
  rw [KFCausalReciprocalNeutralHolomorphic.density_absorbed]
  simp only [profileSum,laplaceSum,Fin.sum_univ_one,Complex.ofReal_one,one_mul,norm_mul,mul_pow,mul_one]
  rw [geometry_neutral]
  have he : fieldSlope geometry = 1 := by norm_num [fieldSlope,geometry]
  rw [he,one_mul]
  unfold slice profile
  ring

theorem physicalAngular_eq (ρ : ℝ) :
    physicalAngular ρ = Real.exp 8*mass*angular ρ :=
  KFCausalNeutralRadialCurvature.actual_angular_integral ρ

theorem physicalAngular_derivative (ρ : ℝ) :
    HasDerivAt physicalAngular (Real.exp 8*mass*angularSlope ρ) ρ := by
  have he : physicalAngular = fun t => Real.exp 8*mass*angular t := funext physicalAngular_eq
  rw [he]
  exact (KFCausalNeutralRadialCurvature.angular_derivative ρ).const_mul _

theorem physicalAngular_second :
    HasDerivAt (fun t => deriv physicalAngular t)
      (Real.exp 8*mass*(-47889/64000)) 0 := by
  have he : deriv physicalAngular = fun t => Real.exp 8*mass*angularSlope t :=
    funext (fun t => (physicalAngular_derivative t).deriv)
  rw [he]
  simpa only [KFCausalNeutralRadialCurvature.angularSecond_zero] using
    (KFCausalNeutralRadialCurvature.angularSlope_derivative 0).const_mul (Real.exp 8*mass)

theorem physicalAngular_curvature_negative : deriv (deriv physicalAngular) 0 < 0 := by
  rw [physicalAngular_second.deriv]
  exact mul_neg_of_pos_of_neg
    (mul_pos (Real.exp_pos _) KFCausalNeutralRadialCoherentKernel.mass_positive) (by norm_num)

theorem physicalAngular_not_monotone : ¬ MonotoneOn physicalAngular (Ici 0) := by
  intro hm
  apply KFCausalNeutralRadialCurvature.angular_not_monotone
  intro a ha b hb hab
  have he := hm ha hb hab
  simp only [physicalAngular_eq] at he
  exact le_of_mul_le_mul_left he
    (mul_pos (Real.exp_pos _) KFCausalNeutralRadialCoherentKernel.mass_positive)

theorem radius_comparison_fails :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ physicalAngular b < physicalAngular a := by
  have hn := physicalAngular_not_monotone
  simp only [MonotoneOn,mem_Ici,not_forall,not_le] at hn
  obtain ⟨a,ha,b,hb,hab,hbad⟩ := hn
  refine ⟨a,b,ha,lt_of_le_of_ne hab ?_,hbad⟩
  intro he
  subst b
  exact lt_irrefl _ hbad

#print axioms geometry_neutral
#print axioms geometry_widths
#print axioms positiveDensity_slice
#print axioms physicalAngular_eq
#print axioms physicalAngular_derivative
#print axioms physicalAngular_second
#print axioms physicalAngular_curvature_negative
#print axioms physicalAngular_not_monotone
#print axioms radius_comparison_fails
end
end UnifiedTheory.Audit.KFCausalNeutralRadialObstruction
