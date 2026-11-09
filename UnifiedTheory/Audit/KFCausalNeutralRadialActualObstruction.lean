/- Failure of the proposed quartic radius monotonicity at an actual
admissible clock scale. This keeps the clock scale fixed while testing
radius monotonicity; it does not assert growth along the full clock flow. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialActualGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialActualObstruction
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open KFCausalNeutralRadialCoherentKernel (quartic mass)
open KFCausalNeutralRadialCurvature (quarticSlope quarticSecond quartic_derivative quarticSlope_derivative)
open KFCausalNeutralRadialActualGeometry (marginal geometry displacement field source profile slice)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity profileSum)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

def exponentSlope (η v : ℝ) : ℝ := 4*η^2*v-4/3
def marginalSlope (η L v : ℝ) : ℝ := Real.exp (2*η^2*v^2-4*v/3)*
  (exponentSlope η v*quartic (2+L*v)+L*quarticSlope (2+L*v))
def marginalSecond (η L v : ℝ) : ℝ := Real.exp (2*η^2*v^2-4*v/3)*
  ((4*η^2+(exponentSlope η v)^2)*quartic (2+L*v)+
    2*exponentSlope η v*L*quarticSlope (2+L*v)+L^2*quarticSecond (2+L*v))
def curvature (η L : ℝ) : ℝ := 555*η^2/32+185/24-46*L/3+55*L^2/8

theorem marginal_derivative (η L v : ℝ) :
    HasDerivAt (marginal η L) (marginalSlope η L v) v := by
  have he := ((((hasDerivAt_id v).pow 2).const_mul (2*η^2)).sub
    (((hasDerivAt_id v).const_mul 4).div_const 3)).exp
  have hp := (quartic_derivative (2+L*v)).comp v (((hasDerivAt_id v).const_mul L).const_add 2)
  convert he.mul hp using 1
  dsimp [marginal,marginalSlope,exponentSlope]
  ring

theorem marginalSlope_derivative (η L v : ℝ) :
    HasDerivAt (marginalSlope η L) (marginalSecond η L v) v := by
  have he := ((((hasDerivAt_id v).pow 2).const_mul (2*η^2)).sub
    (((hasDerivAt_id v).const_mul 4).div_const 3)).exp
  have hl : HasDerivAt (exponentSlope η) (4*η^2) v := by
    simpa only [mul_one] using ((hasDerivAt_id v).const_mul (4*η^2)).sub_const (4/3)
  have hp := (quartic_derivative (2+L*v)).comp v (((hasDerivAt_id v).const_mul L).const_add 2)
  have hq := (quarticSlope_derivative (2+L*v)).comp v (((hasDerivAt_id v).const_mul L).const_add 2)
  convert he.mul ((hl.mul hp).add (hq.const_mul L)) using 1
  dsimp [marginalSlope,marginalSecond,exponentSlope]
  ring

theorem curvature_negative (η L : ℝ) (hη : |η| ≤ 1/64) (hL : |L-1| ≤ 1/64) :
    curvature η L < 0 := by
  have he := mul_self_le_mul_self (abs_nonneg η) hη
  have hl := mul_self_le_mul_self (abs_nonneg (L-1)) hL
  rw [← sq, sq_abs] at he hl
  have hb := abs_le.mp hL
  unfold curvature
  nlinarith

def angular (η L ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, marginal η L (ρ*Real.sin θ))/(2*Real.pi)
def angularSlope (η L ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, Real.sin θ*marginalSlope η L (ρ*Real.sin θ))/(2*Real.pi)
def angularSecond (η L ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, (Real.sin θ)^2*marginalSecond η L (ρ*Real.sin θ))/(2*Real.pi)

theorem angular_derivative (η L ρ : ℝ) :
    HasDerivAt (angular η L) (angularSlope η L ρ) ρ := by
  have hd := KFCausalCompactAngularDerivative.integral_hasDerivAt
    (fun t θ => marginal η L (t*Real.sin θ))
    (fun t θ => Real.sin θ*marginalSlope η L (t*Real.sin θ))
    (by unfold Function.uncurry marginal quartic; fun_prop)
    (by unfold Function.uncurry marginalSlope exponentSlope quartic quarticSlope; fun_prop)
    (fun t θ => by
      convert (marginal_derivative η L (t*Real.sin θ)).comp t
        ((hasDerivAt_id t).mul_const (Real.sin θ)) using 1
      dsimp
      ring) ρ
  exact hd.div_const _

theorem angularSlope_derivative (η L ρ : ℝ) :
    HasDerivAt (angularSlope η L) (angularSecond η L ρ) ρ := by
  have hd := KFCausalCompactAngularDerivative.integral_hasDerivAt
    (fun t θ => Real.sin θ*marginalSlope η L (t*Real.sin θ))
    (fun t θ => (Real.sin θ)^2*marginalSecond η L (t*Real.sin θ))
    (by unfold Function.uncurry marginalSlope exponentSlope quartic quarticSlope; fun_prop)
    (by unfold Function.uncurry marginalSecond exponentSlope quartic quarticSlope quarticSecond; fun_prop)
    (fun t θ => by
      convert ((marginalSlope_derivative η L (t*Real.sin θ)).comp t
        ((hasDerivAt_id t).mul_const (Real.sin θ))).const_mul (Real.sin θ) using 1
      dsimp
      ring) ρ
  exact hd.div_const _

theorem angularSlope_zero (η L : ℝ) : angularSlope η L 0 = 0 := by
  simp only [angularSlope,zero_mul,intervalIntegral.integral_mul_const]
  rw [integral_sin]
  simp

theorem angularSecond_zero (η L : ℝ) : angularSecond η L 0 = curvature η L := by
  simp only [angularSecond,zero_mul,intervalIntegral.integral_mul_const]
  rw [integral_sin_sq]
  simp only [Real.sin_neg,Real.sin_pi,neg_zero,zero_mul,sub_zero,sub_neg_eq_add,zero_add]
  norm_num [marginalSecond,exponentSlope,quartic,quarticSlope,quarticSecond]
  unfold curvature
  field_simp
  ring

theorem angular_not_monotone (η L : ℝ) (hη : |η| ≤ 1/64) (hL : |L-1| ≤ 1/64) :
    ¬ MonotoneOn (angular η L) (Ici 0) := by
  intro hm
  have hp (x : ℝ) (hx : 0 < x) : 0 ≤ angularSlope η L x := by
    rw [← (angular_derivative η L x).deriv,← derivWithin_of_mem_nhds (Ici_mem_nhds hx)]
    exact hm.derivWithin_nonneg
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp (angularSlope_derivative η L 0)).2
  have hnonneg : 0 ≤ angularSecond η L 0 := by
    apply ge_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Ioi] at hx
    simpa only [slope_def_field,angularSlope_zero,sub_zero] using div_nonneg (hp x hx) hx.le
  rw [angularSecond_zero] at hnonneg
  exact (not_lt_of_ge hnonneg) (curvature_negative η L hη hL)

def physicalAngular (ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, ∫ x, slice (ρ*Real.sin θ) x)/(2*Real.pi)

theorem positiveDensity_slice (p : Joint) :
    positiveDensity 1 32 1 (fun _ => 1) geometry (fun _ => 1)
      (fun _ => exponentialProfile source 1 1) p =
        ‖Complex.exp (-chart 32 geometry (p.1.1^2+(p.1.2 0)^2) p.2)‖^2*
          slice (p.1.2 0) (p.1.2 1) := by
  rw [KFCausalReciprocalNeutralHolomorphic.density_absorbed]
  simp only [profileSum,laplaceSum,Fin.sum_univ_one,Complex.ofReal_one,one_mul,norm_mul,mul_pow,mul_one]
  have he (v x : ℝ) : KFCausalReciprocalNeutralKernel.neutral geometry v x =
      (x:ℂ)+(displacement*v:ℝ)*Complex.I := by
    unfold KFCausalReciprocalNeutralKernel.neutral displacement
    push_cast
    ring
  rw [he]
  unfold slice profile field KFCausalChargedPairCoordinates.fieldSlope
  ring

theorem physicalAngular_eq (ρ : ℝ) :
    physicalAngular ρ = Real.exp 8*mass*angular displacement field ρ := by
  unfold physicalAngular
  simp_rw [KFCausalNeutralRadialActualGeometry.slice_integral]
  rw [intervalIntegral.integral_const_mul]
  unfold angular
  ring

theorem physicalAngular_not_monotone : ¬ MonotoneOn physicalAngular (Ici 0) := by
  intro hm
  apply angular_not_monotone displacement field
    KFCausalNeutralRadialActualGeometry.geometry_bounds.1 KFCausalNeutralRadialActualGeometry.geometry_bounds.2
  intro a ha b hb hab
  have he := hm ha hb hab
  simp only [physicalAngular_eq] at he
  exact le_of_mul_le_mul_left he
    (mul_pos (Real.exp_pos _) KFCausalNeutralRadialCoherentKernel.mass_positive)

theorem actual_radius_comparison_fails :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ physicalAngular b < physicalAngular a := by
  have hn := physicalAngular_not_monotone
  simp only [MonotoneOn,mem_Ici,not_forall,not_le] at hn
  obtain ⟨a,ha,b,hb,hab,hbad⟩ := hn
  refine ⟨a,b,ha,lt_of_le_of_ne hab ?_,hbad⟩
  intro he
  subst b
  exact lt_irrefl _ hbad

#print axioms marginal_derivative
#print axioms marginalSlope_derivative
#print axioms curvature_negative
#print axioms angular_derivative
#print axioms angularSlope_derivative
#print axioms angularSlope_zero
#print axioms angularSecond_zero
#print axioms angular_not_monotone
#print axioms positiveDensity_slice
#print axioms physicalAngular_eq
#print axioms physicalAngular_not_monotone
#print axioms actual_radius_comparison_fails
end
end UnifiedTheory.Audit.KFCausalNeutralRadialActualObstruction
