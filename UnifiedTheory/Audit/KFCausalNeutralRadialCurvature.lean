/- The coherent quartic angular average has strictly negative curvature
at radius zero. Thus neutral analyticity alone does not make the full
quartic angular average increase with radius. This is a slice obstruction,
not a counterexample to the integrated Hamiltonian response estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialCoherentKernel
import UnifiedTheory.Audit.KFCausalCompactAngularDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialCurvature
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open KFCausalNeutralRadialCoherentKernel (quartic marginal mass slice)

def quarticSlope (v : ℝ) : ℝ := v^3+7*v/4
def quarticSecond (v : ℝ) : ℝ := 3*v^2+7/4
def exponentSlope (v : ℝ) : ℝ := v/2500-4/3
def marginalSlope (v : ℝ) : ℝ := Real.exp (v^2/5000-4*v/3)*
  (exponentSlope v*quartic (2+v)+quarticSlope (2+v))
def marginalSecond (v : ℝ) : ℝ := Real.exp (v^2/5000-4*v/3)*
  ((1/2500+(exponentSlope v)^2)*quartic (2+v)+
    2*exponentSlope v*quarticSlope (2+v)+quarticSecond (2+v))

theorem quartic_derivative (v : ℝ) : HasDerivAt quartic (quarticSlope v) v := by
  convert (((hasDerivAt_id v).pow 4).div_const 4 |>.add
    (((hasDerivAt_id v).pow 2).const_mul 7 |>.div_const 8)).add_const (75/64) using 1
  dsimp [quartic,quarticSlope]
  ring

theorem quarticSlope_derivative (v : ℝ) : HasDerivAt quarticSlope (quarticSecond v) v := by
  convert ((hasDerivAt_id v).pow 3).add (((hasDerivAt_id v).const_mul 7).div_const 4) using 1
  dsimp [quarticSlope,quarticSecond]
  ring

theorem marginal_derivative (v : ℝ) : HasDerivAt marginal (marginalSlope v) v := by
  have he := (((hasDerivAt_id v).pow 2).div_const 5000 |>.sub
    (((hasDerivAt_id v).const_mul 4).div_const 3)).exp
  have hp := (quartic_derivative (2+v)).comp v ((hasDerivAt_id v).const_add 2)
  convert he.mul hp using 1
  dsimp [marginal,marginalSlope,exponentSlope]
  ring

theorem marginalSlope_derivative (v : ℝ) : HasDerivAt marginalSlope (marginalSecond v) v := by
  have he := (((hasDerivAt_id v).pow 2).div_const 5000 |>.sub
    (((hasDerivAt_id v).const_mul 4).div_const 3)).exp
  have hl : HasDerivAt exponentSlope (1/2500) v :=
    ((hasDerivAt_id v).div_const 2500).sub_const (4/3)
  have hp := (quartic_derivative (2+v)).comp v ((hasDerivAt_id v).const_add 2)
  have hq := (quarticSlope_derivative (2+v)).comp v ((hasDerivAt_id v).const_add 2)
  convert he.mul ((hl.mul hp).add hq) using 1
  dsimp [marginalSlope,marginalSecond,exponentSlope]
  ring

theorem marginalSecond_zero : marginalSecond 0 = -47889/32000 := by
  norm_num [marginalSecond,exponentSlope,quartic,quarticSlope,quarticSecond]

def angular (ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, marginal (ρ*Real.sin θ))/(2*Real.pi)
def angularSlope (ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, Real.sin θ*marginalSlope (ρ*Real.sin θ))/(2*Real.pi)
def angularSecond (ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, (Real.sin θ)^2*marginalSecond (ρ*Real.sin θ))/(2*Real.pi)

theorem angular_derivative (ρ : ℝ) : HasDerivAt angular (angularSlope ρ) ρ := by
  have hd := KFCausalCompactAngularDerivative.integral_hasDerivAt
    (fun t θ => marginal (t*Real.sin θ))
    (fun t θ => Real.sin θ*marginalSlope (t*Real.sin θ))
    (by unfold Function.uncurry marginal quartic; fun_prop)
    (by unfold Function.uncurry marginalSlope exponentSlope quartic quarticSlope; fun_prop)
    (fun t θ => by
      convert (marginal_derivative (t*Real.sin θ)).comp t ((hasDerivAt_id t).mul_const (Real.sin θ)) using 1
      dsimp
      ring) ρ
  exact hd.div_const _

theorem angularSlope_derivative (ρ : ℝ) : HasDerivAt angularSlope (angularSecond ρ) ρ := by
  have hd := KFCausalCompactAngularDerivative.integral_hasDerivAt
    (fun t θ => Real.sin θ*marginalSlope (t*Real.sin θ))
    (fun t θ => (Real.sin θ)^2*marginalSecond (t*Real.sin θ))
    (by unfold Function.uncurry marginalSlope exponentSlope quartic quarticSlope; fun_prop)
    (by unfold Function.uncurry marginalSecond exponentSlope quartic quarticSlope quarticSecond; fun_prop)
    (fun t θ => by
      convert ((marginalSlope_derivative (t*Real.sin θ)).comp t
        ((hasDerivAt_id t).mul_const (Real.sin θ))).const_mul (Real.sin θ) using 1
      dsimp
      ring) ρ
  exact hd.div_const _

theorem angular_zero : angular 0 = 555/64 := by
  norm_num [angular,marginal,quartic]
  field_simp
  ring

theorem angularSlope_zero : angularSlope 0 = 0 := by
  simp only [angularSlope,zero_mul,intervalIntegral.integral_mul_const]
  rw [integral_sin]
  simp

theorem angularSecond_zero : angularSecond 0 = -47889/64000 := by
  simp only [angularSecond,zero_mul,marginalSecond_zero,intervalIntegral.integral_mul_const]
  rw [integral_sin_sq]
  simp only [Real.sin_neg,Real.sin_pi,neg_zero,zero_mul,sub_zero,sub_neg_eq_add,zero_add]
  field_simp
  ring

theorem actual_angular_integral (ρ : ℝ) :
    (∫ θ in -Real.pi..Real.pi, ∫ x, slice (ρ*Real.sin θ) x)/(2*Real.pi) =
      Real.exp 8*mass*angular ρ := by
  simp_rw [KFCausalNeutralRadialCoherentKernel.slice_integral]
  rw [intervalIntegral.integral_const_mul]
  unfold angular
  ring

theorem angular_not_monotone : ¬ MonotoneOn angular (Ici 0) := by
  intro hm
  have hp (x : ℝ) (hx : 0 < x) : 0 ≤ angularSlope x := by
    rw [← (angular_derivative x).deriv,← derivWithin_of_mem_nhds (Ici_mem_nhds hx)]
    exact hm.derivWithin_nonneg
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp (angularSlope_derivative 0)).2
  have hnonneg : 0 ≤ angularSecond 0 := by
    apply ge_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Ioi] at hx
    simpa only [slope_def_field,angularSlope_zero,sub_zero] using div_nonneg (hp x hx) hx.le
  rw [angularSecond_zero] at hnonneg
  norm_num at hnonneg

#print axioms quartic_derivative
#print axioms quarticSlope_derivative
#print axioms marginal_derivative
#print axioms marginalSlope_derivative
#print axioms marginalSecond_zero
#print axioms angular_derivative
#print axioms angularSlope_derivative
#print axioms angular_zero
#print axioms angularSlope_zero
#print axioms angularSecond_zero
#print axioms actual_angular_integral
#print axioms angular_not_monotone
end
end UnifiedTheory.Audit.KFCausalNeutralRadialCurvature
