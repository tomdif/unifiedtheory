import UnifiedTheory.Audit.KFCausalConformal4DNormalizedVolume
import UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactPartials

/- The actual compact coordinate moments are finite homogeneous polynomials.
Joint smoothness follows from that exact integral identity, without an
assumed differentiation-under-integral certificate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalConformal4DVolumeSmoothPolynomial
noncomputable section
open Real MeasureTheory
open scoped BigOperators ContDiff
open KFCausalConformal4DBoostedMoments KFCausalConformal4DNormalizedVolume

def coefficientIntegrand (n k : ℕ) (u v mu : ℝ) : ℝ :=
  (1-u)^3*v^2*(n.choose k : ℝ)*
    (((1+u)/2)^k+((1-u)/2)^k)*((1-u)*v*mu/2)^(n-k)

def coefficient (n k : ℕ) : ℝ :=
  3*∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1,
    coefficientIntegrand n k u v mu

private theorem coefficient_continuous (n k : ℕ) :
    Continuous (fun p : (ℝ×ℝ)×ℝ => coefficientIntegrand n k p.1.1 p.1.2 p.2) := by
  unfold coefficientIntegrand
  fun_prop

private theorem inner_continuous (n k : ℕ) :
    Continuous (fun p : ℝ×ℝ => ∫ mu in (-1:ℝ)..1,
      coefficientIntegrand n k p.1 p.2 mu) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (coefficient_continuous n k) (-1) 1

private theorem outer_continuous (n k : ℕ) :
    Continuous (fun u : ℝ => ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1,
      coefficientIntegrand n k u v mu) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (inner_continuous n k) 0 1

theorem moment_integrand_expansion (n : ℕ) (t r u v mu : ℝ) :
    pair 1 (t/2) (t/2) (r/2) (fun x => x^n) u v mu =
      ∑ k ∈ Finset.range (n+1), t^k*r^(n-k)*coefficientIntegrand n k u v mu := by
  have hp : time 1 (t/2) (t/2) (r/2) u v mu =
      t*((1+u)/2)+r*((1-u)*v*mu/2) := by unfold time; ring
  have hm : time 1 (t/2) (-(t/2)) (r/2) u v mu =
      t*((1-u)/2)+r*((1-u)*v*mu/2) := by unfold time; ring
  unfold pair
  simp only [hp,hm]
  rw [add_pow,add_pow]
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_pow,coefficientIntegrand]
  ring

theorem moment_polynomial (n : ℕ) (t r : ℝ) :
    normalizedMoment n t r =
      ∑ k ∈ Finset.range (n+1), coefficient n k*t^k*r^(n-k) := by
  have hi (u v : ℝ) :
      (∫ mu in (-1:ℝ)..1, ∑ k ∈ Finset.range (n+1),
        t^k*r^(n-k)*coefficientIntegrand n k u v mu) =
      ∑ k ∈ Finset.range (n+1), t^k*r^(n-k)*
        ∫ mu in (-1:ℝ)..1, coefficientIntegrand n k u v mu := by
    rw [intervalIntegral.integral_finset_sum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro k hk
      apply Continuous.intervalIntegrable
      unfold coefficientIntegrand
      fun_prop
  have hm (u : ℝ) :
      (∫ v in (0:ℝ)..1, ∑ k ∈ Finset.range (n+1), t^k*r^(n-k)*
        ∫ mu in (-1:ℝ)..1, coefficientIntegrand n k u v mu) =
      ∑ k ∈ Finset.range (n+1), t^k*r^(n-k)*
        ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1, coefficientIntegrand n k u v mu := by
    rw [intervalIntegral.integral_finset_sum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro k hk
      exact (continuous_const.mul ((inner_continuous n k).comp
        (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  have ho :
      (∫ u in (0:ℝ)..1, ∑ k ∈ Finset.range (n+1), t^k*r^(n-k)*
        ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1, coefficientIntegrand n k u v mu) =
      ∑ k ∈ Finset.range (n+1), t^k*r^(n-k)*
        ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1,
          coefficientIntegrand n k u v mu := by
    rw [intervalIntegral.integral_finset_sum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro k hk
      exact (continuous_const.mul (outer_continuous n k)).intervalIntegrable _ _
  unfold normalizedMoment KFCausalConformal4DNormalizedVolume.average coordinateIntegral
  simp only [moment_integrand_expansion,hi,hm,ho,one_pow,mul_one]
  rw [← mul_assoc]
  have hc : 3/(2*π)*(2*π)=3 := by field_simp [pi_ne_zero]
  rw [hc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold coefficient
  ring

theorem moment_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ×ℝ => normalizedMoment n p.1 p.2) := by
  simp_rw [moment_polynomial]
  fun_prop

theorem normalized_smooth :
    ContDiff ℝ ∞ (fun p : ℝ×(ℝ×ℝ) => normalized p.1 p.2.1 p.2.2) := by
  simp_rw [normalized_polynomial]
  have hm (n : ℕ) : ContDiff ℝ ∞ (fun p : ℝ×(ℝ×ℝ) => normalizedMoment n p.2.1 p.2.2) :=
    (moment_smooth n).comp contDiff_snd
  fun_prop

theorem jacobian_factor_smooth :
    ContDiff ℝ ∞ (fun p : ℝ×(ℝ×ℝ) => jacobianFactor p.1 p.2.1 p.2.2) := by
  simp_rw [jacobian_factor_polynomial]
  have hm (n : ℕ) : ContDiff ℝ ∞ (fun p : ℝ×(ℝ×ℝ) => normalizedMoment n p.2.1 p.2.2) :=
    (moment_smooth n).comp contDiff_snd
  fun_prop

theorem parameter_slope_smooth :
    ContDiff ℝ ∞ (fun p : ℝ×(ℝ×ℝ) => parameterSlope p.1 p.2.1 p.2.2) := by
  unfold parameterSlope
  have hm (n : ℕ) : ContDiff ℝ ∞ (fun p : ℝ×(ℝ×ℝ) => normalizedMoment n p.2.1 p.2.2) :=
    (moment_smooth n).comp contDiff_snd
  fun_prop

private theorem moment_scaling (n : ℕ) (l t r : ℝ) :
    normalizedMoment n (l*t) (l*r)=l^n*normalizedMoment n t r := by
  unfold normalizedMoment
  rw [average_scaling]
  simp_rw [mul_pow]
  exact average_smul t r (l^n) (fun x => x^n)

private theorem even_derivative (A B C D l : ℝ) :
    HasDerivAt (fun s : ℝ => 1+A*s^2+B*s^4+C*s^6+D*s^8)
      (2*A*l+4*B*l^3+6*C*l^5+8*D*l^7) l := by
  have h := ((((hasDerivAt_const l (1:ℝ)).add
    ((hasDerivAt_pow 2 l).const_mul A)).add
    ((hasDerivAt_pow 4 l).const_mul B)).add
    ((hasDerivAt_pow 6 l).const_mul C)).add
    ((hasDerivAt_pow 8 l).const_mul D)
  convert h using 1
  norm_num
  ring

private theorem even_second (A B C D : ℝ) :
    HasDerivAt (deriv (fun s : ℝ => 1+A*s^2+B*s^4+C*s^6+D*s^8)) (2*A) 0 := by
  have he : deriv (fun s : ℝ => 1+A*s^2+B*s^4+C*s^6+D*s^8) =
      fun l => 2*A*l+4*B*l^3+6*C*l^5+8*D*l^7 := by
    funext l
    exact (even_derivative A B C D l).deriv
  rw [he]
  have h := ((((hasDerivAt_id (0:ℝ)).const_mul (2*A)).add
    ((hasDerivAt_pow 3 (0:ℝ)).const_mul (4*B))).add
    ((hasDerivAt_pow 5 (0:ℝ)).const_mul (6*C))).add
    ((hasDerivAt_pow 7 (0:ℝ)).const_mul (8*D))
  simpa only [Nat.cast_ofNat,zero_pow (by decide : 2≠0),
    zero_pow (by decide : 4≠0),zero_pow (by decide : 6≠0),
    mul_zero,mul_one,add_zero] using h

theorem normalized_origin_radial_jets (c t r : ℝ) :
    HasDerivAt (fun l => normalized c (l*t) (l*r)) 0 0 ∧
    HasDerivAt (deriv (fun l => normalized c (l*t) (l*r)))
      (c*((32/15)*t^2+(4/15)*r^2)) 0 := by
  have he : (fun l => normalized c (l*t) (l*r)) =
      fun l => 1+(4*c*normalizedMoment 2 t r)*l^2+
        (6*c^2*normalizedMoment 4 t r)*l^4+
        (4*c^3*normalizedMoment 6 t r)*l^6+
        (c^4*normalizedMoment 8 t r)*l^8 := by
    funext l
    rw [normalized_polynomial]
    simp only [moment_scaling]
    ring
  rw [he]
  constructor
  · simpa only [zero_pow (by decide : 3≠0),zero_pow (by decide : 5≠0),
      zero_pow (by decide : 7≠0),mul_zero,zero_add] using
      even_derivative (4*c*normalizedMoment 2 t r) (6*c^2*normalizedMoment 4 t r)
        (4*c^3*normalizedMoment 6 t r) (c^4*normalizedMoment 8 t r) 0
  · convert even_second (4*c*normalizedMoment 2 t r) (6*c^2*normalizedMoment 4 t r)
        (4*c^3*normalizedMoment 6 t r) (c^4*normalizedMoment 8 t r) using 1
    rw [normalized_moment_two]
    ring

theorem jacobian_factor_origin_radial_jets (c t r : ℝ) :
    HasDerivAt (fun l => jacobianFactor c (l*t) (l*r)) 0 0 ∧
    HasDerivAt (deriv (fun l => jacobianFactor c (l*t) (l*r)))
      (c*((16/5)*t^2+(2/5)*r^2)) 0 := by
  have he : (fun l => jacobianFactor c (l*t) (l*r)) =
      fun l => 1+(6*c*normalizedMoment 2 t r)*l^2+
        (12*c^2*normalizedMoment 4 t r)*l^4+
        (10*c^3*normalizedMoment 6 t r)*l^6+
        (3*c^4*normalizedMoment 8 t r)*l^8 := by
    funext l
    rw [jacobian_factor_polynomial]
    simp only [moment_scaling]
    ring
  rw [he]
  constructor
  · simpa only [zero_pow (by decide : 3≠0),zero_pow (by decide : 5≠0),
      zero_pow (by decide : 7≠0),mul_zero,zero_add] using
      even_derivative (6*c*normalizedMoment 2 t r) (12*c^2*normalizedMoment 4 t r)
        (10*c^3*normalizedMoment 6 t r) (3*c^4*normalizedMoment 8 t r) 0
  · convert even_second (6*c*normalizedMoment 2 t r) (12*c^2*normalizedMoment 4 t r)
        (10*c^3*normalizedMoment 6 t r) (3*c^4*normalizedMoment 8 t r) using 1
    rw [normalized_moment_two]
    ring

theorem normalized_origin_fderiv (c : ℝ) :
    fderiv ℝ (fun p : ℝ×ℝ => normalized c p.1 p.2) (0,0)=0 := by
  have hi : ContDiff ℝ ∞ (fun p : ℝ×ℝ => (c,p)) :=
    contDiff_const.prodMk contDiff_id
  have hs := normalized_smooth.comp hi
  apply ContinuousLinearMap.ext
  intro d
  have hd := (hs.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    (0:ℝ) ((hasDerivAt_id (0:ℝ)).smul_const d)
  have he := hd.unique (normalized_origin_radial_jets c d.1 d.2).1
  simpa only [id_eq,zero_smul,one_smul,ContinuousLinearMap.zero_apply] using he

theorem jacobian_factor_origin_fderiv (c : ℝ) :
    fderiv ℝ (fun p : ℝ×ℝ => jacobianFactor c p.1 p.2) (0,0)=0 := by
  have hi : ContDiff ℝ ∞ (fun p : ℝ×ℝ => (c,p)) :=
    contDiff_const.prodMk contDiff_id
  have hs := jacobian_factor_smooth.comp hi
  apply ContinuousLinearMap.ext
  intro d
  have hd := (hs.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    (0:ℝ) ((hasDerivAt_id (0:ℝ)).smul_const d)
  have he := hd.unique (jacobian_factor_origin_radial_jets c d.1 d.2).1
  simpa only [id_eq,zero_smul,one_smul,ContinuousLinearMap.zero_apply] using he

#print axioms moment_integrand_expansion
#print axioms moment_polynomial
#print axioms moment_smooth
#print axioms normalized_smooth
#print axioms jacobian_factor_smooth
#print axioms parameter_slope_smooth
#print axioms normalized_origin_radial_jets
#print axioms jacobian_factor_origin_radial_jets
#print axioms normalized_origin_fderiv
#print axioms jacobian_factor_origin_fderiv
end
end UnifiedTheory.Audit.KFCausalConformal4DVolumeSmoothPolynomial
