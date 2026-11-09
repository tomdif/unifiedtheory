/- The actual conformal parameter volume as a normalized positive average.
The radial Jacobian factor is an explicit polynomial average, not a supplied
curvature coefficient or an assumed inverse map. -/
import UnifiedTheory.Audit.KFCausalConformal4DRegularVolumeSmoothness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DNormalizedVolume
noncomputable section
open Real MeasureTheory
open KFCausalConformal4DBoostedMoments KFCausalConformal4DTemporalVariation
open KFCausalConformal4DRegularVolume

def average (t r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (3/(2*π))*coordinateIntegral 1 (t/2) (t/2) (r/2) f

def normalizedMoment (n : ℕ) (t r : ℝ) : ℝ := average t r (fun x => x^n)

def normalized (c t r : ℝ) : ℝ := average t r (density c)

def jacobianFactor (c t r : ℝ) : ℝ :=
  average t r (fun x => (1+c*x^2)^3*(1+3*c*x^2))

theorem average_mass (t r : ℝ) : average t r (fun _ => 1)=1 := by
  unfold average
  rw [coordinate_mass]
  field_simp [pi_ne_zero]

theorem average_const (t r a : ℝ) : average t r (fun _ => a)=a := by
  have he : (fun _ : ℝ => a) = fun _ => a*(1:ℝ) := by funext; ring
  rw [he]
  unfold average
  rw [coordinate_smul,coordinate_mass]
  field_simp [pi_ne_zero]

theorem average_add (t r : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    average t r (fun x => f x+g x)=average t r f+average t r g := by
  unfold average
  rw [coordinate_add _ _ _ _ hf hg]
  ring

theorem average_smul (t r a : ℝ) (f : ℝ → ℝ) :
    average t r (fun x => a*f x)=a*average t r f := by
  unfold average
  rw [coordinate_smul]
  ring

theorem average_origin (f : ℝ → ℝ) : average 0 0 f=f 0 := by
  have hp (u v mu : ℝ) : pair 1 (0/2) (0/2) (0/2) f u v mu =
      pair 1 (0/2) (0/2) (0/2) (fun _ => f 0) u v mu := by
    simp [pair,time]
  have he : average 0 0 f=average 0 0 (fun _ => f 0) := by
    unfold average coordinateIntegral
    simp_rw [hp]
  rw [he,average_const]

theorem average_scaling (l t r : ℝ) (f : ℝ → ℝ) :
    average (l*t) (l*r) f=average t r (fun x => f (l*x)) := by
  have hp (u v mu : ℝ) :
      pair 1 (l*t/2) (l*t/2) (l*r/2) f u v mu =
        pair 1 (t/2) (t/2) (r/2) (fun x => f (l*x)) u v mu := by
    unfold pair time
    congr 2 <;> congr 1 <;> ring
  unfold average coordinateIntegral
  simp_rw [hp]

theorem normalized_moment_zero (t r : ℝ) : normalizedMoment 0 t r=1 := by
  simpa only [normalizedMoment,pow_zero] using average_mass t r

theorem normalized_moment_two (t r : ℝ) :
    normalizedMoment 2 t r=(3/10)*t^2-(t^2-r^2)/30 := by
  unfold normalizedMoment average
  rw [coordinate_second]
  field_simp [pi_ne_zero]
  ring

theorem normalized_polynomial (c t r : ℝ) :
    normalized c t r=1+(4*c)*normalizedMoment 2 t r+
      (6*c^2)*normalizedMoment 4 t r+(4*c^3)*normalizedMoment 6 t r+
      c^4*normalizedMoment 8 t r := by
  change (3/(2*π))*coordinateVolume c 1 (t/2) (t/2) (r/2)=_
  rw [coordinate_volume_polynomial]
  have h0 : (3/(2*π))*moment 0 1 (t/2) (t/2) (r/2)=1 :=
    normalized_moment_zero t r
  change _=1+(4*c)*((3/(2*π))*moment 2 1 (t/2) (t/2) (r/2))+
    (6*c^2)*((3/(2*π))*moment 4 1 (t/2) (t/2) (r/2))+
    (4*c^3)*((3/(2*π))*moment 6 1 (t/2) (t/2) (r/2))+
    c^4*((3/(2*π))*moment 8 1 (t/2) (t/2) (r/2))
  linear_combination h0

theorem jacobian_factor_polynomial (c t r : ℝ) :
    jacobianFactor c t r=1+(6*c)*normalizedMoment 2 t r+
      (12*c^2)*normalizedMoment 4 t r+(10*c^3)*normalizedMoment 6 t r+
      (3*c^4)*normalizedMoment 8 t r := by
  have he : (fun x : ℝ => (1+c*x^2)^3*(1+3*c*x^2))=
      (fun x => (1:ℝ)+(6*c)*x^2+(12*c^2)*x^4+(10*c^3)*x^6+(3*c^4)*x^8) := by
    funext x
    ring
  unfold jacobianFactor
  rw [he]
  simp (disch := fun_prop) only [average_add,average_smul,average_mass,normalizedMoment]

theorem normalized_zero (t r : ℝ) : normalized 0 t r=1 := by
  simp only [normalized_polynomial,zero_mul,mul_zero,zero_pow (by decide : 2≠0),
    zero_pow (by decide : 3≠0),zero_pow (by decide : 4≠0),add_zero]

theorem normalized_origin (c : ℝ) : normalized c 0 0=1 := by
  rw [normalized,average_origin,density_polynomial]
  ring

theorem jacobian_factor_origin (c : ℝ) : jacobianFactor c 0 0=1 := by
  rw [jacobianFactor,average_origin]
  ring

theorem normalized_scaling (c l t r : ℝ) :
    normalized c (l*t) (l*r)=normalized (c*l^2) t r := by
  unfold normalized
  rw [average_scaling]
  congr 1
  funext x
  simp only [density_polynomial]
  ring

theorem regular_volume_normalized (c t r : ℝ) :
    regularVolume c t r=(π*(t^2-r^2)^2/24)*normalized c t r := by
  change ((t^2-r^2)^2/16)*coordinateVolume c 1 (t/2) (t/2) (r/2)=
    (π*(t^2-r^2)^2/24)*((3/(2*π))*coordinateVolume c 1 (t/2) (t/2) (r/2))
  field_simp [pi_ne_zero]
  ring

def parameterSlope (c t r : ℝ) : ℝ :=
  4*normalizedMoment 2 t r+(12*c)*normalizedMoment 4 t r+
    (12*c^2)*normalizedMoment 6 t r+(4*c^3)*normalizedMoment 8 t r

theorem normalized_hasDerivAt (c t r : ℝ) :
    HasDerivAt (fun d => normalized d t r) (parameterSlope c t r) c := by
  simp_rw [normalized_polynomial]
  have hd := ((((hasDerivAt_const c (1:ℝ)).add
    ((hasDerivAt_id c).const_mul (4*normalizedMoment 2 t r))).add
    ((hasDerivAt_pow 2 c).const_mul (6*normalizedMoment 4 t r))).add
    ((hasDerivAt_pow 3 c).const_mul (4*normalizedMoment 6 t r))).add
    ((hasDerivAt_pow 4 c).const_mul (normalizedMoment 8 t r))
  convert hd using 1
  · funext d
    simp only [Pi.add_apply,id_eq]
    ring
  · dsimp [parameterSlope]
    ring

theorem jacobian_factor_parameter (c t r : ℝ) :
    jacobianFactor c t r=normalized c t r+(c/2)*parameterSlope c t r := by
  rw [jacobian_factor_polynomial,normalized_polynomial]
  dsimp [parameterSlope]
  ring

theorem normalized_radial_derivative (c t r : ℝ) :
    HasDerivAt (fun l => normalized c (l*t) (l*r))
      (2*c*parameterSlope c t r) 1 := by
  simp_rw [normalized_scaling]
  have hd := (normalized_hasDerivAt (c*1^2) t r).comp 1
    ((hasDerivAt_pow 2 (1:ℝ)).const_mul c)
  simpa only [one_pow,mul_one,mul_comm,mul_left_comm] using hd

#print axioms average_mass
#print axioms average_const
#print axioms average_add
#print axioms average_smul
#print axioms average_origin
#print axioms average_scaling
#print axioms normalized_moment_zero
#print axioms normalized_moment_two
#print axioms normalized_polynomial
#print axioms jacobian_factor_polynomial
#print axioms normalized_zero
#print axioms normalized_origin
#print axioms jacobian_factor_origin
#print axioms normalized_scaling
#print axioms regular_volume_normalized
#print axioms normalized_hasDerivAt
#print axioms jacobian_factor_parameter
#print axioms normalized_radial_derivative
end
end UnifiedTheory.Audit.KFCausalConformal4DNormalizedVolume
