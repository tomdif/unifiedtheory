/- The actual positive fourth-root scaling and its radial derivative.
Strict increase follows from the proved positive parameter-integral factor;
no inverse map or change-of-variables identity is assumed. -/
import UnifiedTheory.Audit.KFCausalConformal4DVolumePositivity
import UnifiedTheory.Audit.KFCausalConformal4DVolumeHomogeneity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DRadialScale
noncomputable section
open Real Set
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DVolumePositivity
open KFCausalConformal4DVolumeHomogeneity

def scale (c t r : ℝ) : ℝ := sqrt (sqrt (normalized c t r))

def radialRadius (c t r l : ℝ) : ℝ := l*scale c (l*t) (l*r)

theorem scale_pos (c t r : ℝ) (hp : 0 < normalized c t r) : 0 < scale c t r :=
  sqrt_pos.mpr (sqrt_pos.mpr hp)

theorem scale_sq (c t r : ℝ) : (scale c t r)^2=sqrt (normalized c t r) :=
  sq_sqrt (sqrt_nonneg _)

theorem scale_fourth (c t r : ℝ) (hp : 0 ≤ normalized c t r) :
    (scale c t r)^4=normalized c t r := by
  calc _ = ((scale c t r)^2)^2 := by ring
       _ = _ := by rw [scale_sq,sq_sqrt hp]

private theorem fourth_root_pow (x : ℝ) (hx : 0 ≤ x) : sqrt (sqrt (x^4))=x := by
  rw [show x^4=(x^2)^2 by ring,sqrt_sq (sq_nonneg x),sqrt_sq hx]

theorem scale_bounds (c t r : ℝ) (hc : |c| ≤ 1/54) (ht : |t| ≤ 3) (hr : |r| ≤ 3) :
    (5/6:ℝ) ≤ scale c t r ∧ scale c t r ≤ 7/6 := by
  obtain ⟨hl,hu⟩ := normalized_bounds c t r hc ht hr
  have hl' := sqrt_le_sqrt (sqrt_le_sqrt hl)
  have hu' := sqrt_le_sqrt (sqrt_le_sqrt hu)
  rw [fourth_root_pow (5/6) (by norm_num)] at hl'
  rw [fourth_root_pow (7/6) (by norm_num)] at hu'
  exact ⟨hl',hu'⟩

theorem scale_origin (c : ℝ) : scale c 0 0=1 := by
  simp only [scale,normalized_origin,sqrt_one]

theorem ray_hasDerivAt (c t r l : ℝ) (hp : 0 < normalized c (l*t) (l*r)) :
    HasDerivAt (radialRadius c t r)
      (jacobianFactor c (l*t) (l*r)/(scale c (l*t) (l*r))^3) l := by
  have hpn : normalized c (l*t) (l*r) ≠ 0 := ne_of_gt hp
  have hsn : sqrt (normalized c (l*t) (l*r)) ≠ 0 := ne_of_gt (sqrt_pos.mpr hp)
  have hn : scale c (l*t) (l*r) ≠ 0 := ne_of_gt (scale_pos c (l*t) (l*r) hp)
  have hd := (hasDerivAt_id l).mul
    (((normalized_ray_hasDerivAt c l t r).sqrt hpn).sqrt hsn)
  have hv : scale c (l*t) (l*r)+l*
      ((2*c*l*parameterSlope (c*l^2) t r)/(2*sqrt (normalized c (l*t) (l*r)))/
        (2*scale c (l*t) (l*r))) =
      jacobianFactor c (l*t) (l*r)/(scale c (l*t) (l*r))^3 := by
    rw [jacobian_factor_parameter,parameter_slope_scaling,← scale_sq]
    calc _ = ((scale c (l*t) (l*r))^4+(c/2)*(l^2*parameterSlope (c*l^2) t r))/
          (scale c (l*t) (l*r))^3 := by field_simp
         _ = _ := by rw [scale_fourth c (l*t) (l*r) hp.le]
  have hd' : HasDerivAt (radialRadius c t r)
      (scale c (l*t) (l*r)+l*
        ((2*c*l*parameterSlope (c*l^2) t r)/(2*sqrt (normalized c (l*t) (l*r)))/
          (2*scale c (l*t) (l*r)))) l := by
    simpa only [radialRadius,scale,one_mul,id_eq] using hd
  rw [hv] at hd'
  exact hd'

private theorem segment_bound (l x : ℝ) (hl : l ∈ Icc (0:ℝ) 1) (hx : |x| ≤ 3) :
    |l*x| ≤ 3 := by
  rw [abs_mul,abs_of_nonneg hl.1]
  calc l*|x| ≤ 1*|x| := mul_le_mul_of_nonneg_right hl.2 (abs_nonneg _)
       _ ≤ 3 := by simpa only [one_mul] using hx

theorem ray_strictMono (c t r : ℝ) (hc : |c| ≤ 1/54) (ht : |t| ≤ 3) (hr : |r| ≤ 3) :
    StrictMonoOn (radialRadius c t r) (Icc (0:ℝ) 1) := by
  have hp (l : ℝ) (hl : l ∈ Icc (0:ℝ) 1) : 0 < normalized c (l*t) (l*r) :=
    normalized_pos c (l*t) (l*r) hc (segment_bound l t hl ht) (segment_bound l r hl hr)
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro l hl
    exact (ray_hasDerivAt c t r l (hp l hl)).continuousAt.continuousWithinAt
  · intro l hl
    have hl' : l ∈ Icc (0:ℝ) 1 := interior_subset hl
    rw [(ray_hasDerivAt c t r l (hp l hl')).deriv]
    exact div_pos (jacobian_factor_pos c (l*t) (l*r) hc
      (segment_bound l t hl' ht) (segment_bound l r hl' hr))
      (pow_pos (scale_pos c (l*t) (l*r) (hp l hl')) _)

#print axioms scale_pos
#print axioms scale_sq
#print axioms scale_fourth
#print axioms scale_bounds
#print axioms scale_origin
#print axioms ray_hasDerivAt
#print axioms ray_strictMono
end
end UnifiedTheory.Audit.KFCausalConformal4DRadialScale
