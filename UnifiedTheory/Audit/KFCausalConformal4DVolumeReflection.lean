/- Radial reflection of the actual compact coordinate integral. The symmetry
comes from reversing its angular coordinate, without an integrability or
symmetry supplier. It passes to the normalized volume and Jacobian factor. -/
import UnifiedTheory.Audit.KFCausalConformal4DRadialScale

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DVolumeReflection
noncomputable section
open Real MeasureTheory
open KFCausalConformal4DBoostedMoments KFCausalConformal4DNormalizedVolume
open KFCausalConformal4DRegularVolume KFCausalConformal4DRadialScale

theorem coordinate_rneg (T m A B : ℝ) (f : ℝ → ℝ) :
    coordinateIntegral T m A (-B) f=coordinateIntegral T m A B f := by
  have hp (u v mu : ℝ) : pair T m A (-B) f u v mu=pair T m A B f u v (-mu) := by
    unfold pair time
    congr 2 <;> congr 1 <;> ring
  have hi (u v : ℝ) : (∫ mu in (-1:ℝ)..1, pair T m A B f u v (-mu)) =
      ∫ mu in (-1:ℝ)..1, pair T m A B f u v mu := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := fun mu => pair T m A B f u v mu)
        (a := (-1:ℝ)) (b := 1))
  unfold coordinateIntegral
  simp_rw [hp,hi]

theorem average_rneg (t r : ℝ) (f : ℝ → ℝ) : average t (-r) f=average t r f := by
  unfold KFCausalConformal4DNormalizedVolume.average
  rw [neg_div,coordinate_rneg]

theorem moment_rneg (n : ℕ) (t r : ℝ) :
    normalizedMoment n t (-r)=normalizedMoment n t r :=
  average_rneg t r _

theorem normalized_rneg (c t r : ℝ) : normalized c t (-r)=normalized c t r :=
  average_rneg t r _

theorem jacobian_rneg (c t r : ℝ) : jacobianFactor c t (-r)=jacobianFactor c t r :=
  average_rneg t r _

theorem parameter_slope_rneg (c t r : ℝ) : parameterSlope c t (-r)=parameterSlope c t r := by
  unfold parameterSlope
  simp only [moment_rneg]

theorem regular_volume_rneg (c t r : ℝ) : regularVolume c t (-r)=regularVolume c t r := by
  rw [regular_volume_normalized,regular_volume_normalized,neg_sq,normalized_rneg]

theorem scale_rneg (c t r : ℝ) : scale c t (-r)=scale c t r := by
  unfold scale
  rw [normalized_rneg]

theorem radial_radius_rneg (c t r l : ℝ) : radialRadius c t (-r) l=radialRadius c t r l := by
  unfold radialRadius
  rw [mul_neg,scale_rneg]

#print axioms coordinate_rneg
#print axioms average_rneg
#print axioms moment_rneg
#print axioms normalized_rneg
#print axioms jacobian_rneg
#print axioms parameter_slope_rneg
#print axioms regular_volume_rneg
#print axioms scale_rneg
#print axioms radial_radius_rneg
end
end UnifiedTheory.Audit.KFCausalConformal4DVolumeReflection
