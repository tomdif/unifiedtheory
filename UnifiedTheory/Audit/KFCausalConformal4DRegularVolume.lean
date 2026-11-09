/- The apparent light-cone denominators in the boosted parameter integral
are removable. A fixed-box formula extends the same timelike volume and its
first variation to all endpoint coordinates. This does not identify that
parameter integral with a curved chronological-diamond measure. -/
import UnifiedTheory.Audit.KFCausalConformal4DTemporalVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DRegularVolume
noncomputable section
open Real
open KFCausalConformal4DBoostedMoments
open KFCausalConformal4DTemporalVariation

theorem coordinate_volume_scaling (c T m A B : ℝ) :
    coordinateVolume c T m A B=T^4*coordinateVolume c 1 m (A*T) (B*T) := by
  have ht (u v mu : ℝ) : pair T m A B (density c) u v mu =
      pair 1 m (A*T) (B*T) (density c) u v mu := by
    unfold pair time
    congr 2 <;> congr 1 <;> ring
  unfold coordinateVolume coordinateIntegral
  simp_rw [ht]
  ring

def regularVolume (c t r : ℝ) : ℝ :=
  ((t^2-r^2)^2/16)*coordinateVolume c 1 (t/2) (t/2) (r/2)

theorem timelike_eq_regular (c t r : ℝ) (hq : 0<t^2-r^2) :
    timelikeVolume c t r=regularVolume c t r := by
  have hs : sqrt (t^2-r^2) ≠ 0 := ne_of_gt (sqrt_pos.mpr hq)
  have ht : (t/sqrt (t^2-r^2))*(sqrt (t^2-r^2)/2)=t/2 := by field_simp
  have hr : (r/sqrt (t^2-r^2))*(sqrt (t^2-r^2)/2)=r/2 := by field_simp
  have hp : (sqrt (t^2-r^2)/2)^4=(t^2-r^2)^2/16 := by
    calc _ = (sqrt (t^2-r^2)^2)^2/16 := by ring
      _ = _ := by rw [sq_sqrt hq.le]
  unfold timelikeVolume regularVolume
  rw [coordinate_volume_scaling,ht,hr,hp]

theorem regular_volume_zero (t r : ℝ) : regularVolume 0 t r=π*(t^2-r^2)^2/24 := by
  unfold regularVolume
  rw [coordinate_volume_zero]
  ring

theorem regular_volume_derivative (t r : ℝ) :
    HasDerivAt (fun c => regularVolume c t r)
      ((π*(t^2-r^2)^2/24)*(6/5*t^2-2/15*(t^2-r^2))) 0 := by
  have h := (coordinate_volume_derivative 1 (t/2) (t/2) (r/2)).const_mul ((t^2-r^2)^2/16)
  convert h using 1
  unfold moment
  rw [coordinate_second]
  ring

theorem regular_volume_null (c t r : ℝ) (hq : t^2-r^2=0) : regularVolume c t r=0 := by
  simp only [regularVolume,hq,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul]

#print axioms coordinate_volume_scaling
#print axioms timelike_eq_regular
#print axioms regular_volume_zero
#print axioms regular_volume_derivative
#print axioms regular_volume_null
end
end UnifiedTheory.Audit.KFCausalConformal4DRegularVolume
