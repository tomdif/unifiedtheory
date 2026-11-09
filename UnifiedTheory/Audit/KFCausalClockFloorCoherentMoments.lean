/- Physical sourced Gaussians and their coordinate moments are in L2.
The estimates follow from the checked complex-source Gaussian absorption,
specialized to real physical positions. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
import UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (source_real_flow)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments

def sourcedPacket (α β : ℝ) (b : Fin 5 → ℂ) (x : Transverse) : ℂ :=
  Complex.exp (linearSource b x)*physicalGaussian α β x

theorem sourcedPacket_continuous (α β : ℝ) (b : Fin 5 → ℂ) :
    Continuous (sourcedPacket α β b) := by
  unfold sourcedPacket linearSource physicalGaussian
  fun_prop

theorem packet_zero_grouping (α β : ℝ) (x : Transverse) :
    packet α β 0 (transverseGrouping x) = physicalGaussian α β x := by
  rw [transverseGrouping_apply]
  have he : (![x 0,x 1,x 2,x 3,x 4]:Transverse) = x := by
    funext i
    fin_cases i <;> rfl
  rw [show (0:ℂ) = ((0:ℝ):ℂ) from rfl,packet_real_flow,flow_initial]
  exact congrArg (physicalGaussian α β) he

theorem coherentPacket_zero_grouping (α β : ℝ) (b : Fin 5 → ℂ) (x : Transverse) :
    coherentPacket α β b 0 (transverseGrouping x) = sourcedPacket α β b x := by
  rw [coherentPacket,packet_zero_grouping]
  have he : (![x 0,x 1,x 2,x 3,x 4]:Transverse) = x := by
    funext i
    fin_cases i <;> rfl
  rw [transverseGrouping_apply,show (0:ℂ) = ((0:ℝ):ℂ) from rfl,source_real_flow,flow_initial]
  change Complex.exp (linearSource b ![x 0,x 1,x 2,x 3,x 4])*physicalGaussian α β x = _
  rw [he]
  rfl

theorem sourcedPacket_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (x : Transverse) :
    ‖sourcedPacket α β b x‖ ≤ Real.exp (sourceConstant α β b/2)*‖physicalGaussian (α/2) (β/2) x‖ := by
  have h := coherentPacket_bound α β hα hβ hw b 0 (by simp; positivity) (transverseGrouping x)
  simpa only [coherentPacket_zero_grouping,packet_zero_grouping] using h

theorem sourcedPacket_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) : MemLp (sourcedPacket α β b) 2 volume := by
  apply ((physicalGaussian_memLp (α/2) (β/2) (by positivity) (by positivity)).const_mul
    (Real.exp (sourceConstant α β b/2):ℂ)).of_le (sourcedPacket_continuous α β b).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    sourcedPacket_bound α β hα hβ hw b x

theorem sourcedPacket_coordinate_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (i : Fin 5) :
    MemLp (fun x : Transverse => (x i:ℂ)*sourcedPacket α β b x) 2 volume := by
  have hc : Continuous (fun x : Transverse => (x i:ℂ)*sourcedPacket α β b x) :=
    (Complex.continuous_ofReal.comp (continuous_apply i)).mul (sourcedPacket_continuous α β b)
  apply ((physicalGaussian_coordinate_memLp (α/2) (β/2) (by positivity) (by positivity) i).const_mul
    (Real.exp (sourceConstant α β b/2):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  have h := mul_le_mul_of_nonneg_left (sourcedPacket_bound α β hα hβ hw b x) (norm_nonneg (x i:ℂ))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_left_comm] using h

#print axioms sourcedPacket_continuous
#print axioms packet_zero_grouping
#print axioms coherentPacket_zero_grouping
#print axioms sourcedPacket_bound
#print axioms sourcedPacket_memLp
#print axioms sourcedPacket_coordinate_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
