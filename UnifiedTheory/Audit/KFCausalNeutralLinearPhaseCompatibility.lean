/- Classify transverse linear coordinates fixed by longitudinal flow.
The only family is x4-2*(x2+x3). Its mixed-coordinate representative is
not fixed by charge rotation unless it is zero. This limits a commuting
phase construction; it is not a theorem excluding other form lifts. -/
import UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates
import UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
import UnifiedTheory.Audit.KFCausalPairedModeCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralLinearPhaseCompatibility
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow scale)
open UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates (coordinate)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (flowEquiv)

def linearValue (a x : Transverse) : ℝ := ∑ i, a i*x i

theorem flow_difference (a x : Transverse) (t : ℝ) :
    linearValue a (flow t x)-linearValue a x =
      (scale t-1)*(a 0*x 0+a 1*x 1+(a 2+2*a 4)*x 2+(a 3+2*a 4)*x 3) := by
  simp [linearValue,Fin.sum_univ_succ,flow]
  ring

theorem scale_double : scale (2*Real.log 2) = 2 := by
  simp [scale,Real.exp_log (by norm_num : (0:ℝ) < 2)]

theorem flow_invariant_iff (a : Transverse) :
    (∀ t x, linearValue a (flow t x) = linearValue a x) ↔
      a = ![0,0,-2*a 4,-2*a 4,a 4] := by
  constructor
  · intro h
    have hz (x : Transverse) :
        a 0*x 0+a 1*x 1+(a 2+2*a 4)*x 2+(a 3+2*a 4)*x 3 = 0 := by
      have he := flow_difference a x (2*Real.log 2)
      rw [h,sub_self,scale_double] at he
      linarith
    have h0 := hz (Pi.single 0 1)
    have h1 := hz (Pi.single 1 1)
    have h2 := hz (Pi.single 2 1)
    have h3 := hz (Pi.single 3 1)
    simp at h0 h1 h2 h3
    funext i
    fin_cases i <;> simp <;> linarith
  · intro ha t x
    have he := flow_difference a x t
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    have h3 := congrFun ha 3
    simp at h0 h1 h2 h3
    rw [h0,h1,h2,h3] at he
    nlinarith

theorem invariant_is_adapted (a : Transverse)
    (ha : ∀ t x, linearValue a (flow t x) = linearValue a x) (x : Transverse) :
    linearValue a x = a 4*coordinate (0,x) := by
  have he := (flow_invariant_iff a).mp ha
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  simp at h0 h1 h2 h3
  simp [linearValue,Fin.sum_univ_succ,h0,h1,h2,h3,
    KFCausalAdaptedNeutralModulationCoordinates.coordinate_apply]
  ring

theorem bare_neutral_changes : flow (2*Real.log 2) (Pi.single 2 1) 4 = 2 := by
  simp [flow,scale_double]
  norm_num

def mixedValue (b : ℝ) (x : Joint 2 4) : ℝ :=
  b*(x (.inr 3)-4*KFCausalPairedModeCoordinates.scale*x (.inr 2))

theorem mixed_representation (b : ℝ) (x : KFCausalEuclideanConfiguration.Space) :
    mixedValue b (KFCausalPairedModeCoordinates.modeIsometry x) =
      b*coordinate (KFCausalEuclideanConfiguration.split x) := by
  change b*(x 5-4*KFCausalPairedModeCoordinates.scale*
    (KFCausalPairedModeCoordinates.scale*(x 3+x 4))) = b*(x 5-2*(x 3+x 4))
  have hs : 4*KFCausalPairedModeCoordinates.scale*KFCausalPairedModeCoordinates.scale = 2 := by
    nlinarith [KFCausalPairedModeCoordinates.scale_square]
  calc
    _ = b*(x 5-(4*KFCausalPairedModeCoordinates.scale*KFCausalPairedModeCoordinates.scale)*(x 3+x 4)) := by ring
    _ = _ := by rw [hs]

theorem charge_half_turn_difference (c : ℝ) (hc : c ≠ 0) (b : ℝ) (x : Joint 2 4) :
    mixedValue b (flowEquiv c hc Real.pi x)-mixedValue b x =
      8*b*KFCausalPairedModeCoordinates.scale*x (.inr 2) := by
  simp [mixedValue,KFCausalNormalizedChargeFlow.flow_apply,KFCausalNormalizedChargeFlow.dilate,
    KFCausalPairedRotation.rotate]
  ring

theorem charge_invariant_iff (c : ℝ) (hc : c ≠ 0) (b : ℝ) :
    (∀ θ x, mixedValue b (flowEquiv c hc θ x) = mixedValue b x) ↔ b = 0 := by
  constructor
  · intro h
    have he := charge_half_turn_difference c hc b (WithLp.toLp 2 (Pi.single (.inr 2) 1))
    rw [h,sub_self] at he
    have hs : KFCausalPairedModeCoordinates.scale ≠ 0 := by
      unfold KFCausalPairedModeCoordinates.scale
      exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hb : 8*b*KFCausalPairedModeCoordinates.scale = 0 := by simpa using he.symm
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hs)).resolve_left (by norm_num)
  · rintro rfl θ x
    simp [mixedValue]

#print axioms flow_difference
#print axioms scale_double
#print axioms flow_invariant_iff
#print axioms invariant_is_adapted
#print axioms bare_neutral_changes
#print axioms mixed_representation
#print axioms charge_half_turn_difference
#print axioms charge_invariant_iff

end
end UnifiedTheory.Audit.KFCausalNeutralLinearPhaseCompatibility
