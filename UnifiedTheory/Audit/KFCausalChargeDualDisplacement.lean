/- Every modulation in the full five-transverse-plus-clock dual space is
the actual dual image of an explicit clock-preserving physical displacement
and clock phase. This is an identity on the entire Hilbert space; no Gaussian,
charge-sector, or operator-domain assumption is used. -/
import UnifiedTheory.Audit.KFCausalChargeDualMomentum
import UnifiedTheory.Audit.KFCausalClockFloorDualClock
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargeDualDisplacement
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalChargeTransverseSplit
open KFCausalChargeDualMomentum (transverseBlock dualMixed_translation_coe)
open KFCausalFourierTranslation
open KFCausalNormalizedChargeFlow
open KFCausalChargeDisplacementCovariance (displacement)
open KFCausalClockChargeMultiplier (jointMultiplier jointMultiplier_coe)
open KFCausalClockFloorDualClock (dualJointMultiplier dualJointMultiplier_coe dualMixed_multiplier)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorDisplacedStates (operator operator_coordinates)
open KFCausalConfigurationTestSpace (Hilbert)

def transverseShift (k : Joint 5 1) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl i => ![k (.inl 0),k (.inl 1)] i
  | .inr i => ![0,k (.inl 2),k (.inl 3),k (.inl 4)] i

def displacementParameter (h : ℝ) (k : Joint 5 1) : Joint 2 4 :=
  dilate (momentumScale h) (transverseShift k)

def clockParameter (k : Joint 5 1) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![k (.inr 0),0,0,0] i

def clockPhase (k : Joint 5 1) (s : ℝ) : ℂ := phase (k (.inr 0)) s

theorem transverseShift_clock (k : Joint 5 1) : transverseShift k (.inr 0) = 0 := rfl

theorem transverseBlock_shift (k : Joint 5 1) :
    transverseBlock (transverseShift k) = (split 5 1 k).1 := by
  ext i
  fin_cases i <;> rfl

theorem displacementParameter_clock (h : ℝ) (k : Joint 5 1) :
    displacementParameter h k (.inr 0) = 0 := rfl

theorem undo_displacementParameter (h : ℝ) (hh : h ≠ 0) (k : Joint 5 1) :
    dilate (momentumScale h)⁻¹ (displacementParameter h k) = transverseShift k := by
  rw [displacementParameter,dilate_compose,inv_mul_cancel₀ (momentumScale_ne_zero h hh),dilate_one]

theorem dilate_clockParameter (c : ℝ) (k : Joint 5 1) :
    dilate c (clockParameter k) = clockParameter k := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [dilate,clockParameter]

theorem phase_clock (k : Joint 5 1) (x : Joint 2 4) :
    phase (clockParameter k) x = clockPhase k (x (.inr 0)) := by
  simp [phase,clockParameter,clockPhase,PiLp.inner_apply,
    Fintype.sum_sum_type,Fin.sum_univ_succ,RCLike.inner_apply]

theorem phase_factor (k x : Joint 5 1) :
    clockPhase k (x (.inr 0))*phase (split 5 1 k).1 (split 5 1 x).1 = phase k x := by
  unfold clockPhase phase
  rw [inner_split]
  simp only [PiLp.inner_apply,Fin.sum_univ_one,split_snd,RCLike.inner_apply,
    conj_trivial,AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

private theorem clockPhase_measurable (k : Joint 5 1) : Measurable (clockPhase k) :=
  (phase_continuous (k (.inr 0))).measurable

private theorem clockPhase_bound (k : Joint 5 1) (s : ℝ) : ‖clockPhase k s‖ ≤ 1 :=
  (phase_norm _ _).le

private theorem phaseAction_clock (k : Joint 5 1) (f : JointHilbert 2 4) :
    phaseAction (clockParameter k) f =
      jointMultiplier (clockPhase k) (clockPhase_measurable k) (clockPhase_bound k) f := by
  apply Lp.ext
  filter_upwards [phaseAction_coe (clockParameter k) f,
    jointMultiplier_coe (clockPhase k) (clockPhase_measurable k) (clockPhase_bound k) f]
    with x hp hj
  rw [hp,hj,phase_clock]

theorem dualPhysical_operator (h : ℝ) (hh : h ≠ 0) (k : Joint 5 1) (f : Hilbert) :
    dualPhysical (operator h (displacementParameter h k) (clockParameter k) f) =
      phaseAction k (dualPhysical f) := by
  change dualMixed (chargeCoordinates (operator h (displacementParameter h k) (clockParameter k) f)) = _
  rw [operator_coordinates]
  change dualMixed (phaseAction (dilate (momentumScale h) (clockParameter k))
    (translation (dilate (momentumScale h)⁻¹ (displacementParameter h k)) (chargeCoordinates f))) = _
  rw [undo_displacementParameter h hh,dilate_clockParameter,phaseAction_clock,dualMixed_multiplier]
  apply Lp.ext
  filter_upwards [dualJointMultiplier_coe (clockPhase k) (clockPhase_measurable k) (clockPhase_bound k)
      (dualMixed (translation (transverseShift k) (chargeCoordinates f))),
    dualMixed_translation_coe (transverseShift k) (transverseShift_clock k) (chargeCoordinates f),
    phaseAction_coe k (dualPhysical f)] with x hm ht hp
  rw [hm,ht,hp,transverseBlock_shift,← mul_assoc,phase_factor]
  rfl

#print axioms transverseShift_clock
#print axioms transverseBlock_shift
#print axioms displacementParameter_clock
#print axioms undo_displacementParameter
#print axioms dilate_clockParameter
#print axioms phase_clock
#print axioms phase_factor
#print axioms dualPhysical_operator
end
end UnifiedTheory.Audit.KFCausalChargeDualDisplacement
