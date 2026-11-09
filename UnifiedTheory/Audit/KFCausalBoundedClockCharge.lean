/- Arbitrary bounded clock multipliers commute with physical charge.
The mixed-coordinate representative is derived by normalization to the
previously proved contractive multiplier construction. -/
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
import UnifiedTheory.Audit.KFCausalClockChargeMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalBoundedClockCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action)
open UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
open UnifiedTheory.Audit.KFCausalClockChargeMultiplier

variable (m : ℝ → ℂ) (hm : Measurable m) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ s, ‖m s‖ ≤ B)

def multiplier : Hilbert →L[ℂ] Hilbert :=
  operator (fun x : Configuration => m x.1) (hm.comp measurable_fst) B hB (fun x => hb x.1)

theorem multiplier_coe (f : Hilbert) : multiplier m hm B hB hb f =ᵐ[volume] fun x => m x.1*f x :=
  operator_coe _ _ _ _ _ f

theorem multiplier_normalized (f : Hilbert) : multiplier m hm B hB hb f =
    ((B+1:ℝ):ℂ) • clockMultiplier (fun s => m s/(B+1:ℝ)) (hm.div_const _)
      (normalized_bound m B hB hb) f := rfl

theorem multiplier_charge (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    multiplier m hm B hB hb (action h hh θ f) = action h hh θ (multiplier m hm B hB hb f) := by
  rw [multiplier_normalized,multiplier_normalized,map_smul,
    multiplier_action (fun s => m s/(B+1:ℝ)) (hm.div_const _) (normalized_bound m B hB hb)]

theorem multiplier_coordinates (f : Hilbert) :
    chargeCoordinates (multiplier m hm B hB hb f) =ᵐ[volume]
      fun x => m (x (.inr 0))*chargeCoordinates f x := by
  rw [multiplier_normalized,map_smul,chargeCoordinates_multiplier]
  filter_upwards [Lp.coeFn_smul ((B+1:ℝ):ℂ)
      (jointMultiplier (fun s => m s/(B+1:ℝ)) (hm.div_const _) (normalized_bound m B hB hb) (chargeCoordinates f)),
    jointMultiplier_coe (fun s => m s/(B+1:ℝ)) (hm.div_const _) (normalized_bound m B hB hb) (chargeCoordinates f)]
    with x hs hj
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hj]
  have hn : ((B+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp

theorem multiplier_norm (f : Hilbert) : ‖multiplier m hm B hB hb f‖ ≤ B*‖f‖ :=
  operator_norm _ _ _ _ _ f

#print axioms multiplier_coe
#print axioms multiplier_normalized
#print axioms multiplier_charge
#print axioms multiplier_coordinates
#print axioms multiplier_norm
end
end UnifiedTheory.Audit.KFCausalBoundedClockCharge
