/- The complementary transverse Fourier representation leaves the actual
clock coordinate untouched. Bounded clock multipliers, the inverse half-
clock and the natural half-clock graph retain their exact representatives. -/
import UnifiedTheory.Audit.KFCausalChargeTransverseSplit
import UnifiedTheory.Audit.KFCausalClockFloorChargedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDualClock
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalClockChargeMultiplier (clockMultiplier jointMultiplier jointMultiplier_coe chargeCoordinates_multiplier)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf half_inverse_graph)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

section Multiplier
variable (w : ℝ → ℂ) (hw : Measurable w) (hb : ∀ s, ‖w s‖ ≤ 1)

def dualProductMultiplier : ProductHilbert 5 1 →L[ℂ] ProductHilbert 5 1 :=
  rightMultiplier 5 1 (fun y => w (y 0)) (hw.comp (by fun_prop)) (fun y => hb (y 0))

def dualJointMultiplier : JointHilbert 5 1 →L[ℂ] JointHilbert 5 1 :=
  multiplyL (fun x => w (x (.inr 0))) (hw.comp (by fun_prop)) (fun x => hb (x (.inr 0)))

theorem dualJointMultiplier_coe (f : JointHilbert 5 1) :
    dualJointMultiplier w hw hb f =ᵐ[volume] fun x => w (x (.inr 0))*f x := multiplyL_coe _ _ _ f

theorem dual_coordinates_multiplier (f : ProductHilbert 5 1) :
    coordinates 5 1 (dualProductMultiplier w hw hb f) = dualJointMultiplier w hw hb (coordinates 5 1 f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe 5 1 (dualProductMultiplier w hw hb f),coordinates_coe 5 1 f,
    dualJointMultiplier_coe w hw hb (coordinates 5 1 f),
    (split_preserves_volume 5 1).quasiMeasurePreserving.ae
      (rightMultiplier_coe 5 1 (fun y => w (y 0)) (hw.comp (by fun_prop)) (fun y => hb (y 0)) f)] with x hc hf hd hp
  simp only [Function.comp_apply] at hc hf
  change (dualProductMultiplier w hw hb f) (split 5 1 x) = w ((split 5 1 x).2 0)*f (split 5 1 x) at hp
  rw [hc,hp,hd,hf,split_snd]

theorem repack_multiplier (f : JointHilbert 5 1) :
    repackPullback (dualJointMultiplier w hw hb f) = jointMultiplier w hw hb (repackPullback f) := by
  apply Lp.ext
  filter_upwards [repackPullback_coe (dualJointMultiplier w hw hb f),repackPullback_coe f,
    jointMultiplier_coe w hw hb (repackPullback f),
    repack_preserves.quasiMeasurePreserving.ae (dualJointMultiplier_coe w hw hb f)] with x hr hf hj hd
  simp only [Function.comp_apply] at hr hf
  rw [hr,hd,hj,hf,repack_clock]

theorem transverseCoordinates_multiplier (f : JointHilbert 2 4) :
    transverseCoordinates (jointMultiplier w hw hb f) = dualProductMultiplier w hw hb (transverseCoordinates f) := by
  apply (coordinates 5 1).injective
  apply repackPullback.injective
  rw [dual_coordinates_multiplier,repack_multiplier,transverseCoordinates_inverse,transverseCoordinates_inverse]

theorem dualMixed_multiplier (f : JointHilbert 2 4) :
    dualMixed (jointMultiplier w hw hb f) = dualJointMultiplier w hw hb (dualMixed f) := by
  change coordinates 5 1 (leftFourier 5 1 (transverseCoordinates (jointMultiplier w hw hb f))) = _
  rw [transverseCoordinates_multiplier]
  have he := leftFourier_commutes 5 1 (fun y => w (y 0)) (hw.comp (by fun_prop)) (fun y => hb (y 0))
    (transverseCoordinates f)
  change leftFourier 5 1 (dualProductMultiplier w hw hb (transverseCoordinates f)) =
    dualProductMultiplier w hw hb (leftFourier 5 1 (transverseCoordinates f)) at he
  rw [he,dual_coordinates_multiplier]
  rfl

theorem dualPhysical_multiplier (f : Hilbert) :
    dualPhysical (clockMultiplier w hw hb f) = dualJointMultiplier w hw hb (dualPhysical f) := by
  change dualMixed (KFCausalPhysicalCircleAction.chargeCoordinates (clockMultiplier w hw hb f)) = _
  rw [chargeCoordinates_multiplier,dualMixed_multiplier]
  rfl
end Multiplier

theorem inverseL_dual_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    dualPhysical (inverseL ε hε f) =ᵐ[volume] fun x =>
      (Real.sqrt (clock ε (x (.inr 0))) : ℂ)⁻¹*(dualPhysical f) x := by
  have he := dualPhysical_multiplier (normalizedInverse ε) (normalizedInverse_measurable ε)
    (normalizedInverse_bound ε hε) f
  rw [normalizedInverse_operator ε hε,map_smul] at he
  have hc : (Real.sqrt ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε).ne'
  filter_upwards [dualJointMultiplier_coe (normalizedInverse ε) (normalizedInverse_measurable ε)
    (normalizedInverse_bound ε hε) (dualPhysical f),
    Lp.coeFn_smul (Real.sqrt ε : ℂ) (dualPhysical (inverseL ε hε f))] with x hj hs
  have hx := congrArg (fun z : _ => z x) he
  dsimp only at hx
  rw [hs,hj] at hx
  simp only [Pi.smul_apply,smul_eq_mul,normalizedInverse] at hx
  apply mul_left_cancel₀ hc
  exact hx.trans (by unfold clock; ring)

theorem dualClockHalf_coe (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    dualPhysical g =ᵐ[volume] fun x => (Real.sqrt (clock ε (x (.inr 0))) : ℂ)*(dualPhysical f) x := by
  have he := (inverseL_graph ε hε g f).mp ((half_inverse_graph ε hε f g).mp hg)
  have hi := inverseL_dual_coe ε hε g
  rw [← he] at hi
  filter_upwards [hi] with x hx
  have hc : (Real.sqrt (clock ε (x (.inr 0))) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (clock_positive ε _ hε.le)).ne'
  rw [hx,← mul_assoc,mul_inv_cancel₀ hc,one_mul]

theorem dualClock_density (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    (fun x => ‖(dualPhysical g) x‖^2) =ᵐ[volume] fun x => clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2 := by
  filter_upwards [dualClockHalf_coe ε hε f g hg] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (clock_positive ε _ hε.le).le]

theorem dualClock_integrable (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    Integrable (fun x => clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2) :=
  ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (dualPhysical g))).mp
    (Lp.memLp (dualPhysical g))).congr (dualClock_density ε hε f g hg)

theorem dualClock_integral (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    (∫ x, clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2) = ‖g‖^2 := by
  rw [← integral_congr_ae (dualClock_density ε hε f g hg),← l2_norm_square,dualPhysical.norm_map]

#print axioms dualJointMultiplier_coe
#print axioms dual_coordinates_multiplier
#print axioms repack_multiplier
#print axioms transverseCoordinates_multiplier
#print axioms dualMixed_multiplier
#print axioms dualPhysical_multiplier
#print axioms inverseL_dual_coe
#print axioms dualClockHalf_coe
#print axioms dualClock_density
#print axioms dualClock_integrable
#print axioms dualClock_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorDualClock
