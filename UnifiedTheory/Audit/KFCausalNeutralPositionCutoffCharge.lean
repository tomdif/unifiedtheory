/- The physical Gaussian localizer is an actual spectator multiplier in
the mixed charge coordinates. This identifies its L2 approximation error
with a charged-coordinate integral; charge commutation is not asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics
import UnifiedTheory.Audit.KFCausalClockFloorChargedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianCutoff (cutoff cutoff_coe)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics (chargedLinear input input_eq)

def spectatorDamping (δ : ℝ) (x : Block 4) : ℂ := (Real.exp (-2*δ*(x 2)^2):ℂ)

theorem spectatorDamping_measurable (δ : ℝ) : Measurable (spectatorDamping δ) := by
  unfold spectatorDamping
  fun_prop

theorem spectatorDamping_norm (δ : ℝ) (hδ : 0 < δ) (x : Block 4) :
    ‖spectatorDamping δ x‖ ≤ 1 := by
  rw [spectatorDamping,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

theorem charged_square (x : Space) :
    (chargedLinear (KFCausalEuclideanConfiguration.split x))^2 =
      2*((split 2 4 (modeIsometry x)).2 2)^2 := by
  change (x 3+x 4)^2 = 2*(scale*(x 3+x 4))^2
  rw [mul_pow,scale_square]
  ring

theorem spectatorDamping_physical (δ : ℝ) (x : Space) :
    spectatorDamping δ (split 2 4 (modeIsometry x)).2 =
      (KFCausalGaussianCutoffTaylor.amplitude δ
        (chargedLinear (KFCausalEuclideanConfiguration.split x)):ℂ) := by
  unfold spectatorDamping KFCausalGaussianCutoffTaylor.amplitude
  rw [charged_square]
  congr 2
  ring

theorem euclidean_cutoff (δ : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    euclideanPullback (cutoff δ hδ chargedLinear f) =
      euclideanMultiplier (spectatorDamping δ) (spectatorDamping_measurable δ)
        (spectatorDamping_norm δ hδ) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (cutoff δ hδ chargedLinear f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (cutoff_coe δ hδ chargedLinear f),
    euclideanMultiplier_coe (spectatorDamping δ) (spectatorDamping_measurable δ)
      (spectatorDamping_norm δ hδ) (euclideanPullback f),euclideanPullback_coe f] with x he ha hm hf
  simp only [Function.comp_apply] at he hf
  change cutoff δ hδ chargedLinear f (KFCausalEuclideanConfiguration.split x) = _ at ha
  rw [he,ha,hm,hf,spectatorDamping_physical]

theorem charge_cutoff_coe (δ : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    chargeCoordinates (cutoff δ hδ chargedLinear f) =ᵐ[volume] fun x =>
      (Real.exp (-2*δ*(x (.inr 2))^2):ℂ)*(chargeCoordinates f) x := by
  rw [← chargeEuclidean_physical,euclidean_cutoff,chargeEuclidean_multiplier,chargeEuclidean_physical]
  exact jointMultiplier_coe (spectatorDamping δ) (spectatorDamping_measurable δ) (spectatorDamping_norm δ hδ) _

theorem norm_difference (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    ‖input ε δ v hε hδ f-KFCausalNeutralPositionCharge.action v f‖ =
      ‖cutoff δ hδ chargedLinear f-f‖ := by
  rw [input_eq,← map_sub,(KFCausalNeutralPositionCharge.action v).norm_map]

theorem norm_difference_square (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    ‖input ε δ v hε hδ f-KFCausalNeutralPositionCharge.action v f‖^2 =
      ∫ x : Joint 2 4, (Real.exp (-2*δ*(x (.inr 2))^2)-1)^2*‖(chargeCoordinates f) x‖^2 := by
  rw [norm_difference,← chargeCoordinates.norm_map (cutoff δ hδ chargedLinear f-f),map_sub,
    KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (chargeCoordinates (cutoff δ hδ chargedLinear f)) (chargeCoordinates f),
    charge_cutoff_coe δ hδ f] with x hs hc
  rw [hs]
  simp only [Pi.sub_apply,hc]
  have he : (Real.exp (-2*δ*(x (.inr 2))^2):ℂ)*(chargeCoordinates f) x-(chargeCoordinates f) x =
      ((Real.exp (-2*δ*(x (.inr 2))^2)-1:ℝ):ℂ)*(chargeCoordinates f) x := by
    push_cast
    ring
  rw [he,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

#print axioms spectatorDamping_measurable
#print axioms spectatorDamping_norm
#print axioms charged_square
#print axioms spectatorDamping_physical
#print axioms euclidean_cutoff
#print axioms charge_cutoff_coe
#print axioms norm_difference
#print axioms norm_difference_square

end
end UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharge
