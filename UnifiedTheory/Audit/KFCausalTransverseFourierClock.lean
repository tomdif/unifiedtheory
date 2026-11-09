/- The actual transverse partial Fourier unitary commutes with full
Fourier transformation and preserves every measurable unbounded spectator
multiplication relation, including the clock spectral exponential. -/
import UnifiedTheory.Audit.KFCausalL2FourierIsometry
import UnifiedTheory.Audit.KFCausalFullFourierProduct
import UnifiedTheory.Audit.KFCausalChargeSpectatorRelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalTransverseFourierClock
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates (pairedEuclidean chargeEuclidean)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalFullFourierProduct
open UnifiedTheory.Audit.KFCausalChargeSpectatorRelation (chargeEuclidean_relation)

theorem mode_fourier (f : JointHilbert 2 4) :
    (Lp.fourierTransformₗᵢ Space ℂ) (modePullback f) = modePullback ((Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) f) :=
  KFCausalL2FourierIsometry.fourier_pullback modeIsometry f

theorem coordinates_fullFourier (f : ProductHilbert 2 4) :
    coordinates 2 4 (fullFourier 2 4 f) = (Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) (coordinates 2 4 f) :=
  (coordinates 2 4).apply_symm_apply _

theorem position_paired (f : FrequencyHilbert) : modePullback (coordinates 2 4 (pairedEuclidean f)) = f :=
  (congrArg modePullback ((coordinates 2 4).apply_symm_apply (modePullback.symm f))).trans
    (modePullback.apply_symm_apply f)

theorem paired_fourier (f : FrequencyHilbert) :
    pairedEuclidean ((Lp.fourierTransformₗᵢ Space ℂ) f) = fullFourier 2 4 (pairedEuclidean f) := by
  apply (coordinates 2 4).injective
  apply modePullback.injective
  rw [position_paired,coordinates_fullFourier,← mode_fourier,position_paired]

theorem charge_fourier (f : FrequencyHilbert) :
    chargeEuclidean ((Lp.fourierTransformₗᵢ Space ℂ) f) =
      (Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) (chargeEuclidean f) := by
  change coordinates 2 4 (leftFourier 2 4 (pairedEuclidean ((Lp.fourierTransformₗᵢ Space ℂ) f))) = _
  rw [paired_fourier,← fullFourier_left_commutes,coordinates_fullFourier]
  rfl

def transverseFourier : FrequencyHilbert ≃ₗᵢ[ℂ] FrequencyHilbert := chargeEuclidean.trans modePullback

theorem transverse_fourier_commutes (f : FrequencyHilbert) :
    transverseFourier ((Lp.fourierTransformₗᵢ Space ℂ) f) =
      (Lp.fourierTransformₗᵢ Space ℂ) (transverseFourier f) := by
  change modePullback (chargeEuclidean ((Lp.fourierTransformₗᵢ Space ℂ) f)) = _
  rw [charge_fourier]
  exact (mode_fourier (chargeEuclidean f)).symm

theorem mode_relation (a : Block 4 → ℂ) (f g : JointHilbert 2 4) :
    (g =ᵐ[volume] fun x => a (split 2 4 x).2*f x) ↔
      modePullback g =ᵐ[volume] fun x => a (split 2 4 (modeIsometry x)).2*(modePullback f) x := by
  constructor
  · intro hfg
    filter_upwards [modePullback_coe f,modePullback_coe g,
      mode_preserves_volume.quasiMeasurePreserving.ae hfg] with x hf hg hh
    rw [hf,hg]
    exact hh
  · intro hfg
    have he : ∀ᵐ x : Space ∂volume, g (modeIsometry x) = a (split 2 4 (modeIsometry x)).2*f (modeIsometry x) := by
      filter_upwards [modePullback_coe f,modePullback_coe g,hfg] with x hf hg hh
      rw [hf,hg] at hh
      exact hh
    have hr := modeIsometry.symm.measurePreserving.quasiMeasurePreserving.ae he
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hr

theorem transverse_relation (a : Block 4 → ℂ) (ha : Measurable a) (f g : FrequencyHilbert) :
    (g =ᵐ[volume] fun x => a (split 2 4 (modeIsometry x)).2*f x) ↔
      transverseFourier g =ᵐ[volume] fun x => a (split 2 4 (modeIsometry x)).2*(transverseFourier f) x :=
  (chargeEuclidean_relation a ha f g).trans (mode_relation a (chargeEuclidean f) (chargeEuclidean g))

theorem clock_relation (a : ℝ → ℂ) (ha : Measurable a) (f g : FrequencyHilbert) :
    (g =ᵐ[volume] fun x => a (x 0)*f x) ↔
      transverseFourier g =ᵐ[volume] fun x => a (x 0)*(transverseFourier f) x :=
  transverse_relation (fun y => a (y 0)) (ha.comp (by fun_prop)) f g

#print axioms mode_fourier
#print axioms coordinates_fullFourier
#print axioms position_paired
#print axioms paired_fourier
#print axioms charge_fourier
#print axioms transverse_fourier_commutes
#print axioms mode_relation
#print axioms transverse_relation
#print axioms clock_relation

end
end UnifiedTheory.Audit.KFCausalTransverseFourierClock
