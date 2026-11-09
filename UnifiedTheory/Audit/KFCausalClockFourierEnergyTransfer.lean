/- Transfer a joint clock-Fourier energy estimate to the full Fourier
transform by transverse Plancherel. The input may couple clock and all
transverse variables; the necessary joint integrability is explicit. -/
import UnifiedTheory.Audit.KFCausalClockFourierFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFourierEnergyTransfer
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockFourierFubini
open UnifiedTheory.Audit.KFCausalProductFourierEnergy (transverse_plancherel)
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

theorem clockFourier_slice_memLp (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hp : MemLp (clockFourier f) 2) :
    ∀ᵐ k ∂(volume : Measure ℝ), MemLp (fun y => clockFourier f (k,y)) 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm hp.1).mp hp
  rw [Measure.volume_eq_prod ℝ TailSpace] at hi
  filter_upwards [hi.prod_right_ae] with k hk
  exact (memLp_two_iff_integrable_sq_norm (clockFourier_slice_integrable f hc hf k).1).mpr hk

theorem fullFourier_slice_plancherel (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hp : MemLp (clockFourier f) 2) :
    ∀ᵐ k ∂(volume : Measure ℝ),
      (∫ y : TailSpace, ‖fullFourier f (k,y)‖^2) = ∫ y : TailSpace, ‖clockFourier f (k,y)‖^2 := by
  filter_upwards [clockFourier_slice_memLp f hc hf hp] with k hk
  simp_rw [fullFourier_slice f hc hf]
  exact transverse_plancherel _ (clockFourier_slice_integrable f hc hf k) hk

theorem fullFourier_weighted_integrable (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hp : MemLp (clockFourier f) 2) (b : ℝ)
    (he : Integrable (fun w : ℝ × TailSpace => Real.exp (b*w.1)*‖clockFourier f w‖^2)) :
    Integrable (fun w : ℝ × TailSpace => Real.exp (b*w.1)*‖fullFourier f w‖^2) := by
  have hm : AEStronglyMeasurable
      (fun w : ℝ × TailSpace => Real.exp (b*w.1)*‖fullFourier f w‖^2) volume :=
    (((measurable_const.mul measurable_fst).exp).mul ((fullFourier_measurable f hf).norm.pow_const 2)).aestronglyMeasurable
  rw [Measure.volume_eq_prod ℝ TailSpace] at he hm ⊢
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [clockFourier_slice_memLp f hc hf hp] with k hk
    have ht := integralFourier_memLp _ (clockFourier_slice_integrable f hc hf k) hk
    have hi := (memLp_two_iff_integrable_sq_norm ht.1).mp ht
    simpa only [fullFourier_slice f hc hf] using hi.const_mul (Real.exp (b*k))
  · have hi := he.integral_norm_prod_left
    apply hi.congr
    filter_upwards [fullFourier_slice_plancherel f hc hf hp] with k hk
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_sq,integral_const_mul]
    rw [hk]

theorem euclidean_weighted_integrable (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hp : MemLp (clockFourier f) 2) (b : ℝ)
    (he : Integrable (fun w : ℝ × TailSpace => Real.exp (b*w.1)*‖clockFourier f w‖^2)) :
    Integrable (fun k : Space => Real.exp (b*k 0)*‖(𝓕 (f ∘ euclideanSplit)) k‖^2) := by
  have hi := euclideanSplit_preserves_volume.integrable_comp_of_integrable
    (fullFourier_weighted_integrable f hc hf hp b he)
  simpa only [Function.comp_apply,fullFourier,MeasurableEquiv.symm_apply_apply,euclideanSplit_apply] using hi

theorem weighted_energy_identity (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hp : MemLp (clockFourier f) 2) (b : ℝ)
    (he : Integrable (fun w : ℝ × TailSpace => Real.exp (b*w.1)*‖clockFourier f w‖^2)) :
    (∫ k : Space, Real.exp (b*k 0)*‖(𝓕 (f ∘ euclideanSplit)) k‖^2) =
      ∫ w : ℝ × TailSpace, Real.exp (b*w.1)*‖clockFourier f w‖^2 := by
  have hi := fullFourier_weighted_integrable f hc hf hp b he
  have hchange := euclideanSplit_preserves_volume.integral_comp'
    (fun w : ℝ × TailSpace => Real.exp (b*w.1)*‖fullFourier f w‖^2)
  have heq : (∫ k : Space, Real.exp (b*k 0)*‖(𝓕 (f ∘ euclideanSplit)) k‖^2) =
      ∫ w : ℝ × TailSpace, Real.exp (b*w.1)*‖fullFourier f w‖^2 := by
    simpa only [fullFourier,MeasurableEquiv.symm_apply_apply,euclideanSplit_apply] using hchange
  rw [heq,Measure.volume_eq_prod ℝ TailSpace]
  rw [Measure.volume_eq_prod ℝ TailSpace] at hi he
  rw [integral_prod _ hi,integral_prod _ he]
  apply integral_congr_ae
  filter_upwards [fullFourier_slice_plancherel f hc hf hp] with k hk
  simp only [integral_const_mul,hk]

#print axioms clockFourier_slice_memLp
#print axioms fullFourier_slice_plancherel
#print axioms fullFourier_weighted_integrable
#print axioms euclidean_weighted_integrable
#print axioms weighted_energy_identity

end
end UnifiedTheory.Audit.KFCausalClockFourierEnergyTransfer
