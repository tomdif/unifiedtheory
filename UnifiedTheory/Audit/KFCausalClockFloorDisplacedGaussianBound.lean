/- A uniform Gaussian envelope after physical recentering. The actual
complex shift error is absorbed into a fixed-width Gaussian for small
hbar; no fixed-hbar source envelope is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedUniformShift
import UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedGaussianBound
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian
open UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates
open UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedUniformShift
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)

theorem gaussianFactor_error_bound (ε q h : ℝ) (hh : h ≠ 0) (Q ξ : Transverse) :
    ‖gaussianFactor ε q h Q ξ‖ ≤
      Real.exp (‖scaledDeviation ε q h‖^2*energy (shearVector (rescaledPosition h Q ξ))) *
        Real.exp (-energy ξ/2) := by
  have hb := packet_error_bound (groundWidth 1) (neutralWidth 1)
    (groundWidth_positive 1 one_ne_zero).le (neutralWidth_positive 1 one_ne_zero).le
    (0:Transverse) (0:Transverse) ξ
    (fun i => scaledDeviation ε q h*(shearVector (rescaledPosition h Q ξ) i:ℂ))
  have he : (∑ i, weight (groundWidth 1) (neutralWidth 1) i *
      ‖scaledDeviation ε q h*(shearVector (rescaledPosition h Q ξ) i:ℂ)‖^2) =
      ‖scaledDeviation ε q h‖^2*energy (shearVector (rescaledPosition h Q ξ)) := by
    simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,energy,realQuadratic,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Pi.zero_apply,zero_add,abs_zero,zero_mul,Finset.sum_const_zero,add_zero] at hb
  rw [he] at hb
  unfold gaussianFactor
  rw [quadratic_rescaled ε q h hh]
  have hf : fluctuation ε q h Q ξ =
      fun i => (ξ i:ℂ)+scaledDeviation ε q h*(shearVector (rescaledPosition h Q ξ) i:ℂ) :=
    funext (fluctuation_eq ε q h hh Q ξ)
  rw [hf]
  simpa only [packet,Pi.zero_apply,Complex.ofReal_zero,sub_zero,linear,zero_mul,
    Finset.sum_const_zero,mul_zero,add_zero,energy] using hb

theorem errorEnergy_bound (ε q h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ 4*ε) (Q ξ : Transverse) :
    ‖scaledDeviation ε q h‖^2*energy (shearVector (rescaledPosition h Q ξ)) ≤
      4*(scaleBound ε)^2*|h| * energy Q+4*(scaleBound ε)^2*|h|^2*energy ξ := by
  have hd := pow_le_pow_left₀ (norm_nonneg _) (scaledDeviation_bound ε q h hε hb hsmall) 2
  rw [mul_pow,scale,Real.sq_sqrt (abs_nonneg h)] at hd
  have he : energy (shearVector (rescaledPosition h Q ξ)) ≤ 4*energy Q+4*|h| * energy ξ := by
    have ht := (energy_shearVector (rescaledPosition h Q ξ)).trans
      (mul_le_mul_of_nonneg_left (energy_add_scale Q ξ (scale h)) (by norm_num : (0:ℝ) ≤ 2))
    apply ht.trans_eq
    rw [scale,Real.sq_sqrt (abs_nonneg h)]
    ring
  have ht := mul_le_mul hd he (energy_nonnegative _) (by positivity)
  exact ht.trans_eq (by ring)

theorem gaussianFactor_bound (ε q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ ε/2) (h1 : |h| ≤ 1) (Q ξ : Transverse) :
    ‖gaussianFactor ε q h Q ξ‖ ≤
      Real.exp (4*(scaleBound ε)^2*energy Q)*Real.exp (-energy ξ/4) := by
  apply (gaussianFactor_error_bound ε q h hh Q ξ).trans
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := errorEnergy_bound ε q h hε hb (by linarith) Q ξ
  have hQ := mul_le_mul_of_nonneg_left h1
    (show 0 ≤ 4*(scaleBound ε)^2*energy Q from by positivity [energy_nonnegative Q])
  have hξ := mul_le_mul_of_nonneg_right (small_coefficient ε h hε hsmall) (energy_nonnegative ξ)
  nlinarith

theorem gaussianFactor_square_bound (ε q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ ε/2) (h1 : |h| ≤ 1) (Q ξ : Transverse) :
    ‖gaussianFactor ε q h Q ξ‖^2 ≤
      Real.exp (8*(scaleBound ε)^2*energy Q)*Real.exp (-energy ξ/2) := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (gaussianFactor_bound ε q h hε hh hb hsmall h1 Q ξ) 2
  rw [mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul] at ht
  convert ht using 1
  congr 1
  · congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  · congr 1
    norm_num only [Nat.cast_ofNat]
    ring

#print axioms gaussianFactor_error_bound
#print axioms errorEnergy_bound
#print axioms gaussianFactor_bound
#print axioms gaussianFactor_square_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedGaussianBound
