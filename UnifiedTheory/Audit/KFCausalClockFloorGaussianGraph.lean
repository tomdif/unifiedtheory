/- The Gaussian strip shift is an actual physical exponential graph pair.
Its unmultiplied input is identified with the proved spectral Gaussian core. -/
import UnifiedTheory.Audit.KFCausalGaussianStrip
import UnifiedTheory.Audit.KFCausalClockFloorGaussianCore
import UnifiedTheory.Audit.KFCausalClockFourierFubini
import UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
import UnifiedTheory.Audit.KFCausalL2FourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGraph
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
open UnifiedTheory.Audit.KFCausalGaussianStrip
open UnifiedTheory.Audit.KFCausalClockFourierFubini
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

variable (F : ℂ → ℂ) (v : Space) (d M : ℝ)
  (hF : ∀ q : ℂ, |q.im| ≤ d → AnalyticAt ℂ F q)
  (hM : 0 ≤ M) (hB : ∀ q : ℂ, |q.im| ≤ d → ‖F q‖ ≤ M)

include hF hM hB in
theorem full_fourier_shift (hbar : ℝ) (hs : |-hbar/2| ≤ d) (k : Space) :
    (exponentialWeight hbar k:ℂ)*(𝓕 (spectralLine F v 0)) k =
      (𝓕 (spectralLine F v (-hbar/2))) k := by
  have h0 : |(0:ℝ)| ≤ d := by simpa only [abs_zero] using (abs_nonneg (-hbar/2)).trans hs
  have hpoint (q : ℝ) (z : TailSpace) :
      (Real.exp (Real.pi*hbar*q):ℂ)*clockFourier (line F v 0) (q,z) =
        clockFourier (line F v (-hbar/2)) (q,z) := by
    change (Real.exp (Real.pi*hbar*q):ℂ)*(𝓕 (fun r : ℝ => line F v 0 (r,z))) q = _
    rw [clock_fourier_shift F v d M hF hM hB (-hbar/2) hs z q,
      ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    have he : Real.pi*hbar*q+2*Real.pi*q*(-hbar/2)=0 := by ring
    rw [he,Real.exp_zero,Complex.ofReal_one,one_mul]
    rfl
  unfold spectralLine
  rw [fourier_iterated _ (line_continuous F v d hF 0 h0) (line_integrable F v d M hF hB 0 h0),
    fourier_iterated _ (line_continuous F v d hF (-hbar/2) hs) (line_integrable F v d M hF hB (-hbar/2) hs)]
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul,exponentialWeight]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← hpoint]
  ring

def physicalState (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) : Hilbert :=
  (straightening ε hε).symm ((spectralLine_memLp F v d M hF hM hB y hy).toLp _)

theorem physicalState_coe (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) :
    straightening ε hε (physicalState F v d M hF hM hB ε hε y hy) =ᵐ[volume] spectralLine F v y := by
  change straightening ε hε ((straightening ε hε).symm _) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (spectralLine_memLp F v d M hF hM hB y hy).coeFn_toLp

theorem physicalState_fourier (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) :
    coupledFourier ε hε (physicalState F v d M hF hM hB ε hε y hy) =ᵐ[volume] 𝓕 (spectralLine F v y) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (straightening ε hε ((straightening ε hε).symm _)) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact fourier_toLp_coe _ (spectralLine_integrable F v d M hF hB y hy)
    (spectralLine_memLp F v d M hF hM hB y hy)

theorem physicalState_half_graph (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (h0 : |(0:ℝ)| ≤ d) (hs : |-hbar/2| ≤ d) :
    (physicalState F v d M hF hM hB ε hε 0 h0,
      physicalState F v d M hF hM hB ε hε (-hbar/2) hs) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply (longitudinal_exponential_graph ε hε hbar (1/2) _ _).mpr
  filter_upwards [physicalState_fourier F v d M hF hM hB ε hε 0 h0,
    physicalState_fourier F v d M hF hM hB ε hε (-hbar/2) hs] with k hk hl
  rw [hk,hl,← full_fourier_shift F v d M hF hM hB hbar hs k]
  congr 3
  unfold exponentialWeight KFCausalClockFloorFourierMultiplier.symbol
  ring

theorem gaussian_translation_fourier (v k : Space) :
    (𝓕 (spectralLine (fun _ => 1) v 0)) k =
      KFCausalEuclideanFourierUniqueness.modulate v gaussian k := by
  have he : spectralLine (fun _ => 1) v 0 = fun x => gaussian (x+v) := funext (spectralLine_one_zero v)
  rw [he]
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ Space) (gaussian : Space → ℂ) v) k
  have hg := congrFun (gaussian_fourier (E := Space)) k
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul,VectorFourier.fourierIntegral,
    Function.comp_apply,innerₗ_apply_apply] at hh hg ⊢
  rw [hh,hg]
  simp only [KFCausalEuclideanFourierUniqueness.modulate,real_inner_comm]

theorem physicalState_one_eq_packet (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (v : Space) (d : ℝ) (h0 : |(0:ℝ)| ≤ d) :
    physicalState (fun _ => 1) v d 1 (fun _ _ => analyticAt_const) (by norm_num)
      (fun _ _ => by simp) ε hε 0 h0 = (KFCausalClockFloorGaussianCore.packet ε hε hbar v).1 := by
  apply (coupledFourier ε hε).injective
  change coupledFourier ε hε (physicalState (fun _ => 1) v d 1 _ _ _ ε hε 0 h0) =
    coupledFourier ε hε ((coupledFourier ε hε).symm _)
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [physicalState_fourier (fun _ => 1) v d 1 (fun _ _ => analyticAt_const)
    (by norm_num) (fun _ _ => by simp) ε hε 0 h0,
    KFCausalModulatedLpTotality.state_coe (gaussian : Space → ℂ) gaussian_memLp v] with k hk hs
  rw [hk]
  exact (gaussian_translation_fourier v k).trans hs.symm

#print axioms full_fourier_shift
#print axioms physicalState_coe
#print axioms physicalState_fourier
#print axioms physicalState_half_graph
#print axioms gaussian_translation_fourier
#print axioms physicalState_one_eq_packet

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGraph
