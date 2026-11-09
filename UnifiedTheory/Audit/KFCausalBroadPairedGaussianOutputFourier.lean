/- Exact partial Fourier transform of the ACTUAL broad paired ordered
output. Slice integrability follows from the positive complex Gaussian
coefficient, and joint output L2 is derived by fiber Plancherel. The
clock-dependent normalization and neutral shear are retained. -/
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputProfile
import UnifiedTheory.Audit.KFCausalPhysicalFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalPartialFourierFiberPlancherel

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalFourierGeneralCoordinates (Product pairedChart pairedChart_preserves_volume
  pairedChart_symm pairedCoordinates_coe)
open KFCausalPhysicalMixedCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalShiftedPhysicalFourierSlices (reconstruct reconstruct_neutral)
open KFCausalShiftedNarrowFourierGeometry (neutral broadRadius radius shifted_coefficient_positive)
open KFCausalShiftedNarrowFourierSlices (gaussian gaussian_integrable gaussian_fourier fourier_mul_right)
open KFCausalBroadPairedGaussianOutputProfile (outputProfile output_coe)
open KFCausalBroadPairedGaussian (output)
open KFCausalPairedGaussianStates (quadratic)
open KFCausalPairedModeCoordinates (scale_square)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalPartialFourierFiberFormula (sliceFourier)

theorem paired_quadratic (w : ℝ) (u : Block 2) (v : Block 4) :
    quadratic w (reconstruct u v)=‖u‖^2/w+w*broadRadius v := by
  rw [KFCausalShiftedNarrowFourierGeometry.narrow_norm_square]
  dsimp [quadratic,reconstruct,broadRadius]
  ring_nf
  rw [scale_square]
  ring

def input (ε a α w h : ℝ) (z : Product) : ℂ :=
  outputProfile ε a α w h (z.2 0,reconstruct z.1 z.2)

def transformed (ε a α w h : ℝ) (z : Product) : ℂ :=
  ((Real.pi:ℂ)/((α:ℂ)*(scale ε (-h/2) (z.2 0))^2))*(w:ℂ)*
    clockAmplitude ε a 0 (-h/2) (z.2 0)*
      Complex.exp (-(w:ℂ)*radius ((α:ℂ)*(scale ε (-h/2) (z.2 0))^2) z.1 z.2-
        (α*w/128:ℝ)*(neutral (scale ε (-h/2) (z.2 0)) z.2)^2)

private theorem input_factor (ε a α w h : ℝ) (u : Block 2) (v : Block 4) :
    input ε a α w h (u,v)=
      gaussian ((α:ℂ)*(scale ε (-h/2) (v 0))^2/(w:ℂ)) u*
        (clockAmplitude ε a 0 (-h/2) (v 0)*
          Complex.exp (-((α:ℂ)*(scale ε (-h/2) (v 0))^2)*(w:ℂ)*(broadRadius v:ℂ)-
            (α*w/128:ℝ)*(neutral (scale ε (-h/2) (v 0)) v)^2)) := by
  unfold input outputProfile
  rw [paired_quadratic,reconstruct_neutral]
  simp only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,gaussian]
  rw [show -(α:ℂ)*(scale ε (-h/2) (v 0))^2*
      ((‖u‖:ℂ)^2/(w:ℂ)+(w:ℂ)*(broadRadius v:ℂ))-
      ((α:ℂ)*(w:ℂ)/(128:ℂ))*(neutral (scale ε (-h/2) (v 0)) v)^2 =
    -((α:ℂ)*(scale ε (-h/2) (v 0))^2/(w:ℂ))*(‖u‖:ℂ)^2+
      (-((α:ℂ)*(scale ε (-h/2) (v 0))^2)*(w:ℂ)*(broadRadius v:ℂ)-
        ((α:ℂ)*(w:ℂ)/(128:ℂ))*(neutral (scale ε (-h/2) (v 0)) v)^2) by ring,
    Complex.exp_add]
  ring

theorem slice_integrable (ε a α w h : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hw : 0 < w) (hb : |h| ≤ 2*Real.pi*ε/3) (v : Block 4) :
    Integrable (fun u => input ε a α w h (u,v)) := by
  have hp := shifted_coefficient_positive α ε (-h/2) (v 0) hα hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
  have hA : 0 < ((α:ℂ)*(scale ε (-h/2) (v 0))^2/(w:ℂ)).re := by
    simpa using div_pos hp hw
  simp_rw [input_factor]
  exact (gaussian_integrable _ hA).mul_const _

theorem slice_fourier (ε a α w h : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hw : 0 < w) (hb : |h| ≤ 2*Real.pi*ε/3) (z : Product) :
    sliceFourier 2 4 (input ε a α w h) z=transformed ε a α w h z := by
  have hp := shifted_coefficient_positive α ε (-h/2) (z.2 0) hα hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
  have hA : 0 < ((α:ℂ)*(scale ε (-h/2) (z.2 0))^2/(w:ℂ)).re := by
    simpa using div_pos hp hw
  unfold sliceFourier
  simp_rw [input_factor]
  rw [fourier_mul_right,gaussian_fourier _ hA]
  unfold transformed gaussian radius
  rw [show -(w:ℂ)*((Real.pi:ℂ)^2/((α:ℂ)*(scale ε (-h/2) (z.2 0))^2)*
      (‖z.1‖:ℂ)^2+((α:ℂ)*(scale ε (-h/2) (z.2 0))^2)*(broadRadius z.2:ℂ))-
      (α*w/128:ℝ)*(neutral (scale ε (-h/2) (z.2 0)) z.2)^2 =
    -((Real.pi:ℂ)^2/((α:ℂ)*(scale ε (-h/2) (z.2 0))^2/(w:ℂ)))*(‖z.1‖:ℂ)^2+
      (-((α:ℂ)*(scale ε (-h/2) (z.2 0))^2)*(w:ℂ)*(broadRadius z.2:ℂ)-
        (α*w/128:ℝ)*(neutral (scale ε (-h/2) (z.2 0)) z.2)^2) by
      rw [div_div_eq_mul_div]; ring,Complex.exp_add,div_div_eq_mul_div]
  ring

theorem transformed_measurable (ε a α w h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) : Measurable (transformed ε a α w h) := by
  have hr := (scale_smooth ε (-h/2) hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)).continuous.measurable
  have hc := (clockAmplitude_smooth ε a 0 (-h/2) hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)).continuous.measurable
  unfold transformed radius neutral broadRadius
  fun_prop

theorem output_mixed_coe (ε a α w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hw : 0 < w) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    mixedCoordinates (output ε a α w hε ha hα h hb) =ᵐ[volume]
      transformed ε a α w h := by
  let f := output ε a α w hε ha hα h hb
  have hp : pairedCoordinates f =ᵐ[volume] input ε a α w h := by
    have ht := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae
      (output_coe ε a α w hε ha hα hw h hb)
    filter_upwards [pairedCoordinates_coe f,ht] with z hz ht
    rw [pairedChart_symm] at ht
    exact hz.trans ht
  have hi : MemLp (input ε a α w h) 2 volume := (Lp.memLp (pairedCoordinates f)).ae_eq hp
  have he : pairedCoordinates f=hi.toLp (input ε a α w h) := by
    apply Lp.ext
    exact hp.trans hi.coeFn_toLp.symm
  have hm : AEStronglyMeasurable (sliceFourier 2 4 (input ε a α w h)) volume := by
    rw [funext (slice_fourier ε a α w h hε hα hw hb)]
    exact (transformed_measurable ε a α w h hε hb).aestronglyMeasurable
  have ht := KFCausalPartialFourierFiberPlancherel.leftFourier_toLp_coe 2 4
    (input ε a α w h) hi
    (Filter.Eventually.of_forall (slice_integrable ε a α w h hε hα hw hb)) hm
  change KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates f) =ᵐ[volume] _
  rw [he]
  exact ht.trans (Filter.Eventually.of_forall (slice_fourier ε a α w h hε hα hw hb))

#print axioms paired_quadratic
#print axioms slice_integrable
#print axioms slice_fourier
#print axioms transformed_measurable
#print axioms output_mixed_coe
end
end UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputFourier
