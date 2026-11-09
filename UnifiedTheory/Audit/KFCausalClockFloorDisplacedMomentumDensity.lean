/- Exact separation of the real phase momentum and imaginary Gaussian
derivative. Their cross term vanishes in the squared norm, leaving an
explicit abs(hbar) remainder after physical recentering. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhysicalPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhysicalPackets
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude source)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (gradient)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments (sourcedPacket)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian (weight)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant (gaussianEnvelope)

def pairing (v P : Transverse) : ℝ := ∑ i, v i*P i
def weightedPairing (α β : ℝ) (v X : Transverse) : ℝ := ∑ i, weight α β i*v i*X i
def moment (v ξ : Transverse) : ℝ := weightedPairing (groundWidth 1) (neutralWidth 1) v ξ

theorem gradient_centered (α β : ℝ) (Q R v X : Transverse) :
    gradient α β (KFCausalClockFloorCenteredGaussian.source α β Q R) v X =
      (-2*(weightedPairing α β v (X-Q):ℂ)+Complex.I*(pairing v R:ℂ))*
        sourcedPacket α β (KFCausalClockFloorCenteredGaussian.source α β Q R) X := by
  simp [gradient,KFCausalClockFloorCenteredGaussian.source,linearSource,weightedPairing,pairing,
    widths,weight,Fin.sum_univ_succ]
  ring

theorem weightedPairing_rescaled (h : ℝ) (hh : h ≠ 0) (Q v ξ : Transverse) :
    weightedPairing (groundWidth h) (neutralWidth h) v (rescaledPosition h Q ξ-Q) = moment v ξ/scale h := by
  unfold moment weightedPairing
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change weight (groundWidth h) (neutralWidth h) i*v i*(Q i+scale h*ξ i-Q i) = _
  rw [← weight_scale h hh i]
  field_simp [(scale_positive h hh).ne']
  ring

theorem pairing_div (v P : Transverse) (h : ℝ) :
    pairing v (fun i => P i/h) = pairing v P/h := by
  simp only [pairing,mul_div_assoc,Finset.sum_div]

theorem ratio_square (h : ℝ) (hh : h ≠ 0) : (h/scale h)^2 = |h| := by
  rw [div_pow,scale,Real.sq_sqrt (abs_nonneg h),← sq_abs h]
  field_simp [abs_ne_zero.mpr hh]

theorem momentum_coefficient (h : ℝ) (hh : h ≠ 0) (P v ξ : Transverse) :
    (-Complex.I*(h:ℂ))*(-2*(moment v ξ/scale h:ℝ)+Complex.I*(pairing v P/h:ℝ)) =
      (pairing v P:ℂ)+Complex.I*(2*(h/scale h)*moment v ξ:ℝ) := by
  push_cast
  field_simp [hh,(scale_positive h hh).ne']
  ring_nf
  rw [Complex.I_sq]
  ring

theorem momentum_coefficient_square (h : ℝ) (hh : h ≠ 0) (P v ξ : Transverse) :
    ‖(pairing v P:ℂ)+Complex.I*(2*(h/scale h)*moment v ξ:ℝ)‖^2 =
      (pairing v P)^2+4*|h| *(moment v ξ)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    sub_zero,add_zero,zero_add]
  calc
    _ = (pairing v P)^2+4*(h/scale h)^2*(moment v ξ)^2 := by ring
    _ = _ := by rw [ratio_square h hh]

theorem displaced_gradient_factor (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (v ξ : Transverse) :
    (-Complex.I*(h:ℂ))*amplitude h q k*
      gradient (groundWidth h) (neutralWidth h) (source h q k) v
        (rescaledPosition h (positionCenter h q k) ξ) =
      ((pairing v (phaseMomentum h q k):ℂ)+Complex.I*(2*(h/scale h)*moment v ξ:ℝ))*
        (amplitude h q k*sourcedPacket (groundWidth h) (neutralWidth h) (source h q k)
          (rescaledPosition h (positionCenter h q k) ξ)) := by
  rw [source_physical h hh,gradient_centered,weightedPairing_rescaled h hh,pairing_div]
  have hc := momentum_coefficient h hh (phaseMomentum h q k) v ξ
  calc
    _ = ((-Complex.I*(h:ℂ))*(-2*(moment v ξ/scale h:ℝ)+Complex.I*(pairing v (phaseMomentum h q k)/h:ℝ)))*
      (amplitude h q k*sourcedPacket (groundWidth h) (neutralWidth h)
        (KFCausalClockFloorCenteredGaussian.source (groundWidth h) (neutralWidth h)
          (positionCenter h q k) (fun i => phaseMomentum h q k i/h))
        (rescaledPosition h (positionCenter h q k) ξ)) := by ring
    _ = _ := by rw [hc]

theorem displaced_momentum_square (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (v ξ : Transverse) :
    ‖(-Complex.I*(h:ℂ))*amplitude h q k*
      gradient (groundWidth h) (neutralWidth h) (source h q k) v
        (rescaledPosition h (positionCenter h q k) ξ)‖^2 =
      ((pairing v (phaseMomentum h q k))^2+4*|h| *(moment v ξ)^2)*gaussianEnvelope 2 ξ := by
  rw [displaced_gradient_factor h hh,norm_mul,mul_pow,momentum_coefficient_square h hh,
    displacedPacket_recenter_square h hh]

theorem physical_gradient_factor (α β : ℝ) (v X : Transverse) :
    KFCausalPhysicalGaussianDerivative.gradient α β v X =
      (-2*(weightedPairing α β v X:ℂ))*KFCausalClockFloorShearBounds.physicalGaussian α β X := by
  simp [KFCausalPhysicalGaussianDerivative.gradient,weightedPairing,weight,widths,Fin.sum_univ_succ]
  ring

def momentDensity (v ξ : Transverse) : ℝ := (moment v ξ)^2*gaussianEnvelope 2 ξ

theorem momentDensity_eq (v ξ : Transverse) :
    momentDensity v ξ = (1/4)*‖KFCausalPhysicalGaussianDerivative.gradient (groundWidth 1) (neutralWidth 1) v ξ‖^2 := by
  rw [physical_gradient_factor,norm_mul,mul_pow]
  have he := KFCausalClockFloorRecenteredMajorant.gaussianEnvelope_square 2 ξ
  norm_num only [div_self (by norm_num : (2:ℝ) ≠ 0),one_mul] at he
  rw [← he]
  simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  norm_num
  unfold momentDensity moment
  ring

theorem momentDensity_integrable (v : Transverse) : Integrable (momentDensity v) := by
  have hm := KFCausalPhysicalGaussianDerivative.gradient_memLp (groundWidth 1) (neutralWidth 1)
    (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero) v
  apply (((memLp_two_iff_integrable_sq_norm hm.1).mp hm).const_mul (1/4:ℝ)).congr
  filter_upwards [] with ξ
  exact (momentDensity_eq v ξ).symm

#print axioms gradient_centered
#print axioms weightedPairing_rescaled
#print axioms pairing_div
#print axioms ratio_square
#print axioms momentum_coefficient
#print axioms momentum_coefficient_square
#print axioms displaced_gradient_factor
#print axioms displaced_momentum_square
#print axioms physical_gradient_factor
#print axioms momentDensity_eq
#print axioms momentDensity_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity
