/- The actual ordered output of the broad paired Gaussian has an explicit
physical-coordinate profile, with its complex relative shear and clock
amplitude retained. This supplies the input to a subsequent genuine partial
Fourier calculation; it does not analytically continue an L2 representative. -/
import UnifiedTheory.Audit.KFCausalBroadPairedGaussian
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputProfile
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedSqueezeFlow (squeeze diagonal offDiagonal)
open KFCausalPairedSqueezeTransport (transport transport_coe squeezeFlow squeezeFlow_apply
  squeezeFlow_quasiMeasurePreserving)
open KFCausalBroadPairedGaussian (output squeezeParameter charged_width neutral_width quadratic_squeeze)
open KFCausalPairedGaussianStates (quadratic)
open KFCausalRelativeGaussianDifferential (position exponent profile)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude gaussianState_profile)
open KFCausalClockFloorRelativeShift (scale)

theorem position_squeeze (t : ℝ) (r : ℂ) (q : Transverse) :
    position r (squeeze t q) 4=(Real.exp t:ℂ)*position r q 4 := by
  have hm : squeeze t q 2+squeeze t q 3=Real.exp t*(q 2+q 3) := by
    dsimp [squeeze,diagonal,offDiagonal]
    ring
  simp only [position,ite_true,← Complex.ofReal_add,hm]
  change ((Real.exp t*q 4:ℝ):ℂ)+_=_
  push_cast
  ring

private theorem exponent_zero (α β : ℝ) (r : ℂ) (q : Transverse) :
    exponent α β 0 r q= -(α:ℂ)*r^2*(KFCausalQuarticChargeProfiles.chargedRadius q:ℂ)-
      (β:ℂ)*(position r q 4)^2 := by
  simp [exponent,KFCausalPhysicalGaussianMoments.widths,Fin.sum_univ_succ,
    position,KFCausalQuarticChargeProfiles.chargedRadius]
  ring

theorem exponent_squeeze (α β t : ℝ) (r : ℂ) (q : Transverse) :
    exponent α (β*Real.exp (-2*t)) 0 r (squeeze t q)=
      -(α:ℂ)*r^2*(quadratic (Real.exp (2*t)) q:ℂ)-(β:ℂ)*(position r q 4)^2 := by
  rw [exponent_zero,quadratic_squeeze,position_squeeze,mul_pow]
  have he : (β*Real.exp (-2*t):ℝ)*(Real.exp t)^2=β := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [mul_assoc,← Real.exp_add]
    ring_nf
    rw [Real.exp_zero,mul_one]
  have hec := congrArg (fun x : ℝ => (x:ℂ)) he
  simp only [Complex.ofReal_mul,Complex.ofReal_pow] at hec
  simp only [Complex.ofReal_mul]
  rw [← mul_assoc,hec]

def outputProfile (ε a α w h : ℝ) (x : Configuration) : ℂ :=
  clockAmplitude ε a 0 (-h/2) x.1*
    Complex.exp (-(α:ℂ)*(scale ε (-h/2) x.1)^2*(quadratic w x.2:ℂ)-
      (α*w/128:ℝ)*(position (scale ε (-h/2) x.1) x.2 4)^2)

theorem output_coe (ε a α w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hw : 0 < w) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    output ε a α w hε ha hα h hb =ᵐ[volume] outputProfile ε a α w h := by
  let t := squeezeParameter w
  let f := KFCausalClockFloorSourcedSpectral.shiftedOutput ε a α (α/128)
    hε ha hα (by positivity) (by linarith) 1 0 0 h hb
  have hf : f =ᵐ[volume] profile (clockAmplitude ε a 0 (-h/2)) (scale ε (-h/2)) α (α/128) 0 := by
    simpa only [f,KFCausalClockFloorSourcedSpectral.shiftedOutput,one_smul] using
      gaussianState_profile ε a α (α/128) 0 (-h/2) 0 hε ha hα (by positivity)
        (by linarith) (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
  filter_upwards [Lp.coeFn_smul (Real.exp (-t/2):ℂ) (transport (-t) f),
    transport_coe (-t) f,(squeezeFlow_quasiMeasurePreserving (-t)).ae hf] with x hs ht hf'
  change ((Real.exp (-t/2):ℂ) • transport (-t) f) x=_
  rw [hs,Pi.smul_apply,smul_eq_mul,ht,hf']
  simp only [squeezeFlow_apply,neg_neg,profile]
  have hn := neutral_width α w hw
  change (α*w/128)*Real.exp (-2*t)=α/128 at hn
  rw [← hn,exponent_squeeze,charged_width w hw]
  rw [← mul_assoc,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show -t/2+t/2=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]
  rfl

theorem output_memLp (ε a α w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hw : 0 < w) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    MemLp (outputProfile ε a α w h) 2 volume :=
  (Lp.memLp (output ε a α w hε ha hα h hb)).ae_eq
    (output_coe ε a α w hε ha hα hw h hb)

#print axioms position_squeeze
#print axioms exponent_squeeze
#print axioms output_coe
#print axioms output_memLp
end
end UnifiedTheory.Audit.KFCausalBroadPairedGaussianOutputProfile
