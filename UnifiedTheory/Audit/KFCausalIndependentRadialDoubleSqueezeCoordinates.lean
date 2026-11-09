/- Exact configuration identities for the composition of reciprocal and
paired squeezes. Both radial parameters vary independently. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketProfiles
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets
import UnifiedTheory.Audit.KFCausalPairedSqueezeTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialDoubleSqueezeCoordinates
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalIndependentRadialPacketProfiles
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalQuarticChargeProfiles (chargedRadius)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial neutral_source_profile)
open KFCausalClockFloorCoherentDerivative (physicalProfile)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalNeutralExponentialProfiles (neutralSource)

def squeeze (t s : ℝ) (q : Transverse) : Transverse :=
  KFCausalReciprocalSqueezeFlow.squeeze t (KFCausalPairedSqueezeFlow.squeeze s q)

theorem first_difference (t s : ℝ) (q : Transverse) :
    squeeze t s q 0-squeeze t s q 1=Real.exp (t-s)*(q 0-q 1) := by
  simp [squeeze,KFCausalReciprocalSqueezeFlow.squeeze,KFCausalPairedSqueezeFlow.squeeze,
    KFCausalReciprocalSqueezeFlow.diagonal,KFCausalReciprocalSqueezeFlow.offDiagonal,
    KFCausalPairedSqueezeFlow.diagonal,KFCausalPairedSqueezeFlow.offDiagonal,
    sub_eq_add_neg,Real.exp_add]
  ring

theorem first_sum (t s : ℝ) (q : Transverse) :
    squeeze t s q 0+squeeze t s q 1=Real.exp (-(t-s))*(q 0+q 1) := by
  simp [squeeze,KFCausalReciprocalSqueezeFlow.squeeze,KFCausalPairedSqueezeFlow.squeeze,
    KFCausalReciprocalSqueezeFlow.diagonal,KFCausalReciprocalSqueezeFlow.offDiagonal,
    KFCausalPairedSqueezeFlow.diagonal,KFCausalPairedSqueezeFlow.offDiagonal,
    sub_eq_add_neg,Real.exp_add]
  ring

theorem second_difference (t s : ℝ) (q : Transverse) :
    squeeze t s q 2-squeeze t s q 3=Real.exp (-(t+s))*(q 2-q 3) := by
  simp [squeeze,KFCausalReciprocalSqueezeFlow.squeeze,KFCausalPairedSqueezeFlow.squeeze,
    KFCausalReciprocalSqueezeFlow.diagonal,KFCausalReciprocalSqueezeFlow.offDiagonal,
    KFCausalPairedSqueezeFlow.diagonal,KFCausalPairedSqueezeFlow.offDiagonal,Real.exp_add]
  ring

theorem second_sum (t s : ℝ) (q : Transverse) :
    squeeze t s q 2+squeeze t s q 3=Real.exp (t+s)*(q 2+q 3) := by
  simp [squeeze,KFCausalReciprocalSqueezeFlow.squeeze,KFCausalPairedSqueezeFlow.squeeze,
    KFCausalReciprocalSqueezeFlow.diagonal,KFCausalReciprocalSqueezeFlow.offDiagonal,
    KFCausalPairedSqueezeFlow.diagonal,KFCausalPairedSqueezeFlow.offDiagonal,Real.exp_add]
  ring

theorem neutral (t s : ℝ) (q : Transverse) :
    squeeze t s q 4=Real.exp (t+s)*q 4 := by
  simp [squeeze,KFCausalReciprocalSqueezeFlow.squeeze,KFCausalPairedSqueezeFlow.squeeze,
    Real.exp_add,mul_assoc]

private theorem radius_modes (q : Transverse) :
    chargedRadius q=(scale*(q 0-q 1))^2+(scale*(q 0+q 1))^2+
      (scale*(q 2-q 3))^2+(scale*(q 2+q 3))^2 := by
  unfold chargedRadius
  ring_nf
  rw [scale_square]
  ring

private theorem exp_square (u : ℝ) : (Real.exp u)^2=Real.exp (2*u) := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem quadratic (t s : ℝ) (q : Transverse) :
    chargedRadius (squeeze t s q)=chargedQuadratic (Real.exp (2*(t-s))) (Real.exp (2*(t+s))) q := by
  rw [radius_modes,first_difference,first_sum,second_difference,second_sum]
  simp only [chargedQuadratic,mul_pow,exp_square,div_eq_mul_inv,← Real.exp_neg]
  rw [show 2 * -(t-s)= -(2*(t-s)) by ring,show 2 * -(t+s)= -(2*(t+s)) by ring]
  ring

theorem neutral_rescaling (β t s : ℝ) (q : Transverse) :
    (β*Real.exp (-2*(t+s)))*(squeeze t s q 4)^2=β*(q 4)^2 := by
  rw [neutral,mul_pow,exp_square]
  calc
    _=β*(Real.exp (-2*(t+s))*Real.exp (2*(t+s)))*q 4^2 := by ring
    _=_ := by rw [← Real.exp_add]; simp

theorem source_rescaling (t s : ℝ) (b : ℂ) (P : Polynomial ℂ) (q : Transverse) :
    ((Real.exp (-(t+s)):ℂ)*b)*(squeeze t s q 4:ℂ)=b*(q 4:ℂ) ∧
      (rescaledPolynomial (t+s) P).eval (squeeze t s q 4:ℂ)=P.eval (q 4:ℂ) := by
  have hn : (Real.exp (-(t+s)):ℂ)*(squeeze t s q 4:ℂ)=(q 4:ℂ) := by
    rw [neutral,Complex.ofReal_mul,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    rw [neg_add_cancel,Real.exp_zero,Complex.ofReal_one,one_mul]
  constructor
  · rw [mul_assoc,mul_comm b,← mul_assoc,hn]
    ring
  · simp only [rescaledPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,hn]

theorem profile_transport (α β t s : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (g : ℝ → ℂ) (x : Configuration) :
    (prefactor (Real.exp (2*(t-s))) (Real.exp (2*(t+s))):ℂ)*
      ((rescaledPolynomial (t+s) P).eval (squeeze t s x.2 4:ℂ)*
      physicalProfile C p α (β*Real.exp (-2*(t+s)))
        (neutralSource ((Real.exp (-(t+s)):ℂ)*b)) g (x.1,squeeze t s x.2))=
      configurationProfile α β (Real.exp (2*(t-s))) (Real.exp (2*(t+s))) b P
        (fun u => C*clockPhase p (u:ℂ)*g u) x := by
  rw [(source_rescaling t s b P x.2).2,neutral_source_profile]
  dsimp only
  rw [(source_rescaling t s b P x.2).1]
  simp only [physicalProfile,KFCausalClockFloorCoherentDerivative.clockMultiplier,
    clockPhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,
    KFCausalClockFloorCoherentMoments.sourcedPacket,KFCausalClockFloorCoherentSources.linearSource,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,Complex.exp_zero,one_mul,
    KFCausalClockFloorShearBounds.physicalGaussian]
  have hs : (∑ i : Fin 4, (squeeze t s x.2 i.castSucc)^2)=chargedRadius (squeeze t s x.2) := by
    simp [Fin.sum_univ_succ,chargedRadius]
    ring
  rw [hs,quadratic,neutral_rescaling]
  simp only [configurationProfile,KFCausalNeutralLinePackets.packet,KFCausalNeutralLinePackets.entire]
  push_cast
  simp only [neg_add,Complex.exp_add]
  ring

#print axioms first_difference
#print axioms first_sum
#print axioms second_difference
#print axioms second_sum
#print axioms neutral
#print axioms quadratic
#print axioms neutral_rescaling
#print axioms source_rescaling
#print axioms profile_transport
end
end UnifiedTheory.Audit.KFCausalIndependentRadialDoubleSqueezeCoordinates
