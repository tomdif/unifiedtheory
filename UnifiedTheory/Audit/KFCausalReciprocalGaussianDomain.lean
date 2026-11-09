/- Actual natural energy-factor domains for the reciprocal Gaussian family.
The proof transports already established Gaussian graphs through the
reciprocal squeeze. The sufficient range w >= 1 is not a sharp boundary. -/
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeEnergy
import UnifiedTheory.Audit.KFCausalReciprocalGaussianCharge
import UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalSqueezeFlow
open KFCausalReciprocalSqueezeTransport
open KFCausalReciprocalGaussianStates (quadratic configurationDensity)
open KFCausalQuarticChargeProfiles (chargedRadius)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalClockFloorInvariantTrial
  (neutralWidth clockFunction neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorCommonDomain (commonEnergyDomain energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

private theorem exp_square (t : ℝ) : Real.exp (2*t) = (Real.exp t)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num

private theorem exp_cancel (t : ℝ) : Real.exp t*Real.exp (-t) = 1 := by
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]

theorem quadratic_squeeze (t : ℝ) (q : Transverse) :
    chargedRadius (squeeze t q) = quadratic (Real.exp (2*t)) q := by
  rw [quadratic,one_div,← Real.exp_neg,show -(2*t)=2*(-t) by ring,
    exp_square t,exp_square (-t)]
  dsimp [chargedRadius,squeeze,diagonal,offDiagonal,pairPolynomial]
  ring

theorem neutral_rescaling (β t : ℝ) (q : Transverse) :
    (β*Real.exp (-2*t))*(squeeze t q 4)^2 = β*(q 4)^2 := by
  change (β*Real.exp (-2*t))*(Real.exp t*q 4)^2 = _
  rw [mul_pow,← exp_square]
  calc
    _ = β*(Real.exp (-2*t)*Real.exp (2*t))*q 4^2 := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem profile_squeeze (α β t : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    KFCausalClockFloorCoherentDerivative.physicalProfile 1 0 α (β*Real.exp (-2*t)) 0 g
      (x.1,squeeze t x.2) = configurationDensity α β (Real.exp (2*t)) g x := by
  simp only [KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentStrip.clockPhase,Complex.ofReal_zero,zero_mul,
    Complex.exp_zero,one_mul,KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,Complex.exp_zero,one_mul,
    KFCausalClockFloorShearBounds.physicalGaussian,configurationDensity]
  congr 2
  have hs : (∑ i : Fin 4, (squeeze t x.2 i.castSucc)^2) = chargedRadius (squeeze t x.2) := by
    simp [Fin.sum_univ_succ,chargedRadius]
    ring
  rw [hs,quadratic_squeeze,neutral_rescaling]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

def baseWidth (t : ℝ) : ℝ := neutralWidth h*Real.exp (-2*t)

include hh in
theorem baseWidth_positive (t : ℝ) : 0 < baseWidth h t :=
  mul_pos (neutralWidth_positive h hh) (Real.exp_pos _)

include hh in
theorem baseWidth_bound (t : ℝ) (ht : 0 ≤ t) : 32*baseWidth h t ≤ groundWidth h := by
  have he : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb := mul_le_mul_of_nonneg_left he (neutralWidth_positive h hh).le
  unfold baseWidth
  nlinarith [neutralWidth_bound h]

def baseState (t : ℝ) (ht : 0 ≤ t) : Hilbert :=
  KFCausalClockFloorSourcedClockMomentum.state ε a (groundWidth h) (baseWidth h t)
    hε ha (groundWidth_positive h hh) (baseWidth_positive h hh t)
    (baseWidth_bound h hh t ht) 1 0 0

theorem state_transport (t : ℝ) (ht : 0 ≤ t) :
    KFCausalReciprocalGaussianCharge.state ε a h (Real.exp (2*t)) hε ha hh (Real.exp_pos _) =
      (Real.exp (-t/2):ℂ) • transport (-t) (baseState ε a h hε ha hh t ht) := by
  apply Lp.ext
  filter_upwards [KFCausalReciprocalGaussianCharge.state_configuration_coe ε a h
      (Real.exp (2*t)) hε ha hh (Real.exp_pos _),
    Lp.coeFn_smul (Real.exp (-t/2):ℂ) (transport (-t) (baseState ε a h hε ha hh t ht)),
    transport_coe (-t) (baseState ε a h hε ha hh t ht),
    (squeezeFlow_quasiMeasurePreserving (-t)).ae
      (KFCausalClockFloorSourcedClockMomentum.state_coe ε a (groundWidth h) (baseWidth h t)
        hε ha (groundWidth_positive h hh) (baseWidth_positive h hh t)
        (baseWidth_bound h hh t ht) 1 0 0)] with x hx hc hu hb
  change _ = _ at hb
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hu]
  change _ = (Real.exp (-t/2):ℂ)*((Real.exp (-(-t)/2):ℂ)*
    (baseState ε a h hε ha hh t ht) (squeezeFlow (-t) x))
  change (baseState ε a h hε ha hh t ht) (squeezeFlow (-t) x) = _ at hb
  rw [hb]
  simp only [squeezeFlow_apply,neg_neg,baseWidth]
  rw [profile_squeeze,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,
    show -t/2+t/2=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]

theorem state_commonEnergyDomain (w : ℝ) (hw : 1 ≤ w)
    (hstrip : |h| ≤ 2*Real.pi*ε/3) :
    KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith) ∈
      commonEnergyDomain ε hε h modelDirections pointField := by
  have ht : 0 ≤ Real.log w/2 := div_nonneg (Real.log_nonneg hw) (by norm_num)
  have he : Real.exp (2*(Real.log w/2)) = w := by
    rw [show 2*(Real.log w/2)=Real.log w by ring,Real.exp_log (by linarith)]
  have hb := KFCausalClockFloorSourcedCommonDomain.state_commonEnergyDomain ε a
    (groundWidth h) (baseWidth h (Real.log w/2)) hε ha (groundWidth_positive h hh)
    (baseWidth_positive h hh _) (baseWidth_bound h hh _ ht) 1 0 0 h
  have hb' := hb hstrip modelDirections pointField
  have hu := (KFCausalReciprocalSqueezeEnergy.common_domain ε hε h (-(Real.log w/2))
    (baseState ε a h hε ha hh _ ht)).mpr hb'
  have hs := state_transport ε a h hε ha hh _ ht
  simp only [he] at hs
  rw [hs]
  exact (commonEnergyDomain ε hε h modelDirections pointField).smul_mem _ hu

#print axioms quadratic_squeeze
#print axioms neutral_rescaling
#print axioms profile_squeeze
#print axioms baseWidth_positive
#print axioms baseWidth_bound
#print axioms state_transport
#print axioms state_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianDomain
