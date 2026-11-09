/- Reciprocal squeeze of the actual polynomial momentum matter spectral endpoint.
Both field scaling factors cancel in its physical representative, and
the existing original second output is exactly inverseL of this vector. -/
import UnifiedTheory.Audit.KFCausalPolynomialMomentumMatterSpectral
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumSecondFactors
import UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumMatterSpectral
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalSqueezeTransport
open KFCausalReciprocalSqueezeFlow (squeeze diagonal offDiagonal)
open KFCausalReciprocalSqueezeEnergy (factorScale)
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile profile_squeeze)
open KFCausalCoherentMatterSpectralProfile (multiplier)
open KFCausalMixedFieldPhysicalProfile (field)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex field_squeeze factor_cancel)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
local notation "τ" => Real.log w/2
local notation "hτ" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h τ
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh τ
local notation "hwidth" => baseWidth_bound h hh τ hτ
local notation "d" => neutralSource ((Real.exp (-τ):ℂ)*b)
local notation "Q" => rescaledPolynomial τ P
local notation "c" => (Real.exp (-τ/2):ℂ)

def spectral (j : Fin 2) : Hilbert := c • (factorScale (-τ) (matterIndex j)^2 • transport (-τ)
  (KFCausalPolynomialMomentumMatterSpectral.spectral ε a α β hε ha hα hβ hwidth h hb C p d 4 Q j))

theorem second_eq (j : Fin 2) :
    KFCausalReciprocalNeutralMomentumSecondFactors.second ε a h w hε ha hh hw hb C p b P (matterIndex j) =
      inverseL ε hε (spectral ε a h w hε ha hh hw hb C p b P j) := by
  simp only [KFCausalReciprocalNeutralMomentumSecondFactors.second,spectral,KFCausalPolynomialMomentumMatterSpectral.second_eq,map_smul,
    KFCausalReciprocalSqueezeClockCommutation.inverse_half_commutes]

theorem spectral_coe (j : Fin 2) :
    spectral ε a h w hε ha hh hw hb C p b P j =ᵐ[volume] fun x =>
      multiplier ε h j x*((1/2:ℂ)*clockSlope ε a (2*h) p x*
        shiftedProfile ε a α (neutralWidth h) (2*h) w C p b P x) := by
  let v := KFCausalPolynomialMomentumMatterSpectral.spectral ε a α β hε ha hα hβ hwidth h hb C p d 4 Q j
  let k := factorScale (-τ) (matterIndex j)^2
  filter_upwards [Lp.coeFn_smul c (k • transport (-τ) v),Lp.coeFn_smul k (transport (-τ) v),
    transport_coe (-τ) v,(squeezeFlow_quasiMeasurePreserving (-τ)).ae
      (KFCausalPolynomialMomentumMatterSpectral.spectral_coe ε a α β hε ha hα hβ hwidth h hb C p d 4 hh Q j)]
    with x hc hk ht hv
  change v (squeezeFlow (-τ) x) = _ at hv
  change (c • (k • transport (-τ) v) : Hilbert) x = _
  rw [hc,Pi.smul_apply,smul_eq_mul,hk,Pi.smul_apply,smul_eq_mul,ht,hv]
  simp only [squeezeFlow_apply,neg_neg,baseWidth,multiplier,field_squeeze,mul_pow,clockSlope]
  rw [profile_squeeze]
  have he : Real.exp (2*τ) = w := by
    rw [show 2*τ=Real.log w by ring,Real.exp_log (by linarith)]
  rw [he]
  have hc' : c*(Real.exp (τ/2):ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show -τ/2+τ/2=0 by ring,Real.exp_zero,Complex.ofReal_one]
  have hk' : k*(Real.exp τ:ℂ)^degree j = 1 := factor_cancel τ j
  calc
    _ = (c*(Real.exp (τ/2):ℂ))*(k*(Real.exp τ:ℂ)^degree j)*
        (field (KFCausalClockFloorRelativeShift.scale ε (-h/2) x.1) x.2^degree j)*
        ((1/2:ℂ)*clockSlope ε a (2*h) p x*
          shiftedProfile ε a α (neutralWidth h) (2*h) w C p b P x) := by unfold clockSlope; ring
    _ = _ := by rw [hc',hk',one_mul,one_mul]; rfl

#print axioms second_eq
#print axioms spectral_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumMatterSpectral
