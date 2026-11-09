/- Reciprocal squeeze of the actual polynomial matter spectral endpoint.
Both field scaling factors cancel in its physical representative, and
the existing original second output is exactly inverseL of this vector. -/
import UnifiedTheory.Audit.KFCausalPolynomialMatterSpectral
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSecondFactors
import UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSpectral
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

def matterIndex (j : Fin 2) : Fin 8 := ⟨j.val+5,by omega⟩

theorem field_squeeze (t : ℝ) (r : ℂ) (q : Transverse) :
    field r (squeeze t q) = (Real.exp t:ℂ)*field r q := by
  simp only [field,squeeze,Matrix.cons_val]
  unfold diagonal offDiagonal
  push_cast
  ring

theorem factor_cancel (t : ℝ) (j : Fin 2) :
    factorScale (-t) (matterIndex j)^2*(Real.exp t:ℂ)^degree j = 1 := by
  have he : (Real.exp (-t):ℂ)*(Real.exp t:ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  have hd : (Real.exp (2*(-t)):ℂ) = (Real.exp (-t):ℂ)^2 := by
    rw [show 2*(-t)=(-t)+(-t) by ring,Real.exp_add,Complex.ofReal_mul,pow_two]
  fin_cases j
  · change (Real.exp (1*(-t)):ℂ)^2*(Real.exp t:ℂ)^2 = 1
    rw [one_mul,← mul_pow,he,one_pow]
  · change (Real.exp (2*(-t)):ℂ)^2*(Real.exp t:ℂ)^4 = 1
    rw [hd,← pow_mul,show (2:ℕ)*2=4 by norm_num,← mul_pow,he,one_pow]

section
variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5) (P : Polynomial ℂ)

theorem polynomial_second_eq (j : Fin 2) :
    KFCausalPolynomialSecondFactors.second ε a α β hε ha hα hβ hw h hb C p b i P (matterIndex j) =
      inverseL ε hε (KFCausalPolynomialMatterSpectral.spectral ε a α β hε ha hα hβ hw h hb C p b i P j) := by
  have he := KFCausalPolynomialMatterSpectral.second_eq ε a α β hε ha hα hβ hw h hb C p b i P j
  convert he using 1
  fin_cases j <;> rfl

end
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
  (KFCausalPolynomialMatterSpectral.spectral ε a α β hε ha hα hβ hwidth h hb C p d 4 Q j))

theorem second_eq (j : Fin 2) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b P (matterIndex j) =
      inverseL ε hε (spectral ε a h w hε ha hh hw hb C p b P j) := by
  simp only [KFCausalReciprocalNeutralSecondFactors.second,spectral,polynomial_second_eq,map_smul,
    KFCausalReciprocalSqueezeClockCommutation.inverse_half_commutes]

theorem spectral_coe (j : Fin 2) :
    spectral ε a h w hε ha hh hw hb C p b P j =ᵐ[volume] fun x =>
      multiplier ε h j x*shiftedProfile ε a α (neutralWidth h) (2*h) w C p b P x := by
  let v := KFCausalPolynomialMatterSpectral.spectral ε a α β hε ha hα hβ hwidth h hb C p d 4 Q j
  let k := factorScale (-τ) (matterIndex j)^2
  filter_upwards [Lp.coeFn_smul c (k • transport (-τ) v),Lp.coeFn_smul k (transport (-τ) v),
    transport_coe (-τ) v,(squeezeFlow_quasiMeasurePreserving (-τ)).ae
      (KFCausalPolynomialMatterSpectral.spectral_coe ε a α β hε ha hα hβ hwidth h hb C p d 4 Q j)]
    with x hc hk ht hv
  change v (squeezeFlow (-τ) x) = _ at hv
  change (c • (k • transport (-τ) v) : Hilbert) x = _
  rw [hc,Pi.smul_apply,smul_eq_mul,hk,Pi.smul_apply,smul_eq_mul,ht,hv]
  simp only [squeezeFlow_apply,neg_neg,baseWidth,multiplier,field_squeeze,mul_pow]
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
        shiftedProfile ε a α (neutralWidth h) (2*h) w C p b P x := by ring
    _ = _ := by rw [hc',hk',one_mul,one_mul]

#print axioms field_squeeze
#print axioms factor_cancel
#print axioms polynomial_second_eq
#print axioms second_eq
#print axioms spectral_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSpectral
