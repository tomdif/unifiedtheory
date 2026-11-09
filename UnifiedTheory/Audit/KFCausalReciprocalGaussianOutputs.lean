/- Identify the constructed growing-factor outputs with the actual
complex-shifted reciprocal Gaussians, including clock-momentum outputs. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum
import UnifiedTheory.Audit.KFCausalReciprocalGaussianCoordinates
import UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianOutputs
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalReciprocalSqueezeFlow
open KFCausalReciprocalSqueezeTransport
open KFCausalReciprocalSqueezeEnergy (degree factorScale)
open KFCausalReciprocalGaussianDomain
open KFCausalReciprocalGaussianMomentum (output momentumOutput)
open KFCausalReciprocalGaussianCoordinates (exponent)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalClockResponseTransport (weakSlope)

private theorem isotropic_exponent (α β : ℝ) (r : ℂ) (q : Transverse) :
    KFCausalRelativeGaussianDifferential.exponent α β 0 r q =
      -(α:ℂ)*r^2*(KFCausalQuarticChargeProfiles.chargedRadius q:ℂ)-
        (β:ℂ)*((q 4:ℂ)+2*(r-1)*((q 2+q 3:ℝ):ℂ))^2 := by
  simp only [KFCausalRelativeGaussianDifferential.exponent,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_sub,Fin.sum_univ_succ]
  change -((α:ℂ)*(r*(q 0:ℂ))^2+((α:ℂ)*(r*(q 1:ℂ))^2+
    ((α:ℂ)*(r*(q 2:ℂ))^2+((α:ℂ)*(r*(q 3:ℂ))^2+
      ((β:ℂ)*((q 4:ℂ)+2*(r-1)*((q 2:ℂ)+(q 3:ℂ)))^2+0))))) = _
  simp only [KFCausalQuarticChargeProfiles.chargedRadius,Complex.ofReal_add,Complex.ofReal_pow]
  ring

theorem exponent_squeeze (α β t : ℝ) (r : ℂ) (q : Transverse) :
    KFCausalRelativeGaussianDifferential.exponent α (β*Real.exp (-2*t)) 0 r (squeeze t q) =
      exponent α β (Real.exp (2*t)) r q := by
  rw [isotropic_exponent,quadratic_squeeze]
  have hm : squeeze t q 2+squeeze t q 3 = Real.exp t*(q 2+q 3) := by
    dsimp [squeeze,diagonal,offDiagonal]
    ring
  have hn : squeeze t q 4 = Real.exp t*q 4 := rfl
  rw [hm,hn]
  have he : Real.exp (-2*t)*(Real.exp t)^2 = 1 := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    norm_num
  have hc : (Real.exp (-2*t):ℂ)*(Real.exp t:ℂ)^2 = 1 := by exact_mod_cast he
  unfold exponent
  simp only [Complex.ofReal_mul,Complex.ofReal_add]
  linear_combination -(β:ℂ)*((q 4:ℂ)+2*(r-1)*((q 2:ℂ)+(q 3:ℂ)))^2*hc

theorem degree_index (n : Fin 3) : degree (index n) = (n.val:ℝ) := by
  fin_cases n <;> dsimp [degree,index] <;> norm_num

private theorem scalar_cancel (t : ℝ) (n : ℕ) :
    (Real.exp (-t/2):ℂ)*(Real.exp (-(n:ℝ)*t):ℂ)*(Real.exp (t/2):ℂ)*(Real.exp t:ℂ)^n = 1 := by
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_mul,
    ← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,← Real.exp_add]
  rw [show -t/2+-(n:ℝ)*t+t/2+(n:ℝ)*t=0 by ring,Real.exp_zero,Complex.ofReal_one]

def shifted (ε a h w : ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  (pointField x.2:ℂ)^n.val*clockAmplitude ε a 0 (-h/2) x.1*
    Complex.exp (exponent (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1) x.2)

theorem amplitude_squeeze (ε a h t : ℝ) (n : Fin 3) (x : Configuration) :
    (Real.exp (-t/2):ℂ)*factorScale (-t) (index n)*(Real.exp (t/2):ℂ)*
      KFCausalGaussianResponseDensities.amplitude ε a (groundWidth h)
        (neutralWidth h*Real.exp (-2*t)) 0 (-h/2) 0 1 pointField n (x.1,squeeze t x.2) =
      shifted ε a h (Real.exp (2*t)) n x := by
  simp only [KFCausalGaussianResponseDensities.amplitude,KFCausalRelativeGaussianDifferential.profile,
    one_mul,exponent_squeeze,squeeze_field,Complex.ofReal_mul,mul_pow,
    factorScale,degree_index]
  rw [show (n.val:ℝ)*(-t)=-(n.val:ℝ)*t by ring]
  calc
    _ = ((Real.exp (-t/2):ℂ)*(Real.exp (-(n.val:ℝ)*t):ℂ)*(Real.exp (t/2):ℂ)*
      (Real.exp t:ℂ)^n.val)*shifted ε a h (Real.exp (2*t)) n x := by unfold shifted; ring
    _ = _ := by rw [scalar_cancel,one_mul]

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "b" => (Real.exp (-t/2):ℂ)

theorem output_coe (n : Fin 3) :
    output ε a h w hε ha hh hw hb (index n) =ᵐ[volume] shifted ε a h w n := by
  let f := KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hbw
    1 0 0 h hb modelDirections pointField (index n)
  filter_upwards [Lp.coeFn_smul b (factorScale (-t) (index n) • transport (-t) f),
    Lp.coeFn_smul (factorScale (-t) (index n)) (transport (-t) f),transport_coe (-t) f,
    (squeezeFlow_quasiMeasurePreserving (-t)).ae
      (KFCausalSourcedResponseFactorBridge.input_factor_density ε a α β hε ha hα hβ hbw
        1 0 0 h hb modelDirections pointField n)] with x hc hd hu hf
  change (b • (factorScale (-t) (index n) • transport (-t) f)) x = _
  rw [hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hd]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hu]
  change f (squeezeFlow (-t) x) = _ at hf
  rw [hf]
  simp only [squeezeFlow_apply,neg_neg,baseWidth]
  have he : Real.exp (2*t) = w := by
    rw [show 2*t=Real.log w by ring,Real.exp_log (by linarith)]
  have hs := amplitude_squeeze ε a h t n x
  rw [he] at hs
  convert hs using 1
  ring

theorem momentumOutput_coe (n : Fin 3) :
    momentumOutput ε a h w hε ha hh hw hb (index n) =ᵐ[volume]
      fun x => (-Complex.I*(h:ℂ))*weakSlope ε a 0 (-h/2) x.1*shifted ε a h w n x := by
  let f := KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hbw
    1 0 0 h hb modelDirections pointField (index n)
  filter_upwards [Lp.coeFn_smul b (factorScale (-t) (index n) • transport (-t) f),
    Lp.coeFn_smul (factorScale (-t) (index n)) (transport (-t) f),transport_coe (-t) f,
    (squeezeFlow_quasiMeasurePreserving (-t)).ae
      (KFCausalSourcedResponseFactorBridge.momentum_factor_density ε a α β hε ha hα hβ hbw
        1 0 0 h hh hb modelDirections pointField n)] with x hc hd hu hf
  change (b • (factorScale (-t) (index n) • transport (-t) f)) x = _
  rw [hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hd]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hu]
  change f (squeezeFlow (-t) x) = _ at hf
  rw [hf]
  simp only [KFCausalGaussianResponseDensities.momentum,squeezeFlow_apply,neg_neg,baseWidth]
  have he : Real.exp (2*t) = w := by
    rw [show 2*t=Real.log w by ring,Real.exp_log (by linarith)]
  have hs := amplitude_squeeze ε a h t n x
  rw [he] at hs
  linear_combination (-Complex.I*(h:ℂ))*weakSlope ε a 0 (-h/2) x.1*hs

#print axioms exponent_squeeze
#print axioms degree_index
#print axioms amplitude_squeeze
#print axioms output_coe
#print axioms momentumOutput_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianOutputs
