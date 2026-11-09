/- An explicit output for pure-clock momentum on the original sourced
Gaussian. The original clock density factor is retained. The derivative
is proved square integrable using bounded multipliers and half-width inputs. -/
import UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
import UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalOriginalPureClockOutput
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile physicalProfile_memLp clockMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative (rate differential)
open UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain (clockSlope profile_clock_derivative profile_smooth)
open UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator (momentOperator momentOperator_coe momentMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (C : ℂ) (p α β : ℝ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)

def profileState : Hilbert :=
  (physicalProfile_memLp C p α β hα hβ hw b _ (clockFunction_memLp ε a hε ha)).toLp
    (physicalProfile C p α β b (clockFunction ε a))

theorem profileState_coe : profileState ε a hε ha C p α β hα hβ hw b =ᵐ[volume]
    physicalProfile C p α β b (clockFunction ε a) := MemLp.coeFn_toLp _

include hε in
theorem profile_half (x : Configuration) :
    physicalProfile C p α β b (clockFunction ε a) x =
      clockFactor (a/2) (chart ε x.1:ℂ)*physicalProfile C p α β b (clockFunction ε (a/2)) x := by
  simp only [physicalProfile,clockMultiplier]
  rw [KFCausalGaussianClockMoment.clockFunction_half ε a x.1 hε]
  ring

include hε in
theorem profile_differential (x : Configuration) :
    differential ε (physicalProfile C p α β b (clockFunction ε a)) x =
      (coefficient ε p x.1-2*(a:ℂ)*(chart ε x.1:ℂ))*
        physicalProfile C p α β b (clockFunction ε a) x := by
  unfold differential
  rw [profile_clock_derivative ε a hε C p α β b x]
  unfold coefficient rate clock clockSlope
  simp only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_one]
  have hc : (Real.exp x.1:ℂ)+(ε:ℂ) ≠ 0 := by
    exact_mod_cast (show Real.exp x.1+ε ≠ 0 by positivity)
  field_simp [hc]
  ring

theorem moment_coe : momentOperator ε a 0 ha (profileState ε (a/2) hε (by positivity) C p α β hα hβ hw b)
    =ᵐ[volume] fun x => (chart ε x.1:ℂ)*physicalProfile C p α β b (clockFunction ε a) x := by
  filter_upwards [momentOperator_coe ε a 0 ha (profileState ε (a/2) hε (by positivity) C p α β hα hβ hw b),
    profileState_coe ε (a/2) hε (by positivity) C p α β hα hβ hw b] with x hm hf
  rw [hm,hf,profile_half ε a hε C p α β b x]
  simp only [momentMultiplier,argument,Complex.ofReal_zero,zero_mul,add_zero,mul_assoc]

def preOutput : Hilbert :=
  boundedPart ε hε p (profileState ε a hε ha C p α β hα hβ hw b)-
    (2*(a:ℂ)) • momentOperator ε a 0 ha (profileState ε (a/2) hε (by positivity) C p α β hα hβ hw b)

theorem preOutput_coe : preOutput ε a hε ha C p α β hα hβ hw b =ᵐ[volume]
    differential ε (physicalProfile C p α β b (clockFunction ε a)) := by
  filter_upwards [Lp.coeFn_sub (boundedPart ε hε p (profileState ε a hε ha C p α β hα hβ hw b))
      ((2*(a:ℂ)) • momentOperator ε a 0 ha (profileState ε (a/2) hε (by positivity) C p α β hα hβ hw b)),
    Lp.coeFn_smul (2*(a:ℂ)) (momentOperator ε a 0 ha (profileState ε (a/2) hε (by positivity) C p α β hα hβ hw b)),
    boundedPart_coe ε hε p (profileState ε a hε ha C p α β hα hβ hw b),
    profileState_coe ε a hε ha C p α β hα hβ hw b,
    moment_coe ε a hε ha C p α β hα hβ hw b] with x hs hsm hb' hf hm
  dsimp only [preOutput]
  rw [hs]
  simp only [Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,hb',hf,hm]
  rw [profile_differential ε a hε C p α β b x]
  ring

theorem profile_graph (h : ℝ) (hh : h ≠ 0) :
    (profileState ε a hε ha C p α β hα hβ hw b,
      outputMap ε a h hε ha p (profileState ε a hε ha C p α β hα hβ hw b)
        (profileState ε (a/2) hε (by positivity) C p α β hα hβ hw b)) ∈
      (pureMomentum ε hε h).graph := by
  have hd : MemLp (differential ε (physicalProfile C p α β b (clockFunction ε a))) 2 volume :=
    (Lp.memLp (preOutput ε a hε ha C p α β hα hβ hw b)).ae_eq (preOutput_coe ε a hε ha C p α β hα hβ hw b)
  have he : preOutput ε a hε ha C p α β hα hβ hw b =
      hd.toLp (differential ε (physicalProfile C p α β b (clockFunction ε a))) :=
    Lp.ext ((preOutput_coe ε a hε ha C p α β hα hβ hw b).trans hd.coeFn_toLp.symm)
  change (_,(-Complex.I*(h:ℂ)) • preOutput ε a hε ha C p α β hα hβ hw b) ∈ _
  rw [he]
  exact KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh _ _ hd
    ((profile_smooth ε a C p α β b).differentiable (by norm_num))

#print axioms profileState_coe
#print axioms profile_half
#print axioms profile_differential
#print axioms moment_coe
#print axioms preOutput_coe
#print axioms profile_graph
end
end UnifiedTheory.Audit.KFCausalOriginalPureClockOutput
