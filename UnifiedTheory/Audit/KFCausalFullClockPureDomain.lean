/- The full clock multiplication of a sourced Gaussian remains in the
pure-clock domain. Its extra derivative is the bounded clock response. -/
import UnifiedTheory.Audit.KFCausalGaussianClockSquare
import UnifiedTheory.Audit.KFCausalOriginalPureClockOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFullClockPureDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier)
open KFCausalClockFloorCoherentMoments (sourcedPacket)
open KFCausalClockFloorInvariantTrial (clockFunction)
open KFCausalGaussianClockSquare (fullClockFunction output)
open KFCausalClockFloorSourcedClockMomentum (state profileState_coe state_coe)
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalPureClockOutputMultipliers (boundedPart boundedPart_coe coefficient)
open KFCausalShiftedClockMomentOperator (momentOperator momentOperator_coe)
open KFCausalClockFloorMomentumResponse (responseOperator responseOperator_coe)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
local notation "F" => physicalProfile C p α β b (clockFunction ε a)
local notation "G" => physicalProfile C p α β b (fullClockFunction ε a)
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "U" => output ε a α β hε ha hα hβ hw C p b
local notation "Uhalf" => output ε (a/2) α β hε (by positivity) hα hβ hw C p b

theorem profile_factor (x : Configuration) : G x = ((Real.exp x.1+ε:ℝ):ℂ)*F x := by
  unfold physicalProfile clockMultiplier fullClockFunction
  ring

theorem profile_smooth : ContDiff ℝ 1 G := by
  rw [funext (profile_factor ε a α β C p b)]
  exact ((Complex.ofRealCLM.contDiff.comp ((contDiff_fst.exp).add contDiff_const)).mul
    (KFCausalCoherentLongitudinalDomain.profile_smooth ε a C p α β b))

include hε in
theorem profile_differential (x : Configuration) :
    differential ε G x = coefficient ε p x.1*G x-
      2*(a:ℂ)*(KFCausalRegularizedLongitudinalChart.chart ε x.1:ℂ)*G x+
      ((KFCausalClockFloorCanonicalDefect.response ε x.1:ℝ):ℂ)*F x := by
  have hs := KFCausalCoherentLongitudinalDomain.profile_smooth ε a C p α β b
  have hF := (hs.differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => F (s,x.2)) (clockDerivative F x) x.1 at hF
  have hd := (((Real.hasDerivAt_exp x.1).add_const ε).ofReal_comp).mul hF
  have hp := ((profile_smooth ε a α β C p b).differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => G (s,x.2)) (clockDerivative G x) x.1 at hp
  have he : clockDerivative G x = (Real.exp x.1:ℂ)*F x+
      ((Real.exp x.1+ε:ℝ):ℂ)*clockDerivative F x := by
    apply hp.unique
    simpa only [profile_factor] using hd
  have hb := KFCausalOriginalPureClockOutput.profile_differential ε a hε C p α β b x
  unfold differential at hb ⊢
  rw [he,profile_factor]
  unfold KFCausalClockFloorCanonicalDefect.response
  unfold KFCausalClockFloorFlow.clock at hb ⊢
  push_cast at hb ⊢
  simp only [← Complex.ofReal_exp] at hb ⊢
  have hc : (Real.exp x.1:ℂ)+(ε:ℂ) ≠ 0 := by
    exact_mod_cast (show Real.exp x.1+ε ≠ 0 by positivity)
  linear_combination (norm := skip) ((Real.exp x.1:ℂ)+(ε:ℂ))*hb
  field_simp [hc]
  ring

def preOutput : Hilbert := boundedPart ε hε p U-
  (2*(a:ℂ)) • momentOperator ε a 0 ha Uhalf+responseOperator ε hε S

theorem output_coe : U =ᵐ[volume] G :=
  profileState_coe α β hα hβ hw C p b (fullClockFunction ε a)
    (KFCausalGaussianClockSquare.fullClockFunction_memLp ε a hε ha)

theorem preOutput_coe : preOutput ε a α β hε ha hα hβ hw C p b =ᵐ[volume] differential ε G := by
  filter_upwards [Lp.coeFn_add (boundedPart ε hε p U-(2*(a:ℂ)) • momentOperator ε a 0 ha Uhalf)
      (responseOperator ε hε S),
    Lp.coeFn_sub (boundedPart ε hε p U) ((2*(a:ℂ)) • momentOperator ε a 0 ha Uhalf),
    Lp.coeFn_smul (2*(a:ℂ)) (momentOperator ε a 0 ha Uhalf),boundedPart_coe ε hε p U,
    momentOperator_coe ε a 0 ha Uhalf,responseOperator_coe ε hε S,
    output_coe ε a α β hε ha hα hβ hw C p b,
    output_coe ε (a/2) α β hε (by positivity) hα hβ hw C p b,
    state_coe ε a α β hε ha hα hβ hw C p b] with x hadd hsub hsm hb' hm hresp hU hUhalf hS
  have hhalf : G x = KFCausalClockFloorFullGaussian.clockFactor (a/2)
      (KFCausalRegularizedLongitudinalChart.chart ε x.1:ℂ)*
        physicalProfile C p α β b (fullClockFunction ε (a/2)) x := by
    rw [profile_factor,profile_factor,KFCausalOriginalPureClockOutput.profile_half ε a hε C p α β b]
    ring
  change (boundedPart ε hε p U-(2*(a:ℂ)) • momentOperator ε a 0 ha Uhalf+responseOperator ε hε S) x = _
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hadd hsub hsm
  rw [hadd,hsub,hsm,hb',hm,hresp,hU,hUhalf,hS,profile_differential ε a α β hε C p b x,hhalf]
  simp only [KFCausalShiftedClockMomentOperator.momentMultiplier,KFCausalClockFloorRelativeShift.argument,
    Complex.ofReal_zero,zero_mul,add_zero]
  ring

include hε ha hα hβ hw in
theorem output_domain (h : ℝ) (hh : h ≠ 0) : U ∈ (pureMomentum ε hε h).domain := by
  have hf : MemLp G 2 volume := (Lp.memLp U).ae_eq (output_coe ε a α β hε ha hα hβ hw C p b)
  have hd : MemLp (differential ε G) 2 volume :=
    (Lp.memLp (preOutput ε a α β hε ha hα hβ hw C p b)).ae_eq
      (preOutput_coe ε a α β hε ha hα hβ hw C p b)
  have he : U = hf.toLp G := Lp.ext ((output_coe ε a α β hε ha hα hβ hw C p b).trans hf.coeFn_toLp.symm)
  rw [he]
  exact KFCausalClockFloorPureClockDifferential.differential_domain ε hε h hh G hf hd
    ((profile_smooth ε a α β C p b).differentiable (by norm_num))

#print axioms profile_factor
#print axioms profile_smooth
#print axioms profile_differential
#print axioms output_coe
#print axioms preOutput_coe
#print axioms output_domain
end
end UnifiedTheory.Audit.KFCausalFullClockPureDomain
