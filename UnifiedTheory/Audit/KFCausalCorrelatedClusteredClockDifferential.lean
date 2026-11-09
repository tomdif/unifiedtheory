/- Differentiate the actual physical clustered input in the clock
direction. Transverse reciprocal widths are retained exactly. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumAmplitudes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockDifferential
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredClockVectors (profile profile_sum)
open KFCausalReciprocalNeutralSliceIntegrability (factor)
open KFCausalCorrelatedClusteredInputProfiles (inputAmplitude amplitudes)
open KFCausalCorrelatedClusteredMomentumAmplitudes (input_derivative amplitude_differential)
open KFCausalClockFloorPureClockDerivative (differential rate)
open KFCausalClockFloorFlow (clock)
open KFCausalCoherentLongitudinalDomain (clockSlope)
open KFCausalCanonicalClockDerivative (clockDerivative)

theorem factor_differentiable (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) :
    Differentiable ℝ (factor α β w 1 b P 0) := by
  unfold KFCausalReciprocalNeutralSliceIntegrability.factor
  simp only [pow_zero,one_mul,KFCausalRelativeGaussianDifferential.position,ite_true,
    sub_self,mul_zero,zero_mul,add_zero,KFCausalNeutralExponentialProfiles.exponentialProfile,one_mul]
  have h4 : Differentiable ℝ (fun q : Transverse => (q 4:ℂ)) :=
    Complex.ofRealCLM.differentiable.comp (by fun_prop)
  have hp : Differentiable ℝ (fun q : Transverse => P.eval (q 4:ℂ)) :=
    (P.differentiable.restrictScalars ℝ).comp h4
  have hqr : Differentiable ℝ (KFCausalReciprocalGaussianStates.quadratic w) := by
    unfold KFCausalReciprocalGaussianStates.quadratic
      KFCausalQuarticChargeProfiles.chargedRadius KFCausalChargedPairCoordinates.pairPolynomial
    fun_prop
  have hq : Differentiable ℝ (fun q => (KFCausalReciprocalGaussianStates.quadratic w q:ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hqr
  have he : Differentiable ℝ (fun q => Complex.exp (KFCausalReciprocalGaussianCoordinates.exponent α β w 1 q)) := by
    simpa only [KFCausalReciprocalGaussianCoordinates.exponent,one_pow,mul_one,sub_self,
      mul_zero,zero_mul,add_zero] using ((hq.const_mul (-(α:ℂ))).sub ((h4.pow 2).const_mul (β:ℂ))).cexp
  exact he.mul ((h4.const_mul b).cexp.mul hp)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β δ : ℝ)

theorem profile_differentiable (hc : ∀ i, Differentiable ℝ (fun s => c s i)) :
    Differentiable ℝ (profile f c α β δ) := by
  have he : profile f c α β δ = fun x => ∑ j, c x.1 (index f j).1*(coefficients f δ j*
      factor α β (widths f δ j) 1 (sources f j) (polynomials f j) 0 x.2) := funext (profile_sum f c α β δ)
  rw [he]
  apply Differentiable.fun_sum
  intro j _
  exact ((hc (index f j).1).comp differentiable_fst).mul
    (((factor_differentiable α β (widths f δ j) (sources f j) (polynomials f j)).comp differentiable_snd).const_mul _)

theorem profile_clock_derivative (d : ℝ → Fin m → ℂ)
    (hd : ∀ s i, HasDerivAt (fun t => c t i) (d s i) s) (x : Configuration) :
    clockDerivative (profile f c α β δ) x = profile f d α β δ x := by
  have hd' : HasDerivAt (fun s => profile f c α β δ (s,x.2)) (profile f d α β δ x) x.1 := by
    simp only [profile_sum]
    exact HasDerivAt.fun_sum (fun j _ => (hd x.1 (index f j).1).mul_const _)
  have hs := profile_differentiable f c α β δ (fun i s => (hd s i).differentiableAt)
  have hf := (hs x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  exact hf.unique hd'

variable (ε : ℝ) (a p : Fin m → ℝ) (hε : 0 < ε)

include hε in
theorem input_differential (x : Configuration) :
    differential ε (profile f (amplitudes ε a p) α β δ) x =
      profile f (KFCausalCorrelatedClusteredMomentumAmplitudes.amplitudes ε a p) α β δ x := by
  let d := fun s i => ((clockSlope ε (a i) s:ℂ)+(p i:ℂ)*Complex.I)*inputAmplitude ε (a i) (p i) s
  unfold differential
  rw [profile_clock_derivative f (amplitudes ε a p) α β δ d
    (fun s i => input_derivative ε (a i) (p i) s hε)]
  simp only [profile_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he := amplitude_differential ε (a (index f j).1) (p (index f j).1) x.1 hε
  dsimp only [d,amplitudes,KFCausalCorrelatedClusteredMomentumAmplitudes.amplitudes]
  rw [← he]
  ring

#print axioms factor_differentiable
#print axioms profile_differentiable
#print axioms profile_clock_derivative
#print axioms input_differential
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockDifferential
