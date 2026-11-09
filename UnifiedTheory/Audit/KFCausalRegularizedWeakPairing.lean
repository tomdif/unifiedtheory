/- Uniform weak time-regularity of the actual Yosida dynamics.
For every fixed form test vector the scalar pairing has a cutoff-independent
Lipschitz bound on each compact time interval. -/
import UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedWeakPairing
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics
open UnifiedTheory.Audit.KFCausalRegularizedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound

def weakSlope (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) (v : FormSpace ε hε hbar coupling 0) : ℂ :=
  (Complex.I*((1/hbar:ℝ):ℂ))*inner ℂ (smoothedLift ε hε hbar coupling a ha s t f)
    (referenceFormOperator ε hε hbar coupling t v)

theorem weak_pairing_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) (v : FormSpace ε hε hbar coupling 0) :
    HasDerivAt (fun z => inner ℂ (dynamics ε hε hbar coupling a ha s z f)
      (embedding ε hε hbar coupling 0 v)) (weakSlope ε hε hbar coupling a ha s t f v) t := by
  have hd := (dynamics_state_derivative ε hε hbar coupling a ha s t f).inner ℂ
    (hasDerivAt_const t (embedding ε hε hbar coupling 0 v))
  rw [weakSlope,smoothed_weak_pairing]
  simpa only [inner_zero_right,zero_add,generator,ContinuousLinearMap.smul_apply,
    inner_smul_left,map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal] using hd

def pairingBound (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w v : FormSpace ε hε hbar coupling 0) : ℝ :=
  |1/hbar| * windowRadius ε hε hbar coupling s T w * (1+Real.exp (2*T)) * ‖v‖

theorem pairingBound_nonneg (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w v : FormSpace ε hε hbar coupling 0) : 0 ≤ pairingBound ε hε hbar coupling s T w v := by
  unfold pairingBound windowRadius
  positivity

theorem weakSlope_window_bound (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) (w v : FormSpace ε hε hbar coupling 0) :
    ‖weakSlope ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w) v‖ ≤
      pairingBound ε hε hbar coupling s T w v := by
  have hf : ‖referenceFormOperator ε hε hbar coupling t v‖ ≤ (1+Real.exp (2*T))*‖v‖ := by
    apply (ContinuousLinearMap.le_opNorm _ v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (referenceForm_norm_le ε hε hbar coupling t).trans
    exact add_le_add le_rfl (Real.exp_le_exp.mpr (by linarith [(abs_le.mp ht).2]))
  have hi := (norm_inner_le_norm (𝕜 := ℂ)
    (smoothedLift ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w))
    (referenceFormOperator ε hε hbar coupling t v)).trans
    (mul_le_mul (smoothed_window_norm ε hε hbar coupling a ha s T t hT ht w) hf
      (norm_nonneg _) (Real.sqrt_nonneg _))
  rw [weakSlope,norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  unfold pairingBound
  have hh := mul_le_mul_of_nonneg_left hi (abs_nonneg (1/hbar))
  simpa only [mul_assoc] using hh

theorem weak_pairing_lipschitz (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s T x y : ℝ) (hT : 0 ≤ T) (hx : |x| ≤ T) (hy : |y| ≤ T)
    (w v : FormSpace ε hε hbar coupling 0) :
    ‖inner ℂ (dynamics ε hε hbar coupling a ha s y (embedding ε hε hbar coupling 0 w))
        (embedding ε hε hbar coupling 0 v) -
      inner ℂ (dynamics ε hε hbar coupling a ha s x (embedding ε hε hbar coupling 0 w))
        (embedding ε hε hbar coupling 0 v)‖ ≤ pairingBound ε hε hbar coupling s T w v * |y-x| := by
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.Icc (-T) T) =>
      (weak_pairing_derivative ε hε hbar coupling a ha s z (embedding ε hε hbar coupling 0 w) v).hasDerivWithinAt)
    (fun z hz => weakSlope_window_bound ε hε hbar coupling a ha s T z hT (abs_le.mpr hz) w v)
    (convex_Icc (-T) T) (abs_le.mp hx) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using hd

#print axioms weak_pairing_derivative
#print axioms weakSlope_window_bound
#print axioms weak_pairing_lipschitz

end
end UnifiedTheory.Audit.KFCausalRegularizedWeakPairing
