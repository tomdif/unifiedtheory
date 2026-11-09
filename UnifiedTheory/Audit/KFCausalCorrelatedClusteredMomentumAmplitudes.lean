/- Actual clock-momentum coefficients. The inverse clock and density
correction are bounded; the remaining chart moment is absorbed by the
clock Gaussian. No derivative integrability is assumed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockVectors
import UnifiedTheory.Audit.KFCausalOriginalPureClockOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumAmplitudes
noncomputable section
open MeasureTheory
open KFCausalCorrelatedClusteredInputProfiles (inputAmplitude inputAmplitude_continuous inputAmplitude_memLp)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockFloorCoherentDerivative (clockMultiplier_memLp)
open KFCausalClockFloorInvariantTrial (clockFunction)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorPureClockDerivative (rate)
open KFCausalClockFloorPureClockCommonDomain (rate_bound)
open KFCausalPureClockOutputMultipliers (coefficient rate_continuous)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalCoherentLongitudinalDomain (clockSlope clockFunction_derivative)

theorem coefficient_continuous (ε p : ℝ) (hε : 0 < ε) : Continuous (coefficient ε p) := by
  have hi : Continuous (fun s => (clock ε s:ℂ)⁻¹) := by
    unfold clock
    fun_prop (disch := intro s; exact Complex.ofReal_ne_zero.mpr (by positivity))
  exact (continuous_const.mul hi).sub (rate_continuous ε hε)

theorem coefficient_bound (ε p : ℝ) (hε : 0 < ε) (s : ℝ) :
    ‖coefficient ε p s‖ ≤ ‖(p:ℂ)*Complex.I-1‖/ε+1/(8*ε) := by
  have hi : ‖(clock ε s:ℂ)⁻¹‖ ≤ 1/ε := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by unfold clock; positivity)]
    simpa only [one_div] using (inv_le_inv₀ (by unfold clock; positivity) hε).mpr
      (show ε ≤ clock ε s by unfold clock; linarith [Real.exp_pos s])
  have hr : ‖(rate ε s:ℂ)‖ ≤ 1/(8*ε) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using rate_bound ε hε s
  exact (norm_sub_le _ _).trans (by
    rw [norm_mul]
    have hm := mul_le_mul_of_nonneg_left hi (norm_nonneg ((p:ℂ)*Complex.I-1))
    simpa only [mul_one_div] using add_le_add hm hr)

def amplitude (ε a p s : ℝ) : ℂ :=
  (coefficient ε p s-2*(a:ℂ)*(chart ε s:ℂ))*inputAmplitude ε a p s

theorem amplitude_continuous (ε a p : ℝ) (hε : 0 < ε) : Continuous (amplitude ε a p) := by
  have ht : Continuous (fun s => (chart ε s:ℂ)) := by unfold chart; fun_prop
  exact ((coefficient_continuous ε p hε).sub (continuous_const.mul ht)).mul
    (inputAmplitude_continuous ε a p)

theorem amplitude_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (amplitude ε a p) 2 volume := by
  let B := ‖(p:ℂ)*Complex.I-1‖/ε+1/(8*ε)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : MemLp (fun s => coefficient ε p s*inputAmplitude ε a p s) 2 volume := by
    apply ((inputAmplitude_memLp ε a p hε ha).const_mul (B:ℂ)).of_le
      ((coefficient_continuous ε p hε).mul (inputAmplitude_continuous ε a p)).aestronglyMeasurable
    filter_upwards [] with s
    simp only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (coefficient_bound ε p hε s) (norm_nonneg (inputAmplitude ε a p s))
  have hm := clockMultiplier_memLp 1 p _ (KFCausalGaussianClockMoment.clockFunction_moment_memLp ε a hε ha)
  change MemLp (fun s : ℝ => 1*clockPhase p (s:ℂ)*((chart ε s:ℂ)*clockFunction ε a s)) 2 volume at hm
  have ht : MemLp (fun s => (chart ε s:ℂ)*inputAmplitude ε a p s) 2 volume := by
    convert hm using 1
    funext s
    unfold inputAmplitude
    ring
  convert hb.sub (ht.const_mul (2*(a:ℂ))) using 1
  funext s
  simp only [amplitude,Pi.sub_apply]
  ring

theorem input_derivative (ε a p s : ℝ) (hε : 0 < ε) :
    HasDerivAt (inputAmplitude ε a p)
      (((clockSlope ε a s:ℂ)+(p:ℂ)*Complex.I)*inputAmplitude ε a p s) s := by
  have hp := (((hasDerivAt_id s).ofReal_comp.const_mul ((p:ℂ)*Complex.I)).cexp).mul
    (clockFunction_derivative ε a s hε)
  convert hp using 1
  simp only [Complex.ofReal_one,mul_one,id_eq]
  unfold inputAmplitude clockPhase
  ring

theorem amplitude_differential (ε a p s : ℝ) (hε : 0 < ε) :
    ((clock ε s)⁻¹:ℂ)*(((clockSlope ε a s:ℂ)+(p:ℂ)*Complex.I)*inputAmplitude ε a p s)+
      (rate ε s:ℂ)*inputAmplitude ε a p s = amplitude ε a p s := by
  unfold amplitude coefficient rate clock clockSlope
  simp only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_one]
  have hc : (Real.exp s:ℂ)+(ε:ℂ) ≠ 0 := by
    exact_mod_cast (show Real.exp s+ε ≠ 0 by positivity)
  field_simp [hc]
  ring

def amplitudes {m : ℕ} (ε : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ := amplitude ε (a i) (p i) s

#print axioms coefficient_continuous
#print axioms coefficient_bound
#print axioms amplitude_continuous
#print axioms amplitude_memLp
#print axioms input_derivative
#print axioms amplitude_differential
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumAmplitudes
