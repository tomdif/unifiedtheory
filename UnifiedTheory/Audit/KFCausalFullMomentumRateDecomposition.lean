/- Exact separation of the full signed energy-form density into the
eight unscaled factor rates and the existing physical energy weights.
All integrals are justified by the derived continuous output curves. -/
import UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing (pairingDensity)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight energyWeight_norm_square)

def rate (h : ℝ) (g k : Fin 8 → ℝ → Hilbert) (i : Fin 8) : ℝ :=
  ∫ θ, (-2/h)*(inner ℂ (g i θ) (k i θ)).im ∂angleMeasure

theorem rate_integrable (h : ℝ) (g k : ℝ → Hilbert) (hg : Continuous g) (hk : Continuous k) :
    Integrable (fun θ => (-2/h)*(inner ℂ (g θ) (k θ)).im) angleMeasure :=
  (continuous_angle_memLp _ (continuous_const.mul (Complex.continuous_im.comp (hg.inner hk)))).integrable (by norm_num)

theorem weighted_inner_im (c : ℂ) (f g : Hilbert) :
    (inner ℂ (c • f) (c • g)).im = ‖c‖^2*(inner ℂ f g).im := by
  rw [inner_smul_left,inner_smul_right,← mul_assoc,Complex.conj_mul',← Complex.ofReal_pow]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

theorem density_decomposition (mass2 quartic vacuum t h : ℝ) (g k : Fin 8 → ℝ → Hilbert) (θ : ℝ) :
    (-2/h)*(pairingDensity mass2 quartic vacuum t g k θ).im =
      ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*((-2/h)*(inner ℂ (g i θ) (k i θ)).im) := by
  simp only [pairingDensity,Complex.im_sum,Finset.mul_sum,weighted_inner_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integral_decomposition (mass2 quartic vacuum t h : ℝ) (g k : Fin 8 → ℝ → Hilbert)
    (hg : ∀ i, Continuous (g i)) (hk : ∀ i, Continuous (k i)) :
    (∫ θ, (-2/h)*(pairingDensity mass2 quartic vacuum t g k θ).im ∂angleMeasure) =
      ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*rate h g k i := by
  simp_rw [density_decomposition]
  rw [integral_finset_sum Finset.univ (fun i _ => (rate_integrable h (g i) (k i) (hg i) (hk i)).const_mul _)]
  exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)

theorem physical_decomposition (mass2 quartic vacuum t h : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (g k : Fin 8 → ℝ → Hilbert) (hg : ∀ i, Continuous (g i)) (hk : ∀ i, Continuous (k i)) :
    (∫ θ, (-2/h)*(pairingDensity mass2 quartic vacuum t g k θ).im ∂angleMeasure) =
      (rate h g k 0+rate h g k 1+rate h g k 2)/2+
        Real.exp (2*t)*((rate h g k 3+rate h g k 4)/2+
          mass2/2*rate h g k 5+quartic/4*rate h g k 6+vacuum*rate h g k 7) := by
  rw [integral_decomposition mass2 quartic vacuum t h g k hg hk]
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

#print axioms rate_integrable
#print axioms weighted_inner_im
#print axioms density_decomposition
#print axioms integral_decomposition
#print axioms physical_decomposition
end
end UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition
