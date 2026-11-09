/- The weighted matter tilt may be negative, but its negative part has a
uniform bound relative to the weighted potential. No false sign is assumed. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterTiltControl
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterCoercivity

theorem tilted_exponential_lower (x : ℝ) : Real.exp x-1 ≤ x*Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at h
  nlinarith only [h]

theorem weightedTilt_lower (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (z : Phase) :
    weightedMean m g κ C z-mean (fun θ => potential m g κ (rotate θ z)) ≤
      weightedTilt m g κ C z := by
  have hp := potential_continuous m g κ z
  have hs := shear_continuous z
  have h := mean_mono
    (fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C)-potential m g κ (rotate θ z))
    (fun θ => potential m g κ (rotate θ z)*(shear (rotate θ z)/C)*Real.exp (shear (rotate θ z)/C))
    (by fun_prop) (by fun_prop) (fun θ => by
      have hh := mul_le_mul_of_nonneg_left (tilted_exponential_lower (shear (rotate θ z)/C))
        (hκ.trans (potential_ge_vacuum m g κ hm hg (rotate θ z)))
      nlinarith only [hh])
  rw [mean_sub _ _ (by fun_prop) hp] at h
  exact h

theorem exists_uniform_tilt_control :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ (m g κ C : ℝ), 0 ≤ m → 0 ≤ g → 0 ≤ κ →
      ∀ z : Phase, -N*weightedMean m g κ C z ≤
        weightedMean m g κ C z+weightedTilt m g κ C z := by
  obtain ⟨c,hc,_,hbound⟩ := exists_weighted_coercivity
  refine ⟨1/c,by positivity,?_⟩
  intro m g κ C hm hg hκ z
  have hM : mean (fun θ => potential m g κ (rotate θ z)) ≤ weightedMean m g κ C z/c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hbound m g κ C hm hg hκ z
  have hT := weightedTilt_lower m g κ C hm hg hκ z
  have hF := hκ.trans (weightedMean_lower m g κ C hm hg hκ z)
  have he : weightedMean m g κ C z/c = (1/c)*weightedMean m g κ C z := by ring
  rw [he] at hM
  nlinarith only [hM,hT,hF]

#print axioms tilted_exponential_lower
#print axioms weightedTilt_lower
#print axioms exists_uniform_tilt_control

end
end UnifiedTheory.Audit.KFCausalClassicalMatterTiltControl

