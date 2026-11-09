/- Uniform weighted-average coercivity for an even power of an affine
trigonometric field, against any zero-mean shear of the model's harmonic degree. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterOverlap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterProfileCoercivity
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics
open UnifiedTheory.Audit.KFCausalClassicalMatterOverlap
open UnifiedTheory.Audit.KFCausalClassicalChargeMean

theorem exponential_dominates_positive_part (b : Fin 4 → ℝ) (hb : ‖b‖ = 1)
    (t θ : ℝ) (ht : 0 ≤ t) :
    max (second b θ) 0/5 ≤ Real.exp (t*second b θ) := by
  have hbound : second b θ ≤ 5 := by
    have h := (le_abs_self (second b θ)).trans (second_abs_bound b θ)
    simpa only [hb,mul_one] using h
  by_cases hs : 0 ≤ second b θ
  · rw [max_eq_left hs]
    exact (by linarith : second b θ/5 ≤ 1).trans (Real.one_le_exp (mul_nonneg ht hs))
  · rw [max_eq_right (le_of_not_ge hs),zero_div]
    exact (Real.exp_pos _).le

theorem normalized_mean_lower (k : ℕ) (a : Fin 3 → ℝ) (b : Fin 4 → ℝ)
    (hb : ‖b‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    overlap k (a,b)/5 ≤ mean (fun θ => first a θ^(2*k)*Real.exp (t*second b θ)) := by
  have h := mean_mono (fun θ => first a θ^(2*k)*(max (second b θ) 0/5))
    (fun θ => first a θ^(2*k)*Real.exp (t*second b θ))
    (by have ha := first_continuous a; have hb' := second_continuous b; fun_prop)
    (by have ha := first_continuous a; have hb' := second_continuous b; fun_prop)
    (fun θ => mul_le_mul_of_nonneg_left (exponential_dominates_positive_part b hb t θ ht)
      ((even_two_mul k).pow_nonneg _))
  rw [overlap_eq_mean]
  convert h using 1
  rw [div_eq_mul_inv,← mean_mul_const]
  congr 1
  funext θ
  ring

theorem power_mean_upper (k : ℕ) (a : Fin 3 → ℝ) :
    mean (fun θ => first a θ^(2*k)) ≤ 3^(2*k)*‖a‖^(2*k) := by
  have h := mean_mono (fun θ => first a θ^(2*k)) (fun _ => (3*‖a‖)^(2*k))
    ((first_continuous a).pow _) continuous_const (fun θ => by
      change first a θ^(2*k) ≤ (3*‖a‖)^(2*k)
      rw [← (even_two_mul k).pow_abs (first a θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (first_abs_bound a θ) _)
  simpa only [mean_const,mul_pow] using h

theorem weighted_power_smul (k : ℕ) (r : ℝ) (a : Fin 3 → ℝ) (f : ℝ → ℝ) :
    mean (fun θ => first (r • a) θ^(2*k)*f θ) =
      r^(2*k)*mean (fun θ => first a θ^(2*k)*f θ) := by
  simp_rw [first_smul,mul_pow]
  have he : (fun θ => r^(2*k)*first a θ^(2*k)*f θ) =
      fun θ => (first a θ^(2*k)*f θ)*r^(2*k) := by funext θ; ring
  rw [he,mean_mul_const,mul_comm]

theorem exists_power_coercivity (k : ℕ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (a : Fin 3 → ℝ) (b : Fin 4 → ℝ),
      c*mean (fun θ => first a θ^(2*k)) ≤
        mean (fun θ => first a θ^(2*k)*Real.exp (second b θ)) := by
  obtain ⟨c₀,hc₀,hmin⟩ := exists_uniform_overlap k
  let c := min 1 (c₀/(5*3^(2*k)))
  have hc : 0 < c := lt_min (by norm_num) (div_pos hc₀ (by positivity))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcc : c*(3^(2*k)) ≤ c₀/5 := by
    have h := min_le_right (1:ℝ) (c₀/(5*3^(2*k)))
    have hp : (0:ℝ) < 3^(2*k) := by positivity
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 5) hp)).mp h
    dsimp [c]
    linarith only [hh]
  refine ⟨c,hc,hc1,?_⟩
  intro a b
  by_cases ha : a = 0
  · subst a
    have hp : 2*k ≠ 0 := (Nat.mul_pos (by norm_num) hk).ne'
    simp only [first,Pi.zero_apply,zero_mul,zero_add,zero_pow hp,mean_const,mul_zero,le_refl]
  by_cases hb : b = 0
  · subst b
    simp only [second,Pi.zero_apply,zero_mul,zero_add,Real.exp_zero,mul_one]
    exact mul_le_of_le_one_left (mean_nonnegative _ (fun θ => (even_two_mul k).pow_nonneg _)) hc1
  let an := ‖a‖⁻¹ • a
  let bn := ‖b‖⁻¹ • b
  have han : ‖an‖ = 1 := norm_smul_inv_norm ha
  have hbn : ‖bn‖ = 1 := norm_smul_inv_norm hb
  have harec : ‖a‖ • an = a := by simp [an,smul_smul,(norm_ne_zero_iff.mpr ha)]
  have hbrec : ‖b‖ • bn = b := by simp [bn,smul_smul,(norm_ne_zero_iff.mpr hb)]
  have hsec (θ : ℝ) : ‖b‖*second bn θ = second b θ := by
    rw [← second_smul,hbrec]
  have hl := (div_le_div_of_nonneg_right (hmin an bn han hbn) (by norm_num : (0:ℝ) ≤ 5)).trans
    (normalized_mean_lower k an bn hbn ‖b‖ (norm_nonneg _))
  simp_rw [hsec] at hl
  have hscaled := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg a) (2*k))
  have he : mean (fun θ => first a θ^(2*k)*Real.exp (second b θ)) =
      ‖a‖^(2*k)*mean (fun θ => first an θ^(2*k)*Real.exp (second b θ)) := by
    conv_lhs => rw [← harec]
    exact weighted_power_smul k ‖a‖ an _
  rw [← he] at hscaled
  apply le_trans _ hscaled
  have hu := mul_le_mul_of_nonneg_left (power_mean_upper k a) hc.le
  have hv := mul_le_mul_of_nonneg_right hcc (pow_nonneg (norm_nonneg a) (2*k))
  nlinarith only [hu,hv]

#print axioms exponential_dominates_positive_part
#print axioms normalized_mean_lower
#print axioms power_mean_upper
#print axioms weighted_power_smul
#print axioms exists_power_coercivity

end
end UnifiedTheory.Audit.KFCausalClassicalMatterProfileCoercivity

