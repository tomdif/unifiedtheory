/- Uniform weighted-mean coercivity for the actual mass/quartic matter
potential, obtained from its finite harmonic degree. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterProfileCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterCoercivity
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics
open UnifiedTheory.Audit.KFCausalClassicalMatterProfileCoercivity
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)

def fieldCoefficients (z : Phase) : Fin 3 → ℝ :=
  ![z.1 (.inr 3),2*scale*z.1 (.inr 2),2*scale*z.2 (.inl 1)]

def shearCoefficients (C : ℝ) (z : Phase) : Fin 4 → ℝ :=
  ![(diagonalPairing z/2)/C,crossPairing z/C,
    (2*scale*z.2 (.inl 1)*z.2 (.inr 3))/C,(2*scale*z.1 (.inr 2)*z.2 (.inr 3))/C]

theorem fieldCoefficients_apply (z : Phase) (θ : ℝ) :
    first (fieldCoefficients z) θ = fieldValue (rotate θ z) := by
  rw [fieldValue_rotate]
  simp [first,fieldCoefficients]
  ring

theorem shearCoefficients_apply (C : ℝ) (z : Phase) (θ : ℝ) :
    second (shearCoefficients C z) θ = shear (rotate θ z)/C := by
  rw [shear_rotate]
  simp [second,shearCoefficients]
  ring

theorem mean_const_mul (a : ℝ) (f : ℝ → ℝ) :
    mean (fun θ => a*f θ) = a*mean f := by
  simp_rw [mul_comm a]
  rw [mean_mul_const,mul_comm]

theorem weightedMean_expansion (m g κ C : ℝ) (z : Phase) :
    weightedMean m g κ C z = κ*exponentialMean C z+
      (m/2)*mean (fun θ => fieldValue (rotate θ z)^2*Real.exp (shear (rotate θ z)/C))+
      (g/4)*mean (fun θ => fieldValue (rotate θ z)^4*Real.exp (shear (rotate θ z)/C)) := by
  have hf : Continuous (fun θ => fieldValue (rotate θ z)) := by
    simp_rw [fieldValue_rotate]
    fun_prop
  have hs := shear_continuous z
  unfold weightedMean potential
  simp_rw [add_mul,mul_assoc]
  rw [mean_add _ _ (by fun_prop) (by fun_prop),mean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [mean_const_mul,exponentialMean]

theorem potential_mean_expansion (m g κ : ℝ) (z : Phase) :
    mean (fun θ => potential m g κ (rotate θ z)) =
      κ+(m/2)*mean (fun θ => fieldValue (rotate θ z)^2)+
      (g/4)*mean (fun θ => fieldValue (rotate θ z)^4) := by
  have hf : Continuous (fun θ => fieldValue (rotate θ z)) := by
    simp_rw [fieldValue_rotate]
    fun_prop
  unfold potential
  rw [mean_add _ _ (by fun_prop) (by fun_prop),mean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [mean_const_mul,mean_const]

theorem exists_weighted_coercivity :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (m g κ C : ℝ), 0 ≤ m → 0 ≤ g → 0 ≤ κ →
      ∀ z : Phase, c*mean (fun θ => potential m g κ (rotate θ z)) ≤ weightedMean m g κ C z := by
  obtain ⟨c₂,hc₂,hc₂1,h₂⟩ := exists_power_coercivity 1 (by norm_num)
  obtain ⟨c₄,hc₄,hc₄1,h₄⟩ := exists_power_coercivity 2 (by norm_num)
  let c := min c₂ c₄
  have hc : 0 < c := lt_min hc₂ hc₄
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hc₂1
  refine ⟨c,hc,hc1,?_⟩
  intro m g κ C hm hg hκ z
  have h2 := h₂ (fieldCoefficients z) (shearCoefficients C z)
  have h4 := h₄ (fieldCoefficients z) (shearCoefficients C z)
  norm_num only [Nat.mul_one,Nat.reduceMul] at h2 h4
  simp_rw [fieldCoefficients_apply,shearCoefficients_apply] at h2 h4
  have h2' : c*mean (fun θ => fieldValue (rotate θ z)^2) ≤
      mean (fun θ => fieldValue (rotate θ z)^2*Real.exp (shear (rotate θ z)/C)) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (mean_nonnegative _ (fun _ => sq_nonneg _))).trans h2
  have h4' : c*mean (fun θ => fieldValue (rotate θ z)^4) ≤
      mean (fun θ => fieldValue (rotate θ z)^4*Real.exp (shear (rotate θ z)/C)) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (mean_nonnegative _ (fun _ => by positivity))).trans h4
  have hv : c*κ ≤ κ*exponentialMean C z :=
    (mul_le_of_le_one_left hκ hc1).trans
      (le_mul_of_one_le_right hκ (exponentialMean_ge_one C z))
  have hm2 := mul_le_mul_of_nonneg_left h2' (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2))
  have hg4 := mul_le_mul_of_nonneg_left h4' (div_nonneg hg (by norm_num : (0:ℝ) ≤ 4))
  rw [weightedMean_expansion,potential_mean_expansion]
  nlinarith only [hv,hm2,hg4]

#print axioms fieldCoefficients_apply
#print axioms shearCoefficients_apply
#print axioms mean_const_mul
#print axioms weightedMean_expansion
#print axioms potential_mean_expansion
#print axioms exists_weighted_coercivity

end
end UnifiedTheory.Audit.KFCausalClassicalMatterCoercivity

