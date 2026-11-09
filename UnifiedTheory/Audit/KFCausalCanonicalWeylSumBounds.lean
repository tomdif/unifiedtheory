/- Simultaneous canonical phase tests are controlled by the displacement
of individual position and momentum tests. Position factors are ordered
before translations, so their exact Weyl product introduces no phase error. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCanonicalWeylSumBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]

theorem operator_add_bound (h : ℝ) (z w : Frequency (X := X)) (hwz : w.1 z.2 = 0)
    (f : Lp ℂ 2 μ) :
    ‖operator μ h (z+w) f-f‖ ≤ ‖operator μ h z f-f‖+‖operator μ h w f-f‖ := by
  have he := operator_product μ h z w f
  rw [hwz,mul_zero,scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul] at he
  rw [← he]
  have hb := norm_sub_le_norm_sub_add_norm_sub (operator μ h z (operator μ h w f)) (operator μ h z f) f
  rw [← map_sub,(operator μ h z).norm_map] at hb
  exact hb.trans_eq (add_comm _ _)

theorem position_sum_bound {ι : Type*} (s : Finset ι) (h : ℝ) (l : ι → X →L[ℝ] ℝ) (f : Lp ℂ 2 μ) :
    ‖operator μ h (∑ i ∈ s, l i,0) f-f‖ ≤ ∑ i ∈ s, ‖operator μ h (l i,0) f-f‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change ‖operator μ h 0 f-f‖ ≤ 0
    rw [operator_zero,sub_self,norm_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he : (((l a+∑ i ∈ s, l i),0) : Frequency (X := X)) = (l a,0)+(∑ i ∈ s, l i,0) := by simp
    rw [he]
    exact (operator_add_bound μ h _ _ (by simp) f).trans (add_le_add (le_refl _) ih)

theorem momentum_sum_bound {ι : Type*} (s : Finset ι) (h : ℝ) (v : ι → X) (f : Lp ℂ 2 μ) :
    ‖operator μ h (0,∑ i ∈ s, v i) f-f‖ ≤ ∑ i ∈ s, ‖operator μ h (0,v i) f-f‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change ‖operator μ h 0 f-f‖ ≤ 0
    rw [operator_zero,sub_self,norm_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he : ((0,(v a+∑ i ∈ s, v i)) : Frequency (X := X)) = (0,v a)+(0,∑ i ∈ s, v i) := by simp
    rw [he]
    exact (operator_add_bound μ h _ _ (by simp) f).trans (add_le_add (le_refl _) ih)

theorem canonical_sum_bound {ι κ : Type*} (s : Finset ι) (r : Finset κ) (h : ℝ)
    (l : ι → X →L[ℝ] ℝ) (v : κ → X) (f : Lp ℂ 2 μ) :
    ‖operator μ h (∑ i ∈ s, l i,∑ j ∈ r, v j) f-f‖ ≤
      (∑ i ∈ s, ‖operator μ h (l i,0) f-f‖)+(∑ j ∈ r, ‖operator μ h (0,v j) f-f‖) := by
  have he : ((∑ i ∈ s, l i),(∑ j ∈ r, v j)) = (∑ i ∈ s, l i,0)+(0,∑ j ∈ r, v j) := by simp
  rw [he]
  exact (operator_add_bound μ h _ _ (by simp) f).trans
    (add_le_add (position_sum_bound μ s h l f) (momentum_sum_bound μ r h v f))

#print axioms operator_add_bound
#print axioms position_sum_bound
#print axioms momentum_sum_bound
#print axioms canonical_sum_bound

end
end UnifiedTheory.Audit.KFCausalCanonicalWeylSumBounds
