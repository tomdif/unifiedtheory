/- Local changes in canonical characteristics are controlled by the
actual near-identity Weyl test and its explicit ordering phase error. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalCharacteristicIncrement
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]

theorem characteristic_increment (h : ℝ) (f : Lp ℂ 2 μ) (hf : ‖f‖ = 1)
    (z w : Frequency (X := X)) :
    ‖characteristic μ h f (z+w)-characteristic μ h f z‖ ≤
      ‖operator μ h w f-f‖+|h| * |w.1 z.2| := by
  unfold characteristic
  rw [← inner_sub_right]
  have hi := norm_inner_le_norm (𝕜 := ℂ) f (operator μ h (z+w) f-operator μ h z f)
  rw [hf,one_mul] at hi
  have ht := norm_sub_le_norm_sub_add_norm_sub (operator μ h (z+w) f)
    (operator μ h z (operator μ h w f)) (operator μ h z f)
  rw [norm_sub_rev (operator μ h (z+w) f)
    (operator μ h z (operator μ h w f)),← map_sub,(operator μ h z).norm_map] at ht
  have he := product_error μ h z w f
  rw [hf,mul_one] at he
  exact hi.trans (ht.trans ((add_le_add he (le_refl _)).trans_eq (add_comm _ _)))

omit [MeasurableSpace X] [BorelSpace X] [Measure.IsAddHaarMeasure μ] in
theorem encoded_pairing_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] Frequency (X := X)) (x d : V) (hd : ‖d‖ ≤ 1) :
    |(L d).1 (L x).2| ≤ ‖L‖*‖(L x).2‖ := by
  calc
    _ ≤ ‖(L d).1‖*‖(L x).2‖ := (L d).1.le_opNorm _
    _ ≤ ‖L d‖*‖(L x).2‖ := mul_le_mul_of_nonneg_right (norm_fst_le _) (norm_nonneg _)
    _ ≤ (‖L‖*‖d‖)*‖(L x).2‖ := mul_le_mul_of_nonneg_right (L.le_opNorm d) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg L) hd) (norm_nonneg _)

#print axioms characteristic_increment
#print axioms encoded_pairing_bound

end
end UnifiedTheory.Audit.KFCausalCanonicalCharacteristicIncrement
