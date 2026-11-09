/- Bounded complex multiplication on L2, with explicit representatives and
bounds. The normalization is only an implementation of the existing
contractive multiplier and does not change the represented function. -/
import UnifiedTheory.Audit.KFCausalContractiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (m : X → ℂ) (hm : Measurable m) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖m x‖ ≤ B)

omit [MeasurableSpace X] in
include hB hb in
theorem normalized_bound (x : X) : ‖m x/(B+1:ℝ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < B+1)]
  exact (div_le_one (by linarith : 0 < B+1)).mpr (by linarith [hb x])

def operator : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ((B+1:ℝ):ℂ) • multiplyL (fun x => m x/(B+1:ℝ))
    (hm.div_const _) (normalized_bound m B hB hb)

theorem operator_coe (f : Lp ℂ 2 μ) : operator m hm B hB hb f =ᵐ[μ] fun x => m x*f x := by
  filter_upwards [Lp.coeFn_smul ((B+1:ℝ):ℂ)
      (multiplyL (fun x => m x/(B+1:ℝ)) (hm.div_const _) (normalized_bound m B hB hb) f),
    multiplyL_coe (fun x => m x/(B+1:ℝ)) (hm.div_const _) (normalized_bound m B hB hb) f] with x hs hx
  change (((B+1:ℝ):ℂ) • multiplyL _ _ _ f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hx]
  have hn : ((B+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp

theorem operator_norm (f : Lp ℂ 2 μ) : ‖operator m hm B hB hb f‖ ≤ B*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operator_coe m hm B hB hb f] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

#print axioms normalized_bound
#print axioms operator_coe
#print axioms operator_norm

end
end UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
