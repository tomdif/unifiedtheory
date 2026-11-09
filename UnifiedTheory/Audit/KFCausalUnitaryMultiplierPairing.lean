/- Pointwise multiplier identities give duality and difference bounds
after an actual L2 unitary coordinate change. No domain hypotheses enter. -/
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalUnitaryMultiplierPairing
noncomputable section
open MeasureTheory

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (M N : H →L[ℂ] H) (m n : X → ℂ)
  (hM : ∀ f, U (M f) =ᵐ[μ] fun x => m x*(U f) x)
  (hN : ∀ f, U (N f) =ᵐ[μ] fun x => n x*(U f) x)

include hM hN in
theorem inner_dual (hn : ∀ x, starRingEnd ℂ (n x) = m x) (f g : H) :
    inner ℂ f (M g) = inner ℂ (N f) g := by
  rw [← U.inner_map_map f (M g),← U.inner_map_map (N f) g,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hM g,hN f] with x hm hn'
  rw [hm,hn']
  change inner ℂ (U f x) (m x • U g x) = inner ℂ (n x • U f x) (U g x)
  rw [inner_smul_right,inner_smul_left,hn]

include hM hN in
theorem difference_bound (b : ℝ) (hb : ∀ x, ‖m x-n x‖ ≤ b) (f : H) :
    ‖M f-N f‖ ≤ b*‖f‖ := by
  rw [← U.norm_map (M f-N f),map_sub,← U.norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (U (M f)) (U (N f)),hM f,hN f] with x hs hm hn
  rw [hs]
  simp only [Pi.sub_apply,hm,hn,← sub_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

#print axioms inner_dual
#print axioms difference_bound

end
end UnifiedTheory.Audit.KFCausalUnitaryMultiplierPairing
