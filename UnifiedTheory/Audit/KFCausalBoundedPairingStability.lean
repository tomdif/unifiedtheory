/- Strong approximation of a bounded family controls every bounded
quadratic pairing. No convergence of either family separately is needed. -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBoundedPairingStability
noncomputable section
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem difference_bound (A : E →L[ℂ] E) (f g : E) :
    ‖inner ℂ f (A f)-inner ℂ g (A g)‖ ≤ ‖A‖*‖f-g‖*(‖f-g‖+2*‖g‖) := by
  have he : inner ℂ f (A f)-inner ℂ g (A g) =
      inner ℂ (f-g) (A f)+inner ℂ g (A (f-g)) := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [he]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (f-g) (A f)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) g (A (f-g))
  have h3 := mul_le_mul_of_nonneg_left (A.le_opNorm f) (norm_nonneg (f-g))
  have h4 := mul_le_mul_of_nonneg_left (A.le_opNorm (f-g)) (norm_nonneg g)
  have hf : ‖f‖ ≤ ‖f-g‖+‖g‖ := by simpa only [sub_add_cancel] using norm_add_le (f-g) g
  have h5 := mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg A) (norm_nonneg (f-g)))
  have hs := norm_add_le (inner ℂ (f-g) (A f)) (inner ℂ g (A (f-g)))
  nlinarith only [h1,h2,h3,h4,h5,hs]

theorem difference_tendsto (A : E →L[ℂ] E) (f g : ℕ → E) (N : ℝ)
    (hg : ∀ n, ‖g n‖ ≤ N) (hd : Tendsto (fun n => ‖f n-g n‖) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ (f n) (A (f n))-inner ℂ (g n) (A (g n))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => (difference_bound A (f n) (g n)).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖f n-g n‖)
      (mul_le_mul_of_nonneg_left (hg n) (by norm_num : (0:ℝ) ≤ 2)))
      (mul_nonneg (norm_nonneg A) (norm_nonneg _))))
  simpa only [mul_zero,zero_add,zero_mul] using
    ((hd.const_mul ‖A‖).mul (hd.add_const (2*N)))

#print axioms difference_bound
#print axioms difference_tendsto

end
end UnifiedTheory.Audit.KFCausalBoundedPairingStability
