/- A concrete finite-cutoff excited/top eigenvalue ratio for the full Wilson
kernel. The positive ground profile is constructed by the imported theorem,
not assumed. The explicit bound degenerates with coupling times spatial
volume and does not give a continuum mass gap. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelRatio
import UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabContinuousRatio
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab

variable (n : ℕ) [NeZero n]

/-- Every actual continuous eigenfunction with a different real eigenvalue has this ratio bound. -/
theorem continuous_eigenvalue_ratio (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℂ))
    (rho : ℝ) (hf : f ≠ 0) (hrho : rho ≠ ‖transfer n β‖)
    (hfeig : ∀ u, (∫ v, (kernel WilsonSingleLinkStaples.character β 2 u v : ℂ) * f v
      ∂measure n) = (rho : ℂ) * f u) :
    |rho / ‖transfer n β‖| ≤
      1 - Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) := by
  obtain ⟨ψ, hψ, _, _, _, heig⟩ :=
    WilsonPositiveGroundState.exists_positive_top_eigenfunction n β hβ
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have h := PositiveKernelRatio.complex_eigenvalue_ratio (measure n) (kernelMap n β) ψ hψ
    ‖transfer n β‖ (Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))) 1
    hlam (Real.exp_pos _) (by norm_num)
    (fun u v => (WilsonSlabBounds.kernel_bounds n β hβ u v).1)
    (fun u v => (WilsonSlabBounds.kernel_bounds n β hβ u v).2)
    heig f rho hf hrho hfeig
  simpa only [div_one] using h

/-- The ratio is strictly below one at each fixed cutoff, with the volume dependence explicit. -/
theorem continuous_eigenvalue_ratio_lt_one (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℂ))
    (rho : ℝ) (hf : f ≠ 0) (hrho : rho ≠ ‖transfer n β‖)
    (hfeig : ∀ u, (∫ v, (kernel WilsonSingleLinkStaples.character β 2 u v : ℂ) * f v
      ∂measure n) = (rho : ℂ) * f u) : |rho / ‖transfer n β‖| < 1 := by
  have h := continuous_eigenvalue_ratio n β hβ f rho hf hrho hfeig
  have hp := Real.exp_pos (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonSlabContinuousRatio
