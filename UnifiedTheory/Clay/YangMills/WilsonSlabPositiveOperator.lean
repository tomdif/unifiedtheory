/- Positivity of the actual interacting Wilson transfer operator is derived
from the constructed temporal-Haar-averaged Hilbert feature. It is not inferred
from the pointwise positivity of the kernel. The conclusion is finite-cutoff
and supplies no cutoff-uniform physical spectral estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabOperator
import UnifiedTheory.Clay.YangMills.CompactKernelOperatorPositivity
import UnifiedTheory.Clay.YangMills.WilsonSlabPositivity
import UnifiedTheory.Clay.YangMills.WilsonEnergyDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabPositiveOperator
noncomputable section
open MeasureTheory WilsonSlabOperator
open scoped ENNReal InnerProductSpace

variable (n : ℕ) [NeZero n]

/-- The actual continuous full-slab feature, specialized to the fundamental SU(2) character. -/
def feature (β : ℝ) (hβ : 0 ≤ β) :=
  WilsonSlabPositivity.slabFeature (n := n) WilsonEnergyDensity.representation β 2 hβ

theorem feature_continuous (β : ℝ) (hβ : 0 ≤ β) : Continuous (feature n β hβ) :=
  WilsonSlabPositivity.slabFeature_continuous WilsonEnergyDensity.representation
    WilsonSingleLinkStaples.character_continuous β 2 hβ

theorem feature_inner (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    inner ℂ (feature n β hβ u) (feature n β hβ v) = (kernelMap n β (u, v) : ℂ) :=
  WilsonSlabPositivity.slabFeature_inner WilsonEnergyDensity.representation
    WilsonSingleLinkStaples.character_continuous β 2 hβ u v

/-- This is positivity of the full bounded L² operator, with no positivity hypothesis. -/
theorem transfer_positive (β : ℝ) (hβ : 0 ≤ β) : (transfer n β).IsPositive :=
  CompactKernelOperatorPositivity.operator_positive (measure n) (kernelMap n β)
    (feature n β hβ) (feature_continuous n β hβ) (feature_inner n β hβ)

/-- Every continuous test has the squared norm of its actual full-slab feature integral. -/
theorem continuous_quadratic (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℂ)) :
    (inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ f)
      (transfer n β (ContinuousMap.toLp 2 (measure n) ℂ f))).re =
      ‖∫ u, f u • feature n β hβ u ∂measure n‖ ^ 2 := by
  unfold transfer
  rw [CompactKernelOperatorPositivity.continuous_quadratic (measure n) (kernelMap n β)
    (feature n β hβ) (feature_continuous n β hβ) (feature_inner n β hβ)]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

end
end UnifiedTheory.Clay.YangMills.WilsonSlabPositiveOperator
