/- Absolute norm bounds for the actual raw Wilson transfer with arbitrary
nonnegative spatial couplings, and comparison of the unmodified raw norm
with the original physical transfer norm. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds
noncomputable section
open WilsonTimeSlab WilsonSingleLinkStaples SpatialPlaquetteCutGeometry
open SpatialWilsonColumnTransfer SpatialWilsonPatchWeights SpatialWilsonReflectionKernel

variable (n : ℕ) [NeZero n]

theorem boundary_le_one (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (u : SpatialLinks (2 * n) Q) : boundary n γ u ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (div_nonneg (hγ p) (by norm_num))
    (WilsonSlabBounds.characterDefect_bounds (spatialHolonomy u p.1 p.2.val.1 p.2.val.2)).1)

theorem kinetic_le_one (β : ℝ) (hβ : 0 ≤ β) (u v : SpatialLinks (2 * n) Q) :
    kineticWeight character β 2 u v ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
  exact Finset.sum_nonneg (fun e _ => (WilsonSlabBounds.characterDefect_bounds ((u e)⁻¹ * v e)).1)

theorem kernel_le_one (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (β : ℝ) (hβ : 0 ≤ β) (u v : SpatialLinks (2 * n) Q) : kernelMap n γ β (u,v) ≤ 1 := by
  have h := mul_le_mul (boundary_le_one n γ hγ u) (kinetic_le_one n β hβ u v)
    (Real.exp_pos _).le (by norm_num)
  have hh := mul_le_mul h (boundary_le_one n γ hγ v) (boundary_pos n γ v).le (by norm_num)
  simpa only [one_mul, kernelMap, ContinuousMap.coe_mk] using hh

theorem norm_le_one (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p) (β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n γ β‖ ≤ 1 := by
  apply (CompactKernelOperator.operator_norm_le (WilsonSlabOperator.measure (2 * n))
    (kernelMap n γ β)).trans
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro uv
  rw [Real.norm_eq_abs, abs_of_pos (kernelMap_pos n γ β uv.1 uv.2)]
  exact kernel_le_one n γ hγ β hβ uv.1 uv.2

theorem raw_full_le_original (β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n (fun _ => β) β‖ ≤ ‖WilsonSlabOperator.transfer (2 * n) β‖ := by
  have h := SpatialWilsonPatchNorm.mass_norm_lower n ∅ (by simp [Aligned]) β hβ
  simpa only [Finset.card_empty, pow_zero, one_mul, omitted, Finset.notMem_empty, if_false] using h

end
end UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds
