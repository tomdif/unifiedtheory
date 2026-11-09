/- A uniformly bounded family of coordinate maps on a Hilbert direct sum. -/
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBoundedDirectSumMap
noncomputable section
open scoped ENNReal

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

variable (B : ∀ i, E i →L[ℂ] E i) (C : ℝ) (hC : 0 ≤ C)
  (hB : ∀ i x, ‖B i x‖ ≤ C * ‖x‖)

include hB in
theorem coordinate_square_bound (i : ι) (x : E i) :
    ‖B i x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hB i x) 2

def applyVector (x : lp E 2) : lp E 2 :=
  ⟨fun i => B i (x i), by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => coordinate_square_bound B C hB i (x i))
    have hx : Summable (fun i => ‖x i‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact hx.mul_left (C ^ 2)⟩

include hC in
theorem applyVector_bound (x : lp E 2) :
    ‖applyVector B C hB x‖ ≤ C * ‖x‖ := by
  have hx : HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  have hy : HasSum (fun i => ‖B i (x i)‖ ^ 2) (‖applyVector B C hB x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (applyVector B C hB x)
  have h := hasSum_le (fun i => coordinate_square_bound B C hB i (x i)) hy (hx.mul_left (C ^ 2))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  simpa only [mul_pow] using h

def linearMap : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun := applyVector B C hB
  map_add' x y := by
    apply lp.ext
    funext i
    exact (B i).map_add (x i) (y i)
  map_smul' c x := by
    apply lp.ext
    funext i
    exact (B i).map_smul c (x i)

def continuousMap : lp E 2 →L[ℂ] lp E 2 :=
  (linearMap B C hB).mkContinuous C (applyVector_bound B C hC hB)

@[simp] theorem continuousMap_apply (x : lp E 2) (i : ι) :
    continuousMap B C hC hB x i = B i (x i) := rfl

end
end UnifiedTheory.Audit.KFCausalBoundedDirectSumMap
