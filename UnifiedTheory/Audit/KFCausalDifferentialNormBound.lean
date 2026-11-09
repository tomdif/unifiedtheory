/- A scalar differential inequality bounds vector increments without
assuming a strong derivative of the vector-valued curve. -/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalDifferentialNormBound
noncomputable section
open Set

variable {H : Type*} [NormedAddCommGroup H]

theorem increment_bound (u : ℝ → H) (d : ℝ → ℝ) (s δ A B : ℝ)
    (hu : Continuous u) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : u s = 0)
    (hd : ∀ t, HasDerivAt (fun z => ‖u z‖^2) (d t) t)
    (hb : ∀ t, |t-s| < δ → |d t| ≤ A*‖u t‖+B*|t-s|)
    (t : ℝ) (ht : |t-s| < δ) :
    ‖u t‖ ≤ (A+Real.sqrt B)*|t-s| := by
  let T := |t-s|
  let K := Icc (s-T) (s+T)
  have hT : 0 ≤ T := abs_nonneg _
  have hs : s ∈ K := ⟨by linarith,by linarith⟩
  have hmem (z : ℝ) : z ∈ K ↔ |z-s| ≤ T := by
    dsimp [K]
    rw [abs_le]
    constructor <;> intro hz <;> constructor <;> linarith [hz.1,hz.2]
  have htt : t ∈ K := (hmem t).mpr le_rfl
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨s,hs⟩ hu.norm.continuousOn
  have hzT : |z-s| ≤ T := (hmem z).mp hz
  have hbound (y : ℝ) (hy : y ∈ K) : ‖d y‖ ≤ A*‖u z‖+B*T := by
    rw [Real.norm_eq_abs]
    exact (hb y (lt_of_le_of_lt ((hmem y).mp hy) ht)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hmax hy) hA)
        (mul_le_mul_of_nonneg_left ((hmem y).mp hy) hB))
  have hm := (convex_Icc (s-T) (s+T)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hd y).hasDerivWithinAt) hbound hs hz
  have hm' : ‖u z‖^2 ≤ (A*‖u z‖+B*T)*T := by
    have he : ‖‖u z‖^2-‖u s‖^2‖ = ‖u z‖^2 := by simp [h0]
    rw [he,Real.norm_eq_abs] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left hzT (by positivity))
  have hroot : ‖u z‖ ≤ (A+Real.sqrt B)*T := by
    by_contra hn
    have hn' : (A+Real.sqrt B)*T < ‖u z‖ := lt_of_not_ge hn
    have hp : 0 < ‖u z‖-A*T := by nlinarith [Real.sqrt_nonneg B]
    have hq : (Real.sqrt B*T)^2 < (‖u z‖-A*T)^2 := by
      apply (sq_lt_sq₀ (by positivity) hp.le).mpr
      nlinarith
    rw [mul_pow,Real.sq_sqrt hB] at hq
    nlinarith [mul_nonneg (mul_nonneg hA hT) hp.le]
  exact (hmax htt).trans hroot

#print axioms increment_bound
end
end UnifiedTheory.Audit.KFCausalDifferentialNormBound
