/- Quantitative injectivity of exp(z)+epsilon*z on the closed vertical
strip. The lower distance bound is derived from the real directional
derivative, without a global inverse or univalence assumption. -/
import UnifiedTheory.Audit.KFCausalComplexClockChart
import Mathlib.Topology.MetricSpace.Antilipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalComplexClockCoercivity
noncomputable section
open Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalComplexClockChart

def segmentPairing (ε : ℝ) (w z : ℂ) (t : ℝ) : ℝ :=
  (complexChart ε (w+(t:ℂ)*(z-w))*star (z-w)).re

theorem segmentPairing_derivative (ε : ℝ) (w z : ℂ) (t : ℝ) :
    HasDerivAt (segmentPairing ε w z)
      (((Complex.exp (w+(t:ℂ)*(z-w))).re+ε)*Complex.normSq (z-w)) t := by
  have hl : HasDerivAt (fun r : ℂ => w+r*(z-w)) (z-w) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).mul_const (z-w)).const_add w
  have h := (((complexChart_derivative ε (w+(t:ℂ)*(z-w))).comp (t:ℂ) hl).mul_const
    (star (z-w))).real_of_complex
  simpa only [segmentPairing,Function.comp_apply,mul_assoc,Complex.star_def,Complex.mul_conj,Complex.mul_re,
    Complex.add_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using h

theorem complexChart_strong_monotone (ε : ℝ) (w z : ℂ)
    (hw : w ∈ closedStrip) (hz : z ∈ closedStrip) :
    ε*Complex.normSq (z-w) ≤ ((complexChart ε z-complexChart ε w)*star (z-w)).re := by
  have hd : Differentiable ℝ (segmentPairing ε w z) :=
    fun t => (segmentPairing_derivative ε w z t).differentiableAt
  have hg : ∀ t ∈ interior (Icc (0:ℝ) 1), ε*Complex.normSq (z-w) ≤ deriv (segmentPairing ε w z) t := by
    intro t ht
    rw [(segmentPairing_derivative ε w z t).deriv]
    have hp := strip_exp_re_nonnegative _ (closedStrip_segment w z hw hz t (interior_subset ht))
    nlinarith [Complex.normSq_nonneg (z-w)]
  have hb := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hg
    0 (by constructor <;> norm_num) 1 (by constructor <;> norm_num) (by norm_num)
  have h₀ : segmentPairing ε w z 0=(complexChart ε w*star (z-w)).re := by simp [segmentPairing]
  have h₁ : segmentPairing ε w z 1=(complexChart ε z*star (z-w)).re := by simp [segmentPairing]
  rw [h₀,h₁,sub_zero,mul_one] at hb
  simpa only [sub_mul,Complex.sub_re] using hb

theorem complexChart_norm_lower (ε : ℝ) (w z : ℂ)
    (hw : w ∈ closedStrip) (hz : z ∈ closedStrip) :
    ε*‖z-w‖ ≤ ‖complexChart ε z-complexChart ε w‖ := by
  by_cases he : z=w
  · simp [he]
  have hp : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hu : ((complexChart ε z-complexChart ε w)*star (z-w)).re ≤
      ‖complexChart ε z-complexChart ε w‖*‖z-w‖ := by
    simpa only [norm_mul,norm_star] using Complex.re_le_norm
      ((complexChart ε z-complexChart ε w)*star (z-w))
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ = ε*Complex.normSq (z-w) := by rw [Complex.normSq_eq_norm_sq]; ring
    _ ≤ _ := (complexChart_strong_monotone ε w z hw hz).trans hu
    _ = _ := mul_comm _ _

theorem complexChart_injOn (ε : ℝ) (hε : 0 < ε) : Set.InjOn (complexChart ε) closedStrip := by
  intro z hz w hw he
  by_contra hn
  have hp := mul_pos hε (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
  have hb := complexChart_norm_lower ε w z hw hz
  rw [he,sub_self,norm_zero] at hb
  linarith

#print axioms segmentPairing_derivative
#print axioms complexChart_strong_monotone
#print axioms complexChart_norm_lower
#print axioms complexChart_injOn

end
end UnifiedTheory.Audit.KFCausalComplexClockCoercivity
