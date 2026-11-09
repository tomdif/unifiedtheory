/- A bounded Lipschitz map that is the identity throughout a closed ball.
This permits long-interval Picard constructions followed by a growth estimate. -/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRadialBallClipping
noncomputable section
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def clip (R : ℝ) (x : E) : E := (R/max R ‖x‖) • x

theorem clip_identity (R : ℝ) (hR : 0 < R) (x : E) (hx : ‖x‖ ≤ R) : clip R x = x := by
  simp only [clip,max_eq_left hx,div_self (ne_of_gt hR),one_smul]

theorem clip_norm (R : ℝ) (hR : 0 < R) (x : E) : ‖clip R x‖ = R/max R ‖x‖*‖x‖ := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [clip,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hR.le hm.le)]

theorem clip_norm_le_radius (R : ℝ) (hR : 0 < R) (x : E) : ‖clip R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [clip_norm R hR x,div_mul_eq_mul_div,div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le

theorem clip_norm_le (R : ℝ) (hR : 0 < R) (x : E) : ‖clip R x‖ ≤ ‖x‖ := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [clip_norm R hR x]
  have hc : R/max R ‖x‖ ≤ 1 := (div_le_one hm).mpr (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)

theorem clip_lipschitz (R : ℝ) (hR : 0 < R) : LipschitzWith 2 (clip R : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  let a := max R ‖x‖
  let b := max R ‖y‖
  have ha : 0 < a := hR.trans_le (le_max_left _ _)
  have hb : 0 < b := hR.trans_le (le_max_left _ _)
  have hab : 0 < a*b := mul_pos ha hb
  have hRa : R ≤ a := le_max_left _ _
  have hy : ‖y‖ ≤ b := le_max_right _ _
  have hfirst : R/a ≤ 1 := (div_le_one ha).mpr hRa
  have hsecond : R/(a*b)*‖y‖ ≤ 1 := by
    rw [div_mul_eq_mul_div,div_le_one hab]
    exact (mul_le_mul_of_nonneg_left hy hR.le).trans (mul_le_mul_of_nonneg_right hRa hb.le)
  have hid : R/a-R/b=R*(b-a)/(a*b) := by field_simp
  have hnorm : |b-a| ≤ ‖x-y‖ := by
    have hm := abs_max_sub_max_le_abs ‖y‖ ‖x‖ R
    have hn := abs_norm_sub_norm_le y x
    simpa only [a,b,max_comm,norm_sub_rev] using hm.trans hn
  have hcoeff : |R/a-R/b| ≤ (R/(a*b))*‖x-y‖ := by
    rw [hid,abs_div,abs_mul,abs_of_pos hR,abs_of_pos hab]
    calc
      R*|b-a|/(a*b) ≤ R*‖x-y‖/(a*b) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnorm hR.le) hab.le
      _ = _ := by ring
  have he : clip R x-clip R y=(R/a) • (x-y)+(R/a-R/b) • y := by
    dsimp only [clip,a,b]
    module
  rw [he]
  calc
    _ ≤ ‖(R/a) • (x-y)‖+‖(R/a-R/b) • y‖ := norm_add_le _ _
    _ = (R/a)*‖x-y‖+|R/a-R/b| * ‖y‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hR.le ha.le)]
    _ ≤ 1*‖x-y‖+((R/(a*b))*‖x-y‖)*‖y‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hfirst (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
    _ = ‖x-y‖+(R/(a*b)*‖y‖)*‖x-y‖ := by ring
    _ ≤ ‖x-y‖+1*‖x-y‖ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hsecond (norm_nonneg _))
    _ = ((2:ℝ≥0):ℝ)*‖x-y‖ := by norm_num; ring

#print axioms clip_identity
#print axioms clip_norm
#print axioms clip_norm_le_radius
#print axioms clip_norm_le
#print axioms clip_lipschitz
end
end UnifiedTheory.Audit.KFCausalRadialBallClipping
