/- A globally bounded Lipschitz auxiliary map for the propagator
existence proof. It is exactly the identity on the unit sphere. -/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRadialCutoff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cutoff (x : E) : E := (2/(1+‖x‖) : ℝ) • x

theorem cutoff_on_unit_sphere (x : E) (hx : ‖x‖=1) : cutoff x=x := by
  norm_num [cutoff,hx]

theorem cutoff_norm_le (x : E) : ‖cutoff x‖ ≤ 2 := by
  have hx : 0 < 1+‖x‖ := by positivity
  rw [cutoff,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div,div_le_iff₀ hx]
  nlinarith [norm_nonneg x]

theorem cutoff_lipschitz : LipschitzWith 4 (cutoff : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  let a := 1+‖x‖
  let b := 1+‖y‖
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hab : 0<a*b := mul_pos ha hb
  have hx : 1 ≤ a := by dsimp [a]; linarith [norm_nonneg x]
  have hy : ‖y‖ ≤ a*b := by
    have ht : b ≤ a*b := by nlinarith
    dsimp [b] at ht
    linarith
  have hfirst : 2/a ≤ 2 := (div_le_iff₀ ha).mpr (by linarith)
  have hsecond : (2/(a*b))*‖y‖ ≤ 2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hab]
    linarith
  have hid : 2/a-2/b=2*(b-a)/(a*b) := by field_simp
  have hnorm : |b-a| ≤ ‖x-y‖ := by
    simpa [a,b,abs_sub_comm] using abs_norm_sub_norm_le x y
  have hcoeff : |2/a-2/b| ≤ (2/(a*b))*‖x-y‖ := by
    rw [hid,abs_div,abs_mul,abs_of_pos hab]
    norm_num
    calc
      2*|b-a|/(a*b) ≤ 2*‖x-y‖/(a*b) := by gcongr
      _ = (2/(a*b))*‖x-y‖ := by ring
  have he : cutoff x-cutoff y=(2/a : ℝ) • (x-y)+(2/a-2/b : ℝ) • y := by
    dsimp [cutoff,a,b]
    module
  rw [he]
  calc
    _ ≤ ‖(2/a : ℝ) • (x-y)‖+‖(2/a-2/b : ℝ) • y‖ := norm_add_le _ _
    _ = (2/a)*‖x-y‖+|2/a-2/b| *‖y‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ 2/a by positivity)]
    _ ≤ 2*‖x-y‖+((2/(a*b))*‖x-y‖)*‖y‖ := by gcongr
    _ = 2*‖x-y‖+((2/(a*b))*‖y‖)*‖x-y‖ := by ring
    _ ≤ 2*‖x-y‖+2*‖x-y‖ := by gcongr
    _ = (4 : ℝ)*‖x-y‖ := by ring

#print axioms cutoff_on_unit_sphere
#print axioms cutoff_norm_le
#print axioms cutoff_lipschitz

end
end UnifiedTheory.Audit.KFCausalRadialCutoff
