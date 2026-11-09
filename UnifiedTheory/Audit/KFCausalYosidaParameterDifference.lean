/- The two-sided resolvent equations control changes of cutoff. The
Yosida difference factors through the smoothing defect at the second cutoff. -/
import UnifiedTheory.Audit.KFCausalYosidaApproximation
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalYosidaParameterDifference
noncomputable section
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
open UnifiedTheory.Audit.KFCausalYosidaApproximation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_difference_apply (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ)
    (hs : Resolves T S b) (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x) (f : H) :
    R f-S f = (b-a) • R (S f) := by
  have hp := hl (point T S b hs f)
  rw [point_value] at hp
  change R (f-b • S f+a • S f) = S f at hp
  simp only [map_add,map_sub,ContinuousLinearMap.map_smul_of_tower] at hp
  calc
    R f-S f = R f-(R f-b • R (S f)+a • R (S f)) := congrArg (fun x : H => R f-x) hp.symm
    _ = (b-a) • R (S f) := by rw [sub_smul]; abel

theorem yosida_difference_apply (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ)
    (hs : Resolves T S b) (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x) (f : H) :
    yosida R a f-yosida S b f =
      (a-b) • ((f-b • S f)-a • R (f-b • S f)) := by
  have hr := resolvent_difference_apply T R S a b hs hl f
  have hp : R f = S f+(b-a) • R (S f) := (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)
  simp only [yosida_apply,map_sub,ContinuousLinearMap.map_smul_of_tower]
  rw [hp]
  module

theorem yosida_difference_bound (T : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hr : Resolves T R a) (hs : Resolves T S b)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re)
    (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x) (f : H) :
    ‖yosida R a f-yosida S b f‖ ≤ 2*|a-b| *‖f-b • S f‖ := by
  rw [yosida_difference_apply T R S a b hs hl,norm_smul,Real.norm_eq_abs]
  have hn := (norm_sub_le (f-b • S f) (a • R (f-b • S f))).trans
    (add_le_add le_rfl (scaled_resolvent_contraction T R a ha hr hp (f-b • S f)))
  have he := mul_le_mul_of_nonneg_left hn (abs_nonneg (a-b))
  nlinarith

#print axioms resolvent_difference_apply
#print axioms yosida_difference_apply
#print axioms yosida_difference_bound

end
end UnifiedTheory.Audit.KFCausalYosidaParameterDifference
