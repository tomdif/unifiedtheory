/- A statewise stability estimate with no exponential loss. The source
term is the difference of generators acting on the second evolution.
Controlling this term in an approximation limit is a separate obligation. -/
import UnifiedTheory.Audit.KFCausalHilbertStateEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertEvolutionStability
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalHilbertEvolution
open UnifiedTheory.Audit.KFCausalHilbertStateEvolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "M" => H →L[ℂ] H

def interaction (A B : ℝ → M) (hA : Continuous A) (hB : Continuous B)
    (hskewA : ∀ t, star (A t) = -A t) (hskewB : ∀ t, star (B t) = -B t)
    (s t : ℝ) (f : H) : H :=
  star (evolution A hA hskewA s t) (evolution B hB hskewB s t f)

theorem interaction_derivative (A B : ℝ → M) (hA : Continuous A) (hB : Continuous B)
    (hskewA : ∀ t, star (A t) = -A t) (hskewB : ∀ t, star (B t) = -B t)
    (s t : ℝ) (f : H) :
    HasDerivAt (fun z => interaction A B hA hB hskewA hskewB s z f)
      (star (evolution A hA hskewA s t) ((B t-A t) (evolution B hB hskewB s t f))) t := by
  have hd := operator_apply_derivative (fun z => star (evolution A hA hskewA s z))
    (fun z => evolution B hB hskewB s z f) (star (A t*evolution A hA hskewA s t))
    (B t (evolution B hB hskewB s t f)) t
    (evolution_derivative A hA hskewA s t).star (evolution_state_derivative B hB hskewB s t f)
  convert hd using 1
  simp only [star_mul,hskewA,ContinuousLinearMap.mul_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sub_apply,map_neg,map_sub]
  abel

theorem interaction_initial (A B : ℝ → M) (hA : Continuous A) (hB : Continuous B)
    (hskewA : ∀ t, star (A t) = -A t) (hskewB : ∀ t, star (B t) = -B t)
    (s : ℝ) (f : H) : interaction A B hA hB hskewA hskewB s s f = f := by
  simp only [interaction,evolution_initial,star_one,ContinuousLinearMap.one_apply]

theorem interaction_error_norm (A B : ℝ → M) (hA : Continuous A) (hB : Continuous B)
    (hskewA : ∀ t, star (A t) = -A t) (hskewB : ∀ t, star (B t) = -B t)
    (s t : ℝ) (f : H) :
    ‖interaction A B hA hB hskewA hskewB s t f-f‖ =
      ‖evolution A hA hskewA s t f-evolution B hB hskewB s t f‖ := by
  have hn := evolution_norm A hA hskewA t s
    (evolution A hA hskewA s t f-evolution B hB hskewB s t f)
  rw [map_sub,← ContinuousLinearMap.mul_apply,evolution_compose,evolution_initial,
    ContinuousLinearMap.one_apply,norm_sub_rev] at hn
  simpa only [interaction,evolution_reverse] using hn

theorem evolution_difference_bound (A B : ℝ → M) (hA : Continuous A) (hB : Continuous B)
    (hskewA : ∀ t, star (A t) = -A t) (hskewB : ∀ t, star (B t) = -B t)
    (s t C : ℝ) (f : H)
    (hsource : ∀ z ∈ uIcc s t, ‖(B z-A z) (evolution B hB hskewB s z f)‖ ≤ C) :
    ‖evolution A hA hskewA s t f-evolution B hB hskewB s t f‖ ≤ C*|t-s| := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc s t) =>
      (interaction_derivative A B hA hB hskewA hskewB s z f).hasDerivWithinAt)
    (fun z (hz : z ∈ uIcc s t) => by
      rw [evolution_reverse,evolution_norm]
      exact hsource z hz)
    (convex_uIcc s t) (left_mem_uIcc : s ∈ uIcc s t) (right_mem_uIcc : t ∈ uIcc s t)
  rw [interaction_initial,interaction_error_norm,Real.norm_eq_abs] at hb
  exact hb

#print axioms interaction_derivative
#print axioms interaction_error_norm
#print axioms evolution_difference_bound

end
end UnifiedTheory.Audit.KFCausalHilbertEvolutionStability
