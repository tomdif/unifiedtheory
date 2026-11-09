/- Two-parameter evolution for a continuous bounded skew-adjoint
Hamiltonian generator. Composition and backward evolution prove both
unitary identities without any finite-dimensional assumption. -/
import UnifiedTheory.Audit.KFCausalHilbertGlobalFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertEvolution
noncomputable section
open UnifiedTheory.Audit.KFCausalHilbertGlobalFlow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "M" => H →L[ℂ] H

def evolution (A : ℝ → M) (hA : Continuous A) (hskew : ∀ t, star (A t) = -A t)
    (s t : ℝ) : M :=
  globalFlow (fun r => A (s+r)) (hA.comp (continuous_const.add continuous_id))
    (fun r => hskew (s+r)) (t-s)

theorem evolution_initial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s : ℝ) : evolution A hA hskew s s = 1 := by
  simpa only [evolution,sub_self] using globalFlow_initial (fun r => A (s+r))
    (hA.comp (continuous_const.add continuous_id)) (fun r => hskew (s+r))

theorem evolution_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    HasDerivAt (evolution A hA hskew s) (A t*evolution A hA hskew s t) t := by
  have hd := (globalFlow_derivative (fun r => A (s+r))
    (hA.comp (continuous_const.add continuous_id)) (fun r => hskew (s+r)) (t-s)).scomp t
      ((hasDerivAt_id t).sub_const s)
  simpa only [evolution,Function.comp_def,one_smul,show s+(t-s)=t by ring] using hd

theorem evolution_compose (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (r s t : ℝ) :
    evolution A hA hskew s t * evolution A hA hskew r s = evolution A hA hskew r t := by
  have he : (fun z => evolution A hA hskew s z * evolution A hA hskew r s) =
      evolution A hA hskew r := by
    refine global_solution_unique_at A _ _ hskew ?_ ?_ s ?_
    · intro z
      simpa only [mul_assoc] using
        (evolution_derivative A hA hskew s z).mul_const (evolution A hA hskew r s)
    · exact evolution_derivative A hA hskew r
    · rw [evolution_initial,one_mul]
  exact congrFun he t

theorem evolution_gram (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    star (evolution A hA hskew s t) * evolution A hA hskew s t = 1 :=
  globalFlow_gram _ _ _ _

theorem evolution_inverse (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    evolution A hA hskew s t * evolution A hA hskew t s = 1 := by
  rw [evolution_compose,evolution_initial]

theorem evolution_reverse (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    star (evolution A hA hskew s t) = evolution A hA hskew t s := by
  calc
    _ = star (evolution A hA hskew s t) *
        (evolution A hA hskew s t * evolution A hA hskew t s) := by
      rw [evolution_inverse,mul_one]
    _ = _ := by rw [← mul_assoc,evolution_gram,one_mul]

theorem evolution_unitary (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    star (evolution A hA hskew s t) * evolution A hA hskew s t = 1 ∧
      evolution A hA hskew s t * star (evolution A hA hskew s t) = 1 := by
  rw [evolution_reverse]
  exact ⟨evolution_inverse A hA hskew t s,evolution_inverse A hA hskew s t⟩

theorem evolution_norm (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) (f : H) :
    ‖evolution A hA hskew s t f‖ = ‖f‖ :=
  (evolution A hA hskew s t).norm_map_iff_adjoint_comp_self.mpr (evolution_gram A hA hskew s t) f

theorem evolution_inner (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) (f g : H) :
    inner ℂ (evolution A hA hskew s t f) (evolution A hA hskew s t g) = inner ℂ f g :=
  (evolution A hA hskew s t).inner_map_map_iff_adjoint_comp_self.mpr (evolution_gram A hA hskew s t) f g

theorem evolution_surjective (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    Function.Surjective (evolution A hA hskew s t) := by
  intro f
  refine ⟨evolution A hA hskew t s f,?_⟩
  have he := congrArg (fun X : M => X f) (evolution_inverse A hA hskew s t)
  exact he

theorem evolution_factor (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    evolution A hA hskew s t = evolution A hA hskew 0 t * star (evolution A hA hskew 0 s) := by
  rw [evolution_reverse,evolution_compose]

theorem evolution_initial_time_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) :
    HasDerivAt (fun r => evolution A hA hskew r t) (-evolution A hA hskew s t * A s) s := by
  have he : (fun r => evolution A hA hskew r t) =
      (fun r => evolution A hA hskew 0 t * star (evolution A hA hskew 0 r)) :=
    funext fun r => evolution_factor A hA hskew r t
  rw [he]
  have hd := (evolution_derivative A hA hskew 0 s).star.const_mul (evolution A hA hskew 0 t)
  convert hd using 1
  rw [star_mul,hskew,mul_neg,mul_neg,← mul_assoc,← evolution_factor,neg_mul]

theorem evolution_opNorm_le_one (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) : ‖evolution A hA hskew s t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [evolution_norm,one_mul]

theorem evolution_joint_continuous (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) :
    Continuous (fun p : ℝ × ℝ => evolution A hA hskew p.1 p.2) := by
  have hc : Continuous (evolution A hA hskew 0) :=
    continuous_iff_continuousAt.mpr fun t => (evolution_derivative A hA hskew 0 t).continuousAt
  have he : (fun p : ℝ × ℝ => evolution A hA hskew p.1 p.2) =
      (fun p : ℝ × ℝ => evolution A hA hskew 0 p.2 * star (evolution A hA hskew 0 p.1)) :=
    funext fun p => evolution_factor A hA hskew p.1 p.2
  rw [he]
  exact (hc.comp continuous_snd).mul (hc.comp continuous_fst).star

#print axioms evolution_initial
#print axioms evolution_derivative
#print axioms evolution_compose
#print axioms evolution_inverse
#print axioms evolution_reverse
#print axioms evolution_unitary
#print axioms evolution_norm
#print axioms evolution_inner
#print axioms evolution_surjective
#print axioms evolution_initial_time_derivative
#print axioms evolution_opNorm_le_one
#print axioms evolution_joint_continuous

end
end UnifiedTheory.Audit.KFCausalHilbertEvolution
