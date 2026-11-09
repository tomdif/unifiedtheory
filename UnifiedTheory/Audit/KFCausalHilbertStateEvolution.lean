/- State solutions and uniqueness for the constructed bounded Hilbert-space
evolution. Derivatives are with respect to real physical time. -/
import UnifiedTheory.Audit.KFCausalHilbertEvolution
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertStateEvolution
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalHilbertIntervalPropagator
open UnifiedTheory.Audit.KFCausalHilbertEvolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
local notation "M" => H →L[ℂ] H

theorem operator_apply_derivative (U : ℝ → M) (v : ℝ → H) (U' : M) (v' : H) (t : ℝ)
    (hU : HasDerivAt U U' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun z => U z (v z)) (U' (v t)+U t v') t := by
  have hR : HasDerivAt (fun z => (U z).restrictScalars ℝ) (U'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hU
  exact hR.clm_apply hv

variable [CompleteSpace H]

theorem skew_inner (A : M) (hA : star A = -A) (f g : H) :
    inner ℂ (A f) g = -inner ℂ f (A g) := by
  rw [← A.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hA,
    ContinuousLinearMap.neg_apply,inner_neg_right]

theorem solution_inner_derivative (A : ℝ → M) (hA : ∀ t, star (A t) = -A t)
    (v : ℝ → H) (hv : ∀ t, HasDerivAt v (A t (v t)) t) (t : ℝ) :
    HasDerivAt (fun z => inner ℂ (v z) (v z)) 0 t := by
  have hd := (hv t).inner ℂ (hv t)
  simpa only [skew_inner (A t) (hA t),add_neg_cancel] using hd

theorem state_solution_unique (A : ℝ → M) (hA : ∀ t, star (A t) = -A t)
    (u v : ℝ → H) (hu : ∀ t, HasDerivAt u (A t (u t)) t)
    (hv : ∀ t, HasDerivAt v (A t (v t)) t) (s : ℝ) (hinit : u s=v s) : u=v := by
  have hd : ∀ t, HasDerivAt (fun z => u z-v z) (A t (u t-v t)) t := by
    intro t
    simpa only [map_sub] using (hu t).sub (hv t)
  funext t
  have he := constant_on_interval (fun z => inner ℂ (u z-v z) (u z-v z))
    (min s t) (max s t)
    (fun z _ => (solution_inner_derivative A hA (fun z => u z-v z) hd z).hasDerivWithinAt)
    s t ⟨min_le_left _ _,le_max_left _ _⟩ ⟨min_le_right _ _,le_max_right _ _⟩
  simp only [hinit,sub_self,inner_zero_left] at he
  exact sub_eq_zero.mp (inner_self_eq_zero.mp he)

theorem evolution_state_derivative (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s t : ℝ) (f : H) :
    HasDerivAt (fun z => evolution A hA hskew s z f)
      (A t (evolution A hA hskew s t f)) t := by
  have hd := operator_apply_derivative (evolution A hA hskew s) (fun _ => f)
    (A t*evolution A hA hskew s t) 0 t (evolution_derivative A hA hskew s t)
      (hasDerivAt_const t f)
  simpa only [ContinuousLinearMap.mul_apply,map_zero,add_zero] using hd

theorem evolution_state_unique (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s : ℝ) (f : H)
    (v : ℝ → H) (hinit : v s=f) (hv : ∀ t, HasDerivAt v (A t (v t)) t) :
    v = fun t => evolution A hA hskew s t f := by
  apply state_solution_unique A hskew v _ hv (fun t => evolution_state_derivative A hA hskew s t f) s
  rw [evolution_initial,ContinuousLinearMap.one_apply,hinit]

theorem existsUnique_state_solution (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (s : ℝ) (f : H) :
    ∃! v : ℝ → H, v s=f ∧ ∀ t, HasDerivAt v (A t (v t)) t := by
  refine ⟨fun t => evolution A hA hskew s t f,⟨?_,?_⟩,?_⟩
  · change evolution A hA hskew s s f = f
    rw [evolution_initial,ContinuousLinearMap.one_apply]
  · exact fun t => evolution_state_derivative A hA hskew s t f
  · intro v hv
    exact evolution_state_unique A hA hskew s f v hv.1 hv.2

#print axioms operator_apply_derivative
#print axioms solution_inner_derivative
#print axioms state_solution_unique
#print axioms evolution_state_derivative
#print axioms evolution_state_unique
#print axioms existsUnique_state_solution

end
end UnifiedTheory.Audit.KFCausalHilbertStateEvolution
