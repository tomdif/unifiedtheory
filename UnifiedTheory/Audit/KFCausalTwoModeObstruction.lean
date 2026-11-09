/- The free-parent obstruction only needs two physical modes: frequency
   squared zero and one. No negative frequency-squared hypothesis is needed.
   The map is the same time-dependent symplectic point map for both modes. -/
import UnifiedTheory.Audit.KFCausalLocalClockObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTwoModeObstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalLocalClockObstruction

theorem affine_generator_match (a b c d da db dc dd ρ mass k : ℝ)
    (h0 : generatorMatch a b c d da db dc dd ρ mass 0)
    (h1 : generatorMatch a b c d da db dc dd ρ mass 1) :
    generatorMatch a b c d da db dc dd ρ mass k := by
  refine ⟨?_, h0.2.1, ?_, ?_⟩
  · linear_combination (1-k)*h0.1+k*h1.1
  · linear_combination (1-k)*h0.2.2.1+k*h1.2.2.1
  · linear_combination (1-k)*h0.2.2.2+k*h1.2.2.2

theorem two_mode_map_forces_zero_mass
    (a b c d da db dc dd ρ mass : ℝ → ℝ)
    (ha : ∀ t, 0 < t → HasDerivAt a (da t) t)
    (hb : ∀ t, 0 < t → HasDerivAt b (db t) t)
    (hc : ∀ t, 0 < t → HasDerivAt c (dc t) t)
    (hρ : ∀ t, 0 < t → 0 < ρ t)
    (hsym : ∀ t, 0 < t → a t*d t-b t*c t = 1)
    (h0 : ∀ t, 0 < t → generatorMatch (a t) (b t) (c t) (d t)
      (da t) (db t) (dc t) (dd t) (ρ t) (mass t) 0)
    (h1 : ∀ t, 0 < t → generatorMatch (a t) (b t) (c t) (d t)
      (da t) (db t) (dc t) (dd t) (ρ t) (mass t) 1) :
    ∀ t, 0 < t → mass t = 0 := by
  apply local_canonical_map_forces_zero_mass a b c d da db dc dd ρ mass ha hb hc hρ hsym
  intro t ht k
  exact affine_generator_match _ _ _ _ _ _ _ _ _ _ k (h0 t ht) (h1 t ht)

theorem areal_two_mode_map_impossible
    (a b c d da db dc dd ρ : ℝ → ℝ)
    (ha : ∀ t, 0 < t → HasDerivAt a (da t) t)
    (hb : ∀ t, 0 < t → HasDerivAt b (db t) t)
    (hc : ∀ t, 0 < t → HasDerivAt c (dc t) t)
    (hρ : ∀ t, 0 < t → 0 < ρ t)
    (hsym : ∀ t, 0 < t → a t*d t-b t*c t = 1) :
    ¬ (∀ t, 0 < t → ∀ k ∈ ({0,1} : Set ℝ),
      generatorMatch (a t) (b t) (c t) (d t)
        (da t) (db t) (dc t) (dd t) (ρ t) (1/(4*t^2)) k) := by
  intro h
  have hz := two_mode_map_forces_zero_mass a b c d da db dc dd ρ
    (fun t => 1/(4*t^2)) ha hb hc hρ hsym
    (fun t ht => h t ht 0 (by simp)) (fun t ht => h t ht 1 (by simp)) 1 (by norm_num)
  norm_num at hz

#print axioms affine_generator_match
#print axioms two_mode_map_forces_zero_mass
#print axioms areal_two_mode_map_impossible

end
end UnifiedTheory.Audit.KFCausalTwoModeObstruction
