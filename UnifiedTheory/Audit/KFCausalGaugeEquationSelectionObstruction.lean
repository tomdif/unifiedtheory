/- The repository's Yang--Mills equation admits nonzero abelian field jets
in every positive gauge dimension. Thus that equation and the Lie bracket
identities alone do not select the Standard Model gauge algebra. These are
actual ConnectionData witnesses, not global microscopic causal histories. -/
import UnifiedTheory.LayerA.NonabelianYangMills

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGaugeEquationSelectionObstruction
noncomputable section
open UnifiedTheory.LayerA.GaugeConnection
open UnifiedTheory.LayerA.NonabelianYangMills

def constantField (k : ℕ) : ConnectionData 4 (k+1) where
  A := fun _ _ => 0
  dA := fun μ ν a => if μ=0 ∧ ν=1 ∧ a=0 then 1 else 0
  ddA := fun _ _ _ _ => 0
  ddA_comm := fun _ _ _ _ => rfl

theorem field_is_nonzero (k : ℕ) :
    curvature abelianSC (constantField k) 0 1 0=1 := by
  simp [abelian_curvature,constantField]

theorem field_satisfies_equation (k : ℕ) :
    satisfiesNonabelianYM abelianSC (constantField k) := by
  intro ν a
  simp [yangMillsDivNonabelian,covariantDerivF,abelianSC,constantField]

theorem every_positive_dimension (d : ℕ) (hd : 0 < d) :
    ∃ sc : StructureConstants d, ∃ conn : ConnectionData 4 d,
      satisfiesNonabelianYM sc conn ∧
        ∃ μ ν a, curvature sc conn μ ν a ≠ 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  refine ⟨abelianSC,constantField k,field_satisfies_equation k,0,1,0,?_⟩
  rw [field_is_nonzero]
  norm_num

theorem no_unique_dimension_from_equation :
    ¬ ∃ selected : ℕ, ∀ d : ℕ, ∀ sc : StructureConstants d,
      ∀ conn : ConnectionData 4 d, satisfiesNonabelianYM sc conn →
        (∃ μ ν a, curvature sc conn μ ν a ≠ 0) → d=selected := by
  rintro ⟨selected,h⟩
  obtain ⟨sc₁,conn₁,hym₁,hnz₁⟩ := every_positive_dimension 1 (by norm_num)
  obtain ⟨sc₂,conn₂,hym₂,hnz₂⟩ := every_positive_dimension 2 (by norm_num)
  have h1 := h 1 sc₁ conn₁ hym₁ hnz₁
  have h2 := h 2 sc₂ conn₂ hym₂ hnz₂
  omega

#print axioms field_is_nonzero
#print axioms field_satisfies_equation
#print axioms every_positive_dimension
#print axioms no_unique_dimension_from_equation
end
end UnifiedTheory.Audit.KFCausalGaugeEquationSelectionObstruction
