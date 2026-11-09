/- Resolvents at different spectral parameters commute, using inverse
identities on the actual partial-operator graph. -/
import UnifiedTheory.Audit.KFCausalMassFormOperator
import Mathlib.Algebra.Module.Torsion.Free

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPartialResolventCommutation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem spectral_identity (T : V →ₗ.[ℂ] V) (R Q : V →L[ℂ] V) (lam b : ℝ)
    (hl : ∀ x y, (x,y) ∈ T.graph → R (lam • x-y) = x)
    (hg : ∀ f, (Q f,b • Q f-f) ∈ T.graph) : R-Q = (b-lam) • (R*Q) := by
  ext f
  have he := hl (Q f) (b • Q f-f) (hg f)
  simp only [map_sub,ContinuousLinearMap.map_smul_of_tower] at he
  change R f-Q f = (b-lam) • R (Q f)
  rw [sub_smul]
  calc
    R f-Q f = R f-(lam • R (Q f)-(b • R (Q f)-R f)) := congrArg (fun x => R f-x) he.symm
    _ = _ := by abel

theorem resolvents_commute (T : V →ₗ.[ℂ] V) (R Q : V →L[ℂ] V) (lam b : ℝ)
    (hRl : ∀ x y, (x,y) ∈ T.graph → R (lam • x-y) = x)
    (hRg : ∀ f, (R f,lam • R f-f) ∈ T.graph)
    (hQl : ∀ x y, (x,y) ∈ T.graph → Q (b • x-y) = x)
    (hQg : ∀ f, (Q f,b • Q f-f) ∈ T.graph) : R*Q = Q*R := by
  have h₁ := spectral_identity T R Q lam b hRl hQg
  have h₂ := spectral_identity T Q R b lam hQl hRg
  by_cases he : b = lam
  · have heq : R = Q := by
      apply sub_eq_zero.mp
      simpa only [he,sub_self,zero_smul] using h₁
    rw [heq]
  · apply (smul_right_injective (M := V →L[ℂ] V) (sub_ne_zero.mpr he))
    change (b-lam) • (R*Q) = (b-lam) • (Q*R)
    rw [← h₁]
    have hn := congrArg Neg.neg h₂
    simpa only [neg_sub,← neg_smul,neg_sub] using hn

theorem regularization_commutes (R Q A : V →L[ℂ] V) (b : ℝ)
    (hc : R*Q = Q*R) (hA : A = b • (b • Q-1)) : R*A = A*R := by
  rw [hA]
  ext x
  have he := congrArg (fun L : V →L[ℂ] V => L x) hc
  simp only [ContinuousLinearMap.mul_apply] at he
  simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,map_sub,
    ContinuousLinearMap.map_smul_of_tower,he]

#print axioms spectral_identity
#print axioms resolvents_commute
#print axioms regularization_commutes
end
end UnifiedTheory.Audit.KFCausalPartialResolventCommutation
