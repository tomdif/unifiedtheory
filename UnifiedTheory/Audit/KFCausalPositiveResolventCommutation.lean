/- Commutation of actual positive shifted inverses, with the (T+a)
sign convention and all equations on the original operator domain. -/
import UnifiedTheory.Audit.KFCausalYosidaApproximation
import Mathlib.Algebra.Module.Torsion.Free

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPositiveResolventCommutation
noncomputable section
open KFCausalPositiveResolventBounds KFCausalYosidaApproximation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem spectral_identity (T : H →ₗ.[ℂ] H) (R Q : H →L[ℂ] H) (a b : ℝ)
    (hl : ∀ x : T.domain, R (T x+a • (x:H))=x) (hq : Resolves T Q b) :
    R-Q=(b-a) • (R*Q) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := hl (point T Q b hq f)
  rw [point_value] at he
  change R (f-b • Q f+a • Q f)=Q f at he
  simp only [map_add,map_sub,ContinuousLinearMap.map_smul_of_tower] at he
  change R f-Q f=(b-a) • R (Q f)
  rw [sub_smul]
  calc
    R f-Q f=R f-(R f-b • R (Q f)+a • R (Q f)) := congrArg (fun z => R f-z) he.symm
    _ = _ := by abel

theorem resolvents_commute (T : H →ₗ.[ℂ] H) (R Q : H →L[ℂ] H) (a b : ℝ)
    (hr : Resolves T R a) (hq : Resolves T Q b)
    (hlr : ∀ x : T.domain, R (T x+a • (x:H))=x)
    (hlq : ∀ x : T.domain, Q (T x+b • (x:H))=x) : R*Q=Q*R := by
  have h₁ := spectral_identity T R Q a b hlr hq
  have h₂ := spectral_identity T Q R b a hlq hr
  by_cases he : b=a
  · have heq : R=Q := by
      apply sub_eq_zero.mp
      simpa only [he,sub_self,zero_smul] using h₁
    rw [heq]
  · apply smul_right_injective (M := H →L[ℂ] H) (sub_ne_zero.mpr he)
    change (b-a) • (R*Q)=(b-a) • (Q*R)
    rw [← h₁]
    have hn := congrArg Neg.neg h₂
    simpa only [neg_sub,← neg_smul,neg_sub] using hn

theorem yosida_commutes (R Q : H →L[ℂ] H) (a : ℝ) (hc : R*Q=Q*R) :
    yosida R a*Q=Q*yosida R a := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun L : H →L[ℂ] H => L x) hc
  simp only [ContinuousLinearMap.mul_apply] at he
  simp only [ContinuousLinearMap.mul_apply,yosida_apply,map_sub,
    ContinuousLinearMap.map_smul_of_tower,he]

theorem yosidas_commute (R Q : H →L[ℂ] H) (a b : ℝ) (hc : R*Q=Q*R) :
    yosida R a*yosida Q b=yosida Q b*yosida R a := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun L : H →L[ℂ] H => L x) hc
  simp only [ContinuousLinearMap.mul_apply] at he
  simp only [ContinuousLinearMap.mul_apply,yosida_apply,map_sub,
    ContinuousLinearMap.map_smul_of_tower,he]
  module

#print axioms spectral_identity
#print axioms resolvents_commute
#print axioms yosida_commutes
#print axioms yosidas_commute
end
end UnifiedTheory.Audit.KFCausalPositiveResolventCommutation
