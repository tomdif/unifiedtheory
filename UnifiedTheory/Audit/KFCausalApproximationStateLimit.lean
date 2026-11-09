/- Assemble the actual Cauchy trajectory family and uniform coercivity
into a continuous uniform state limit, retaining a quantitative norm rate. -/
import UnifiedTheory.Audit.KFCausalCauchyApproximationFamily
import UnifiedTheory.Audit.KFCausalCoerciveCauchyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalApproximationStateLimit
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem exists_state_limit (A : ℝ → ℝ → V →L[ℂ] V) (F S : ℝ → V →L[ℂ] V)
    (l r : ℝ) (hlr : l ≤ r) (x : V)
    (hfamily : ∃ B C : ℝ, 2 ≤ B ∧ 0 ≤ C ∧ ∃ w : ℕ → ℝ → V,
      (∀ n, w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n) (A (B+n) t (w n t)) (Icc l r) t) ∧
      ∀ n m : ℕ, ∀ t ∈ Icc l r,
        energy (F t) (S t (w n t-w m t)) ≤ C*(1/(B+n)+1/(B+m)))
    (hnorm : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ v, ‖v‖^2 ≤ K*energy (F t) (S t v)) :
    ∃ B C : ℝ, 2 ≤ B ∧ 0 ≤ C ∧ ∃ w : ℕ → ℝ → V, ∃ u : ℝ → V,
      (∀ n, w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n) (A (B+n) t (w n t)) (Icc l r) t) ∧
      u l = x ∧ ContinuousOn u (Icc l r) ∧ TendstoUniformlyOn w u atTop (Icc l r) ∧
      ∀ n : ℕ, ∀ t ∈ Icc l r, ‖w n t-u t‖^2 ≤ C/(B+n) := by
  obtain ⟨B,C,hB,hC,w,hw,he⟩ := hfamily
  obtain ⟨K,hK,hnorm⟩ := hnorm
  have hbound : ∀ n m : ℕ, ∀ t ∈ Icc l r,
      ‖w n t-w m t‖^2 ≤ (K*C)*(1/(B+n)+1/(B+m)) := by
    intro n m t ht
    exact (hnorm t ht _).trans ((mul_le_mul_of_nonneg_left (he n m t ht) hK).trans_eq (by ring))
  obtain ⟨u,huc,hu,hrate⟩ := KFCausalCoerciveCauchyLimit.exists_uniform_limit w l r B (K*C)
    hB (mul_nonneg hK hC) (fun n => (hw n).2.1) hbound
  exact ⟨B,K*C,hB,mul_nonneg hK hC,w,u,hw,
    KFCausalCoerciveCauchyLimit.limit_initial w u l r hlr hu x (fun n => (hw n).1),huc,hu,hrate⟩

#print axioms exists_state_limit
end
end UnifiedTheory.Audit.KFCausalApproximationStateLimit
