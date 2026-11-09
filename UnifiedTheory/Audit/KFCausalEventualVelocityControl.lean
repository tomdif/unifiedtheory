/- Transfer an existing uniform velocity-energy witness to any chosen
approximation family by bounded-equation uniqueness, then use coercivity. -/
import UnifiedTheory.Audit.KFCausalStableTrajectoryNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEventualVelocityControl
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem eventual_norm_bound (A : ℝ → ℝ → V →L[ℂ] V) (F S : ℝ → V →L[ℂ] V)
    (l r : ℝ) (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) (w : ℕ → ℝ → V) (x : V)
    (hA : ∀ n, ContinuousOn (A (b n)) (Icc l r))
    (hi : ∀ n, w n l = x) (hc : ∀ n, ContinuousOn (w n) (Icc l r))
    (hd : ∀ n t, t ∈ Icc l r → HasDerivWithinAt (w n) (A (b n) t (w n t)) (Icc l r) t)
    (hwitness : ∃ B M : ℝ, 0 ≤ M ∧ ∀ b, B ≤ b → ∃ v : ℝ → V,
      v l = x ∧ ContinuousOn v (Icc l r) ∧ ∀ t ∈ Icc l r,
        HasDerivWithinAt v (A b t (v t)) (Icc l r) t ∧ energy (F t) (S t (A b t (v t))) ≤ M)
    (hnorm : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ z, ‖z‖^2 ≤ K*energy (F t) (S t z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc l r, ‖A (b n) t (w n t)‖ ≤ C := by
  obtain ⟨B,M,hM,hv⟩ := hwitness
  obtain ⟨K,hK,hcoerce⟩ := hnorm
  refine ⟨K*M+1,by positivity,?_⟩
  filter_upwards [hb.eventually (eventually_ge_atTop B)] with n hn
  obtain ⟨v,hvi,hvc,hvd⟩ := hv (b n) hn
  have he := KFCausalResolventDomainTrajectories.solution_unique (A (b n)) l r (hA n)
    (w n) v (hc n) hvc (hd n) (fun t ht => (hvd t ht).1) ((hi n).trans hvi.symm)
  intro t ht
  have henergy : energy (F t) (S t (A (b n) t (w n t))) ≤ M := by
    rw [he t ht]
    exact (hvd t ht).2
  have hsq := (hcoerce t ht (A (b n) t (w n t))).trans (mul_le_mul_of_nonneg_left henergy hK)
  simpa only [mul_one] using KFCausalStableTrajectoryNorm.square_to_bound (K*M)
    ‖A (b n) t (w n t)‖ 1 (mul_nonneg hK hM) (norm_nonneg _) zero_le_one
    (by simpa only [one_pow,mul_one] using hsq)

#print axioms eventual_norm_bound
end
end UnifiedTheory.Audit.KFCausalEventualVelocityControl
