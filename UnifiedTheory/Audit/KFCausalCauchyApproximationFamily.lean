/- A uniform velocity family and the two-solution estimate give a
quantitative energy-Cauchy family of actual approximate trajectories. -/
import UnifiedTheory.Audit.KFCausalGraphVelocityFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCauchyApproximationFamily
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

theorem window_bound (κ M δ l r t E : ℝ) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (ht : t ∈ Icc l r)
    (he : E ≤ Real.exp (κ*(t-l))*((6+κ)*M*δ*(t-l))) :
    E ≤ (Real.exp (κ*(r-l))*(6+κ)*M*(r-l))*δ := by
  have hJ : 0 ≤ (6+κ)*M*δ := by positivity
  have htime := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) hJ
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) hκ)
  have hm := mul_le_mul hexp htime (mul_nonneg hJ (sub_nonneg.mpr ht.1)) (Real.exp_pos _).le
  exact he.trans (hm.trans_eq (by ring))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_cauchy_family (A : ℝ → ℝ → V →L[ℂ] V) (F S : ℝ → V →L[ℂ] V)
    (q ω ρ : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r) (x : V)
    (hfamily : ∃ B κ M : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧ 0 ≤ M ∧ ∃ w : ℕ → ℝ → V, ∀ n,
      w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧ ∀ t ∈ Icc l r,
        HasDerivWithinAt (w n) (A (B+n) t (w n t)) (Icc l r) t ∧
        energy (F t) (S t (A (B+n) t (w n t))) ≤ M ∧
        q t < B+n ∧ 2*ω t ≤ B+n ∧ ρ t ≤ κ)
    (hcompare : ∀ b c κ M t, 2 ≤ b → 2 ≤ c → 0 ≤ κ → 0 ≤ M → l ≤ t →
      (∀ u ∈ Icc l t, q u < b ∧ q u < c ∧ ρ u ≤ κ) →
      ∀ u v : ℝ → V, ContinuousOn u (Icc l t) → ContinuousOn v (Icc l t) →
      (∀ z ∈ Ioo l t, HasDerivAt u (A b z (u z)) z) →
      (∀ z ∈ Ioo l t, HasDerivAt v (A c z (v z)) z) → u l = v l →
      (∀ z ∈ Icc l t, energy (F z) (S z (A b z (u z))) ≤ M) →
      (∀ z ∈ Icc l t, energy (F z) (S z (A c z (v z))) ≤ M) →
      energy (F t) (S t (u t-v t)) ≤ Real.exp (κ*(t-l))*((6+κ)*M*(1/b+1/c)*(t-l))) :
    ∃ B C : ℝ, 2 ≤ B ∧ 0 ≤ C ∧ ∃ w : ℕ → ℝ → V,
      (∀ n, w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n) (A (B+n) t (w n t)) (Icc l r) t) ∧
      ∀ n m : ℕ, ∀ t ∈ Icc l r,
        energy (F t) (S t (w n t-w m t)) ≤ C*(1/(B+n)+1/(B+m)) := by
  obtain ⟨B,κ,M,hB,hκ,hM,w,hw⟩ := hfamily
  let C := Real.exp (κ*(r-l))*(6+κ)*M*(r-l)
  have hC : 0 ≤ C := by dsimp [C]; exact mul_nonneg (by positivity) (sub_nonneg.mpr hlr)
  refine ⟨B,C,hB,hC,w,fun n => ⟨(hw n).1,(hw n).2.1,fun t ht => ((hw n).2.2 t ht).1⟩,?_⟩
  intro n m t ht
  have hsub : Icc l t ⊆ Icc l r := Icc_subset_Icc le_rfl ht.2
  have hbn : 2 ≤ B+(n:ℝ) := hB.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hbm : 2 ≤ B+(m:ℝ) := hB.trans (le_add_of_nonneg_right (Nat.cast_nonneg m))
  have hbpos : 0 < B+(n:ℝ) := lt_of_lt_of_le (by norm_num) hbn
  have hcpos : 0 < B+(m:ℝ) := lt_of_lt_of_le (by norm_num) hbm
  apply window_bound κ M (1/(B+n)+1/(B+m)) l r t _ hκ hM (by positivity) ht
  exact hcompare (B+n) (B+m) κ M t hbn hbm hκ hM ht.1
    (fun u hu => ⟨((hw n).2.2 u (hsub hu)).2.2.1,((hw m).2.2 u (hsub hu)).2.2.1,
      ((hw n).2.2 u (hsub hu)).2.2.2.2⟩)
    (w n) (w m) ((hw n).2.1.mono hsub) ((hw m).2.1.mono hsub)
    (KFCausalUniformGraphTrajectories.subinterval_derivative (w n) (fun u => A (B+n) u (w n u))
      l r t ht.2 (fun u hu => ((hw n).2.2 u hu).1))
    (KFCausalUniformGraphTrajectories.subinterval_derivative (w m) (fun u => A (B+m) u (w m u))
      l r t ht.2 (fun u hu => ((hw m).2.2 u hu).1))
    ((hw n).1.trans (hw m).1.symm)
    (fun u hu => ((hw n).2.2 u (hsub hu)).2.1)
    (fun u hu => ((hw m).2.2 u (hsub hu)).2.1)

#print axioms window_bound
#print axioms exists_cauchy_family
end
end UnifiedTheory.Audit.KFCausalCauchyApproximationFamily
