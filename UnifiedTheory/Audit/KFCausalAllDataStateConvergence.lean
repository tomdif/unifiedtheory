/- Uniform state convergence for every initial form-space state, obtained
from dense graph-data convergence and common initial-state stability. -/
import UnifiedTheory.Audit.KFCausalCommonStableFamily
import UnifiedTheory.Audit.KFCausalDenseUniformStateLimit
import UnifiedTheory.Audit.KFCausalCauchyApproximationFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalAllDataStateConvergence
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem exists_all_data_limits (T : V →ₗ.[ℂ] V) (A : ℝ → ℝ → V →L[ℂ] V)
    (F S : ℝ → V →L[ℂ] V) (q ω ρ : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r)
    (hD : Dense (T.domain : Set V))
    (hfamily : ∃ B κ L : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A (B+n) t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n ∧ 2*ω t ≤ B+n ∧ ρ t ≤ κ) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y, (x,y) ∈ T.graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ t ∈ Icc l r,
        energy (F t) (S t (A (B+n) t (w n x t))) ≤ M)
    (hnorm : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ z, ‖z‖^2 ≤ K*energy (F t) (S t z))
    (hcompare : ∀ b c κ M t, 2 ≤ b → 2 ≤ c → 0 ≤ κ → 0 ≤ M → l ≤ t →
      (∀ z ∈ Icc l t, q z < b ∧ q z < c ∧ ρ z ≤ κ) →
      ∀ u v : ℝ → V, ContinuousOn u (Icc l t) → ContinuousOn v (Icc l t) →
      (∀ z ∈ Ioo l t, HasDerivAt u (A b z (u z)) z) →
      (∀ z ∈ Ioo l t, HasDerivAt v (A c z (v z)) z) → u l = v l →
      (∀ z ∈ Icc l t, energy (F z) (S z (A b z (u z))) ≤ M) →
      (∀ z ∈ Icc l t, energy (F z) (S z (A c z (v z))) ≤ M) →
      energy (F t) (S t (u t-v t)) ≤ Real.exp (κ*(t-l))*((6+κ)*M*(1/b+1/c)*(t-l))) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V, ∃ u : V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A (B+n) t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n) ∧
      (∀ x, u x l = x ∧ ContinuousOn (u x) (Icc l r) ∧
        TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r)) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y t, t ∈ Icc l r → ‖u x t-u y t‖ ≤ L*‖x-y‖ := by
  obtain ⟨B,κ,L,hB,hκ,hL,w,hw,hparams,hstable,hvelocity⟩ := hfamily
  obtain ⟨K,hK,hnorm⟩ := hnorm
  have hBn (n : ℕ) : 2 ≤ B+n := hB.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hDconv (x : V) (hx : x ∈ T.domain) :
      UniformCauchySeqOn (fun n => w n x) atTop (Icc l r) := by
    obtain ⟨y,hxy⟩ := LinearPMap.mem_domain_iff.mp hx
    obtain ⟨M,hM,hvel⟩ := hvelocity x y hxy
    let C := Real.exp (κ*(r-l))*(6+κ)*M*(r-l)
    have hC : 0 ≤ C := mul_nonneg (by positivity) (sub_nonneg.mpr hlr)
    apply KFCausalCoerciveCauchyLimit.uniform_cauchy_of_norm_sq (fun n => w n x) (Icc l r)
      B (K*C) hB (mul_nonneg hK hC)
    intro n m t ht
    have hsub : Icc l t ⊆ Icc l r := Icc_subset_Icc le_rfl ht.2
    have he := hcompare (B+n) (B+m) κ M t (hBn n) (hBn m) hκ hM ht.1
      (fun z hz => ⟨(hparams n z (hsub hz)).1,(hparams m z (hsub hz)).1,(hparams n z (hsub hz)).2.2⟩)
      (w n x) (w m x) ((hw n x).2.1.mono hsub) ((hw m x).2.1.mono hsub)
      (KFCausalUniformGraphTrajectories.subinterval_derivative (w n x)
        (fun z => A (B+n) z (w n x z)) l r t ht.2 (hw n x).2.2)
      (KFCausalUniformGraphTrajectories.subinterval_derivative (w m x)
        (fun z => A (B+m) z (w m x z)) l r t ht.2 (hw m x).2.2)
      ((hw n x).1.trans (hw m x).1.symm)
      (fun z hz => hvel n z (hsub hz)) (fun z hz => hvel m z (hsub hz))
    have hdelta : 0 ≤ 1/(B+(n:ℝ))+1/(B+(m:ℝ)) := by
      have hn : 0 < B+(n:ℝ) := lt_of_lt_of_le (by norm_num) (hBn n)
      have hm : 0 < B+(m:ℝ) := lt_of_lt_of_le (by norm_num) (hBn m)
      positivity
    have he' := KFCausalCauchyApproximationFamily.window_bound κ M (1/(B+n)+1/(B+m)) l r t _
      hκ hM hdelta ht he
    exact (hnorm t ht _).trans ((mul_le_mul_of_nonneg_left he' hK).trans_eq (by dsimp only [C]; ring))
  have hc (x : V) : UniformCauchySeqOn (fun n => w n x) atTop (Icc l r) :=
    KFCausalDenseUniformStateLimit.uniform_cauchy_of_dense w (T.domain : Set V) (Icc l r) L hL hD
      hstable hDconv x
  obtain ⟨u,hu⟩ := KFCausalDenseUniformStateLimit.exists_uniform_limits w l r
    (fun n x => (hw n x).2.1) hc
  refine ⟨B,L,hB,hL,w,u,hw,(fun n t ht => (hparams n t ht).1),?_,hstable,?_⟩
  · intro x
    exact ⟨KFCausalCoerciveCauchyLimit.limit_initial (fun n => w n x) (u x) l r hlr (hu x).2 x
      (fun n => (hw n x).1),(hu x).1,(hu x).2⟩
  · exact KFCausalDenseUniformStateLimit.limit_stability w u (Icc l r) L (fun x => (hu x).2) hstable

#print axioms exists_all_data_limits
end
end UnifiedTheory.Audit.KFCausalAllDataStateConvergence
