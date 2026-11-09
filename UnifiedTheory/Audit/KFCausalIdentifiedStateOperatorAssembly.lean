/- Replace the unspecified limits of a constructed bounded operator family
by an explicit evolution, using a proved trajectory identification. -/
import UnifiedTheory.Audit.KFCausalStateOperatorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalIdentifiedStateOperatorAssembly
noncomputable section
open Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem identify (A : ℝ → ℝ → V →L[ℂ] V) (q : ℝ → ℝ) (K : ℝ → V → V) (l r : ℝ)
    (hK : ∀ x, ContinuousOn (fun t => K t x) (Icc l r))
    (hidentify : ∀ b : ℕ → ℝ, Tendsto b atTop atTop → (∀ n, 0 < b n) →
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < b n) →
      ∀ w : ℕ → ℝ → V, ∀ u : ℝ → V, ContinuousOn u (Icc l r) →
      TendstoUniformlyOn w u atTop (Icc l r) →
      (∀ n t, t ∈ Icc l r → HasDerivWithinAt (w n) (A (b n) t (w n t)) (Icc l r) t) →
      ∀ t ∈ Icc l r, u t = K t (u l))
    (hex : ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ P : ℕ → ℝ → V →L[ℂ] V, ∃ U : ℝ → V →L[ℂ] V,
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n) ∧
      (∀ n, P n l = 1) ∧ U l = 1 ∧
      (∀ n t, t ∈ Icc l r → ‖P n t‖ ≤ L) ∧ (∀ t ∈ Icc l r, ‖U t‖ ≤ L) ∧
      (∀ n x, ContinuousOn (fun t => P n t x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (fun z => P n z x) (A (B+n) t (P n t x)) (Icc l r) t) ∧
      ∀ x, ContinuousOn (fun t => U t x) (Icc l r) ∧
        TendstoUniformlyOn (fun n t => P n t x) (fun t => U t x) atTop (Icc l r)) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ P : ℕ → ℝ → V →L[ℂ] V,
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n) ∧
      (∀ n, P n l = 1) ∧ (∀ n t, t ∈ Icc l r → ‖P n t‖ ≤ L) ∧
      (∀ n x, ContinuousOn (fun t => P n t x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (fun z => P n z x) (A (B+n) t (P n t x)) (Icc l r) t) ∧
      ∀ x, ContinuousOn (fun t => K t x) (Icc l r) ∧
        TendstoUniformlyOn (fun n t => P n t x) (fun t => K t x) atTop (Icc l r) := by
  obtain ⟨B,L,hB,hL,P,U,hadm,hi,hUi,hPn,_hUn,hd,hconv⟩ := hex
  have hb : Tendsto (fun n : ℕ => B+(n:ℝ)) atTop atTop := by
    simpa only [add_comm] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds (x := B))
  have hbp (n : ℕ) : 0 < B+(n:ℝ) :=
    add_pos_of_pos_of_nonneg (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hB) (Nat.cast_nonneg n)
  refine ⟨B,L,hB,hL,P,hadm,hi,hPn,hd,fun x => ⟨hK x,(hconv x).2.congr_right ?_⟩⟩
  intro t ht
  simpa only [hUi,ContinuousLinearMap.one_apply] using
    hidentify (fun n : ℕ => B+(n:ℝ)) hb hbp hadm (fun n z => P n z x) (fun z => U z x)
      (hconv x).1 (hconv x).2 (fun n => (hd n x).2) t ht

#print axioms identify
end
end UnifiedTheory.Audit.KFCausalIdentifiedStateOperatorAssembly
