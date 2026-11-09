/- Domain membership of an identified state evolution from approximate
velocity bounds and weak resolvent-graph compactness. -/
import UnifiedTheory.Audit.KFCausalWeakResolventGraphLimit
import UnifiedTheory.Audit.KFCausalEventualVelocityControl
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalApproximationDomainLimit
noncomputable section
open Set Filter Topology TopologicalSpace
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [SeparableSpace V]

theorem family_graph_bound (G : ℝ → V →ₗ.[ℂ] V) (A E : ℝ → ℝ → V →L[ℂ] V)
    (R F S : ℝ → V →L[ℂ] V) (q ω ρ : ℝ → ℝ) (Phi : ℝ → V → V) (lam l r : ℝ)
    (hA : ∀ b, 0 < b → (∀ t ∈ Icc l r, q t < b) → ContinuousOn (A b) (Icc l r))
    (hR : ∀ t ∈ Icc l r, ∀ f, (R t f,lam • R t f-f) ∈ (G t).graph)
    (hleft : ∀ t ∈ Icc l r, ∀ x y, (x,y) ∈ (G t).graph → R t (lam • x-y) = x)
    (hgraph : ∀ b, 0 < b → ∀ t ∈ Icc l r, q t < b → ∀ x, (E b t x,A b t x) ∈ (G t).graph)
    (hsmoothed : ∀ b : ℕ → ℝ, Tendsto b atTop atTop → ∀ w : ℕ → ℝ → V, ∀ u : ℝ → V,
      ContinuousOn u (Icc l r) → TendstoUniformlyOn w u atTop (Icc l r) →
      TendstoUniformlyOn (fun n t => E (b n) t (w n t)) u atTop (Icc l r))
    (hcommon : ∃ B κ : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧
      (∀ b, B ≤ b → ∀ t ∈ Icc l r, q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ) ∧
      ∀ x y, (x,y) ∈ (G l).graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ b, B ≤ b →
        ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A b t (w t)) (Icc l r) t ∧ energy (F t) (S t (A b t (w t))) ≤ M)
    (hnorm : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ z, ‖z‖^2 ≤ K*energy (F t) (S t z))
    (hfamily : ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ P : ℕ → ℝ → V →L[ℂ] V,
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n) ∧
      (∀ n, P n l = 1) ∧ (∀ n t, t ∈ Icc l r → ‖P n t‖ ≤ L) ∧
      (∀ n x, ContinuousOn (fun t => P n t x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (fun z => P n z x) (A (B+n) t (P n t x)) (Icc l r) t) ∧
      ∀ x, ContinuousOn (fun t => Phi t x) (Icc l r) ∧
        TendstoUniformlyOn (fun n t => P n t x) (fun t => Phi t x) atTop (Icc l r)) :
    ∀ x y, (x,y) ∈ (G l).graph → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc l r, ∃ v : V, ‖v‖ ≤ C ∧ (Phi t x,v) ∈ (G t).graph := by
  obtain ⟨Bv,_κ,_hBv,_hκ,_hparams,hbudget⟩ := hcommon
  obtain ⟨B,_L,hB,_hL,P,hadm,hi,_hPn,hd,hconv⟩ := hfamily
  have hb : Tendsto (fun n : ℕ => B+(n:ℝ)) atTop atTop := by
    simpa only [add_comm] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds (x := B))
  have hbp (n : ℕ) : 0 < B+(n:ℝ) :=
    add_pos_of_pos_of_nonneg (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hB) (Nat.cast_nonneg n)
  intro x y hxy
  obtain ⟨M,hM,hwitness⟩ := hbudget x y hxy
  obtain ⟨C,hC,hbound⟩ := KFCausalEventualVelocityControl.eventual_norm_bound A F S l r
    (fun n : ℕ => B+(n:ℝ)) hb (fun n t => P n t x) x
    (fun n => hA (B+n) (hbp n) (hadm n))
    (fun n => by simp only [hi,ContinuousLinearMap.one_apply])
    (fun n => (hd n x).1) (fun n => (hd n x).2) ⟨Bv,M,hM,hwitness⟩ hnorm
  have hlim := hsmoothed (fun n : ℕ => B+(n:ℝ)) hb (fun n t => P n t x)
    (fun t => Phi t x) (hconv x).1 (hconv x).2
  refine ⟨C,hC,fun t ht => ?_⟩
  exact KFCausalWeakResolventGraphLimit.bounded_graph_limit (G t) (R t) lam
    (hR t ht) (hleft t ht) (fun n => E (B+n) t (P n t x)) (fun n => A (B+n) t (P n t x))
    (Phi t x) C (fun n => hgraph (B+n) (hbp n) t ht (hadm n t ht) (P n t x))
    (hlim.tendsto_at ht) (hbound.mono (fun n hn => hn t ht))

omit [CompleteSpace V] [SeparableSpace V] in
theorem domain_of_graph_bound (G : ℝ → V →ₗ.[ℂ] V) (Phi : ℝ → V → V) (l r : ℝ)
    (hbound : ∀ x y, (x,y) ∈ (G l).graph → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc l r, ∃ v : V, ‖v‖ ≤ C ∧ (Phi t x,v) ∈ (G t).graph)
    (x : (G l).domain) (t : ℝ) (ht : t ∈ Icc l r) : Phi t x ∈ (G t).domain := by
  obtain ⟨C,_hC,hv⟩ := hbound x (G l x) ((G l).mem_graph x)
  obtain ⟨v,_hv,hg⟩ := hv t ht
  exact LinearPMap.mem_domain_of_mem_graph hg

#print axioms family_graph_bound
#print axioms domain_of_graph_bound
end
end UnifiedTheory.Audit.KFCausalApproximationDomainLimit
