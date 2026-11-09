/- Every finite connected vertex set admits a closed tour with exactly
2*(card-1) steps. The construction inserts one adjacent unused vertex at
a time and is independent of a spanning-tree or enumeration assumption. -/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteConnectedTours
noncomputable section
open SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
theorem insert_spur {r t x y : V} (w : G.Walk r t) (hx : x ∈ w.support) (hxy : G.Adj x y) :
    ∃ q : G.Walk r t, q.length = w.length + 2 ∧
      ∀ z, z ∈ q.support ↔ z = y ∨ z ∈ w.support := by
  induction w with
  | @nil a =>
    have he : x = a := by simpa using hx
    subst x
    refine ⟨.cons hxy (.cons hxy.symm .nil),by simp,?_⟩
    intro z
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons]
    tauto
  | @cons r s t hrs w ih =>
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      refine ⟨.cons hxy (.cons hxy.symm (.cons hrs w)),by simp,?_⟩
      intro z
      simp only [Walk.support_cons, List.mem_cons]
      tauto
    · obtain ⟨q,hq,hs⟩ := ih hx
      refine ⟨.cons hrs q,by simp only [Walk.length_cons]; omega,?_⟩
      intro z
      simp only [Walk.support_cons, List.mem_cons, hs]
      tauto

omit [DecidableEq V] in
theorem boundary (S A : Finset V) (hS : (G.induce (S : Set V)).Preconnected)
    (hAS : A ⊆ S) (hA : A.Nonempty) (hne : A ≠ S) :
    ∃ x ∈ A, ∃ y ∈ S, y ∉ A ∧ G.Adj x y := by
  classical
  obtain ⟨r,hr⟩ := hA
  have hn : ¬ S ⊆ A := by intro h; exact hne (Finset.Subset.antisymm hAS h)
  obtain ⟨v,hv,hvA⟩ := Finset.not_subset.mp hn
  obtain ⟨w⟩ := hS ⟨r,hAS hr⟩ ⟨v,hv⟩
  obtain ⟨d,_,hd,hd'⟩ := w.exists_boundary_dart {z | z.val ∈ A} hr hvA
  exact ⟨d.fst.val,hd,d.snd.val,d.snd.property,hd',d.adj⟩

theorem growing_tour (S : Finset V) (r : V) (hr : r ∈ S)
    (hS : (G.induce (S : Set V)).Preconnected) (j : ℕ) (hj : j + 1 ≤ S.card) :
    ∃ w : G.Walk r r, w.length = 2 * j ∧ w.support.toFinset.card = j + 1 ∧
      w.support.toFinset ⊆ S := by
  induction j with
  | zero =>
    refine ⟨.nil,by simp,by simp,?_⟩
    simpa using hr
  | succ j ih =>
    obtain ⟨w,hw,hcard,hsub⟩ := ih (by omega)
    have hne : w.support.toFinset ≠ S := by
      intro he
      rw [he] at hcard
      omega
    obtain ⟨x,hx,y,hy,hyA,hxy⟩ := boundary G S w.support.toFinset hS hsub
      ⟨r,List.mem_toFinset.mpr w.start_mem_support⟩ hne
    obtain ⟨q,hq,hs⟩ := insert_spur G w (List.mem_toFinset.mp hx) hxy
    have he : q.support.toFinset = insert y w.support.toFinset := by
      ext z
      simp only [List.mem_toFinset, Finset.mem_insert, hs]
    refine ⟨q,by omega,?_,?_⟩
    · rw [he, Finset.card_insert_of_notMem hyA, hcard]
    · rw [he]
      exact Finset.insert_subset hy hsub

/-- A closed tour visits precisely the connected set, with a linear length. -/
theorem covering_tour (S : Finset V) (r : V) (hr : r ∈ S)
    (hS : (G.induce (S : Set V)).Preconnected) :
    ∃ w : G.Walk r r, w.length = 2 * (S.card - 1) ∧ w.support.toFinset = S := by
  have hp := Finset.card_pos.mpr (show S.Nonempty from ⟨r,hr⟩)
  obtain ⟨w,hw,hcard,hsub⟩ := growing_tour G S r hr hS (S.card - 1) (by omega)
  exact ⟨w,hw,Finset.eq_of_subset_of_card_le hsub (by omega)⟩

end
end UnifiedTheory.Clay.YangMills.FiniteConnectedTours
