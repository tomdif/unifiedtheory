/-
  LayerB/BigBangIsPosetMinimum.lean — The Big Bang as poset minimum

  Any finite nonempty partial order has minimal elements.
  "Before the Big Bang" asks for elements below the minimum.
  A finite set has none.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finite.Defs
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BigBangIsPosetMinimum

/-- Every finite nonempty partial order has a minimal element:
    an element m with no x strictly below it.

    Uses: the strict order on a finite type is well-founded. -/
theorem exists_minimal (α : Type*) [PartialOrder α] [Finite α] [Nonempty α] :
    ∃ m : α, ∀ x : α, ¬(x < m) := by
  have wf : IsWellFounded α (· < ·) := ⟨IsWellFounded.wf⟩
  obtain ⟨m, hm⟩ := wf.wf.has_min Set.univ ⟨Classical.arbitrary α, Set.mem_univ _⟩
  exact ⟨m, fun x hxm => hm.2 x (Set.mem_univ _) hxm⟩

/-- Every finite nonempty partial order has a maximal element. -/
theorem exists_maximal (α : Type*) [PartialOrder α] [Finite α] [Nonempty α] :
    ∃ m : α, ∀ x : α, ¬(m < x) := by
  have wf : IsWellFounded α (· > ·) := ⟨IsWellFounded.wf⟩
  obtain ⟨m, hm⟩ := wf.wf.has_min Set.univ ⟨Classical.arbitrary α, Set.mem_univ _⟩
  exact ⟨m, fun x hmx => hm.2 x (Set.mem_univ _) hmx⟩

/-- A minimal element has no strict predecessors. -/
theorem nothing_before_minimum (α : Type*) [PartialOrder α] [Finite α] [Nonempty α] :
    ∃ m : α, ∀ x : α, x ≤ m → x = m := by
  obtain ⟨m, hm⟩ := exists_minimal α
  exact ⟨m, fun x hxm => by
    rcases eq_or_lt_of_le hxm with h | h
    · exact h
    · exact absurd h (hm x)⟩

/-- **THE BIG BANG THEOREM.**

    Every finite nonempty causal set has:
    (1) A minimal element (the Big Bang) with no causal past
    (2) A maximal element (the present boundary) with no causal future
    (3) Nothing is strictly before the minimum -/
theorem big_bang (α : Type*) [PartialOrder α] [Finite α] [Nonempty α] :
    (∃ m : α, ∀ x : α, ¬(x < m))
    ∧ (∃ m : α, ∀ x : α, ¬(m < x))
    ∧ (∃ m : α, ∀ x : α, x ≤ m → x = m) :=
  ⟨exists_minimal α, exists_maximal α, nothing_before_minimum α⟩

end UnifiedTheory.LayerB.BigBangIsPosetMinimum
