/-
  LayerA/CensusIdentities.lean — the census local layer as DETERMINISTIC
  IDENTITIES (not ensemble averages), upgrading it to Lean-grade.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  The small-rank scan (`scratchpad/census.py`) confirmed two THEOREMS, not
  statistics — both hold on EVERY finite relation, with no measure:

   • BULK CANCELLATION: Σⱼ(|pastⱼ| − |futureⱼ|) = 0 identically, because each
     related pair contributes once to some element's past and once to some
     element's future (Fubini/double-counting). The discrete image of
     "closed manifold ⇒ anomaly cancels" is a static combinatorial identity —
     so the growth process is not merely WHERE the net orientation asymmetry
     lives, it is the ONLY place it CAN live. The no-go isn't mirrored; it's
     forced.

   • ARROW-ODDNESS: the per-event orientation source `past − future` negates
     under order reversal (the dual swaps past and future), identically.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace UnifiedTheory.LayerA.CensusIdentities

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (r : α → α → Prop) [DecidableRel r]

/-- Number of ancestors (causal past) of `j`. -/
def pastCard (j : α) : ℕ := (univ.filter (fun i => r i j)).card
/-- Number of descendants (causal future) of `j`. -/
def futureCard (j : α) : ℕ := (univ.filter (fun k => r j k)).card
/-- The per-event orientation source: past minus future. -/
def orientationSource (j : α) : ℤ := (pastCard r j : ℤ) - (futureCard r j : ℤ)

/-- Total past size = total future size: both count all related pairs once. -/
theorem sum_pastCard_eq_sum_futureCard :
    ∑ j, pastCard r j = ∑ i, futureCard r i := by
  simp only [pastCard, futureCard, card_filter]
  exact Finset.sum_comm

/-- **BULK CANCELLATION (identity).** The total orientation source vanishes on
    every finite relation. No measure, no rank scan — pure double-counting. -/
theorem bulk_cancellation : ∑ j, orientationSource r j = 0 := by
  simp only [orientationSource]
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
      sum_pastCard_eq_sum_futureCard, sub_self]

/-! ## Arrow-oddness of the orientation source -/

/-- Reversing the order swaps past and future, definitionally. -/
theorem pastCard_flip (j : α) :
    pastCard (fun a b => r b a) j = futureCard r j := rfl
theorem futureCard_flip (j : α) :
    futureCard (fun a b => r b a) j = pastCard r j := rfl

/-- **ARROW-ODDNESS (identity).** The per-event orientation source negates under
    order reversal. Holds pointwise on every finite relation. -/
theorem orientationSource_arrow_odd (j : α) :
    orientationSource (fun a b => r b a) j = - orientationSource r j := by
  simp only [orientationSource, pastCard_flip, futureCard_flip]; ring

/-- **Frontier accumulation.** The birth source accumulates (each event
    newborn-maximal exactly once, future then empty ⇒ source = |past|) to
    `Σⱼ|pastⱼ| = Σⱼ|futureⱼ|` — the total related-pair count `R`, by
    `sum_pastCard_eq_sum_futureCard`. Bookkeeping, not statistics. -/
theorem frontier_symmetric : (∑ j, pastCard r j) = ∑ i, futureCard r i :=
  sum_pastCard_eq_sum_futureCard r

end UnifiedTheory.LayerA.CensusIdentities
