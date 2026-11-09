/- The causal order does not select a gauge group.

Link variables on any partial order containing a causal diamond
x < a, x < b, a ≠ b (common future y) realise every element of every group
as a diamond holonomy. So the order alone constrains neither the gauge
group nor its holonomy group; any selection must come from added input.

Separately, "minimal chiral anomaly-free" does not select the Standard
Model: a U(1) theory with five Weyl fermions of charges -10,-4,-2,7,9 is
anomaly-free (gravitational and cubic) and strictly chiral (no opposite
charges, no neutral fermion). See gauge_minimal_chiral_search.py for the
nonabelian cases (minimum 12 Weyl fermions; 14 inside SU(3)xSU(2)xU(1)). -/
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Int.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.CausalOrderGaugeUniversality

/-- A gauge field as one group element per ordered pair of events. -/
def LinkField (α G : Type*) := α → α → G

/-- Holonomy around the causal diamond x → a → y ← b ← x. -/
def diamondHol {α G : Type*} [Group G] (U : LinkField α G) (x a b y : α) : G :=
  U x a * U a y * (U b y)⁻¹ * (U x b)⁻¹

theorem every_element_is_diamond_holonomy {α G : Type*} [PartialOrder α] [Group G]
    (x a b y : α) (hxa : x < a) (hxb : x < b) (hab : a ≠ b) (g : G) :
    ∃ U : LinkField α G, diamondHol U x a b y = g := by
  classical
  refine ⟨fun p q => if p = x ∧ q = a then g else 1, ?_⟩
  have h1 : ¬ (a = x ∧ y = a) := fun h => (ne_of_gt hxa) h.1
  have h2 : ¬ (b = x ∧ y = a) := fun h => (ne_of_gt hxb) h.1
  have h3 : b ≠ a := Ne.symm hab
  simp [diamondHol, h1, h2, h3]

/-- No property of the order can single out a gauge group: on the same
diamond, two arbitrary groups both attain every holonomy. -/
theorem order_does_not_select_group {α : Type*} [PartialOrder α]
    (x a b y : α) (hxa : x < a) (hxb : x < b) (hab : a ≠ b)
    (G H : Type*) [Group G] [Group H] :
    (∀ g : G, ∃ U : LinkField α G, diamondHol U x a b y = g) ∧
      (∀ h : H, ∃ U : LinkField α H, diamondHol U x a b y = h) :=
  ⟨every_element_is_diamond_holonomy x a b y hxa hxb hab,
    every_element_is_diamond_holonomy x a b y hxa hxb hab⟩

/-- Five-fermion chiral anomaly-free U(1) charges. -/
def u1Charges : List ℤ := [-10, -4, -2, 7, 9]

theorem u1_grav_anomaly_free : (u1Charges.map id).sum = 0 := by decide

theorem u1_cubic_anomaly_free : (u1Charges.map (fun q => q ^ 3)).sum = 0 := by decide

theorem u1_strictly_chiral :
    (∀ q ∈ u1Charges, q ≠ 0) ∧ (∀ q ∈ u1Charges, ∀ r ∈ u1Charges, q + r ≠ 0) := by
  decide

#print axioms every_element_is_diamond_holonomy
#print axioms order_does_not_select_group
#print axioms u1_cubic_anomaly_free
#print axioms u1_strictly_chiral

end UnifiedTheory.Audit.CausalOrderGaugeUniversality
