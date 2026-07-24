/-
  Audit/KFCausalCSpecBridgePoset.lean   (Step 3 — the amended bridge poset + gates)

  The global specialization order is a graded height-4 poset generated ONLY by the
  covering relations

        atom_{i,a}  ⋖  bridge_{e,a}  ⋖  marker_{e,a}  ⋖  top ,

  where `bridge_{e,a}` lies above exactly `atom_{src e, a}` and `atom_{dst e, σ_e a}`,
  and every bridge owns a PRIVATE `marker` (so `↑bridge = {marker, top}` and distinct
  bridges have distinct strict futures — avoiding the shared-top `Γ=0` collapse).

  The monodromy lives ENTIRELY in the bridge incidence (an ORDER relation to a
  separate carrier), never in an identification, so the order stays acyclic.

  GATES (all proved here, axiom-clean):
    1. global_strictLE_rank_lt        4. global_le_normalForm            [GATE]
    2. global_antisymm                5. no_crossChart_atom_splice
    3. bridge_strictFuture_injective  6. bridge_incidence_recovers_transport

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgePoset

open Relation

variable {Chart Edge : Type*}

/-- The base graph: each edge has a source and target chart and an `S3` transport. -/
structure BaseGraph (Chart Edge : Type*) where
  src : Edge → Chart
  dst : Edge → Chart
  perm : Edge → Equiv.Perm (Fin 3)

/-- Four kinds of global point. -/
inductive GPoint (Chart Edge : Type*)
  | atom   : Chart → Fin 3 → GPoint Chart Edge
  | bridge : Edge → Fin 3 → GPoint Chart Edge
  | marker : Edge → Fin 3 → GPoint Chart Edge
  | top    : GPoint Chart Edge

open GPoint

/-- Height grading: atoms 1, bridges 2, markers 3, top 4. -/
def rank : GPoint Chart Edge → ℕ
  | atom _ _   => 1
  | bridge _ _ => 2
  | marker _ _ => 3
  | top        => 4

/-- The covering relation, as an inductive relation (clean inversion). -/
inductive Cov (G : BaseGraph Chart Edge) : GPoint Chart Edge → GPoint Chart Edge → Prop
  | atomBridge {i : Chart} {b : Fin 3} {e : Edge} {a : Fin 3}
      (h : (i = G.src e ∧ b = a) ∨ (i = G.dst e ∧ b = G.perm e a)) :
      Cov G (atom i b) (bridge e a)
  | bridgeMarker {e : Edge} {a : Fin 3} : Cov G (bridge e a) (marker e a)
  | markerTop {e : Edge} {a : Fin 3} : Cov G (marker e a) top

/-- The global specialization order: reflexive-transitive closure of covers. -/
def globalLE (G : BaseGraph Chart Edge) : GPoint Chart Edge → GPoint Chart Edge → Prop :=
  ReflTransGen (Cov G)

/-! ## Rank gates -/

theorem cov_rank (G : BaseGraph Chart Edge) {x y : GPoint Chart Edge} (h : Cov G x y) :
    rank y = rank x + 1 := by
  cases h <;> rfl

theorem globalLE_rank_le (G : BaseGraph Chart Edge) {x y : GPoint Chart Edge}
    (h : globalLE G x y) : rank x ≤ rank y := by
  induction h with
  | refl => exact le_refl _
  | tail _ hby ih => have := cov_rank G hby; omega

/-- **GATE 1.**  Strict order strictly increases rank. -/
theorem global_strictLE_rank_lt (G : BaseGraph Chart Edge) {x y : GPoint Chart Edge}
    (h : globalLE G x y) (hne : x ≠ y) : rank x < rank y := by
  cases h with
  | refl => exact absurd rfl hne
  | tail hxb hby => have := globalLE_rank_le G hxb; have := cov_rank G hby; omega

/-- **GATE 2.**  Antisymmetry — free from the rank grading. -/
theorem global_antisymm (G : BaseGraph Chart Edge) {x y : GPoint Chart Edge}
    (hxy : globalLE G x y) (hyx : globalLE G y x) : x = y := by
  by_contra hne
  have := global_strictLE_rank_lt G hxy hne
  have := global_strictLE_rank_lt G hyx (Ne.symm hne)
  omega

/-! ## Reachability — the bounded strict futures that block splices -/

theorem top_reachable (G : BaseGraph Chart Edge) {y : GPoint Chart Edge}
    (h : globalLE G top y) : y = top := by
  induction h with
  | refl => rfl
  | tail _ hzy ih => subst ih; cases hzy

theorem marker_reachable (G : BaseGraph Chart Edge) {e : Edge} {a : Fin 3}
    {y : GPoint Chart Edge} (h : globalLE G (marker e a) y) :
    y = marker e a ∨ y = top := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hzy ih =>
      rcases ih with rfl | rfl
      · cases hzy; exact Or.inr rfl
      · cases hzy

theorem bridge_reachable (G : BaseGraph Chart Edge) {e : Edge} {a : Fin 3}
    {y : GPoint Chart Edge} (h : globalLE G (bridge e a) y) :
    y = bridge e a ∨ y = marker e a ∨ y = top := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hzy ih =>
      rcases ih with rfl | rfl | rfl
      · cases hzy; exact Or.inr (Or.inl rfl)
      · cases hzy; exact Or.inr (Or.inr rfl)
      · cases hzy

theorem atom_reachable (G : BaseGraph Chart Edge) {i : Chart} {b : Fin 3}
    {y : GPoint Chart Edge} (h : globalLE G (atom i b) y) :
    y = atom i b
    ∨ (∃ e a, y = bridge e a ∧ Cov G (atom i b) (bridge e a))
    ∨ (∃ e a, y = marker e a ∧ Cov G (atom i b) (bridge e a))
    ∨ y = top := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hzy ih =>
      rcases ih with rfl | ⟨e, a, rfl, hinc⟩ | ⟨e, a, rfl, hinc⟩ | rfl
      · cases hzy with
        | atomBridge h => exact Or.inr (Or.inl ⟨_, _, rfl, .atomBridge h⟩)
      · cases hzy; exact Or.inr (Or.inr (Or.inl ⟨e, a, rfl, hinc⟩))
      · cases hzy; exact Or.inr (Or.inr (Or.inr rfl))
      · cases hzy

/-! ## GATE 4 — the normal form (classifies every comparison; no splice) -/

def IsAtom : GPoint Chart Edge → Prop | atom _ _ => True | _ => False
def IsBridge : GPoint Chart Edge → Prop | bridge _ _ => True | _ => False
def IsMarker : GPoint Chart Edge → Prop | marker _ _ => True | _ => False

/-- Every intended comparison type. -/
def IntendedLE (G : BaseGraph Chart Edge) (x y : GPoint Chart Edge) : Prop :=
  x = y
  ∨ (∃ e a, y = bridge e a ∧ Cov G x (bridge e a))           -- atom → incident bridge
  ∨ (∃ e a, y = marker e a ∧ Cov G x (bridge e a))           -- atom → marker of incident bridge
  ∨ (IsAtom x ∧ y = top)                                     -- atom → top
  ∨ (∃ e a, x = bridge e a ∧ y = marker e a)                 -- bridge → its own marker
  ∨ (IsBridge x ∧ y = top)                                   -- bridge → top
  ∨ (IsMarker x ∧ y = top)                                   -- marker → top

/-- **GATE 4.**  The global order contains ONLY the intended comparisons — no
atom→atom and no bridge→bridge splice. -/
theorem global_le_normalForm (G : BaseGraph Chart Edge) {x y : GPoint Chart Edge}
    (h : globalLE G x y) : IntendedLE G x y := by
  cases x with
  | atom i b =>
      rcases atom_reachable G h with rfl | ⟨e, a, rfl, hinc⟩ | ⟨e, a, rfl, hinc⟩ | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨e, a, rfl, hinc⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨e, a, rfl, hinc⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨trivial, rfl⟩)))
  | bridge e a =>
      rcases bridge_reachable G h with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, a, rfl, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨trivial, rfl⟩)))))
  | marker e a =>
      rcases marker_reachable G h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, rfl⟩)))))
  | top =>
      rw [top_reachable G h]; exact Or.inl rfl

/-! ## GATE 5 — no cross-chart atom splice -/

/-- **GATE 5.**  No two distinct atoms are ever comparable — the equal-rank atom
layer carries no order, so no cross-chart atom→atom splice. -/
theorem no_crossChart_atom_splice (G : BaseGraph Chart Edge)
    (i j : Chart) (a b : Fin 3)
    (h : globalLE G (atom i a) (atom j b)) : (atom i a : GPoint Chart Edge) = atom j b := by
  by_contra hne
  exact absurd (global_strictLE_rank_lt G h hne) (by simp [rank])

/-! ## GATE 3 — bridges have distinct strict futures -/

/-- **GATE 3.**  Distinct bridges have distinct strict futures (the private marker
separates them). -/
theorem bridge_strictFuture_injective (G : BaseGraph Chart Edge)
    {e e' : Edge} {a a' : Fin 3}
    (h : ∀ y, globalLE G (bridge e a) y ↔ globalLE G (bridge e' a') y) :
    (⟨e, a⟩ : Edge × Fin 3) = ⟨e', a'⟩ := by
  have hmem : globalLE G (bridge e a) (marker e a) := ReflTransGen.single .bridgeMarker
  have h2 : globalLE G (bridge e' a') (marker e a) := (h (marker e a)).mp hmem
  rcases bridge_reachable G h2 with heq | heq | heq
  · exact absurd heq (by simp)
  · obtain ⟨rfl, rfl⟩ := GPoint.marker.inj heq.symm; rfl
  · exact absurd heq (by simp)

/-! ## GATE 6 — the transport is recovered from the order alone -/

/-- **GATE 6.**  A `dst`-atom sits under `bridge e a` iff its coordinate is the
transport `σ_e a`; so `σ_e` is read off the incidence in `globalLE` alone (its only
appearance is in the recovered value, not the hypothesis). -/
theorem bridge_incidence_recovers_transport (G : BaseGraph Chart Edge)
    (e : Edge) (a b : Fin 3)
    (hdst : Cov G (atom (G.dst e) b) (bridge e a))
    (hne : G.src e ≠ G.dst e) : b = G.perm e a := by
  cases hdst with
  | atomBridge h =>
      rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1.symm hne
      · exact h2

#print axioms global_strictLE_rank_lt
#print axioms global_antisymm
#print axioms bridge_strictFuture_injective
#print axioms global_le_normalForm
#print axioms no_crossChart_atom_splice
#print axioms bridge_incidence_recovers_transport

end UnifiedTheory.Audit.KFCausalCSpecBridgePoset
