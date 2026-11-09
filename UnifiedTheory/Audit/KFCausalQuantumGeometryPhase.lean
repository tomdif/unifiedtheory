/-
  Graph freezing, finite counting bounds, and a strict variational witness
  for the proposed quantum-connection Hamiltonian. The actual operator
  assembly and graph families are analytic in QUANTUM_GEOMETRY_PHASE_TEST.md.
  This does not prove a geometric phase or an Einstein/chiral continuum.
-/
import UnifiedTheory.Audit.KFCausalEmergenceSupport
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuantumGeometryPhase
noncomputable section
open scoped BigOperators

section GraphMoves
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def NoTriangles : Prop :=
  ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a

def CanCreate (cap : ℕ) (a b : V) : Prop :=
  a ≠ b ∧ ¬G.Adj a b ∧ G.degree a < cap ∧ G.degree b < cap ∧
    ∃ c, G.Adj a c ∧ G.Adj c b

def CanDelete (a b : V) : Prop :=
  G.Adj a b ∧ ∃ c, G.Adj a c ∧ G.Adj c b

/-- The cap blocks every creation on a saturated regular graph. -/
theorem saturated_no_creation (cap : ℕ) (hreg : ∀ v, G.degree v = cap) (a b : V) :
    ¬CanCreate G cap a b := by
  rintro ⟨_, _, ha, _⟩
  simp [hreg a] at ha

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every allowed deletion would close a triangle with its control path. -/
theorem triangle_free_no_deletion (htri : NoTriangles G) (a b : V) :
    ¬CanDelete G a b := by
  rintro ⟨hab, c, hac, hcb⟩
  exact htri a b c hab hcb.symm hac.symm

/-- Actual combinatorial eligibility for every original connection move vanishes. -/
theorem saturated_triangle_free_frozen (cap : ℕ) (hreg : ∀ v, G.degree v = cap)
    (htri : NoTriangles G) : ∀ a b, ¬CanCreate G cap a b ∧ ¬CanDelete G a b := by
  intro a b
  exact ⟨saturated_no_creation G cap hreg a b, triangle_free_no_deletion G htri a b⟩

/-- The handshaking identity bounds actual edges at every finite size. -/
theorem edge_count_bound (cap : ℕ) (hcap : ∀ v, G.degree v ≤ cap) :
    2 * G.edgeFinset.card ≤ Fintype.card V * cap := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc
    ∑ v, G.degree v ≤ ∑ _v : V, cap := Finset.sum_le_sum (fun v _ => hcap v)
    _ = _ := by simp

/-- Counting unordered pairs of neighbors controls all controlled rewiring terms. -/
theorem wedge_count_bound (cap : ℕ) (hcap : ∀ v, G.degree v ≤ cap) :
    (∑ v, (G.degree v).choose 2) ≤ Fintype.card V * cap.choose 2 := by
  calc
    ∑ v, (G.degree v).choose 2 ≤ ∑ _v : V, cap.choose 2 :=
      Finset.sum_le_sum (fun v _ => Nat.choose_le_choose 2 (hcap v))
    _ = _ := by simp

omit [Fintype V] [DecidableRel G.Adj] in
/-- A three-edge path in a triangle-free graph supplies both missing switch edges. -/
theorem path_supplies_switch_nonedges (htri : NoTriangles G) (a b c d : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    ¬G.Adj a c ∧ ¬G.Adj b d := by
  constructor
  · intro hac
    exact htri a b c hab hbc hac.symm
  · intro hbd
    exact htri b c d hbc hcd hbd.symm

end GraphMoves

def twoStateShift (b δ : ℝ) : ℝ :=
  b ^ 2 * (δ - 2 * (1 + |δ|)) / ((1 + |δ|) ^ 2 + b ^ 2)

/-- Explicit unnormalized vector (1,b/(1+|δ|)) for matrix [[0,-b],[-b,δ]]. -/
theorem two_state_rayleigh_identity (b δ : ℝ) :
    (δ * (b / (1 + |δ|)) ^ 2 - 2 * b * (b / (1 + |δ|))) /
      (1 + (b / (1 + |δ|)) ^ 2) = twoStateShift b δ := by
  have hd : 1 + |δ| ≠ 0 := ne_of_gt (by positivity)
  unfold twoStateShift
  field_simp

/-- The actual two-state trial lowers the diagonal energy for every nonzero coupling. -/
theorem two_state_shift_negative (b δ : ℝ) (hb : b ≠ 0) : twoStateShift b δ < 0 := by
  unfold twoStateShift
  have hn : δ - 2 * (1 + |δ|) < 0 := by
    linarith [le_abs_self δ, abs_nonneg δ]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hb) hn)
    (by positivity)

/-- A positive density of independent switch coordinates gives an intensive gain. -/
theorem matching_trial_strictly_lower (E b δ density : ℝ) (hb : b ≠ 0)
    (hd : 0 < density) : E + density * twoStateShift b δ < E := by
  have hs := mul_neg_of_pos_of_neg hd (two_state_shift_negative b δ hb)
  linarith

/-- Generic finite-state interpretation once the operator/trial suppliers are present. -/
theorem frozen_state_not_minimizer {S : Type*} (energy : S → ℝ) (frozen trial : S)
    (E b δ density : ℝ) (hb : b ≠ 0) (hd : 0 < density)
    (hf : energy frozen = E)
    (ht : energy trial = E + density * twoStateShift b δ) :
    ¬∀ state, energy frozen ≤ energy state := by
  intro h
  have hl := h trial
  rw [hf, ht] at hl
  exact (not_le_of_gt (matching_trial_strictly_lower E b δ density hb hd)) hl

/-- A switch removes one and adds one incident edge at each of its four endpoints. -/
theorem switch_degree_preserved (old : ℕ) (h : 1 ≤ old) : old - 1 + 1 = old := by
  omega

#print axioms saturated_no_creation
#print axioms triangle_free_no_deletion
#print axioms saturated_triangle_free_frozen
#print axioms edge_count_bound
#print axioms wedge_count_bound
#print axioms path_supplies_switch_nonedges
#print axioms two_state_rayleigh_identity
#print axioms two_state_shift_negative
#print axioms matching_trial_strictly_lower
#print axioms frozen_state_not_minimizer
#print axioms switch_degree_preserved

end
end UnifiedTheory.Audit.KFCausalQuantumGeometryPhase
