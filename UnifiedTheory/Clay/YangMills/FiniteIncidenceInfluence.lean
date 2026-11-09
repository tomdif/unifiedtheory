/- Incidence double counting for finite local interactions. This module proves
an influence-row bound from explicit interaction-size and incidence-degree
bounds. It does not assert those geometric bounds for a cylinder. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteIncidenceInfluence
noncomputable section
open scoped BigOperators

variable {I P : Type*} [Fintype I] [Fintype P] [DecidableEq I] [DecidableEq P]

/-- Interactions containing the given coordinate. -/
def incidentFaces (face : P → Finset I) (a : I) : Finset P :=
  Finset.univ.filter (fun p => a ∈ face p)

omit [Fintype I] [DecidableEq P] in
@[simp] theorem mem_incidentFaces (face : P → Finset I) (a : I) (p : P) :
    p ∈ incidentFaces face a ↔ a ∈ face p := by simp [incidentFaces]

/-- Off-diagonal shared interactions, with repetitions across distinct faces retained. -/
def sharedFaces (face : P → Finset I) (a b : I) : Finset P :=
  if a = b then ∅ else incidentFaces face a ∩ incidentFaces face b

def multiplicity (face : P → Finset I) (a b : I) : ℕ := (sharedFaces face a b).card

omit [Fintype I] in
@[simp] theorem multiplicity_self (face : P → Finset I) (a : I) :
    multiplicity face a a = 0 := by simp [multiplicity, sharedFaces]

omit [Fintype I] in
theorem sharedFaces_symm (face : P → Finset I) (a b : I) :
    sharedFaces face a b = sharedFaces face b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [sharedFaces, if_neg h, if_neg (Ne.symm h), Finset.inter_comm]

omit [Fintype I] in
theorem multiplicity_symm (face : P → Finset I) (a b : I) :
    multiplicity face a b = multiplicity face b a := by
  rw [multiplicity, sharedFaces_symm]
  rfl

omit [Fintype I] in
theorem multiplicity_eq_sum (face : P → Finset I) (a b : I) :
    multiplicity face a b = ∑ p ∈ incidentFaces face a,
      if a ≠ b ∧ b ∈ face p then 1 else 0 := by
  by_cases h : a = b
  · subst b; simp
  · rw [multiplicity, sharedFaces, if_neg h, Finset.card_eq_sum_ones]
    simp only [ne_eq, h, not_false_eq_true, true_and]
    have he : (fun p => if b ∈ face p then (1 : ℕ) else 0) =
        (fun p => if p ∈ incidentFaces face b then 1 else 0) := by
      funext p
      simp only [mem_incidentFaces]
    rw [he, Finset.sum_ite_mem]

/-- Exact double counting, without a distinct-neighbor assumption. -/
theorem row_eq (face : P → Finset I) (a : I) :
    ∑ b, multiplicity face a b = ∑ p ∈ incidentFaces face a, ((face p).erase a).card := by
  simp_rw [multiplicity_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have he : (face p).erase a = Finset.univ.filter (fun b => a ≠ b ∧ b ∈ face p) := by
    ext b
    simp [ne_comm]
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- At most d faces through a coordinate and at most r other coordinates per face give dr. -/
theorem row_le (face : P → Finset I) (a : I) (d r : ℕ)
    (hface : ∀ p, (face p).card ≤ r + 1) (hdegree : (incidentFaces face a).card ≤ d) :
    ∑ b, multiplicity face a b ≤ d * r := by
  rw [row_eq]
  calc
    _ ≤ ∑ _p ∈ incidentFaces face a, r := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := Finset.card_erase_add_one ((mem_incidentFaces face a p).mp hp)
      have hc := hface p
      omega
    _ ≤ d * r := by
      simpa only [Finset.sum_const, smul_eq_mul] using Nat.mul_le_mul_right r hdegree

/-- The six-by-three Wilson incidence count, ready for an explicit geometric instantiation. -/
theorem row_le_eighteen (face : P → Finset I) (a : I)
    (hface : ∀ p, (face p).card ≤ 4) (hdegree : (incidentFaces face a).card ≤ 6) :
    ∑ b, multiplicity face a b ≤ 18 := row_le face a 6 3 hface hdegree

def coefficient (face : P → Finset I) (β : ℝ) (a b : I) : ℝ :=
  2 * β * (multiplicity face a b : ℝ)

omit [Fintype I] in
theorem coefficient_nonneg (face : P → Finset I) (β : ℝ) (hβ : 0 ≤ β) (a b : I) :
    0 ≤ coefficient face β a b := by unfold coefficient; positivity

omit [Fintype I] in
@[simp] theorem coefficient_self (face : P → Finset I) (β : ℝ) (a : I) :
    coefficient face β a a = 0 := by simp [coefficient]

omit [Fintype I] in
theorem coefficient_symm (face : P → Finset I) (β : ℝ) (a b : I) :
    coefficient face β a b = coefficient face β b a := by
  simp only [coefficient, multiplicity_symm face a b]

/-- The row majorant is explicit once both finite incidence bounds have actually been proved. -/
theorem coefficient_row_le (face : P → Finset I) (β : ℝ) (hβ : 0 ≤ β) (a : I)
    (hface : ∀ p, (face p).card ≤ 4) (hdegree : (incidentFaces face a).card ≤ 6) :
    ∑ b, coefficient face β a b ≤ 36 * β := by
  simp only [coefficient, ← Finset.mul_sum, ← Nat.cast_sum]
  have h : (↑(∑ b, multiplicity face a b) : ℝ) ≤ 18 := by
    exact_mod_cast row_le_eighteen face a hface hdegree
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * β)]

end
end UnifiedTheory.Clay.YangMills.FiniteIncidenceInfluence
