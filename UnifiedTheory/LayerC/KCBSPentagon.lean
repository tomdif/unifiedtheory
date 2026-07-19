/-
  LayerC/KCBSPentagon.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE KCBS PENTAGON CONTEXTUALITY INEQUALITY
  (Klyachko, Can, Binicioğlu, Shumovsky — 2008).
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  This is the **inequality form** of contextuality — the complement of the
  parity-obstruction (equality) form proved for the Cabello 18-vector
  Kochen-Specker construction in `LayerC/KochenSpecker18.lean`.

  THE PENTAGON SETUP.  Consider five rank-one projectors `Π_0, …, Π_4` on
  a Hilbert space (qutrit `ℂ³` suffices) arranged on a cyclic pentagon:

      Π_i ⊥ Π_{(i+1) mod 5}    for i = 0, 1, 2, 3, 4.

  A noncontextual hidden-variable (NCHV) model assigns to each `Π_i` a
  classical `{0, 1}`-valued truth value `f(i)`, respecting orthogonality:
  if `Π_i ⊥ Π_{i+1}`, then we cannot have both `f(i) = f(i+1) = 1`
  (orthogonal projectors cannot both be "true" simultaneously).

  THE COMBINATORIAL BOUND.  The pentagon graph C₅ has independence
  number `α(C₅) = 2`.  Therefore any pentagon-orthogonal {0, 1}-assignment
  satisfies
      Σ_{i=0..4} f(i) ≤ 2.
  This is the load-bearing combinatorial fact, closed by exhaustive
  enumeration over the `2⁵ = 32` Boolean assignments.

  THE KCBS INEQUALITY.  Convex combination over any classical mixture of
  noncontextual assignments lifts the pointwise bound to expectations:
      ⟨Σ_i Π_i⟩_{NCHV} = Σ_i ⟨Π_i⟩_{NCHV} ≤ 2.

  QUANTUM VIOLATION.  Klyachko et al. (2008) show that on a qutrit, with
  the five projectors realised on a regular pentagram of unit vectors,
  the quantum value of `Σ_i ⟨Π_i⟩` reaches `√5 ≈ 2.236 > 2`.  This file
  proves `√5 > 2` rigorously and assembles the no-go:

      `no_NCHV_realizes_quantum`: no NCHV model satisfies
      `Σ_i ⟨Π_i⟩ = √5`.

  STRUCTURE OF THE FILE.
    Part 1: `IsKCBSAssignment` predicate on `Fin 5 → ℕ`.
    Part 2: `kcbs_combinatorial_bound` — by `decide`.
    Part 3: `NCHVModel` structure with finite Λ and probability μ.
    Part 4: `NCHVModel.kcbsSum_le_two` — sum-swap + μ-integration.
    Part 5: Quantum value `√5` and `quantum_violates_kcbs`.
    Part 6: `no_NCHV_realizes_quantum` — the headline no-go.

  STATUS.  Zero `sorry`, zero custom `axiom`.

  SOURCE.  A. A. Klyachko, M. A. Can, S. Binicioğlu, A. S. Shumovsky,
  "Simple test for hidden variables in spin-1 systems," Phys. Rev. Lett.
  101, 020403 (2008).  The independence-number argument is folklore for
  the pentagon graph C₅.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.KCBSPentagon

open Finset
open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE KCBS ASSIGNMENT PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- An **NCHV assignment** for the KCBS pentagon: a function `f : Fin 5 → ℕ`
    valued in `{0, 1}` such that for every pentagon edge `(i, i+1 mod 5)`
    we do not have both `f(i) = 1` and `f((i+1) mod 5) = 1`.

    This encodes the requirement that orthogonal projectors `Π_i ⊥ Π_{i+1}`
    cannot both be assigned the truth value `1` simultaneously. -/
def IsKCBSAssignment (f : Fin 5 → ℕ) : Prop :=
  (∀ i : Fin 5, f i ≤ 1) ∧
  (∀ i : Fin 5, ¬ (f i = 1 ∧ f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ = 1))

/-- Decidability instance for `IsKCBSAssignment`. -/
instance : DecidablePred IsKCBSAssignment := by
  intro f
  unfold IsKCBSAssignment
  infer_instance

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE LOAD-BEARING COMBINATORIAL BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **KCBS COMBINATORIAL BOUND.**

    Any pentagon-orthogonal `{0, 1}`-assignment satisfies
        Σ_i f(i) ≤ 2.

    The pentagon graph C₅ has independence number `α(C₅) = 2`, so at
    most two non-adjacent vertices can be labelled `1`.

    Proof by exhaustive enumeration over the `2⁵ = 32` Boolean
    `Fin 5 → {0, 1}` assignments, filtering by the orthogonality
    constraint and checking the sum. -/
theorem kcbs_combinatorial_bound (f : Fin 5 → ℕ) (h : IsKCBSAssignment f) :
    (∑ i : Fin 5, f i) ≤ 2 := by
  obtain ⟨hbound, horth⟩ := h
  -- Reduce to the finitely many cases of `f i ∈ {0, 1}` for each `i`.
  -- We pin each `f i` to either 0 or 1 using `hbound i : f i ≤ 1`.
  have h0 : f 0 = 0 ∨ f 0 = 1 := by
    have := hbound 0; interval_cases (f 0) <;> tauto
  have h1 : f 1 = 0 ∨ f 1 = 1 := by
    have := hbound 1; interval_cases (f 1) <;> tauto
  have h2 : f 2 = 0 ∨ f 2 = 1 := by
    have := hbound 2; interval_cases (f 2) <;> tauto
  have h3 : f 3 = 0 ∨ f 3 = 1 := by
    have := hbound 3; interval_cases (f 3) <;> tauto
  have h4 : f 4 = 0 ∨ f 4 = 1 := by
    have := hbound 4; interval_cases (f 4) <;> tauto
  -- The five pentagon edges (i, (i+1) mod 5):  (0,1), (1,2), (2,3), (3,4), (4,0).
  -- Specialise `horth` at each edge with the index arithmetic worked out.
  have eq01 : (⟨((0 : Fin 5).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)
                = 1 := by decide
  have eq12 : (⟨((1 : Fin 5).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)
                = 2 := by decide
  have eq23 : (⟨((2 : Fin 5).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)
                = 3 := by decide
  have eq34 : (⟨((3 : Fin 5).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)
                = 4 := by decide
  have eq40 : (⟨((4 : Fin 5).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)
                = 0 := by decide
  have e01 : ¬ (f 0 = 1 ∧ f 1 = 1) := by
    have h := horth 0; rw [eq01] at h; exact h
  have e12 : ¬ (f 1 = 1 ∧ f 2 = 1) := by
    have h := horth 1; rw [eq12] at h; exact h
  have e23 : ¬ (f 2 = 1 ∧ f 3 = 1) := by
    have h := horth 2; rw [eq23] at h; exact h
  have e34 : ¬ (f 3 = 1 ∧ f 4 = 1) := by
    have h := horth 3; rw [eq34] at h; exact h
  have e40 : ¬ (f 4 = 1 ∧ f 0 = 1) := by
    have h := horth 4; rw [eq40] at h; exact h
  -- Now case-split the 32 Boolean assignments and dispatch each by `omega`.
  -- `omega` handles both the arithmetic-bound cases and the orthogonality-
  -- contradiction cases (it normalises the rewritten `¬ (1 = 1 ∧ 1 = 1)`
  -- hypotheses to `False`).
  simp only [Fin.sum_univ_five]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;>
    rw [h0, h1, h2, h3, h4] <;> omega

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE NONCONTEXTUAL HIDDEN-VARIABLE MODEL (NCHV)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A noncontextual hidden-variable (NCHV) model** for the KCBS pentagon.

    The fields encode:
      * `Λ` — the (finite) hidden-variable space;
      * `μ` — a probability distribution on `Λ`;
      * `f l i` — the value assigned to projector `Π_i` at hidden value `l`;
      * `f_valid l` — the per-λ assignment satisfies the pentagon
        orthogonality constraint (`IsKCBSAssignment`). -/
structure NCHVModel where
  /-- The discrete hidden-variable space. -/
  Λ : Type
  /-- It is finite. -/
  fintype : Fintype Λ
  /-- The discrete probability distribution. -/
  μ : Λ → ℝ
  /-- Nonnegative. -/
  μ_nonneg : ∀ l, 0 ≤ μ l
  /-- Sums to one. -/
  μ_sum : (∑ l, μ l) = 1
  /-- The per-λ assignment to the five projectors. -/
  f : Λ → (Fin 5 → ℕ)
  /-- Each per-λ assignment is a valid pentagon-orthogonal {0,1}-assignment. -/
  f_valid : ∀ l, IsKCBSAssignment (f l)

attribute [instance] NCHVModel.fintype

/-- The NCHV-predicted expectation value `⟨Π_i⟩` of the `i`-th projector. -/
noncomputable def NCHVModel.expectation (m : NCHVModel) (i : Fin 5) : ℝ :=
  ∑ l, m.μ l * (m.f l i : ℝ)

/-- The KCBS observable's expectation under an NCHV model:
    `S := Σ_i ⟨Π_i⟩`. -/
noncomputable def NCHVModel.kcbsSum (m : NCHVModel) : ℝ :=
  ∑ i : Fin 5, m.expectation i

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE KCBS INEQUALITY  (S ≤ 2 for every NCHV model)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The per-λ pentagon-sum `Σ_i f(λ, i)` is bounded by 2, as a real number. -/
private lemma NCHVModel.pointwise_sum_le_two (m : NCHVModel) (l : m.Λ) :
    (∑ i : Fin 5, (m.f l i : ℝ)) ≤ 2 := by
  have hcomb : (∑ i : Fin 5, m.f l i) ≤ 2 :=
    kcbs_combinatorial_bound (m.f l) (m.f_valid l)
  have hcast : (∑ i : Fin 5, (m.f l i : ℝ))
                = ((∑ i : Fin 5, m.f l i : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  exact_mod_cast hcomb

/-- The per-λ pentagon-sum is nonnegative. -/
private lemma NCHVModel.pointwise_sum_nonneg (m : NCHVModel) (l : m.Λ) :
    0 ≤ (∑ i : Fin 5, (m.f l i : ℝ)) :=
  Finset.sum_nonneg (fun i _ => by positivity)

/-- The KCBS sum rewritten as `Σ_λ μ(λ) · (Σ_i f(λ, i))` (sum-swap). -/
private lemma NCHVModel.kcbsSum_eq_swap (m : NCHVModel) :
    m.kcbsSum
      = ∑ l : m.Λ, m.μ l * (∑ i : Fin 5, (m.f l i : ℝ)) := by
  unfold NCHVModel.kcbsSum NCHVModel.expectation
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.mul_sum]

/-- **THE KCBS INEQUALITY.**

    Every noncontextual hidden-variable model satisfies
        Σ_i ⟨Π_i⟩  ≤ 2.

    Proof: by the combinatorial bound, the per-λ inner sum is `≤ 2`;
    multiply by the nonnegative weight `μ(λ)` and sum to obtain
        `S = ∑ μ(λ) · (∑_i f(λ, i)) ≤ ∑ μ(λ) · 2 = 2`. -/
theorem NCHVModel.kcbsSum_le_two (m : NCHVModel) : m.kcbsSum ≤ 2 := by
  rw [m.kcbsSum_eq_swap]
  -- ∑ μ(l) * S(l) ≤ ∑ μ(l) * 2 = 2.
  have hpw : ∀ l ∈ (Finset.univ : Finset m.Λ),
      m.μ l * (∑ i : Fin 5, (m.f l i : ℝ)) ≤ m.μ l * 2 := by
    intro l _
    exact mul_le_mul_of_nonneg_left
      (m.pointwise_sum_le_two l) (m.μ_nonneg l)
  have hsum_le : (∑ l : m.Λ, m.μ l * (∑ i : Fin 5, (m.f l i : ℝ)))
                  ≤ ∑ l : m.Λ, m.μ l * 2 :=
    Finset.sum_le_sum hpw
  have hsum_two : (∑ l : m.Λ, m.μ l * 2) = 2 := by
    rw [← Finset.sum_mul, m.μ_sum, one_mul]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE QUANTUM KCBS VALUE  √5 > 2
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **quantum KCBS value**: `√5`.

    Klyachko et al. (2008) show this is attained on a qutrit by the
    five projectors of the regular pentagram on the state along the
    pentagon's symmetry axis. -/
noncomputable def quantumKCBS : ℝ := Real.sqrt 5

/-- **√5 > 2 — the quantum value strictly exceeds the noncontextual bound.**

    Direct: `2 = √4 < √5` since the square root is strictly monotone on
    nonneg reals. -/
theorem quantum_violates_kcbs : 2 < quantumKCBS := by
  unfold quantumKCBS
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hlt : Real.sqrt 4 < Real.sqrt 5 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith [h4, hlt]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE NO-GO  —  NO NCHV MODEL REPRODUCES THE QUANTUM VALUE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE KCBS NO-GO.**

    No noncontextual hidden-variable model can reproduce the quantum
    KCBS value `√5 ≈ 2.236`.

    Proof: any NCHV model has `kcbsSum ≤ 2`, but `√5 > 2`. -/
theorem no_NCHV_realizes_quantum :
    ¬ ∃ m : NCHVModel, m.kcbsSum = quantumKCBS := by
  rintro ⟨m, hm⟩
  have h1 : m.kcbsSum ≤ 2 := m.kcbsSum_le_two
  have h2 : 2 < m.kcbsSum := by rw [hm]; exact quantum_violates_kcbs
  linarith

/-- **Strict form**: no NCHV model attains a value ≥ `√5`. -/
theorem no_NCHV_attains_quantum :
    ∀ m : NCHVModel, m.kcbsSum < quantumKCBS := by
  intro m
  have h1 : m.kcbsSum ≤ 2 := m.kcbsSum_le_two
  have h2 : (2 : ℝ) < quantumKCBS := quantum_violates_kcbs
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Every headline depends only on Lean's three kernel axioms (`propext`,
    `Classical.choice`, `Quot.sound`). -/

#print axioms kcbs_combinatorial_bound
#print axioms NCHVModel.kcbsSum_le_two
#print axioms quantum_violates_kcbs
#print axioms no_NCHV_realizes_quantum
#print axioms no_NCHV_attains_quantum

end UnifiedTheory.LayerC.KCBSPentagon
