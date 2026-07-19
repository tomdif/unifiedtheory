/-
  LayerC/KochenSpecker18.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE KOCHEN-SPECKER THEOREM (Cabello-Estebaranz-García-Alcaine, 1996).
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  We give a fully formal, finite, combinatorial proof of the Kochen-Specker
  theorem in its sharpest classical form: the Cabello-Estebaranz-García-Alcaine
  18-vector / 9-tetrad construction in ℝ⁴.

  THE CONSTRUCTION.  We exhibit 18 specific vectors in ℤ⁴ (and hence in ℝ⁴
  after normalization, though the parity proof is purely combinatorial and
  needs no real numbers) and 9 mutually-orthogonal tetrads such that:

    • Each of the 9 tetrads consists of 4 pairwise orthogonal vectors.
    • Each of the 18 vectors appears in **exactly 2** of the 9 tetrads.

  THE PARITY OBSTRUCTION.  A "KS noncoloring" is a function
      f : {v₀, …, v₁₇} → {0, 1}
  with the property that, on every tetrad T, exactly one vector receives
  the value 1.  We prove no such f can exist:

      Σ_{T} Σ_{v ∈ T} f(v) = 9 · 1 = 9          (sum-to-one in each tetrad)
                          = Σ_{v} (#tetrads ∋ v) · f(v)
                          = 2 · Σ_{v} f(v)        (each v in exactly 2 tetrads)

  The first line is odd, the last is even.  Contradiction.

  This excludes any noncontextual {0,1}-valued assignment compatible with
  the orthogonality structure of these 18 ℝ⁴ vectors — the strongest known
  no-go result for hidden variables of the noncontextual kind, complementing
  Bell's nonlocality theorem.

  SOURCE.  Cabello, Estebaranz, García-Alcaine, "Bell-Kochen-Specker theorem:
  A proof with 18 vectors," Phys. Lett. A 212, 183 (1996).
  Encoded here following the standard tabulation reproduced on the Wikipedia
  page "Kochen-Specker theorem".

  STATUS.  Zero `sorry`, zero custom `axiom`.  The combinatorial facts
  (orthogonality of each tetrad, two-fold appearance of each vector) are
  closed by `decide`; the parity argument is closed by `Finset.sum_comm` and
  `omega`.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace UnifiedTheory.LayerC.KochenSpecker18

open Finset

/-! ## The 18 Cabello vectors in ℤ⁴.

We work over ℤ throughout: the parity argument is purely combinatorial
and orthogonality `⟨v,w⟩ = 0` is preserved by any rescaling, so the integer
representation is faithful to the ℝ⁴ statement. -/

/-- The 18 Cabello-Estebaranz-García-Alcaine vectors, as functions `Fin 4 → ℤ`.

The canonical CEG enumeration (each appears in exactly two of the nine
tetrads of `cabelloTetrad` below):

```
  v₀  = (0, 0, 0, 1)      v₉  = (0, 0, 1, 1)
  v₁  = (0, 0, 1, 0)      v₁₀ = (1, 1, 1, 1)
  v₂  = (1, 1, 0, 0)      v₁₁ = (0, 1, 0, -1)
  v₃  = (1, -1, 0, 0)     v₁₂ = (1, 0, 0, 1)
  v₄  = (0, 1, 0, 0)      v₁₃ = (1, 0, 0, -1)
  v₅  = (1, 0, 1, 0)      v₁₄ = (0, 1, -1, 0)
  v₆  = (1, 0, -1, 0)     v₁₅ = (1, 1, -1, 1)
  v₇  = (1, -1, 1, -1)    v₁₆ = (1, 1, 1, -1)
  v₈  = (1, -1, -1, 1)    v₁₇ = (-1, 1, 1, 1)
```
-/
def cabelloVector : Fin 18 → (Fin 4 → ℤ)
  | ⟨0,  _⟩ => ![0,  0,  0,  1]
  | ⟨1,  _⟩ => ![0,  0,  1,  0]
  | ⟨2,  _⟩ => ![1,  1,  0,  0]
  | ⟨3,  _⟩ => ![1, -1,  0,  0]
  | ⟨4,  _⟩ => ![0,  1,  0,  0]
  | ⟨5,  _⟩ => ![1,  0,  1,  0]
  | ⟨6,  _⟩ => ![1,  0, -1,  0]
  | ⟨7,  _⟩ => ![1, -1,  1, -1]
  | ⟨8,  _⟩ => ![1, -1, -1,  1]
  | ⟨9,  _⟩ => ![0,  0,  1,  1]
  | ⟨10, _⟩ => ![1,  1,  1,  1]
  | ⟨11, _⟩ => ![0,  1,  0, -1]
  | ⟨12, _⟩ => ![1,  0,  0,  1]
  | ⟨13, _⟩ => ![1,  0,  0, -1]
  | ⟨14, _⟩ => ![0,  1, -1,  0]
  | ⟨15, _⟩ => ![1,  1, -1,  1]
  | ⟨16, _⟩ => ![1,  1,  1, -1]
  | ⟨17, _⟩ => ![-1, 1,  1,  1]
  | ⟨n+18, h⟩ => absurd h (by omega)

/-- Unnormalized integer inner product on `Fin 4 → ℤ`. -/
def innerZ (v w : Fin 4 → ℤ) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3

/-! ## The 9 Cabello tetrads.

Each tetrad is encoded as a `Finset (Fin 18)` of size 4. The nine columns
of the CEG table are:

```
  T₀ : v₀  v₁  v₂  v₃         (0,0,0,1)(0,0,1,0)(1,1,0,0)(1,-1,0,0)
  T₁ : v₀  v₄  v₅  v₆         (0,0,0,1)(0,1,0,0)(1,0,1,0)(1,0,-1,0)
  T₂ : v₂  v₇  v₈  v₉         (1,1,0,0)(1,-1,1,-1)(1,-1,-1,1)(0,0,1,1)
  T₃ : v₆  v₇  v₁₀ v₁₁        (1,0,-1,0)(1,-1,1,-1)(1,1,1,1)(0,1,0,-1)
  T₄ : v₁  v₄  v₁₂ v₁₃        (0,0,1,0)(0,1,0,0)(1,0,0,1)(1,0,0,-1)
  T₅ : v₈  v₁₀ v₁₃ v₁₄        (1,-1,-1,1)(1,1,1,1)(1,0,0,-1)(0,1,-1,0)
  T₆ : v₃  v₉  v₁₅ v₁₆        (1,-1,0,0)(0,0,1,1)(1,1,-1,1)(1,1,1,-1)
  T₇ : v₅  v₁₁ v₁₅ v₁₇        (1,0,1,0)(0,1,0,-1)(1,1,-1,1)(-1,1,1,1)
  T₈ : v₁₂ v₁₄ v₁₆ v₁₇        (1,0,0,1)(0,1,-1,0)(1,1,1,-1)(-1,1,1,1)
```
-/
def cabelloTetrad : Fin 9 → Finset (Fin 18)
  | ⟨0, _⟩ => {0, 1, 2, 3}
  | ⟨1, _⟩ => {0, 4, 5, 6}
  | ⟨2, _⟩ => {2, 7, 8, 9}
  | ⟨3, _⟩ => {6, 7, 10, 11}
  | ⟨4, _⟩ => {1, 4, 12, 13}
  | ⟨5, _⟩ => {8, 10, 13, 14}
  | ⟨6, _⟩ => {3, 9, 15, 16}
  | ⟨7, _⟩ => {5, 11, 15, 17}
  | ⟨8, _⟩ => {12, 14, 16, 17}
  | ⟨n+9, h⟩ => absurd h (by omega)

/-! ## Verification of orthogonality and tetrad sizes. -/

/-- Each tetrad has exactly 4 elements. -/
theorem cabelloTetrad_card (t : Fin 9) : (cabelloTetrad t).card = 4 := by
  fin_cases t <;> decide

/-- The 9 tetrads consist of pairwise orthogonal vectors.  Closed by
case-enumeration: for each of the 9 tetrads, all 4·3 = 12 pairs of
*distinct* vectors are dispatched to `decide`. -/
theorem cabelloTetrad_orthogonal
    (t : Fin 9) {i j : Fin 18}
    (hi : i ∈ cabelloTetrad t) (hj : j ∈ cabelloTetrad t) (hij : i ≠ j) :
    innerZ (cabelloVector i) (cabelloVector j) = 0 := by
  fin_cases t <;>
    · simp only [cabelloTetrad, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;>
        rcases hj with rfl | rfl | rfl | rfl <;>
        first
          | exact (hij rfl).elim
          | decide

/-- The load-bearing combinatorial fact: each of the 18 vectors appears in
**exactly 2** of the 9 tetrads. -/
theorem cabelloVector_in_exactly_two_tetrads (v : Fin 18) :
    ((Finset.univ : Finset (Fin 9)).filter
      (fun t => v ∈ cabelloTetrad t)).card = 2 := by
  fin_cases v <;> decide

/-! ## The Kochen-Specker noncoloring property and its impossibility. -/

/-- A **KS-noncoloring** of the Cabello configuration is a function
`f : Fin 18 → ℕ` with `f v ∈ {0,1}` such that the values in each tetrad sum
to `1` (equivalently: exactly one vector per tetrad is assigned the value
`1`).  This is the noncontextual hidden-variable property to be excluded. -/
def IsKSNoncoloring (f : Fin 18 → ℕ) : Prop :=
  (∀ v, f v ≤ 1) ∧ (∀ t : Fin 9, ∑ v ∈ cabelloTetrad t, f v = 1)

/-! ### The two-faces sum identity (Σ_T Σ_{v∈T} f v = Σ_v (#T ∋ v) · f v) -/

/-- Indicator form of the inner sum: summing `f` over a finset `s ⊆ Fin 18`
equals summing the indicator `if v ∈ s then f v else 0` over all of `Fin 18`. -/
private lemma sum_eq_indicator_sum
    (s : Finset (Fin 18)) (f : Fin 18 → ℕ) :
    (∑ v ∈ s, f v)
      = ∑ v : Fin 18, (if v ∈ s then f v else 0) := by
  rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin 18))) (p := (· ∈ s))]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext v; simp

/-- Indicator form of a counting sum: the cardinality of a filtered finset
equals the sum of the indicator. -/
private lemma card_filter_eq_indicator_sum (v : Fin 18) :
    ((Finset.univ : Finset (Fin 9)).filter
        (fun t => v ∈ cabelloTetrad t)).card
      = ∑ t : Fin 9, (if v ∈ cabelloTetrad t then (1 : ℕ) else 0) := by
  rw [Finset.card_filter]

/-- Sum-swap identity: summing `f` over each tetrad and then over all tetrads
equals, for each vector `v`, the multiplicity (number of tetrads containing
`v`) times `f v`. -/
theorem sum_over_tetrads_eq_multiplicity (f : Fin 18 → ℕ) :
    (∑ t : Fin 9, ∑ v ∈ cabelloTetrad t, f v)
      = ∑ v : Fin 18,
          ((Finset.univ : Finset (Fin 9)).filter
            (fun t => v ∈ cabelloTetrad t)).card * f v := by
  -- Step 1: rewrite the LHS via the indicator.
  have hLHS :
      (∑ t : Fin 9, ∑ v ∈ cabelloTetrad t, f v)
        = ∑ t : Fin 9, ∑ v : Fin 18,
            (if v ∈ cabelloTetrad t then f v else 0) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact sum_eq_indicator_sum (cabelloTetrad t) f
  -- Step 2: rewrite the RHS via the indicator and pull the constant `f v`
  -- inside the inner sum over `t`.
  have hRHS :
      (∑ v : Fin 18,
          ((Finset.univ : Finset (Fin 9)).filter
            (fun t => v ∈ cabelloTetrad t)).card * f v)
        = ∑ v : Fin 18, ∑ t : Fin 9,
            (if v ∈ cabelloTetrad t then f v else 0) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [card_filter_eq_indicator_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : v ∈ cabelloTetrad t
    · simp [h]
    · simp [h]
  -- Step 3: combine and swap the two outer sums.
  rw [hLHS, hRHS, Finset.sum_comm]

/-- **The Kochen-Specker theorem (Cabello 18-vector form).**

There is no `{0,1}`-valued assignment to the 18 Cabello vectors of ℝ⁴ that
gives, in each of the nine orthogonal tetrads, exactly one vector the value
`1`.  Consequently, the orthogonality structure of these 18 vectors admits
**no noncontextual hidden-variable model**.

The proof is a one-line parity argument: 9 (odd) = 2·(an integer) (even). -/
theorem no_KS_noncoloring : ¬ ∃ f : Fin 18 → ℕ, IsKSNoncoloring f := by
  rintro ⟨f, _hf01, hf⟩
  -- Sum-of-ones in each tetrad gives 9 overall.
  have h9 : (∑ t : Fin 9, ∑ v ∈ cabelloTetrad t, f v) = 9 := by
    have : (∑ t : Fin 9, ∑ v ∈ cabelloTetrad t, f v) = ∑ _t : Fin 9, 1 :=
      Finset.sum_congr rfl (fun t _ => hf t)
    simpa using this
  -- Sum-swap: same expression = Σ_v (#tetrads ∋ v) · f v.
  have hswap := sum_over_tetrads_eq_multiplicity f
  -- Each vector is in exactly 2 tetrads, so it equals 2 · Σ_v f v.
  have heven :
      (∑ v : Fin 18,
        ((Finset.univ : Finset (Fin 9)).filter
          (fun t => v ∈ cabelloTetrad t)).card * f v)
        = 2 * ∑ v : Fin 18, f v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [cabelloVector_in_exactly_two_tetrads v]
  -- Combine: 9 = 2 · (Σ f) — impossible.
  have hfinal : 9 = 2 * ∑ v : Fin 18, f v := by
    rw [← heven, ← hswap, h9]
  omega

/-! ## A clean restatement and small sanity checks. -/

/-- Restated headline: the Cabello configuration is **KS-uncolorable**. -/
theorem cabello_KS_uncolorable :
    ¬ ∃ f : Fin 18 → ℕ, IsKSNoncoloring f :=
  no_KS_noncoloring

/-- Sanity: each of the 18 Cabello vectors is nonzero. -/
theorem cabelloVector_ne_zero (i : Fin 18) :
    ∃ k : Fin 4, cabelloVector i k ≠ 0 := by
  fin_cases i
  all_goals first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩

/-! ## Axiom audit

The headline theorem `no_KS_noncoloring` depends only on the three Lean kernel
axioms `propext`, `Classical.choice`, `Quot.sound` — no custom `axiom`, no
`sorry`.  Uncomment the line below to verify locally:

```
#print axioms no_KS_noncoloring
-- 'no_KS_noncoloring' depends on axioms: [propext, Classical.choice, Quot.sound]
```
-/

end UnifiedTheory.LayerC.KochenSpecker18
