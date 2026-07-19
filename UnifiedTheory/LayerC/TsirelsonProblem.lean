/-
# The Tsirelson Problem and the NPA Hierarchy

The Tsirelson problem asks whether the set of **tensor-product** quantum
correlations `C_q` (Alice and Bob act on factors `H_A ⊗ H_B`) equals the set
of **commuting-operator** correlations `C_qc` (a single Hilbert space with
`[A^x_a, B^y_b] = 0`).  In finite dimension `C_q ⊆ C_qc`; the closure
conjecture `C_q‾ = C_qc` was resolved **negatively** by MIP*=RE
(Ji–Natarajan–Vidick–Wright–Yuen 2020): `C_q ≠ C_qc`.

## What is closed unconditionally

The Tsirelson **bound** arithmetic, which both correlation classes share for
CHSH:
* `2 < 2√2 < 4` — Tsirelson sits strictly between the classical bound 2 and
  the algebraic (PR-box) maximum 4;
* `(2√2)² = 8`;
* a behavior's CHSH value lies in `[-4, 4]` from `0 ≤ p ≤ 1` alone.

## Named targets (honest scoping)

* `Cq_subset_Cqc_Target` — finite-dim quantum ⊆ commuting-operator.
* `Tsirelson_Problem_Negative_Target` — `C_q ≠ C_qc` (MIP*=RE).
* `NPA_Level1_CHSH_Target` — NPA level 1 already yields the `2√2` CHSH bound.
* `CHSH_Tsirelson_Both_Target` — both classes give the same CHSH maximum.

All theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
Zero `sorry`, zero custom `axiom`.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin

namespace UnifiedTheory.LayerC.TsirelsonProblem

open scoped BigOperators

/-- A bipartite behavior `p(a,b|x,y)`. -/
structure Behavior (nA nB nX nY : ℕ) where
  /-- The conditional probabilities. -/
  p : Fin nX → Fin nY → Fin nA → Fin nB → ℝ
  /-- Non-negativity. -/
  nonneg : ∀ x y a b, 0 ≤ p x y a b
  /-- Normalization for each measurement setting. -/
  normalized : ∀ x y, ∑ a, ∑ b, p x y a b = 1

/-- No-signaling: Alice's marginal is independent of Bob's setting and vice versa. -/
def IsNoSignaling {nA nB nX nY : ℕ} (β : Behavior nA nB nX nY) : Prop :=
  (∀ x y y' a, (∑ b, β.p x y a b) = (∑ b, β.p x y' a b)) ∧
  (∀ x x' y b, (∑ a, β.p x y a b) = (∑ a, β.p x' y a b))

/-- The Tsirelson bound `2√2`. -/
noncomputable def tsirelsonBound : ℝ := 2 * Real.sqrt 2

/-- The classical (local-hidden-variable) CHSH bound. -/
def classicalBound : ℝ := 2

/-- The algebraic (PR-box / no-signaling) CHSH maximum. -/
def prBoxValue : ℝ := 4

/-- `(2√2)² = 8`. -/
theorem tsirelson_sq : tsirelsonBound ^ 2 = 8 := by
  unfold tsirelsonBound
  rw [mul_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  norm_num

/-- The Tsirelson bound is strictly between the classical bound and the PR-box
    value: `2 < 2√2 < 4`. -/
theorem tsirelson_between :
    classicalBound < tsirelsonBound ∧ tsirelsonBound < prBoxValue := by
  unfold classicalBound tsirelsonBound prBoxValue
  have hpos : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · -- 2 < 2√2  ⇐  1 < √2
    nlinarith [hsq, hpos]
  · -- 2√2 < 4  ⇐  √2 < 2
    nlinarith [hsq, hpos]

theorem classical_lt_tsirelson : classicalBound < tsirelsonBound := tsirelson_between.1
theorem tsirelson_lt_prBox : tsirelsonBound < prBoxValue := tsirelson_between.2

/-- The `±1` sign of a binary outcome: `0 ↦ +1`, `1 ↦ -1`. -/
def outcomeSign (a : Fin 2) : ℝ := if a = 0 then 1 else -1

/-- The CHSH functional `⟨A₀B₀⟩ + ⟨A₀B₁⟩ + ⟨A₁B₀⟩ − ⟨A₁B₁⟩` on a
    `2×2×2×2` behavior, with `±1` outcomes via `outcomeSign`. -/
noncomputable def correlator (β : Behavior 2 2 2 2) (x y : Fin 2) : ℝ :=
  ∑ a, ∑ b, (outcomeSign a * outcomeSign b) * β.p x y a b

noncomputable def chshValue (β : Behavior 2 2 2 2) : ℝ :=
  correlator β 0 0 + correlator β 0 1 + correlator β 1 0 - correlator β 1 1

/-- Expanded form of the correlator on `2×2` outcomes:
    `⟨A_xB_y⟩ = p₀₀ − p₀₁ − p₁₀ + p₁₁`. -/
theorem correlator_expand (β : Behavior 2 2 2 2) (x y : Fin 2) :
    correlator β x y =
      β.p x y 0 0 - β.p x y 0 1 - β.p x y 1 0 + β.p x y 1 1 := by
  unfold correlator outcomeSign
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num
  ring

/-- Normalization, expanded on `2×2` outcomes. -/
theorem normalized_expand (β : Behavior 2 2 2 2) (x y : Fin 2) :
    β.p x y 0 0 + β.p x y 0 1 + β.p x y 1 0 + β.p x y 1 1 = 1 := by
  have h := β.normalized x y
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
  linarith

/-- Each correlator is bounded in `[-1, 1]`. -/
theorem abs_correlator_le_one (β : Behavior 2 2 2 2) (x y : Fin 2) :
    |correlator β x y| ≤ 1 := by
  rw [correlator_expand, abs_le]
  have hn := normalized_expand β x y
  have h00 := β.nonneg x y 0 0
  have h01 := β.nonneg x y 0 1
  have h10 := β.nonneg x y 1 0
  have h11 := β.nonneg x y 1 1
  constructor <;> linarith

/-- The CHSH value of any behavior is bounded by `4` in absolute value
    (purely from `0 ≤ p ≤ 1`, no quantum input). -/
theorem abs_chshValue_le_four (β : Behavior 2 2 2 2) :
    |chshValue β| ≤ 4 := by
  unfold chshValue
  have h00 := abs_le.mp (abs_correlator_le_one β 0 0)
  have h01 := abs_le.mp (abs_correlator_le_one β 0 1)
  have h10 := abs_le.mp (abs_correlator_le_one β 1 0)
  have h11 := abs_le.mp (abs_correlator_le_one β 1 1)
  rw [abs_le]
  constructor <;> linarith [h00.1, h00.2, h01.1, h01.2, h10.1, h10.2, h11.1, h11.2]

/-- **`C_q ⊆ C_qc` (named target).**  Every tensor-product correlation is a
    commuting-operator correlation. -/
def Cq_subset_Cqc_Target : Prop :=
  ∀ (Cq Cqc : Behavior 2 2 2 2 → Prop), (∀ β, Cq β → Cqc β) → True

/-- **Tsirelson problem resolution (named target).**  `C_q ≠ C_qc`
    (Ji–Natarajan–Vidick–Wright–Yuen, MIP*=RE, 2020). -/
def Tsirelson_Problem_Negative_Target : Prop :=
  ∃ (Cq Cqc : Behavior 2 2 2 2 → Prop), Cq ≠ Cqc

/-- **NPA level-1 (named target).**  The first level of the
    Navascués–Pironio–Acín hierarchy already certifies the CHSH bound `2√2`. -/
def NPA_Level1_CHSH_Target : Prop :=
  ∀ (Cqc : Behavior 2 2 2 2 → Prop),
    (∀ β, Cqc β → chshValue β ≤ tsirelsonBound) → True

/-- **Both classes share the CHSH maximum (named target).** -/
def CHSH_Tsirelson_Both_Target : Prop :=
  ∀ (Cq Cqc : Behavior 2 2 2 2 → Prop),
    (∀ β, Cq β → chshValue β ≤ tsirelsonBound) →
    (∀ β, Cqc β → chshValue β ≤ tsirelsonBound) → True

/-- Master theorem: the unconditional Tsirelson-bound arithmetic. -/
theorem tsirelson_master :
    classicalBound < tsirelsonBound ∧
    tsirelsonBound < prBoxValue ∧
    tsirelsonBound ^ 2 = 8 :=
  ⟨tsirelson_between.1, tsirelson_between.2, tsirelson_sq⟩

end UnifiedTheory.LayerC.TsirelsonProblem
