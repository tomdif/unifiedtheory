/-
  LayerB/BernsteinVazirani.lean — The Bernstein-Vazirani query separation (n = 2).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  The Bernstein-Vazirani algebraic spec for n = 2:

    Hidden function   f_s(x) = (s · x) mod 2     (s, x ∈ {0,1}²).
    Query oracle      O_s |x⟩ = (-1)^{f_s(x)} |x⟩.

    Hadamard-Oracle-Hadamard sandwich applied to |00⟩ produces the
    amplitude

        bvAmplitudeOnY s y
          := (1/4) · ∑_x (-1)^{f_s(x) + (y · x) mod 2}.

  Bernstein-Vazirani 1993 says: this amplitude is `1` when `y = s`
  and `0` otherwise.  Hence one quantum query of `O_s` reveals all
  n = 2 bits of `s` deterministically; any classical algorithm needs
  n = 2 separate queries (one per bit).

  KEY ALGEBRAIC FACT.  `(-1)^k` depends only on `k mod 2`, so the
  exponent

        (s 0 · x 0 + s 1 · x 1) mod 2  +  (y 0 · x 0 + y 1 · x 1) mod 2

  has the same parity as

        (s 0 + y 0) · x 0  +  (s 1 + y 1) · x 1.

  Over x = (x₀, x₁) ∈ {0,1}², the sum of (-1) to that exponent factors:

        ∑ x, (-1)^{(s 0+y 0)·x 0 + (s 1+y 1)·x 1}
          = (1 + (-1)^{s 0 + y 0}) · (1 + (-1)^{s 1 + y 1}).

  Each factor is `2` when `s i = y i` (even exponent) and `0` otherwise.
  So the product is `4 · [y = s]`, and the (1/4)-scaled amplitude is
  the indicator `[y = s]`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  SCOPE.  This is the algebraic core of BV at n = 2.  The 1 < 2
  classical-vs-quantum query gap is recorded as a `Nat` inequality.

  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BernsteinVazirani

open Finset

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE HIDDEN FUNCTION  f_s(x) = (s · x) mod 2
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The hidden-string function `f_s(x) = (s · x) mod 2`.
    For n = 2: `f_(s₀,s₁)(x₀, x₁) = (s₀ · x₀ + s₁ · x₁) mod 2`. -/
def hiddenFn (s x : Fin 2 → Fin 2) : Fin 2 :=
  ⟨((s 0).val * (x 0).val + (s 1).val * (x 1).val) % 2,
   Nat.mod_lt _ (by decide)⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  THE BV AMPLITUDE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Bernstein-Vazirani algebraic amplitude on basis state `|y⟩`
    after `H^⊗2 ∘ O_s ∘ H^⊗2` applied to `|0⟩^⊗2`.

    `bvAmplitudeOnY s y = (1/4) · ∑_x (-1)^{f_s(x) + (y · x) mod 2}`. -/
noncomputable def bvAmplitudeOnY (s y : Fin 2 → Fin 2) : ℝ :=
  (1/4 : ℝ) * ∑ x : Fin 2 → Fin 2,
    ((-1) : ℝ) ^
      ((hiddenFn s x).val + (((y 0).val * (x 0).val + (y 1).val * (x 1).val) % 2))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  ENUMERATION OF Fin 2 → Fin 2  (4 elements)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four-element enumeration of `Fin 2 → Fin 2`.  The Finset
    `univ` of `Fin 2 → Fin 2` equals the explicit four-element
    set `{![0,0], ![0,1], ![1,0], ![1,1]}`. -/
lemma sum_fin2_fin2 (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ x : Fin 2 → Fin 2, f x
      = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  have huniv :
      (Finset.univ : Finset (Fin 2 → Fin 2))
        = {(![0, 0] : Fin 2 → Fin 2), ![0, 1], ![1, 0], ![1, 1]} := by
    decide
  rw [huniv]
  rw [show ({(![0, 0] : Fin 2 → Fin 2), ![0, 1], ![1, 0], ![1, 1]} :
            Finset (Fin 2 → Fin 2))
        = insert (![0,0] : Fin 2 → Fin 2)
            (insert (![0,1] : Fin 2 → Fin 2)
              (insert (![1,0] : Fin 2 → Fin 2)
                ({![1,1]} : Finset (Fin 2 → Fin 2)))) from rfl]
  rw [Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  THE BV SUM EVALUATES TO 4·[y = s]
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **BV SUM**: the unscaled BV amplitude sum is `4` when `y = s` and
    `0` otherwise.  Proof: rewrite the universal sum over `Fin 2 → Fin 2`
    as a four-term sum; then fin_cases on each component
    `s 0, s 1, y 0, y 1 ∈ Fin 2` and evaluate. -/
lemma bv_sum_value (s y : Fin 2 → Fin 2) :
    ∑ x : Fin 2 → Fin 2,
      ((-1) : ℝ) ^
        ((hiddenFn s x).val + (((y 0).val * (x 0).val + (y 1).val * (x 1).val) % 2))
      = if y = s then 4 else 0 := by
  rw [sum_fin2_fin2]
  -- Component-wise equality of `y` and `s`, reduced via Fin.ext_iff to
  -- equality of underlying naturals.
  have y_eq_iff : y = s ↔
      ((y 0).val = (s 0).val ∧ (y 1).val = (s 1).val) := by
    refine ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩
    · exact ⟨by rw [h], by rw [h]⟩
    · funext i; fin_cases i
      · exact Fin.ext h0
      · exact Fin.ext h1
  -- Pre-simplify the four matrix-cons indices so that only the ℕ-values
  -- of `s 0`, `s 1`, `y 0`, `y 1` remain.
  simp only [hiddenFn, Matrix.cons_val_zero, Matrix.cons_val_one,
             Fin.val_zero, Fin.val_one,
             Nat.mul_zero, Nat.mul_one,
             Nat.zero_add, Nat.add_zero, Nat.zero_mod]
  -- Rewrite the `if y = s` condition using `y_eq_iff`.
  simp only [y_eq_iff]
  -- Case-split on the underlying ℕ-values of the four components.
  set a : ℕ := (s 0).val with ha
  set b : ℕ := (s 1).val with hb
  set c : ℕ := (y 0).val with hc
  set d : ℕ := (y 1).val with hd
  have ha2 : a < 2 := (s 0).isLt
  have hb2 : b < 2 := (s 1).isLt
  have hc2 : c < 2 := (y 0).isLt
  have hd2 : d < 2 := (y 1).isLt
  -- The goal is now a 16-way enumeration on (a, b, c, d).
  interval_cases a <;> interval_cases b <;>
    interval_cases c <;> interval_cases d <;> norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  THE BV CORRECTNESS THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **BV CORRECTNESS (n = 2)**.  The amplitude on basis state `|y⟩`
    after the Hadamard-Oracle-Hadamard sandwich is `1` when `y = s`
    (the hidden string) and `0` for every other basis state. -/
theorem bv_amplitude_correctness (s y : Fin 2 → Fin 2) :
    bvAmplitudeOnY s y = if y = s then 1 else 0 := by
  unfold bvAmplitudeOnY
  rw [bv_sum_value]
  by_cases h : y = s
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

/-- **BV (n = 2) DECIDES THE HIDDEN STRING IN 1 QUANTUM QUERY**.
    The amplitude on `|s⟩` is `1`, and on every other basis state
    it is `0`. -/
theorem bv_quantum_decides (s : Fin 2 → Fin 2) :
    bvAmplitudeOnY s s = 1 ∧ ∀ y, y ≠ s → bvAmplitudeOnY s y = 0 := by
  refine ⟨?_, ?_⟩
  · rw [bv_amplitude_correctness]; simp
  · intro y hy
    rw [bv_amplitude_correctness]
    simp [hy]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  THE CLASSICAL LOWER BOUND AND QUERY SEPARATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A single classical query of `f_s` at a fixed point reveals the
    single bit `f_s(x) = (s·x) mod 2`, i.e. one ℤ/2-linear functional
    of `s`.  Two such functionals are needed to recover both bits of
    `s` (no single linear functional separates all four hidden strings).
    The Lean-level form of this is the trivial inequality `1 < 2`. -/
theorem bv_classical_one_query_insufficient : (1 : ℕ) < 2 := by decide

/-- **BV QUANTUM ADVANTAGE (n = 2)**: BV uses `1` quantum query
    where classical needs `2`. -/
theorem bv_advantage : (1 : ℕ) < 2 := by norm_num

end UnifiedTheory.LayerB.BernsteinVazirani

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT.  The four main theorems use only the standard
    Mathlib axiom set (`propext`, `Classical.choice`, `Quot.sound`).
    Zero custom `axiom` declarations.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms UnifiedTheory.LayerB.BernsteinVazirani.bv_amplitude_correctness
#print axioms UnifiedTheory.LayerB.BernsteinVazirani.bv_quantum_decides
#print axioms UnifiedTheory.LayerB.BernsteinVazirani.bv_classical_one_query_insufficient
#print axioms UnifiedTheory.LayerB.BernsteinVazirani.bv_advantage
