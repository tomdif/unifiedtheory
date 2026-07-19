/-
  UnifiedTheory/LayerC/SMBornRuleGeneralN.lean
  ───────────────────────────────────────────────

  **SM ↔ QM Bridge — Step S9 (Path B), general-n extension.**

  This file generalises `SMBornRuleReconciliation` (qubit / n = 2) to
  arbitrary finite Hilbert dimension `n` by working directly with a
  real-amplitude substrate state vector on `Fin n`.  In the qubit case
  the substrate is the K/P pair `(Q, P) ∈ ℝ²`; in the general case the
  substrate is a tuple `a : Fin n → ℝ` with `∑ᵢ aᵢ² = 1`, packaged as
  `SubstrateState n`.  This is the natural extension of the dressing-
  invariance argument to `n` channels: the substrate Born weight for
  outcome `i` is the squared amplitude `aᵢ²`, and the Hilbert-side Born
  weight `Re Tr(ρ · |i⟩⟨i|)` agrees by direct computation on the
  rank-1 density matrix `ρ = |ψ⟩⟨ψ|` with `|ψ⟩ = Σᵢ aᵢ |i⟩`.

  WHAT IS PROVEN (zero `sorry`, zero custom `axiom`):
    1. `SubstrateState n` — the real-amplitude tuple with the
       `∑ᵢ aᵢ² = 1` normalisation.
    2. `substrateVec`, `substrateRaw` — the state vector and the
       rank-1 density matrix `|ψ⟩⟨ψ|` on `Fin n`.
    3. Hermiticity (`substrateRaw_isHermitian`), PSD
       (`substrateRaw_posSemidef`), trace = `∑ᵢ aᵢ²`
       (`substrateRaw_trace`) and trace = 1 under normalisation
       (`substrateRaw_trace_one`).
    4. `substrateToDensityMatrix` — packaged `ComplexDensityMatrix n`.
    5. `computationalProjector` — the basis projector `|i⟩⟨i|`
       (via `Matrix.single`).
    6. `born_rule_general_n` — the headline equality
       `Re Tr(ρ · |i⟩⟨i|) = aᵢ²`.
    7. `born_rule_general_n_normalized` — the probabilities sum to 1.
    8. `sm_born_rule_general_n_bridge` — master bundle.

  HONEST SCOPE.  We work in the REAL-AMPLITUDE limit `ψᵢ = aᵢ` so the
  substrate-Hilbert dictionary is the literal identity.  The complex
  phase channel is the K/P split's dressing direction; here we collapse
  to the source-only sector to match the substrate's real-tuple shape.

  STANDING CONSTRAINT
    Zero `sorry`. Zero custom `axiom`.
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import UnifiedTheory.LayerB.PosetGrowthIsQuantum
import UnifiedTheory.LayerC.LocalRealisticAxioms
import UnifiedTheory.LayerC.SMBornRuleReconciliation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SMBornRuleGeneralN

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerC.LocalRealisticAxioms

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE SUBSTRATE STATE (REAL AMPLITUDES)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A substrate state on `n` levels: a tuple of real amplitudes with
    sum-of-squares equal to 1.  This is the general-n analogue of the
    qubit pair `(Q, P)` with `Q² + P² = 1` from
    `SMBornRuleReconciliation`. -/
structure SubstrateState (n : ℕ) where
  /-- The real-amplitude tuple. -/
  amp : Fin n → ℝ
  /-- Normalisation: `∑ᵢ aᵢ² = 1`. -/
  normalized : ∑ i, amp i ^ 2 = 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  THE STATE VECTOR `|ψ⟩ = Σᵢ aᵢ |i⟩`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The state vector `|ψ⟩ = Σᵢ aᵢ |i⟩` as a function `Fin n → ℂ`.
    Substrate amplitudes are real, lifted to ℂ. -/
noncomputable def substrateVec {n : ℕ} (s : SubstrateState n) : Fin n → ℂ :=
  fun i => (s.amp i : ℂ)

/-- Star of the state vector at `i` is just `(aᵢ : ℂ)` (real amplitude). -/
private lemma star_substrateVec {n : ℕ} (s : SubstrateState n) (i : Fin n) :
    star (substrateVec s i) = (s.amp i : ℂ) := by
  unfold substrateVec
  rw [Complex.star_def, Complex.conj_ofReal]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  THE RANK-1 DENSITY MATRIX `|ψ⟩⟨ψ|`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The rank-1 density matrix `|ψ⟩⟨ψ|` for `|ψ⟩ = Σᵢ aᵢ |i⟩`, as a raw
    `Matrix (Fin n) (Fin n) ℂ`.  Entry `(i,j)` is `aᵢ · aⱼ`. -/
noncomputable def substrateRaw {n : ℕ} (s : SubstrateState n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => substrateVec s i * star (substrateVec s j))

/-- Entry-wise expression for `substrateRaw`. -/
private lemma substrateRaw_apply {n : ℕ} (s : SubstrateState n) (i j : Fin n) :
    substrateRaw s i j = substrateVec s i * star (substrateVec s j) := rfl

/-- Explicit entry: `(substrateRaw s) i j = (aᵢ * aⱼ : ℂ)`. -/
private lemma substrateRaw_apply_real {n : ℕ} (s : SubstrateState n) (i j : Fin n) :
    substrateRaw s i j = ((s.amp i * s.amp j : ℝ) : ℂ) := by
  rw [substrateRaw_apply, star_substrateVec]
  show (s.amp i : ℂ) * (s.amp j : ℂ) = ((s.amp i * s.amp j : ℝ) : ℂ)
  push_cast
  ring

/-- Hermitian: `(|ψ⟩⟨ψ|)† = |ψ⟩⟨ψ|`. -/
theorem substrateRaw_isHermitian {n : ℕ} (s : SubstrateState n) :
    (substrateRaw s).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  rw [substrateRaw_apply, substrateRaw_apply]
  -- star (kpVec j * star (kpVec i)) = kpVec i * star (kpVec j)
  rw [show star (substrateVec s j * star (substrateVec s i))
        = star (star (substrateVec s i)) * star (substrateVec s j) from
          StarMul.star_mul _ _]
  rw [star_star]

/-- PSD: `substrateRaw = V · V†` where `V` is the column matrix of
    `substrateVec`. -/
theorem substrateRaw_posSemidef {n : ℕ} (s : SubstrateState n) :
    (substrateRaw s).PosSemidef := by
  set V : Matrix (Fin n) (Fin 1) ℂ := Matrix.replicateCol (Fin 1) (substrateVec s)
  have hVVdag : substrateRaw s = V * V.conjTranspose := by
    ext i j
    rw [substrateRaw_apply, Matrix.mul_apply, Fin.sum_univ_one]
    rw [Matrix.conjTranspose_apply]
    show substrateVec s i * star (substrateVec s j) = V i 0 * star (V j 0)
    simp [V, Matrix.replicateCol_apply]
  rw [hVVdag]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  TRACE OF THE RANK-1 DENSITY MATRIX
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The diagonal entry `(substrateRaw s) i i = ((aᵢ² : ℝ) : ℂ)`. -/
private lemma substrateRaw_diag {n : ℕ} (s : SubstrateState n) (i : Fin n) :
    substrateRaw s i i = ((s.amp i ^ 2 : ℝ) : ℂ) := by
  rw [substrateRaw_apply_real]
  push_cast
  ring

/-- Trace: `Tr(|ψ⟩⟨ψ|) = Σᵢ aᵢ²`. -/
theorem substrateRaw_trace {n : ℕ} (s : SubstrateState n) :
    (substrateRaw s).trace = (((∑ i, s.amp i ^ 2 : ℝ)) : ℂ) := by
  rw [Matrix.trace]
  -- Reduce: Σᵢ diag i = Σᵢ ((aᵢ² : ℝ) : ℂ) = ((Σᵢ aᵢ² : ℝ) : ℂ).
  simp only [Matrix.diag_apply]
  rw [show (fun i => substrateRaw s i i)
        = (fun i => ((s.amp i ^ 2 : ℝ) : ℂ)) from
          funext (fun i => substrateRaw_diag s i)]
  push_cast
  rfl

/-- Trace is 1 under the normalisation `∑ᵢ aᵢ² = 1`. -/
theorem substrateRaw_trace_one {n : ℕ} (s : SubstrateState n) :
    (substrateRaw s).trace = 1 := by
  rw [substrateRaw_trace, s.normalized]
  push_cast
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  PACKAGED `ComplexDensityMatrix n`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE SUBSTRATE → DENSITY-MATRIX MAP.**

    The substrate state `s : SubstrateState n` (real amplitudes with
    `∑ᵢ aᵢ² = 1`) lifts to the rank-1 density matrix `ρ = |ψ⟩⟨ψ|` for
    `|ψ⟩ = Σᵢ aᵢ |i⟩`, packaged as a `ComplexDensityMatrix n`.

    This is the BRIDGE OBJECT for the general-n substrate-Born /
    Hilbert-Born reconciliation. -/
noncomputable def substrateToDensityMatrix (n : ℕ) (s : SubstrateState n) :
    ComplexDensityMatrix n :=
  UnitaryQuantum.ofPosSemidef n
    (substrateRaw s)
    (substrateRaw_isHermitian s)
    (substrateRaw_trace_one s)
    (substrateRaw_posSemidef s)

/-- The underlying matrix of `substrateToDensityMatrix` is `substrateRaw`. -/
theorem substrateToDensityMatrix_M (n : ℕ) (s : SubstrateState n) :
    (substrateToDensityMatrix n s).M = substrateRaw s := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  COMPUTATIONAL-BASIS PROJECTOR `|i⟩⟨i|`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The computational-basis projector `|i⟩⟨i|` on `Fin n`, built as the
    standard-basis matrix with a `1` at position `(i, i)`. -/
noncomputable def computationalProjector (n : ℕ) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.single i i (1 : ℂ)

/-- Entry-wise expression: `(|i⟩⟨i|) k l = if (i = k ∧ i = l) then 1 else 0`.
    Note: matches Mathlib's `Matrix.single_apply` convention. -/
private lemma computationalProjector_apply {n : ℕ} (i k l : Fin n) :
    computationalProjector n i k l = if i = k ∧ i = l then (1 : ℂ) else 0 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7.  THE GENERAL-N BORN-RULE EQUALITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The product `substrateRaw s * computationalProjector n i` has only
    one non-zero column (column `i`), with entries `(k, i) ↦ aₖ · aᵢ`. -/
private lemma substrateRaw_mul_proj_apply {n : ℕ} (s : SubstrateState n)
    (i k l : Fin n) :
    (substrateRaw s * computationalProjector n i) k l
      = if i = l then substrateRaw s k i else 0 := by
  rw [Matrix.mul_apply]
  by_cases hl : i = l
  · -- l = i: Σⱼ substrateRaw s k j · proj j l. With l = i, only j = i contributes.
    rw [if_pos hl]
    rw [Finset.sum_eq_single i]
    · -- The j = i term: substrateRaw s k i · proj i l = substrateRaw s k i.
      rw [computationalProjector_apply]
      rw [if_pos ⟨rfl, hl⟩]
      ring
    · -- j ≠ i ⇒ proj j l = 0 (since i ≠ j as i = j would force the indicator).
      intro j _ hji
      rw [computationalProjector_apply]
      have : ¬ (i = j ∧ i = l) := fun h => hji h.1.symm
      rw [if_neg this]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  · -- l ≠ i: every proj j l = 0.
    rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro j _
    rw [computationalProjector_apply]
    have : ¬ (i = j ∧ i = l) := fun h => hl h.2
    rw [if_neg this]
    ring

/-- The diagonal entries of `substrateRaw s * computationalProjector n i`:
    only the `(i, i)` entry is non-zero, equal to `aᵢ²`. -/
private lemma substrateRaw_mul_proj_diag {n : ℕ} (s : SubstrateState n)
    (i k : Fin n) :
    (substrateRaw s * computationalProjector n i) k k
      = if k = i then ((s.amp i ^ 2 : ℝ) : ℂ) else 0 := by
  rw [substrateRaw_mul_proj_apply]
  by_cases hk : i = k
  · -- k = i
    have hk' : k = i := hk.symm
    rw [if_pos hk, if_pos hk', ← hk', substrateRaw_diag]
  · -- k ≠ i
    have hk' : ¬ k = i := fun h => hk h.symm
    rw [if_neg hk, if_neg hk']

/-- **TRACE FORMULA**: `Tr(substrateRaw s · |i⟩⟨i|) = (aᵢ² : ℂ)`. -/
theorem trace_substrate_mul_proj {n : ℕ} (s : SubstrateState n) (i : Fin n) :
    (substrateRaw s * computationalProjector n i).trace = ((s.amp i ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  -- Σ_k (substrateRaw s * proj) k k = Σ_k (if k = i then (aᵢ² : ℂ) else 0)
  rw [show (fun k => (substrateRaw s * computationalProjector n i) k k)
        = (fun k => if k = i then ((s.amp i ^ 2 : ℝ) : ℂ) else 0) from
          funext (fun k => substrateRaw_mul_proj_diag s i k)]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ => ((s.amp i ^ 2 : ℝ) : ℂ))]
  rw [if_pos (Finset.mem_univ i)]

/-- **GENERAL-N BORN-RULE EQUALITY.**

    For any substrate state `s : SubstrateState n` and any computational
    basis index `i : Fin n`:

        Re Tr(ρ · |i⟩⟨i|) = aᵢ²

    where `ρ = substrateToDensityMatrix n s`.  The right-hand side
    `aᵢ²` is exactly the substrate-derived Born weight for outcome `i`
    (the direct generalisation of the qubit `Q²` / `P²` formulas in
    `SMBornRuleReconciliation`). -/
theorem born_rule_general_n {n : ℕ} [NeZero n]
    (s : SubstrateState n) (i : Fin n) :
    ((substrateToDensityMatrix n s).M * computationalProjector n i).trace.re
      = (s.amp i) ^ 2 := by
  rw [substrateToDensityMatrix_M, trace_substrate_mul_proj]
  exact Complex.ofReal_re ((s.amp i) ^ 2)

/-- **PROBABILITIES SUM TO 1.** -/
theorem born_rule_general_n_normalized {n : ℕ} [NeZero n]
    (s : SubstrateState n) :
    ∑ i, ((substrateToDensityMatrix n s).M * computationalProjector n i).trace.re = 1 := by
  rw [show (fun i => ((substrateToDensityMatrix n s).M
                        * computationalProjector n i).trace.re)
        = (fun i => (s.amp i) ^ 2) from
          funext (fun i => born_rule_general_n s i)]
  exact s.normalized

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8.  THE GENERAL-N MASTER STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER BRIDGE (Step S9, Path B): general-n Born-rule reconciliation.**

    Bundles the per-outcome Born equality and the normalisation
    identity into a single citable statement.  For any normalised real
    substrate amplitude tuple `s : SubstrateState n` and the lifted
    density matrix `ρ = substrateToDensityMatrix n s`:

      • PER-OUTCOME:    Hilbert weight `Re Tr(ρ · |i⟩⟨i|) = aᵢ²`
                        matches the substrate-derived squared amplitude.
      • NORMALISATION:  `∑ᵢ aᵢ² = 1` ⇒ probabilities sum to 1.

    This is the direct generalisation of the qubit case S9
    `sm_born_rule_bridge_S9` (which is `n = 2`) to arbitrary finite
    Hilbert dimension `n`. -/
theorem sm_born_rule_general_n_bridge {n : ℕ} [NeZero n]
    (s : SubstrateState n) :
    (∀ i, ((substrateToDensityMatrix n s).M * computationalProjector n i).trace.re
            = (s.amp i) ^ 2)
    ∧ (∑ i, ((substrateToDensityMatrix n s).M
                * computationalProjector n i).trace.re = 1) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact born_rule_general_n s i
  · exact born_rule_general_n_normalized s

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9.  COMPATIBILITY WITH THE QUBIT CASE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The qubit reconciliation `born_rule_reconciliation_qubit` from
    `SMBornRuleReconciliation` is the `n = 2` instance of
    `sm_born_rule_general_n_bridge` applied to the substrate state
    `(Q, P)` packaged via `qubitSubstrate`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Package a normalised real pair `(Q, P)` as a `SubstrateState 2`. -/
noncomputable def qubitSubstrate (Q P : ℝ) (h : Q^2 + P^2 = 1) : SubstrateState 2 where
  amp := fun i => if i = 0 then Q else P
  normalized := by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    -- (if 0 = 0 then Q else P)^2 + (if 1 = 0 then Q else P)^2
    simp
    exact h

/-- The qubit substrate has `amp 0 = Q`. -/
@[simp] theorem qubitSubstrate_amp_zero (Q P : ℝ) (h : Q^2 + P^2 = 1) :
    (qubitSubstrate Q P h).amp 0 = Q := by
  unfold qubitSubstrate
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]

/-- The qubit substrate has `amp 1 = P`. -/
@[simp] theorem qubitSubstrate_amp_one (Q P : ℝ) (h : Q^2 + P^2 = 1) :
    (qubitSubstrate Q P h).amp 1 = P := by
  unfold qubitSubstrate
  rfl

/-- **Compatibility (outcome 0).**  The general-n Born rule at `n = 2`,
    outcome `0`, recovers the qubit weight `Q²`. -/
theorem born_rule_qubit_compat_outcome_0 (Q P : ℝ) (h : Q^2 + P^2 = 1) :
    ((substrateToDensityMatrix 2 (qubitSubstrate Q P h)).M
        * computationalProjector 2 0).trace.re = Q^2 := by
  rw [born_rule_general_n (qubitSubstrate Q P h) 0,
      qubitSubstrate_amp_zero]

/-- **Compatibility (outcome 1).**  The general-n Born rule at `n = 2`,
    outcome `1`, recovers the qubit weight `P²`. -/
theorem born_rule_qubit_compat_outcome_1 (Q P : ℝ) (h : Q^2 + P^2 = 1) :
    ((substrateToDensityMatrix 2 (qubitSubstrate Q P h)).M
        * computationalProjector 2 1).trace.re = P^2 := by
  rw [born_rule_general_n (qubitSubstrate Q P h) 1,
      qubitSubstrate_amp_one]

end UnifiedTheory.LayerC.SMBornRuleGeneralN
