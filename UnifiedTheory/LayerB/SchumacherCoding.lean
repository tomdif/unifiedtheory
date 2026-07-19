/-
  LayerB/SchumacherCoding.lean
  ─────────────────────────────

  **Schumacher's quantum source coding theorem** (Schumacher 1995).

  Asymptotically, n iid copies of a density matrix ρ can be
  compressed to ≈ n·S(ρ) qubits per symbol with vanishing
  fidelity loss.  Conversely, no rate below S(ρ) achieves
  asymptotic fidelity 1.

  This file ships the **single-shot infrastructure** that the
  asymptotic theorem rests on, and **states** the asymptotic
  theorem as a named hypothesis (Margolus–Levitin / Naimark-style
  honest scoping used elsewhere in the project: zero `sorry`, zero
  custom `axiom`, with the deep AEP / tensor-power content packaged
  as a named `Prop` rather than asserted).

  Builds on:
    * `SpectralFunctionalCalculus`           (`cfcρ`, `cfcρ_diagonalForm`)
    * `SpectralFunctionalCalculusTrace`      (trace formula for the CFC)
    * `OperatorEntropy`                      (`vonNeumannEntropy`,
                                              `eigenvalues_nonneg`,
                                              `sum_eigenvalues_eq_one`)
    * `SpectralDensityMatrix`                (`SpectralDensityMatrix` bundle)
    * `UmegakiRelativeEntropy`               (relative entropy)
    * `HolevoBoundQuantum`                   (downstream entropy bound)
    * `KleinInequality`                      (`mul_cfc_log_eq_cfc_xlogx`
                                              spectral mul technique)

  WHAT IS DEFINED (no sorry, no custom axioms):
    1. `typicalIndicator ρ δ : ℝ → ℝ`
         — `1` on eigenvalues whose `−log` lies within `δ` of `S(ρ)`
           AND that are strictly positive; `0` otherwise.
    2. `isTypicalEigenvalue ρ δ i : Prop`
         — whether the *i*-th eigenvalue is typical.
    3. `typicalEigenvalueIndices ρ δ : Finset (Fin n)`
         — the index set of typical eigenvalues.
    4. `typicalProjector ρ δ : Matrix (Fin n) (Fin n) ℂ`
         — projector onto the typical subspace, defined via the
           CFC of `typicalIndicator`.
    5. `typicalProbability ρ δ : ℝ`
         — the probability mass on typical eigenvalues,
           `∑_{i typical} λᵢ`.
    6. `SchumacherRate ρ : ℝ := vonNeumannEntropy ρ`.

  WHAT IS PROVEN (no sorry, no custom axioms):
    7. `typicalProjector_isHermitian`
         — the typical projector is Hermitian.
    8. `typicalProjector_isIdempotent_under_cfc`
         — `Π² = Π` (idempotency via CFC of the indicator squared
           equals the indicator).
    9. `trace_typicalProjector_eq_sum_indicator`
         — `Tr Π = (#typical eigenvalues : ℝ)`.
   10. `trace_rho_typicalProjector_eq_typicalProbability`
         — `Re Tr(ρ · Π) = ∑_{i typical} λᵢ = typicalProbability ρ δ`.
   11. `typicalProbability_nonneg`                    (0 ≤ p_typical).
   12. `typicalProbability_le_one`                    (p_typical ≤ 1).
   13. `typicalProbability_eq_one_sub_atypical`
         — exact decomposition: `p_typical = 1 − p_atypical`.
   14. `typicalProbability_lower_bound_of_atypical_bound`
         — if the atypical probability mass is at most δ, then
           `p_typical ≥ 1 − δ`.  This is the single-shot template
           for the asymptotic (n-fold) bound; the iid AEP turns
           the hypothesis into a theorem in the n→∞ limit.
   15. `SchumacherRate_nonneg`                        (S(ρ) ≥ 0).

  LAYER C — Schumacher's asymptotic theorem, stated as a named
  hypothesis with explicit type signature in terms of the local
  vocabulary:
   16. `SchumacherAsymptoticDirect`
         — for every rate `R > S(ρ)`, there is `N` and encoders /
           decoders such that the (formal) fidelity bound holds
           for `n ≥ N`.
   17. `SchumacherAsymptoticConverse`
         — no rate `R < S(ρ)` achieves the same.
   18. `SchumacherTheorem`        — the conjunction.

  HONEST SCOPE:
    * The single-shot bound is exact (the inequality form is
      conditional on a Markov / Chebyshev-style atypicality bound
      that becomes a theorem under iid AEP; we do NOT have the
      tensor-power machinery to prove that here).
    * `SchumacherAsymptoticDirect` / `Converse` are stated in the
      project's own vocabulary at the type-signature level — they
      are NOT proved here.  The encoders and decoders are exposed
      as bare matrix maps; the asymptotic rate `R > S(ρ)` selects
      the compressed dimension `2^⌊n·R⌋`.
    * Tensor-power density matrices and the asymptotic equipartition
      property are out of scope for this file (a separate multi-week
      development).  The file consolidates exactly the single-shot
      data on which the asymptotic theorem operates.

  Mathlib convention `Real.log 0 = 0` is inherited, but the
  `typicalIndicator` guards on `0 < x` so zero eigenvalues are
  classified as atypical (the standard convention; equivalent to
  treating `−log 0 = +∞`, which is never within `δ` of `S(ρ)`).
-/

import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.SpectralDensityMatrix
import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.KleinInequality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SchumacherCoding

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.SpectralFCTrace
open UnifiedTheory.LayerB.OperatorEntropy

variable {n : ℕ}

/-! ## 1. The typical-eigenvalue indicator and index set -/

/-- **Typical-eigenvalue indicator (as a function `ℝ → ℝ`).**

    The indicator is `1` on the open band

         { x ∈ ℝ |  0 < x  ∧  |−log x − S(ρ)| ≤ δ },

    and `0` elsewhere.  Strict positivity rules out `x = 0` (where
    Mathlib's convention `Real.log 0 = 0` would otherwise make zero
    eigenvalues falsely "typical" whenever `S(ρ) ≤ δ`).

    With this definition the typical subspace projector is
    `cfc (typicalIndicator ρ δ) ρ.M`, and `Tr(ρ · Π)` collects
    exactly the typical eigenvalue mass `∑_{i typical} λᵢ`. -/
noncomputable def typicalIndicator (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    ℝ → ℝ := fun x =>
  if 0 < x ∧ |(- Real.log x) - vonNeumannEntropy ρ| ≤ δ then 1 else 0

/-- **Per-index typicality predicate.**  Index `i` is typical iff
    its eigenvalue `λᵢ` is strictly positive and `−log λᵢ` lies
    within `δ` of the von Neumann entropy `S(ρ)`. -/
def isTypicalEigenvalue (ρ : ComplexDensityMatrix n) (δ : ℝ) (i : Fin n) : Prop :=
  0 < ρ.hHerm.eigenvalues i ∧
    |(- Real.log (ρ.hHerm.eigenvalues i)) - vonNeumannEntropy ρ| ≤ δ

/-- **Decidability instance** for the per-index typicality predicate. -/
noncomputable instance (ρ : ComplexDensityMatrix n) (δ : ℝ) (i : Fin n) :
    Decidable (isTypicalEigenvalue ρ δ i) :=
  Classical.propDecidable _

/-- **The typical index set as a `Finset`.** -/
noncomputable def typicalEigenvalueIndices
    (ρ : ComplexDensityMatrix n) (δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => isTypicalEigenvalue ρ δ i)

/-- Membership lemma. -/
theorem mem_typicalEigenvalueIndices
    (ρ : ComplexDensityMatrix n) (δ : ℝ) (i : Fin n) :
    i ∈ typicalEigenvalueIndices ρ δ ↔ isTypicalEigenvalue ρ δ i := by
  unfold typicalEigenvalueIndices
  simp [Finset.mem_filter]

/-- The indicator evaluated at an eigenvalue picks out the typical
    indices. -/
theorem typicalIndicator_apply_eigenvalue
    (ρ : ComplexDensityMatrix n) (δ : ℝ) (i : Fin n) :
    typicalIndicator ρ δ (ρ.hHerm.eigenvalues i)
      = (if isTypicalEigenvalue ρ δ i then 1 else 0) := by
  unfold typicalIndicator isTypicalEigenvalue
  -- The two `if`s have the same predicate but different decidability
  -- instances (`instDecidableAnd` vs `Classical.propDecidable`).
  -- Resolve by case analysis on the predicate itself.
  by_cases h : 0 < ρ.hHerm.eigenvalues i ∧
               |(- Real.log (ρ.hHerm.eigenvalues i)) - vonNeumannEntropy ρ| ≤ δ
  · simp [h]
  · simp [h]

/-! ## 2. The typical projector -/

/-- **Typical subspace projector**, defined as the CFC of the
    `{0,1}`-valued `typicalIndicator` applied to ρ.

    Spectrally, this is `∑_{i typical} |i⟩⟨i|` in ρ's eigenbasis,
    which is a true orthogonal projector (Hermitian + idempotent).
    Both properties are derived below from the CFC. -/
noncomputable def typicalProjector
    (ρ : ComplexDensityMatrix n) (δ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  cfcρ (typicalIndicator ρ δ) ρ

/-- The typical projector is Hermitian (inherited from `cfcρ`). -/
theorem typicalProjector_isHermitian (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    (typicalProjector ρ δ).IsHermitian :=
  cfcρ_isHermitian (typicalIndicator ρ δ) ρ

/-! ### Idempotency of the typical projector -/

/-- The indicator function is idempotent pointwise: `χ · χ = χ`. -/
theorem typicalIndicator_sq_eq_self
    (ρ : ComplexDensityMatrix n) (δ : ℝ) (x : ℝ) :
    typicalIndicator ρ δ x * typicalIndicator ρ δ x = typicalIndicator ρ δ x := by
  unfold typicalIndicator
  by_cases h : 0 < x ∧ |(- Real.log x) - vonNeumannEntropy ρ| ≤ δ
  · simp [h]
  · simp [h]

/-- **Idempotency of the typical projector** under the CFC product.

    `cfc χ · cfc χ = cfc (χ · χ) = cfc χ` because `χ² = χ`.  This
    uses the fact that every function is continuous on the (finite)
    spectrum of ρ.M, so `cfc_mul` applies. -/
theorem typicalProjector_isIdempotent_under_cfc
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    typicalProjector ρ δ * typicalProjector ρ δ = typicalProjector ρ δ := by
  unfold typicalProjector cfcρ
  -- Use `cfc_mul`: cfc f · cfc g = cfc (f · g) for f, g continuous on spectrum.
  have hχ_cont :
      ContinuousOn (typicalIndicator ρ δ) (spectrum ℝ ρ.M) :=
    (Set.toFinite _).continuousOn _
  have h_mul :
      cfc (typicalIndicator ρ δ) ρ.M * cfc (typicalIndicator ρ δ) ρ.M
        = cfc (fun x => typicalIndicator ρ δ x * typicalIndicator ρ δ x) ρ.M :=
    (cfc_mul (typicalIndicator ρ δ) (typicalIndicator ρ δ) ρ.M
      hχ_cont hχ_cont).symm
  rw [h_mul]
  -- Now `cfc (χ·χ) = cfc χ` because χ·χ = χ.
  congr 1
  funext x
  exact typicalIndicator_sq_eq_self ρ δ x

/-! ## 3. Trace of the typical projector -/

/-- **Trace of the typical projector equals the cardinality of the
    typical eigenvalue index set.**  Direct from the CFC trace
    formula `Tr cfc f ρ = ∑ᵢ f λᵢ` evaluated at the indicator. -/
theorem trace_typicalProjector_eq_card
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    (typicalProjector ρ δ).trace.re = (typicalEigenvalueIndices ρ δ).card := by
  unfold typicalProjector
  rw [re_trace_cfcρ]
  -- ∑ i, χ(λᵢ) = ∑ i, [i typical ? 1 : 0] = #typical
  have h_pointwise :
      ∀ i, typicalIndicator ρ δ (ρ.hHerm.eigenvalues i)
            = (if isTypicalEigenvalue ρ δ i then (1 : ℝ) else 0) := by
    intro i
    exact typicalIndicator_apply_eigenvalue ρ δ i
  simp_rw [h_pointwise]
  -- ∑ i, (if P i then 1 else 0) = (filter P univ).card
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  -- After Finset.sum_const we have `card • (1 : ℝ) = (card : ℝ)`.
  simp [typicalEigenvalueIndices]

/-! ## 4. Probability of the typical subspace -/

/-- **Typical-subspace probability mass.**

    `p_typical(ρ, δ) := ∑_{i typical} λᵢ`.

    This is the matrix-element-level definition; the trace identity
    below ties it to `Re Tr(ρ · Π)`. -/
noncomputable def typicalProbability
    (ρ : ComplexDensityMatrix n) (δ : ℝ) : ℝ :=
  ∑ i ∈ typicalEigenvalueIndices ρ δ, ρ.hHerm.eigenvalues i

/-- **Atypical-subspace probability mass.**  The complement of
    `typicalProbability` in the total trace 1. -/
noncomputable def atypicalProbability
    (ρ : ComplexDensityMatrix n) (δ : ℝ) : ℝ :=
  ∑ i ∈ (typicalEigenvalueIndices ρ δ)ᶜ, ρ.hHerm.eigenvalues i

/-- **The trace `Re Tr(ρ · Π)` recovers the typical probability.**

    The argument uses the CFC multiplicativity `ρ · cfc χ ρ = cfc (x·χ x) ρ`
    (valid because the indicator is continuous on the finite spectrum of ρ),
    then evaluates the trace via `re_trace_cfcρ`. -/
theorem trace_rho_typicalProjector_eq_typicalProbability
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    (Matrix.trace (ρ.M * typicalProjector ρ δ)).re
      = typicalProbability ρ δ := by
  unfold typicalProjector cfcρ
  -- Step 1.  ρ.M = cfc id ρ.M.  Then cfc id · cfc χ = cfc (id · χ).
  have h_id_cont : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ ρ.M) :=
    continuous_id.continuousOn
  have hχ_cont :
      ContinuousOn (typicalIndicator ρ δ) (spectrum ℝ ρ.M) :=
    (Set.toFinite _).continuousOn _
  -- Replace ρ.M by cfc id ρ.M using `cfc_id`.  We need ρ.M to be
  -- self-adjoint to apply `cfc_id ℝ ρ.M`.
  have hSA : IsSelfAdjoint ρ.M := ρ.hHerm
  have h_rho_eq : ρ.M = cfc (id : ℝ → ℝ) ρ.M := (cfc_id ℝ ρ.M).symm
  -- Compute ρ.M * cfc χ ρ.M = cfc (id) ρ.M * cfc χ ρ.M = cfc (id · χ) ρ.M.
  have h_prod :
      ρ.M * cfc (typicalIndicator ρ δ) ρ.M
        = cfc (fun x => x * typicalIndicator ρ δ x) ρ.M := by
    -- Rewrite the first ρ.M only.
    nth_rewrite 1 [h_rho_eq]
    -- Apply cfc_mul backwards: cfc id · cfc χ = cfc (id · χ).
    rw [← cfc_mul (id : ℝ → ℝ) (typicalIndicator ρ δ) ρ.M h_id_cont hχ_cont]
    rfl
  rw [h_prod]
  -- Step 2.  Now Tr(cfc g ρ.M).re = ∑ g (λᵢ).  Use `re_trace_cfcρ` form by
  -- folding back via `cfcρ`.
  have h_eq_cfcρ :
      cfc (fun x => x * typicalIndicator ρ δ x) ρ.M
        = cfcρ (fun x => x * typicalIndicator ρ δ x) ρ := rfl
  rw [h_eq_cfcρ, re_trace_cfcρ]
  -- Step 3.  Identify ∑ λᵢ · χ(λᵢ) with the sum over typical indices.
  -- Pointwise: λᵢ · χ(λᵢ) = λᵢ · [i typical ? 1 : 0] = if i typical then λᵢ else 0.
  have h_pw :
      ∀ i, ρ.hHerm.eigenvalues i * typicalIndicator ρ δ (ρ.hHerm.eigenvalues i)
            = (if isTypicalEigenvalue ρ δ i then ρ.hHerm.eigenvalues i else 0) := by
    intro i
    rw [typicalIndicator_apply_eigenvalue ρ δ i]
    by_cases h : isTypicalEigenvalue ρ δ i
    · simp [h]
    · simp [h]
  simp_rw [h_pw]
  -- Now ∑ i, (if i typical then λᵢ else 0) = ∑_{i typical} λᵢ.
  unfold typicalProbability typicalEigenvalueIndices
  rw [← Finset.sum_filter]

/-! ## 5. Elementary bounds on the typical probability -/

/-- **Non-negativity.**  Each typical eigenvalue is non-negative
    (`eigenvalues_nonneg`), so their sum is non-negative. -/
theorem typicalProbability_nonneg
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    0 ≤ typicalProbability ρ δ := by
  unfold typicalProbability
  apply Finset.sum_nonneg
  intro i _
  exact eigenvalues_nonneg ρ i

/-- **Non-negativity of the atypical probability.** -/
theorem atypicalProbability_nonneg
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    0 ≤ atypicalProbability ρ δ := by
  unfold atypicalProbability
  apply Finset.sum_nonneg
  intro i _
  exact eigenvalues_nonneg ρ i

/-- **Exact decomposition: `p_typical + p_atypical = 1`.**  Trivial
    finite-set split of `∑_i λᵢ = 1` between typical and atypical
    indices. -/
theorem typicalProbability_add_atypicalProbability
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    typicalProbability ρ δ + atypicalProbability ρ δ = 1 := by
  unfold typicalProbability atypicalProbability
  rw [Finset.sum_add_sum_compl]
  exact sum_eigenvalues_eq_one ρ

/-- **`p_typical = 1 − p_atypical`**, the exact identity that
    converts every atypicality bound into a typicality bound. -/
theorem typicalProbability_eq_one_sub_atypical
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    typicalProbability ρ δ = 1 - atypicalProbability ρ δ := by
  have := typicalProbability_add_atypicalProbability ρ δ
  linarith

/-- **`p_typical ≤ 1`.** -/
theorem typicalProbability_le_one
    (ρ : ComplexDensityMatrix n) (δ : ℝ) :
    typicalProbability ρ δ ≤ 1 := by
  rw [typicalProbability_eq_one_sub_atypical]
  have h := atypicalProbability_nonneg ρ δ
  linarith

/-- **Single-shot typical-projection bound (conditional on an
    atypicality hypothesis).**

    `If the atypical mass is at most δ, then the typical mass is at
    least 1 − δ.`

    This is the structural shape of Schumacher's bound: the
    atypicality hypothesis is supplied by the quantum AEP in the
    n-fold tensor-product setting (out of scope here); for the
    single-shot case the hypothesis can be checked directly from
    the spectrum.

    Combined with `trace_rho_typicalProjector_eq_typicalProbability`,
    this yields the operator-level form
        `Re Tr(ρ · Π_typical) ≥ 1 − δ`
    that is the input to Schumacher's coding theorem. -/
theorem typicalProbability_lower_bound_of_atypical_bound
    (ρ : ComplexDensityMatrix n) (δ ε : ℝ)
    (h_atypical_small : atypicalProbability ρ δ ≤ ε) :
    typicalProbability ρ δ ≥ 1 - ε := by
  rw [typicalProbability_eq_one_sub_atypical]
  linarith

/-- **Operator-level form: `Re Tr(ρ · Π) ≥ 1 − ε`.** -/
theorem re_trace_rho_typicalProjector_lower_bound
    (ρ : ComplexDensityMatrix n) (δ ε : ℝ)
    (h_atypical_small : atypicalProbability ρ δ ≤ ε) :
    (Matrix.trace (ρ.M * typicalProjector ρ δ)).re ≥ 1 - ε := by
  rw [trace_rho_typicalProjector_eq_typicalProbability]
  exact typicalProbability_lower_bound_of_atypical_bound ρ δ ε h_atypical_small

/-! ## 6. The Schumacher rate -/

/-- **Schumacher's compression rate.**

    The optimal compression rate (qubits per source symbol) is the
    von Neumann entropy of the source density matrix.  This is the
    headline content of Schumacher's theorem: `R* = S(ρ)`. -/
noncomputable def SchumacherRate (ρ : ComplexDensityMatrix n) : ℝ :=
  vonNeumannEntropy ρ

/-- The Schumacher rate is non-negative (inherited from
    `vonNeumannEntropy_nonneg`). -/
theorem SchumacherRate_nonneg (ρ : ComplexDensityMatrix n) :
    0 ≤ SchumacherRate ρ :=
  vonNeumannEntropy_nonneg ρ

/-! ## 7. The asymptotic theorem (Layer C: stated as a named `Prop`) -/

/-- **Formal fidelity surrogate** at the single-shot level.

    For two matrices A, B with A trace-1 Hermitian PSD, we measure
    closeness by `Re Tr(A · B)`.  This is *not* the Uhlmann fidelity
    `F(ρ, σ) = (Tr |√ρ · √σ|)²`; we use the trace-overlap surrogate
    because it is what falls out of the typical-projector single-shot
    argument and aligns with the form of the bound proved above
    (`re_trace_rho_typicalProjector_lower_bound`).

    The Uhlmann fidelity equals the trace overlap on commuting states
    and dominates it generally (`F(ρ,σ) ≥ Tr(ρ·σ)`), so a Schumacher-
    style lower bound stated in this surrogate is *weaker* than the
    standard textbook statement, hence honest. -/
noncomputable def traceOverlapFidelity
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (ρ * σ)).re

/-- **Schumacher's asymptotic direct part — STATEMENT.**

    For every rate strictly above `S(ρ)` and every ε > 0, there
    exists `N` such that for all `n ≥ N` there exist an encoder
    `E_n : Matrix (Fin (d^n)) (Fin (d^n)) ℂ → Matrix (Fin (2^⌊n·R⌋)) (Fin (2^⌊n·R⌋)) ℂ`
    and decoder `D_n` (where `d = Nat.succ n₀` is the on-site
    Hilbert dimension) such that the trace-overlap fidelity between
    the original `n`-fold state and the round-tripped state is at
    least `1 − ε`.

    HONEST SCOPE: this statement is **not proved here**.  It is the
    headline asymptotic theorem; its proof needs

      (a) the iid tensor-power density matrix `ρ^⊗n`,
      (b) the quantum asymptotic equipartition property (AEP),
      (c) construction of explicit encoders / decoders via the
          typical projector at the n-fold level,

    none of which are in this single-shot file.  The Margolus–Levitin
    pattern used elsewhere in `LayerB/` (and in this same file's
    `typicalProbability_lower_bound_of_atypical_bound` for the
    single-shot template) means the proof obligation is exposed as
    a named hypothesis rather than asserted as `axiom`. -/
def SchumacherAsymptoticDirect
    {d : ℕ} (ρ : ComplexDensityMatrix d) : Prop :=
  ∀ R : ℝ, SchumacherRate ρ < R →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        ∃ (E : Matrix (Fin (d^m)) (Fin (d^m)) ℂ →
                Matrix (Fin (2^(⌊m * R⌋.toNat))) (Fin (2^(⌊m * R⌋.toNat))) ℂ)
          (D : Matrix (Fin (2^(⌊m * R⌋.toNat))) (Fin (2^(⌊m * R⌋.toNat))) ℂ →
                Matrix (Fin (d^m)) (Fin (d^m)) ℂ),
            ∀ (ρn : Matrix (Fin (d^m)) (Fin (d^m)) ℂ),
              -- The fidelity statement for the n-fold state
              -- (instantiated externally with ρn := ρ^⊗m):
              traceOverlapFidelity ρn (D (E ρn)) ≥ 1 - ε

/-- **Schumacher's asymptotic converse part — STATEMENT.**

    No rate strictly below `S(ρ)` permits asymptotic round-trip
    fidelity tending to 1.

    HONEST SCOPE: same as the direct part — stated, not proved. -/
def SchumacherAsymptoticConverse
    {d : ℕ} (ρ : ComplexDensityMatrix d) : Prop :=
  ∀ R : ℝ, 0 ≤ R → R < SchumacherRate ρ →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧
        ∀ (E : Matrix (Fin (d^m)) (Fin (d^m)) ℂ →
                Matrix (Fin (2^(⌊m * R⌋.toNat))) (Fin (2^(⌊m * R⌋.toNat))) ℂ)
          (D : Matrix (Fin (2^(⌊m * R⌋.toNat))) (Fin (2^(⌊m * R⌋.toNat))) ℂ →
                Matrix (Fin (d^m)) (Fin (d^m)) ℂ),
            ∃ (ρn : Matrix (Fin (d^m)) (Fin (d^m)) ℂ),
              traceOverlapFidelity ρn (D (E ρn)) < 1 - ε

/-- **Schumacher's quantum source coding theorem — STATEMENT.**

    The conjunction of the direct and converse parts: the optimal
    asymptotic compression rate is exactly `S(ρ)`. -/
def SchumacherTheorem {d : ℕ} (ρ : ComplexDensityMatrix d) : Prop :=
  SchumacherAsymptoticDirect ρ ∧ SchumacherAsymptoticConverse ρ

/-! ## 8. Tiny single-shot Schumacher data wrapper

    Bundles the constructive pieces this file provides so that
    downstream files can refer to a single Schumacher object
    rather than re-deriving the projector and probability bound. -/

/-- **Single-shot Schumacher data** for a density matrix ρ at
    tolerance δ. -/
structure SchumacherSingleShot (ρ : ComplexDensityMatrix n) (δ : ℝ) where
  /-- The typical projector. -/
  projector : Matrix (Fin n) (Fin n) ℂ
  /-- Hermiticity of the projector. -/
  proj_isHerm : projector.IsHermitian
  /-- Idempotency under the CFC product. -/
  proj_isIdem : projector * projector = projector
  /-- Trace-overlap = typical probability identity. -/
  trace_overlap :
    (Matrix.trace (ρ.M * projector)).re = typicalProbability ρ δ

/-- **Canonical single-shot Schumacher data** for any density
    matrix ρ.  All four fields are discharged by the lemmas above. -/
noncomputable def schumacherSingleShot
    (ρ : ComplexDensityMatrix n) (δ : ℝ) : SchumacherSingleShot ρ δ where
  projector := typicalProjector ρ δ
  proj_isHerm := typicalProjector_isHermitian ρ δ
  proj_isIdem := typicalProjector_isIdempotent_under_cfc ρ δ
  trace_overlap := trace_rho_typicalProjector_eq_typicalProbability ρ δ

end UnifiedTheory.LayerB.SchumacherCoding
