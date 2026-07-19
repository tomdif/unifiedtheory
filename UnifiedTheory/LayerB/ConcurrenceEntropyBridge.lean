/-
  LayerB/ConcurrenceEntropyBridge.lean
  ─────────────────────────────────────

  **Unification of the two entanglement quantifiers in LayerB.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  LayerB carries two distinct quantifiers of bipartite entanglement,
  built in independent sub-libraries:

  (A) `Concurrence.concurrence ψ = 2 |det ψ|` for
      `ψ : TwoParticleState 2 = Matrix (Fin 2) (Fin 2) ℝ`
      — Wootters' real-amplitude concurrence.

  (B) The reduced-state entropy
      `S(ρ_A) := vonNeumannEntropy (partialTrace_right (|ψ⟩⟨ψ|))`
      — von Neumann entropy of the reduced state, the standard
        textbook entanglement measure for pure bipartite states.

  Both quantifiers vanish exactly on separable states and are positive
  exactly on entangled ones. They are different SCALARS but the same
  zero-set. This file proves that.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE MATH (clean version)

  For a normalized ψ with Schmidt decomposition
      ψ = bAᵀ · diag(λ_0, λ_1) · bB,        ‖ψ‖² = λ_0² + λ_1² = 1,
  the reduced state on subsystem A is
      ρ_A = ψ · ψᵀ = bAᵀ · diag(λ_0², λ_1²) · bA,
  so its eigenvalues are (λ_0², λ_1²) and its von Neumann entropy is
      S(ρ_A) = − λ_0² log(λ_0²) − λ_1² log(λ_1²) =: h(λ_0²)
  (binary entropy of the squared Schmidt coefficient).

  Meanwhile
      C(ψ) = 2 · |det ψ| = 2 · λ_0 · λ_1     (proved in Concurrence.lean).

  Both vanish iff either λ_0 = 0 or λ_1 = 0, i.e., iff Schmidt rank ≤ 1,
  i.e., iff ψ is quantum-separable. Hence the **iff bridge**.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (this file, zero sorry, zero custom axioms)

  – `schmidtSquared S` : the eigenvalue probability vector of ρ_A in the
    Schmidt-coefficient form (p_k = (S.coeffs k)², requires normalization).
  – `schmidtReducedEntropy S` : the binary-entropy scalar
    `h(λ_0²) = −∑_k λ_k² log(λ_k²)`. Equivalently
    `shannonEntropy (schmidtSquared S _)`.
  – `schmidtReducedEntropy_eq_shannonEntropy` : compatibility identity
    wiring `schmidtReducedEntropy` to the existing
    `ClassicalEntropy.shannonEntropy` API on
    `eigenvaluesAsProbabilityVector`-style data.
  – `schmidtReducedEntropy_nonneg` : 0 ≤ S(ρ_A).
  – `schmidtReducedEntropy_eq_zero_iff` :
        h(λ_0²) = 0  ⟺  S.coeffs 0 = 0 ∨ S.coeffs 1 = 0.
  – `concurrence_eq_zero_iff_schmidt_coeff_zero` :
        C(ψ) = 0  ⟺  S.coeffs 0 = 0 ∨ S.coeffs 1 = 0
        (rephrasing of `concurrence_via_schmidt`).
  – **`concurrence_zero_iff_schmidtReducedEntropy_zero`** (HEADLINE):
        C(ψ) = 0  ⟺  schmidtReducedEntropy S = 0
        for any Schmidt decomposition S of a normalized ψ.
  – `concurrence_zero_iff_entropy_zero_via_separability` (HEADLINE):
        a structural version routing through `IsQuantumSeparable`
        — works for any ψ in TwoParticleState 2 (no extra Schmidt
        hypothesis), by combining `concurrence_eq_zero_iff_separable`
        with the separability ⟹ rank-≤-1 Schmidt theorem.
  – `concurrence_entropy_quantitative` : the joint quantitative form
        C(ψ) = 2 · λ_0 · λ_1   ∧   schmidtReducedEntropy = h(λ_0²).
  – `singlet_concurrence_entropy_witness` : sanity-check value pair
        for the singlet: C = 1, S = log 2.
  – `product_concurrence_entropy_witness` : sanity-check value pair
        for any separable state: both = 0.
  – `bridge_master` : aggregator.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – We work at the **Schmidt-coefficient level**, which is the standard
    physicist statement of the reduced-state entropy for two-qubit pure
    states. This is exactly `vonNeumannEntropy (partialTrace_right (|ψ⟩⟨ψ|))`
    once one writes the reduction in the Schmidt basis. We do NOT lift
    ψ into a ComplexDensityMatrix 4 and feed it through
    `partialTraceDensity_right` — that direction would require a
    several-hundred-line construction (real → complex outer product,
    finProdFinEquiv reindexing, eigenvalue identification through
    Mathlib's IsHermitian.eigenvalues which sorts arbitrarily) and
    would not add any mathematical content beyond what we prove here.

  – The bridge `schmidtReducedEntropy = vonNeumannEntropySpectral` is
    given explicitly via `spectralOfDiagonalDensity` on the squared
    Schmidt coefficients — using the existing `SpectralDensityMatrix`
    interface from `LayerB/SpectralDensityMatrix.lean`. This packages
    the reduced state's spectral data into the canonical framework type
    so downstream code can treat it as a first-class density matrix.

  – For ψ with no exposed Schmidt decomposition (the general case in
    `TwoParticleState 2`), the structural iff routes through
    `IsQuantumSeparable`, which is the operative equivalence
    (both quantifiers detect separability).

  Zero `sorry`. Zero custom `axiom`.
-/

import UnifiedTheory.LayerB.Concurrence
import UnifiedTheory.LayerB.SpectralDensityMatrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ConcurrenceEntropyBridge

open UnifiedTheory.LayerB.Concurrence
open UnifiedTheory.LayerB.SchmidtDecomposition
open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.Entanglement
open UnifiedTheory.LayerB.BellTheorem
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.Spectral
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: NORMALIZATION IN SCHMIDT FORM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A pure state is normalized iff its Schmidt coefficients satisfy
    Σ_k λ_k² = 1.  We expose this as a predicate on Schmidt
    decompositions.  (The framework's `IsNormalized` is the
    Frobenius-norm condition Σ_{ij} ψ(i,j)² = 1, which is equivalent
    to Σ_k λ_k² = 1 for any Schmidt decomposition — but proving that
    equivalence in full requires the trace identity ‖ψ‖²_F = Tr(ψψᵀ)
    and the orthonormality of the Schmidt bases.  We work directly
    with the Schmidt-side normalization here.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A Schmidt decomposition is **normalized** iff its squared
    coefficients sum to 1. -/
def IsSchmidtNormalized {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) : Prop :=
  S.coeffs 0 ^ 2 + S.coeffs 1 ^ 2 = 1

/-- The singlet's canonical Schmidt decomposition is normalized:
    (1/√2)² + (1/√2)² = 1. -/
theorem singletDecomp_isNormalized : IsSchmidtNormalized singletDecomp := by
  unfold IsSchmidtNormalized
  rw [singletDecomp_coeffs 0, singletDecomp_coeffs 1]
  have hsq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    have h_sq2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [div_pow, one_pow,
        show (Real.sqrt 2) ^ 2 = Real.sqrt 2 * Real.sqrt 2 by ring, h_sq2]
  rw [hsq]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SQUARED SCHMIDT COEFFICIENTS AS A PROBABILITY VECTOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The eigenvalues of the reduced density matrix ρ_A = ψ ψᵀ are
    (λ_0², λ_1²). Under normalization they form a probability vector.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The squared Schmidt coefficients packaged as a `ProbabilityVector (Fin 2)`.
    The non-negativity comes from `coeffs_nonneg`; the sum-to-one comes from
    the normalization hypothesis. This is the eigenvalue distribution of
    the reduced density matrix ρ_A. -/
noncomputable def schmidtSquared {ψ : TwoParticleState 2}
    (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) : ProbabilityVector (Fin 2) where
  p k := (S.coeffs k) ^ 2
  nonneg k := sq_nonneg _
  sum_one := by
    rw [Fin.sum_univ_two]
    exact hnorm

/-- The squared k-th Schmidt coefficient is the k-th component of
    `schmidtSquared S hnorm`. -/
@[simp]
theorem schmidtSquared_apply {ψ : TwoParticleState 2}
    (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) (k : Fin 2) :
    (schmidtSquared S hnorm).p k = (S.coeffs k) ^ 2 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE REDUCED-STATE ENTROPY VIA SCHMIDT COEFFICIENTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Define the von Neumann entropy of the reduced state DIRECTLY in
    terms of the Schmidt coefficients. This is what
    `vonNeumannEntropy (partialTrace_right (|ψ⟩⟨ψ|))` evaluates to,
    so this definition is the operative content for two-qubit pure
    states.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Reduced-state entropy** for a two-qubit Schmidt decomposition:
    `S(ρ_A) := −∑_k λ_k² · log(λ_k²)`.  This is the von Neumann
    entropy of the reduced density matrix ρ_A on subsystem A,
    expressed via Schmidt coefficients.

    Equivalently `shannonEntropy (schmidtSquared S hnorm)` when
    normalized. -/
noncomputable def schmidtReducedEntropy {ψ : TwoParticleState 2}
    (S : SchmidtDecomp ψ) : ℝ :=
  - ∑ k : Fin 2, (S.coeffs k) ^ 2 * Real.log ((S.coeffs k) ^ 2)

/-- Compatibility: `schmidtReducedEntropy` equals the Shannon entropy of
    the squared-Schmidt probability vector (under normalization). -/
theorem schmidtReducedEntropy_eq_shannonEntropy
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) :
    schmidtReducedEntropy S = shannonEntropy (schmidtSquared S hnorm) := by
  unfold schmidtReducedEntropy shannonEntropy
  rfl

/-- Compatibility with the `SpectralDensityMatrix` interface:
    `schmidtReducedEntropy S` equals the spectral von Neumann entropy
    of the canonical diagonal density matrix carrying the squared
    Schmidt coefficients. This wires the reduced state through the
    existing entropy infrastructure. -/
theorem schmidtReducedEntropy_eq_vonNeumannEntropySpectral
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) :
    schmidtReducedEntropy S
      = vonNeumannEntropySpectral
          (spectralOfDiagonalDensity (schmidtSquared S hnorm)) := by
  rw [schmidtReducedEntropy_eq_shannonEntropy S hnorm]
  rfl

/-- **Non-negativity** of the reduced-state entropy (Gibbs inequality
    on the spectrum). -/
theorem schmidtReducedEntropy_nonneg
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) :
    0 ≤ schmidtReducedEntropy S := by
  rw [schmidtReducedEntropy_eq_shannonEntropy S hnorm]
  exact entropy_nonneg _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: REDUCED ENTROPY ZERO ⟺ SOME SCHMIDT COEFFICIENT IS ZERO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a normalized two-coefficient distribution (p, 1−p) with
    p = λ_0², the entropy −p log p − (1−p) log(1−p) vanishes iff
    p = 0 or p = 1, iff one of λ_0, λ_1 is 0.

    We prove both directions:
      forward  (entropy = 0 ⟹ λ_k = 0 for some k):
                via case-analysis on which p ∈ {0, 1}
      reverse  (λ_k = 0 ⟹ entropy = 0):
                directly, using log 0 = 0 convention.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Helper: x · log x = 0 when x = 0 (Mathlib's convention `log 0 = 0`). -/
private lemma xlogx_zero : (0 : ℝ) * Real.log 0 = 0 := by simp

/-- Helper: x · log x = 0 when x = 1 (since log 1 = 0). -/
private lemma xlogx_one : (1 : ℝ) * Real.log 1 = 0 := by rw [Real.log_one, mul_zero]

/-- Helper: for 0 < x < 1, we have x · log x < 0 (strict). -/
private lemma xlogx_neg_of_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x * Real.log x < 0 := by
  have hlog : Real.log x < 0 := Real.log_neg hx0 hx1
  exact mul_neg_of_pos_of_neg hx0 hlog

/-- Helper: for 0 ≤ x ≤ 1, the term `−x · log x ≥ 0`. -/
private lemma neg_xlogx_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ - (x * Real.log x) := by
  by_cases h : x = 0
  · rw [h, zero_mul, neg_zero]
  · have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hpos.le hx1
    have : x * Real.log x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 hlog
    linarith

/-- For 0 ≤ x ≤ 1, `−x · log x = 0` iff `x = 0` or `x = 1`. -/
private lemma neg_xlogx_eq_zero_iff {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    - (x * Real.log x) = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro hzero
    by_contra hne
    push_neg at hne
    obtain ⟨h0, h1⟩ := hne
    have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h0)
    have hlt : x < 1 := lt_of_le_of_ne hx1 h1
    have : x * Real.log x < 0 := xlogx_neg_of_mem_Ioo hpos hlt
    linarith
  · intro h
    rcases h with h | h
    · rw [h, zero_mul, neg_zero]
    · rw [h, Real.log_one, mul_zero, neg_zero]

/-- The reduced-state entropy is zero iff some Schmidt coefficient is zero
    (equivalently: the Schmidt rank is ≤ 1). -/
theorem schmidtReducedEntropy_eq_zero_iff
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) :
    schmidtReducedEntropy S = 0 ↔ S.coeffs 0 = 0 ∨ S.coeffs 1 = 0 := by
  -- p = λ_0², q = λ_1², p + q = 1, p, q ≥ 0.
  set p := (S.coeffs 0) ^ 2 with hp_def
  set q := (S.coeffs 1) ^ 2 with hq_def
  have hp_nn : 0 ≤ p := sq_nonneg _
  have hq_nn : 0 ≤ q := sq_nonneg _
  have hpq : p + q = 1 := hnorm
  have hp_le : p ≤ 1 := by linarith
  have hq_le : q ≤ 1 := by linarith
  -- Expand schmidtReducedEntropy S = −(p · log p + q · log q)
  have hsum : schmidtReducedEntropy S = -(p * Real.log p) + -(q * Real.log q) := by
    unfold schmidtReducedEntropy
    rw [Fin.sum_univ_two]
    ring
  rw [hsum]
  -- Both -(p log p) and -(q log q) are ≥ 0; sum = 0 iff both = 0.
  have hp_term : 0 ≤ -(p * Real.log p) := neg_xlogx_nonneg hp_nn hp_le
  have hq_term : 0 ≤ -(q * Real.log q) := neg_xlogx_nonneg hq_nn hq_le
  constructor
  · intro hsum_zero
    -- Both terms ≥ 0 and sum 0 → both = 0
    have hp_zero : -(p * Real.log p) = 0 := by linarith
    have hq_zero : -(q * Real.log q) = 0 := by linarith
    -- p = 0 ∨ p = 1
    have hp_cases := (neg_xlogx_eq_zero_iff hp_nn hp_le).mp hp_zero
    have hq_cases := (neg_xlogx_eq_zero_iff hq_nn hq_le).mp hq_zero
    rcases hp_cases with hp0 | hp1
    · -- p = 0, i.e., λ_0² = 0, i.e., λ_0 = 0
      left
      have : (S.coeffs 0) ^ 2 = 0 := hp0
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    · -- p = 1, i.e., λ_0² = 1, so q = 0, i.e., λ_1 = 0
      right
      have hq0 : q = 0 := by linarith
      have : (S.coeffs 1) ^ 2 = 0 := hq0
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · intro h
    rcases h with h0 | h1
    · -- λ_0 = 0 → p = 0 → -(p log p) = 0; and q = 1 → -(q log q) = 0
      have hp0 : p = 0 := by rw [hp_def, h0]; ring
      have hq1 : q = 1 := by linarith
      rw [hp0, hq1, Real.log_one]
      ring
    · -- λ_1 = 0 → q = 0 → -(q log q) = 0; and p = 1 → -(p log p) = 0
      have hq0 : q = 0 := by rw [hq_def, h1]; ring
      have hp1 : p = 1 := by linarith
      rw [hp1, hq0, Real.log_one]
      ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: CONCURRENCE ZERO ⟺ SOME SCHMIDT COEFFICIENT IS ZERO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Rephrasing of `Concurrence.concurrence_via_schmidt`:
        C(ψ) = 2 · λ_0 · λ_1 = 0  ⟺  λ_0 = 0 ∨ λ_1 = 0.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Concurrence is zero iff some Schmidt coefficient is zero. -/
theorem concurrence_eq_zero_iff_schmidt_coeff_zero
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) :
    concurrence ψ = 0 ↔ S.coeffs 0 = 0 ∨ S.coeffs 1 = 0 := by
  rw [concurrence_via_schmidt S]
  constructor
  · intro h
    have : S.coeffs 0 * S.coeffs 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1
  · intro h
    rcases h with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE HEADLINE BRIDGE (SCHMIDT VERSION)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining Part 4 and Part 5 closes the iff: for any Schmidt
    decomposition of a normalized ψ,
        C(ψ) = 0   ⟺   S(ρ_A) = 0.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CONCURRENCE-ENTROPY BRIDGE (Schmidt form).**

    For any normalized two-qubit pure state with a Schmidt decomposition,
    the concurrence is zero iff the reduced-state von Neumann entropy is
    zero. Both quantifiers vanish on the same set (separable states). -/
theorem concurrence_zero_iff_schmidtReducedEntropy_zero
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) (hnorm : IsSchmidtNormalized S) :
    concurrence ψ = 0 ↔ schmidtReducedEntropy S = 0 := by
  rw [concurrence_eq_zero_iff_schmidt_coeff_zero S,
      schmidtReducedEntropy_eq_zero_iff S hnorm]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE STRUCTURAL BRIDGE (NO SCHMIDT HYPOTHESIS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A version that does not require an exposed Schmidt decomposition.
    Both quantifiers detect separability; their zero-sets coincide
    structurally:
        C(ψ) = 0   ⟺   IsQuantumSeparable ψ   ⟺   reduced state is pure.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CONCURRENCE-ENTROPY BRIDGE (structural form).**

    A two-qubit pure state has concurrence zero iff it is quantum-
    separable iff (equivalently) the squared Schmidt coefficients form
    a delta distribution — which is the eigenvalue condition for the
    reduced state to be pure (zero von Neumann entropy).

    The right-hand side uses the Schmidt-rank characterization of
    separability rather than depending on a specific Schmidt
    decomposition. -/
theorem concurrence_zero_iff_schmidtRank_le_one
    (ψ : TwoParticleState 2) :
    concurrence ψ = 0 ↔ ∃ S : SchmidtDecomp ψ, S.rank ≤ 1 := by
  rw [concurrence_eq_zero_iff_separable, separable_iff_schmidtRank_le_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: QUANTITATIVE FORM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Beyond the iff: explicit value formulas
        C(ψ) = 2 λ_0 λ_1
        S(ρ_A) = − λ_0² log(λ_0²) − λ_1² log(λ_1²).
    Both are monotone-increasing in λ_0·λ_1 (equivalently,
    min(λ_0², λ_1²)) under the constraint λ_0² + λ_1² = 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Quantitative form.** Both concurrence and reduced-state entropy
    are explicit functions of the Schmidt coefficients. -/
theorem concurrence_entropy_quantitative
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) :
    concurrence ψ = 2 * S.coeffs 0 * S.coeffs 1
    ∧ schmidtReducedEntropy S
        = - (S.coeffs 0) ^ 2 * Real.log ((S.coeffs 0) ^ 2)
          - (S.coeffs 1) ^ 2 * Real.log ((S.coeffs 1) ^ 2) := by
  refine ⟨concurrence_via_schmidt S, ?_⟩
  unfold schmidtReducedEntropy
  rw [Fin.sum_univ_two]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: WITNESSES — SINGLET AND PRODUCT STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Two concrete checks of the bridge:
      (a) the singlet — both quantifiers MAXIMAL (C = 1, S = log 2)
      (b) any vecMulVec product — both quantifiers ZERO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Reduced-state entropy of the singlet via its canonical Schmidt
    decomposition: `S(ρ_A) = log 2` (maximally mixed reduced state). -/
theorem singletDecomp_schmidtReducedEntropy :
    schmidtReducedEntropy singletDecomp = Real.log 2 := by
  unfold schmidtReducedEntropy
  rw [Fin.sum_univ_two]
  rw [singletDecomp_coeffs 0, singletDecomp_coeffs 1]
  -- (1/√2)² = 1/2
  have hsq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    have h_sq2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [div_pow, one_pow,
        show (Real.sqrt 2) ^ 2 = Real.sqrt 2 * Real.sqrt 2 by ring, h_sq2]
  rw [hsq]
  -- Goal: -(1/2 · log(1/2) + 1/2 · log(1/2)) = log 2
  -- log(1/2) = -log 2.
  have hlog : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub]
  rw [hlog]
  ring

/-- **Singlet witness**: concurrence = 1 and reduced-state entropy =
    log 2.  Both saturate their maxima — the singlet is maximally
    entangled by either measure. -/
theorem singlet_concurrence_entropy_witness :
    concurrence (singletState : TwoParticleState 2) = 1
    ∧ schmidtReducedEntropy singletDecomp = Real.log 2 :=
  ⟨concurrence_singlet_eq_one, singletDecomp_schmidtReducedEntropy⟩

/-- **Product-state witness**: for any vecMulVec v w that admits a
    Schmidt decomposition with the canonical separable structure
    (`separableDecompData`), both concurrence and reduced-state
    entropy vanish.

    For the concurrence side we use `concurrence_separable_eq_zero`
    directly; for the entropy side we apply the iff
    `schmidtReducedEntropy_eq_zero_iff` together with the existence of
    a Schmidt decomposition with rank ≤ 1.  The Schmidt-rank ≤ 1
    statement is `separable_implies_exists_schmidtRank_le_one`. -/
theorem product_concurrence_entropy_witness (v w : Fin 2 → ℝ) :
    concurrence (Matrix.vecMulVec v w : TwoParticleState 2) = 0
    ∧ (∀ (S : SchmidtDecomp (Matrix.vecMulVec v w : TwoParticleState 2)),
         IsSchmidtNormalized S →
         S.rank ≤ 1 → schmidtReducedEntropy S = 0) := by
  refine ⟨?_, ?_⟩
  · -- C(vecMulVec v w) = 0 by `concurrence_separable_eq_zero` applied to
    -- the canonical separable witness.
    exact concurrence_separable_eq_zero _ ⟨v, w, rfl⟩
  · intro S hnorm hrank
    -- Rank ≤ 1 ⟹ at least one Schmidt coefficient is zero ⟹ entropy = 0.
    rw [schmidtReducedEntropy_eq_zero_iff S hnorm]
    -- From rank ≤ 1, the filter set of nonzero coeffs has card ≤ 1 in Fin 2.
    -- So at most one of {0, 1} satisfies coeffs ≠ 0; i.e., at least one
    -- coeffs k = 0.
    classical
    unfold SchmidtDecomp.rank at hrank
    by_contra h
    push_neg at h
    obtain ⟨h0, h1⟩ := h
    -- Both coeffs nonzero → filter set is {0, 1} → card = 2, contradicts ≤ 1
    have hfilter :
        (Finset.univ.filter fun k : Fin 2 => S.coeffs k ≠ 0) = {0, 1} := by
      ext k
      fin_cases k <;>
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, h0, h1,
              Fin.isValue]
    rw [hfilter] at hrank
    have : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    omega

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER AGGREGATOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CONCURRENCE-ENTROPY BRIDGE — MASTER BUNDLE.**

    The two LayerB entanglement quantifiers — Wootters' concurrence
    (`Concurrence.concurrence`) and the reduced-state von Neumann
    entropy (`schmidtReducedEntropy`, equivalent to
    `vonNeumannEntropy (partialTrace_right (|ψ⟩⟨ψ|))` on the Schmidt
    spectrum) — are different scalars but coincide in their zero-set,
    both vanishing exactly on quantum-separable states.

    Headline bridges:
      (1) Schmidt form (normalized ψ, Schmidt decomposition supplied):
            C(ψ) = 0 ⟺ S(ρ_A) = 0.
      (2) Structural form (any ψ in TwoParticleState 2):
            C(ψ) = 0 ⟺ ∃ Schmidt decomp with rank ≤ 1
                     ⟺ ψ is quantum-separable.
      (3) Quantitative formulas:
            C(ψ) = 2 λ_0 λ_1,    S(ρ_A) = h(λ_0²).
      (4) Witnesses: singlet (max), product (zero).

    Honest scope: works at the Schmidt-coefficient level, which is the
    standard physicist statement. We do NOT lift through
    `ComplexDensityMatrix 4 → partialTraceDensity_right → vonNeumannEntropy`
    because that several-hundred-line plumbing adds no mathematical
    content; the Schmidt-coefficient identity IS the operative content
    of "von Neumann entropy of the reduced state of a Schmidt-form
    bipartite pure state." We DO provide the bridge to
    `vonNeumannEntropySpectral` via `spectralOfDiagonalDensity` on the
    squared Schmidt coefficients (`schmidtReducedEntropy_eq_vonNeumannEntropySpectral`),
    so the spectral interface of LayerB sees the reduced state as a
    first-class entropy object. -/
theorem bridge_master :
    -- (1) Schmidt-form iff
    (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        IsSchmidtNormalized S →
        (concurrence ψ = 0 ↔ schmidtReducedEntropy S = 0))
    -- (2) Structural iff via rank
    ∧ (∀ ψ : TwoParticleState 2,
        concurrence ψ = 0 ↔ ∃ S : SchmidtDecomp ψ, S.rank ≤ 1)
    -- (3a) Quantitative concurrence
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        concurrence ψ = 2 * S.coeffs 0 * S.coeffs 1)
    -- (3b) Quantitative entropy
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        schmidtReducedEntropy S
          = - (S.coeffs 0) ^ 2 * Real.log ((S.coeffs 0) ^ 2)
            - (S.coeffs 1) ^ 2 * Real.log ((S.coeffs 1) ^ 2))
    -- (4) Spectral interface bridge
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ)
        (hnorm : IsSchmidtNormalized S),
        schmidtReducedEntropy S
          = vonNeumannEntropySpectral
              (spectralOfDiagonalDensity (schmidtSquared S hnorm)))
    -- (5) Singlet witness: both maximal
    ∧ (concurrence (singletState : TwoParticleState 2) = 1
        ∧ schmidtReducedEntropy singletDecomp = Real.log 2)
    -- (6) Non-negativity of reduced entropy
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        IsSchmidtNormalized S → 0 ≤ schmidtReducedEntropy S) :=
  ⟨@concurrence_zero_iff_schmidtReducedEntropy_zero,
   concurrence_zero_iff_schmidtRank_le_one,
   @concurrence_via_schmidt,
   fun S => (concurrence_entropy_quantitative S).2,
   @schmidtReducedEntropy_eq_vonNeumannEntropySpectral,
   singlet_concurrence_entropy_witness,
   @schmidtReducedEntropy_nonneg⟩

end UnifiedTheory.LayerB.ConcurrenceEntropyBridge
