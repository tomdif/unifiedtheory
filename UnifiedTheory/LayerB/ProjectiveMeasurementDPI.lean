/-
  LayerB/ProjectiveMeasurementDPI.lean
  ─────────────────────────────────────

  **Data-processing inequality (DPI) for Umegaki relative entropy
  under a projective measurement in σ's eigenbasis.**

  Phase B1 of the Lindblad–Uhlmann roadmap (Approach A, "clean
  special case").

  STATEMENT (Approach A — σ-eigenbasis):

      For positive-definite density matrices ρ, σ, with outcome
      distributions in σ's eigenbasis given by
      `p_b(τ) := Re ((U_σ* · τ · U_σ)_{bb})`,

        klDivergence (outcomesInSigmaBasis ρ hσ)
                      (outcomesInSigmaBasis σ hσ)
          ≤  umegakiRelativeEntropy ρ σ.

  PROOF STRATEGY:
    Let `V := U_ρ* · U_σ`.  Then `p_b(ρ) = ∑_i ‖V_{ib}‖² λ_i` and
    `p_b(σ) = μ_b` (σ is diagonal in its own eigenbasis).
    From `trace_mul_cfc_log_eq_sum_mixed`,
      `S(ρ‖σ) = ∑_i λ_i log λ_i − ∑_{i,b} ‖V_{ib}‖² λ_i log μ_b`.
    And
      `KL(p‖q) = ∑_b p_b log p_b − ∑_b p_b log μ_b`.
    Note `∑_b p_b log μ_b = ∑_{i,b} ‖V_{ib}‖² λ_i log μ_b` (relabel),
    so
      `S(ρ‖σ) − KL(p‖q) = ∑_i λ_i log λ_i − ∑_b p_b log p_b`.
    The log-sum inequality, applied per `b` with weights
    `a_i := ‖V_{ib}‖² λ_i` and reference `b_i := ‖V_{ib}‖²`
    (column-stochastic), gives
      `p_b log p_b = klTerm (∑_i ‖V_{ib}‖² λ_i) (∑_i ‖V_{ib}‖²)
                      ≤ ∑_i klTerm (‖V_{ib}‖² λ_i) (‖V_{ib}‖²)
                       = ∑_i ‖V_{ib}‖² λ_i log λ_i`.
    Summing over `b` and using `∑_b ‖V_{ib}‖² = 1` (row-stochastic
    for V unitary) yields the result.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `outcomesInSigmaBasis ρ hσ`     — measurement-outcome
                                           probability vector for ρ
                                           in σ's eigenbasis.
    2. `outcomesInSigmaBasis_self_eq_eigenvalues`
                                          — for τ = σ, the outcomes
                                            equal σ's eigenvalues.
    3. `umegaki_dpi_projective_sigma_basis`
                                          — the DPI itself.

  SCOPE / BLOCKER for Approach B (general basis):
    For an arbitrary measurement basis (not σ's eigenbasis), one
    obtains two transition matrices `R^ρ_{bi} := ‖U_ρ* B|_b · e_i‖²`
    and `R^σ_{bj} := ‖U_σ* B|_b · e_j‖²`, with `p_b = ∑_i R^ρ_{bi}
    λ_i` and `q_b = ∑_j R^σ_{bj} μ_j`.  The previous cancellation
    `∑_b p_b log μ_b = ∑_{i,b} … log μ_b` no longer holds (q_b
    mixes μ_j's), so one needs either operator-concavity of `log`
    (Lieb) or Stinespring + Klein on a larger space.  Neither is
    in scope here; deferred to a follow-up.

  NO `sorry`, NO custom `axiom`.
-/

import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.LogSumInequality
import UnifiedTheory.LayerB.ClassicalRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ProjectiveMeasurementDPI

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.SpectralFCTrace
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.OperatorMonotoneLog
open UnifiedTheory.LayerB.KleinInequality
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.LogSumInequality

variable {n : ℕ}

/-! ## 1. Helper lemmas mirroring those in `KleinInequalityFull` -/

/-- For any complex `z`, `z * star z = ‖z‖²` (as complex number).
    Local copy of the private lemma in `KleinInequalityFull`. -/
private lemma complex_mul_star_eq_sq_norm' (z : ℂ) :
    z * star z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl]
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]

/-- `star z * z = ‖z‖²` (as complex). -/
private lemma complex_star_mul_eq_sq_norm' (z : ℂ) :
    star z * z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [mul_comm]; exact complex_mul_star_eq_sq_norm' z

/-! ## 2. The "transition" probabilities ‖V_{ij}‖² are doubly stochastic -/

/-- Row sums of `‖V_{ij}‖²` equal 1 for unitary V (V * star V = 1). -/
private lemma row_sum_sq_norm_eq_one'
    (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V * star V = 1) (i : Fin n) :
    ∑ j, ‖V i j‖^2 = 1 := by
  have h : (V * star V) i i = (1 : Matrix (Fin n) (Fin n) ℂ) i i := by rw [hV]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ j, V i j * (star V) j i = ((‖V i j‖^2 : ℝ) : ℂ) := by
    intro j
    show V i j * star (V i j) = _
    exact complex_mul_star_eq_sq_norm' (V i j)
  rw [Finset.sum_congr rfl (fun j _ => h2 j)] at h
  have h3 : ((∑ j, ‖V i j‖^2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]; push_cast; rfl
  exact_mod_cast h3

/-- Column sums of `‖V_{ij}‖²` equal 1 for unitary V (star V * V = 1). -/
private lemma col_sum_sq_norm_eq_one'
    (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : star V * V = 1) (j : Fin n) :
    ∑ i, ‖V i j‖^2 = 1 := by
  have h : (star V * V) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by rw [hV]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ i, (star V) j i * V i j = ((‖V i j‖^2 : ℝ) : ℂ) := by
    intro i
    show star (V i j) * V i j = _
    exact complex_star_mul_eq_sq_norm' (V i j)
  rw [Finset.sum_congr rfl (fun i _ => h2 i)] at h
  have h3 : ((∑ i, ‖V i j‖^2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]; push_cast; rfl
  exact_mod_cast h3

/-! ## 3. The measurement-outcome diagonal entry `(U_σ* ρ U_σ)_{bb}`
       expressed as `∑_i ‖V_{ib}‖² λ_i` -/

/-- **Diagonal-entry formula.**  With `V := star U_ρ * U_σ`,
    `(star U_σ * ρ * U_σ)_{bb} = ∑_i ‖V_{ib}‖² · λ_i` (as a
    complex number with real value). -/
private lemma diag_entry_sigma_basis_formula
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosDef)
    (Uσ : Matrix (Fin n) (Fin n) ℂ)
    (_hUσ : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Fin n) :
    (star Uσ * ρ * Uσ) b b
      = ((∑ i, ‖((star hρ.1.eigenvectorUnitary.val) * Uσ) i b‖^2
                * hρ.1.eigenvalues i : ℝ) : ℂ) := by
  set Uρ : Matrix (Fin n) (Fin n) ℂ := hρ.1.eigenvectorUnitary.val with hUρ_def
  set lam : Fin n → ℝ := hρ.1.eigenvalues with hlam_def
  set Dlam : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))
  set V : Matrix (Fin n) (Fin n) ℂ := star Uρ * Uσ with hV_def
  -- Spectral decomposition ρ = Uρ * Dlam * star Uρ.
  have hρ_spec : ρ = Uρ * Dlam * star Uρ := by
    have h := hρ.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  rw [hρ_spec]
  -- Rearrange: star Uσ * (Uρ * Dlam * star Uρ) * Uσ
  --          = (star Uσ * Uρ) * Dlam * (star Uρ * Uσ)
  --          = star V * Dlam * V.
  have hstar_V_eq : star V = star Uσ * Uρ := by
    rw [hV_def, StarMul.star_mul, star_star]
  have hreassoc :
      star Uσ * (Uρ * Dlam * star Uρ) * Uσ
        = (star Uσ * Uρ) * Dlam * (star Uρ * Uσ) := by
    noncomm_ring
  rw [hreassoc, ← hstar_V_eq, ← hV_def]
  -- (star V * Dlam * V) b b = ∑_i ∑_j (star V) b i * (Dlam) i j * V j b
  --                          (but Dlam is diagonal, so only i = j contributes)
  --                        = ∑_i (star V) b i * lam i * V i b
  --                        = ∑_i star (V i b) * lam i * V i b
  --                        = ∑_i lam i * (star (V i b) * V i b)
  --                        = ∑_i lam i * ‖V i b‖²  (as complex).
  rw [Matrix.mul_apply]
  -- Goal: ∑ j, (star V * Dlam) b j * V j b = ((∑ i, ‖V i b‖² * lam i : ℝ) : ℂ)
  have h_entry : ∀ j, (star V * Dlam) b j = star (V j b) * ((lam j : ℝ) : ℂ) := by
    intro j
    rw [Matrix.mul_apply]
    -- ∑ k, (star V) b k * Dlam k j
    -- Dlam k j = if k = j then (lam j : ℂ) else 0
    rw [Finset.sum_eq_single j]
    · -- main term: (star V) b j * Dlam j j = star (V j b) * (lam j : ℂ)
      show (star V) b j * (Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) j j
            = star (V j b) * ((lam j : ℝ) : ℂ)
      rw [Matrix.diagonal_apply_eq]
      rfl
    · intro k _ hkj
      show (star V) b k * (Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) k j = 0
      rw [Matrix.diagonal_apply_ne _ hkj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [Finset.sum_congr rfl (fun j _ => by rw [h_entry j])]
  -- Now ∑ j, star (V j b) * (lam j : ℂ) * V j b
  -- = ∑ j, (lam j : ℂ) * (star (V j b) * V j b)
  -- = ∑ j, (lam j : ℂ) * ((‖V j b‖² : ℝ) : ℂ)
  -- = ((∑ j, ‖V j b‖² * lam j : ℝ) : ℂ)
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have h_mod : star (V j b) * V j b = ((‖V j b‖^2 : ℝ) : ℂ) :=
    complex_star_mul_eq_sq_norm' (V j b)
  -- Rearrange and use h_mod
  have hreorder : star (V j b) * ((lam j : ℝ) : ℂ) * V j b
                = ((lam j : ℝ) : ℂ) * (star (V j b) * V j b) := by ring
  rw [hreorder, h_mod]
  push_cast
  ring

/-! ## 4. Positivity / boundedness of `(U_σ* ρ U_σ)_{bb}` -/

/-- The diagonal entry `(star U_σ * ρ * U_σ)_{bb}` is non-negative
    when ρ is positive-definite. -/
private lemma diag_entry_sigma_basis_nonneg
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosDef)
    (Uσ : Matrix (Fin n) (Fin n) ℂ)
    (hUσ : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Fin n) :
    0 ≤ ((star Uσ * ρ * Uσ) b b).re := by
  rw [diag_entry_sigma_basis_formula ρ hρ Uσ hUσ b, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sq_nonneg _) (hρ.eigenvalues_pos i).le

/-- The diagonal entries `(star U_σ * ρ * U_σ)_{bb}` sum to 1
    when ρ is a density matrix (trace 1). -/
private lemma diag_entry_sigma_basis_sum_one
    (ρ : ComplexDensityMatrix n)
    (Uσ : Matrix (Fin n) (Fin n) ℂ)
    (hUσ : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (∑ b, (star Uσ * ρ.M * Uσ) b b) = 1 := by
  -- ∑ b, (star Uσ * ρ * Uσ) b b = Tr (star Uσ * ρ * Uσ)
  --                              = Tr (ρ * Uσ * star Uσ)  (cyclicity)
  --                              = Tr ρ = 1.
  have h_trace : Matrix.trace (star Uσ * ρ.M * Uσ) = Matrix.trace ρ.M := by
    rw [Matrix.trace_mul_cycle]
    -- Goal: Tr (Uσ * star Uσ * ρ) = Tr ρ
    have h_unit : Uσ * star Uσ = 1 := by
      rw [Matrix.mem_unitaryGroup_iff] at hUσ; exact hUσ
    rw [h_unit, Matrix.one_mul]
  have h_trace_def : Matrix.trace (star Uσ * ρ.M * Uσ)
                    = ∑ b, (star Uσ * ρ.M * Uσ) b b := rfl
  rw [← h_trace_def, h_trace, ρ.hTrace]

/-- The diagonal entries `(star U_σ * ρ * U_σ)_{bb}` are real
    (their imaginary part is zero), when ρ is Hermitian. -/
private lemma diag_entry_sigma_basis_im_zero
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosDef)
    (Uσ : Matrix (Fin n) (Fin n) ℂ)
    (hUσ : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Fin n) :
    ((star Uσ * ρ * Uσ) b b).im = 0 := by
  rw [diag_entry_sigma_basis_formula ρ hρ Uσ hUσ b, Complex.ofReal_im]

/-! ## 5. The measurement-outcome probability vector -/

/-- **Measurement-outcome probability vector for ρ in σ's eigenbasis.**

    `outcomesInSigmaBasis ρ hσ` packages the outcome probabilities
    `p_b(ρ) := Re ((U_σ* · ρ · U_σ)_{bb})` of a projective
    measurement in the eigenbasis of `σ` as a `ProbabilityVector`. -/
noncomputable def outcomesInSigmaBasis
    (ρ : ComplexDensityMatrix n) (hσ : ComplexDensityMatrix n) (_hσ_pos : hσ.M.PosDef)
    (hρ : ρ.M.PosDef) :
    ProbabilityVector (Fin n) where
  p b := ((star hσ.hHerm.eigenvectorUnitary.val
                * ρ.M
                * hσ.hHerm.eigenvectorUnitary.val) b b).re
  nonneg b := diag_entry_sigma_basis_nonneg ρ.M hρ
                hσ.hHerm.eigenvectorUnitary.val hσ.hHerm.eigenvectorUnitary.2 b
  sum_one := by
    -- ∑ b, Re ((U* ρ U) b b) = Re (∑ b ...) = Re (Tr (U* ρ U)) = Re (Tr ρ) = Re 1 = 1.
    set Uσ := hσ.hHerm.eigenvectorUnitary.val
    have hUσ_mem : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ :=
      hσ.hHerm.eigenvectorUnitary.2
    have h_sum_re : ∑ b, ((star Uσ * ρ.M * Uσ) b b).re
                  = (∑ b, (star Uσ * ρ.M * Uσ) b b).re := by
      rw [Complex.re_sum]
    rw [h_sum_re, diag_entry_sigma_basis_sum_one ρ Uσ hUσ_mem, Complex.one_re]

/-! ## 6. For τ = σ, outcomes equal the eigenvalues of σ -/

/-- **Outcomes of σ in σ's own eigenbasis equal σ's eigenvalues.**
    `(U_σ* · σ · U_σ)_{bb} = μ_b` where `μ = σ.eigenvalues`. -/
private lemma outcomesInSigmaBasis_sigma_eq_eigenvalues
    (hσ : ComplexDensityMatrix n) (hσ_pos : hσ.M.PosDef) (b : Fin n) :
    (outcomesInSigmaBasis hσ hσ hσ_pos hσ_pos).p b = hσ.hHerm.eigenvalues b := by
  -- (outcomesInSigmaBasis hσ hσ).p b = Re ((U* σ U) b b)
  -- And (U* σ U) = diagonal (ofReal ∘ eigenvalues) by the spectral theorem.
  show ((star hσ.hHerm.eigenvectorUnitary.val
            * hσ.M
            * hσ.hHerm.eigenvectorUnitary.val) b b).re = hσ.hHerm.eigenvalues b
  -- σ = U * diag(μ) * star U  ⟹  star U * σ * U = diag(μ).
  have hσ_spec : hσ.M = hσ.hHerm.eigenvectorUnitary.val
                       * Matrix.diagonal
                            (fun i => ((hσ.hHerm.eigenvalues i : ℝ) : ℂ))
                       * star hσ.hHerm.eigenvectorUnitary.val := by
    have h := hσ.hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  set Uσ := hσ.hHerm.eigenvectorUnitary.val
  set Dmu := Matrix.diagonal (fun i => ((hσ.hHerm.eigenvalues i : ℝ) : ℂ))
  have hUσ_mem : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hσ.hHerm.eigenvectorUnitary.2
  have h_star_U_U : star Uσ * Uσ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hUσ_mem; exact hUσ_mem
  have h_U_star_U : Uσ * star Uσ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hUσ_mem; exact hUσ_mem
  -- star Uσ * (Uσ * Dmu * star Uσ) * Uσ = (star Uσ * Uσ) * Dmu * (star Uσ * Uσ) = Dmu.
  have h_reduce : star Uσ * hσ.M * Uσ = Dmu := by
    rw [hσ_spec]
    calc star Uσ * (Uσ * Dmu * star Uσ) * Uσ
        = (star Uσ * Uσ) * Dmu * (star Uσ * Uσ) := by noncomm_ring
      _ = 1 * Dmu * 1 := by rw [h_star_U_U]
      _ = Dmu := by rw [Matrix.one_mul, Matrix.mul_one]
  rw [h_reduce]
  -- Dmu b b = ((hσ.hHerm.eigenvalues b : ℝ) : ℂ)
  show ((Matrix.diagonal (fun i => ((hσ.hHerm.eigenvalues i : ℝ) : ℂ))) b b).re
        = hσ.hHerm.eigenvalues b
  rw [Matrix.diagonal_apply_eq, Complex.ofReal_re]

/-! ## 7. Trace formula for `Tr (ρ · log σ)` via the σ-basis outcomes -/

/-- **Key relabel identity.**  The mixed-basis trace formula
    `Tr(ρ · log σ) = ∑_i ∑_b ‖V_{ib}‖² · λ_i · log μ_b` can be
    summed-over-`i`-first to give
    `Tr(ρ · log σ) = ∑_b p_b · log μ_b`
    where `p_b = ∑_i ‖V_{ib}‖² λ_i` is the diagonal entry of
    `U_σ* ρ U_σ` (i.e. the σ-basis outcome of ρ). -/
private lemma re_trace_mul_cfc_log_eq_sum_outcomes
    (ρ σ : ComplexDensityMatrix n)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef) :
    (Matrix.trace (ρ.M * cfc Real.log σ.M)).re
      = ∑ b, (outcomesInSigmaBasis ρ σ hσ_pos hρ_pos).p b
              * Real.log (σ.hHerm.eigenvalues b) := by
  -- Use trace_mul_cfc_log_eq_sum_mixed.
  rw [trace_mul_cfc_log_eq_sum_mixed ρ.M σ.M hρ_pos hσ_pos]
  -- Goal: Re (∑ i, ∑ j, ‖V_{ij}‖² (λ_i : ℂ) (log μ_j : ℂ))
  --       = ∑ b, p_b * log μ_b
  set Uρ : Matrix (Fin n) (Fin n) ℂ := hρ_pos.1.eigenvectorUnitary.val
  set Uσ : Matrix (Fin n) (Fin n) ℂ := hσ_pos.1.eigenvectorUnitary.val
  set lam : Fin n → ℝ := hρ_pos.1.eigenvalues
  set mu : Fin n → ℝ := hσ_pos.1.eigenvalues
  -- Note: hρ_pos.1 = ρ.hHerm? Let me use canonical access via hρ_pos.1.
  set V : Matrix (Fin n) (Fin n) ℂ := star Uρ * Uσ
  -- Step 1: turn the complex double sum into a real double sum.
  rw [Complex.re_sum]
  have h_per_i_re : ∀ i,
      (∑ j, ((‖V i j‖^2 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ)
            * ((Real.log (mu j) : ℝ) : ℂ)).re
        = ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j) := by
    intro i
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show ((‖V i j‖^2 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ) * ((Real.log (mu j) : ℝ) : ℂ)
          = ((‖V i j‖^2 * lam i * Real.log (mu j) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [Finset.sum_congr rfl (fun i _ => h_per_i_re i)]
  -- Goal: ∑ i, ∑ j, ‖V_{ij}‖² * lam i * log mu j = ∑ b, p_b * log mu b
  -- Swap sums: ∑ i ∑ j = ∑ j ∑ i.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  -- ∑ i, ‖V i b‖² * lam i * log mu b = (∑ i, ‖V i b‖² * lam i) * log mu b
  --                                  = p_b * log mu b
  have h_factor : ∑ i, ‖V i b‖^2 * lam i * Real.log (mu b)
                = (∑ i, ‖V i b‖^2 * lam i) * Real.log (mu b) := by
    rw [← Finset.sum_mul]
  rw [h_factor]
  -- Now we need: (∑ i, ‖V i b‖² * lam i) = p_b := Re ((U_σ* ρ U_σ)_{bb})
  have h_pb : (∑ i, ‖V i b‖^2 * lam i)
            = (outcomesInSigmaBasis ρ σ hσ_pos hρ_pos).p b := by
    -- p_b = Re ((star Uσ * ρ * Uσ) b b)
    -- and we proved (star Uσ * ρ * Uσ) b b = ((∑ i, ‖V_{ib}‖² λ_i : ℝ) : ℂ).
    show _ = ((star Uσ * ρ.M * Uσ) b b).re
    rw [diag_entry_sigma_basis_formula ρ.M hρ_pos Uσ hσ_pos.1.eigenvectorUnitary.2 b,
        Complex.ofReal_re]
  rw [h_pb]

/-! ## 8. Re Tr (ρ · log ρ) — packaging -/

/-- Real part of `Tr(ρ · log ρ)` as a sum over eigenvalues. -/
private lemma re_trace_rho_log_rho
    (ρ : ComplexDensityMatrix n) (hρ_pos : ρ.M.PosDef) :
    (Matrix.trace (ρ.M * cfc Real.log ρ.M)).re
      = ∑ i, hρ_pos.1.eigenvalues i * Real.log (hρ_pos.1.eigenvalues i) :=
  re_trace_mul_cfc_log_eq_sum ρ.M hρ_pos

/-! ## 9. The key Jensen / log-sum step:
       `∑_b p_b log p_b ≤ ∑_i λ_i log λ_i`. -/

/-- **Quantum-classical contraction of `x log x`.**  With
    `p_b := ∑_i ‖V_{ib}‖² λ_i` and column-stochastic `V`
    (`∑_i ‖V_{ib}‖² = 1` for each `b` and `∑_b ‖V_{ib}‖² = 1`
    for each `i`),

      `∑_b p_b · log p_b   ≤   ∑_i λ_i · log λ_i`. -/
private lemma sum_p_log_p_le_sum_lam_log_lam
    {V : Matrix (Fin n) (Fin n) ℂ}
    {lam : Fin n → ℝ}
    (hlam_pos : ∀ i, 0 < lam i)
    (h_col_sum : ∀ b, ∑ i, ‖V i b‖^2 = 1)
    (h_row_sum : ∀ i, ∑ b, ‖V i b‖^2 = 1) :
    (∑ b, (∑ i, ‖V i b‖^2 * lam i) *
            Real.log (∑ i, ‖V i b‖^2 * lam i))
      ≤ ∑ i, lam i * Real.log (lam i) := by
  -- Per-b apply log-sum with a := |V i b|² lam i, b := |V i b|².
  -- Then klTerm (∑ |V_{ib}|² λ_i) (∑ |V_{ib}|²) ≤ ∑ klTerm (|V_{ib}|² λ_i) (|V_{ib}|²).
  -- The LHS equals (p_b) · log (p_b / 1) = p_b log p_b.
  -- The RHS equals ∑_i klTerm (|V_{ib}|² λ_i) (|V_{ib}|²)
  --              = ∑_i |V_{ib}|² (klTerm λ_i 1)         (klTerm_smul_left, c := |V_{ib}|²)
  --              = ∑_i |V_{ib}|² λ_i log λ_i.
  -- Summing over b and swapping gives the result.
  have h_per_b : ∀ b,
      (∑ i, ‖V i b‖^2 * lam i) * Real.log (∑ i, ‖V i b‖^2 * lam i)
        ≤ ∑ i, ‖V i b‖^2 * lam i * Real.log (lam i) := by
    intro b
    set w := fun i => ‖V i b‖^2 with hw_def
    -- a_i := w i * lam i, b_i := w i.
    have ha_nn : ∀ i, 0 ≤ w i * lam i :=
      fun i => mul_nonneg (sq_nonneg _) (hlam_pos i).le
    have hb_nn : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
    have hAC : ∀ i, w i * lam i ≠ 0 → w i ≠ 0 := by
      intro i hi
      have ⟨hw_i, _⟩ := mul_ne_zero_iff.mp hi
      exact hw_i
    have hLS := log_sum_real (fun i => w i * lam i) (fun i => w i) ha_nn hb_nn hAC
    -- hLS : klTerm (∑ w i * lam i) (∑ w i) ≤ ∑ klTerm (w i * lam i) (w i)
    -- Identify ∑ w i = 1 (column-stochastic, where i is the row, b is the column).
    have hw_sum : (∑ i, w i) = 1 := h_col_sum b
    rw [hw_sum] at hLS
    -- LHS = klTerm (∑ w i * lam i) 1
    -- Identify klTerm (p) 1 = p log p.
    set p := ∑ i, w i * lam i with hp_def
    -- p ≥ 0 (sum of nonneg).
    have hp_nn : 0 ≤ p := Finset.sum_nonneg (fun i _ => ha_nn i)
    -- Now klTerm p 1: if p = 0, both sides are 0; otherwise p · log (p / 1) = p · log p.
    have h_lhs_eq : klTerm p 1 = p * Real.log p := by
      by_cases hp_zero : p = 0
      · rw [hp_zero, klTerm_zero_left, zero_mul]
      · rw [klTerm_of_ne_zero hp_zero, div_one]
    -- Identify klTerm (w i * lam i) (w i) = w i * lam i * log (lam i)  when w i ≠ 0,
    -- and = 0 when w i = 0 (both sides vanish).
    have h_rhs_per : ∀ i, klTerm (w i * lam i) (w i)
                      = w i * lam i * Real.log (lam i) := by
      intro i
      by_cases hwi : w i = 0
      · -- LHS: klTerm (w i * lam i) (w i) = klTerm (0 * lam i) 0 = klTerm 0 0 = 0.
        -- RHS: w i * lam i * Real.log (lam i) = 0 * lam i * Real.log (lam i) = 0.
        rw [hwi]; simp [klTerm_zero_left]
      · -- w i ≠ 0; klTerm (w i * lam i) (w i) = w i * lam i * log ((w i * lam i)/(w i))
        --                                      = w i * lam i * log (lam i)
        have h_lam_ne : lam i ≠ 0 := ne_of_gt (hlam_pos i)
        have h_prod_ne : w i * lam i ≠ 0 := mul_ne_zero hwi h_lam_ne
        rw [klTerm_of_ne_zero h_prod_ne]
        rw [show w i * lam i / w i = lam i from by field_simp]
    have h_rhs_eq : (∑ i, klTerm (w i * lam i) (w i))
                  = ∑ i, w i * lam i * Real.log (lam i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_rhs_per i
    rw [h_lhs_eq, h_rhs_eq] at hLS
    -- hLS : p * log p ≤ ∑ i, w i * lam i * log (lam i)
    -- Goal:    p     * log    p     ≤ ∑ i, w i * lam i * log (lam i)
    -- by hp_def these are identical.
    exact hLS
  -- Sum over b.
  calc (∑ b, (∑ i, ‖V i b‖^2 * lam i) * Real.log (∑ i, ‖V i b‖^2 * lam i))
      ≤ ∑ b, ∑ i, ‖V i b‖^2 * lam i * Real.log (lam i) := Finset.sum_le_sum (fun b _ => h_per_b b)
    _ = ∑ i, ∑ b, ‖V i b‖^2 * lam i * Real.log (lam i) := Finset.sum_comm
    _ = ∑ i, (∑ b, ‖V i b‖^2) * (lam i * Real.log (lam i)) := by
            apply Finset.sum_congr rfl
            intro i _
            calc (∑ b, ‖V i b‖^2 * lam i * Real.log (lam i))
                = ∑ b, ‖V i b‖^2 * (lam i * Real.log (lam i)) := by
                      apply Finset.sum_congr rfl; intro b _; ring
              _ = (∑ b, ‖V i b‖^2) * (lam i * Real.log (lam i)) := by
                      rw [← Finset.sum_mul]
    _ = ∑ i, lam i * Real.log (lam i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [h_row_sum i, one_mul]

/-! ## 10. The main theorem -/

/-- **DPI of Umegaki relative entropy under projective measurement
    in σ's eigenbasis.**

    For positive-definite density matrices ρ, σ, the classical KL
    divergence between their projective-measurement outcome
    distributions in σ's eigenbasis is bounded above by the Umegaki
    quantum relative entropy:

      `klDivergence (outcomesInSigmaBasis ρ hσ)
                     (outcomesInSigmaBasis σ hσ)
          ≤  umegakiRelativeEntropy ρ σ`. -/
theorem umegaki_dpi_projective_sigma_basis
    (ρ σ : ComplexDensityMatrix n)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef) :
    klDivergence (outcomesInSigmaBasis ρ σ hσ_pos hρ_pos)
                 (outcomesInSigmaBasis σ σ hσ_pos hσ_pos)
      ≤ umegakiRelativeEntropy ρ σ := by
  -- Vacuous case: n = 0.
  by_cases hn : n = 0
  · subst hn
    -- KL is sum over empty index set = 0; umegakiRelativeEntropy similarly.
    have h_kl : klDivergence (outcomesInSigmaBasis ρ σ hσ_pos hρ_pos)
                              (outcomesInSigmaBasis σ σ hσ_pos hσ_pos) = 0 := by
      unfold klDivergence
      apply Finset.sum_eq_zero
      intro i _; exact (Fin.elim0 i)
    have h_S : umegakiRelativeEntropy ρ σ = 0 := by
      unfold umegakiRelativeEntropy operatorLog cfcρ
      -- Tr over empty index set is 0; product of empty-matrix is 0.
      have h_tr : Matrix.trace (ρ.M * (cfc Real.log ρ.M - cfc Real.log σ.M)) = 0 := by
        simp [Matrix.trace, Matrix.diag]
      rw [h_tr, Complex.zero_re]
    rw [h_kl, h_S]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  -- Setup mirrored from KleinInequalityFull.klein_inequality.
  set Uρ : Matrix (Fin n) (Fin n) ℂ := hρ_pos.1.eigenvectorUnitary.val with hUρ_def
  set Uσ : Matrix (Fin n) (Fin n) ℂ := hσ_pos.1.eigenvectorUnitary.val with hUσ_def
  set lam : Fin n → ℝ := hρ_pos.1.eigenvalues with hlam_def
  set mu : Fin n → ℝ := hσ_pos.1.eigenvalues with hmu_def
  set V : Matrix (Fin n) (Fin n) ℂ := star Uρ * Uσ with hV_def
  -- Positivity.
  have hlam_pos : ∀ i, 0 < lam i := fun i => hρ_pos.eigenvalues_pos i
  have hmu_pos : ∀ j, 0 < mu j := fun j => hσ_pos.eigenvalues_pos j
  -- V is unitary.
  have hUρ_mem : Uρ ∈ Matrix.unitaryGroup (Fin n) ℂ := hρ_pos.1.eigenvectorUnitary.2
  have hUσ_mem : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ := hσ_pos.1.eigenvectorUnitary.2
  have hV_mem : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    mul_mem (Unitary.star_mem hUρ_mem) hUσ_mem
  have hV_mul_star : V * star V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hV_mem; exact hV_mem
  have hstar_V_mul_V : star V * V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hV_mem; exact hV_mem
  have hrow_sum : ∀ i, ∑ b, ‖V i b‖^2 = 1 :=
    row_sum_sq_norm_eq_one' V hV_mul_star
  have hcol_sum : ∀ b, ∑ i, ‖V i b‖^2 = 1 :=
    col_sum_sq_norm_eq_one' V hstar_V_mul_V
  -- Establish: p_b(ρ) = ∑_i ‖V_{ib}‖² λ_i, q_b(σ) = μ_b.
  have hp_formula : ∀ b, (outcomesInSigmaBasis ρ σ hσ_pos hρ_pos).p b
                          = ∑ i, ‖V i b‖^2 * lam i := by
    intro b
    show ((star Uσ * ρ.M * Uσ) b b).re = _
    rw [diag_entry_sigma_basis_formula ρ.M hρ_pos Uσ hUσ_mem b,
        Complex.ofReal_re]
  have hq_formula : ∀ b, (outcomesInSigmaBasis σ σ hσ_pos hσ_pos).p b = mu b :=
    fun b => outcomesInSigmaBasis_sigma_eq_eigenvalues σ hσ_pos b
  -- The outcomes for ρ are positive (sum-of-positives + at least one V_{i,b} ≠ 0).
  -- Actually we don't need them positive — only the standard `klTerm` machinery.
  -- Step 1: Expand `klDivergence`.
  unfold klDivergence
  -- KL = ∑ b, klTerm (p_b) (q_b)
  --    = ∑ b, klTerm (∑ i, ‖V_{ib}‖² λ_i) (μ_b)
  have h_KL_eq :
      (∑ b, klTerm ((outcomesInSigmaBasis ρ σ hσ_pos hρ_pos).p b)
                    ((outcomesInSigmaBasis σ σ hσ_pos hσ_pos).p b))
        = ∑ b, klTerm (∑ i, ‖V i b‖^2 * lam i) (mu b) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [hp_formula b, hq_formula b]
  rw [h_KL_eq]
  -- Step 2: Each klTerm (p_b) (μ_b) = p_b * log p_b - p_b * log μ_b
  -- (because p_b ≥ 0 and μ_b > 0).
  have h_klterm_split : ∀ b,
      klTerm (∑ i, ‖V i b‖^2 * lam i) (mu b)
        = (∑ i, ‖V i b‖^2 * lam i) * Real.log (∑ i, ‖V i b‖^2 * lam i)
          - (∑ i, ‖V i b‖^2 * lam i) * Real.log (mu b) := by
    intro b
    rw [klTerm_eq]
    -- (∑ ‖V_{ib}‖² λ_i) * log ((∑ ‖V_{ib}‖² λ_i) / μ_b)
    set p := ∑ i, ‖V i b‖^2 * lam i with hp_def
    by_cases hp_zero : p = 0
    · rw [hp_zero]; simp
    · have hp_pos : 0 < p :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hlam_pos i).le))
                       (Ne.symm hp_zero)
      have hmu_ne : mu b ≠ 0 := ne_of_gt (hmu_pos b)
      rw [Real.log_div hp_zero hmu_ne, mul_sub]
  rw [Finset.sum_congr rfl (fun b _ => h_klterm_split b)]
  rw [Finset.sum_sub_distrib]
  -- KL = (∑ b, p_b log p_b) - (∑ b, p_b log μ_b)
  -- Step 3: Identify (∑ b, p_b log μ_b) = Re Tr (ρ · log σ).
  have h_2nd_eq :
      (∑ b, (∑ i, ‖V i b‖^2 * lam i) * Real.log (mu b))
        = (Matrix.trace (ρ.M * cfc Real.log σ.M)).re := by
    rw [re_trace_mul_cfc_log_eq_sum_outcomes ρ σ hρ_pos hσ_pos]
    apply Finset.sum_congr rfl
    intro b _
    rw [hp_formula b]
  rw [h_2nd_eq]
  -- Now: (∑ b, p_b log p_b) - Re Tr (ρ · log σ) ≤ umegakiRelativeEntropy ρ σ.
  -- Unfold umegakiRelativeEntropy:
  --   S(ρ‖σ) = Re Tr (ρ · (operatorLog ρ - operatorLog σ))
  --          = Re Tr (ρ · log ρ) - Re Tr (ρ · log σ).
  unfold umegakiRelativeEntropy
  have h_S_expand :
      (Matrix.trace (ρ.M * (operatorLog ρ - operatorLog σ))).re
        = (Matrix.trace (ρ.M * cfc Real.log ρ.M)).re
          - (Matrix.trace (ρ.M * cfc Real.log σ.M)).re := by
    show (Matrix.trace (ρ.M * (cfcρ Real.log ρ - cfcρ Real.log σ))).re = _
    unfold cfcρ
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [h_S_expand]
  -- Goal: (∑ b, p_b log p_b) - Re Tr (ρ · log σ) ≤ Re Tr (ρ · log ρ) - Re Tr (ρ · log σ)
  -- i.e. (∑ b, p_b log p_b) ≤ Re Tr (ρ · log ρ).
  -- Re Tr (ρ · log ρ) = ∑ i, λ_i log λ_i  (re_trace_mul_cfc_log_eq_sum).
  rw [re_trace_rho_log_rho ρ hρ_pos]
  -- Goal: (∑ b, p_b log p_b) - Re Tr (ρ · log σ) ≤ (∑ i, λ_i log λ_i) - Re Tr (ρ · log σ).
  -- ⟺ (∑ b, p_b log p_b) ≤ ∑ i, λ_i log λ_i.
  have h_main := sum_p_log_p_le_sum_lam_log_lam
                  (V := V) (lam := lam) hlam_pos hcol_sum hrow_sum
  linarith

/-! ## 11. Axiom audit -/

-- VERIFIED 2026-05-30:
--   #print axioms umegaki_dpi_projective_sigma_basis
--     ⟹  [propext, Classical.choice, Quot.sound]
-- Depends ONLY on Lean's three standard axioms.
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.ProjectiveMeasurementDPI
