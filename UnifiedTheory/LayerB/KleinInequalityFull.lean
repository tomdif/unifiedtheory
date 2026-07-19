/-
  LayerB/KleinInequalityFull.lean
  ────────────────────────────────

  **Klein's inequality, full non-commuting case**, for positive
  definite complex Hermitian matrices `A, B : Matrix (Fin n) (Fin n) ℂ`:

      Re Tr (A − B)  ≤  Re Tr ( A · ( log A − log B ) ) .

  Proof strategy: the two-basis scalar reduction.

    1. Write A = U_A · diag(λ) · star U_A and B = U_B · diag(μ) · star U_B
       using `Matrix.IsHermitian.spectral_theorem`.
    2. Set V := star U_A · U_B (unitary).
    3. The "transition" entries `P_{ij} := ‖V_{ij}‖²` are doubly
       stochastic: rows sum to 1, columns sum to 1.
    4. Tr(A · log B) = ∑_{i,j} λ_i · P_{ij} · log μ_j (mixed-basis formula).
    5. Jensen for log (concave on (0, ∞)):
            ∑_j P_{ij} log μ_j ≤ log (∑_j P_{ij} μ_j).
    6. Scalar Klein per index, applied to `λ_i` and `c_i := ∑_j P_{ij} μ_j`.
    7. ∑ c_i = Tr B (column sums of P = 1).
    Combining 4–7 closes the inequality.

  Immediate corollary (the Lindblad–Uhlmann deliverable):

      0  ≤  S(ρ‖σ)  :=  Re Tr ( ρ · (log ρ − log σ) ).

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.KleinInequality
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KleinInequalityFull

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.SpectralFCTrace
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.OperatorMonotoneLog
open UnifiedTheory.LayerB.KleinInequality
open UnifiedTheory.LayerB.CFCDiagonalDischarge
open UnifiedTheory.LayerB.UmegakiRelativeEntropy

variable {n : ℕ}

/-! ## 1. Spectral form of `cfc Real.log` on a PosDef matrix -/

/-- For a positive-definite Hermitian matrix `B`, the operator log can
    be written explicitly via the spectral theorem as

      `cfc Real.log B = U_B · diagonal (ofReal ∘ log ∘ μ) · star U_B`

    where `U_B = hB.1.eigenvectorUnitary` and `μ = hB.1.eigenvalues`. -/
private lemma cfc_log_spectral_form
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef) :
    cfc Real.log B
      = (hB.1.eigenvectorUnitary.val)
          * Matrix.diagonal (fun j => ((Real.log (hB.1.eigenvalues j) : ℝ) : ℂ))
          * (star hB.1.eigenvectorUnitary.val) := by
  have h_eq : cfc Real.log B = hB.1.cfc Real.log :=
    Matrix.IsHermitian.cfc_eq hB.1 Real.log
  rw [h_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- Analogous spectral form for `A` itself. -/
private lemma posDef_spectral_form
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    A = (hA.1.eigenvectorUnitary.val)
          * Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ))
          * (star hA.1.eigenvectorUnitary.val) := by
  have h := hA.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  -- The diagonal in spectral_theorem uses `RCLike.ofReal ∘ hA.1.eigenvalues`.
  -- We want `(fun i => ((... : ℝ) : ℂ))`; these are definitionally equal.
  exact h

/-! ## 2. Building blocks: trace of conjugation by a unitary -/

/-- Trace cyclicity through a unitary conjugation, in the
    `Matrix.unitaryGroup` flavor. -/
private lemma trace_unitary_conj
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (U * M * star U) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle]
  -- Goal: Tr (star U * U * M) = Tr M
  have h1 : star U * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hU
    exact hU
  rw [h1, Matrix.one_mul]

/-! ## 2b. Helper: `z · star z = ‖z‖² : ℂ` -/

/-- For any complex `z`, `z * star z = (‖z‖² : ℂ)` (as complex numbers). -/
private lemma complex_mul_star_eq_sq_norm (z : ℂ) :
    z * star z = ((‖z‖^2 : ℝ) : ℂ) := by
  -- star = conj for ℂ; z * conj z = normSq z; normSq z = ‖z‖².
  rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl]
  rw [Complex.mul_conj]
  -- Goal: (normSq z : ℂ) = ((‖z‖^2 : ℝ) : ℂ)
  rw [Complex.normSq_eq_norm_sq]

/-- And the dual: `star z * z = (‖z‖² : ℂ)`. -/
private lemma complex_star_mul_eq_sq_norm (z : ℂ) :
    star z * z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [mul_comm]
  exact complex_mul_star_eq_sq_norm z

/-! ## 3. The unitary V := star U_A * U_B and its squared entries P -/

/-- Define `V := star U_A · U_B`.  Since both `U_A` and `U_B` are
    unitary, so is `V`. -/
private lemma V_is_unitary
    (UA UB : Matrix (Fin n) (Fin n) ℂ)
    (hUA : UA ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hUB : UB ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (star UA * UB) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  -- The unitary group is closed under multiplication and stars.
  have h_starUA : star UA ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hUA
  exact mul_mem h_starUA hUB

/-- For any unitary V, the rows of |V_{ij}|² sum to 1.

    From V * star V = 1, taking entry (i,i):
    1 = ∑_j V_{ij} · (star V)_{ji} = ∑_j V_{ij} · conj V_{ij} = ∑_j ‖V_{ij}‖². -/
private lemma row_sum_sq_norm_eq_one
    (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V * star V = 1)
    (i : Fin n) :
    ∑ j, ‖V i j‖^2 = 1 := by
  have h : (V * star V) i i = (1 : Matrix (Fin n) (Fin n) ℂ) i i := by
    rw [hV]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  -- (star V) j i = star (V i j) = conj (V i j)
  -- V i j * conj (V i j) = ‖V i j‖² (as ℂ).
  have h2 : ∀ j, V i j * (star V) j i = ((‖V i j‖^2 : ℝ) : ℂ) := by
    intro j
    show V i j * star (V i j) = _
    exact complex_mul_star_eq_sq_norm (V i j)
  rw [Finset.sum_congr rfl (fun j _ => h2 j)] at h
  have h3 : ((∑ j, ‖V i j‖^2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]
    push_cast
    rfl
  exact_mod_cast h3

/-- The column sums of |V_{ij}|² also sum to 1.

    From star V * V = 1, taking entry (j,j):
    1 = ∑_i (star V)_{ji} · V_{ij} = ∑_i conj V_{ij} · V_{ij} = ∑_i ‖V_{ij}‖². -/
private lemma col_sum_sq_norm_eq_one
    (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : star V * V = 1)
    (j : Fin n) :
    ∑ i, ‖V i j‖^2 = 1 := by
  have h : (star V * V) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by
    rw [hV]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ i, (star V) j i * V i j = ((‖V i j‖^2 : ℝ) : ℂ) := by
    intro i
    show star (V i j) * V i j = _
    exact complex_star_mul_eq_sq_norm (V i j)
  rw [Finset.sum_congr rfl (fun i _ => h2 i)] at h
  have h3 : ((∑ i, ‖V i j‖^2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]
    push_cast
    rfl
  exact_mod_cast h3

/-! ## 4. The mixed-basis trace formula -/

/-- **Mixed-basis trace formula.**  For positive-definite Hermitian
    matrices A and B with eigen-decompositions A = U_A · diag(λ) · star U_A,
    B = U_B · diag(μ) · star U_B, setting V := star U_A · U_B,

      `Tr(A · cfc Real.log B) = ∑_i ∑_j ‖V_{ij}‖² · λ_i · log μ_j`. -/
lemma trace_mul_cfc_log_eq_sum_mixed
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    Matrix.trace (A * cfc Real.log B)
      = ∑ i, ∑ j,
          ((‖((star hA.1.eigenvectorUnitary.val)
              * hB.1.eigenvectorUnitary.val) i j‖^2 : ℝ) : ℂ)
            * ((hA.1.eigenvalues i : ℝ) : ℂ)
            * ((Real.log (hB.1.eigenvalues j) : ℝ) : ℂ) := by
  -- Notation.
  set UA : Matrix (Fin n) (Fin n) ℂ := hA.1.eigenvectorUnitary.val with hUA_def
  set UB : Matrix (Fin n) (Fin n) ℂ := hB.1.eigenvectorUnitary.val with hUB_def
  set lam : Fin n → ℝ := hA.1.eigenvalues with hlam_def
  set mu : Fin n → ℝ := hB.1.eigenvalues with hmu_def
  set Dlam : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))
  set Dlog : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.diagonal (fun j => ((Real.log (mu j) : ℝ) : ℂ))
  set V : Matrix (Fin n) (Fin n) ℂ := star UA * UB with hV_def
  -- Spectral decompositions.
  have hA_spec : A = UA * Dlam * star UA := posDef_spectral_form A hA
  have hlogB_spec : cfc Real.log B = UB * Dlog * star UB :=
    cfc_log_spectral_form B hB
  -- Substitute.
  rw [hA_spec, hlogB_spec]
  -- A * log B = UA * Dlam * (star UA * UB) * Dlog * star UB
  --           = UA * (Dlam * V * Dlog * star UB).
  have hreassoc :
      UA * Dlam * star UA * (UB * Dlog * star UB)
        = UA * (Dlam * V * Dlog * star UB) := by
    rw [hV_def]; noncomm_ring
  rw [hreassoc]
  -- Now use Tr (UA * X) = Tr (X * UA).
  rw [Matrix.trace_mul_comm]
  -- Goal: Tr (Dlam * V * Dlog * star UB * UA) = (the sum)
  -- Now `star UB * UA = star V`:
  have hstar_V_eq : star V = star UB * UA := by
    rw [hV_def, StarMul.star_mul, star_star]
  rw [show Dlam * V * Dlog * star UB * UA
        = Dlam * V * Dlog * (star UB * UA) by noncomm_ring,
      ← hstar_V_eq]
  -- Now: Tr (Dlam * V * Dlog * star V) = ∑_i ∑_j ...
  -- Expand via trace = ∑_i diag, and unfold the matrix products.
  rw [Matrix.trace]
  show ∑ i, Matrix.diag (Dlam * V * Dlog * star V) i = _
  -- For each i, diag (M) i = M i i = ∑_k (Dlam * V) i k * (Dlog * star V) k i.
  -- (Dlam * V) i k = lam i * V i k (after diagonal_mul); but this needs Dlam diagonal.
  -- Better: directly compute the (i,i) entry.
  apply Finset.sum_congr rfl
  intro i _
  -- M_{ii} where M = Dlam * V * Dlog * star V
  -- (M)_{ii} = ∑_j (Dlam * V * Dlog)_{ij} * (star V)_{ji}
  -- And (Dlam * V * Dlog)_{ij} = (Dlam * V)_{ij} * (Dlog j j -- wait, only when nonzero)
  -- Recall mul_diagonal: (M * diag d)_{ij} = M_{ij} * d_j; diagonal_mul: (diag d * M)_{ij} = d_i * M_{ij}.
  -- So (Dlam * V)_{ik} = (lam i : ℂ) * V_{ik} (diagonal_mul applied to V).
  --    (Dlam * V * Dlog)_{ij} = ((Dlam * V) * Dlog)_{ij} = (Dlam * V)_{ij} * (Dlog applied at j j) -- wait Dlog is at position (j,j).
  --    = (lam i : ℂ) * V_{ij} * (log mu j : ℂ).
  -- And (star V)_{ji} = star (V_{ij}) = conj (V_{ij}).
  -- So M_{ii} = ∑_j (lam i : ℂ) * V_{ij} * (log mu j : ℂ) * conj (V_{ij})
  --          = ∑_j (‖V_{ij}‖² : ℂ) * (lam i : ℂ) * (log mu j : ℂ)
  --          (since V · conj V = ‖V‖² real, but order matters; we'll reassociate).
  show (Dlam * V * Dlog * star V) i i = _
  -- Compute by unfolding mul_apply repeatedly.
  rw [Matrix.mul_apply]
  -- ∑ j, (Dlam * V * Dlog) i j * (star V) j i
  -- Compute each (Dlam * V * Dlog) i j.
  have h_entry : ∀ j,
      (Dlam * V * Dlog) i j = ((lam i : ℝ) : ℂ) * V i j
                                * ((Real.log (mu j) : ℝ) : ℂ) := by
    intro j
    rw [show Dlam * V * Dlog = Dlam * (V * Dlog) by noncomm_ring]
    rw [Matrix.diagonal_mul]
    -- (Dlam * (V * Dlog))_{ij} = lam i * (V * Dlog)_{ij}
    -- And (V * Dlog)_{ij} = V_{ij} * log μ_j.
    show _ * (V * Dlog) i j = _
    rw [Matrix.mul_diagonal]
    ring
  rw [Finset.sum_congr rfl (fun j _ => by rw [h_entry j])]
  -- Now ∑ j, ((lam i : ℂ) * V_{ij} * (log mu j : ℂ)) * (star V) j i
  -- (star V) j i = star (V i j) = conj (V i j)
  -- We want ∑ j, (‖V_{ij}‖² : ℂ) * (lam i : ℂ) * (log mu j : ℂ)
  apply Finset.sum_congr rfl
  intro j _
  show ((lam i : ℝ) : ℂ) * V i j * ((Real.log (mu j) : ℝ) : ℂ)
          * (star V) j i = _
  -- (star V) j i = star (V i j)
  have h_starV : (star V) j i = star (V i j) := by
    show (star V) j i = star (V i j)
    rfl
  rw [h_starV]
  -- LHS = (lam i : ℂ) * V_{ij} * (log mu j : ℂ) * star (V_{ij})
  -- = (V_{ij} * star V_{ij}) * (lam i : ℂ) * (log mu j : ℂ)
  -- = (‖V_{ij}‖² : ℂ) * (lam i : ℂ) * (log mu j : ℂ).
  have h_mod : V i j * star (V i j) = ((‖V i j‖^2 : ℝ) : ℂ) :=
    complex_mul_star_eq_sq_norm (V i j)
  -- We want to use h_mod.  Rearrange:
  have hreorder :
      ((lam i : ℝ) : ℂ) * V i j * ((Real.log (mu j) : ℝ) : ℂ) * star (V i j)
        = (V i j * star (V i j)) * ((lam i : ℝ) : ℂ) * ((Real.log (mu j) : ℝ) : ℂ) := by
    ring
  rw [hreorder, h_mod]

/-! ## 5. Finite Jensen for `Real.log` -/

/-- **Finite Jensen for `Real.log`.**  For a probability vector `P` and
    a strictly positive function `μ` on a finite index set,

      `∑_i P_i · log μ_i  ≤  log (∑_i P_i · μ_i)`. -/
private lemma jensen_log_finite_sum
    {ι : Type*} [Fintype ι] (P : ι → ℝ) (μ : ι → ℝ)
    (hP_nonneg : ∀ i, 0 ≤ P i) (hP_sum : ∑ i, P i = 1)
    (hμ_pos : ∀ i, 0 < μ i) :
    ∑ i, P i * Real.log (μ i) ≤ Real.log (∑ i, P i * μ i) := by
  -- Use ConcaveOn.le_map_sum on Real.log over Set.Ioi 0.
  have h_concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have h_w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ P i := fun i _ => hP_nonneg i
  have h_w_sum : ∑ i ∈ Finset.univ, P i = 1 := hP_sum
  have h_mem : ∀ i ∈ Finset.univ, μ i ∈ Set.Ioi (0 : ℝ) := fun i _ => hμ_pos i
  have hJensen := h_concave.le_map_sum h_w_nonneg h_w_sum h_mem
  -- Convert smul to multiplication.
  simp only [smul_eq_mul] at hJensen
  exact hJensen

/-! ## 6. Per-eigenvalue setup: `c_i = ∑_j P_{ij} μ_j > 0`, etc. -/

/-- The "transition" matrix `P_{ij} := ‖V_{ij}‖²` has nonneg entries. -/
private lemma transition_nonneg
    (V : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    0 ≤ ‖V i j‖^2 := sq_nonneg _

/-- Convex combination `c_i := ∑_j P_{ij} · μ_j` of strictly positive
    values, with row-sum-1 weights, is strictly positive whenever n > 0
    (so the sum is non-empty). -/
private lemma cbar_pos
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → ℝ) (μ : ι → ℝ)
    (hP_nonneg : ∀ j, 0 ≤ P j) (hP_sum : ∑ j, P j = 1)
    (hμ_pos : ∀ j, 0 < μ j) :
    0 < ∑ j, P j * μ j := by
  -- The sum equals 1 means at least one P j > 0.
  obtain ⟨j₀, hj₀⟩ : ∃ j, 0 < P j := by
    by_contra hcontra
    push_neg at hcontra
    -- Then P j ≤ 0 for all j, combined with hP_nonneg → P j = 0.
    have h_all_zero : ∀ j, P j = 0 := fun j =>
      le_antisymm (hcontra j) (hP_nonneg j)
    have : ∑ j, P j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact h_all_zero j
    rw [this] at hP_sum
    exact zero_ne_one hP_sum
  -- Now ∑ P j * μ j ≥ P j₀ * μ j₀ > 0.
  have h_ge : ∑ j, P j * μ j ≥ P j₀ * μ j₀ := by
    have h_terms_nonneg : ∀ j ∈ Finset.univ, 0 ≤ P j * μ j := fun j _ =>
      mul_nonneg (hP_nonneg j) (hμ_pos j).le
    calc ∑ j, P j * μ j
        = ∑ j ∈ Finset.univ, P j * μ j := rfl
      _ ≥ P j₀ * μ j₀ :=
        Finset.single_le_sum (f := fun j => P j * μ j) h_terms_nonneg
          (Finset.mem_univ j₀)
  have h_pos : 0 < P j₀ * μ j₀ := mul_pos hj₀ (hμ_pos j₀)
  linarith

/-! ## 7. The main theorem: Klein's inequality (non-commuting case) -/

/-- **Klein's inequality** for positive definite Hermitian matrices.

    For `A B : Matrix (Fin n) (Fin n) ℂ` both positive definite,

      `Re Tr (A − B)  ≤  Re Tr ( A · ( log A − log B ) )`. -/
theorem klein_inequality
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    (Matrix.trace A - Matrix.trace B).re
      ≤ (Matrix.trace (A * (cfc Real.log A - cfc Real.log B))).re := by
  -- Handle n = 0 specially (vacuous).
  by_cases hn : n = 0
  · subst hn
    -- Use klein_inequality_zero from KleinInequality.lean.
    exact klein_inequality_zero A B hA hB
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  -- Notation.
  set UA : Matrix (Fin n) (Fin n) ℂ := hA.1.eigenvectorUnitary.val with hUA_def
  set UB : Matrix (Fin n) (Fin n) ℂ := hB.1.eigenvectorUnitary.val with hUB_def
  set lam : Fin n → ℝ := hA.1.eigenvalues with hlam_def
  set mu : Fin n → ℝ := hB.1.eigenvalues with hmu_def
  set V : Matrix (Fin n) (Fin n) ℂ := star UA * UB with hV_def
  -- Positivity of eigenvalues.
  have hlam_pos : ∀ i, 0 < lam i := fun i => hA.eigenvalues_pos i
  have hmu_pos : ∀ j, 0 < mu j := fun j => hB.eigenvalues_pos j
  -- V is unitary.
  have hUA_mem : UA ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hA.1.eigenvectorUnitary.2
  have hUB_mem : UB ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hB.1.eigenvectorUnitary.2
  have hV_mem : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    V_is_unitary UA UB hUA_mem hUB_mem
  have hV_mul_star : V * star V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hV_mem
    exact hV_mem
  have hstar_V_mul_V : star V * V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hV_mem
    exact hV_mem
  -- P_{ij} := ‖V_{ij}‖²; row sums = column sums = 1.
  have hrow_sum : ∀ i, ∑ j, ‖V i j‖^2 = 1 :=
    row_sum_sq_norm_eq_one V hV_mul_star
  have hcol_sum : ∀ j, ∑ i, ‖V i j‖^2 = 1 :=
    col_sum_sq_norm_eq_one V hstar_V_mul_V
  -- Define c_i := ∑_j ‖V_{ij}‖² · μ_j.
  set cbar : Fin n → ℝ := fun i => ∑ j, ‖V i j‖^2 * mu j with hcbar_def
  have hcbar_pos : ∀ i, 0 < cbar i := by
    intro i
    rw [hcbar_def]
    exact cbar_pos (fun j => ‖V i j‖^2) mu
      (fun j => sq_nonneg _) (hrow_sum i) hmu_pos
  /- ============================================================
     Step A: LHS of Klein = ∑ (lam i - cbar i).
     ============================================================ -/
  -- Tr A = ∑ lam i.
  have h_trace_A : (Matrix.trace A).re = ∑ i, lam i := by
    have h : Matrix.trace A = ∑ i, ((lam i : ℝ) : ℂ) :=
      hA.1.trace_eq_sum_eigenvalues
    rw [h, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.ofReal_re _
  -- Tr B = ∑ mu j.
  have h_trace_B : (Matrix.trace B).re = ∑ j, mu j := by
    have h : Matrix.trace B = ∑ j, ((mu j : ℝ) : ℂ) :=
      hB.1.trace_eq_sum_eigenvalues
    rw [h, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact Complex.ofReal_re _
  -- ∑_i cbar i = ∑_j mu j  (column sums of P).
  have h_cbar_sum_eq_trace_B : ∑ i, cbar i = ∑ j, mu j := by
    -- ∑_i cbar i = ∑_i ∑_j ‖V i j‖² · μ_j
    --           = ∑_j (∑_i ‖V i j‖²) · μ_j   (swap)
    --           = ∑_j μ_j   (column sums = 1).
    rw [hcbar_def]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hcol_sum j, one_mul]
  -- (Tr A - Tr B).re = ∑ (lam i - cbar i).
  have h_LHS_eq : (Matrix.trace A - Matrix.trace B).re = ∑ i, (lam i - cbar i) := by
    rw [Complex.sub_re, h_trace_A, h_trace_B, ← h_cbar_sum_eq_trace_B,
        Finset.sum_sub_distrib]
  /- ============================================================
     Step B: RHS of Klein = ∑ lam i · log lam i - ∑_{i,j} ‖V_{ij}‖² · lam i · log mu j.
     ============================================================ -/
  -- Re Tr (A * log A) = ∑ lam i · log lam i.
  have h_RHS_A : (Matrix.trace (A * cfc Real.log A)).re
                = ∑ i, lam i * Real.log (lam i) :=
    re_trace_mul_cfc_log_eq_sum A hA
  -- Re Tr (A * log B) = ∑_{i,j} ‖V_{ij}‖² · lam i · log mu j.
  have h_RHS_B : (Matrix.trace (A * cfc Real.log B)).re
                = ∑ i, ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j) := by
    rw [trace_mul_cfc_log_eq_sum_mixed A B hA hB]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    -- ((‖V_{ij}‖^2 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ) * ((log mu j : ℝ) : ℂ)
    -- → ‖V_{ij}‖^2 * lam i * log mu j  (real part)
    rw [show ((‖V i j‖^2 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ) * ((Real.log (mu j) : ℝ) : ℂ)
          = ((‖V i j‖^2 * lam i * Real.log (mu j) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  -- Combine: Re Tr (A * (log A - log B)) = ∑ lam i · log lam i - ∑_{i,j} ‖V_{ij}‖² · lam i · log mu j.
  have h_RHS_eq :
      (Matrix.trace (A * (cfc Real.log A - cfc Real.log B))).re
        = (∑ i, lam i * Real.log (lam i))
            - ∑ i, ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, h_RHS_A, h_RHS_B]
  /- ============================================================
     Step C: Jensen + Klein scalar combine to close the inequality.
     ============================================================ -/
  rw [h_LHS_eq, h_RHS_eq]
  -- Per-i lower bound on RHS-i contribution.
  -- ∑_j ‖V_{ij}‖² · log μ_j ≤ log (∑_j ‖V_{ij}‖² · μ_j) = log cbar_i  (Jensen).
  have h_per_i_jensen : ∀ i,
      ∑ j, ‖V i j‖^2 * Real.log (mu j) ≤ Real.log (cbar i) := by
    intro i
    rw [hcbar_def]
    exact jensen_log_finite_sum (fun j => ‖V i j‖^2) mu
      (fun j => sq_nonneg _) (hrow_sum i) hmu_pos
  -- Per-i scalar Klein.
  have h_per_i_klein : ∀ i,
      lam i - cbar i ≤ lam i * Real.log (lam i) - lam i * Real.log (cbar i) :=
    fun i => klein_scalar (hlam_pos i) (hcbar_pos i)
  -- Combine.
  -- We want: ∑ (lam i - cbar i)
  --           ≤ ∑ lam i · log lam i - ∑ ∑ ‖V_{ij}‖² · lam i · log μ_j.
  -- Rearrange ∑ ∑ ‖V_{ij}‖² · lam i · log μ_j = ∑ i, lam i · (∑ j, ‖V_{ij}‖² · log μ_j).
  have h_inner_factor : ∀ i,
      ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j)
        = lam i * ∑ j, ‖V i j‖^2 * Real.log (mu j) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_inner_factor i)]
  -- Now: ∑ (lam i - cbar i) ≤ ∑ lam i · log lam i - ∑ lam i · (∑ ‖V_{ij}‖² log μ_j)
  -- Equivalently: ∑ ((lam i · log lam i) - lam i · (∑ ‖V_{ij}‖² log μ_j) - (lam i - cbar i)) ≥ 0.
  -- We'll use: per-i,
  --   lam i - cbar i
  --     ≤ lam i log lam i - lam i log cbar i           (klein)
  --     ≤ lam i log lam i - lam i (∑ ‖V_{ij}‖² log μ_j)  (Jensen, with lam i ≥ 0).
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  -- per-i: lam i - cbar i ≤ lam i log lam i - lam i (∑ ‖V_{ij}‖² log μ_j)
  have hk := h_per_i_klein i
  have hj := h_per_i_jensen i
  -- lam i ≥ 0; multiply hj by lam i to get lam i · (∑ ‖V_{ij}‖² log μ_j) ≤ lam i · log cbar i.
  have hlam_i_nn : 0 ≤ lam i := (hlam_pos i).le
  have hj_scaled : lam i * (∑ j, ‖V i j‖^2 * Real.log (mu j))
                    ≤ lam i * Real.log (cbar i) :=
    mul_le_mul_of_nonneg_left hj hlam_i_nn
  -- klein:  lam i - cbar i ≤ lam i log lam i - lam i log cbar i
  -- Need to show ≤ lam i log lam i - lam i (∑ ‖V_{ij}‖² log μ_j).
  linarith

/-! ## 8. Corollary: Umegaki relative entropy is nonneg (Gibbs) -/

/-- **Gibbs's inequality / non-negativity of Umegaki relative entropy.**

    For two positive-definite density matrices ρ, σ,

      `0  ≤  S(ρ‖σ)  :=  Re Tr ( ρ · (log ρ − log σ) )`. -/
theorem umegakiRelativeEntropy_nonneg
    (ρ σ : ComplexDensityMatrix n)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef) :
    0 ≤ umegakiRelativeEntropy ρ σ := by
  -- Klein's inequality applied to ρ.M and σ.M.
  have hKlein := klein_inequality ρ.M σ.M hρ_pos hσ_pos
  -- LHS = (Tr ρ - Tr σ).re = (1 - 1).re = 0.
  have h_trρ := ρ.hTrace
  have h_trσ := σ.hTrace
  have h_LHS : (Matrix.trace ρ.M - Matrix.trace σ.M).re = 0 := by
    rw [h_trρ, h_trσ, sub_self, Complex.zero_re]
  rw [h_LHS] at hKlein
  -- umegakiRelativeEntropy ρ σ = (Tr (ρ.M * (operatorLog ρ - operatorLog σ))).re
  -- and operatorLog ρ = cfc Real.log ρ.M (since cfcρ Real.log ρ = cfc Real.log ρ.M).
  unfold umegakiRelativeEntropy
  unfold operatorLog
  show 0 ≤ (Matrix.trace (ρ.M * (cfcρ Real.log ρ - cfcρ Real.log σ))).re
  unfold cfcρ
  exact hKlein

/-! ## 9. Axiom audit. -/

-- VERIFIED 2026-05-30:
--   #print axioms klein_inequality
--     ⟹  [propext, Classical.choice, Quot.sound]
--   #print axioms umegakiRelativeEntropy_nonneg
--     ⟹  [propext, Classical.choice, Quot.sound]
-- Both depend ONLY on Lean's three standard axioms.
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.KleinInequalityFull
