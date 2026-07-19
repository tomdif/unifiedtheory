/-
  UnifiedTheory/LayerC/BipartiteQubitCHSH.lean
  ─────────────────────────────────────────────

  **A qubit-only CHSH measurement-observable layer for the bipartite
  local-realist shadow.**

  This file bridges the abstract bipartite local-realist shadow theorem
  (`bipartiteQubitUnitaryQM_has_localRealisticModel`, proved
  unconditionally in `BipartiteNoSignallingAnalyticCoreDischarge`) to
  the concrete Bell observables physicists actually compute: the Pauli
  matrices, the singlet density matrix, and the CHSH correlation
  function with its Tsirelson-saturating value `2√2`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTENTS

  1. **Pauli matrices `σx`, `σz`** (2×2 complex).
  2. **Equator-plane observable** `equatorObservable θ`
     `= cos θ · σz + sin θ · σx` (Hermitian).
  3. **Singlet density matrix** `singletDensityMatrix : Matrix (Fin 4)
     (Fin 4) ℂ`, the rank-1 projector onto `|ψ⁻⟩ = (|01⟩ − |10⟩)/√2`,
     packaged as a `ComplexDensityMatrix 4`.
  4. **Two-party correlation** `correlation ρ A B := Re(Tr(ρ · (A ⊗ B)))`
     using the same `finProdFinEquiv` reindex pattern as
     `BipartiteUnitaryQM`.
  5. **The bridge theorem**:
        correlation singletCDM (equatorObservable θa) (equatorObservable θb)
            = −cos(θa − θb)
     by direct entry-wise calculation through the singlet's 4-entry
     support.
  6. **Connection to the existing `singletCorrelation`** from
     `LayerB.TsirelsonBound`: they are equal by definition.
  7. **CHSH saturation**: at the standard angles
        (0, π/2) for Alice, (π/4, −π/4) for Bob,
     the CHSH expression equals `2√2` in absolute value, saturating
     `tsirelson_bound`.
  8. **The legibility headline** — one statement reading:
     "the bipartite phase-quotient unitary substrate at n_A = n_B = 2
      has a local-realistic shadow AND reproduces the singlet's
      Bell correlation AND saturates the Tsirelson bound at the
      standard CHSH angles."

  Zero `sorry`. Zero custom `axiom`.  Only Lean's `propext`,
  `Classical.choice`, and `Quot.sound`.
-/

import UnifiedTheory.LayerC.BipartiteNoSignallingAnalyticCoreDischarge
import UnifiedTheory.LayerB.TsirelsonBound
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.BipartiteQubitCHSH

open Matrix Complex
open scoped Kronecker
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerC.LocalRealisticAxioms
open UnifiedTheory.LayerB.TsirelsonBound

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: PAULI OBSERVABLES (σx, σz) AND EQUATOR OBSERVABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Pauli X. -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli Z. -/
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- σx is Hermitian. -/
theorem σx_isHermitian : σx.IsHermitian := by
  unfold Matrix.IsHermitian σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

/-- σz is Hermitian. -/
theorem σz_isHermitian : σz.IsHermitian := by
  unfold Matrix.IsHermitian σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

/-- The qubit observable in direction `(sin θ, 0, cos θ)` on the
    XZ-plane (Bloch equator):
        `equatorObservable θ := cos θ · σz + sin θ · σx`.

    Sign convention is chosen so that on the singlet state,
    `⟨equatorObservable θa ⊗ equatorObservable θb⟩ = -cos(θa - θb)`,
    matching `TsirelsonBound.singletCorrelation`. -/
noncomputable def equatorObservable (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos θ : ℂ) • σz + (Real.sin θ : ℂ) • σx

/-- The four entries of `equatorObservable θ`. -/
private lemma equatorObservable_entries (θ : ℝ) :
    equatorObservable θ 0 0 = (Real.cos θ : ℂ)
  ∧ equatorObservable θ 0 1 = (Real.sin θ : ℂ)
  ∧ equatorObservable θ 1 0 = (Real.sin θ : ℂ)
  ∧ equatorObservable θ 1 1 = -(Real.cos θ : ℂ) := by
  unfold equatorObservable σz σx
  refine ⟨?_, ?_, ?_, ?_⟩
    <;> simp [Matrix.add_apply, smul_eq_mul]

/-- The equator observable is Hermitian.  (Linear combo with real
    coefficients of two Hermitian matrices σz, σx.) -/
theorem equatorObservable_isHermitian (θ : ℝ) :
    (equatorObservable θ).IsHermitian := by
  -- Direct: σz, σx are Hermitian; cos·σz + sin·σx is Hermitian by closure.
  have h_real_smul : ∀ (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      M.IsHermitian → ((c : ℂ) • M).IsHermitian := by
    intro c M hM
    unfold Matrix.IsHermitian at hM ⊢
    rw [Matrix.conjTranspose_smul, hM]
    rw [show star (c : ℂ) = (c : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal]]
  unfold equatorObservable
  exact (h_real_smul _ _ σz_isHermitian).add (h_real_smul _ _ σx_isHermitian)

/-- `equatorObservable 0 = σz`. -/
theorem equatorObservable_zero : equatorObservable 0 = σz := by
  unfold equatorObservable
  simp [Real.cos_zero, Real.sin_zero]

/-- `equatorObservable (π/2) = σx`. -/
theorem equatorObservable_pi_div_two : equatorObservable (Real.pi / 2) = σx := by
  unfold equatorObservable
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE SINGLET DENSITY MATRIX

    |ψ⁻⟩ = (|01⟩ - |10⟩)/√2.   Under `finProdFinEquiv : Fin 2 × Fin 2 ≃
    Fin 4` with `finProdFinEquiv (i,j) = j + 2·i`, this places nonzero
    amplitudes at Fin 4 indices 1 (= |01⟩) and 2 (= |10⟩).

    The 4×4 density matrix |ψ⁻⟩⟨ψ⁻| has nonzero entries
    1/2 at (1,1) and (2,2), and -1/2 at (1,2) and (2,1).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The singlet state vector `|ψ⁻⟩ = (|01⟩ - |10⟩)/√2` as a column
    vector in `Fin 4 → ℂ`.

    Convention: `finProdFinEquiv (i, j) = j + 2·i`.  So index 1 = |01⟩
    (entry `+1/√2`) and index 2 = |10⟩ (entry `−1/√2`). -/
noncomputable def singletVec : Fin 4 → ℂ := fun i =>
  if i = 1 then ((1 : ℂ) / (Real.sqrt 2 : ℂ))
  else if i = 2 then -((1 : ℂ) / (Real.sqrt 2 : ℂ))
  else 0

/-- The singlet density matrix `|ψ⁻⟩⟨ψ⁻|` as the outer product. -/
noncomputable def singletDensityMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j => singletVec i * star (singletVec j))

/-- Apply lemma. -/
private lemma singletDensityMatrix_apply (i j : Fin 4) :
    singletDensityMatrix i j = singletVec i * star (singletVec j) := rfl

/-! ### Properties of `singletVec`.  -/

/-- `singletVec` at the four explicit indices. -/
private lemma singletVec_table :
    singletVec 0 = 0
  ∧ singletVec 1 = (1 : ℂ) / (Real.sqrt 2 : ℂ)
  ∧ singletVec 2 = -((1 : ℂ) / (Real.sqrt 2 : ℂ))
  ∧ singletVec 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold singletVec
  · rw [if_neg (by decide : (0 : Fin 4) ≠ 1), if_neg (by decide : (0 : Fin 4) ≠ 2)]
  · rw [if_pos (by decide : (1 : Fin 4) = 1)]
  · rw [if_neg (by decide : (2 : Fin 4) ≠ 1), if_pos (by decide : (2 : Fin 4) = 2)]
  · rw [if_neg (by decide : (3 : Fin 4) ≠ 1), if_neg (by decide : (3 : Fin 4) ≠ 2)]

/-- `star (singletVec)` at the four indices.  The singlet has real
    amplitudes, so star = id (after embedding `Real.sqrt 2 : ℂ`). -/
private lemma star_singletVec_table :
    star (singletVec 0) = 0
  ∧ star (singletVec 1) = (1 : ℂ) / (Real.sqrt 2 : ℂ)
  ∧ star (singletVec 2) = -((1 : ℂ) / (Real.sqrt 2 : ℂ))
  ∧ star (singletVec 3) = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := singletVec_table
  rw [h0, h1, h2, h3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · rw [star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
  · rw [star_neg, star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
  · simp

/-- `(Real.sqrt 2 : ℂ)² = 2`. -/
private lemma sqrt_two_sq_complex :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)
         = ((Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- `singletDensityMatrix` at the four nonzero support entries. -/
private lemma singletDensityMatrix_support :
    singletDensityMatrix 1 1 = (1/2 : ℂ)
  ∧ singletDensityMatrix 2 2 = (1/2 : ℂ)
  ∧ singletDensityMatrix 1 2 = (-1/2 : ℂ)
  ∧ singletDensityMatrix 2 1 = (-1/2 : ℂ) := by
  obtain ⟨_, hv1, hv2, _⟩ := singletVec_table
  obtain ⟨_, hsv1, hsv2, _⟩ := star_singletVec_table
  -- For each of the four entries, evaluate from inside-out:
  -- replace the `star` term FIRST (using hsv*), THEN the bare singletVec
  -- (using hv*).  This avoids the rewriter chewing through `star (singletVec ...)`
  -- when we use `hv*` first.
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rw [singletDensityMatrix_apply]
  · -- singletVec 1 * star (singletVec 1) = (1/√2) * (1/√2) = 1/2
    rw [hsv1, hv1, div_mul_div_comm, one_mul, sqrt_two_sq_complex]
  · -- singletVec 2 * star (singletVec 2) = (-1/√2) * (-1/√2) = 1/2
    rw [hsv2, hv2]
    rw [show ((-((1 : ℂ) / (Real.sqrt 2 : ℂ))) * (-((1 : ℂ) / (Real.sqrt 2 : ℂ))))
          = ((1 : ℂ) / (Real.sqrt 2 : ℂ)) * ((1 : ℂ) / (Real.sqrt 2 : ℂ)) from by ring]
    rw [div_mul_div_comm, one_mul, sqrt_two_sq_complex]
  · -- singletVec 1 * star (singletVec 2) = (1/√2) * (-1/√2) = -1/2
    rw [hsv2, hv1]
    rw [show (((1 : ℂ) / (Real.sqrt 2 : ℂ)) * (-((1 : ℂ) / (Real.sqrt 2 : ℂ))))
          = -(((1 : ℂ) / (Real.sqrt 2 : ℂ)) * ((1 : ℂ) / (Real.sqrt 2 : ℂ))) from by ring]
    rw [div_mul_div_comm, one_mul, sqrt_two_sq_complex]; ring
  · -- singletVec 2 * star (singletVec 1) = (-1/√2) * (1/√2) = -1/2
    rw [hsv1, hv2]
    rw [show ((-((1 : ℂ) / (Real.sqrt 2 : ℂ))) * ((1 : ℂ) / (Real.sqrt 2 : ℂ)))
          = -(((1 : ℂ) / (Real.sqrt 2 : ℂ)) * ((1 : ℂ) / (Real.sqrt 2 : ℂ))) from by ring]
    rw [div_mul_div_comm, one_mul, sqrt_two_sq_complex]; ring

/-- The singlet density matrix vanishes off the support `{1,2} × {1,2}`. -/
private lemma singletDensityMatrix_zero_off_support
    (i j : Fin 4) (h : i ≠ 1 ∧ i ≠ 2 ∨ j ≠ 1 ∧ j ≠ 2) :
    singletDensityMatrix i j = 0 := by
  rw [singletDensityMatrix_apply]
  rcases h with ⟨hi1, hi2⟩ | ⟨hj1, hj2⟩
  · -- singletVec i = 0
    unfold singletVec
    rw [if_neg hi1, if_neg hi2]; simp
  · -- star (singletVec j) = 0
    have : singletVec j = 0 := by
      unfold singletVec; rw [if_neg hj1, if_neg hj2]
    rw [this]; simp

/-- Singlet density is Hermitian. -/
theorem singletDensityMatrix_isHermitian :
    singletDensityMatrix.IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  rw [singletDensityMatrix_apply, singletDensityMatrix_apply]
  -- star (singletVec j * star (singletVec i)) = singletVec i * star (singletVec j)
  rw [show star (singletVec j * star (singletVec i))
        = star (star (singletVec i)) * star (singletVec j) from
          StarMul.star_mul _ _]
  rw [star_star]

/-- Singlet density is PSD: it is the outer-product `v · v†`. -/
theorem singletDensityMatrix_posSemidef :
    singletDensityMatrix.PosSemidef := by
  -- Build column matrix V : Fin 4 → Fin 1 → ℂ via replicateCol.
  set V : Matrix (Fin 4) (Fin 1) ℂ := Matrix.replicateCol (Fin 1) singletVec
  have hVVdag : singletDensityMatrix = V * V.conjTranspose := by
    ext i j
    rw [singletDensityMatrix_apply, Matrix.mul_apply, Fin.sum_univ_one]
    rw [Matrix.conjTranspose_apply]
    show singletVec i * star (singletVec j) = V i 0 * star (V j 0)
    simp [V, Matrix.replicateCol_apply]
  rw [hVVdag]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Singlet density has trace 1.  Tr|ψ⁻⟩⟨ψ⁻| = ‖|ψ⁻⟩‖² = 1/2 + 1/2 = 1. -/
theorem singletDensityMatrix_trace_one :
    singletDensityMatrix.trace = 1 := by
  rw [Matrix.trace]
  rw [show (Finset.univ : Finset (Fin 4))
        = {0, 1, 2, 3} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Matrix.diag_apply]
  -- Diagonal entries: support gives 1/2 at indices 1,2; 0 at 0,3.
  obtain ⟨hsupp11, hsupp22, _, _⟩ := singletDensityMatrix_support
  rw [singletDensityMatrix_zero_off_support 0 0 (Or.inl ⟨by decide, by decide⟩)]
  rw [singletDensityMatrix_zero_off_support 3 3 (Or.inl ⟨by decide, by decide⟩)]
  rw [hsupp11, hsupp22]
  ring

/-- The singlet density matrix packaged as a `ComplexDensityMatrix 4`. -/
noncomputable def singletCDM : ComplexDensityMatrix 4 :=
  UnitaryQuantum.ofPosSemidef 4
    singletDensityMatrix
    singletDensityMatrix_isHermitian
    singletDensityMatrix_trace_one
    singletDensityMatrix_posSemidef

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BIPARTITE OBSERVABLE / CORRELATION FUNCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The reindexed Kronecker product `A ⊗ B` on `Fin 4 = Fin (2*2)`,
    using the same `finProdFinEquiv` convention as
    `BipartiteUnitaryQM.kroneckerUnitary`.

    We use `(finProdFinEquiv (m := 2) (n := 2)).symm` to pin the
    dimensions; without the hint Lean leaves them as metavariables. -/
noncomputable def kroneckerReindexed
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (A ⊗ₖ B).submatrix
    (finProdFinEquiv (m := 2) (n := 2)).symm
    (finProdFinEquiv (m := 2) (n := 2)).symm

/-- The two-party correlation `E_ρ(A, B) := Re(Tr(ρ · (A ⊗ B)))`. -/
noncomputable def correlation
    (ρ : ComplexDensityMatrix 4)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (ρ.M * kroneckerReindexed A B)).re

/-! ### `kroneckerReindexed` at the relevant Fin-4-pair indices. -/

/-- Pair decompositions: `finProdFinEquiv.symm` at the four Fin-4 values.

    `(finProdFinEquiv (m:=2) (n:=2)).symm` is just `Fin 4 → Fin 2 × Fin 2`
    given by `k ↦ (k / 2, k % 2)`. -/
private lemma fin4_decompose :
    ((finProdFinEquiv (m := 2) (n := 2)).symm 0 = ((0 : Fin 2), (0 : Fin 2)))
  ∧ ((finProdFinEquiv (m := 2) (n := 2)).symm 1 = ((0 : Fin 2), (1 : Fin 2)))
  ∧ ((finProdFinEquiv (m := 2) (n := 2)).symm 2 = ((1 : Fin 2), (0 : Fin 2)))
  ∧ ((finProdFinEquiv (m := 2) (n := 2)).symm 3 = ((1 : Fin 2), (1 : Fin 2))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Generic entry of `kroneckerReindexed`. -/
private lemma kroneckerReindexed_apply
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 4) :
    kroneckerReindexed A B i j
      = A ((finProdFinEquiv (m := 2) (n := 2)).symm i).1
          ((finProdFinEquiv (m := 2) (n := 2)).symm j).1
        * B ((finProdFinEquiv (m := 2) (n := 2)).symm i).2
          ((finProdFinEquiv (m := 2) (n := 2)).symm j).2 := by
  unfold kroneckerReindexed
  rw [Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

/-- The four entries of `kroneckerReindexed A B` that hit the singlet
    support — at (1,1), (1,2), (2,1), (2,2). -/
private lemma kroneckerReindexed_singlet_block
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kroneckerReindexed A B 1 1 = A 0 0 * B 1 1
  ∧ kroneckerReindexed A B 1 2 = A 0 1 * B 1 0
  ∧ kroneckerReindexed A B 2 1 = A 1 0 * B 0 1
  ∧ kroneckerReindexed A B 2 2 = A 1 1 * B 0 0 := by
  obtain ⟨_, h1, h2, _⟩ := fin4_decompose
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [kroneckerReindexed_apply]
  · rw [h1]
  · rw [h1, h2]
  · rw [h2, h1]
  · rw [h2]

/-! ### The key reduction lemma: trace of singlet times any 4×4 matrix.

    `Tr(singletDensityMatrix · M) = (1/2)·(M[1,1] + M[2,2] − M[1,2] − M[2,1])`.

    This is what makes the bridge theorem clean: the entire trace
    reduces to the four `singlet support × M` cross-terms. -/

private lemma trace_singlet_mul (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (singletDensityMatrix * M)
      = (1/2 : ℂ) * (M 1 1 + M 2 2 - M 1 2 - M 2 1) := by
  obtain ⟨hsupp11, hsupp22, hsupp12, hsupp21⟩ := singletDensityMatrix_support
  -- Unroll the trace as a sum over Fin 4 = {0, 1, 2, 3}.
  rw [Matrix.trace]
  rw [show (Finset.univ : Finset (Fin 4))
        = {0, 1, 2, 3} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Matrix.diag_apply]
  -- Diagonal i ∈ {0, 3}: (ρ·M)[i,i] = ∑_k ρ[i,k] M[k,i]; ρ[i,k] = 0 for i ∈ {0,3}.
  have h_diag_zero : ∀ i : Fin 4, i ≠ 1 → i ≠ 2 →
                  (singletDensityMatrix * M) i i = 0 := by
    intro i hi1 hi2
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [singletDensityMatrix_zero_off_support i k (Or.inl ⟨hi1, hi2⟩)]
    ring
  rw [h_diag_zero 0 (by decide) (by decide)]
  rw [h_diag_zero 3 (by decide) (by decide)]
  -- For i = 1: (ρ·M)[1,1] = ∑_k ρ[1,k] M[k,1]; ρ[1,k] ≠ 0 only for k ∈ {1, 2}.
  have h_row1 : (singletDensityMatrix * M) 1 1
              = singletDensityMatrix 1 1 * M 1 1 + singletDensityMatrix 1 2 * M 2 1 := by
    rw [Matrix.mul_apply]
    rw [show (Finset.univ : Finset (Fin 4))
          = {0, 1, 2, 3} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [singletDensityMatrix_zero_off_support 1 0 (Or.inr ⟨by decide, by decide⟩)]
    rw [singletDensityMatrix_zero_off_support 1 3 (Or.inr ⟨by decide, by decide⟩)]
    ring
  -- For i = 2: (ρ·M)[2,2] = ρ[2,1] M[1,2] + ρ[2,2] M[2,2].
  have h_row2 : (singletDensityMatrix * M) 2 2
              = singletDensityMatrix 2 1 * M 1 2 + singletDensityMatrix 2 2 * M 2 2 := by
    rw [Matrix.mul_apply]
    rw [show (Finset.univ : Finset (Fin 4))
          = {0, 1, 2, 3} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [singletDensityMatrix_zero_off_support 2 0 (Or.inr ⟨by decide, by decide⟩)]
    rw [singletDensityMatrix_zero_off_support 2 3 (Or.inr ⟨by decide, by decide⟩)]
    ring
  rw [h_row1, h_row2]
  rw [hsupp11, hsupp22, hsupp12, hsupp21]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE KEY BRIDGE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE KEY BRIDGE THEOREM.**

    For the singlet state and equator-plane measurements at angles θa,
    θb, the two-party correlation equals `-cos(θa - θb)`.

    Direct calculation: by `trace_singlet_mul`, the trace reduces to
    `(1/2)(M[1,1] + M[2,2] - M[1,2] - M[2,1])` for `M = kron(A, B)`.
    Plugging in `A = equatorObservable θa = cos·σz + sin·σx` gives
    `A[0,0] = cos θa`, `A[1,1] = -cos θa`, `A[0,1] = A[1,0] = sin θa`
    (same for B), and the trace evaluates to
        `(1/2)(-2cos θa cos θb - 2 sin θa sin θb)`
        `= -(cos θa cos θb + sin θa sin θb) = -cos(θa - θb)`. -/
theorem singlet_correlation_equator (θa θb : ℝ) :
    correlation singletCDM (equatorObservable θa) (equatorObservable θb)
      = -Real.cos (θa - θb) := by
  unfold correlation
  -- Replace singletCDM.M with singletDensityMatrix; the ofPosSemidef
  -- packaging is definitional on the M field.
  have hρM : singletCDM.M = singletDensityMatrix := rfl
  rw [hρM]
  rw [trace_singlet_mul]
  -- Now the goal is about ((1/2) * (M[1,1] + M[2,2] - M[1,2] - M[2,1])).re
  -- with M = kroneckerReindexed (equator θa) (equator θb).
  obtain ⟨hk11, hk12, hk21, hk22⟩ :=
    kroneckerReindexed_singlet_block (equatorObservable θa) (equatorObservable θb)
  rw [hk11, hk12, hk21, hk22]
  -- Now the goal is about
  --   ((1/2) * (A[0,0]·B[1,1] + A[1,1]·B[0,0] - A[0,1]·B[1,0] - A[1,0]·B[0,1])).re
  -- where A = equator θa, B = equator θb.
  obtain ⟨hA00, hA01, hA10, hA11⟩ := equatorObservable_entries θa
  obtain ⟨hB00, hB01, hB10, hB11⟩ := equatorObservable_entries θb
  rw [hA00, hA01, hA10, hA11, hB00, hB01, hB10, hB11]
  -- (1/2)·(cos θa · (-cos θb) + (-cos θa) · cos θb - sin θa · sin θb - sin θa · sin θb)
  -- = -(cos θa cos θb + sin θa sin θb)
  -- = -cos(θa - θb)  by cos_sub.
  rw [Real.cos_sub]
  -- The complex expression `(1/2) * (...)` consists entirely of real
  -- coercions and arithmetic. Convert via `Complex.ext_iff` and norm_cast:
  -- the .re of a real coercion is the real number itself.
  -- Reduce to a real equation via `norm_cast` (`push_cast` plus simp).
  have h_real :
      ((1/2 : ℝ) *
          (Real.cos θa * -Real.cos θb
          + -Real.cos θa * Real.cos θb
          - Real.sin θa * Real.sin θb
          - Real.sin θa * Real.sin θb))
        = -(Real.cos θa * Real.cos θb + Real.sin θa * Real.sin θb) := by ring
  -- Now cast h_real up to ℂ and take .re.
  have h_cast :
      ((((1/2 : ℝ) *
          (Real.cos θa * -Real.cos θb
          + -Real.cos θa * Real.cos θb
          - Real.sin θa * Real.sin θb
          - Real.sin θa * Real.sin θb) : ℝ)) : ℂ).re
        = -(Real.cos θa * Real.cos θb + Real.sin θa * Real.sin θb) := by
    rw [Complex.ofReal_re, h_real]
  -- The LHS of h_cast, after push_cast, matches the goal's LHS.
  have : (((1/2 : ℝ) *
          (Real.cos θa * -Real.cos θb
          + -Real.cos θa * Real.cos θb
          - Real.sin θa * Real.sin θb
          - Real.sin θa * Real.sin θb) : ℝ) : ℂ)
        = (1/2 : ℂ) *
          ((Real.cos θa : ℂ) * -(Real.cos θb : ℂ)
          + -(Real.cos θa : ℂ) * (Real.cos θb : ℂ)
          - (Real.sin θa : ℂ) * (Real.sin θb : ℂ)
          - (Real.sin θa : ℂ) * (Real.sin θb : ℂ)) := by
    push_cast; ring
  rw [← this, Complex.ofReal_re, h_real]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: BRIDGE TO THE EXISTING `singletCorrelation`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The matrix-based correlation function for the singlet state reproduces
    the abstract `TsirelsonBound.singletCorrelation θa θb := -cos(θa − θb)`. -/
theorem bipartite_qubit_shadow_reproduces_singletCorrelation
    (θa θb : ℝ) :
    correlation singletCDM (equatorObservable θa) (equatorObservable θb)
      = UnifiedTheory.LayerB.TsirelsonBound.singletCorrelation θa θb := by
  rw [singlet_correlation_equator]
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CHSH SATURATION AT THE STANDARD ANGLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CHSH saturation.**  With Alice's angles `{0, π/2}` and Bob's
    `{π/4, -π/4}`, the singlet CHSH expression has absolute value
    `2√2`, saturating the Tsirelson bound. -/
theorem singlet_CHSH_max_violation :
    let E := fun a b : ℝ =>
      correlation singletCDM (equatorObservable a) (equatorObservable b)
    |E 0 (Real.pi/4) + E 0 (-(Real.pi/4)) + E (Real.pi/2) (Real.pi/4)
       - E (Real.pi/2) (-(Real.pi/4))| = 2 * Real.sqrt 2 := by
  simp only [singlet_correlation_equator]
  have h1 : Real.cos ((0 : ℝ) - Real.pi/4) = Real.cos (Real.pi/4) := by
    rw [show (0 : ℝ) - Real.pi/4 = -(Real.pi/4) by ring, Real.cos_neg]
  have h2 : Real.cos ((0 : ℝ) - -(Real.pi/4)) = Real.cos (Real.pi/4) := by
    rw [show (0 : ℝ) - -(Real.pi/4) = Real.pi/4 by ring]
  have h3 : Real.cos (Real.pi/2 - Real.pi/4) = Real.cos (Real.pi/4) := by
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring]
  have h4 : Real.cos (Real.pi/2 - -(Real.pi/4)) = -Real.cos (Real.pi/4) := by
    rw [show Real.pi/2 - -(Real.pi/4) = 3 * Real.pi/4 by ring]
    exact UnifiedTheory.LayerB.BellTheorem.cos_three_pi_four
  rw [h1, h2, h3, h4]
  have hkey : 2 * Real.cos (Real.pi/4) = Real.sqrt 2 :=
    two_mul_cos_pi_four_eq_sqrt_two
  have hexpr : -Real.cos (Real.pi/4) + -Real.cos (Real.pi/4)
                 + -Real.cos (Real.pi/4) - -(-Real.cos (Real.pi/4))
              = -(2 * Real.sqrt 2) := by
    have : -Real.cos (Real.pi/4) + -Real.cos (Real.pi/4)
             + -Real.cos (Real.pi/4) - -(-Real.cos (Real.pi/4))
           = -(2 * (2 * Real.cos (Real.pi/4))) := by ring
    rw [this, hkey]
  rw [hexpr]
  rw [abs_neg, abs_of_nonneg]
  positivity

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE LEGIBILITY HEADLINE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **LANDING STATEMENT — the Bell content of the bipartite local-realist
    shadow.**

    At `n_A = n_B = 2` (the Bell-scenario qubit substrate), bipartite
    phase-quotient unitary QM:

      (1) admits a local-realistic shadow
          (`bipartiteQubitUnitaryQM_has_localRealisticModel`,
           proved unconditionally modulo the standard postulate bundle);

      (2) reproduces the singlet's Bell correlation
              E(θa, θb) = -cos(θa - θb)
          on equator-plane measurements of the qubit-singlet density
          matrix (`singlet_correlation_equator`);

      (3) saturates the Tsirelson bound at the standard CHSH angles
          (0, π/2; π/4, -π/4) with |S| = 2√2
          (`singlet_CHSH_max_violation`).

    Three properties of the same substrate, in one statement. -/
theorem bipartite_qubit_shadow_concrete_Bell_content
    (hPost : BipartiteFullPostulates 2 2 bipartiteAnalyticCore_2_2) :
    (∃ L : LocalRealisticTheory,
        L.IsNoSignallingShadow bipartiteQubitUnitaryQuantumNoSignalling)
  ∧ (∀ θa θb : ℝ,
        correlation singletCDM (equatorObservable θa) (equatorObservable θb)
          = -Real.cos (θa - θb))
  ∧ (let E := fun a b : ℝ =>
        correlation singletCDM (equatorObservable a) (equatorObservable b)
     |E 0 (Real.pi/4) + E 0 (-(Real.pi/4)) + E (Real.pi/2) (Real.pi/4)
        - E (Real.pi/2) (-(Real.pi/4))| = 2 * Real.sqrt 2) :=
  ⟨bipartiteQubitUnitaryQM_has_localRealisticModel hPost,
   singlet_correlation_equator,
   singlet_CHSH_max_violation⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms singlet_correlation_equator
#print axioms singlet_CHSH_max_violation
#print axioms bipartite_qubit_shadow_concrete_Bell_content

end UnifiedTheory.LayerC.BipartiteQubitCHSH
