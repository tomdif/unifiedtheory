/-
  UnifiedTheory/LayerC/PhaseFaithfulnessAllN.lean
  ───────────────────────────────────────────────

  **Unconditional discharge of `PhaseFaithfulnessAnalyticCore n`
  for every dimension `n`.**

  This file proves, for every `n : ℕ` with `[NeZero n]`:

      theorem phaseFaithfulnessAnalyticCore_general :
          PhaseFaithfulnessAnalyticCore n

  Together with `PhaseQuotientUnitaryQM.lean`, this makes the
  headline theorem `phaseQuotientUnitaryQM_has_localRealisticModel n`
  **unconditional at every dimension**.

  ## Proof outline

  Set `W := star V.val * U.val`.  Since `V, U` are unitary, `W` is
  unitary.  The hypothesis `U ρ U* = V ρ V*` for every density
  matrix `ρ` is equivalent (after multiplying by `star V` on the
  left and by `V` on the right) to `W ρ W* = ρ`, hence
  `W ρ = ρ W`:  **`W` commutes with every density matrix**.

  * **Step 1 (`W` diagonal).**  Take `ρ_k := |k⟩⟨k|` — the rank-1
    diagonal projector onto basis vector `k`.  This is a valid
    density matrix.  Commutation `W ρ_k = ρ_k W`, applied at the
    `(k, c)` and `(c, k)` matrix entries for `c ≠ k`, forces
    `W_{c, k} = 0` and `W_{k, c} = 0`.  Quantifying over `k` shows
    `W` is diagonal.

  * **Step 2 (`W` constant on the diagonal).**  Take the
    superposition `|ψ_{i,j}⟩ = (|i⟩ + |j⟩)/√2` and its rank-1
    density `ρ_{i,j} := |ψ⟩⟨ψ| = (1/2)·(|i⟩+|j⟩)·(⟨i|+⟨j|)`.  With
    `W` diagonal, commutation `(W ρ_{i,j})_{i,j} = (ρ_{i,j} W)_{i,j}`
    forces `W_{i,i} = W_{j,j}`.

  * **Step 3 (conclude).**  Hence `W = λ · I` for some
    `λ : ℂ`.  Since `W` is unitary, `|λ| = 1`, i.e., `λ ∈ Circle`.
    Then `star V * U = λ I`, so `U = λ V`, equivalently
    `V = λ⁻¹ U`, with `λ⁻¹ ∈ Circle`.  This is exactly
    `phaseEquiv U V`.

  ## Standing constraint

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerC.PhaseQuotientUnitaryQM
import Mathlib.Data.Matrix.Basis

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LocalRealisticAxioms

open Matrix
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.UnitaryInvariance
open UnitaryQuantum

/-! ## 1.  Basic density matrices used in the proof. -/

section BasicDensities

variable (n : ℕ) [NeZero n]

/-- The rank-1 diagonal projector `|k⟩⟨k|` as a `ComplexDensityMatrix`. -/
noncomputable def diagDensity (k : Fin n) : ComplexDensityMatrix n :=
  ofPosSemidef n (Matrix.single k k (1 : ℂ))
    (by
      -- Hermitian: single i i c is fixed by conjugate-transpose when c is real.
      -- single k k 1 = diagonal (Pi.single k 1).
      rw [← Matrix.diagonal_single]
      refine Matrix.isHermitian_diagonal_iff.mpr ?_
      intro i
      by_cases h : i = k
      · subst h; simp
      · have h' : k ≠ i := fun he => h he.symm
        simp [Pi.single_apply, h'])
    (by
      -- Trace = 1.
      exact Matrix.trace_single_eq_same k (1 : ℂ))
    (by
      -- PSD via diagonal of a non-negative function.
      rw [← Matrix.diagonal_single]
      apply Matrix.PosSemidef.diagonal
      intro i
      by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_apply, h])

/-- The unit-superposition vector `ψ = |i⟩ + |j⟩` as a function. -/
noncomputable def superVec (i j : Fin n) : Fin n → ℂ :=
  Pi.single i (1 : ℂ) + Pi.single j (1 : ℂ)

/-- The unnormalised superposition density: `|ψ⟩⟨ψ|` with
    `ψ = |i⟩+|j⟩`.  Defined as `vecMulVec ψ (star ψ)`. -/
noncomputable def superRank1 (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec (superVec n i j) (star (superVec n i j))

/-- For `i ≠ j`, the superRank1 matrix at `(i, j)` is `1`. -/
private lemma superRank1_apply_ij {i j : Fin n} (hij : i ≠ j) :
    superRank1 n i j i j = 1 := by
  unfold superRank1 superVec
  rw [Matrix.vecMulVec_apply]
  have hji : j ≠ i := Ne.symm hij
  simp only [Pi.add_apply, Pi.star_apply, star_add, Pi.single_apply]
  -- (1 + 0) * star (0 + 1) = 1 * 1 = 1.
  by_cases hii : i = i
  · simp [hij, hji]
  · exact absurd rfl hii

/-- `superRank1 n i j` is Hermitian: `star (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ)`. -/
private lemma superRank1_isHermitian (i j : Fin n) :
    (superRank1 n i j).IsHermitian := by
  unfold superRank1 Matrix.IsHermitian
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  -- ψ[b] * star ψ[a] becomes star (... b a) = ψ[a] * star (ψ b).
  rw [StarMul.star_mul, star_star, mul_comm]

/-- `superRank1 n i j` is positive semidefinite. -/
private lemma superRank1_posSemidef (i j : Fin n) :
    (superRank1 n i j).PosSemidef := by
  unfold superRank1
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- Trace of `superRank1 n i j` for `i ≠ j` equals `2`. -/
private lemma superRank1_trace {i j : Fin n} (hij : i ≠ j) :
    (superRank1 n i j).trace = 2 := by
  -- trace = sum_a (vecMulVec ψ (star ψ))[a,a] = sum_a ψ[a] * star ψ[a].
  have hji : j ≠ i := Ne.symm hij
  -- Show the trace equals the sum over Fin n of the diagonal entries.
  -- Each diagonal entry simplifies to "(if a = i then 1 else 0) + (if a = j then 1 else 0)".
  rw [Matrix.trace]
  have h_diag_fn : ∀ a : Fin n,
      Matrix.diag (superRank1 n i j) a
        = (if a = i then (1:ℂ) else 0) + (if a = j then (1:ℂ) else 0) := by
    intro a
    unfold superRank1 superVec Matrix.diag
    rw [Matrix.vecMulVec_apply]
    -- ψ a * star (ψ a) where ψ a = Pi.single i 1 + Pi.single j 1
    -- Note: Pi.single_apply gives `if i = a then 1 else 0`, not `if a = i`.
    -- We use the explicit form.
    by_cases hai : a = i
    · subst hai
      have haj : a ≠ j := hij
      have haj_sym : j ≠ a := haj.symm
      simp [Pi.add_apply, Pi.star_apply, Pi.single_apply, haj, haj_sym]
    · by_cases haj : a = j
      · subst haj
        have hai_ne : a ≠ i := hai
        have hai_sym : i ≠ a := hai_ne.symm
        simp [Pi.add_apply, Pi.star_apply, Pi.single_apply, hai_ne, hai_sym]
      · have hai' : i ≠ a := fun h => hai h.symm
        have haj' : j ≠ a := fun h => haj h.symm
        simp [Pi.add_apply, Pi.star_apply, Pi.single_apply,
              hai', haj', hai, haj]
  rw [Finset.sum_congr rfl (fun a _ => h_diag_fn a)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j]
  simp
  ring

/-- The superposition density matrix `(1/2)·(|i⟩+|j⟩)(⟨i|+⟨j|)`
    for **distinct** indices `i ≠ j`. -/
noncomputable def superDensity (i j : Fin n) (hij : i ≠ j) :
    ComplexDensityMatrix n :=
  ofPosSemidef n ((1/2 : ℂ) • superRank1 n i j)
    (by
      -- IsHermitian for a smul: (1/2) is real so star = self.
      have hsuper_herm : (superRank1 n i j).IsHermitian := superRank1_isHermitian n i j
      have h_star_half : star ((1 : ℂ)/2) = (1 : ℂ)/2 := by
        simp [Complex.star_def, Complex.conj_ofReal]
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul]
      show star ((1 : ℂ)/2) • (superRank1 n i j).conjTranspose = (1/2 : ℂ) • superRank1 n i j
      rw [h_star_half, hsuper_herm.eq])
    (by
      -- Trace = (1/2) · trace(superRank1) = (1/2) · 2 = 1.
      rw [Matrix.trace_smul, superRank1_trace n hij]
      show (1/2 : ℂ) • (2 : ℂ) = 1
      rw [smul_eq_mul]
      ring)
    (by
      -- PSD: (1/2) • PSD is PSD when 1/2 ≥ 0.
      refine Matrix.PosSemidef.smul (superRank1_posSemidef n i j) ?_
      -- 0 ≤ (1/2 : ℂ) in ComplexOrder.
      have h_half : ((1:ℂ)/2) = ((1/2:ℝ) : ℂ) := by push_cast; ring
      change (0:ℂ) ≤ (1/2 : ℂ)
      rw [h_half]
      exact RCLike.ofReal_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1/2))

end BasicDensities

/-! ## 2.  `W` commutes with every density matrix. -/

section CommuteW

variable {n : ℕ} [NeZero n]

/-- The commutator matrix `W := star V * U`.  We do **not** package
    this as a `unitaryGroup` element here — only the underlying
    matrix is needed for the commutation arguments.  Unitarity is
    proven separately as `W_unitary` below. -/
private noncomputable def Wmat (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  star V.val * U.val

private lemma Wmat_unitary (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    Wmat U V * star (Wmat U V) = 1 := by
  unfold Wmat
  -- (star V * U) * star (star V * U) = (star V * U) * (star U * V)
  --   = star V * (U * star U) * V = star V * 1 * V = star V * V = 1.
  rw [Matrix.star_mul, star_star]
  -- Now: (star V * U) * (star U * V) = 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc U.val (star U.val) V.val]
  have hUU : U.val * star U.val = 1 :=
    (Matrix.mem_unitaryGroup_iff.mp U.property)
  rw [hUU, Matrix.one_mul]
  exact (Matrix.mem_unitaryGroup_iff'.mp V.property)

private lemma Wmat_star_unitary (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    star (Wmat U V) * Wmat U V = 1 := by
  unfold Wmat
  rw [Matrix.star_mul, star_star]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.val (star V.val) U.val]
  have hVV : V.val * star V.val = 1 :=
    (Matrix.mem_unitaryGroup_iff.mp V.property)
  rw [hVV, Matrix.one_mul]
  exact (Matrix.mem_unitaryGroup_iff'.mp U.property)

/-- The key commutation lemma: if `U ρ U* = V ρ V*` (as matrices)
    for every density matrix `ρ`, then `W ρ = ρ W` where
    `W = star V * U`. -/
private lemma Wmat_commute_of_phen
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (hAct : ∀ ρ : ComplexDensityMatrix n,
      unitaryConjugate U ρ = unitaryConjugate V ρ)
    (ρ : ComplexDensityMatrix n) :
    Wmat U V * ρ.M = ρ.M * Wmat U V := by
  -- Convert `unitaryConjugate U ρ = unitaryConjugate V ρ` to the matrix
  -- equality `U ρ U* = V ρ V*`.
  have h_mat : U.val * ρ.M * star U.val = V.val * ρ.M * star V.val := by
    have h := hAct ρ
    rw [ComplexDensityMatrix.ext_iff_M] at h
    exact h
  -- Multiply both sides on the right by V:
  --   U ρ U* V = V ρ V* V = V ρ · 1 = V ρ.
  have h_right : U.val * ρ.M * star U.val * V.val = V.val * ρ.M := by
    rw [h_mat, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp V.property,
        Matrix.mul_one]
  -- Multiply both sides on the left by star V:
  --   star V * (U ρ U* V) = star V * V ρ = 1 * ρ = ρ.
  have h_both : star V.val * (U.val * ρ.M * star U.val * V.val) = ρ.M := by
    rw [h_right, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp V.property,
        Matrix.one_mul]
  -- Rewrite LHS as W ρ W*: star V * U ρ (star U V) = W ρ (star W).
  have h_WW : Wmat U V * ρ.M * star (Wmat U V) = ρ.M := by
    have h_starW : star (Wmat U V) = star U.val * V.val := by
      unfold Wmat
      rw [Matrix.star_mul, star_star]
    rw [h_starW]
    unfold Wmat
    -- (star V * U) * ρ * (star U * V) = star V * (U ρ U* V) by associativity.
    have : (star V.val * U.val) * ρ.M * (star U.val * V.val)
            = star V.val * (U.val * ρ.M * star U.val * V.val) := by
      simp only [Matrix.mul_assoc]
    rw [this, h_both]
  -- Now: W ρ W* = ρ.  Multiply both sides on the right by W:
  --   W ρ W* W = ρ W ⇒ W ρ · (W* · W) = ρ W ⇒ W ρ · 1 = ρ W ⇒ W ρ = ρ W.
  -- Multiply h_WW on the right by W.
  have h_mul : Wmat U V * ρ.M * star (Wmat U V) * Wmat U V = ρ.M * Wmat U V := by
    rw [h_WW]
  calc Wmat U V * ρ.M
      = Wmat U V * ρ.M * 1 := by rw [Matrix.mul_one]
    _ = Wmat U V * ρ.M * (star (Wmat U V) * Wmat U V) := by
          rw [Wmat_star_unitary]
    _ = Wmat U V * ρ.M * star (Wmat U V) * Wmat U V := by
          rw [← Matrix.mul_assoc]
    _ = ρ.M * Wmat U V := h_mul

end CommuteW

/-! ## 3.  `W` is a scalar matrix.

    From `W ρ = ρ W` for every density matrix `ρ`, we conclude:
    * `W` is diagonal (use the rank-1 projectors `|k⟩⟨k|`);
    * `W`'s diagonal entries are all equal (use the superposition
      density matrices for distinct pairs `i ≠ j`).
    Hence `W = λ · I` for `λ := W_{0,0}`. -/

section WScalar

variable {n : ℕ} [NeZero n]

/-- **`W` is diagonal.**  Off-diagonal entries `W_{a,b}` for `a ≠ b`
    vanish, because `W` commutes with the rank-1 projector
    `|b⟩⟨b|`. -/
private lemma Wmat_offdiag_zero
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (hAct : ∀ ρ : ComplexDensityMatrix n,
      unitaryConjugate U ρ = unitaryConjugate V ρ)
    (a b : Fin n) (hab : a ≠ b) :
    Wmat U V a b = 0 := by
  -- ρ_b = |b⟩⟨b| = single b b 1 as a density matrix.
  have h_comm : Wmat U V * (Matrix.single b b (1:ℂ))
                  = (Matrix.single b b (1:ℂ)) * Wmat U V := by
    have h := Wmat_commute_of_phen U V hAct (diagDensity n b)
    -- Reduce diagDensity.M = single b b 1.
    have h_M : (diagDensity n b).M = Matrix.single b b (1:ℂ) := rfl
    rw [h_M] at h
    exact h
  -- Read off the (a, b) entry: LHS = W a b; RHS = 0 (since a ≠ b).
  have hLHS : (Wmat U V * Matrix.single b b (1:ℂ)) a b = Wmat U V a b := by
    simp [Matrix.mul_single_apply_same]
  have hRHS : (Matrix.single b b (1:ℂ) * Wmat U V) a b = 0 := by
    have hab' : a ≠ b := hab
    simp [Matrix.single_mul_apply_of_ne, hab']
  have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) h_comm
  simp only at this
  rw [hLHS, hRHS] at this
  exact this

/-- **`W`'s diagonal entries are all equal.**  Use the superposition
    density `(1/2)|ψ⟩⟨ψ|` with `ψ = |i⟩+|j⟩` (for `i ≠ j`); having
    already established `W` is diagonal, the `(i, j)` entry of the
    commutation equation forces `W_{i,i} = W_{j,j}`. -/
private lemma Wmat_diag_eq
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (hAct : ∀ ρ : ComplexDensityMatrix n,
      unitaryConjugate U ρ = unitaryConjugate V ρ)
    (i j : Fin n) :
    Wmat U V i i = Wmat U V j j := by
  by_cases hij : i = j
  · subst hij; rfl
  -- Use the superposition density for i ≠ j.
  -- We have W ρ = ρ W where ρ = (1/2) (single i i + single i j + single j i + single j j).
  have h_comm := Wmat_commute_of_phen U V hAct (superDensity n i j hij)
  -- (superDensity n i j hij).M = (1/2) • superRank1 n i j.
  have h_M : (superDensity n i j hij).M = (1/2 : ℂ) • superRank1 n i j := rfl
  rw [h_M] at h_comm
  -- Extract the (i, j) entry.  Using diagonality of W and the (i,j) entry
  -- of superRank1 = 1 (since j ≠ i so single j i 1 (i,j) = 0 and similarly
  -- for single j j; but single i j 1 (i,j) = 1; single i i 1 (i,j) = 0).
  -- W diagonal: (W ρ)_{i,j} = sum_l W_{i,l} ρ_{l,j} = W_{i,i} ρ_{i,j} = W_{i,i} * (1/2).
  -- (ρ W)_{i,j} = sum_l ρ_{i,l} W_{l,j} = ρ_{i,j} W_{j,j} = (1/2) * W_{j,j}.
  -- So W_{i,i} = W_{j,j}.
  have hSR_ij : superRank1 n i j i j = 1 := superRank1_apply_ij n hij
  -- (W * ρ.M) i j = sum_l W i l * ρ.M l j.  With W off-diagonal zero, only l = i contributes:
  -- = W i i * ρ.M i j = W i i * (1/2) * superRank1[i,j] = W i i * (1/2) * 1 = W i i / 2.
  have hLHS_ij : (Wmat U V * ((1/2 : ℂ) • superRank1 n i j)) i j
                 = (1/2 : ℂ) * Wmat U V i i := by
    rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    rw [Matrix.mul_apply]
    -- sum over l: W i l * superRank1 l j.
    have h_diag_W : ∀ l : Fin n, l ≠ i → Wmat U V i l = 0 := by
      intro l hl
      exact Wmat_offdiag_zero U V hAct i l (fun h => hl h.symm)
    -- Replace sum with the single nonzero term.
    rw [Finset.sum_eq_single i]
    · rw [hSR_ij]
      ring
    · intro l _ hl
      rw [h_diag_W l hl]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  -- (ρ.M * W) i j = sum_l ρ.M i l * W l j.  Only l = j contributes
  -- (W off-diagonal zero ⇒ W l j = 0 for l ≠ j).
  -- = (1/2) * superRank1[i,j] * W j j = (1/2) * 1 * W j j = W j j / 2.
  have hRHS_ij : (((1/2 : ℂ) • superRank1 n i j) * Wmat U V) i j
                 = (1/2 : ℂ) * Wmat U V j j := by
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rw [Matrix.mul_apply]
    have h_diag_W' : ∀ l : Fin n, l ≠ j → Wmat U V l j = 0 := by
      intro l hl
      exact Wmat_offdiag_zero U V hAct l j hl
    rw [Finset.sum_eq_single j]
    · rw [hSR_ij]
      ring
    · intro l _ hl
      rw [h_diag_W' l hl]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Combine.
  have h_eq : (1/2 : ℂ) * Wmat U V i i = (1/2 : ℂ) * Wmat U V j j := by
    have h_apply := congrArg
      (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h_comm
    simp only at h_apply
    rw [hLHS_ij, hRHS_ij] at h_apply
    exact h_apply
  -- Cancel the 1/2.
  have h_half_ne : (1/2 : ℂ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h_half_ne h_eq

/-- **Putting it together: `W` is the scalar matrix `λ · I`.** -/
private lemma Wmat_eq_scalar
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (hAct : ∀ ρ : ComplexDensityMatrix n,
      unitaryConjugate U ρ = unitaryConjugate V ρ) :
    let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    Wmat U V = (Wmat U V i₀ i₀) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro i₀
  ext a b
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    -- W a a = W i₀ i₀ by Wmat_diag_eq.
    rw [Wmat_diag_eq U V hAct a i₀]
    simp
  · -- W a b = 0 by Wmat_offdiag_zero.
    rw [Wmat_offdiag_zero U V hAct a b hab]
    simp [hab]

end WScalar

/-! ## 4.  The scalar `λ` has unit norm. -/

section LambdaUnit

variable {n : ℕ} [NeZero n]

/-- **`|λ|² = 1` where `λ := W_{0,0}`.**  From `star W · W = 1` and
    `W = λ I` we get `(star λ · λ) I = 1`, so reading off the
    `(0, 0)` entry: `star λ · λ = 1`. -/
private lemma lambda_norm_sq_eq_one
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (hAct : ∀ ρ : ComplexDensityMatrix n,
      unitaryConjugate U ρ = unitaryConjugate V ρ) :
    let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    star (Wmat U V i₀ i₀) * Wmat U V i₀ i₀ = 1 := by
  intro i₀
  -- star W · W = 1.
  have hWW : star (Wmat U V) * Wmat U V = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Wmat_star_unitary U V
  -- W = lam I (with lam := W i₀ i₀).
  have hW_eq : Wmat U V = (Wmat U V i₀ i₀) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Wmat_eq_scalar U V hAct
  -- Read off the (i₀, i₀) entry of `star W · W = 1`.
  -- LHS at (i₀, i₀):  (star W · W)[i₀,i₀] = sum_l (star W)[i₀,l] * W[l,i₀]
  --                                       = sum_l star (W[l, i₀]) * W[l, i₀]
  -- Now W = lam • I means W[l, i₀] = lam if l = i₀ else 0.
  -- So only l = i₀ contributes: = star lam * lam.
  -- RHS at (i₀, i₀): 1.
  have h_apply := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℂ => M i₀ i₀) hWW
  simp only [Matrix.one_apply_eq] at h_apply
  -- h_apply : (star W * W) i₀ i₀ = 1.
  -- Compute (star W * W) i₀ i₀ via Matrix.mul_apply.
  rw [Matrix.mul_apply] at h_apply
  -- Now h_apply : ∑ l, (star W) i₀ l * W l i₀ = 1.
  -- Substitute hW_eq pointwise: W l i₀ = lam if l = i₀ else 0.
  have hW_pt : ∀ l : Fin n, Wmat U V l i₀ = if l = i₀ then Wmat U V i₀ i₀ else 0 := by
    intro l
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M l i₀) hW_eq
    simp only at this
    rw [this]
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : l = i₀
    · simp [h]
    · simp [h]
  have hstarW_pt : ∀ l : Fin n, (star (Wmat U V)) i₀ l = star (Wmat U V l i₀) := by
    intro l; rfl
  -- Reduce the sum: only l = i₀ contributes.
  have h_sum_eq : (∑ l : Fin n, (star (Wmat U V)) i₀ l * Wmat U V l i₀)
                  = star (Wmat U V i₀ i₀) * Wmat U V i₀ i₀ := by
    apply Finset.sum_eq_single i₀
    · intro l _ hl
      rw [hstarW_pt l, hW_pt l]
      simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_sum_eq] at h_apply
  exact h_apply

end LambdaUnit

/-! ## 5.  The main theorem: phase-faithfulness for all `n`. -/

/-- **`PhaseFaithfulnessAnalyticCore n`** is provable for every `n`
    with `[NeZero n]`.  This makes the headline theorem
    `phaseQuotientUnitaryQM_has_localRealisticModel` unconditional
    at every dimension. -/
theorem phaseFaithfulnessAnalyticCore_general (n : ℕ) [NeZero n] :
    PhaseFaithfulnessAnalyticCore n := by
  intro U V hAct
  -- The pivotal scalar lam := W_{0,0} where W = star V * U.
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  set lam : ℂ := Wmat U V i₀ i₀ with hlam_def
  -- Step 1: |lam| = 1.
  have hlam_sq : star lam * lam = 1 := lambda_norm_sq_eq_one U V hAct
  have hlam_norm : ‖lam‖ = 1 := by
    have h_normSq : Complex.normSq lam = 1 := by
      have hns : (Complex.normSq lam : ℂ) = star lam * lam := by
        rw [Complex.normSq_eq_conj_mul_self]
        rfl
      have : (Complex.normSq lam : ℂ) = 1 := by rw [hns]; exact hlam_sq
      exact_mod_cast this
    have h_sq : ‖lam‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]; exact h_normSq
    have h_nn : 0 ≤ ‖lam‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖lam‖ - 1), sq_nonneg (‖lam‖ + 1)]
  -- Step 2: V = lam⁻¹ • U.  (Since W = star V * U = lam I, multiply by V on the left.)
  have hW_eq : Wmat U V = lam • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Wmat_eq_scalar U V hAct
  -- W = star V * U = lam I  ⟹  V * W = V * lam I = lam V  ⟹  U = lam V  (since V * star V * U = U).
  have hVW_eq_U : V.val * Wmat U V = U.val := by
    unfold Wmat
    rw [← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.mp V.property,
        Matrix.one_mul]
  have hU_eq : U.val = lam • V.val := by
    rw [← hVW_eq_U, hW_eq]
    rw [Matrix.mul_smul, Matrix.mul_one]
  -- Step 3: V = lam⁻¹ • U.  Witness phase z := lam⁻¹ ∈ Circle.
  -- (For complex lam with |lam|=1, lam⁻¹ = star lam.)
  have hlam_ne : lam ≠ 0 := by
    intro h
    rw [h] at hlam_sq
    simp at hlam_sq
  refine ⟨⟨lam⁻¹, ?_⟩, ?_⟩
  · -- ‖lam⁻¹‖ = 1.
    change lam⁻¹ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [norm_inv, hlam_norm, inv_one]
  · -- V.val = (lam⁻¹) • U.val.
    -- From U.val = lam • V.val, multiply both sides by lam⁻¹:
    --   lam⁻¹ • U.val = lam⁻¹ • (lam • V.val) = (lam⁻¹ * lam) • V.val = V.val.
    show V.val = ((⟨lam⁻¹, _⟩ : Circle) : ℂ) • U.val
    simp only
    rw [hU_eq]
    rw [← smul_assoc]
    show V.val = (lam⁻¹ • lam) • V.val
    rw [smul_eq_mul, inv_mul_cancel₀ hlam_ne, one_smul]

/-! ## 6.  Headline upgrades.

    With `phaseFaithfulnessAnalyticCore_general` discharged, the
    headline theorem becomes unconditional at every dimension. -/

/-- **THE UNCONDITIONAL HEADLINE AT EVERY DIMENSION.**

    Phase-quotient unitary quantum mechanics on a Hilbert space of
    arbitrary dimension `n ≥ 1` admits a local-realistic model — with
    no hypotheses whatsoever. -/
theorem phaseQuotientUnitaryQM_has_localRealisticModel
    (n : ℕ) [NeZero n] :
    ∃ L : LocalRealisticTheory, L.IsNoSignallingShadow
      (phaseQuotientUnitaryQuantumNoSignalling n) :=
  phaseQuotientUnitaryQM_has_localRealisticModel_of_core n
    (phaseFaithfulnessAnalyticCore_general n)

/-- **`PhenomenalFaithfulness` for `phaseQuotientUnitaryQuantumNoSignalling`,
    unconditionally.** -/
theorem phaseQuotient_phenomenalFaithfulness_general (n : ℕ) [NeZero n] :
    (phaseQuotientUnitaryQuantumNoSignalling n).PhenomenalFaithfulness :=
  phaseQuotient_phenomenalFaithfulness_of_core n
    (phaseFaithfulnessAnalyticCore_general n)

end UnifiedTheory.LayerC.LocalRealisticAxioms
