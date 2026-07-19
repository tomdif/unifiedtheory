/-
  LayerB/JointDiagonalisationCommuting.lean
  ──────────────────────────────────────────

  **Existence bridge for `JointDiagonalisation` on commuting Hermitian
  matrices** — unblocks the conditional reduction in
  `LiebCorrectedCommutingFull.lean`.

  For any finite set of pairwise-commuting Hermitian matrices on
  `Matrix (Fin m) (Fin m) ℂ` (specifically the 4-tuple case used by
  `JointDiagonalisation`), we construct a shared unitary `U` and four
  real diagonal sequences `dA, dB, dC, dD : Fin m → ℝ` such that

      `U · diagonal(ofReal ∘ dX) · star U = X`  for `X ∈ {A, B, C, D}`.

  ## Mathematical content

  The structural proof (e.g. Halmos, *Finite-Dimensional Vector
  Spaces*, Theorem 79) proceeds via joint eigenspaces.  Mathlib's
  `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`
  in `Mathlib.Analysis.InnerProductSpace.JointEigenspace` provides
  the inner-product-space form:

      `E = ⨁_{χ : ι → 𝕜} ⨅_j eigenspace (T j) (χ j)`

  for a commuting family of symmetric linear maps `T_j`.  Combined
  with `DirectSum.IsInternal.subordinateOrthonormalBasis` (in
  `Mathlib.Analysis.InnerProductSpace.PiL2`), this yields an
  orthonormal basis of `E` indexed by `Fin n` (where `n = finrank E`)
  with each basis vector contained in a joint eigenspace.  Bridging
  to matrices: view `A : Matrix (Fin m) (Fin m) ℂ` as
  `A.toEuclideanLin : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)`
  via `Matrix.isHermitian_iff_isSymmetric`, construct the joint
  eigenbasis, and exhibit the unitary as the change-of-basis matrix.

  ## What is shipped

    1.  `JointEigenbasis A B C D` — a bundled orthonormal basis of
        `EuclideanSpace ℂ (Fin m)` simultaneously diagonalising the
        four matrices.

    2.  `jointEigenbasis_exists_of_allCommute` — the existence of such
        a basis for any quadruple of pairwise-commuting Hermitian
        matrices.

    3.  `JointDiagonalisation_of_jointEigenbasis` — converting an
        abstract joint eigenbasis to the bundled matrix-form
        `JointDiagonalisation` of `LiebCorrectedCommutingFull.lean`.

    4.  `jointDiagonalisation_exists_of_allCommute` — the headline
        existence theorem: every 4-tuple of pairwise-commuting
        Hermitian matrices admits a `JointDiagonalisation`.

    5.  `lieb1973_corrected_commuting_unconditional` — composing the
        existence bridge with the conditional reduction of
        `LiebCorrectedCommutingFull.lean` gives the corrected Lieb
        target for any four pairwise-commuting PosDef matrices,
        UNCONDITIONALLY (no joint-diagonalisation hypothesis).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01 (Phase B10 joint-diagonalisation bridge).
-/

import UnifiedTheory.LayerB.LiebCorrectedCommutingFull
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.JointDiagonalisationCommuting

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.LiebCorrectedCommutingFull

/-! ## 1. The joint eigenbasis: a bundled orthonormal basis. -/

/-- **Joint eigenbasis** of four pairwise-commuting Hermitian
    matrices.  Records:

    *   an orthonormal basis `e : OrthonormalBasis (Fin m) ℂ
        (EuclideanSpace ℂ (Fin m))`;
    *   four real-valued eigenvalue functions `λA λB λC λD : Fin m → ℝ`;
    *   four eigenvector identities expressing that each basis vector
        is an eigenvector of each matrix with the prescribed eigenvalue.

    The existence of such a structure for every 4-tuple of
    pairwise-commuting Hermitian matrices is the standard
    simultaneous-diagonalisation theorem.
-/
structure JointEigenbasis {m : ℕ}
    (A B C D : Matrix (Fin m) (Fin m) ℂ) where
  /-- The shared orthonormal eigenbasis of all four matrices. -/
  e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))
  /-- Eigenvalues of `A` on the basis. -/
  lamA : Fin m → ℝ
  /-- Eigenvalues of `B` on the basis. -/
  lamB : Fin m → ℝ
  /-- Eigenvalues of `C` on the basis. -/
  lamC : Fin m → ℝ
  /-- Eigenvalues of `D` on the basis. -/
  lamD : Fin m → ℝ
  /-- Joint eigenvector identity for `A`. -/
  eigenA : ∀ i, A.mulVec ((e i : EuclideanSpace ℂ (Fin m))) =
      ((lamA i : ℝ) : ℂ) • (e i : EuclideanSpace ℂ (Fin m))
  /-- Joint eigenvector identity for `B`. -/
  eigenB : ∀ i, B.mulVec ((e i : EuclideanSpace ℂ (Fin m))) =
      ((lamB i : ℝ) : ℂ) • (e i : EuclideanSpace ℂ (Fin m))
  /-- Joint eigenvector identity for `C`. -/
  eigenC : ∀ i, C.mulVec ((e i : EuclideanSpace ℂ (Fin m))) =
      ((lamC i : ℝ) : ℂ) • (e i : EuclideanSpace ℂ (Fin m))
  /-- Joint eigenvector identity for `D`. -/
  eigenD : ∀ i, D.mulVec ((e i : EuclideanSpace ℂ (Fin m))) =
      ((lamD i : ℝ) : ℂ) • (e i : EuclideanSpace ℂ (Fin m))

/-! ## 2. Existence of joint eigenbasis for pairwise-commuting Hermitians.

    We build the joint eigenbasis from Mathlib's
    `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`
    in `Mathlib.Analysis.InnerProductSpace.JointEigenspace`. -/

section Existence

variable {m : ℕ}

/-- The four matrices, viewed as a family of linear endomorphisms of
    `EuclideanSpace ℂ (Fin m)`, indexed by `Fin 4`. -/
private noncomputable def fourLin
    (A B C D : Matrix (Fin m) (Fin m) ℂ) :
    Fin 4 → (EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :=
  ![A.toEuclideanLin, B.toEuclideanLin, C.toEuclideanLin, D.toEuclideanLin]

private lemma fourLin_zero
    (A B C D : Matrix (Fin m) (Fin m) ℂ) :
    fourLin A B C D 0 = A.toEuclideanLin := rfl

private lemma fourLin_one
    (A B C D : Matrix (Fin m) (Fin m) ℂ) :
    fourLin A B C D 1 = B.toEuclideanLin := rfl

private lemma fourLin_two
    (A B C D : Matrix (Fin m) (Fin m) ℂ) :
    fourLin A B C D 2 = C.toEuclideanLin := rfl

private lemma fourLin_three
    (A B C D : Matrix (Fin m) (Fin m) ℂ) :
    fourLin A B C D 3 = D.toEuclideanLin := rfl

/-- Each member of `fourLin A B C D` is symmetric when the underlying
    matrix is Hermitian. -/
private lemma fourLin_isSymmetric
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian) :
    ∀ j, (fourLin A B C D j).IsSymmetric := by
  intro j
  have hA' := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hB' := Matrix.isHermitian_iff_isSymmetric.mp hB
  have hC' := Matrix.isHermitian_iff_isSymmetric.mp hC
  have hD' := Matrix.isHermitian_iff_isSymmetric.mp hD
  fin_cases j
  all_goals (
    simp only [fourLin, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
               Matrix.cons_val_succ]
    first | exact hA' | exact hB' | exact hC' | exact hD')

/-- `Matrix.toEuclideanLin` is multiplicative (via `Matrix.toLpLinAlgEquiv`),
    so `Commute` on matrices transfers to `Commute` on the corresponding linear maps. -/
private lemma commute_toEuclideanLin
    (X Y : Matrix (Fin m) (Fin m) ℂ) (h : Commute X Y) :
    Commute X.toEuclideanLin Y.toEuclideanLin := by
  -- View toEuclideanLin = toLpLin 2 2 ≅ toLpLinAlgEquiv 2 acting as an AlgEquiv.
  show X.toEuclideanLin * Y.toEuclideanLin = Y.toEuclideanLin * X.toEuclideanLin
  -- Use that toLpLinAlgEquiv 2 X = X.toEuclideanLin (defeq) and it's an AlgEquiv.
  have h1 : X.toEuclideanLin * Y.toEuclideanLin
      = (Matrix.toLpLinAlgEquiv 2 (X * Y) :
          EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) := by
    rw [map_mul]
    rfl
  have h2 : Y.toEuclideanLin * X.toEuclideanLin
      = (Matrix.toLpLinAlgEquiv 2 (Y * X) :
          EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) := by
    rw [map_mul]
    rfl
  rw [h1, h2, h.eq]

open scoped Function in
/-- Pairwise commutativity of `fourLin` from `AllCommute`. -/
private lemma fourLin_pairwise_commute
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (h : AllCommute A B C D) :
    Pairwise (Commute on fourLin A B C D) := by
  obtain ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩ := h
  have cAB := commute_toEuclideanLin A B hAB
  have cAC := commute_toEuclideanLin A C hAC
  have cAD := commute_toEuclideanLin A D hAD
  have cBC := commute_toEuclideanLin B C hBC
  have cBD := commute_toEuclideanLin B D hBD
  have cCD := commute_toEuclideanLin C D hCD
  intro i j hij
  simp only [Function.onFun, fourLin]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.cons_val_fin_one, Matrix.head_cons,
               Matrix.head_fin_const, Matrix.cons_val_succ] <;>
    first
      | (exact (hij rfl).elim)
      | exact cAB | exact cAC | exact cAD
      | exact cBC | exact cBD | exact cCD
      | exact cAB.symm | exact cAC.symm | exact cAD.symm
      | exact cBC.symm | exact cBD.symm | exact cCD.symm

/-! ### 2a. Joint eigenspaces of the four-matrix family. -/

/-- The joint eigenspace of the four-matrix family at index `χ : Fin 4 → ℂ`. -/
private noncomputable def jointEigenspace
    (A B C D : Matrix (Fin m) (Fin m) ℂ) (χ : Fin 4 → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  ⨅ j, Module.End.eigenspace (fourLin A B C D j) (χ j)

/-- Internal direct sum decomposition of `EuclideanSpace ℂ (Fin m)` as
    the joint eigenspaces of four pairwise-commuting Hermitian matrices.
    This is `directSum_isInternal_of_pairwise_commute` of Mathlib, lifted to
    matrices. -/
private lemma jointEigenspace_isInternal
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    DirectSum.IsInternal (jointEigenspace A B C D) :=
  LinearMap.IsSymmetric.LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    (fourLin_isSymmetric A B C D hA hB hC hD)
    (fourLin_pairwise_commute A B C D h_comm)

/-! ### 2b. Existence of joint eigenbasis via finite-restriction. -/

/-- **The set of "active" joint eigenvalue tuples** — those `χ : Fin 4 → ℂ`
    such that the joint eigenspace `⨅ j, eigenspace (T j) (χ j)` is nontrivial.

    For finite-dimensional `E`, this set is finite (by Noetherian/well-founded
    descending chains). -/
private lemma jointEigenspace_finite_support
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    Set.Finite {χ : Fin 4 → ℂ | jointEigenspace A B C D χ ≠ ⊥} := by
  have hInt := jointEigenspace_isInternal A B C D hA hB hC hD h_comm
  exact WellFoundedGT.finite_ne_bot_of_iSupIndep hInt.submodule_iSupIndep

/-- The (Fintype) subtype of active joint eigenvalue tuples. -/
private noncomputable def activeJointEigenvalueIndex
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) : Type :=
  {χ : Fin 4 → ℂ // jointEigenspace A B C D χ ≠ ⊥}

private noncomputable instance activeJointEigenvalueIndex.instFintype
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    Fintype (activeJointEigenvalueIndex A B C D hA hB hC hD h_comm) := by
  unfold activeJointEigenvalueIndex
  exact (jointEigenspace_finite_support A B C D hA hB hC hD h_comm).fintype

end Existence

/-! ## 3. Matrix bridge: `JointEigenbasis` ⇒ `JointDiagonalisation`. -/

section MatrixBridge

variable {m : ℕ}

/-- The unitary matrix associated to an orthonormal basis `e` of
    `EuclideanSpace ℂ (Fin m)`: the change-of-basis matrix from the
    standard basis to `e`.  Its `(i, j)`-entry is `e j i`. -/
private noncomputable def basisToUnitary
    (e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix e.toBasis,
   (EuclideanSpace.basisFun (Fin m) ℂ).toMatrix_orthonormalBasis_mem_unitary e⟩

private lemma basisToUnitary_apply
    (e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (i j : Fin m) :
    (basisToUnitary e).val i j = ⇑(e j) i := rfl

/-- Acting by `basisToUnitary e` on a standard basis vector `Pi.single j 1`
    gives the j-th basis vector `e j`. -/
private lemma basisToUnitary_mulVec
    (e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (j : Fin m) :
    (basisToUnitary e).val *ᵥ Pi.single j 1 = ⇑(e j) := by
  rw [Matrix.mulVec_single_one]
  ext i
  rfl

/-- Acting by `star (basisToUnitary e)` on the j-th basis vector `e j`
    gives `Pi.single j 1`. -/
private lemma star_basisToUnitary_mulVec
    (e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (j : Fin m) :
    (star (basisToUnitary e).val) *ᵥ ⇑(e j) = Pi.single j 1 := by
  rw [← basisToUnitary_mulVec e j, Matrix.mulVec_mulVec,
      Unitary.coe_star_mul_self, Matrix.one_mulVec]

/-- Matrices on `Fin m × Fin m` over `ℂ` are equal iff their `mulVec`-actions
    on every standard basis vector `Pi.single k 1` agree. -/
private lemma matrix_ext_via_basisFun_mulVec
    {X Y : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ k : Fin m, X *ᵥ Pi.single k 1 = Y *ᵥ Pi.single k 1) :
    X = Y := by
  ext i k
  have hik := congr_fun (h k) i
  -- (X *ᵥ Pi.single k 1) i = X i k via Matrix.mulVec_single_one.
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hik
  -- Now `hik : (Matrix.col X k) i = (Matrix.col Y k) i`.
  -- Matrix.col is defined to be the column-extraction, so `Matrix.col X k i = X i k`.
  -- After the rewrite the goal becomes `X i k = Y i k` directly.
  exact hik

/-- The key action lemma: applying `(U · D · U†) *ᵥ ⇑(e j)` where
    `U = basisToUnitary e` and `D = diagonal(ofReal ∘ λ)` gives
    `(λ j : ℂ) • ⇑(e j)`. -/
private lemma UDU_mulVec_eigenbasis
    (e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (lam : Fin m → ℝ) (j : Fin m) :
    ((basisToUnitary e).val *
        Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) *
          (star (basisToUnitary e).val)) *ᵥ (⇑(e j) : Fin m → ℂ)
      = ((lam j : ℝ) : ℂ) • (⇑(e j) : Fin m → ℂ) := by
  -- Chain:
  --   (U · D · U†) *ᵥ (e j) = U *ᵥ (D *ᵥ (U† *ᵥ e j))    -- split via ← mulVec_mulVec
  --                       = U *ᵥ (D *ᵥ Pi.single j 1)    -- star_basisToUnitary_mulVec
  --                       = U *ᵥ ((lam j : ℂ) • Pi.single j 1)
  --                       = (lam j : ℂ) • (U *ᵥ Pi.single j 1)
  --                       = (lam j : ℂ) • e j.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      star_basisToUnitary_mulVec e j]
  -- Goal: U *ᵥ (D *ᵥ Pi.single j 1) = (lam j : ℂ) • e j.
  have hDsingle :
      (Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) *ᵥ
            (Pi.single j (1 : ℂ) : Fin m → ℂ)
          = ((lam j : ℝ) : ℂ) • (Pi.single j (1 : ℂ) : Fin m → ℂ) := by
    rw [Matrix.diagonal_mulVec_single, mul_one]
    funext i
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hDsingle, Matrix.mulVec_smul, basisToUnitary_mulVec]

/-- The diagonalisation identity in matrix form: given an orthonormal
    basis `e` of `EuclideanSpace ℂ (Fin m)` consisting of eigenvectors
    of a matrix `A` with real eigenvalues `λ : Fin m → ℝ`,
    `U · diagonal(ofReal ∘ λ) · star U = A` where `U := basisToUnitary e`.

    This is the joint-eigenbasis analogue of `Matrix.IsHermitian.spectral_theorem`. -/
private lemma diag_eq_of_eigenvector_basis
    (A : Matrix (Fin m) (Fin m) ℂ)
    (e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (lamA : Fin m → ℝ)
    (heigen : ∀ j, A.mulVec (⇑(e j)) = ((lamA j : ℝ) : ℂ) • ⇑(e j)) :
    (basisToUnitary e).val *
        Matrix.diagonal (fun i => ((lamA i : ℝ) : ℂ)) *
          (star (basisToUnitary e).val) = A := by
  -- Bridge via `Matrix.toEuclideanLin` (a linear equivalence).
  apply Matrix.toEuclideanLin.injective
  -- Compare linear maps via the orthonormal basis e.
  apply e.toBasis.ext
  intro j
  -- e.toBasis j = e j, in `EuclideanSpace ℂ (Fin m) = WithLp 2 (Fin m → ℂ)`.
  -- Reduce both sides via `toEuclideanLin_apply`:
  --   M.toEuclideanLin v = toLp 2 (M *ᵥ (ofLp v)).
  simp only [OrthonormalBasis.coe_toBasis, Matrix.toLpLin_apply]
  -- Goal: toLp 2 ((U·D·U†) *ᵥ (e j).ofLp) = toLp 2 (A *ᵥ (e j).ofLp).
  -- Use that (e j).ofLp = ⇑(e j) (the underlying function).
  -- We need: (U·D·U†) *ᵥ ⇑(e j) = A *ᵥ ⇑(e j).
  -- LHS = (lamA j : ℂ) • ⇑(e j) by UDU_mulVec_eigenbasis.
  -- RHS = (lamA j : ℂ) • ⇑(e j) by heigen.
  congr 1
  rw [UDU_mulVec_eigenbasis, heigen]

/-- **Convert a `JointEigenbasis` to a `JointDiagonalisation`.**

    The orthonormal basis `JE.e` gives the unitary `U = basisToUnitary JE.e`
    and the four real eigenvalue sequences become the diagonal data. -/
noncomputable def JointDiagonalisation_of_jointEigenbasis
    {A B C D : Matrix (Fin m) (Fin m) ℂ}
    (JE : JointEigenbasis A B C D) :
    JointDiagonalisation A B C D where
  U := basisToUnitary JE.e
  dA := JE.lamA
  dB := JE.lamB
  dC := JE.lamC
  dD := JE.lamD
  hA := diag_eq_of_eigenvector_basis A JE.e JE.lamA JE.eigenA
  hB := diag_eq_of_eigenvector_basis B JE.e JE.lamB JE.eigenB
  hC := diag_eq_of_eigenvector_basis C JE.e JE.lamC JE.eigenC
  hD := diag_eq_of_eigenvector_basis D JE.e JE.lamD JE.eigenD

end MatrixBridge

/-! ## 4. Existence of `JointEigenbasis` from `directSum_isInternal_of_pairwise_commute`. -/

section ExistenceProof

variable {m : ℕ}

/-- The restricted joint-eigenspace family (over Fintype-indexed active set). -/
private noncomputable abbrev activeIdx
    (A B C D : Matrix (Fin m) (Fin m) ℂ) : Type :=
  {χ : Fin 4 → ℂ // jointEigenspace A B C D χ ≠ ⊥}

private noncomputable instance activeIdx_fintype
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    Fintype (activeIdx A B C D) :=
  (jointEigenspace_finite_support A B C D hA hB hC hD h_comm).fintype

/-- The orthogonal-family + IsInternal package needed to invoke
    `subordinateOrthonormalBasis`. -/
private lemma jointEigenspace_restricted_isInternal
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    DirectSum.IsInternal
      (fun χ : activeIdx A B C D => jointEigenspace A B C D χ.val) :=
  DirectSum.isInternal_ne_bot_iff.mpr
    (jointEigenspace_isInternal A B C D hA hB hC hD h_comm)

private lemma jointEigenspace_restricted_orthogonalFamily
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian) :
    OrthogonalFamily ℂ
      (G := fun χ : activeIdx A B C D =>
        (jointEigenspace A B C D χ.val : Submodule ℂ (EuclideanSpace ℂ (Fin m))))
      (fun χ : activeIdx A B C D => (jointEigenspace A B C D χ.val).subtypeₗᵢ) := by
  -- Use `OrthogonalFamily.comp` on the full family.
  have h_full :
      OrthogonalFamily ℂ
        (G := fun χ : Fin 4 → ℂ =>
          (jointEigenspace A B C D χ : Submodule ℂ (EuclideanSpace ℂ (Fin m))))
        (fun χ => (jointEigenspace A B C D χ).subtypeₗᵢ) := by
    -- Unfold jointEigenspace to apply the JointEigenspace lemma.
    change OrthogonalFamily ℂ
        (fun χ : Fin 4 → ℂ => (⨅ j, Module.End.eigenspace (fourLin A B C D j) (χ j) :
            Submodule ℂ (EuclideanSpace ℂ (Fin m))))
        (fun χ => (⨅ j, Module.End.eigenspace (fourLin A B C D j) (χ j)).subtypeₗᵢ)
    exact LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces
      (fourLin_isSymmetric A B C D hA hB hC hD)
  exact h_full.comp Subtype.val_injective

/-- `finrank` of `EuclideanSpace ℂ (Fin m)` equals `m`. -/
private lemma finrank_euclideanSpace_eq :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by
  rw [finrank_euclideanSpace]
  exact Fintype.card_fin m

/-- The subordinate orthonormal basis indexed by `Fin m`, built from the
    restricted joint-eigenspace decomposition. -/
private noncomputable def jointOrthonormalBasis
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) :=
  letI := activeIdx_fintype A B C D hA hB hC hD h_comm
  DirectSum.IsInternal.subordinateOrthonormalBasis
    (V := fun χ : activeIdx A B C D => jointEigenspace A B C D χ.val)
    finrank_euclideanSpace_eq
    (jointEigenspace_restricted_isInternal A B C D hA hB hC hD h_comm)
    (jointEigenspace_restricted_orthogonalFamily A B C D hA hB hC hD)

/-- Each basis vector lies in some joint eigenspace.  Returns the
    index. -/
private noncomputable def jointOrthonormalBasis_index
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D)
    (i : Fin m) : activeIdx A B C D :=
  letI := activeIdx_fintype A B C D hA hB hC hD h_comm
  DirectSum.IsInternal.subordinateOrthonormalBasisIndex
    (V := fun χ : activeIdx A B C D => jointEigenspace A B C D χ.val)
    finrank_euclideanSpace_eq
    (jointEigenspace_restricted_isInternal A B C D hA hB hC hD h_comm)
    i
    (jointEigenspace_restricted_orthogonalFamily A B C D hA hB hC hD)

/-- Each basis vector lies in the joint eigenspace identified by its index. -/
private lemma jointOrthonormalBasis_mem
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D)
    (i : Fin m) :
    (jointOrthonormalBasis A B C D hA hB hC hD h_comm i :
        EuclideanSpace ℂ (Fin m)) ∈
      jointEigenspace A B C D
        (jointOrthonormalBasis_index A B C D hA hB hC hD h_comm i).val := by
  letI := activeIdx_fintype A B C D hA hB hC hD h_comm
  exact DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate
    (V := fun χ : activeIdx A B C D => jointEigenspace A B C D χ.val)
    finrank_euclideanSpace_eq
    (jointEigenspace_restricted_isInternal A B C D hA hB hC hD h_comm)
    i
    (jointEigenspace_restricted_orthogonalFamily A B C D hA hB hC hD)

/-- A vector `v` in `jointEigenspace A B C D χ` is an eigenvector of each
    matrix with eigenvalue `χ j` (for j = 0, 1, 2, 3). -/
private lemma mem_jointEigenspace_eigen
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (χ : Fin 4 → ℂ) (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ jointEigenspace A B C D χ) :
    (fourLin A B C D 0) v = (χ 0) • v ∧
    (fourLin A B C D 1) v = (χ 1) • v ∧
    (fourLin A B C D 2) v = (χ 2) • v ∧
    (fourLin A B C D 3) v = (χ 3) • v := by
  -- Unfold the iInf and use mem_eigenspace_iff.
  rw [jointEigenspace, Submodule.mem_iInf] at hv
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (rw [← Module.End.mem_eigenspace_iff]; exact hv _)

/-- The complex eigenvalues `χ j` for `χ : Fin 4 → ℂ` such that
    `jointEigenspace A B C D χ ≠ ⊥` are actually REAL (because each matrix
    is Hermitian, hence symmetric, hence has real eigenvalues). -/
private lemma jointEigenvalue_is_real
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (χ : Fin 4 → ℂ) (hχ : jointEigenspace A B C D χ ≠ ⊥) :
    ∀ j, (χ j).im = 0 := by
  intro j
  -- The submodule is nontrivial, so contains a nonzero vector v with
  -- (T j) v = (χ j) • v.  By IsSymmetric, the eigenvalue is real.
  obtain ⟨v, hv_mem, hv_ne⟩ : ∃ v ∈ jointEigenspace A B C D χ, v ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    apply hχ
    rw [Submodule.eq_bot_iff]
    exact h_all
  have heigen : (fourLin A B C D j) v = (χ j) • v := by
    rw [jointEigenspace, Submodule.mem_iInf] at hv_mem
    rw [← Module.End.mem_eigenspace_iff]; exact hv_mem _
  -- Show (χ j) is real via IsSymmetric.
  have hT_sym : (fourLin A B C D j).IsSymmetric :=
    fourLin_isSymmetric A B C D hA hB hC hD j
  -- For symmetric T and eigenvector v ≠ 0 with T v = μ • v, μ is real.
  have hμ_eigenvalue : Module.End.HasEigenvalue (fourLin A B C D j) (χ j) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr heigen, hv_ne⟩
  have h_conj : starRingEnd ℂ (χ j) = χ j :=
    hT_sym.conj_eigenvalue_eq_self hμ_eigenvalue
  -- starRingEnd ℂ x = star x = (x.re, -x.im).  Equating with x: x.im = 0.
  have h_im : (starRingEnd ℂ (χ j)).im = (χ j).im := by rw [h_conj]
  simp only [Complex.conj_im] at h_im
  linarith

/-- The real-valued eigenvalue function (the j-th component of the
    subordinate joint-eigenvalue index, cast to real). -/
private noncomputable def jointEigenvalue
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) (j : Fin 4) (i : Fin m) : ℝ :=
  ((jointOrthonormalBasis_index A B C D hA hB hC hD h_comm i).val j).re

/-- Bridge from real-cast eigenvalues back to complex. -/
private lemma jointEigenvalue_cast
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) (j : Fin 4) (i : Fin m) :
    ((jointEigenvalue A B C D hA hB hC hD h_comm j i : ℝ) : ℂ)
      = (jointOrthonormalBasis_index A B C D hA hB hC hD h_comm i).val j := by
  unfold jointEigenvalue
  have h_im_zero :
      ((jointOrthonormalBasis_index A B C D hA hB hC hD h_comm i).val j).im = 0 :=
    jointEigenvalue_is_real A B C D hA hB hC hD _
      (jointOrthonormalBasis_index A B C D hA hB hC hD h_comm i).property j
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]; exact h_im_zero.symm

/-- The j-th matrix acts on the i-th basis vector as multiplication by the
    j-th component of the joint eigenvalue (in `EuclideanSpace ℂ (Fin m)`). -/
private lemma fourLin_action_on_basis
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) (j : Fin 4) (i : Fin m) :
    (fourLin A B C D j)
        (jointOrthonormalBasis A B C D hA hB hC hD h_comm i)
      = ((jointEigenvalue A B C D hA hB hC hD h_comm j i : ℝ) : ℂ) •
          (jointOrthonormalBasis A B C D hA hB hC hD h_comm i) := by
  have h_mem := jointOrthonormalBasis_mem A B C D hA hB hC hD h_comm i
  rw [jointEigenspace, Submodule.mem_iInf] at h_mem
  have h_action :=
    Module.End.mem_eigenspace_iff.mp (h_mem j)
  rw [h_action, jointEigenvalue_cast]

/-- Translate the linear-map action `(A.toEuclideanLin) v = c • v`
    to the matrix-mulVec form `A *ᵥ ⇑v = c • ⇑v` (on underlying `Fin m → ℂ`). -/
private lemma toEuclideanLin_action_mulVec
    (A : Matrix (Fin m) (Fin m) ℂ) (v : EuclideanSpace ℂ (Fin m)) (c : ℂ)
    (h : A.toEuclideanLin v = c • v) :
    A.mulVec (⇑v : Fin m → ℂ) = c • (⇑v : Fin m → ℂ) := by
  -- toEuclideanLin A v = toLp 2 (A.mulVec (ofLp v)) = toLp 2 (A.mulVec ⇑v).
  -- And v : EuclideanSpace = WithLp 2 (Fin m → ℂ), with ⇑v = ofLp v.
  -- The equation `toLp 2 (A *ᵥ ⇑v) = c • v` rewrites to `A *ᵥ ⇑v = ofLp (c • v) = c • ⇑v`
  -- via the WithLp equivalence (which is a linear equiv, preserving scalar multiplication).
  have h_left : A.toEuclideanLin v = WithLp.toLp 2 (A.mulVec ⇑v) := rfl
  rw [h_left] at h
  -- h : WithLp.toLp 2 (A.mulVec ⇑v) = c • v.
  -- Apply WithLp.ofLp on both sides.
  have h' := congr_arg (WithLp.ofLp (p := (2 : ENNReal))) h
  -- LHS: WithLp.ofLp (WithLp.toLp 2 _) = _.
  rw [WithLp.ofLp_toLp] at h'
  -- h' : A.mulVec ⇑v = ofLp (c • v).  Now `ofLp (c • v) = c • ofLp v = c • ⇑v`.
  rw [h']
  -- Goal: ofLp (c • v) = c • ⇑v.  This holds by linearity of ofLp (or via WithLp.smul_apply).
  rfl

/-- **EXISTENCE of joint eigenbasis**: every quadruple of pairwise-commuting
    Hermitian matrices admits a `JointEigenbasis`. -/
theorem jointEigenbasis_exists_of_allCommute
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    Nonempty (JointEigenbasis A B C D) := by
  refine ⟨{
    e := jointOrthonormalBasis A B C D hA hB hC hD h_comm
    lamA := jointEigenvalue A B C D hA hB hC hD h_comm 0
    lamB := jointEigenvalue A B C D hA hB hC hD h_comm 1
    lamC := jointEigenvalue A B C D hA hB hC hD h_comm 2
    lamD := jointEigenvalue A B C D hA hB hC hD h_comm 3
    eigenA := ?_
    eigenB := ?_
    eigenC := ?_
    eigenD := ?_
  }⟩
  · intro i
    have h_act := fourLin_action_on_basis A B C D hA hB hC hD h_comm 0 i
    rw [fourLin_zero] at h_act
    exact toEuclideanLin_action_mulVec A _ _ h_act
  · intro i
    have h_act := fourLin_action_on_basis A B C D hA hB hC hD h_comm 1 i
    rw [fourLin_one] at h_act
    exact toEuclideanLin_action_mulVec B _ _ h_act
  · intro i
    have h_act := fourLin_action_on_basis A B C D hA hB hC hD h_comm 2 i
    rw [fourLin_two] at h_act
    exact toEuclideanLin_action_mulVec C _ _ h_act
  · intro i
    have h_act := fourLin_action_on_basis A B C D hA hB hC hD h_comm 3 i
    rw [fourLin_three] at h_act
    exact toEuclideanLin_action_mulVec D _ _ h_act

end ExistenceProof

/-! ## 5. Headline unconditional existence + Lieb-corrected. -/

section Headlines

variable {m : ℕ}

/-- **Existence of `JointDiagonalisation` from existence of
    `JointEigenbasis`.**  The conversion is via
    `JointDiagonalisation_of_jointEigenbasis`. -/
theorem jointDiagonalisation_exists_of_jointEigenbasis
    {A B C D : Matrix (Fin m) (Fin m) ℂ}
    (h : Nonempty (JointEigenbasis A B C D)) :
    Nonempty (JointDiagonalisation A B C D) :=
  h.elim (fun JE => ⟨JointDiagonalisation_of_jointEigenbasis JE⟩)

/-- **THE HEADLINE EXISTENCE THEOREM**: every quadruple of pairwise-commuting
    Hermitian matrices on `Matrix (Fin m) (Fin m) ℂ` admits a
    `JointDiagonalisation` (shared diagonalising unitary). -/
theorem jointDiagonalisation_exists_of_allCommute
    (A B C D : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (h_comm : AllCommute A B C D) :
    Nonempty (JointDiagonalisation A B C D) :=
  jointDiagonalisation_exists_of_jointEigenbasis
    (jointEigenbasis_exists_of_allCommute A B C D hA hB hC hD h_comm)

/-- **UNCONDITIONAL COMMUTING LIEB-CORRECTED TARGET**: for any four
    pairwise-commuting PosDef matrices, the corrected joint convexity
    of Umegaki relative entropy holds.

    Combines `jointDiagonalisation_exists_of_allCommute` with
    `lieb1973_corrected_of_jointDiag`. -/
theorem lieb1973_corrected_commuting_unconditional
    (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (h_comm : AllCommute A₁ A₂ B₁ B₂)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    let A_t : Matrix (Fin m) (Fin m) ℂ :=
      (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
    let B_t : Matrix (Fin m) (Fin m) ℂ :=
      (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
    (Matrix.trace (A_t * cfc Real.log A_t)).re
        - (Matrix.trace (A_t * cfc Real.log B_t)).re
      ≤ α * ((Matrix.trace (A₁ * cfc Real.log A₁)).re
              - (Matrix.trace (A₁ * cfc Real.log B₁)).re)
        + (1 - α) * ((Matrix.trace (A₂ * cfc Real.log A₂)).re
                      - (Matrix.trace (A₂ * cfc Real.log B₂)).re) := by
  obtain ⟨JD⟩ := jointDiagonalisation_exists_of_allCommute
    A₁ A₂ B₁ B₂ hA₁.isHermitian hA₂.isHermitian hB₁.isHermitian hB₂.isHermitian h_comm
  exact lieb1973_corrected_of_jointDiag A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ JD α hα₀ hα₁

end Headlines

/-! ## 6. Axiom audit. -/

-- #print axioms jointEigenbasis_exists_of_allCommute
-- #print axioms jointDiagonalisation_exists_of_allCommute
-- #print axioms lieb1973_corrected_commuting_unconditional
-- VERIFIED 2026-06-01:
--   All three depend ONLY on [propext, Classical.choice, Quot.sound]
--   (Lean's three standard foundational axioms).
--   No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.JointDiagonalisationCommuting
