/-
  LayerB/CFCLogTensor.lean
  ─────────────────────────

  **Discharge of `CFC_LogTensor_Identity_Target`.**

  This file delivers, UNCONDITIONALLY, the spectral tensor identity for
  the matrix logarithm:

      `cfc Real.log (A ⊗ₖ B) = cfc Real.log A ⊗ₖ I_m + I_n ⊗ₖ cfc Real.log B`

  for positive-definite Hermitian matrices `A` on `Fin n` and `B` on
  `Fin m`, then reindexes through `finProdFinEquiv : Fin n × Fin m ≃
  Fin (n * m)` to discharge the target gate
  `CFC_LogTensor_Identity_Target` declared in
  `UmegakiTensorAdditivity.lean`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Mathematical content (spectral decomposition route):

  1. PosDef `A = U_A · D_A · U_A†` with `D_A = diagonal(λ ∘ eigenvalues)`.
     Likewise `B = U_B · D_B · U_B†`.

  2. Kronecker preserves multiplication and `*`:
       `A ⊗ₖ B = (U_A ⊗ₖ U_B) · (D_A ⊗ₖ D_B) · (U_A ⊗ₖ U_B)†`.

  3. `D_A ⊗ₖ D_B = diagonal (i, j ↦ a_i · b_j)` (diagonal-tensor-diagonal).

  4. CFC commutes with the star-algebra automorphism `M ↦ W · M · W†`
     given by the unitary `W = U_A ⊗ₖ U_B` (general
     `StarAlgHomClass.map_cfc`).

  5. The diagonal log:
       `cfc Real.log (diag(a_i b_j)) = diag(Real.log a_i + Real.log b_j)`
       = `diag(Real.log a_i) + diag(Real.log b_j)` (additive on diagonal).
     We then split each summand as `diag(Real.log a_i) ⊗ₖ 1` and
     `1 ⊗ₖ diag(Real.log b_j)` (kronecker with the identity).

  6. Reassemble via `mul_kronecker_mul` to bring conjugation through:
       `(U_A ⊗ₖ U_B) · (diag(log a_i) ⊗ₖ 1) · (U_A ⊗ₖ U_B)†
          = (U_A · diag(log a_i) · U_A†) ⊗ₖ (U_B · 1 · U_B†)
          = cfc Real.log A ⊗ₖ 1`.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  STANDING CONSTRAINT: zero `sorry`, zero custom `axiom`.

  ## Build target

      `lake build UnifiedTheory.LayerB.CFCLogTensor`
-/

import UnifiedTheory.LayerB.UmegakiTensorAdditivity
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CFCLogTensor

open Matrix Complex
open scoped Kronecker MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.UmegakiTensorAdditivity
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.CFCDiagonalDischarge

/-! ## 1.  Hermiticity of building blocks. -/

/-- `(1 : Matrix m m ℂ)` is self-adjoint. -/
lemma isSelfAdjoint_one_matrix {m : ℕ} :
    IsSelfAdjoint (1 : Matrix (Fin m) (Fin m) ℂ) := by
  change (1 : Matrix (Fin m) (Fin m) ℂ).IsHermitian
  exact Matrix.isHermitian_one

/-- `(A ⊗ₖ B)` is self-adjoint when `A` and `B` are self-adjoint. -/
lemma isSelfAdjoint_kronecker {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A ⊗ₖ B) := by
  change (A ⊗ₖ B).IsHermitian
  have hA' : A.conjTranspose = A := hA
  have hB' : B.conjTranspose = B := hB
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hA', hB']

/-! ## 2.  Generic entrywise diagonal CFC on an arbitrary finite index. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ℝ`-spectrum of the complex diagonal matrix with real entries
    (generic index version). -/
lemma spectrum_real_diagonal_ofReal_generic (d : ι → ℝ) :
    spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) = Set.range d := by
  ext r
  rw [← spectrum.algebraMap_mem_iff ℂ
        (R := ℝ) (a := Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) (r := r),
      spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h1 : ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ r := hi
    rw [RCLike.algebraMap_eq_ofReal] at h1
    exact Complex.ofReal_inj.mp h1
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [RCLike.algebraMap_eq_ofReal]
    change ((d i : ℝ) : ℂ) = ((r : ℝ) : ℂ)
    exact_mod_cast hi

lemma diagonal_entry_mem_spectrum_real_generic (d : ι → ℝ) (i : ι) :
    d i ∈ spectrum ℝ (Matrix.diagonal (fun j => ((d j : ℝ) : ℂ))) := by
  rw [spectrum_real_diagonal_ofReal_generic]; exact ⟨i, rfl⟩

lemma isSelfAdjoint_diagonal_ofReal_generic (d : ι → ℝ) :
    IsSelfAdjoint (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) := by
  change (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian
  refine isHermitian_diagonal_of_self_adjoint _ ?_
  change star (fun i => ((d i : ℝ) : ℂ)) = (fun i => ((d i : ℝ) : ℂ))
  funext i
  exact Complex.conj_ofReal _

/-- The candidate alternative `⋆`-algebra homomorphism (generic index):
    for a continuous real-valued function `g` on the spectrum of the
    diagonal matrix, return the complex diagonal matrix whose `i`-th
    entry is `g(d i)` cast to `ℂ`. -/
@[simps]
noncomputable def entrywiseDiagHomGeneric (d : ι → ℝ) :
    C(spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))), ℝ)
      →⋆ₐ[ℝ] (Matrix ι ι ℂ) where
  toFun g :=
    Matrix.diagonal
      (fun i =>
        ((g ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
  map_zero' := by ext i j; simp
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  map_mul' f g := by
    change Matrix.diagonal
            (fun i => ((((f * g) : C(_, _))
              ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
          = Matrix.diagonal
              (fun i =>
                ((f ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
            * Matrix.diagonal
                (fun i =>
                  ((g ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
    rw [Matrix.diagonal_mul_diagonal]
    refine congrArg _ ?_
    funext i
    simp [ContinuousMap.mul_apply]
  map_add' f g := by
    change Matrix.diagonal
            (fun i => ((((f + g) : C(_, _))
              ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
          = Matrix.diagonal
              (fun i =>
                ((f ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
            + Matrix.diagonal
                (fun i =>
                  ((g ⟨d i, diagonal_entry_mem_spectrum_real_generic d i⟩ : ℝ) : ℂ))
    rw [Matrix.diagonal_add]
    refine congrArg _ ?_
    funext i
    simp [ContinuousMap.add_apply]
  commutes' r := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.algebraMap_matrix_apply, RCLike.algebraMap_eq_ofReal,
            Matrix.diagonal_apply_eq, _root_.algebraMap_apply]
    · simp [Matrix.algebraMap_matrix_apply, h]
  map_star' f := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    refine congrArg _ ?_
    funext i
    simp [Complex.conj_ofReal]

lemma entrywiseDiagHomGeneric_continuous (d : ι → ℝ) :
    Continuous (entrywiseDiagHomGeneric d) := by
  have hfin : FiniteDimensional ℝ
      C(spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))), ℝ) :=
    FiniteDimensional.of_injective
      (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  exact (entrywiseDiagHomGeneric d).toLinearMap.continuous_of_finiteDimensional

lemma entrywiseDiagHomGeneric_map_id (d : ι → ℝ) :
    entrywiseDiagHomGeneric d
        ((ContinuousMap.id ℝ).restrict
          (spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))))
      = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := rfl

/-- **Generic-index entrywise CFC on a diagonal matrix.** -/
theorem cfc_diagonal_entrywise_generic (f : ℝ → ℝ) (d : ι → ℝ) :
    cfc f (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))
      = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  set D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  have hSA : IsSelfAdjoint D := isSelfAdjoint_diagonal_ofReal_generic d
  have hfin : (spectrum ℝ D).Finite := by
    rw [hD, spectrum_real_diagonal_ofReal_generic]
    exact Set.finite_range d
  have hCont : ContinuousOn f (spectrum ℝ D) := hfin.continuousOn f
  rw [cfc_apply (R := ℝ) (A := Matrix ι ι ℂ) f D hSA hCont]
  have huniq : cfcHom (R := ℝ) (A := Matrix ι ι ℂ) hSA
                = entrywiseDiagHomGeneric d := by
    refine cfcHom_eq_of_continuous_of_map_id hSA (entrywiseDiagHomGeneric d)
      (entrywiseDiagHomGeneric_continuous d) ?_
    exact entrywiseDiagHomGeneric_map_id d
  rw [huniq]
  change
    entrywiseDiagHomGeneric d
        ⟨(spectrum ℝ D).restrict f, hCont.restrict⟩
      = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ))
  rfl

/-! ## 3.  Diagonal log on a product index, split into a Kronecker sum. -/

variable {n m : ℕ}

/-- **Diagonal log on the Kronecker eigenvalue product.**
    For positive eigenvalues `a : Fin n → ℝ` (all `> 0`) and
    `b : Fin m → ℝ` (all `> 0`),

      `cfc Real.log (diag(i,j ↦ ((a i * b j : ℝ) : ℂ)))
         = diag(i ↦ ((Real.log (a i) : ℝ) : ℂ)) ⊗ₖ 1
            + 1 ⊗ₖ diag(j ↦ ((Real.log (b j) : ℝ) : ℂ))`. -/
lemma cfc_log_diagonal_kronecker
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    cfc Real.log (Matrix.diagonal
        (fun p : Fin n × Fin m => (((a p.1) * (b p.2) : ℝ) : ℂ)))
      = (Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ)
        + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
            (Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ))) := by
  -- Apply the generic-index entrywise CFC on `ι = Fin n × Fin m`.
  have h_cfc :
      cfc Real.log (Matrix.diagonal
          (fun p : Fin n × Fin m => (((a p.1) * (b p.2) : ℝ) : ℂ)))
        = Matrix.diagonal
            (fun p : Fin n × Fin m =>
              ((Real.log ((a p.1) * (b p.2)) : ℝ) : ℂ)) :=
    cfc_diagonal_entrywise_generic (ι := Fin n × Fin m) Real.log
      (fun p => (a p.1) * (b p.2))
  rw [h_cfc]
  -- Now: diag(log(a_i b_j)) = diag(log a_i + log b_j).
  have h_log_split :
      (fun p : Fin n × Fin m =>
          ((Real.log ((a p.1) * (b p.2)) : ℝ) : ℂ))
        = fun p : Fin n × Fin m =>
            ((Real.log (a p.1) + Real.log (b p.2) : ℝ) : ℂ) := by
    funext p
    rw [Real.log_mul (ne_of_gt (ha p.1)) (ne_of_gt (hb p.2))]
  rw [h_log_split]
  -- Split diag(log a + log b) into diag(log a) ⊗ I + I ⊗ diag(log b).
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [Matrix.add_apply, Matrix.kroneckerMap_apply]
  by_cases hii : i = i'
  · by_cases hjj : j = j'
    · subst hii; subst hjj
      simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
            Complex.ofReal_add]
    · -- j ≠ j': all four terms are 0
      have hne : ((i, j) : Fin n × Fin m) ≠ (i', j') := by
        intro h; apply hjj; exact (Prod.mk.inj h).2
      rw [Matrix.diagonal_apply_ne _ hne,
          Matrix.diagonal_apply_ne _ hjj,
          Matrix.one_apply_ne hjj]
      simp
  · -- i ≠ i': all four terms are 0
    have hne : ((i, j) : Fin n × Fin m) ≠ (i', j') := by
      intro h; apply hii; exact (Prod.mk.inj h).1
    rw [Matrix.diagonal_apply_ne _ hne,
        Matrix.diagonal_apply_ne _ hii,
        Matrix.one_apply_ne hii]
    simp

/-! ## 4.  Kronecker of two unitaries is unitary. -/

/-- The Kronecker of two unitary matrices, packaged as an element of
    the unitary group on the product index. -/
noncomputable def kroneckerUnitary
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Fin n × Fin m) ℂ :=
  ⟨U.val ⊗ₖ V.val, Matrix.kronecker_mem_unitary U.property V.property⟩

@[simp] lemma kroneckerUnitary_val
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    (kroneckerUnitary U V).val = U.val ⊗ₖ V.val := rfl

/-- `star (U ⊗ₖ V) = (star U) ⊗ₖ (star V)`. -/
lemma star_kroneckerUnitary
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    star (kroneckerUnitary U V).val
      = (star U.val) ⊗ₖ (star V.val) := by
  change (U.val ⊗ₖ V.val)ᴴ = U.valᴴ ⊗ₖ V.valᴴ
  exact Matrix.conjTranspose_kronecker U.val V.val

/-! ## 5.  CFC commutes with unitary conjugation (Fin n × Fin m index). -/

/-- **CFC naturality for unitary conjugation** on a `Fin n × Fin m`-indexed
    Hermitian matrix.  Generic-index version of
    `LayerB/UnitaryInvariance.lean`'s `cfc_unitary_conj`. -/
lemma cfc_unitary_conj_prod
    (W : Matrix.unitaryGroup (Fin n × Fin m) ℂ)
    (M : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) (f : ℝ → ℝ)
    (hM : IsSelfAdjoint M) :
    cfc f (W.val * M * star W.val) = W.val * (cfc f M) * star W.val := by
  have hf : ContinuousOn f (spectrum ℝ M) := (Set.toFinite _).continuousOn _
  let φ : (Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
            ≃⋆ₐ[ℂ] (Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :=
    Unitary.conjStarAlgAut ℂ _ W
  have h_phi_M : φ M = W.val * M * star W.val := by
    simp [φ, Unitary.conjStarAlgAut_apply]
  have h_phi_cfc : φ (cfc f M) = W.val * (cfc f M) * star W.val := by
    simp [φ, Unitary.conjStarAlgAut_apply]
  have h_phi_cont : Continuous φ := by
    have h_eq : (φ : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ →
                       Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
              = fun M => W.val * M * star W.val := by
      funext M; simp [φ, Unitary.conjStarAlgAut_apply]
    rw [h_eq]
    fun_prop
  have h_phi_M_SA : IsSelfAdjoint (φ M) := by
    rw [h_phi_M]; exact hM.conjugate W.val
  have key : φ (cfc f M) = cfc f (φ M) :=
    StarAlgHomClass.map_cfc (S := ℂ) (R := ℝ) φ f M hf h_phi_cont hM h_phi_M_SA
  rw [h_phi_M, h_phi_cfc] at key
  exact key.symm

/-! ## 6.  Spectral decomposition of `A ⊗ₖ B`. -/

/-- For PosDef `A`, the spectral decomposition `A = U · D_A · U†`. -/
lemma posDef_spectral_decomp
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    A = hA.1.eigenvectorUnitary.val
        * Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ))
        * star hA.1.eigenvectorUnitary.val := by
  have h := hA.1.spectral_theorem (𝕜 := ℂ)
  rw [Unitary.conjStarAlgAut_apply] at h
  convert h using 2

/-! ## 7.  Main spectral identity on `Fin n × Fin m`. -/

/-- **MAIN LEMMA (un-submatrixed)**: the spectral log of a Kronecker
    product of two positive-definite Hermitian matrices equals the
    Kronecker sum of the spectral logs. -/
theorem cfc_log_kronecker_prod
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B)
      = (cfc Real.log A) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
        + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (cfc Real.log B) := by
  classical
  -- Eigenvalues and their positivity.
  set a : Fin n → ℝ := hA.1.eigenvalues with ha_def
  set b : Fin m → ℝ := hB.1.eigenvalues with hb_def
  have ha_pos : ∀ i, 0 < a i := fun i => hA.eigenvalues_pos i
  have hb_pos : ∀ j, 0 < b j := fun j => hB.eigenvalues_pos j
  -- Eigenvector unitaries.
  set U : Matrix.unitaryGroup (Fin n) ℂ := hA.1.eigenvectorUnitary with hU_def
  set V : Matrix.unitaryGroup (Fin m) ℂ := hB.1.eigenvectorUnitary with hV_def
  set W : Matrix.unitaryGroup (Fin n × Fin m) ℂ := kroneckerUnitary U V with hW_def
  -- Diagonal matrices.
  set D_A : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) with hDA_def
  set D_B : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun j => ((b j : ℝ) : ℂ)) with hDB_def
  -- Spectral decompositions.
  have hA_spec : A = U.val * D_A * star U.val :=
    posDef_spectral_decomp A hA
  have hB_spec : B = V.val * D_B * star V.val :=
    posDef_spectral_decomp B hB
  -- Hermiticity of D_A, D_B.
  have hDA_SA : IsSelfAdjoint D_A := isSelfAdjoint_diagonal_ofReal_generic a
  have hDB_SA : IsSelfAdjoint D_B := isSelfAdjoint_diagonal_ofReal_generic b
  -- Kronecker decomposition.
  have h_AB :
      A ⊗ₖ B = W.val * (D_A ⊗ₖ D_B) * star W.val := by
    rw [hA_spec, hB_spec]
    -- (U D_A U†) ⊗ (V D_B V†) = (U ⊗ V) (D_A U†) ⊗ (D_B V†)
    --                        = (U ⊗ V) ((D_A ⊗ D_B) (U† ⊗ V†))
    --                        = (U ⊗ V) (D_A ⊗ D_B) (U ⊗ V)†
    have h1 :
        (U.val * D_A * star U.val) ⊗ₖ (V.val * D_B * star V.val)
          = (U.val * D_A) ⊗ₖ (V.val * D_B) *
              ((star U.val) ⊗ₖ (star V.val)) := by
      have := Matrix.mul_kronecker_mul (U.val * D_A) (star U.val) (V.val * D_B) (star V.val)
      exact this
    rw [h1]
    have h2 :
        (U.val * D_A) ⊗ₖ (V.val * D_B) = (U.val ⊗ₖ V.val) * (D_A ⊗ₖ D_B) := by
      have := Matrix.mul_kronecker_mul U.val D_A V.val D_B
      exact this
    rw [h2]
    -- Now arrange: ((U ⊗ V) (D_A ⊗ D_B)) ((star U) ⊗ (star V))
    --            = W * (D_A ⊗ D_B) * star W
    rw [hW_def, star_kroneckerUnitary, kroneckerUnitary_val]
  -- Combine to compute cfc Real.log (A ⊗ₖ B).
  rw [h_AB]
  -- Hermiticity of D_A ⊗ₖ D_B.
  have hDAB_SA : IsSelfAdjoint ((D_A ⊗ₖ D_B) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :=
    isSelfAdjoint_kronecker hDA_SA hDB_SA
  -- Apply cfc-unitary-conjugation on product index.
  rw [cfc_unitary_conj_prod W (D_A ⊗ₖ D_B) Real.log hDAB_SA]
  -- Now: cfc Real.log (D_A ⊗ₖ D_B).
  -- First, D_A ⊗ₖ D_B = diagonal (i,j ↦ ((a i : ℂ) * (b j : ℂ))).
  have h_diag_prod :
      (D_A ⊗ₖ D_B :
        Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
        = Matrix.diagonal (fun p : Fin n × Fin m =>
            (((a p.1) * (b p.2) : ℝ) : ℂ)) := by
    rw [hDA_def, hDB_def, Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext p
    push_cast
    ring
  rw [h_diag_prod]
  -- Apply the diagonal-log Kronecker split.
  rw [cfc_log_diagonal_kronecker a b ha_pos hb_pos]
  -- Distribute W · (X ⊗ₖ 1 + 1 ⊗ₖ Y) · star W
  --   = W · (X ⊗ₖ 1) · star W + W · (1 ⊗ₖ Y) · star W
  rw [Matrix.mul_add, Matrix.add_mul]
  -- Goal: W · ((diag log a) ⊗ 1) · star W + W · (1 ⊗ (diag log b)) · star W
  --     = cfc log A ⊗ 1 + 1 ⊗ cfc log B
  -- We compute each summand by Kronecker decomposition.
  congr 1
  · -- W · (diag(log a) ⊗ 1) · star W = cfc log A ⊗ 1
    rw [hW_def, star_kroneckerUnitary, kroneckerUnitary_val]
    rw [show U.val ⊗ₖ V.val * (Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)) ⊗ₖ
              (1 : Matrix (Fin m) (Fin m) ℂ))
          = (U.val * Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ))) ⊗ₖ
              (V.val * (1 : Matrix (Fin m) (Fin m) ℂ))
        from by rw [← Matrix.mul_kronecker_mul]]
    rw [show ((U.val * Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)))
                  ⊗ₖ (V.val * (1 : Matrix (Fin m) (Fin m) ℂ)))
              * (star U.val ⊗ₖ star V.val)
          = ((U.val * Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ))) * star U.val)
              ⊗ₖ ((V.val * (1 : Matrix (Fin m) (Fin m) ℂ)) * star V.val)
        from by rw [← Matrix.mul_kronecker_mul]]
    -- V * 1 * star V = V * star V = 1.
    have h_VV : V.val * (1 : Matrix (Fin m) (Fin m) ℂ) * star V.val = 1 := by
      rw [Matrix.mul_one]
      exact Matrix.mem_unitaryGroup_iff.mp V.property
    -- U * diag(log a) * star U = cfc log A: use cfc_unitary_conj.
    have h_UU :
        U.val * Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)) * star U.val
          = cfc Real.log A := by
      -- We use the entrywise CFC on diag(a) plus unitary conjugation.
      -- log A = cfc log (U D_A star U) = U (cfc log D_A) star U
      --       = U · diag(log a) · star U.
      have h_log_DA :
          cfc Real.log D_A
            = Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)) := by
        rw [hDA_def]
        exact cfc_diagonal_entrywise_generic (ι := Fin n) Real.log a
      calc U.val * Matrix.diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)) * star U.val
          = U.val * (cfc Real.log D_A) * star U.val := by rw [h_log_DA]
        _ = cfc Real.log (U.val * D_A * star U.val) := by
              rw [cfc_unitary_conj U D_A Real.log hDA_SA
                    (by exact (Set.toFinite _).continuousOn _)]
        _ = cfc Real.log A := by rw [← hA_spec]
    rw [h_UU, h_VV]
  · -- W · (1 ⊗ (diag log b)) · star W = 1 ⊗ cfc log B
    rw [hW_def, star_kroneckerUnitary, kroneckerUnitary_val]
    rw [show U.val ⊗ₖ V.val * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
              Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)))
          = (U.val * (1 : Matrix (Fin n) (Fin n) ℂ))
              ⊗ₖ (V.val * Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)))
        from by rw [← Matrix.mul_kronecker_mul]]
    rw [show ((U.val * (1 : Matrix (Fin n) (Fin n) ℂ))
                ⊗ₖ (V.val * Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ))))
              * (star U.val ⊗ₖ star V.val)
          = ((U.val * (1 : Matrix (Fin n) (Fin n) ℂ)) * star U.val)
              ⊗ₖ ((V.val * Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ))) * star V.val)
        from by rw [← Matrix.mul_kronecker_mul]]
    have h_UU : U.val * (1 : Matrix (Fin n) (Fin n) ℂ) * star U.val = 1 := by
      rw [Matrix.mul_one]
      exact Matrix.mem_unitaryGroup_iff.mp U.property
    have h_VV :
        V.val * Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)) * star V.val
          = cfc Real.log B := by
      have h_log_DB :
          cfc Real.log D_B
            = Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)) := by
        rw [hDB_def]
        exact cfc_diagonal_entrywise_generic (ι := Fin m) Real.log b
      calc V.val * Matrix.diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)) * star V.val
          = V.val * (cfc Real.log D_B) * star V.val := by rw [h_log_DB]
        _ = cfc Real.log (V.val * D_B * star V.val) := by
              rw [cfc_unitary_conj V D_B Real.log hDB_SA
                    (by exact (Set.toFinite _).continuousOn _)]
        _ = cfc Real.log B := by rw [← hB_spec]
    rw [h_UU, h_VV]

/-! ## 8.  Reindex to `Fin (n*m)` and discharge the target gate.

The submatrix `M ↦ M.submatrix e.symm e.symm` along an equivalence is a
star-algebra automorphism (preserves +, *, scalar, and `*`).  The
continuous functional calculus commutes with star-algebra
homomorphisms (`StarAlgHomClass.map_cfc`), so submatrix and `cfc`
commute. -/

/-- Star algebra equivalence
    `Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ ≃⋆ₐ[ℂ]
       Matrix (Fin (n * m)) (Fin (n * m)) ℂ`
    via `finProdFinEquiv`. -/
noncomputable def reindexProdStarAlgEquiv (n m : ℕ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (n * m)) (Fin (n * m)) ℂ where
  toFun M := M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  invFun M := M.submatrix finProdFinEquiv finProdFinEquiv
  left_inv M := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  right_inv M := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  map_add' M N := by ext i j; simp [Matrix.submatrix_apply]
  map_mul' M N := by
    -- (M * N).submatrix e.symm e.symm = M.submatrix e.symm e.symm * N.submatrix e.symm e.symm
    -- using `submatrix_mul_equiv` with e₂ = e.symm (an equivalence).
    have h := Matrix.submatrix_mul_equiv (n := Fin n × Fin m)
      (m := Fin n × Fin m) (p := Fin n × Fin m)
      (α := ℂ) M N
      (e₁ := (finProdFinEquiv.symm : Fin (n * m) → Fin n × Fin m))
      (e₂ := finProdFinEquiv.symm)
      (e₃ := (finProdFinEquiv.symm : Fin (n * m) → Fin n × Fin m))
    exact h.symm
  map_star' M := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
  map_smul' c M := by ext i j; simp [Matrix.submatrix_apply, Matrix.smul_apply]

@[simp] lemma reindexProdStarAlgEquiv_apply (n m : ℕ)
    (M : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    reindexProdStarAlgEquiv n m M
      = M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm := rfl

lemma reindexProdStarAlgEquiv_continuous (n m : ℕ) :
    Continuous (reindexProdStarAlgEquiv n m) := by
  have h_eq :
      (reindexProdStarAlgEquiv n m :
         Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ →
           Matrix (Fin (n * m)) (Fin (n * m)) ℂ)
        = fun M => M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
    funext M; rfl
  rw [h_eq]
  exact continuous_pi (fun i => continuous_pi (fun j =>
    (continuous_apply_apply (finProdFinEquiv.symm i) (finProdFinEquiv.symm j))))

/-- `cfc` commutes with the reindex equivalence. -/
lemma cfc_submatrix_finProdFinEquiv (n m : ℕ)
    (M : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (f : ℝ → ℝ) (hM : IsSelfAdjoint M) :
    cfc f (M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
      = (cfc f M).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  have hf : ContinuousOn f (spectrum ℝ M) := (Set.toFinite _).continuousOn _
  have hφ : Continuous (reindexProdStarAlgEquiv n m) :=
    reindexProdStarAlgEquiv_continuous n m
  have hφM : IsSelfAdjoint (reindexProdStarAlgEquiv n m M) := by
    change star (reindexProdStarAlgEquiv n m M)
            = reindexProdStarAlgEquiv n m M
    rw [← map_star]
    exact congrArg _ hM
  have key : reindexProdStarAlgEquiv n m (cfc f M)
              = cfc f (reindexProdStarAlgEquiv n m M) := by
    exact StarAlgHomClass.map_cfc (S := ℂ) (R := ℝ)
      (reindexProdStarAlgEquiv n m) f M hf hφ hM hφM
  simp only [reindexProdStarAlgEquiv_apply] at key
  exact key.symm

/-! ## 9.  Final discharge of `CFC_LogTensor_Identity_Target`. -/

/-- **Headline theorem.**  The `CFC_LogTensor_Identity_Target` is
    discharged unconditionally. -/
theorem cfcLogTensorIdentity_holds : CFC_LogTensor_Identity_Target := by
  intro n m A B hA hB
  -- Hermiticity of A ⊗ₖ B.
  have hAB_SA : IsSelfAdjoint (A ⊗ₖ B) :=
    isSelfAdjoint_kronecker hA.1 hB.1
  -- Submatrix-cfc commutation, applied to A ⊗ₖ B.
  rw [cfc_submatrix_finProdFinEquiv n m (A ⊗ₖ B) Real.log hAB_SA]
  -- Apply the un-submatrixed main lemma.
  rw [cfc_log_kronecker_prod A B hA hB]

/-! ## 10.  Axiom audit (intended state after build)

    The following are intended to print only
      `propext, Classical.choice, Quot.sound`
    (Lean's three standard axioms).  No `sorry`, no custom `axiom`. -/

#print axioms cfcLogTensorIdentity_holds
#print axioms cfc_log_kronecker_prod

end UnifiedTheory.LayerB.CFCLogTensor
