/-
  LayerB/WeakSubadditivity.lean
  ──────────────────────────────

  **Weak subadditivity of the von Neumann entropy.**

  For a bipartite quantum state `ρ_AB : ComplexDensityMatrix (n_A * n_B)`
  with marginals

      ρ_A := Tr_B ρ_AB   (`partialTraceDensity_right`)
      ρ_B := Tr_A ρ_AB   (`partialTraceDensity_left`)

  the von Neumann entropies satisfy

      S(ρ_AB)  ≤  S(ρ_A) + S(ρ_B).

  ## Strategy (the real proof, no shortcut)

  Weak subadditivity is exactly the non-negativity of the quantum mutual
  information, which is a relative entropy:

      S(ρ_A) + S(ρ_B) − S(ρ_AB)
          =  S(ρ_AB ‖ ρ_A ⊗ ρ_B)
          =  umegakiRelativeEntropy ρ_AB (ρ_A ⊗ ρ_B)
          ≥  0          (Klein / Gibbs).

  The non-negativity is `umegakiRelativeEntropy_nonneg` (Klein's
  inequality, already proved in `KleinInequalityFull.lean`).  The work is
  the IDENTITY

      umegaki(ρ_AB, ρ_A ⊗ ρ_B) = − S(AB) + S(A) + S(B),

  which we assemble from:

    * `re_trace_mul_operatorLog` :  Re Tr(ρ · log ρ) = −S(ρ)        (xlogx),
    * the CFC tensor-log identity  log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B
      (`operatorLog_kroneckerDM`),
    * and the **marginal trace identities**

          Tr(ρ_AB · (M ⊗ I)) = Tr(ρ_A · M),
          Tr(ρ_AB · (I ⊗ M)) = Tr(ρ_B · M),

      which are the genuinely new pieces proved here at the
      product-index level (`trace_mul_kronecker_one_right`,
      `trace_mul_one_kronecker_left`).

  ## Downstream

    * `ArakiLieb.EntropyData.Subadditivity_Target` is discharged on a
      concrete `EntropyData` built from a bipartite density matrix
      (`vonNeumannEntropy`-valued), giving the FULLY UNCONDITIONAL
      Araki–Lieb sandwich `vonNeumannEntropy`-version.
    * `EntanglementAssistedCapacity.mutualInfo_nonneg_of_subadditive` is
      fed the operator-level subadditivity, proving `I(A:B) ≥ 0` for a
      genuine bipartite state.

  STANDING CONSTRAINT (NON-NEGOTIABLE): zero `sorry`, zero custom `axiom`.

  ## Build

      lake build UnifiedTheory.LayerB.WeakSubadditivity
-/
import UnifiedTheory.LayerB.UmegakiTensorAdditivityFull
import UnifiedTheory.LayerB.PartialTraceDPI
import UnifiedTheory.LayerB.HolevoUmegakiDischarge
import UnifiedTheory.LayerB.ArakiLieb
import UnifiedTheory.LayerB.EntanglementAssistedCapacity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.WeakSubadditivity

open Matrix Complex
open scoped Kronecker ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.UmegakiTensorAdditivity
open UnifiedTheory.LayerB.UmegakiTensorAdditivityFull
open UnifiedTheory.LayerB.CFCLogTensor
open UnifiedTheory.LayerB.HolevoUmegakiDischarge

variable {n_A n_B : ℕ}

/-! ## 1.  Marginal trace identities at the product-index level.

These are the genuinely new pieces.  Working with matrices indexed by
`Fin n_A × Fin n_B`, we show the "partial-trace adjoint" identities

    Tr( M · (A ⊗ₖ I) ) = Tr( (Tr_B M) · A ),
    Tr( M · (I ⊗ₖ B) ) = Tr( (Tr_A M) · B ),

by expanding both sides as explicit index sums and reindexing. -/

/-- **Right marginal trace identity (product index).**
    `Tr( M · (A ⊗ I) ) = Tr( (partialTrace_right M) · A )`. -/
lemma trace_mul_kronecker_one_right
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
    (A : Matrix (Fin n_A) (Fin n_A) ℂ) :
    Matrix.trace
        (M * (A ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)))
      = Matrix.trace ((partialTrace_right M) * A) := by
  classical
  -- Expand both traces as explicit index sums.
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply]
  -- LHS: ∑ p, (M * (A ⊗ 1)) p p ;  expand the matrix product and the
  -- product index p = (i,k).
  rw [Fintype.sum_prod_type]
  -- LHS = ∑ i, ∑ k, (M * (A ⊗ 1)) (i,k) (i,k)
  -- RHS = ∑ i, ((Tr_B M) * A) i i
  -- Compute each side into the canonical form ∑ i ∑ j ∑ k M (i,k) (j,k) * A j i.
  have hLHS : ∀ i : Fin n_A, ∀ k : Fin n_B,
      (M * (A ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))) (i, k) (i, k)
        = ∑ j, M (i, k) (j, k) * A j i := by
    intro i k
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- ∑ j, ∑ l, M (i,k) (j,l) * (A ⊗ 1) (j,l) (i,k)
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single k]
    · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
    · intro l _ hl
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hl, mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hRHS : ∀ i : Fin n_A,
      ((partialTrace_right M) * A) i i
        = ∑ j, (∑ k, M (i, k) (j, k)) * A j i := by
    intro i
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  simp_rw [hLHS, hRHS]
  -- LHS: ∑ i, ∑ k, ∑ j, M (i,k) (j,k) * A j i
  -- RHS: ∑ i, ∑ j, (∑ k, M (i,k) (j,k)) * A j i
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- **Left marginal trace identity (product index).**
    `Tr( M · (I ⊗ B) ) = Tr( (partialTrace_left M) · B )`. -/
lemma trace_mul_one_kronecker_left
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
    (B : Matrix (Fin n_B) (Fin n_B) ℂ) :
    Matrix.trace
        (M * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ B))
      = Matrix.trace ((partialTrace_left M) * B) := by
  classical
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply]
  -- LHS: ∑ p, (M * (1 ⊗ B)) p p ;  p = (i,k).
  rw [Fintype.sum_prod_type]
  -- We sum k (the surviving B-index) on the outside to match Tr_A.
  have hLHS : ∀ i : Fin n_A, ∀ k : Fin n_B,
      (M * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ B)) (i, k) (i, k)
        = ∑ l, M (i, k) (i, l) * B l k := by
    intro i k
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- ∑ a, ∑ l, M (i,k) (a,l) * (1 ⊗ B) (a,l) (i,k)
    -- (1 ⊗ B) (a,l) (i,k) = (1) a i * B l k, forcing a = i.
    rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro l _
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro l _
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne ha, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hRHS : ∀ k : Fin n_B,
      ((partialTrace_left M) * B) k k
        = ∑ l, (∑ i, M (i, k) (i, l)) * B l k := by
    intro k
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
  simp_rw [hLHS, hRHS]
  -- LHS: ∑ i, ∑ k, ∑ l, M (i,k) (i,l) * B l k
  -- RHS: ∑ k, ∑ l, (∑ i, M (i,k) (i,l)) * B l k
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]

/-! ## 2.  Reindexing bridge.

The operator log of `kroneckerDM ρ_A ρ_B` is a `submatrix
finProdFinEquiv.symm finProdFinEquiv.symm` of a product-indexed matrix.
We move the whole trace `Tr( P · Q.submatrix e.symm e.symm )` to the
product-index world `Tr( (reindexFactor P) · Q )`, where the marginal
trace identities apply. -/

/-- `Tr( P · Q.submatrix e.symm e.symm ) = Tr( (reindexFactor P) · Q )`,
    where `e = finProdFinEquiv`.  Reindex the whole product to the
    product-index world. -/
lemma trace_mul_submatrix_symm
    (P : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ)
    (Q : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    Matrix.trace
        (P * Q.submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
      = Matrix.trace ((reindexFactor P) * Q) := by
  unfold reindexFactor
  set R : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ :=
    Q.submatrix finProdFinEquiv.symm finProdFinEquiv.symm with hR
  -- Q = R.submatrix e e  (e.symm ∘ e = id).
  have hQ : Q = R.submatrix finProdFinEquiv finProdFinEquiv := by
    rw [hR, Matrix.submatrix_submatrix]
    simp
  -- RHS: (P.submatrix e e) * Q = (P.submatrix e e) * (R.submatrix e e)
  --                            = (P * R).submatrix e e
  rw [hQ, Matrix.submatrix_mul_equiv P R finProdFinEquiv finProdFinEquiv finProdFinEquiv]
  -- Goal: Tr(P * R) = Tr((P * R).submatrix e e).
  exact (trace_reindexFactor (P * R)).symm

/-! ## 3.  The cross term `Tr(ρ_AB · log(ρ_A ⊗ ρ_B))`.

Combining the CFC tensor-log identity with the marginal trace
identities, the cross term splits into the two marginal x-log-x traces,
i.e. `−S(A) − S(B)`. -/

/-- The matrix underlying `partialTraceDensity_right ρ` is exactly the
    product-index right partial trace of `reindexFactor ρ.M`. -/
lemma partialTraceDensity_right_M_eq
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (partialTraceDensity_right ρ).M
      = partialTrace_right (reindexFactor ρ.M) := rfl

/-- The matrix underlying `partialTraceDensity_left ρ` is exactly the
    product-index left partial trace of `reindexFactor ρ.M`. -/
lemma partialTraceDensity_left_M_eq
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (partialTraceDensity_left ρ).M
      = partialTrace_left (reindexFactor ρ.M) := rfl

/-- **Cross-term identity.**  For a bipartite state `ρ_AB` with
    positive-definite marginals `ρ_A := Tr_B ρ_AB`, `ρ_B := Tr_A ρ_AB`,

      Re Tr( ρ_AB · log(ρ_A ⊗ ρ_B) )  =  − S(ρ_A) − S(ρ_B).

    Assembled from the CFC tensor-log identity, the reindexing bridge,
    the two marginal trace identities, and `re_trace_mul_operatorLog`
    (Re Tr(ρ · log ρ) = −S(ρ)) on each marginal. -/
lemma re_trace_mul_operatorLog_kronecker_marginals
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    (Matrix.trace
        (ρ.M * operatorLog
          (kroneckerDM (partialTraceDensity_right ρ)
                        (partialTraceDensity_left ρ)))).re
      = - vonNeumannEntropy (partialTraceDensity_right ρ)
        - vonNeumannEntropy (partialTraceDensity_left ρ) := by
  set ρA := partialTraceDensity_right ρ with hρA
  set ρB := partialTraceDensity_left ρ with hρB
  -- Step 1: expand the operator log of the Kronecker product.
  rw [operatorLog_kroneckerDM cfcLogTensorIdentity_holds ρA ρB hA hB]
  -- Step 2: move the trace to the product-index world.
  rw [trace_mul_submatrix_symm ρ.M
        ((cfc Real.log ρA.M) ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)
          + (1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ (cfc Real.log ρB.M))]
  -- Step 3: distribute over the sum and apply the marginal identities.
  rw [Matrix.mul_add, Matrix.trace_add,
      trace_mul_kronecker_one_right (reindexFactor ρ.M) (cfc Real.log ρA.M),
      trace_mul_one_kronecker_left (reindexFactor ρ.M) (cfc Real.log ρB.M)]
  -- partialTrace_right/left (reindexFactor ρ.M) = ρA.M / ρB.M, and
  -- cfc Real.log ρA.M = operatorLog ρA.
  rw [← partialTraceDensity_right_M_eq ρ, ← partialTraceDensity_left_M_eq ρ]
  show (Matrix.trace (ρA.M * operatorLog ρA)
          + Matrix.trace (ρB.M * operatorLog ρB)).re = _
  rw [Complex.add_re, re_trace_mul_operatorLog ρA, re_trace_mul_operatorLog ρB]
  ring

/-! ## 4.  Positive-definiteness of the Kronecker product density. -/

/-- The Kronecker product of two positive-definite density matrices is
    positive definite (so Klein's inequality applies to it). -/
lemma kroneckerDM_posDef
    (ρA : ComplexDensityMatrix n_A) (ρB : ComplexDensityMatrix n_B)
    (hA : ρA.M.PosDef) (hB : ρB.M.PosDef) :
    (kroneckerDM ρA ρB).M.PosDef := by
  classical
  -- (kroneckerDM ρA ρB).M = (ρA.M ⊗ₖ ρB.M).submatrix e.symm e.symm.
  have hKron : (ρA.M ⊗ₖ ρB.M).PosDef := hA.kronecker hB
  show ((ρA.M ⊗ₖ ρB.M).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).PosDef
  -- PosSemidef is preserved by submatrix.
  have hPSD : ((ρA.M ⊗ₖ ρB.M).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm).PosSemidef :=
    hKron.posSemidef.submatrix finProdFinEquiv.symm
  -- IsUnit is preserved by submatrix along an equiv.
  have hUnit : IsUnit ((ρA.M ⊗ₖ ρB.M).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) :=
    (Matrix.isUnit_submatrix_equiv finProdFinEquiv.symm finProdFinEquiv.symm).mpr
      hKron.isUnit
  exact hPSD.posDef_iff_isUnit.mpr hUnit

/-! ## 5.  The mutual-information identity and weak subadditivity. -/

/-- **Quantum mutual information as a relative entropy (identity).**
    For a bipartite state `ρ_AB` with positive-definite marginals,

      umegaki(ρ_AB, ρ_A ⊗ ρ_B)  =  S(ρ_A) + S(ρ_B) − S(ρ_AB).

    This is the exact algebraic identity behind subadditivity. -/
theorem mutualInfo_eq_umegaki
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    umegakiRelativeEntropy ρ
        (kroneckerDM (partialTraceDensity_right ρ) (partialTraceDensity_left ρ))
      = vonNeumannEntropy (partialTraceDensity_right ρ)
        + vonNeumannEntropy (partialTraceDensity_left ρ)
        - vonNeumannEntropy ρ := by
  set ρA := partialTraceDensity_right ρ with hρA
  set ρB := partialTraceDensity_left ρ with hρB
  unfold umegakiRelativeEntropy
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  -- Re Tr(ρ · log ρ) = −S(ρ).
  rw [re_trace_mul_operatorLog ρ]
  -- Re Tr(ρ · log(ρA ⊗ ρB)) = −S(ρA) − S(ρB).
  rw [re_trace_mul_operatorLog_kronecker_marginals ρ hA hB]
  ring

/-- **WEAK SUBADDITIVITY OF VON NEUMANN ENTROPY.**

    For a bipartite quantum state `ρ_AB : ComplexDensityMatrix (n_A * n_B)`
    whose marginals `ρ_A := Tr_B ρ_AB`, `ρ_B := Tr_A ρ_AB` are
    positive definite,

      S(ρ_AB)  ≤  S(ρ_A) + S(ρ_B).

    This is a REAL theorem: the mutual-information identity
    (`mutualInfo_eq_umegaki`) plus Klein's inequality
    (`umegakiRelativeEntropy_nonneg`).  The only hypotheses are the
    positive-definiteness of `ρ_AB` and its two marginals (required for
    the operator logarithms and for Klein). -/
theorem weak_subadditivity
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    vonNeumannEntropy ρ
      ≤ vonNeumannEntropy (partialTraceDensity_right ρ)
        + vonNeumannEntropy (partialTraceDensity_left ρ) := by
  -- Klein: 0 ≤ umegaki(ρ_AB, ρ_A ⊗ ρ_B).
  have hKlein :
      0 ≤ umegakiRelativeEntropy ρ
            (kroneckerDM (partialTraceDensity_right ρ)
                          (partialTraceDensity_left ρ)) :=
    umegakiRelativeEntropy_nonneg ρ
      (kroneckerDM (partialTraceDensity_right ρ) (partialTraceDensity_left ρ))
      hρ (kroneckerDM_posDef _ _ hA hB)
  -- Identity: umegaki = S(A) + S(B) − S(AB).
  rw [mutualInfo_eq_umegaki ρ hA hB] at hKlein
  linarith

/-! ## 6.  Downstream discharges. -/

open UnifiedTheory.LayerB.ArakiLieb
open UnifiedTheory.LayerB.EntanglementAssistedCapacity

/-- **Discharge of `ArakiLieb.EntropyData.Subadditivity_Target`.**

    For any `EntropyData` whose entropy fields are the von Neumann
    entropies of a genuine bipartite state `ρ_AB` and its marginals,
    the abstract `Subadditivity_Target` (`SAB ≤ SA + SB`) holds — not by
    fiat, but as a consequence of the operator-level
    `weak_subadditivity`. -/
theorem entropyData_subadditivity_of_density
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef)
    (d : EntropyData)
    (hSA : d.SA = vonNeumannEntropy (partialTraceDensity_right ρ))
    (hSB : d.SB = vonNeumannEntropy (partialTraceDensity_left ρ))
    (hSAB : d.SAB = vonNeumannEntropy ρ) :
    d.Subadditivity_Target := by
  show d.SAB ≤ d.SA + d.SB
  rw [hSA, hSB, hSAB]
  exact weak_subadditivity ρ hρ hA hB

/-- **Operator-level quantum-mutual-information non-negativity**
    (discharges the `mutualInfo_nonneg`-style target of
    `EntanglementAssistedCapacity`).

    With `S_A := S(ρ_A)`, `S_B := S(ρ_B)`, `S_AB := S(ρ_AB)`,

      I(A:B) := S_A + S_B − S_AB  ≥  0,

    obtained by feeding the operator-level `weak_subadditivity` into the
    scalar `mutualInfo_nonneg_of_subadditive`. -/
theorem mutualInfo_nonneg_of_density
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    0 ≤ mutualInfo
          (vonNeumannEntropy (partialTraceDensity_right ρ))
          (vonNeumannEntropy (partialTraceDensity_left ρ))
          (vonNeumannEntropy ρ) :=
  mutualInfo_nonneg_of_subadditive _ _ _ (weak_subadditivity ρ hρ hA hB)

/-- **The quantum mutual information equals the relative entropy
    `S(ρ_AB ‖ ρ_A ⊗ ρ_B)`** — the information-theoretic content of the
    capacity formula, now with `mutualInfo` literally identified with the
    Umegaki relative entropy. -/
theorem mutualInfo_eq_relativeEntropy
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    mutualInfo
        (vonNeumannEntropy (partialTraceDensity_right ρ))
        (vonNeumannEntropy (partialTraceDensity_left ρ))
        (vonNeumannEntropy ρ)
      = umegakiRelativeEntropy ρ
          (kroneckerDM (partialTraceDensity_right ρ)
                        (partialTraceDensity_left ρ)) := by
  unfold mutualInfo
  rw [mutualInfo_eq_umegaki ρ hA hB]

/-- **Fully assembled Araki–Lieb sandwich for a bipartite density
    matrix.**  Given a purification datum `d` whose physical-marginal
    fields are the von Neumann entropies of `ρ_AB`, `ρ_A`, `ρ_B`, the
    upper edge of the sandwich is now an honest consequence of
    `weak_subadditivity` (rather than a hypothesis); the lower edge is
    the abstract Araki–Lieb bound `arakiLieb_abs`.  The result is

        |S(ρ_A) − S(ρ_B)|  ≤  S(ρ_AB)  ≤  S(ρ_A) + S(ρ_B). -/
theorem arakiLieb_sandwich_unconditional
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef)
    (d : EntropyData)
    (hSA : d.SA = vonNeumannEntropy (partialTraceDensity_right ρ))
    (hSB : d.SB = vonNeumannEntropy (partialTraceDensity_left ρ))
    (hSAB : d.SAB = vonNeumannEntropy ρ) :
    |d.SA - d.SB| ≤ d.SAB ∧ d.SAB ≤ d.SA + d.SB :=
  d.arakiLieb_sandwich
    (entropyData_subadditivity_of_density ρ hρ hA hB d hSA hSB hSAB)

/-! ## 7.  Axiom audit. -/

#print axioms weak_subadditivity
#print axioms mutualInfo_eq_umegaki
#print axioms entropyData_subadditivity_of_density
#print axioms mutualInfo_nonneg_of_density

end UnifiedTheory.LayerB.WeakSubadditivity
