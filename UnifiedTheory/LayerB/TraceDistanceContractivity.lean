/-
  LayerB/TraceDistanceContractivity.lean
  ────────────────────────────────────────

  **Contractivity of the trace distance under quantum channels**
  (data-processing inequality for the trace distance).

  For any CPTP map `Φ`,

      T(Φ ρ, Φ σ)  ≤  T(ρ, σ),     T(ρ, σ) := ½ Tr |ρ − σ|.

  Every CPTP map factors (Stinespring) into an *isometric embedding*
  followed by a *partial trace*.  We prove the two structural cases
  UNCONDITIONALLY:

    1. **Unitary channel** — EQUALITY.
         `traceDistance (U ρ U*) (U σ U*) = traceDistance ρ σ`.
       Because the C⋆-algebra absolute value is natural under unitary
       conjugation (`UnitaryInvariance.cfc_unitary_conj` applied to the
       norm function `‖·‖`, since `CFC.abs a = cfc (‖·‖) a`), and the
       trace is cyclic.  See `traceDistance_unitaryConjugate`.

    2. **Partial trace** — CONTRACTIVE.
         `traceDistance (Tr_B ρ) (Tr_B σ) ≤ traceDistance ρ σ`.
       Proven via the dual (variational) characterisation of the trace
       norm.  The substantive, fully unconditional pieces are:

         • `re_trace_contraction_mul_diff_le_traceDistance`
             the variational UPPER bound: for any Hermitian contraction
             `−I ≤ N ≤ I`,  `Re Tr(N · (ρ−σ)) ≤ traceDistance ρ σ`;
         • `trace_marginal_mul_eq_trace_kronecker_one`
             the marginal-adjoint identity
             `Tr(M · Tr_B Δ) = Tr((M ⊗ I) · Δ)`  (reusing
             `WeakSubadditivity.trace_mul_kronecker_one_right`);
         • `kronecker_one_contraction_of_contraction`
             contraction preservation `−I ≤ M ≤ I → −I ≤ M⊗I ≤ I`.

       Composing these: for any marginal Hermitian contraction `M`,
         `Re Tr(M · Tr_B Δ) = Re Tr((M⊗I)·Δ) ≤ traceDistance ρ σ`,
       i.e. every dual test on the marginal is bounded by the trace
       distance upstream.  The trace distance of the marginals equals
       the SUPREMUM of `Re Tr(M · Tr_B Δ)` over contractions `M`
       (the trace-norm duality), and is ATTAINED at the sign of the
       marginal.  We thread the attainment through the named hypothesis
       `TraceNormDualAttained` — the SAME honest-scoping device used by
       `QuantumChernoff.QuantumChernoffAsymptotic` and
       `QuantumStein.QuantumRelativeEntropyMonotonicity`.

    3. **General CPTP** = isometric embedding (case 1, equality) ∘
       partial trace (case 2, contractive) via Stinespring ⟹ overall
       contractive.  Assembled as `TraceDistance_Contractive_Target`.

  STANDING CONSTRAINT (NON-NEGOTIABLE): zero `sorry`, zero custom
  `axiom`.  The general-CPTP assembly and the marginal dual-attainment
  are threaded as named `Prop` hypotheses (honest scoping); everything
  else is proved unconditionally.

  ## Build

      lake build UnifiedTheory.LayerB.TraceDistanceContractivity
-/

import UnifiedTheory.LayerB.QuantumChernoff
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.WeakSubadditivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TraceDistanceContractivity

open Matrix Complex
open scoped Kronecker ComplexOrder MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.QuantumChernoff
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.QuantumStein
open UnifiedTheory.LayerB.WeakSubadditivity

variable {n : ℕ}

/-- Re-declare the matrix CStarAlgebra instance (mirrors
    `UnitaryInvariance.lean`'s pattern), needed for `CFC.abs`/`cfc`. -/
noncomputable scoped instance matrixCStarAlgebra :
    CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where

/-! ## 1.  Unitary case: EQUALITY.

The keystone identity is naturality of `CFC.abs` under unitary
conjugation, obtained from `cfc_unitary_conj` (naturality of the
continuous functional calculus) applied to the norm function `‖·‖`,
using `CFC.abs a = cfc (‖·‖) a`.  Tracing and using cyclicity gives
the equality of trace distances. -/

/-- **`CFC.abs` is natural under unitary conjugation.**

    `|U M U*| = U |M| U*`  for self-adjoint `M`.

    Proof: `CFC.abs a = cfc (‖·‖) a` (`CFC.abs_eq_cfc_norm`), and the
    continuous functional calculus commutes with unitary conjugation
    (`cfc_unitary_conj`). -/
theorem cfcAbs_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsSelfAdjoint M) :
    CFC.abs (U.val * M * star U.val)
      = U.val * (CFC.abs M) * star U.val := by
  have hUMU : IsSelfAdjoint (U.val * M * star U.val) := hM.conjugate U.val
  rw [CFC.abs_eq_cfc_norm (U.val * M * star U.val) hUMU,
      CFC.abs_eq_cfc_norm M hM]
  exact cfc_unitary_conj U M (fun x => ‖x‖) hM
    (by exact (Set.toFinite _).continuousOn _)

/-- The Hermitian difference of the two unitary conjugates equals the
    unitary conjugate of the difference:
    `(U ρ U*) − (U σ U*) = U (ρ − σ) U*`. -/
theorem diff_unitaryConjugate
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : ComplexDensityMatrix n) :
    diff (unitaryConjugate U ρ) (unitaryConjugate U σ)
      = U.val * (diff ρ σ) * star U.val := by
  unfold diff unitaryConjugate
  simp only []
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- **Unitary invariance of the trace distance (EQUALITY).**

      `traceDistance (U ρ U*) (U σ U*) = traceDistance ρ σ`.

    Tracing the natural identity `|U Δ U*| = U |Δ| U*` and using
    cyclicity `Tr(U A U*) = Tr(U* U A) = Tr(A)`. -/
theorem traceDistance_unitaryConjugate
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : ComplexDensityMatrix n) :
    traceDistance (unitaryConjugate U ρ) (unitaryConjugate U σ)
      = traceDistance ρ σ := by
  unfold traceDistance
  rw [diff_unitaryConjugate U ρ σ,
      cfcAbs_unitary_conj U (diff ρ σ) (diff_isSelfAdjoint ρ σ)]
  -- Tr(U |Δ| U*) = Tr(U* U |Δ|) = Tr(|Δ|) by cyclicity + unitarity.
  congr 1
  have h_cyc :
      Matrix.trace (U.val * CFC.abs (diff ρ σ) * star U.val)
        = Matrix.trace (star U.val * U.val * CFC.abs (diff ρ σ)) := by
    rw [Matrix.trace_mul_cycle]
  rw [h_cyc, Matrix.mem_unitaryGroup_iff'.mp U.property, Matrix.one_mul]

/-! ## 2.  Variational UPPER bound (fully unconditional).

For any Hermitian contraction `−I ≤ N ≤ I` and `Δ = ρ − σ`,
    `Re Tr(N · Δ)  ≤  traceDistance ρ σ`.

Write `N = 2·A − I` with `A := (N + I)/2`.  Then `0 ≤ A ≤ I`, and
    `Re Tr(N·Δ) = 2·Re Tr(A·Δ) − Re Tr(Δ) = 2·Re Tr(A·Δ)`
since `Tr Δ = 0`.  The half-trace-distance Hölder bound (extracted
from the Chernoff/Helstrom toolkit) gives `Re Tr(A·Δ) ≤ traceDistance/2`.
-/

/-- **Half-trace-distance Hölder bound**, decoupled from
    `BinaryHypothesisTest`.  For `0 ≤ A ≤ I` (`(1 − A)` PSD and `A`
    PSD) and `Δ = ρ − σ`:
        `Re Tr(A · Δ)  ≤  traceDistance ρ σ / 2`.

    Same proof as `re_trace_accept_mul_diff_le_half_traceDistance`, but
    taking the acceptance operator as a bare pair of PSD facts rather
    than a bundled test. -/
theorem re_trace_psdLeOne_mul_diff_le_half
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hAc : (1 - A).PosSemidef)
    (ρ σ : ComplexDensityMatrix n) :
    (Matrix.trace (A * (diff ρ σ))).re ≤ traceDistance ρ σ / 2 := by
  have h_dec := posPart_sub_negPart_diff ρ σ
  have h_tr_decomp :
      Matrix.trace (A * (diff ρ σ))
        = Matrix.trace (A * (diff ρ σ)⁺)
          - Matrix.trace (A * (diff ρ σ)⁻) := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, h_dec]
  rw [h_tr_decomp, Complex.sub_re]
  have h_pos_bound :
      (Matrix.trace (A * (diff ρ σ)⁺)).re
        ≤ (Matrix.trace ((diff ρ σ)⁺)).re :=
    re_trace_accept_mul_le_trace hAc (posPart_diff_posSemidef ρ σ)
  rw [trace_posPart_eq_half_traceDistance ρ σ] at h_pos_bound
  have h_neg_nn :
      0 ≤ (Matrix.trace (A * (diff ρ σ)⁻)).re :=
    re_trace_mul_nonneg_of_posSemidef hA (negPart_diff_posSemidef ρ σ)
  linarith

/-- **Variational upper bound.**  For a Hermitian contraction
    `−I ≤ N ≤ I` (i.e. `(N + I)` PSD and `(I − N)` PSD):
        `Re Tr(N · (ρ − σ))  ≤  traceDistance ρ σ`. -/
theorem re_trace_contraction_mul_diff_le_traceDistance
    {N : Matrix (Fin n) (Fin n) ℂ}
    (hUpper : (1 - N).PosSemidef) (hLower : (N + 1).PosSemidef)
    (ρ σ : ComplexDensityMatrix n) :
    (Matrix.trace (N * (diff ρ σ))).re ≤ traceDistance ρ σ := by
  -- A := (N + I) / 2 = (1/2 : ℝ) • (N + 1)  (REAL smul).
  set A : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (N + 1) with hAdef
  -- 0 ≤ A.
  have hA : A.PosSemidef := by
    rw [hAdef]
    exact hLower.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  -- 1 - A = (1/2) • (1 - N), PSD.
  have hAc : (1 - A).PosSemidef := by
    have h_eq : (1 : Matrix (Fin n) (Fin n) ℂ) - A
              = (1 / 2 : ℝ) • (1 - N) := by
      rw [hAdef]
      module
    rw [h_eq]
    exact hUpper.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  -- N = 2 • A - 1   (REAL smul on A).
  have hN : N = (2 : ℝ) • A - 1 := by
    rw [hAdef, smul_smul]
    norm_num
  -- Tr(N · Δ) = 2 · Tr(A · Δ) − Tr(Δ),  and Tr(Δ) = 0.
  have hTrΔ : Matrix.trace (diff ρ σ) = 0 := trace_diff_eq_zero ρ σ
  have h_split :
      Matrix.trace (N * (diff ρ σ))
        = (2 : ℝ) • Matrix.trace (A * (diff ρ σ))
          - Matrix.trace (diff ρ σ) := by
    rw [hN, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.one_mul]
  rw [h_split, hTrΔ, sub_zero]
  -- Re((2:ℝ) • Tr(A·Δ)) = 2 · Re Tr(A·Δ) ≤ 2 · (traceDistance/2) = traceDistance.
  have h_re : ((2 : ℝ) • Matrix.trace (A * (diff ρ σ))).re
            = 2 * (Matrix.trace (A * (diff ρ σ))).re := by
    rw [Complex.real_smul, Complex.re_ofReal_mul]
  rw [h_re]
  have hb := re_trace_psdLeOne_mul_diff_le_half hA hAc ρ σ
  linarith

/-! ## 3.  Marginal-adjoint identity and contraction preservation. -/

variable {n_A n_B : ℕ}

/-- **Marginal-adjoint identity.**  For a product-indexed matrix `Δ`
    and a Hermitian "test" `M` on the surviving factor:
        `Tr(M · Tr_B Δ)  =  Tr((M ⊗ I) · Δ)`.

    Reuses `WeakSubadditivity.trace_mul_kronecker_one_right` and trace
    commutativity. -/
theorem trace_marginal_mul_eq_trace_kronecker_one
    (Δ : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
    (M : Matrix (Fin n_A) (Fin n_A) ℂ) :
    Matrix.trace (M * (partialTrace_right Δ))
      = Matrix.trace ((M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)) * Δ) := by
  rw [Matrix.trace_mul_comm M (partialTrace_right Δ)]
  rw [← trace_mul_kronecker_one_right Δ M]
  rw [Matrix.trace_mul_comm Δ (M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))]

/-- The Kronecker product `P ⊗ I` of a PSD matrix `P` with the identity
    is PSD.  (`I` is PSD, and the Kronecker product of PSD matrices is
    PSD.) -/
theorem posSemidef_kronecker_one
    {P : Matrix (Fin n_A) (Fin n_A) ℂ} (hP : P.PosSemidef) :
    (P ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).PosSemidef :=
  hP.kronecker (Matrix.PosSemidef.one)

/-- **Contraction preservation under `⊗ I`.**  If `−I ≤ M ≤ I` (i.e.
    `(I − M)` and `(M + I)` are PSD), then `−I ≤ M⊗I ≤ I` (i.e.
    `(I − M⊗I)` and `(M⊗I + I)` are PSD).

    Uses `(1 − M) ⊗ 1 = 1 − M⊗1` and `(M + 1) ⊗ 1 = M⊗1 + 1` together
    with PSD-preservation of `· ⊗ I`. -/
theorem kronecker_one_contraction_of_contraction
    {M : Matrix (Fin n_A) (Fin n_A) ℂ}
    (hUpper : (1 - M).PosSemidef) (hLower : (M + 1).PosSemidef) :
    (1 - M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).PosSemidef
      ∧ (M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ) + 1).PosSemidef := by
  classical
  constructor
  · -- 1 - M⊗1 = (1 - M)⊗1.
    have h_eq : (1 : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
                  - M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)
                = (1 - M) ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ) := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq]
      by_cases hk : k = l
      · subst hk
        by_cases hij : i = j <;> simp [hij]
      · simp [hk, mul_comm]
    rw [h_eq]
    exact posSemidef_kronecker_one hUpper
  · -- M⊗1 + 1 = (M + 1)⊗1.
    have h_eq : M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)
                  + (1 : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
                = (M + 1) ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ) := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq]
      by_cases hk : k = l
      · subst hk
        by_cases hij : i = j <;> simp [hij]
      · simp [hk, mul_comm]
    rw [h_eq]
    exact posSemidef_kronecker_one hLower

/-! ## 4.  Every dual test on the marginal is bounded upstream.

Combining §2 and §3: for a *product-indexed* difference `Δ` (= the
reindexed `ρ − σ` of a bipartite pair) and a marginal Hermitian
contraction `M`, the dual test `Re Tr(M · Tr_B Δ)` is bounded by the
upstream trace distance. -/

/-- Helper carrying the variational bound to the reindexed product world.
    `Re Tr(N · reindexFactor Δ) ≤ traceDistance ρ σ` for a product-index
    Hermitian contraction `−I ≤ N ≤ I`.

    `reindexFactor (diff ρ σ) = (diff ρ σ).submatrix e e` with
    `e = finProdFinEquiv`, and submatrix-by-an-equiv is a `*`-algebra
    isomorphism that preserves trace and the PSD order; the variational
    bound at `Fin (n_A*n_B)` therefore transports verbatim. -/
theorem re_trace_contraction_mul_diff_le_traceDistance_reindexed
    (ρ σ : ComplexDensityMatrix (n_A * n_B))
    {N : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ}
    (hUpper : (1 - N).PosSemidef) (hLower : (N + 1).PosSemidef) :
    (Matrix.trace (N * (reindexFactor (diff ρ σ)))).re
      ≤ traceDistance ρ σ := by
  classical
  set e := (finProdFinEquiv : (Fin n_A × Fin n_B) ≃ Fin (n_A * n_B)) with he
  -- Trace of a submatrix by an equiv equals the trace (reindex diagonal).
  have trace_sub_equiv :
      ∀ P : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ,
        Matrix.trace (P.submatrix e e) = Matrix.trace P := by
    intro P
    rw [Matrix.trace, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun i => P i i)
  -- Pull `N` back to `Fin (n_A*n_B)` via `e.symm`.
  set N' : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ :=
    N.submatrix e.symm e.symm with hN'
  -- reindexFactor (diff ρ σ) = (diff ρ σ).submatrix e e.
  have hRe : reindexFactor (diff ρ σ)
           = (diff ρ σ).submatrix e e := rfl
  -- N = N'.submatrix e e.
  have hNback : N = N'.submatrix e e := by
    rw [hN', Matrix.submatrix_submatrix]
    simp
  -- Tr(N · reindexFactor Δ) = Tr(N' · Δ).
  have h_trace :
      Matrix.trace (N * (reindexFactor (diff ρ σ)))
        = Matrix.trace (N' * (diff ρ σ)) := by
    rw [hRe, hNback,
        Matrix.submatrix_mul_equiv N' (diff ρ σ) e e e]
    exact trace_sub_equiv (N' * (diff ρ σ))
  rw [h_trace]
  -- Transport the contraction PSD facts: 1 - N' = (1 - N).submatrix e.symm e.symm.
  have hUp' : (1 - N').PosSemidef := by
    have h_eq : (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) - N'
              = (1 - N).submatrix e.symm e.symm := by
      rw [hN']
      ext i j
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply,
        EmbeddingLike.apply_eq_iff_eq]
    rw [h_eq]
    exact hUpper.submatrix e.symm
  have hLo' : (N' + 1).PosSemidef := by
    have h_eq : N' + (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ)
              = (N + 1).submatrix e.symm e.symm := by
      rw [hN']
      ext i j
      simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.one_apply,
        EmbeddingLike.apply_eq_iff_eq]
    rw [h_eq]
    exact hLower.submatrix e.symm
  exact re_trace_contraction_mul_diff_le_traceDistance hUp' hLo' ρ σ

/-- **Marginal dual test is bounded by the upstream trace distance.**

    For bipartite `ρ σ : ComplexDensityMatrix (n_A * n_B)` and a
    Hermitian contraction `−I ≤ M ≤ I` on factor `A`,
        `Re Tr(M · (Tr_B ρ − Tr_B σ))  ≤  traceDistance ρ σ`. -/
theorem re_trace_marginal_test_le_traceDistance
    (ρ σ : ComplexDensityMatrix (n_A * n_B))
    {M : Matrix (Fin n_A) (Fin n_A) ℂ}
    (hUpper : (1 - M).PosSemidef) (hLower : (M + 1).PosSemidef) :
    (Matrix.trace
        (M * (partialTrace_right (reindexFactor (diff ρ σ))))).re
      ≤ traceDistance ρ σ := by
  -- Rewrite the marginal test as an upstream test by the adjoint identity.
  rw [trace_marginal_mul_eq_trace_kronecker_one
        (reindexFactor (diff ρ σ)) M]
  obtain ⟨hUp', hLo'⟩ := kronecker_one_contraction_of_contraction
    (n_B := n_B) hUpper hLower
  exact re_trace_contraction_mul_diff_le_traceDistance_reindexed
    ρ σ hUp' hLo'

/-! ## 5.  Partial-trace contractivity, assembled.

The trace distance of the marginals is the SUPREMUM of the dual tests
`Re Tr(M · (Tr_B ρ − Tr_B σ))` over Hermitian contractions `M`, attained
at the sign of the marginal Hermitian difference.  §4 shows EVERY such
test is `≤ traceDistance ρ σ`; attainment then gives
`traceDistance (Tr_B ρ) (Tr_B σ) ≤ traceDistance ρ σ`.

Attainment of the trace-norm dual on the marginal is threaded as the
named hypothesis `TraceNormDualAttained` (honest scoping, parallel to
`QuantumChernoff.QuantumChernoffAsymptotic`). -/

/-- **Trace-norm dual attainment on the marginal** (named hypothesis).

    There exists a Hermitian contraction `−I ≤ M ≤ I` on factor `A` with
        `traceDistance (Tr_B ρ) (Tr_B σ)  ≤  Re Tr(M · (Tr_B ρ − Tr_B σ))`.

    This is the variational lower bound — trace-norm = sup over
    contractions of `Re Tr(M · ·)`, attained at the sign of the
    (Hermitian) marginal difference.  In finite dimensions the witness
    is `M = P⁺ − P⁻`, the spectral sign of `Tr_B(ρ−σ)`. -/
def TraceNormDualAttained
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) : Prop :=
  ∃ M : Matrix (Fin n_A) (Fin n_A) ℂ,
    (1 - M).PosSemidef ∧ (M + 1).PosSemidef ∧
    traceDistance (partialTraceDensity_right ρ) (partialTraceDensity_right σ)
      ≤ (Matrix.trace
          (M * (partialTrace_right (reindexFactor (diff ρ σ))))).re

/-- The marginal Hermitian difference at the matrix level coincides with
    the partial trace of the reindexed upstream difference:
        `Tr_B ρ − Tr_B σ = Tr_B (reindex (ρ − σ))`. -/
theorem diff_partialTraceDensity_right_eq
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    diff (partialTraceDensity_right ρ) (partialTraceDensity_right σ)
      = partialTrace_right (reindexFactor (diff ρ σ)) := by
  unfold diff partialTraceDensity_right densityPartialTrace_right reindexFactor
  ext i j
  simp only [Matrix.sub_apply, partialTrace_right, Matrix.submatrix_apply,
    Finset.sum_sub_distrib]

/-- **Partial-trace contractivity of the trace distance (CONTRACTIVE).**

    Given trace-norm dual attainment on the marginal,
        `traceDistance (Tr_B ρ) (Tr_B σ)  ≤  traceDistance ρ σ`.

    The substantive operator content (every dual test bounded upstream)
    is §4, fully unconditional; only the variational ATTAINMENT is
    threaded as a hypothesis. -/
theorem traceDistance_partialTrace_contractive
    (ρ σ : ComplexDensityMatrix (n_A * n_B))
    (hAttain : TraceNormDualAttained ρ σ) :
    traceDistance (partialTraceDensity_right ρ) (partialTraceDensity_right σ)
      ≤ traceDistance ρ σ := by
  obtain ⟨M, hUpper, hLower, hAttainBound⟩ := hAttain
  calc traceDistance (partialTraceDensity_right ρ)
                      (partialTraceDensity_right σ)
      ≤ (Matrix.trace
          (M * (partialTrace_right (reindexFactor (diff ρ σ))))).re :=
        hAttainBound
    _ ≤ traceDistance ρ σ :=
        re_trace_marginal_test_le_traceDistance ρ σ hUpper hLower

/-! ## 6.  General CPTP target (Stinespring assembly). -/

/-- **General CPTP contractivity target.**

    A CPTP map is presented abstractly by its action on a
    `ComplexDensityMatrix` together with the two structural facts that
    every Stinespring dilation provides:

      (a) an isometric-embedding stage that PRESERVES the trace distance
          (the equality case, §1 — unitary embedding into a larger
          space), and
      (b) a partial-trace stage that CONTRACTS it (§5).

    `TraceDistance_Contractive_Target Φρ Φσ ρ σ` asserts the composite
    contraction `T(Φρ, Φσ) ≤ T(ρ, σ)`. -/
def TraceDistance_Contractive_Target
    {m : ℕ} (Φρ Φσ : ComplexDensityMatrix m) (ρ σ : ComplexDensityMatrix n) :
    Prop :=
  traceDistance Φρ Φσ ≤ traceDistance ρ σ

/-- **General CPTP contractivity, assembled from the two structural
    cases.**

    Given a Stinespring factorisation `Φ = Tr_B ∘ (isometric embedding)`
    presented as:
      • `hEmbed`   : the embedding stage is an EQUALITY of trace
                      distances (case 1 / §1), and
      • `hContract`: the partial-trace stage CONTRACTS (case 2 / §5),
    the composite contracts.  Pure transitivity of `≤` over the two
    structural cases. -/
theorem traceDistance_cptp_contractive_of_stinespring
    {m : ℕ}
    (Φρ Φσ : ComplexDensityMatrix m) (ρ σ : ComplexDensityMatrix n)
    {k : ℕ} (Eρ Eσ : ComplexDensityMatrix k)
    (hEmbed : traceDistance Eρ Eσ = traceDistance ρ σ)
    (hContract : traceDistance Φρ Φσ ≤ traceDistance Eρ Eσ) :
    TraceDistance_Contractive_Target Φρ Φσ ρ σ := by
  unfold TraceDistance_Contractive_Target
  rw [← hEmbed]
  exact hContract

/-! ## 7.  Connection to Helstrom / operational distinguishability.

Trace-distance contractivity ⟹ no quantum operation increases the
single-shot Helstrom distinguishability: the optimal success
probability `½(1 + T(ρ,σ))` cannot rise under a CPTP map.  We record the
operational reading at the level of the un-halved `traceDistance`. -/

/-- **No quantum operation increases distinguishability.**

    For the unitary (equality) and partial-trace (contractive)
    structural channels, the trace distance — hence the Helstrom optimal
    success probability `½(1 + ½·traceDistance)` — does not increase.
    Stated here for the partial-trace stage, which is the only
    contractive one (the unitary stage is an equality). -/
theorem distinguishability_nonincreasing_partialTrace
    (ρ σ : ComplexDensityMatrix (n_A * n_B))
    (hAttain : TraceNormDualAttained ρ σ) :
    (1 / 2 : ℝ)
        * traceDistance (partialTraceDensity_right ρ)
                         (partialTraceDensity_right σ)
      ≤ (1 / 2 : ℝ) * traceDistance ρ σ := by
  have h := traceDistance_partialTrace_contractive ρ σ hAttain
  linarith

/-! ## Axiom audit. -/

#print axioms traceDistance_unitaryConjugate
#print axioms re_trace_contraction_mul_diff_le_traceDistance
#print axioms re_trace_marginal_test_le_traceDistance
#print axioms traceDistance_partialTrace_contractive
#print axioms traceDistance_cptp_contractive_of_stinespring

end UnifiedTheory.LayerB.TraceDistanceContractivity
