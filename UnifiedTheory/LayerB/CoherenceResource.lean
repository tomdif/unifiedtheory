/-
  LayerB/CoherenceResource.lean
  ──────────────────────────────────────────────────────────────────────

  **Resource theory of quantum coherence — the relative entropy of
  coherence (Baumgratz–Cramer–Plenio, PRL 113, 140401 (2014)).**

  Fix a reference basis.  The *dephasing* map Δ zeroes every off-diagonal
  entry of a matrix:

        Δ(ρ) i j  =  if i = j then ρ i j else 0.

  A state is *incoherent* iff it is fixed by Δ, i.e. diagonal in the
  reference basis.  The *relative entropy of coherence* is

        C(ρ)  =  S(Δ ρ) − S(ρ)  =  S(ρ ‖ Δ ρ)

  where S is the von Neumann entropy.  It is a faithful, non-negative
  resource monotone of the resource theory of coherence: incoherent
  states have C = 0, and C ≥ 0 with equality iff ρ is incoherent.

  ──────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN UNCONDITIONALLY (no `sorry`, no custom `axiom`):

    Dephasing algebra (raw matrices):
      · `dephase`                  — the off-diagonal-killing map.
      · `dephase_idempotent`       — Δ ∘ Δ = Δ.
      · `dephase_isDiag`           — Δ ρ is a diagonal matrix.
      · `dephase_diagonal_apply`   — Δ ρ agrees with ρ on the diagonal.
      · `dephase_offDiag_zero`     — Δ ρ is 0 off the diagonal.
      · `dephase_add`              — additivity (linearity, part 1).
      · `dephase_smul`             — homogeneity (linearity, part 2).
      · `dephase_trace`            — Tr(Δ ρ) = Tr ρ (trace-preserving).
      · `dephase_zero`, `dephase_one`.

    Incoherent states (= diagonal = fixed by Δ):
      · `IsIncoherent`             — predicate `Δ ρ = ρ`.
      · `isIncoherent_iff_diagonal`— Δ ρ = ρ ⟺ ρ off-diagonal entries 0.
      · `dephase_isIncoherent`     — Δ ρ is always incoherent (idempotence).
      · `diagonalDensityMatrix` is incoherent.

    Density-matrix level:
      · `diagProbVector`           — the diagonal of a density matrix is a
                                     genuine `ProbabilityVector` (PSD ⇒
                                     non-negative, trace 1 ⇒ sums to 1).
      · `dephasedDM`               — the dephased density matrix
                                     `Δ ρ := diagonalDensityMatrix (diag ρ)`.
      · `dephasedDM_M_eq_dephase`  — its underlying matrix is `dephase ρ.M`.
      · `dephasedDM_isIncoherent`  — `Δ ρ` is incoherent.
      · `coherence`                — C(ρ) = S(Δ ρ) − S(ρ).
      · `coherence_incoherent_zero`— incoherent ⇒ C(ρ) = 0.       (★ key)
      · `coherence_diagonalDensityMatrix_zero` — diagonal ⇒ C = 0.

  STATED AS NAMED TARGETS (require the deferred cfc-of-diagonal /
  Klein-faithfulness machinery the repo flags as out of scope):
      · `Coherence_Nonneg_Target`            — C ρ ≥ 0.
      · `Coherence_Zero_Iff_Incoherent_Target` — C ρ = 0 ⟺ incoherent.
      · `Coherence_Monotone_Target`          — IO-monotonicity.
      · `coherence_master`                   — the conjunction.

  The named targets are *definitions of propositions*, not axioms; the
  master theorem records that they together characterise C as a faithful
  resource monotone.  Nothing here is assumed.
-/

import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.DiagonalDensityMatrix
import UnifiedTheory.LayerB.DiagonalVonNeumannEntropy
import Mathlib.LinearAlgebra.Matrix.IsDiag

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CoherenceResource

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.DiagonalDensityMatrix

variable {n : ℕ}

/-! ## 1. The dephasing map on raw matrices -/

/-- **Dephasing.**  Zero every off-diagonal entry, keep the diagonal.
    This is the incoherent-state projector of the resource theory of
    coherence in the fixed reference basis. -/
def dephase (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then ρ i j else 0

@[simp] theorem dephase_apply (ρ : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    dephase ρ i j = if i = j then ρ i j else 0 := rfl

/-- On the diagonal, `Δ ρ` agrees with `ρ`. -/
@[simp] theorem dephase_diagonal_apply (ρ : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : dephase ρ i i = ρ i i := by simp [dephase]

/-- Off the diagonal, `Δ ρ` is zero. -/
theorem dephase_offDiag_zero (ρ : Matrix (Fin n) (Fin n) ℂ)
    {i j : Fin n} (h : i ≠ j) : dephase ρ i j = 0 := by simp [dephase, h]

/-- **`Δ ρ` is a diagonal matrix.** -/
theorem dephase_isDiag (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.IsDiag (dephase ρ) := by
  intro i j h
  exact dephase_offDiag_zero ρ h

/-- **Idempotence:** `Δ (Δ ρ) = Δ ρ`. -/
theorem dephase_idempotent (ρ : Matrix (Fin n) (Fin n) ℂ) :
    dephase (dephase ρ) = dephase ρ := by
  funext i j
  by_cases h : i = j
  · subst h; simp [dephase]
  · simp [dephase, h]

/-- **Additivity** (linearity, part 1). -/
theorem dephase_add (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    dephase (ρ + σ) = dephase ρ + dephase σ := by
  funext i j
  by_cases h : i = j <;> simp [dephase, h]

/-- **Homogeneity** (linearity, part 2). -/
theorem dephase_smul (c : ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    dephase (c • ρ) = c • dephase ρ := by
  funext i j
  by_cases h : i = j <;> simp [dephase, h]

@[simp] theorem dephase_zero :
    dephase (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  funext i j; by_cases h : i = j <;> simp [dephase, h]

@[simp] theorem dephase_one :
    dephase (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  funext i j
  by_cases h : i = j
  · subst h; simp [dephase]
  · simp [dephase, h, Matrix.one_apply_ne h]

/-- **Trace-preserving:** `Tr (Δ ρ) = Tr ρ`. -/
theorem dephase_trace (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (dephase ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, dephase_diagonal_apply]

/-- Dephasing as `Matrix.diagonal` of the diagonal entries. -/
theorem dephase_eq_diagonal (ρ : Matrix (Fin n) (Fin n) ℂ) :
    dephase ρ = Matrix.diagonal (fun i => ρ i i) := by
  funext i j
  by_cases h : i = j
  · subst h; simp [dephase, Matrix.diagonal_apply_eq]
  · simp [dephase, h]

/-! ## 2. Incoherent states -/

/-- **Incoherent** state: one fixed by the dephasing map, i.e. diagonal
    in the reference basis. -/
def IsIncoherent (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop := dephase ρ = ρ

/-- `Δ ρ = ρ` iff `ρ` has vanishing off-diagonal entries. -/
theorem isIncoherent_iff_diagonal (ρ : Matrix (Fin n) (Fin n) ℂ) :
    IsIncoherent ρ ↔ ∀ i j, i ≠ j → ρ i j = 0 := by
  constructor
  · intro h i j hij
    have heq := congrFun (congrFun h i) j
    rw [dephase_offDiag_zero ρ hij] at heq
    exact heq.symm
  · intro h
    funext i j
    by_cases hij : i = j
    · subst hij; simp [dephase]
    · simp [dephase, hij, h i j hij]

/-- A diagonal (`IsDiag`) matrix is incoherent. -/
theorem isDiag_isIncoherent {ρ : Matrix (Fin n) (Fin n) ℂ}
    (h : Matrix.IsDiag ρ) : IsIncoherent ρ :=
  (isIncoherent_iff_diagonal ρ).2 (fun _ _ hij => h hij)

/-- **`Δ ρ` is always incoherent** (idempotence). -/
theorem dephase_isIncoherent (ρ : Matrix (Fin n) (Fin n) ℂ) :
    IsIncoherent (dephase ρ) := dephase_idempotent ρ

/-! ## 3. The diagonal of a density matrix is a probability vector -/

/-- The diagonal entries of a complex density matrix are real and
    non-negative (from positive semidefiniteness) and sum to 1 (from
    trace 1); hence they form a genuine `ProbabilityVector`. -/
noncomputable def diagProbVector (ρ : ComplexDensityMatrix n) :
    ProbabilityVector (Fin n) where
  p := fun i => (ρ.M i i).re
  nonneg := by
    intro i
    have hPSD : ρ.M.PosSemidef := posSemidef_of_ComplexDensityMatrix ρ
    have h : (0 : ℂ) ≤ ρ.M i i := hPSD.diag_nonneg
    exact (Complex.nonneg_iff.mp h).1
  sum_one := by
    -- (∑ᵢ (ρ.M i i).re) = (∑ᵢ ρ.M i i).re = (Tr ρ).re = 1.
    have hsum : (∑ i, (ρ.M i i).re) = (∑ i, ρ.M i i).re :=
      (Complex.re_sum Finset.univ (fun i => ρ.M i i)).symm
    rw [hsum]
    have htr : (∑ i, ρ.M i i) = ρ.M.trace := by
      rw [Matrix.trace]; rfl
    rw [htr, ρ.hTrace]
    simp

@[simp] theorem diagProbVector_apply (ρ : ComplexDensityMatrix n) (i : Fin n) :
    (diagProbVector ρ).p i = (ρ.M i i).re := rfl

/-- Each diagonal entry of a density matrix is already real (imaginary
    part zero), so it equals the cast of its real part. -/
theorem diag_eq_ofReal (ρ : ComplexDensityMatrix n) (i : Fin n) :
    ρ.M i i = ((diagProbVector ρ).p i : ℂ) := by
  have hPSD : ρ.M.PosSemidef := posSemidef_of_ComplexDensityMatrix ρ
  have h : (0 : ℂ) ≤ ρ.M i i := hPSD.diag_nonneg
  have him : (ρ.M i i).im = 0 := ((Complex.nonneg_iff.mp h).2).symm
  apply Complex.ext
  · simp [diagProbVector]
  · simp [diagProbVector, him]

/-! ## 4. The dephased density matrix -/

/-- **The dephased density matrix** `Δ ρ`: the genuine `ComplexDensityMatrix`
    whose underlying matrix is `ρ` with off-diagonals removed.  It is
    constructed as the diagonal density matrix of `diagProbVector ρ`, so
    Hermiticity / trace / PSD come for free from `diagonalDensityMatrix`. -/
noncomputable def dephasedDM (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n :=
  diagonalDensityMatrix (diagProbVector ρ)

/-- **The underlying matrix of `dephasedDM ρ` is exactly `dephase ρ.M`.** -/
theorem dephasedDM_M_eq_dephase (ρ : ComplexDensityMatrix n) :
    (dephasedDM ρ).M = dephase ρ.M := by
  rw [dephase_eq_diagonal]
  unfold dephasedDM
  change Matrix.diagonal (fun i => ((diagProbVector ρ).p i : ℂ))
      = Matrix.diagonal (fun i => ρ.M i i)
  congr 1
  funext i
  exact (diag_eq_ofReal ρ i).symm

/-- `dephasedDM ρ` is an incoherent state. -/
theorem dephasedDM_isIncoherent (ρ : ComplexDensityMatrix n) :
    IsIncoherent (dephasedDM ρ).M := by
  rw [dephasedDM_M_eq_dephase]
  exact dephase_isIncoherent ρ.M

/-- A `diagonalDensityMatrix` is incoherent. -/
theorem diagonalDensityMatrix_isIncoherent (P : ProbabilityVector (Fin n)) :
    IsIncoherent (diagonalDensityMatrix P).M := by
  have hdiag : Matrix.IsDiag (diagonalDensityMatrix P).M := by
    change Matrix.IsDiag (Matrix.diagonal (fun i => ((P.p i : ℂ))))
    exact Matrix.isDiag_diagonal _
  exact isDiag_isIncoherent hdiag

/-! ## 5. The relative entropy of coherence -/

/-- **Relative entropy of coherence**

        C(ρ)  =  S(Δ ρ) − S(ρ).

    Here `S` is the von Neumann entropy and `Δ ρ = dephasedDM ρ` is the
    dephased density matrix (off-diagonals removed).  This is the
    Baumgratz–Cramer–Plenio coherence monotone, equal to the relative
    entropy `S(ρ ‖ Δ ρ)`. -/
noncomputable def coherence (ρ : ComplexDensityMatrix n) : ℝ :=
  vonNeumannEntropy (dephasedDM ρ) - vonNeumannEntropy ρ

/-- **The von Neumann entropy depends only on the underlying matrix.**
    Two complex density matrices with the same underlying matrix `M`
    have the same eigenvalue multiset (the Hermiticity proof is in `Prop`,
    hence irrelevant), so the same entropy. -/
theorem vonNeumannEntropy_congr {ρ σ : ComplexDensityMatrix n}
    (h : ρ.M = σ.M) : vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  -- The eigenvalue functions agree: they are `IsHermitian.eigenvalues`
  -- of equal matrices, and the Hermiticity proof is proof-irrelevant.
  have hev : ρ.hHerm.eigenvalues = σ.hHerm.eigenvalues := by
    rcases ρ with ⟨M₁, hH₁, _, _⟩
    rcases σ with ⟨M₂, hH₂, _, _⟩
    simp only at h
    subst h
    rfl
  unfold vonNeumannEntropy
  rw [hev]

/-- **Incoherent ⇒ zero coherence.**

    If `ρ` is already diagonal in the reference basis then `Δ ρ = ρ` as
    density matrices, so the two entropies coincide and `C(ρ) = 0`.  This
    is the only direction of faithfulness provable without the deferred
    cfc-of-diagonal machinery, and it is proven unconditionally here. -/
theorem coherence_incoherent_zero (ρ : ComplexDensityMatrix n)
    (h : IsIncoherent ρ.M) : coherence ρ = 0 := by
  unfold coherence
  -- It suffices to show dephasedDM ρ has the SAME underlying matrix as ρ,
  -- since vonNeumannEntropy only depends on M (through hHerm.eigenvalues).
  have hM : (dephasedDM ρ).M = ρ.M := by
    rw [dephasedDM_M_eq_dephase]; exact h
  -- vonNeumannEntropy is determined by ρ.hHerm.eigenvalues, which is
  -- determined by ρ.M.  Equal M ⇒ equal entropy.
  have hent : vonNeumannEntropy (dephasedDM ρ) = vonNeumannEntropy ρ :=
    vonNeumannEntropy_congr hM
  rw [hent, sub_self]

/-- **A diagonal density matrix has zero coherence.** -/
theorem coherence_diagonalDensityMatrix_zero (P : ProbabilityVector (Fin n)) :
    coherence (diagonalDensityMatrix P) = 0 :=
  coherence_incoherent_zero _ (diagonalDensityMatrix_isIncoherent P)

/-- **The dephased state has zero coherence** (it is incoherent). -/
theorem coherence_dephasedDM_zero (ρ : ComplexDensityMatrix n) :
    coherence (dephasedDM ρ) = 0 :=
  coherence_incoherent_zero _ (dephasedDM_isIncoherent ρ)

/-! ## 6. Named resource-theoretic targets

    These three properties together state that `C` is a *faithful,
    non-negative resource monotone* for the resource theory of coherence.
    Non-negativity and faithfulness follow from Klein's inequality
    (`KleinInequalityFull.umegakiRelativeEntropy_nonneg`) once the identity
    `C ρ = umegakiRelativeEntropy ρ (dephasedDM ρ)` is established — which
    in turn needs the cfc-of-diagonal lemma the repo flags as deferred
    (Mathlib's `IsHermitian.eigenvalues` permutes the diagonal of a
    diagonal matrix, so `log (Δ ρ)` is not definitionally diagonal).
    Monotonicity is the data-processing inequality restricted to
    incoherent operations.  We record them as named propositions, NOT as
    axioms; the `coherence_master` theorem is their conjunction. -/

/-- **Target: C ρ ≥ 0** (non-negativity; via Klein / relative entropy). -/
def Coherence_Nonneg_Target : Prop :=
  ∀ {m : ℕ} (ρ : ComplexDensityMatrix m), 0 ≤ coherence ρ

/-- **Target: C ρ = 0 ⟺ ρ incoherent** (faithfulness).
    The (⇐) direction is the proven `coherence_incoherent_zero`. -/
def Coherence_Zero_Iff_Incoherent_Target : Prop :=
  ∀ {m : ℕ} (ρ : ComplexDensityMatrix m),
    coherence ρ = 0 ↔ IsIncoherent ρ.M

/-- **Target: C is monotone under incoherent operations.**
    For any incoherent operation Φ (modelled abstractly as a map on
    density matrices that preserves incoherence), `C (Φ ρ) ≤ C ρ`. -/
def Coherence_Monotone_Target : Prop :=
  ∀ {m : ℕ} (Φ : ComplexDensityMatrix m → ComplexDensityMatrix m),
    (∀ σ, IsIncoherent σ.M → IsIncoherent (Φ σ).M) →
    ∀ ρ : ComplexDensityMatrix m, coherence (Φ ρ) ≤ coherence ρ

/-- **Master statement.**  `C` is a faithful, non-negative resource
    monotone of the resource theory of coherence.  The (⇐) half of
    faithfulness — incoherent ⇒ C = 0 — is discharged unconditionally
    inside this conjunction by `coherence_incoherent_zero`; the
    remaining halves are the three named targets above. -/
theorem coherence_master :
    (∀ {m : ℕ} (ρ : ComplexDensityMatrix m),
        IsIncoherent ρ.M → coherence ρ = 0) ∧
    (Coherence_Nonneg_Target →
     Coherence_Zero_Iff_Incoherent_Target →
     Coherence_Monotone_Target →
       (∀ {m : ℕ} (ρ : ComplexDensityMatrix m), 0 ≤ coherence ρ)
       ∧ (∀ {m : ℕ} (ρ : ComplexDensityMatrix m),
            coherence ρ = 0 ↔ IsIncoherent ρ.M)) := by
  refine ⟨fun ρ h => coherence_incoherent_zero ρ h, ?_⟩
  intro hNonneg hFaithful _hMono
  exact ⟨fun ρ => hNonneg ρ, fun ρ => hFaithful ρ⟩

end UnifiedTheory.LayerB.CoherenceResource
