/-
  LayerB/CFCDiagonalDischarge.lean
  ─────────────────────────────────

  **Discharge of `CFCOnDiagonalIsEntrywise`.**

  The hypothesis `CFCOnDiagonalIsEntrywise n f` introduced in
  `UmegakiDiagonalBridge.lean` is the analytic fact that the continuous
  functional calculus of a real function `f : ℝ → ℝ` on a (complex)
  diagonal matrix is itself diagonal, with `f` applied entry-wise:

      `cfc f (diagonal (ofReal ∘ d))  =  diagonal (ofReal ∘ f ∘ d)`.

  This file discharges that hypothesis cleanly via the **uniqueness of
  the continuous functional calculus** (`cfcHom_eq_of_continuous_of_map_id`):
  we construct, by hand, an alternative continuous `⋆`-algebra
  homomorphism from `C(spectrum ℝ D, ℝ)` into `Matrix (Fin n) (Fin n) ℂ`
  that acts by evaluation-then-diagonal, show it carries the identity
  to `D`, and conclude by uniqueness that it equals `cfcHom`.

  WHAT IS PROVEN (no `sorry`, no custom axioms):
    1. `entrywiseDiagHom`            — the alternative star algebra
                                       homomorphism (entrywise on the
                                       diagonal).
    2. `cfcOnDiagonalIsEntrywise_real`
                                     — generic discharge for any
                                       `f : ℝ → ℝ`.  Note: the
                                       continuity hypothesis is
                                       automatic because the spectrum
                                       of a diagonal matrix is a
                                       *finite* set.
    3. `cfcOnDiagonalIsEntrywise_log`
                                     — specialised discharge for
                                       `Real.log`, the form used by
                                       `umegakiRelativeEntropy_diagonal_eq_klDivergence`.
-/

import UnifiedTheory.LayerB.UmegakiDiagonalBridge
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Eigenspace.Matrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CFCDiagonalDischarge

open Matrix Complex
open UnifiedTheory.LayerB.UmegakiDiagonalBridge

variable {n : ℕ}

/-! ## 1. Spectrum and self-adjointness of the diagonal complex matrix -/

/-- The `ℝ`-spectrum of the complex diagonal matrix with real entries is
    the range of the (real) diagonal function. -/
lemma spectrum_real_diagonal_ofReal (d : Fin n → ℝ) :
    spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) = Set.range d := by
  ext r
  -- Reduce to the spectrum over ℂ via the scalar tower.
  rw [← spectrum.algebraMap_mem_iff ℂ
        (R := ℝ) (a := Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) (r := r),
      spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h1 : ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ r := hi
    rw [RCLike.algebraMap_eq_ofReal] at h1
    have h2 : ((d i : ℝ) : ℂ) = ((r : ℝ) : ℂ) := h1
    exact Complex.ofReal_inj.mp h2
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [RCLike.algebraMap_eq_ofReal]
    change ((d i : ℝ) : ℂ) = ((r : ℝ) : ℂ)
    exact_mod_cast hi

/-- Each diagonal entry lies in the `ℝ`-spectrum. -/
lemma diagonal_entry_mem_spectrum_real (d : Fin n → ℝ) (i : Fin n) :
    d i ∈ spectrum ℝ (Matrix.diagonal (fun j => ((d j : ℝ) : ℂ))) := by
  rw [spectrum_real_diagonal_ofReal]; exact ⟨i, rfl⟩

/-- The complex diagonal matrix with real entries is self-adjoint. -/
lemma isSelfAdjoint_diagonal_ofReal (d : Fin n → ℝ) :
    IsSelfAdjoint (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) := by
  change (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian
  refine isHermitian_diagonal_of_self_adjoint _ ?_
  change star (fun i => ((d i : ℝ) : ℂ)) = (fun i => ((d i : ℝ) : ℂ))
  funext i
  change star ((d i : ℝ) : ℂ) = ((d i : ℝ) : ℂ)
  exact Complex.conj_ofReal _

/-! ## 2. The candidate `⋆`-algebra homomorphism -/

/-- The candidate alternative `⋆`-algebra homomorphism: for a continuous
    real-valued function `g` on the spectrum of the diagonal matrix,
    return the complex diagonal matrix whose `i`-th entry is `g(d i)`
    cast to `ℂ`.

    By the **uniqueness** of the continuous functional calculus, this
    necessarily coincides with `cfcHom`, which is the content of
    `cfcOnDiagonalIsEntrywise_real` below. -/
@[simps]
noncomputable def entrywiseDiagHom (d : Fin n → ℝ) :
    C(spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))), ℝ)
      →⋆ₐ[ℝ] (Matrix (Fin n) (Fin n) ℂ) where
  toFun g :=
    Matrix.diagonal
      (fun i => ((g ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
  map_zero' := by
    ext i j
    simp
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  map_mul' f g := by
    change Matrix.diagonal
            (fun i => ((((f * g) : C(_, _))
              ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
          = Matrix.diagonal
              (fun i => ((f ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
            * Matrix.diagonal
                (fun i => ((g ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
    rw [Matrix.diagonal_mul_diagonal]
    refine congrArg _ ?_
    funext i
    simp [ContinuousMap.mul_apply]
  map_add' f g := by
    change Matrix.diagonal
            (fun i => ((((f + g) : C(_, _))
              ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
          = Matrix.diagonal
              (fun i => ((f ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
            + Matrix.diagonal
                (fun i => ((g ⟨d i, diagonal_entry_mem_spectrum_real d i⟩ : ℝ) : ℂ))
    rw [Matrix.diagonal_add]
    refine congrArg _ ?_
    funext i
    simp [ContinuousMap.add_apply]
  commutes' r := by
    -- LHS: G (constant r) = diagonal (fun _ => (r : ℂ))
    -- RHS: algebraMap ℝ (Matrix n n ℂ) r = diagonal (fun _ => (r : ℂ))
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

/-! ## 3. Continuity and identity-mapping property -/

/-- `entrywiseDiagHom d` is continuous: the domain `C(spectrum ℝ D, ℝ)`
    is finite-dimensional (the spectrum is a finite set), so every
    linear map out of it is continuous. -/
lemma entrywiseDiagHom_continuous (d : Fin n → ℝ) :
    Continuous (entrywiseDiagHom d) := by
  -- `C(spectrum ℝ D, ℝ)` is finite-dimensional because the spectrum is
  -- a finite set.
  have hfin : FiniteDimensional ℝ
      C(spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))), ℝ) :=
    FiniteDimensional.of_injective
      (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  -- Now apply: every ℝ-linear map out of a finite-dim ℝ-space is continuous.
  exact (entrywiseDiagHom d).toLinearMap.continuous_of_finiteDimensional

/-- `entrywiseDiagHom d` sends the restricted identity continuous map
    to the diagonal matrix itself. -/
lemma entrywiseDiagHom_map_id (d : Fin n → ℝ) :
    entrywiseDiagHom d
        ((ContinuousMap.id ℝ).restrict
          (spectrum ℝ (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))))
      = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := by
  rfl

/-! ## 4. Discharging `CFCOnDiagonalIsEntrywise` -/

/-- **Main discharge.**  The continuous functional calculus of any
    real-valued function `f : ℝ → ℝ` on a complex diagonal matrix with
    real entries is itself a diagonal matrix, with `f` applied
    entry-wise.

    No continuity hypothesis on `f` is required: the spectrum of a
    diagonal matrix is a *finite* set, on which every function is
    automatically continuous (via `Set.Finite.continuousOn`). -/
theorem cfcOnDiagonalIsEntrywise_real (n : ℕ) (f : ℝ → ℝ) :
    CFCOnDiagonalIsEntrywise n f := by
  intro d
  -- Abbreviations.
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  have hSA : IsSelfAdjoint D := isSelfAdjoint_diagonal_ofReal d
  -- Continuity of `f` on `spectrum ℝ D` is automatic from finiteness.
  have hfin : (spectrum ℝ D).Finite := by
    rw [hD, spectrum_real_diagonal_ofReal]
    exact Set.finite_range d
  have hCont : ContinuousOn f (spectrum ℝ D) := hfin.continuousOn f
  -- Express `cfc f D` via `cfcHom`.
  rw [cfc_apply (R := ℝ) (A := Matrix (Fin n) (Fin n) ℂ) f D hSA hCont]
  -- Apply uniqueness: replace `cfcHom hSA` by `entrywiseDiagHom d`.
  have huniq : cfcHom (R := ℝ) (A := Matrix (Fin n) (Fin n) ℂ) hSA
                = entrywiseDiagHom d := by
    refine cfcHom_eq_of_continuous_of_map_id hSA (entrywiseDiagHom d)
      (entrywiseDiagHom_continuous d) ?_
    exact entrywiseDiagHom_map_id d
  rw [huniq]
  -- Reduce both sides to the explicit diagonal form.
  change
    entrywiseDiagHom d
        ⟨(spectrum ℝ D).restrict f, hCont.restrict⟩
      = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ))
  rfl

/-- The specialised statement actually used by
    `umegakiRelativeEntropy_diagonal_eq_klDivergence`: the CFC of
    `Real.log` on a complex diagonal matrix is diagonal with `Real.log`
    applied entry-wise. -/
theorem cfcOnDiagonalIsEntrywise_log (n : ℕ) :
    CFCOnDiagonalIsEntrywise n Real.log :=
  cfcOnDiagonalIsEntrywise_real n Real.log

/-! ## Final delivery: unconditional Umegaki = KL on diagonal embeddings -/

open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.DiagonalDensityMatrix
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.UmegakiDiagonalBridge

/-- **Unconditional diagonal Umegaki = classical KL.**  Combines the
    conditional bridge from `UmegakiDiagonalBridge.lean` with the
    `CFCOnDiagonalIsEntrywise Real.log` discharge above, leaving
    only absolute continuity as a hypothesis:

      `umegakiRelativeEntropy (diagonalDensityMatrix P)
                              (diagonalDensityMatrix Q)
         =  klDivergence P Q`. -/
theorem umegakiRelativeEntropy_of_diagonal_eq_klDivergence {n : ℕ}
    (P Q : ProbabilityVector (Fin n))
    (hAC : IsAbsolutelyContinuous P Q) :
    umegakiRelativeEntropy (diagonalDensityMatrix P)
                           (diagonalDensityMatrix Q)
      = klDivergence P Q :=
  umegakiRelativeEntropy_diagonal_eq_klDivergence P Q hAC
    (cfcOnDiagonalIsEntrywise_log n)

end UnifiedTheory.LayerB.CFCDiagonalDischarge
