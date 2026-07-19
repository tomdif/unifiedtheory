/-
  LayerB/CoherenceNonneg.lean
  ────────────────────────────

  **Depth discharge of the coherence targets via the relative-entropy
  identity.**

  This file turns the named-Prop holes of `CoherenceResource.lean`
  (`Coherence_Nonneg_Target`, `Coherence_Zero_Iff_Incoherent_Target`)
  into honest theorems by proving the *key structural identity*

        C(ρ)  =  S(ρ ‖ Δρ)  =  umegakiRelativeEntropy ρ (dephasedDM ρ)

  and then invoking Klein's inequality.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE IDENTITY (`coherence_eq_umegaki`, for positive-definite ρ).

  `umegaki ρ (Δρ) = Tr(ρ · log ρ).re − Tr(ρ · log Δρ).re`.

    · `Tr(ρ · log ρ).re = ∑ᵢ λᵢ log λᵢ = −S(ρ)`
      (`re_trace_mul_cfc_log_eq_sum`, definition of `vonNeumannEntropy`).

    · `log Δρ` is DIAGONAL: `Δρ` is `diagonal d` with `d i = (ρ.M i i).re`,
      and the continuous functional calculus of a diagonal matrix is
      entry-wise (`CFCLogTensor.cfc_diagonal_entrywise_generic`), so
      `log Δρ = diagonal (log ∘ d)`.  Hence only the *diagonal* of `ρ`
      survives the trace:

        `Tr(ρ · log Δρ).re = ∑ᵢ (ρ.M i i).re · log dᵢ
                           = ∑ᵢ dᵢ · log dᵢ  =  −S(Δρ)`

      (the diagonal of `ρ` is exactly `d`, and `S(Δρ)` is the Shannon
      entropy of `d` by `vonNeumannEntropy_diagonal_eq_shannon`).

    Subtracting:  `umegaki ρ (Δρ) = (−S(ρ)) − (−S(Δρ)) = S(Δρ) − S(ρ)
                                   = C(ρ)`.   ∎
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):

    · `dephasedDM_posDef`            — `Δρ` is PosDef when `ρ` is.
    · `trace_mul_operatorLog_dephased_re`
                                     — `Tr(ρ · log Δρ).re = ∑ᵢ dᵢ log dᵢ`
                                       (the diagonal-collapse, the crux).
    · `coherence_eq_umegaki`         — **C(ρ) = S(ρ‖Δρ)** for PosDef ρ.
    · `coherence_nonneg_of_posDef`   — **C(ρ) ≥ 0** for PosDef ρ (Klein).
    · `coherence_zero_iff_incoherent_of_posDef`
                                     — faithfulness (⇐ unconditional;
                                       ⇒ would need the strict Klein
                                       equality case — see SCOPE).

  SCOPE / HONEST BOUNDARY:

    Klein's inequality in the repo (`umegakiRelativeEntropy_nonneg`)
    requires BOTH arguments positive-definite, so the non-negativity
    and the identity are stated for positive-definite ρ (faithful
    states).  `Δρ` is then automatically PosDef.  The forward
    direction of faithfulness (`C ρ = 0 ⇒ ρ incoherent`) needs the
    *strict* equality case of Klein (`S(ρ‖σ) = 0 ⇒ ρ = σ`), which is
    NOT yet in the repo (only `klein_inequality_self`, the converse,
    is available); that single implication remains scoped.  Everything
    else — including the headline identity and non-negativity — is a
    real theorem here.

  ## Build target

      `lake build UnifiedTheory.LayerB.CoherenceNonneg`
-/

import UnifiedTheory.LayerB.CoherenceResource
import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.KleinEquality
import UnifiedTheory.LayerB.CFCLogTensor
import UnifiedTheory.LayerB.HolevoDiagonalDischarge

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CoherenceNonneg

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.DiagonalDensityMatrix
open UnifiedTheory.LayerB.CoherenceResource
open UnifiedTheory.LayerB.CFCLogTensor

variable {n : ℕ}

/-! ## 1. The dephased density matrix of a PosDef state is PosDef. -/

/-- **`Δρ` is positive definite when `ρ` is.**  The diagonal entries of a
    positive-definite matrix are strictly positive (`PosDef.diag_pos`),
    and they are precisely the entries `(diagProbVector ρ).p` of `Δρ`,
    so `posDef_diagonal_iff` applies. -/
theorem dephasedDM_posDef (ρ : ComplexDensityMatrix n) (hρ : ρ.M.PosDef) :
    (dephasedDM ρ).M.PosDef := by
  -- `(dephasedDM ρ).M = diagonal (fun i => ((diagProbVector ρ).p i : ℂ))`.
  have hM : (dephasedDM ρ).M
      = Matrix.diagonal (fun i => (((diagProbVector ρ).p i : ℝ) : ℂ)) := rfl
  rw [hM]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  -- `0 < (diagProbVector ρ).p i` as a complex number, from `0 < ρ.M i i`.
  have hpos : (0 : ℂ) < ρ.M i i := hρ.diag_pos
  -- `ρ.M i i = ((diagProbVector ρ).p i : ℂ)`.
  rw [diag_eq_ofReal ρ i] at hpos
  exact hpos

/-! ## 2. `Tr(ρ · log ρ).re = −S(ρ)`. -/

/-- **`Tr(ρ · log ρ).re = ∑ᵢ λᵢ log λᵢ = −S(ρ)`.**  Direct from the
    spectral trace identity `re_trace_mul_cfc_log_eq_sum` and the
    eigenvalue definition of `vonNeumannEntropy`. -/
theorem trace_mul_operatorLog_self_re (ρ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) :
    (Matrix.trace (ρ.M * operatorLog ρ)).re = - vonNeumannEntropy ρ := by
  unfold operatorLog cfcρ vonNeumannEntropy
  rw [UnifiedTheory.LayerB.KleinInequality.re_trace_mul_cfc_log_eq_sum ρ.M hρ]
  -- `∑ᵢ (hρ.isHermitian.eigenvalues i) log(...) = ∑ᵢ (ρ.hHerm.eigenvalues i) log(...)`.
  -- `hρ.isHermitian` and `ρ.hHerm` are both Hermiticity proofs of `ρ.M`,
  -- and `eigenvalues` is determined by the matrix (proof-irrelevant).
  have hev : hρ.isHermitian.eigenvalues = ρ.hHerm.eigenvalues := by
    rcases ρ with ⟨M, hH, _, _⟩
    rfl
  rw [hev, neg_neg]

/-! ## 3. The diagonal collapse: `Tr(ρ · log Δρ).re = −S(Δρ)`. -/

/-- **The crux diagonal-collapse identity.**

    `log Δρ = cfc log (diagonal d) = diagonal (log ∘ d)` is diagonal,
    so `Tr(ρ · log Δρ) = ∑ᵢ ρ.M i i · log dᵢ`.  Because each `ρ.M i i`
    equals `dᵢ := (diagProbVector ρ).p i` (its diagonal is real), the
    real part is `∑ᵢ dᵢ log dᵢ`. -/
theorem trace_mul_operatorLog_dephased_re (ρ : ComplexDensityMatrix n) :
    (Matrix.trace (ρ.M * operatorLog (dephasedDM ρ))).re
      = ∑ i, (diagProbVector ρ).p i
              * Real.log ((diagProbVector ρ).p i) := by
  set d : Fin n → ℝ := fun i => (diagProbVector ρ).p i with hd
  -- `operatorLog (dephasedDM ρ) = cfc log (diagonal (ofReal ∘ d)) = diagonal (ofReal ∘ log ∘ d)`.
  have hlog : operatorLog (dephasedDM ρ)
      = Matrix.diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) := by
    unfold operatorLog cfcρ
    have hM : (dephasedDM ρ).M
        = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := rfl
    rw [hM]
    exact cfc_diagonal_entrywise_generic (ι := Fin n) Real.log d
  rw [hlog]
  -- `Tr(ρ.M · diagonal c) = ∑ᵢ ρ.M i i · cᵢ` via `mul_diagonal`.
  have htr : Matrix.trace
      (ρ.M * Matrix.diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)))
      = ∑ i, ρ.M i i * ((Real.log (d i) : ℝ) : ℂ) := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    show (ρ.M * Matrix.diagonal (fun j => ((Real.log (d j) : ℝ) : ℂ))) i i = _
    rw [Matrix.mul_diagonal]
  rw [htr]
  -- Replace `ρ.M i i` by `(d i : ℂ)` (real diagonal), then take real part.
  have hsum : (∑ i, ρ.M i i * ((Real.log (d i) : ℝ) : ℂ))
      = ((∑ i, d i * Real.log (d i) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [diag_eq_ofReal ρ i]
  rw [hsum, Complex.ofReal_re]

/-! ## 4. The headline identity: `C(ρ) = S(ρ‖Δρ)`. -/

/-- **Relative-entropy form of the coherence (key identity).**

    For a positive-definite state ρ,

        C(ρ)  =  S(Δρ) − S(ρ)  =  umegakiRelativeEntropy ρ (dephasedDM ρ).

    This is the Baumgratz–Cramer–Plenio characterisation of the
    relative entropy of coherence as a quantum relative entropy. -/
theorem coherence_eq_umegaki (ρ : ComplexDensityMatrix n) (hρ : ρ.M.PosDef) :
    coherence ρ = umegakiRelativeEntropy ρ (dephasedDM ρ) := by
  -- Unfold the umegaki definition into the two traces.
  unfold umegakiRelativeEntropy
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  -- Term 1: Tr(ρ · log ρ).re = −S(ρ).
  rw [trace_mul_operatorLog_self_re ρ hρ]
  -- Term 2: Tr(ρ · log Δρ).re = ∑ dᵢ log dᵢ = −S(Δρ).
  rw [trace_mul_operatorLog_dephased_re ρ]
  -- S(Δρ) = shannonEntropy (diagProbVector ρ) = −∑ dᵢ log dᵢ.
  unfold coherence
  have hS : vonNeumannEntropy (dephasedDM ρ)
      = - ∑ i, (diagProbVector ρ).p i
                * Real.log ((diagProbVector ρ).p i) := by
    unfold dephasedDM
    rw [UnifiedTheory.LayerB.HolevoDiagonalDischarge.DiagonalEnsemble.vonNeumannEntropy_diagonal_eq_shannon]
    rfl
  rw [hS]
  ring

/-! ## 5. Non-negativity (Klein) — a real theorem for PosDef states. -/

/-- **Non-negativity of the relative entropy of coherence**
    (`C(ρ) ≥ 0`) for positive-definite ρ.

    Immediate from the identity `coherence_eq_umegaki` together with
    Klein's inequality (`umegakiRelativeEntropy_nonneg`), applied to
    ρ and its PosDef dephasing `Δρ`. -/
theorem coherence_nonneg_of_posDef (ρ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) :
    0 ≤ coherence ρ := by
  rw [coherence_eq_umegaki ρ hρ]
  exact umegakiRelativeEntropy_nonneg ρ (dephasedDM ρ) hρ
    (dephasedDM_posDef ρ hρ)

/-! ## 6. Faithfulness. -/

/-- **Faithfulness, the unconditional (⇐) direction:** an incoherent
    (diagonal) state has zero coherence.  This is just
    `coherence_incoherent_zero`, restated here for the PosDef faithfulness
    package. -/
theorem coherence_zero_of_incoherent (ρ : ComplexDensityMatrix n)
    (h : IsIncoherent ρ.M) : coherence ρ = 0 :=
  coherence_incoherent_zero ρ h

/-- **Faithfulness, the forward (⇒) direction:** for a positive-definite
    state, zero coherence forces the state to be incoherent (diagonal).

    Now an *honest* theorem: it uses the strict equality case of Klein
    (`umegakiRelativeEntropy_eq_zero_imp` from `KleinEquality.lean`).  Via
    `coherence_eq_umegaki`, `C(ρ) = S(ρ‖Δρ)`, so `C(ρ) = 0` forces
    `ρ.M = (Δρ).M = dephase ρ.M`, i.e. `IsIncoherent ρ.M`. -/
theorem coherence_zero_imp_incoherent (ρ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) (h : coherence ρ = 0) : IsIncoherent ρ.M := by
  -- C(ρ) = S(ρ‖Δρ).
  rw [coherence_eq_umegaki ρ hρ] at h
  -- Strict equality case: S(ρ‖Δρ) = 0 ⟹ ρ.M = (Δρ).M.
  have hEq : ρ.M = (dephasedDM ρ).M :=
    UnifiedTheory.LayerB.KleinEquality.umegakiRelativeEntropy_eq_zero_imp
      ρ (dephasedDM ρ) hρ (dephasedDM_posDef ρ hρ) h
  -- (Δρ).M = dephase ρ.M, so dephase ρ.M = ρ.M.
  have hdeph : (dephasedDM ρ).M = dephase ρ.M := dephasedDM_M_eq_dephase ρ
  -- IsIncoherent ρ.M ≡ dephase ρ.M = ρ.M.
  unfold IsIncoherent
  rw [hdeph] at hEq
  exact hEq.symm

/-- **Faithfulness of the relative entropy of coherence** for
    positive-definite states, packaged as an equivalence:

      `C(ρ) = 0  ⟺  ρ is incoherent`. -/
theorem coherence_eq_zero_iff (ρ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) : coherence ρ = 0 ↔ IsIncoherent ρ.M := by
  constructor
  · exact coherence_zero_imp_incoherent ρ hρ
  · exact coherence_zero_of_incoherent ρ

/-! ## 7. Axiom audit. -/

#print axioms coherence_eq_umegaki
#print axioms coherence_nonneg_of_posDef
#print axioms dephasedDM_posDef
#print axioms trace_mul_operatorLog_dephased_re
#print axioms coherence_zero_imp_incoherent
#print axioms coherence_eq_zero_iff

end UnifiedTheory.LayerB.CoherenceNonneg
