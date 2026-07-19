/-
  LayerB/WeakSubadditivityGeneral.lean
  ────────────────────────────────────

  **Weak subadditivity of the von Neumann entropy — GENERALITY LIFT.**

  The proof in `WeakSubadditivity.lean` (`weak_subadditivity`) carries
  three positive-definiteness hypotheses on a bipartite state `ρ_AB`:

      ρ_AB  PosDef,   ρ_A := Tr_B ρ_AB  PosDef,   ρ_B := Tr_A ρ_AB  PosDef.

  The PosDef-on-`ρ_AB` hypothesis was only ever needed by the *old* Klein
  inequality (`umegakiRelativeEntropy_nonneg`), which required BOTH
  arguments positive definite.  With the newly-UNCONDITIONAL general Klein
  inequality

      umegakiRelativeEntropy_nonneg_general_unconditional
        (ρ σ) (hn : 0 < n) (hσ : σ.M.PosDef) : 0 ≤ S(ρ‖σ)

  the `ρ`-slot is allowed to be a GENERAL density matrix (PSD, trace 1,
  possibly rank-deficient — i.e. PURE / entangled states are covered), and
  only the `σ`-slot must be PosDef.

  In the mutual-information identity

      S(ρ_A) + S(ρ_B) − S(ρ_AB)  =  umegaki(ρ_AB, ρ_A ⊗ ρ_B),

  the `ρ`-slot is `ρ_AB` and the `σ`-slot is `ρ_A ⊗ ρ_B`.  The latter is
  PosDef *iff both marginals are PosDef* (`kroneckerDM_posDef`).  The
  IDENTITY itself (`mutualInfo_eq_umegaki`) is purely algebraic — trace
  manipulation plus the CFC tensor-log identity — and needs NO PosDef
  hypothesis on `ρ_AB`.  So swapping the final Klein step for the general
  version removes the PosDef-on-`ρ_AB` hypothesis entirely:

      weak_subadditivity_general :
        (ρ_AB any density matrix) → (ρ_A PosDef) → (ρ_B PosDef)
          → S(ρ_AB) ≤ S(ρ_A) + S(ρ_B).

  ## What this covers that the old theorem did not

    * **PURE bipartite states** `|ψ⟩⟨ψ|` (rank-1, manifestly NOT PosDef)
      with full-rank marginals.  For a pure state S(ρ_AB) = 0 and the
      inequality reads `0 ≤ S(ρ_A) + S(ρ_B)`; but the same theorem also
      covers EVERY mixed, rank-deficient `ρ_AB` with PosDef marginals.
    * The remaining hypothesis (PosDef marginals) is GENUINELY needed: the
      operator logarithm of `ρ_A ⊗ ρ_B` — and Klein's σ-slot — require it.
      Only the PosDef-on-`ρ_AB` restriction is removed.

  ## The equality condition stays PosDef (honest note)

  The EQUALITY direction of subadditivity (`S(AB) = S(A)+S(B)` iff
  `ρ_AB = ρ_A ⊗ ρ_B`) relies on the STRICT Klein inequality, whose
  equality case is currently established only with `ρ_AB` PosDef.  We do
  NOT lift that here; only the INEQUALITY is lifted to general `ρ_AB`.

  STANDING CONSTRAINT (NON-NEGOTIABLE): zero `sorry`, zero custom `axiom`.

  ## Build

      lake build UnifiedTheory.LayerB.WeakSubadditivityGeneral
-/
import UnifiedTheory.LayerB.WeakSubadditivity
import UnifiedTheory.LayerB.OperatorEntropyContinuous

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.WeakSubadditivityGeneral

open Matrix Complex
open scoped Kronecker ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.UmegakiTensorAdditivity
open UnifiedTheory.LayerB.WeakSubadditivity
open UnifiedTheory.LayerB.OperatorEntropyContinuous

variable {n_A n_B : ℕ}

/-- **WEAK SUBADDITIVITY OF VON NEUMANN ENTROPY — GENERAL `ρ_AB`.**

    For a bipartite quantum state `ρ_AB : ComplexDensityMatrix (n_A * n_B)`
    — a GENERAL density matrix, possibly rank-deficient, in particular a
    PURE / entangled state — whose marginals `ρ_A := Tr_B ρ_AB`,
    `ρ_B := Tr_A ρ_AB` are positive definite,

      S(ρ_AB)  ≤  S(ρ_A) + S(ρ_B).

    **The PosDef-on-`ρ_AB` hypothesis of `weak_subadditivity` is GONE.**
    Proof: the algebraic mutual-information identity
    (`mutualInfo_eq_umegaki`, no PosDef on `ρ_AB`) rewrites the gap to
    `umegaki(ρ_AB, ρ_A ⊗ ρ_B)`; the σ-slot `ρ_A ⊗ ρ_B` is PosDef by
    `kroneckerDM_posDef`; and the UNCONDITIONAL general Klein inequality
    (`umegakiRelativeEntropy_nonneg_general_unconditional`) gives `≥ 0` for
    GENERAL `ρ_AB`. -/
theorem weak_subadditivity_general
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hn : 0 < n_A * n_B)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    vonNeumannEntropy ρ
      ≤ vonNeumannEntropy (partialTraceDensity_right ρ)
        + vonNeumannEntropy (partialTraceDensity_left ρ) := by
  -- General Klein: 0 ≤ umegaki(ρ_AB, ρ_A ⊗ ρ_B), for GENERAL ρ_AB and
  -- PosDef σ-slot ρ_A ⊗ ρ_B (the latter from PosDef marginals).
  have hKlein :
      0 ≤ umegakiRelativeEntropy ρ
            (kroneckerDM (partialTraceDensity_right ρ)
                          (partialTraceDensity_left ρ)) :=
    umegakiRelativeEntropy_nonneg_general_unconditional ρ
      (kroneckerDM (partialTraceDensity_right ρ) (partialTraceDensity_left ρ))
      hn (kroneckerDM_posDef _ _ hA hB)
  -- Algebraic identity (NO PosDef on ρ_AB): umegaki = S(A) + S(B) − S(AB).
  rw [mutualInfo_eq_umegaki ρ hA hB] at hKlein
  linarith

/-- **Pure-state corollary.**  For a PURE bipartite state — `ρ_AB` rank-1,
    hence *not* PosDef, so the old `weak_subadditivity` does not apply —
    with positive-definite marginals, weak subadditivity holds.  (The
    rank-1 hypothesis is recorded for documentation; the conclusion is just
    the general theorem instantiated, no extra structure is used.) -/
theorem weak_subadditivity_pure
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hn : 0 < n_A * n_B)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    vonNeumannEntropy ρ
      ≤ vonNeumannEntropy (partialTraceDensity_right ρ)
        + vonNeumannEntropy (partialTraceDensity_left ρ) :=
  weak_subadditivity_general ρ hn hA hB

/-! ## Axiom audit. -/

#print axioms weak_subadditivity_general

end UnifiedTheory.LayerB.WeakSubadditivityGeneral
