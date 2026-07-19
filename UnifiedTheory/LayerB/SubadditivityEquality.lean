/-
  LayerB/SubadditivityEquality.lean
  ──────────────────────────────────

  **The equality condition for subadditivity of the von Neumann entropy.**

  Weak subadditivity (`WeakSubadditivity.weak_subadditivity`) gives

      S(ρ_AB)  ≤  S(ρ_A) + S(ρ_B).

  This file proves the **saturation / equality case**:

      S(ρ_AB) = S(ρ_A) + S(ρ_B)   ⟺   ρ_AB = ρ_A ⊗ ρ_B,

  i.e. the von Neumann entropy is additive over a bipartition *exactly*
  when the joint state is a product (uncorrelated) state.  Equivalently,
  the quantum mutual information vanishes iff the state factorizes:

      I(A : B) = 0   ⟺   ρ_AB = ρ_A ⊗ ρ_B.

  ## Proof (pure assembly of two just-proved results)

  The mutual information is *exactly* a relative entropy
  (`WeakSubadditivity.mutualInfo_eq_umegaki`):

      umegaki(ρ_AB, ρ_A ⊗ ρ_B)  =  S(ρ_A) + S(ρ_B) − S(ρ_AB).

  Hence `S(ρ_AB) = S(ρ_A) + S(ρ_B)` is equivalent to
  `umegaki(ρ_AB, ρ_A ⊗ ρ_B) = 0`, and the **strict Klein faithfulness**
  (`KleinEquality.umegakiRelativeEntropy_eq_zero_iff`) turns the vanishing
  of the relative entropy into `ρ_AB.M = (ρ_A ⊗ ρ_B).M`.  Done.

  The only hypotheses are positive-definiteness of `ρ_AB` and its two
  marginals (genuinely required: the operator logarithms and Klein's
  faithfulness both need PosDef).

  STANDING CONSTRAINT: zero `sorry`, zero custom `axiom`.

  ## Build

      lake build UnifiedTheory.LayerB.SubadditivityEquality
-/
import UnifiedTheory.LayerB.WeakSubadditivity
import UnifiedTheory.LayerB.KleinEquality

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SubadditivityEquality

open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.UmegakiTensorAdditivity
open UnifiedTheory.LayerB.EntanglementAssistedCapacity
open UnifiedTheory.LayerB.WeakSubadditivity
open UnifiedTheory.LayerB.KleinEquality

variable {n_A n_B : ℕ}

/-! ## 1.  The equality condition for subadditivity. -/

/-- **EQUALITY CONDITION FOR SUBADDITIVITY (saturation case).**

    For a bipartite quantum state `ρ_AB : ComplexDensityMatrix (n_A * n_B)`
    whose marginals `ρ_A := Tr_B ρ_AB`, `ρ_B := Tr_A ρ_AB` are positive
    definite, the subadditivity inequality `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` is
    saturated **iff** the joint state is the product of its marginals:

      S(ρ_AB) = S(ρ_A) + S(ρ_B)   ⟺   ρ_AB = ρ_A ⊗ ρ_B.

    Entropy is additive over a bipartition exactly for *uncorrelated*
    (product) states.

    This is a REAL `↔` theorem: the mutual-information identity
    (`mutualInfo_eq_umegaki`) reduces the entropy equation to the
    vanishing of `umegaki(ρ_AB, ρ_A ⊗ ρ_B)`, and the strict Klein
    faithfulness (`umegakiRelativeEntropy_eq_zero_iff`) turns that into
    the matrix identity `ρ_AB.M = (ρ_A ⊗ ρ_B).M`. -/
theorem subadditivity_equality
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    vonNeumannEntropy ρ
        = vonNeumannEntropy (partialTraceDensity_right ρ)
          + vonNeumannEntropy (partialTraceDensity_left ρ)
      ↔ ρ.M
          = (kroneckerDM (partialTraceDensity_right ρ)
                          (partialTraceDensity_left ρ)).M := by
  -- The Kronecker product density and its positive-definiteness.
  set ρAB_prod :=
    kroneckerDM (partialTraceDensity_right ρ) (partialTraceDensity_left ρ)
    with hρAB_prod
  have hprod_posDef : ρAB_prod.M.PosDef := kroneckerDM_posDef _ _ hA hB
  -- The mutual-information identity:
  --   umegaki(ρ, ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B) − S(ρ).
  have hId : umegakiRelativeEntropy ρ ρAB_prod
      = vonNeumannEntropy (partialTraceDensity_right ρ)
        + vonNeumannEntropy (partialTraceDensity_left ρ)
        - vonNeumannEntropy ρ :=
    mutualInfo_eq_umegaki ρ hA hB
  -- The strict Klein faithfulness:  umegaki(ρ, ρ_A ⊗ ρ_B) = 0 ⟺ ρ.M = (ρ_A ⊗ ρ_B).M.
  have hKlein : umegakiRelativeEntropy ρ ρAB_prod = 0 ↔ ρ.M = ρAB_prod.M :=
    umegakiRelativeEntropy_eq_zero_iff ρ ρAB_prod hρ hprod_posDef
  -- Assemble.
  constructor
  · intro hEq
    -- S(ρ) = S(ρ_A) + S(ρ_B) ⟹ umegaki = 0 ⟹ ρ.M = (ρ_A ⊗ ρ_B).M.
    apply hKlein.mp
    rw [hId]; linarith
  · intro hMatrix
    -- ρ.M = (ρ_A ⊗ ρ_B).M ⟹ umegaki = 0 ⟹ S(ρ) = S(ρ_A) + S(ρ_B).
    have hzero : umegakiRelativeEntropy ρ ρAB_prod = 0 := hKlein.mpr hMatrix
    rw [hId] at hzero; linarith

/-! ## 2.  The mutual-information form: `I(A:B) = 0 ⟺ product state`. -/

/-- **ZERO MUTUAL INFORMATION ⟺ PRODUCT STATE.**

    With the quantum mutual information
    `I(A:B) := S(ρ_A) + S(ρ_B) − S(ρ_AB)` (the `mutualInfo` of the three
    von Neumann entropies), it vanishes **iff** the joint state is
    uncorrelated:

      I(A : B) = 0   ⟺   ρ_AB = ρ_A ⊗ ρ_B.

    Combined with `mutualInfo_nonneg_of_density` (I(A:B) ≥ 0 always), this
    says: a bipartite state carries *zero* mutual information precisely
    when it factorizes — there is no classical or quantum correlation to
    measure. -/
theorem mutualInfo_eq_zero_iff_product
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    mutualInfo
        (vonNeumannEntropy (partialTraceDensity_right ρ))
        (vonNeumannEntropy (partialTraceDensity_left ρ))
        (vonNeumannEntropy ρ)
      = 0
      ↔ ρ.M
          = (kroneckerDM (partialTraceDensity_right ρ)
                          (partialTraceDensity_left ρ)).M := by
  -- mutualInfo SA SB SAB = SA + SB − SAB, so I = 0 ⟺ S(ρ) = S(ρ_A) + S(ρ_B).
  rw [show mutualInfo
        (vonNeumannEntropy (partialTraceDensity_right ρ))
        (vonNeumannEntropy (partialTraceDensity_left ρ))
        (vonNeumannEntropy ρ)
        = vonNeumannEntropy (partialTraceDensity_right ρ)
          + vonNeumannEntropy (partialTraceDensity_left ρ)
          - vonNeumannEntropy ρ from rfl]
  rw [sub_eq_zero, eq_comm]
  exact subadditivity_equality ρ hρ hA hB

/-! ## 3.  A correlation corollary: positive mutual information ⟺ non-product.

    The contrapositive packaging of the saturation case: a bipartite
    state has *strictly positive* mutual information exactly when it is
    **not** a product of its marginals.  This is the precise sense in
    which "any correlation costs subadditivity slack". -/

/-- **STRICT SUBADDITIVITY ⟺ CORRELATION (non-product).**

    For a bipartite state with positive-definite marginals,

      S(ρ_AB) < S(ρ_A) + S(ρ_B)   ⟺   ρ_AB ≠ ρ_A ⊗ ρ_B.

    The entropy is *strictly* subadditive precisely when the state is
    correlated (not a product). -/
theorem strict_subadditivity_iff_not_product
    (ρ : ComplexDensityMatrix (n_A * n_B))
    (hρ : ρ.M.PosDef)
    (hA : (partialTraceDensity_right ρ).M.PosDef)
    (hB : (partialTraceDensity_left ρ).M.PosDef) :
    vonNeumannEntropy ρ
        < vonNeumannEntropy (partialTraceDensity_right ρ)
          + vonNeumannEntropy (partialTraceDensity_left ρ)
      ↔ ρ.M
          ≠ (kroneckerDM (partialTraceDensity_right ρ)
                          (partialTraceDensity_left ρ)).M := by
  -- weak subadditivity gives ≤; combine with the equality characterization.
  have hle : vonNeumannEntropy ρ
      ≤ vonNeumannEntropy (partialTraceDensity_right ρ)
        + vonNeumannEntropy (partialTraceDensity_left ρ) :=
    weak_subadditivity ρ hρ hA hB
  have hEqIff := subadditivity_equality ρ hρ hA hB
  constructor
  · intro hlt hMatrix
    -- equality from product would contradict the strict inequality.
    exact absurd (hEqIff.mpr hMatrix) (ne_of_lt hlt)
  · intro hne
    -- ≤ and ≠-equality ⟹ <.
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (hEqIff.mp h) hne

/-! ## 4.  Axiom audit. -/

#print axioms subadditivity_equality
#print axioms mutualInfo_eq_zero_iff_product
#print axioms strict_subadditivity_iff_not_product

end UnifiedTheory.LayerB.SubadditivityEquality
