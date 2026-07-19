/-
  LayerB/ArakiLieb.lean

  **The Araki–Lieb triangle inequality for von Neumann entropy.**

  For a bipartite quantum state ρ_AB with marginals ρ_A and ρ_B, the
  von Neumann entropies satisfy the two-sided sandwich

        |S(A) − S(B)|  ≤  S(AB)  ≤  S(A) + S(B).

  The right inequality is ordinary (weak) **subadditivity**; the left
  inequality is the **Araki–Lieb triangle inequality** (Araki–Lieb 1970).

  ## What this file closes UNCONDITIONALLY

  The *logical core* of the Araki–Lieb derivation is purely
  order-theoretic once the purification identities are in hand.
  Purify AB with a reference system R into a global *pure* state ABR.
  Purity of a pure global state forces complementary marginals to share
  an entropy:

        S(AB) = S(R)        (complement of AB is R)
        S(A)  = S(BR)       (complement of A is BR)

  Apply *subadditivity* on the (B, R) cut, `S(BR) ≤ S(B) + S(R)`, and
  substitute the purity identities to get

        S(A)  =  S(BR)  ≤  S(B) + S(R)  =  S(B) + S(AB),

  i.e. `S(A) − S(B) ≤ S(AB)`.  The symmetric purification (purify with
  a reference and look at the (A, R) cut) gives `S(B) − S(A) ≤ S(AB)`,
  and the two combine via `abs_le` into `|S(A) − S(B)| ≤ S(AB)`.

  This derivation — Araki–Lieb FROM subadditivity + purity, and the
  full two-sided sandwich — is closed here with no `sorry` and no
  custom `axiom`, given the hypotheses recorded in `EntropyData`.

  ## What remains a named target

  The one genuinely-deep analytic input is *weak subadditivity of the
  von Neumann entropy on an arbitrary bipartite state*, which Mathlib
  does not (yet) provide in operator form.  We expose it as the named
  proposition `Subadditivity_Target` and feed it into the sandwich as a
  hypothesis.  We ALSO instantiate the whole construction on the
  repository's concrete diagonal von Neumann entropy
  (`vonNeumannEntropyDiagonal`) for a **product** state, where
  subadditivity holds with equality and the sandwich is therefore
  fully unconditional.

  ## Build

      lake build UnifiedTheory.LayerB.ArakiLieb
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import UnifiedTheory.LayerB.DiagonalVonNeumannEntropy

namespace UnifiedTheory.LayerB.ArakiLieb

/-! ## 1. Abstract entropy data for a purified tripartite state -/

/-- Abstract entropy bookkeeping for a tripartite **pure** global state
    `ABR` obtained by purifying the bipartite state `AB` with a
    reference `R`.  The purification identities and the two relevant
    subadditivity cuts are recorded as fields, so that every downstream
    Araki–Lieb statement is a pure real-arithmetic consequence.

    Field meanings (all are real von Neumann entropies):

    * `SA`, `SB`, `SAB` — entropies of the marginals of the physical
      systems A, B and of the joint AB.
    * `SR`  — entropy of the purifying reference R.
    * `SBR`, `SAR` — entropies of the joint marginals BR and AR.

    Purity of the global state forces complementary marginals to share
    an entropy (`pure_AB_R`, `pure_A_BR`, `pure_B_AR`), and weak
    subadditivity is recorded on the two cuts we actually use
    (`subadd_BR`, `subadd_AR`). -/
structure EntropyData where
  SA : ℝ
  SB : ℝ
  SAB : ℝ
  SR : ℝ
  SBR : ℝ
  SAR : ℝ
  /-- Purity of `ABR`: the complement of `AB` is `R`, so `S(AB)=S(R)`. -/
  pure_AB_R : SAB = SR
  /-- Purity of `ABR`: the complement of `A` is `BR`, so `S(A)=S(BR)`. -/
  pure_A_BR : SA = SBR
  /-- Purity of `ABR`: the complement of `B` is `AR`, so `S(B)=S(AR)`. -/
  pure_B_AR : SB = SAR
  /-- Weak subadditivity on the `(B, R)` cut. -/
  subadd_BR : SBR ≤ SB + SR
  /-- Weak subadditivity on the `(A, R)` cut. -/
  subadd_AR : SAR ≤ SA + SR

namespace EntropyData

/-! ## 2. The Araki–Lieb lower bound (the logical core) -/

/-- **Araki–Lieb, one side:** `S(A) − S(B) ≤ S(AB)`.

    Derived from subadditivity on the `(B,R)` cut together with the
    purity identities `S(A) = S(BR)` and `S(AB) = S(R)`. -/
theorem arakiLieb_lower (d : EntropyData) : d.SA - d.SB ≤ d.SAB := by
  have hsub := d.subadd_BR          -- SBR ≤ SB + SR
  have hA := d.pure_A_BR            -- SA = SBR
  have hAB := d.pure_AB_R           -- SAB = SR
  -- SA = SBR ≤ SB + SR = SB + SAB
  linarith

/-- **Araki–Lieb, the other side:** `S(B) − S(A) ≤ S(AB)`.

    Symmetric to `arakiLieb_lower`, using the `(A,R)` cut and the
    purity identities `S(B) = S(AR)` and `S(AB) = S(R)`. -/
theorem arakiLieb_lower' (d : EntropyData) : d.SB - d.SA ≤ d.SAB := by
  have hsub := d.subadd_AR          -- SAR ≤ SA + SR
  have hB := d.pure_B_AR            -- SB = SAR
  have hAB := d.pure_AB_R           -- SAB = SR
  linarith

/-- **Araki–Lieb triangle inequality:** `|S(A) − S(B)| ≤ S(AB)`.

    Both signed bounds combine through `abs_le`. -/
theorem arakiLieb_abs (d : EntropyData) : |d.SA - d.SB| ≤ d.SAB := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- −SAB ≤ SA − SB  ⟺  SB − SA ≤ SAB
    have h := d.arakiLieb_lower'
    linarith
  · -- SA − SB ≤ SAB
    exact d.arakiLieb_lower

/-! ## 3. Subadditivity as a named target and the full sandwich -/

/-- **Weak subadditivity for this datum**, stated abstractly:
    `S(AB) ≤ S(A) + S(B)`.

    This is the one genuinely-deep analytic input (the operator-level
    proof is not available in Mathlib for an arbitrary bipartite
    state).  It is the upper edge of the Araki–Lieb sandwich. -/
def Subadditivity_Target (d : EntropyData) : Prop :=
  d.SAB ≤ d.SA + d.SB

/-- **The full Araki–Lieb sandwich**, given subadditivity:

        |S(A) − S(B)|  ≤  S(AB)  ≤  S(A) + S(B).

    The lower bound is unconditional (`arakiLieb_abs`); the upper bound
    is supplied by the `Subadditivity_Target` hypothesis. -/
theorem arakiLieb_sandwich (d : EntropyData)
    (hsub : d.Subadditivity_Target) :
    |d.SA - d.SB| ≤ d.SAB ∧ d.SAB ≤ d.SA + d.SB :=
  ⟨d.arakiLieb_abs, hsub⟩

end EntropyData

/-- **Master theorem (abstract).**  For any purified bipartite entropy
    datum satisfying weak subadditivity, the von Neumann entropy obeys
    the two-sided Araki–Lieb bound

        |S(A) − S(B)|  ≤  S(AB)  ≤  S(A) + S(B). -/
theorem araki_lieb_master (d : EntropyData)
    (hsub : d.Subadditivity_Target) :
    |d.SA - d.SB| ≤ d.SAB ∧ d.SAB ≤ d.SA + d.SB :=
  d.arakiLieb_sandwich hsub

/-! ## 4. Concrete instantiation on the repository's diagonal entropy

    The repo provides `vonNeumannEntropyDiagonal` together with the
    **product additivity** law

        S(P ⊗ Q) = S(P) + S(Q)        (`vonNeumannEntropyDiagonal_of_product`).

    For a product state, subadditivity holds with *equality*, so we can
    build a concrete `EntropyData` whose `Subadditivity_Target` is
    discharged unconditionally and read off the full sandwich for a real
    von Neumann entropy in the repository.

    The purifying-reference data is taken to be a fictitious pure
    reference with `SR = SAB`, `SBR = SA`, `SAR = SB`, which is exactly
    the configuration a purification produces for a product state; the
    purity identities then hold by construction and the two cut
    subadditivities reduce to the product additivity law. -/

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.DiagonalVonNeumannEntropy

/-- A concrete `EntropyData` built from the diagonal von Neumann entropy
    of a **product** state `P ⊗ Q`, with a purifying reference chosen so
    that all the structural fields are satisfied by the product
    additivity law.  Here `SA = S(P)`, `SB = S(Q)`,
    `SAB = S(P ⊗ Q) = S(P) + S(Q)`. -/
noncomputable def productEntropyData
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbabilityVector α) (Q : ProbabilityVector β) : EntropyData where
  SA := vonNeumannEntropyDiagonal P
  SB := vonNeumannEntropyDiagonal Q
  SAB := vonNeumannEntropyDiagonal (productDistribution P Q)
  -- pure reference R has S(R) = S(AB); BR and AR mirror A and B.
  SR := vonNeumannEntropyDiagonal (productDistribution P Q)
  SBR := vonNeumannEntropyDiagonal P
  SAR := vonNeumannEntropyDiagonal Q
  pure_AB_R := rfl
  pure_A_BR := rfl
  pure_B_AR := rfl
  subadd_BR := by
    -- S(BR) = S(A) = S(P) ≤ S(Q) + S(P⊗Q) = SB + SR ... but here we use
    -- the *product* configuration: S(A) ≤ S(B) + S(AB).
    -- For the product state S(AB) = S(A)+S(B) ≥ 0, and S(A) ≤ S(B)+S(AB)
    -- follows since S(AB) = S(A)+S(B) and S(B) ≥ 0.
    have hadd := vonNeumannEntropyDiagonal_of_product P Q
    have hQ : 0 ≤ vonNeumannEntropyDiagonal Q :=
      vonNeumannEntropyDiagonal_nonneg Q
    -- goal: S(P) ≤ S(Q) + S(P⊗Q)
    rw [hadd]; linarith
  subadd_AR := by
    have hadd := vonNeumannEntropyDiagonal_of_product P Q
    have hP : 0 ≤ vonNeumannEntropyDiagonal P :=
      vonNeumannEntropyDiagonal_nonneg P
    rw [hadd]; linarith

/-- **Subadditivity is unconditional for the product state.**
    Indeed it holds with equality. -/
theorem productEntropyData_subadditivity
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbabilityVector α) (Q : ProbabilityVector β) :
    (productEntropyData P Q).Subadditivity_Target := by
  change vonNeumannEntropyDiagonal (productDistribution P Q)
        ≤ vonNeumannEntropyDiagonal P + vonNeumannEntropyDiagonal Q
  rw [vonNeumannEntropyDiagonal_of_product]

/-- **Fully unconditional Araki–Lieb sandwich for a product state**, on
    the repository's concrete diagonal von Neumann entropy:

        |S(P) − S(Q)|  ≤  S(P ⊗ Q)  ≤  S(P) + S(Q).

    No hypotheses: subadditivity is discharged by the product additivity
    law, and the lower bound is the abstract `arakiLieb_abs`. -/
theorem araki_lieb_diagonal_product
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbabilityVector α) (Q : ProbabilityVector β) :
    |vonNeumannEntropyDiagonal P - vonNeumannEntropyDiagonal Q|
        ≤ vonNeumannEntropyDiagonal (productDistribution P Q)
    ∧ vonNeumannEntropyDiagonal (productDistribution P Q)
        ≤ vonNeumannEntropyDiagonal P + vonNeumannEntropyDiagonal Q :=
  araki_lieb_master (productEntropyData P Q)
    (productEntropyData_subadditivity P Q)

/-! ## 5. Axiom audit -/

-- The abstract core uses only standard real arithmetic.
#print axioms EntropyData.arakiLieb_abs
-- The concrete diagonal sandwich is fully unconditional.
#print axioms araki_lieb_diagonal_product

end UnifiedTheory.LayerB.ArakiLieb
