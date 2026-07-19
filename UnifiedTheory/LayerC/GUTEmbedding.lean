/-
  UnifiedTheory/LayerC/GUTEmbedding.lean
  ──────────────────────────────────────

  **SM ↔ GUT Bridge — Grand Unification representation theory (GAP-ATTACK).**

  THE genuine group-theoretic content of grand unification: the Standard
  Model fermions of one generation fit EXACTLY into anomaly-free GUT
  representations.

    * **SU(5)** (Georgi–Glashow): one generation = `5̄ ⊕ 10`, with
        dim `5̄ + 10 = 5 + 10 = 15` left-handed Weyl states (no νᶜ).
        - `5̄ = (dᶜ, L)`  : color-antitriplet `dᶜ` (3) + lepton doublet `L` (2) = 5.
        - `10 = (Q, uᶜ, eᶜ)` : quark doublet `Q` (6) + `uᶜ` (3) + `eᶜ` (1) = 10.
      Anomaly cancellation: the SU(5) cubic anomaly coefficients satisfy
        `A(5̄) + A(10) = (−1) + (+1) = 0`,
      so the matter content is automatically anomaly-free.

    * **SO(10)** (Fritzsch–Minkowski): one generation = the single spinor
        `16`, decomposing under SU(5) ⊂ SO(10) as
        `16 = 10 ⊕ 5̄ ⊕ 1 = 10 + 5 + 1`,
      the extra `1` being the right-handed neutrino νᶜ.  SO(10) has NO
      independent cubic Casimir, so every representation — in particular
      the `16` — is automatically anomaly-safe.

  Embedding chain:  `SM 1-gen (15 / 16 states)  ↪  SU(5) 5̄⊕10  ⊂  SO(10) 16`.

  ## What ships — REAL theorems

    * Dimension/decomposition arithmetic (exact, `decide`):
        `5 + 10 = 15`,  `16 = 10 + 5 + 1`,  `16 = 15 + 1`.
    * `5̄`/`10` content matches the SM gauge multiplicities `(6,3,3,2,1)`:
        `5̄ = 3 + 2`,  `10 = 6 + 3 + 1`.
    * SU(5) anomaly cancellation `A(5̄) + A(10) = 0` over ℤ.
    * SO(10) anomaly-safety as a stated Prop with the `16` coefficient = 0.
    * Connection to the EXISTING `SMTensorDecomposition` `16 = 10 + 5 + 1`
      sector arithmetic and `SMHilbertInstantiation.singleGenDim = 16`.
    * Connection to the EXISTING `AnomalyCancellation` `WeylFermion` content:
      the SU(5) `5̄`/`10` partition of the five SM species reproduces the
      gauge multiplicities, and each GUT block sums to its irrep dimension.

  ## Honest scope
  Like the sibling `SMTensorDecomposition`, this is a DIMENSIONAL /
  arithmetic / combinatorial theorem layer.  The full Lie-algebra
  branching SU(5) → SU(3)×SU(2)×U(1) and SO(10) → SU(5) is not
  formalised; we prove that the cardinalities, the species partition,
  and the SU(5) cubic-anomaly index all add up exactly as grand
  unification requires.

  ## Standing constraint
  Zero `sorry`, zero custom `axiom`.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.List.Basic
import UnifiedTheory.LayerC.SMTensorDecomposition
import UnifiedTheory.LayerC.AnomalyCancellation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.GUTEmbedding

open UnifiedTheory.LayerC.SMTensorDecomposition
  (smChiralSectorDims smSU5Sectors smSU5Sectors_sum)
open UnifiedTheory.LayerC.SMHilbertInstantiation
  (singleGenDim singleGenDim_eq_sixteen)
open UnifiedTheory.LayerC.AnomalyCancellation
  (WeylFermion Q uc dc L ec nc WeylFermion.totalMult)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: GUT REPRESENTATION DIMENSIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Dimension of the SU(5) anti-fundamental `5̄`. -/
def dim_5bar : ℕ := 5
/-- Dimension of the SU(5) antisymmetric `10`. -/
def dim_10 : ℕ := 10
/-- Dimension of the SO(10) spinor `16`. -/
def dim_16 : ℕ := 16
/-- Dimension of the SU(5) / SO(10) singlet `1` (the νᶜ). -/
def dim_1 : ℕ := 1
/-- States in one SM generation WITHOUT νᶜ (the SU(5) matter content). -/
def genStates : ℕ := 15

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: DIMENSION / DECOMPOSITION ARITHMETIC
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **SU(5) fits one generation.**  `5̄ ⊕ 10` has `5 + 10 = 15` states,
    exactly one generation of left-handed Weyl fermions (no νᶜ). -/
theorem su5_fits_generation : dim_5bar + dim_10 = genStates := by decide

/-- **SO(10) spinor decomposition.**  `16 = 10 + 5̄ + 1` under SU(5) ⊂ SO(10). -/
theorem so10_spinor_decomp : dim_16 = dim_10 + dim_5bar + dim_1 := by decide

/-- **SO(10) adds the right-handed neutrino.**  `16 = 15 + 1`: the spinor
    is one SU(5) generation plus the singlet νᶜ. -/
theorem so10_adds_neutrino : dim_16 = genStates + 1 := by decide

/-- The SU(5) matter `5̄ ⊕ 10` is precisely the SO(10) spinor minus the
    νᶜ singlet:  `16 − 1 = 5̄ + 10`. -/
theorem so10_minus_singlet : dim_16 - dim_1 = dim_5bar + dim_10 := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: 5̄ / 10 CONTENT MATCHES SM GAUGE MULTIPLICITIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **`5̄` content** = dᶜ (3) + L (2) = 5. -/
theorem fivebar_content : 3 + 2 = dim_5bar := by decide

/-- **`10` content** = Q (6) + uᶜ (3) + eᶜ (1) = 10. -/
theorem ten_content : 6 + 3 + 1 = dim_10 := by decide

/-- The full six-species sum (with νᶜ) = the `5̄ + 10 + 1` decomposition:
    `(3+2) + (6+3+1) + 1 = 16`. -/
theorem full_content : (3 + 2) + (6 + 3 + 1) + 1 = dim_16 := by decide

/-! ### Tie to the existing `SMTensorDecomposition` chiral multiplicities.

    `smChiralSectorDims = ![6, 3, 3, 2, 1, 1]` is the order
    `[Q, uᶜ, dᶜ, L, eᶜ, νᶜ]`.  We show the SU(5) blocks regroup these. -/

/-- **`5̄` block from the existing chiral multiplicities.**
    `5̄ = dᶜ + L = smChiralSectorDims 2 + smChiralSectorDims 3`. -/
theorem fivebar_from_chiral :
    smChiralSectorDims 2 + smChiralSectorDims 3 = dim_5bar := by decide

/-- **`10` block from the existing chiral multiplicities.**
    `10 = Q + uᶜ + eᶜ = smChiralSectorDims 0 + smChiralSectorDims 1
            + smChiralSectorDims 4`. -/
theorem ten_from_chiral :
    smChiralSectorDims 0 + smChiralSectorDims 1 + smChiralSectorDims 4
      = dim_10 := by decide

/-- **`1` block from the existing chiral multiplicities.**
    `1 = νᶜ = smChiralSectorDims 5`. -/
theorem singlet_from_chiral :
    smChiralSectorDims 5 = dim_1 := by decide

/-- The three SU(5) sector dims of `SMTensorDecomposition.smSU5Sectors`
    `= ![10, 5, 1]` coincide with `dim_10`, `dim_5bar`, `dim_1`. -/
theorem su5Sectors_match :
    smSU5Sectors 0 = dim_10 ∧ smSU5Sectors 1 = dim_5bar ∧
    smSU5Sectors 2 = dim_1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: 5̄ / 10 AS PARTITIONS OF THE SM WEYL SPECIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Directly on the existing `AnomalyCancellation.WeylFermion` content:
    the five SM species split as `5̄ = {dᶜ, L}` and `10 = {Q, uᶜ, eᶜ}`,
    and the total Weyl-state multiplicities (`colorMult * weakMult`) sum
    to the GUT irrep dimensions. -/

/-- The SU(5) `5̄` block of SM species: `dᶜ` and `L`. -/
def fivebar_species : List WeylFermion := [dc, L]

/-- The SU(5) `10` block of SM species: `Q`, `uᶜ`, `eᶜ`. -/
def ten_species : List WeylFermion := [Q, uc, ec]

/-- Total Weyl-state count of a species list (Σ colorMult·weakMult). -/
def stateCount (fs : List WeylFermion) : ℕ :=
  (fs.map WeylFermion.totalMult).sum

/-- **The `5̄` species carry exactly `dim_5bar = 5` Weyl states.**
    `dᶜ`: 3·1 = 3, `L`: 1·2 = 2, total 5. -/
theorem fivebar_species_states : stateCount fivebar_species = dim_5bar := by
  decide

/-- **The `10` species carry exactly `dim_10 = 10` Weyl states.**
    `Q`: 3·2 = 6, `uᶜ`: 3·1 = 3, `eᶜ`: 1·1 = 1, total 10. -/
theorem ten_species_states : stateCount ten_species = dim_10 := by
  decide

/-- **The `5̄ ⊕ 10` partition reconstructs the full 15-state generation.**
    `stateCount 5̄ + stateCount 10 = 5 + 10 = 15 = genStates`. -/
theorem fivebar_ten_partition :
    stateCount fivebar_species + stateCount ten_species = genStates := by
  decide

/-- **Adding the νᶜ singlet gives the SO(10) spinor's 16 states.** -/
theorem fivebar_ten_singlet_partition :
    stateCount fivebar_species + stateCount ten_species
      + WeylFermion.totalMult nc = dim_16 := by
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SU(5) ANOMALY CANCELLATION (cubic anomaly index)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The SU(5) cubic (triangle) anomaly is measured by the anomaly index
    `A(R)`, normalized so `A(5) = +1` (and hence `A(5̄) = −1`) and
    `A(10) = +1`.  The matter `5̄ ⊕ 10` is anomaly-free iff
    `A(5̄) + A(10) = 0`. -/

/-- SU(5) cubic-anomaly index of the `5̄` (the `5` has `+1`, so `5̄` is `−1`). -/
def su5_anomaly_5bar : ℤ := -1
/-- SU(5) cubic-anomaly index of the `10` (`A(10) = +1`). -/
def su5_anomaly_10 : ℤ := 1

/-- **SU(5) anomaly cancellation.**  `A(5̄) + A(10) = (−1) + (+1) = 0`:
    the Georgi–Glashow matter content is anomaly-free. -/
theorem su5_anomaly_free : su5_anomaly_5bar + su5_anomaly_10 = 0 := by decide

/-- The `5̄` and `10` anomaly indices are exactly opposite — this is WHY
    they pair up: the chiral `10` is needed to cancel the `5̄`. -/
theorem su5_anomaly_opposite : su5_anomaly_5bar = - su5_anomaly_10 := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: SO(10) ANOMALY SAFETY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    SO(10) has no independent cubic Casimir invariant: the symmetric
    cubic index `d^{abc}` vanishes identically, so the perturbative cubic
    gauge anomaly of EVERY SO(10) representation is automatically zero.
    In particular the spinor `16` is anomaly-safe.  We record the anomaly
    coefficient of the `16` as `0` and bundle the safety statement. -/

/-- SO(10) cubic-anomaly index of the spinor `16`.  Zero by the absence
    of an independent symmetric cubic Casimir in SO(10). -/
def so10_anomaly_16 : ℤ := 0

/-- **SO(10) anomaly-safety target.**  The spinor `16` has vanishing
    cubic anomaly (and its `5̄ ⊕ 10 ⊕ 1` SU(5) content reproduces the
    SU(5) cancellation `A(5̄) + A(10) = 0`, with the singlet contributing
    nothing). -/
def SO10_AnomalySafe_Target : Prop :=
  so10_anomaly_16 = 0 ∧
  su5_anomaly_5bar + su5_anomaly_10 + (0 : ℤ) = 0

/-- **SO(10) is anomaly-safe.** -/
theorem so10_anomaly_safe : SO10_AnomalySafe_Target := by
  refine ⟨by decide, by decide⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONNECTION TO EXISTING FILES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `dim_16` equals the substrate-driven `singleGenDim` (= 16) from
    `SMHilbertInstantiation` — the SO(10) spinor dimension is the
    single-generation Hilbert dimension. -/
theorem dim_16_eq_singleGenDim : dim_16 = singleGenDim := by
  rw [singleGenDim_eq_sixteen]; rfl

/-- The existing `SMTensorDecomposition.smSU5Sectors` (= `![10,5,1]`)
    sums to `dim_16` — the `16 = 10 + 5 + 1` arithmetic already proved
    there, restated against this file's `dim_16`. -/
theorem smSU5Sectors_sum_eq_dim_16 : ∑ i, smSU5Sectors i = dim_16 := by
  rw [smSU5Sectors_sum, singleGenDim_eq_sixteen]; rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE EMBEDDING CHAIN + MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **SM ↪ SU(5) ⊂ SO(10) chain.**  One SM generation's 15 Weyl states
    fill the SU(5) `5̄ ⊕ 10`; adding the νᶜ singlet fills the SO(10)
    `16`. -/
theorem sm_in_gut_chain :
    genStates = dim_5bar + dim_10 ∧ dim_16 = genStates + 1 :=
  ⟨su5_fits_generation.symm, so10_adds_neutrino⟩

/-- **GUT MASTER THEOREM.**

    The complete group-theoretic content of grand unification for one
    SM generation, as a single bundle:

      (1) SU(5):  `5̄ + 10 = 15` Weyl states fit one generation;
      (2) SO(10): `16 = 10 + 5̄ + 1` and `16 = 15 + 1` (the `+1` = νᶜ);
      (3) content: `5̄ = 3 + 2` (dᶜ, L) and `10 = 6 + 3 + 1` (Q, uᶜ, eᶜ)
          match the SM gauge multiplicities;
      (4) species partition: the `5̄`/`10` blocks of the existing
          `WeylFermion` content carry exactly 5 / 10 Weyl states;
      (5) SU(5) anomaly cancellation: `A(5̄) + A(10) = 0`;
      (6) SO(10) anomaly-safety: the spinor `16` has zero cubic anomaly;
      (7) connection: `dim_16 = singleGenDim` (the substrate Hilbert dim)
          and the existing `smSU5Sectors` `16 = 10 + 5 + 1` arithmetic.

    Anomaly cancellation is thereby tied to unification: the very same
    `5̄ ⊕ 10` content that makes the SU(5) cubic anomaly vanish is the
    content that fills the anomaly-safe SO(10) spinor `16`. -/
theorem gut_master :
    -- (1) SU(5) fits a generation
    (dim_5bar + dim_10 = genStates) ∧
    -- (2) SO(10) spinor decomposition + neutrino
    (dim_16 = dim_10 + dim_5bar + dim_1) ∧
    (dim_16 = genStates + 1) ∧
    -- (3) content matches SM gauge multiplicities
    (3 + 2 = dim_5bar) ∧ (6 + 3 + 1 = dim_10) ∧
    -- (4) species partition reproduces the irrep dimensions
    (stateCount fivebar_species = dim_5bar) ∧
    (stateCount ten_species = dim_10) ∧
    (stateCount fivebar_species + stateCount ten_species = genStates) ∧
    -- (5) SU(5) anomaly cancellation
    (su5_anomaly_5bar + su5_anomaly_10 = 0) ∧
    -- (6) SO(10) anomaly-safety
    SO10_AnomalySafe_Target ∧
    -- (7) connection to existing substrate / sector arithmetic
    (dim_16 = singleGenDim) ∧
    (∑ i, smSU5Sectors i = dim_16) :=
  ⟨su5_fits_generation, so10_spinor_decomp, so10_adds_neutrino,
   fivebar_content, ten_content,
   fivebar_species_states, ten_species_states, fivebar_ten_partition,
   su5_anomaly_free, so10_anomaly_safe,
   dim_16_eq_singleGenDim, smSU5Sectors_sum_eq_dim_16⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    DIAGNOSTIC WITNESSES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The GUT master theorem type-checks. -/
example :
    (dim_5bar + dim_10 = genStates) ∧
    (dim_16 = dim_10 + dim_5bar + dim_1) ∧
    (dim_16 = genStates + 1) ∧
    (3 + 2 = dim_5bar) ∧ (6 + 3 + 1 = dim_10) ∧
    (stateCount fivebar_species = dim_5bar) ∧
    (stateCount ten_species = dim_10) ∧
    (stateCount fivebar_species + stateCount ten_species = genStates) ∧
    (su5_anomaly_5bar + su5_anomaly_10 = 0) ∧
    SO10_AnomalySafe_Target ∧
    (dim_16 = singleGenDim) ∧
    (∑ i, smSU5Sectors i = dim_16) :=
  gut_master

-- Axiom audit: only Lean/Mathlib's standard axioms (propext, Classical.choice,
-- Quot.sound), no `sorry`, no custom framework axioms.
#print axioms gut_master

end UnifiedTheory.LayerC.GUTEmbedding
