/-
  UnifiedTheory/LayerC/SMTensorDecomposition.lean
  ─────────────────────────────────────────────────

  **SM ↔ QM Bridge — Step S2 (Path B).**

  This file establishes the FACTORISATION of the single-generation
  Hilbert space `ℂ^16` as a tensor product of four qubit factors
  `ℂ^2 ⊗ ℂ^2 ⊗ ℂ^2 ⊗ ℂ^2`, matching:

    * the framework substrate identity
        `singleGenDim = N_W ^ d_eff = 2 ^ 4 = 16`
      from `LayerC.SMHilbertInstantiation`, and

    * the SO(10) spinor `16 → 10 + 5̄ + 1` decomposition under
      SU(5) ⊂ SO(10), i.e. one SM generation:

        Q_L : 6,  u_R^c : 3,  d_R^c : 3,
        L_L : 2,  e_R^c : 1,  ν_R^c : 1
        total: 6 + 3 + 3 + 2 + 1 + 1 = 16

      grouped via SU(5) as

        10 of SU(5) = Q_L (6) + u_R^c (3) + e_R^c (1)
         5̄ of SU(5) = d_R^c (3) + L_L (2)
         1 of SU(5) = ν_R^c (1)
        total: 10 + 5 + 1 = 16.

  ## What ships

  ### Tier 1 — Numerical identities

    * `singleGenDim_eq_qubit_pow_4` : `singleGenDim = 2 ^ 4`.
    * `singleGenDim_eq_two_pow_d_eff` : `singleGenDim = 2 ^ atom_d_eff`.
    * `singleGenDim_eq_NW_pow_d_eff` : `singleGenDim = atom_N_W ^ atom_d_eff`.

  ### Tier 2 — Index equivalences (the typed factorisations)

    * `fourQubitEquiv`
        : `Fin singleGenDim ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2)`.
    * `twoQubitEquiv`
        : `Fin 4 ≃ (Fin 2 × Fin 2)`.
    * `threeQubitEquiv`
        : `Fin 8 ≃ (Fin 2 × Fin 2 × Fin 2)`.
    * `singleGenIndexCard`
        : `Fintype.card (Fin singleGenDim)
              = Fintype.card (Fin 2 × Fin 2 × Fin 2 × Fin 2)`.

  ### Tier 3 — SU(5) chiral sector decomposition

    * `smChiralSectorDims  : Fin 6 → ℕ := ![6,3,3,2,1,1]`
        (Q_L, u_R^c, d_R^c, L_L, e_R^c, ν_R^c).
    * `smSU5Sectors        : Fin 3 → ℕ := ![10, 5, 1]`
        (10, 5̄, 1 of SU(5)).
    * `smChiralSectors_sum` : `∑ i, smChiralSectorDims i = singleGenDim`.
    * `smSU5Sectors_sum`    : `∑ i, smSU5Sectors i        = singleGenDim`.
    * `smSU5_eq_chiral_grouping` : the SU(5) sector dims arise from
       grouping the six chiral sectors as (Q_L + u_R^c + e_R^c)
       + (d_R^c + L_L) + (ν_R^c).

  ### Tier 4 — Headline bridge theorem

    `sm_tensor_decomposition_S2` bundles:
      • `singleGenDim = 2 ^ 4`,
      • `Fin singleGenDim ≃ (Fin 2)^×4`,
      • the SU(5) sector sum identity, and
      • coincidence with `dim_spinor_SO10`.

  ## Honest scope

  We ship the DIMENSIONAL FACTORISATION as a typed Lean term
  (`Equiv` between `Fin 16` and the 4-fold qubit index type).  The
  full Lie-algebra representation theory of SU(5) ⊂ SO(10) is OUT
  of scope; the chiral-fermion identification is a labelling layer
  on top of the dimensional factorisation.  All we claim and prove
  is that the cardinalities add up: 10 + 5 + 1 = 16 and
  6 + 3 + 3 + 2 + 1 + 1 = 16, with both equal to
  `singleGenDim = atom_N_W ^ atom_d_eff`.

  ## Standing constraint

  Zero `sorry`, zero custom `axiom`.
-/

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import UnifiedTheory.LayerC.SMHilbertInstantiation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SMTensorDecomposition

open UnifiedTheory.LayerC.SMHilbertInstantiation
  (singleGenDim singleGenDim_eq_sixteen singleGenNS)
open UnifiedTheory.LayerB.CrossSectorIdentitySearch
  (atom_N_W atom_d_eff)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    TIER 1: NUMERICAL IDENTITIES — singleGenDim = 2^4 = N_W^d_eff
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The single-generation Hilbert space dimension factors as four
    qubits.  This is the substrate identity
    `singleGenDim = atom_N_W ^ atom_d_eff = 2 ^ 4 = 16`. -/
theorem singleGenDim_eq_qubit_pow_4 : singleGenDim = 2 ^ 4 := by
  unfold singleGenDim atom_N_W atom_d_eff
  decide

/-- The single-generation dimension equals `2 ^ atom_d_eff`. -/
theorem singleGenDim_eq_two_pow_d_eff : singleGenDim = 2 ^ atom_d_eff := by
  unfold singleGenDim atom_N_W
  rfl

/-- The single-generation dimension equals `atom_N_W ^ atom_d_eff`
    (the LayerC restatement of the substrate `def`). -/
theorem singleGenDim_eq_NW_pow_d_eff :
    singleGenDim = atom_N_W ^ atom_d_eff := rfl

/-- `atom_d_eff = 4` (re-export). -/
theorem d_eff_eq_four : atom_d_eff = 4 := by unfold atom_d_eff; rfl

/-- `atom_N_W = 2` (re-export). -/
theorem N_W_eq_two : atom_N_W = 2 := by unfold atom_N_W; rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    TIER 2: INDEX EQUIVALENCES (the typed tensor factorisation)

    We build `Fin singleGenDim ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2)`
    by composing `finProdFinEquiv` three times.

    Convention: `singleGenDim = 16 = 2 * 8 = 2 * (2 * 4) = 2 * (2 * (2 * 2))`.
    Reading off the products right-to-left.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `Fin 4 ≃ Fin 2 × Fin 2`.  Two-qubit factorisation. -/
def twoQubitEquiv : Fin 4 ≃ (Fin 2 × Fin 2) :=
  (finProdFinEquiv (m := 2) (n := 2)).symm

/-- `Fin 8 ≃ Fin 2 × Fin 2 × Fin 2`.  Three-qubit factorisation
    (using right-associativity of the product). -/
def threeQubitEquiv : Fin 8 ≃ (Fin 2 × Fin 2 × Fin 2) :=
  (finProdFinEquiv (m := 2) (n := 4)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 2)) twoQubitEquiv)

/-- `Fin singleGenDim ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2`.

    THE FOUR-QUBIT INDEX EQUIVALENCE.  Provides the typed Hilbert-
    space factorisation `ℂ^16 ≃ ℂ^2 ⊗ ℂ^2 ⊗ ℂ^2 ⊗ ℂ^2` (since for
    `Fin`-indexed Euclidean spaces, the tensor product is indexed
    by the product of `Fin`s).

    Built by composing the canonical `2 * 8 = 16` and `2 * 4 = 8`
    and `2 * 2 = 4` reductions. -/
def fourQubitEquiv :
    Fin singleGenDim ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2) :=
  -- Rewrite `Fin singleGenDim` as `Fin 16 = Fin (2 * 8)`.
  (finCongr singleGenDim_eq_qubit_pow_4).trans <|
  -- `Fin (2 ^ 4) = Fin 16 = Fin (2 * 8)` by `decide`.
  (finCongr (by decide : (2 ^ 4 : ℕ) = 2 * 8)).trans <|
  -- `Fin (2 * 8) ≃ Fin 2 × Fin 8`.
  (finProdFinEquiv (m := 2) (n := 8)).symm.trans <|
  -- Combine with three-qubit equiv on the right factor.
  Equiv.prodCongr (Equiv.refl (Fin 2)) threeQubitEquiv

/-- Cardinality check: `|Fin singleGenDim| = |Fin 2 × Fin 2 × Fin 2 × Fin 2|`. -/
theorem singleGenIndexCard :
    Fintype.card (Fin singleGenDim)
      = Fintype.card (Fin 2 × Fin 2 × Fin 2 × Fin 2) := by
  rw [Fintype.card_congr fourQubitEquiv]

/-- The four-qubit equiv is, in particular, an equivalence of finite
    sets of cardinality 16. -/
theorem fourQubitEquiv_card_eq :
    Fintype.card (Fin 2 × Fin 2 × Fin 2 × Fin 2) = singleGenDim := by
  rw [← singleGenIndexCard, Fintype.card_fin]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    TIER 3: SU(5) CHIRAL SECTOR DECOMPOSITION

    The 16-dim single-generation Hilbert space partitions into the
    six SU(5) chiral sectors of the SO(10) 16 spinor:

      Q_L : 6   (quark doublet, 2 weak × 3 colour)
      u_R^c : 3 (up-quark singlet, 3 colour)
      d_R^c : 3 (down-quark singlet, 3 colour)
      L_L : 2   (lepton doublet, 2 weak)
      e_R^c : 1 (electron singlet)
      ν_R^c : 1 (right-handed neutrino — SO(10)-mandated)

    Total: 6+3+3+2+1+1 = 16.

    Under SU(5) ⊂ SO(10), they group into 10 + 5̄ + 1:

      10 of SU(5) = Q_L (6) + u_R^c (3) + e_R^c (1) = 10
      5̄ of SU(5) = d_R^c (3) + L_L (2) = 5
      1 of SU(5) = ν_R^c (1) = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The six SU(5)-chiral-sector dimensions of one SM generation,
    in the order `[Q_L, u_R^c, d_R^c, L_L, e_R^c, ν_R^c]`. -/
def smChiralSectorDims : Fin 6 → ℕ := ![6, 3, 3, 2, 1, 1]

/-- The three SU(5) irrep dimensions inside the SO(10) 16-spinor,
    in the order `[10, 5̄, 1]`. -/
def smSU5Sectors : Fin 3 → ℕ := ![10, 5, 1]

/-- **CHIRAL SECTOR SUM.** The six chiral-sector dimensions sum to
    the single-generation Hilbert dimension:
    `6 + 3 + 3 + 2 + 1 + 1 = 16 = singleGenDim`. -/
theorem smChiralSectors_sum :
    ∑ i, smChiralSectorDims i = singleGenDim := by
  rw [singleGenDim_eq_sixteen]
  decide

/-- **SU(5) SECTOR SUM.** The three SU(5) irrep dimensions inside the
    SO(10) spinor sum to the single-generation Hilbert dimension:
    `10 + 5 + 1 = 16 = singleGenDim`. -/
theorem smSU5Sectors_sum : ∑ i, smSU5Sectors i = singleGenDim := by
  rw [singleGenDim_eq_sixteen]
  decide

/-- **Individual sector values** (Q_L). -/
theorem smChiralSectorDims_QL : smChiralSectorDims 0 = 6 := rfl

/-- **Individual sector values** (u_R^c). -/
theorem smChiralSectorDims_uRc : smChiralSectorDims 1 = 3 := rfl

/-- **Individual sector values** (d_R^c). -/
theorem smChiralSectorDims_dRc : smChiralSectorDims 2 = 3 := rfl

/-- **Individual sector values** (L_L). -/
theorem smChiralSectorDims_LL : smChiralSectorDims 3 = 2 := rfl

/-- **Individual sector values** (e_R^c). -/
theorem smChiralSectorDims_eRc : smChiralSectorDims 4 = 1 := rfl

/-- **Individual sector values** (ν_R^c). -/
theorem smChiralSectorDims_nRc : smChiralSectorDims 5 = 1 := rfl

/-- **10 of SU(5)** = Q_L + u_R^c + e_R^c = 6 + 3 + 1 = 10. -/
theorem smSU5_ten_eq_QL_uRc_eRc :
    smSU5Sectors 0
      = smChiralSectorDims 0 + smChiralSectorDims 1 + smChiralSectorDims 4 := by
  decide

/-- **5̄ of SU(5)** = d_R^c + L_L = 3 + 2 = 5. -/
theorem smSU5_fivebar_eq_dRc_LL :
    smSU5Sectors 1
      = smChiralSectorDims 2 + smChiralSectorDims 3 := by
  decide

/-- **1 of SU(5)** = ν_R^c = 1. -/
theorem smSU5_one_eq_nRc :
    smSU5Sectors 2 = smChiralSectorDims 5 := by
  decide

/-- **SU(5) grouping identity.**  The SU(5)-sector dimensions arise
    as sums of chiral-sector dimensions under the standard
    `16 = 10 + 5̄ + 1` grouping. -/
theorem smSU5_eq_chiral_grouping :
    smSU5Sectors 0
        = smChiralSectorDims 0 + smChiralSectorDims 1 + smChiralSectorDims 4 ∧
    smSU5Sectors 1
        = smChiralSectorDims 2 + smChiralSectorDims 3 ∧
    smSU5Sectors 2
        = smChiralSectorDims 5 :=
  ⟨smSU5_ten_eq_QL_uRc_eRc, smSU5_fivebar_eq_dRc_LL, smSU5_one_eq_nRc⟩

/-- **SU(5) sum coincides with chiral sum.**  Both sum to 16. -/
theorem smSU5Sectors_eq_chiral_sum :
    ∑ i, smSU5Sectors i = ∑ i, smChiralSectorDims i := by
  rw [smSU5Sectors_sum, smChiralSectors_sum]

/-- **The 6+3+3+2+1+1 = 10+5+1 = 16 identity** as a single equality. -/
theorem chiral_eq_SU5_eq_sixteen :
    ∑ i, smChiralSectorDims i = 16 ∧
    ∑ i, smSU5Sectors i        = 16 := by
  refine ⟨?_, ?_⟩
  · rw [smChiralSectors_sum, singleGenDim_eq_sixteen]
  · rw [smSU5Sectors_sum,  singleGenDim_eq_sixteen]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    TIER 4: COINCIDENCE WITH SO(10) SPINOR DIMENSION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The single-generation dimension equals the SO(10) spinor
    dimension (re-exported from `SMHilbertInstantiation` for
    self-contained citation). -/
theorem singleGenDim_eq_dim_spinor_SO10 :
    singleGenDim = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 :=
  UnifiedTheory.LayerC.SMHilbertInstantiation.singleGenDim_eq_spinor

/-- The chiral-sector sum equals `dim_spinor_SO10`. -/
theorem smChiralSectors_sum_eq_spinor :
    ∑ i, smChiralSectorDims i
      = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 := by
  rw [smChiralSectors_sum, singleGenDim_eq_dim_spinor_SO10]

/-- The SU(5)-sector sum equals `dim_spinor_SO10`. -/
theorem smSU5Sectors_sum_eq_spinor :
    ∑ i, smSU5Sectors i
      = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 := by
  rw [smSU5Sectors_sum, singleGenDim_eq_dim_spinor_SO10]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    TIER 5: HEADLINE BRIDGE THEOREM (Step S2)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HEADLINE — SM ↔ QM Bridge, Step S2 (Path B).**

    The single-generation Hilbert space `ℂ^16` factors as a four-fold
    tensor product of qubits, matching the SU(5) decomposition
    `16 = 10 + 5̄ + 1` of the SO(10) spinor, which in turn breaks into
    the six SU(5) chiral sectors `6 + 3 + 3 + 2 + 1 + 1 = 16` of one
    SM generation (Q_L, u_R^c, d_R^c, L_L, e_R^c, ν_R^c).

    The conjuncts:
      (1) `singleGenDim = 2 ^ 4`             — dimensional factorisation
      (2) `Fin singleGenDim ≃ (Fin 2)^×4`    — typed index equivalence
      (3) `Σ chiral = singleGenDim`          — six-sector sum
      (4) `Σ SU5    = singleGenDim`          — three-sector sum
      (5) `singleGenDim = dim_spinor_SO10`   — coincidence with SO(10) spinor.

    Conjuncts (1)–(2) are the Path-B tensor factorisation; (3)–(5) are
    the SU(5)/SO(10) chiral-sector labelling layer.

    Per honest scope: this is a DIMENSIONAL / INDEX-LEVEL theorem.
    The Lie-algebra representation theory of SU(5) → SO(10) is not
    formalised; we record only that the cardinalities add up. -/
theorem sm_tensor_decomposition_S2 :
    -- (1) dimensional factorisation
    singleGenDim = 2 ^ 4 ∧
    -- (2) typed four-qubit index equivalence
    Nonempty (Fin singleGenDim ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2)) ∧
    -- (3) six chiral sectors sum to the Hilbert dim
    (∑ i, smChiralSectorDims i = singleGenDim) ∧
    -- (4) three SU(5) sectors sum to the Hilbert dim
    (∑ i, smSU5Sectors i = singleGenDim) ∧
    -- (5) coincidence with SO(10) spinor
    singleGenDim = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 := by
  refine ⟨singleGenDim_eq_qubit_pow_4, ⟨fourQubitEquiv⟩, ?_, ?_, ?_⟩
  · exact smChiralSectors_sum
  · exact smSU5Sectors_sum
  · exact singleGenDim_eq_dim_spinor_SO10

/-- **Numerical capstone.**  The two sector decompositions and the
    qubit tensor exponent all agree at the value 16. -/
theorem sm_tensor_decomposition_S2_numerical :
    singleGenDim = 16 ∧
    (2 ^ 4 : ℕ) = 16 ∧
    (∑ i, smChiralSectorDims i) = 16 ∧
    (∑ i, smSU5Sectors i) = 16 := by
  refine ⟨singleGenDim_eq_sixteen, by decide, ?_, ?_⟩
  · rw [smChiralSectors_sum, singleGenDim_eq_sixteen]
  · rw [smSU5Sectors_sum, singleGenDim_eq_sixteen]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    TIER 6: DIAGNOSTIC EXAMPLES — type-checking witnesses
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four-qubit equivalence type-checks. -/
example : Fin singleGenDim ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2) :=
  fourQubitEquiv

/-- The chiral-sector function type-checks. -/
example : Fin 6 → ℕ := smChiralSectorDims

/-- The SU(5)-sector function type-checks. -/
example : Fin 3 → ℕ := smSU5Sectors

/-- The headline bridge theorem type-checks. -/
example :
    singleGenDim = 2 ^ 4 ∧
    Nonempty (Fin singleGenDim ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2)) ∧
    (∑ i, smChiralSectorDims i = singleGenDim) ∧
    (∑ i, smSU5Sectors i = singleGenDim) ∧
    singleGenDim = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 :=
  sm_tensor_decomposition_S2

end UnifiedTheory.LayerC.SMTensorDecomposition
