/-
  UnifiedTheory/LayerC/AtomicOperationalDictionary.lean
  ─────────────────────────────────────────────────────

  **SM ↔ QM Bridge — Step S7 (Path A).**

  THE ATOMIC-OPERATIONAL DICTIONARY.

  This file collects, in a single citable `Prop`, every place where
  a framework substrate atom (or a polynomial combination of atoms)
  equals the dimension/index of an operational quantum structure
  used elsewhere in the LayerB/LayerC bridge.

  Concretely, the dictionary bundles nine clauses:

    (1)  atom_N_W = 2                                  (qubit dim)
    (2)  atom_N_c = 3                                  (qutrit dim)
    (3)  singleGenDim = 16                             (one full SM
                                                        generation Hilbert
                                                        space dim)
    (4)  singleGenDim = dim_spinor_SO10                (LayerB ↔ LayerC
                                                        substrate bridge)
    (5)  seesawDim    = 126                            (heavy-ν_R Majorana
                                                        mass irrep dim)
    (6)  atom_disc ∣ seesawDim                         (disc=7 prime-
                                                        factors 126)
    (7)  atom_disc = atom_N_c + atom_d_eff             (disc = N_c + d_eff)
    (8)  atom_disc = atom_N_W + atom_N_total           (alt. atomic id.)
    (9)  atom_N_total = atom_N_W + atom_N_c            (N_total decomp.)

  Every clause is proved either by `rfl`, by `decide`, or by citation
  of an already-existing theorem in LayerB/LayerC.  Zero new content
  is introduced — this file is a CATALOGUE, not a derivation.

  ## What this file MEANS structurally

  The dictionary closes the loop on Path A: the substrate atoms
  {N_W, N_c, N_total, d_eff, disc} that LayerB derives from the
  framework's algebraic backbone are SIMULTANEOUSLY (a) the
  dimensions of operational no-signalling theories at LayerC and
  (b) the prime factors of SO(10) GUT-irrep dimensions.  No
  reconciliation step is required — the same integers play both
  roles, by EQUALITY at every clause.

  ## Standing constraint
  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.CrossSectorIdentitySearch
import UnifiedTheory.LayerB.SO10EmbeddingTest
import UnifiedTheory.LayerC.SMHilbertInstantiation
import UnifiedTheory.LayerC.SMSeeSawSubspace

set_option relaxedAutoImplicit false
set_option linter.dupNamespace false

namespace UnifiedTheory.LayerC.AtomicOperationalDictionary

open UnifiedTheory.LayerB.CrossSectorIdentitySearch
  (atom_N_W atom_N_c atom_d_eff atom_N_total atom_disc
   disc_eq_Nc_plus_d disc_eq_NW_plus_Ntotal Ntotal_eq_NW_plus_Nc)
open UnifiedTheory.LayerC.SMHilbertInstantiation
  (singleGenDim singleGenDim_eq_sixteen singleGenDim_eq_spinor)
open UnifiedTheory.LayerC.SMSeeSawSubspace
  (seesawDim seesawDim_eq_126 disc_prime_factor_of_seesawDim)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE DICTIONARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE ATOMIC-OPERATIONAL DICTIONARY.**

    A single `Prop` that asserts every place at which a framework
    substrate atom (or a polynomial expression in the atoms) equals
    the dimension or index of an operational quantum structure used
    in the SM ↔ QM Path A bridge.

    Nine clauses:

      (1) N_W = 2
            qubit Hilbert space dimension (Raymond–Robichaud single
            system at n = atom_N_W in `qubitNS`).
      (2) N_c = 3
            qutrit Hilbert space dimension (color slice, n = atom_N_c
            in `qutritNS`).
      (3) singleGenDim = N_W ^ d_eff = 16
            single-generation Hilbert dimension forced by the substrate
            atoms (`singleGenNS`).
      (4) singleGenDim = dim_spinor_SO10
            the same 16 IS the SO(10) spinor representation dimension
            (Layer B representation theory).
      (5) seesawDim = 2 · N_c² · disc = 126
            the see-saw subspace dimension forced by {N_c, disc}.
      (6) atom_disc ∣ seesawDim
            disc = 7 prime-factors the 126_R irrep.
      (7) atom_disc = atom_N_c + atom_d_eff
            the structural identity disc = N_c + d_eff.
      (8) atom_disc = atom_N_W + atom_N_total
            equivalent decomposition disc = N_W + N_total.
      (9) atom_N_total = atom_N_W + atom_N_c
            N_total = N_W + N_c.

    All nine clauses re-export pre-existing definitional equalities
    or LayerB/LayerC theorems; the dictionary itself is a CATALOGUE,
    not a derivation. -/
def AtomicOperationalDictionary : Prop :=
  -- (1) N_W = qubit Hilbert dim
  atom_N_W = 2 ∧
  -- (2) N_c = qutrit Hilbert dim
  atom_N_c = 3 ∧
  -- (3) Single-generation Hilbert dim = 16
  singleGenDim = 16 ∧
  -- (4) Single-generation = SO(10) spinor dim
  singleGenDim = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 ∧
  -- (5) See-saw subspace dim = 126
  seesawDim = 126 ∧
  -- (6) atom_disc prime-factors the see-saw irrep dim
  atom_disc ∣ seesawDim ∧
  -- (7) Atomic identity: disc = N_c + d_eff
  atom_disc = atom_N_c + atom_d_eff ∧
  -- (8) Atomic identity: disc = N_W + N_total
  atom_disc = atom_N_W + atom_N_total ∧
  -- (9) Atomic identity: N_total = N_W + N_c
  atom_N_total = atom_N_W + atom_N_c

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: HEADLINE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE ATOMIC-OPERATIONAL DICTIONARY HOLDS.**

    All nine clauses are simultaneously satisfied.  Each clause is
    discharged by `rfl`, by `decide`, or by citation of a LayerB /
    LayerC theorem already in the framework.  No new content is
    introduced. -/
theorem atomicOperationalDictionary_holds : AtomicOperationalDictionary := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) N_W = 2
    rfl
  · -- (2) N_c = 3
    rfl
  · -- (3) singleGenDim = 16
    exact singleGenDim_eq_sixteen
  · -- (4) singleGenDim = dim_spinor_SO10
    exact singleGenDim_eq_spinor
  · -- (5) seesawDim = 126
    exact seesawDim_eq_126
  · -- (6) atom_disc ∣ seesawDim
    exact disc_prime_factor_of_seesawDim
  · -- (7) atom_disc = atom_N_c + atom_d_eff
    exact disc_eq_Nc_plus_d
  · -- (8) atom_disc = atom_N_W + atom_N_total
    exact disc_eq_NW_plus_Ntotal
  · -- (9) atom_N_total = atom_N_W + atom_N_c
    exact Ntotal_eq_NW_plus_Nc

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: PROJECTORS — INDIVIDUAL CLAUSES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Re-export each clause as a standalone theorem for downstream
    citation. -/

/-- (1) `atom_N_W = 2` — qubit Hilbert dimension. -/
theorem dict_NW_eq_two : atom_N_W = 2 := rfl

/-- (2) `atom_N_c = 3` — qutrit Hilbert dimension. -/
theorem dict_Nc_eq_three : atom_N_c = 3 := rfl

/-- (3) `singleGenDim = 16` — single-generation Hilbert dimension. -/
theorem dict_singleGenDim_eq_sixteen : singleGenDim = 16 :=
  singleGenDim_eq_sixteen

/-- (4) `singleGenDim = dim_spinor_SO10` — substrate ↔ SO(10) bridge. -/
theorem dict_singleGenDim_eq_spinor :
    singleGenDim = UnifiedTheory.LayerB.SO10EmbeddingTest.dim_spinor_SO10 :=
  singleGenDim_eq_spinor

/-- (5) `seesawDim = 126` — see-saw subspace dimension. -/
theorem dict_seesawDim_eq_126 : seesawDim = 126 :=
  seesawDim_eq_126

/-- (6) `atom_disc ∣ seesawDim` — discriminant is a prime factor of 126. -/
theorem dict_disc_dvd_seesawDim : atom_disc ∣ seesawDim :=
  disc_prime_factor_of_seesawDim

/-- (7) `atom_disc = atom_N_c + atom_d_eff` — disc = N_c + d_eff. -/
theorem dict_disc_eq_Nc_plus_d_eff : atom_disc = atom_N_c + atom_d_eff :=
  disc_eq_Nc_plus_d

/-- (8) `atom_disc = atom_N_W + atom_N_total` — disc = N_W + N_total. -/
theorem dict_disc_eq_NW_plus_Ntotal : atom_disc = atom_N_W + atom_N_total :=
  disc_eq_NW_plus_Ntotal

/-- (9) `atom_N_total = atom_N_W + atom_N_c` — N_total = N_W + N_c. -/
theorem dict_Ntotal_eq_NW_plus_Nc : atom_N_total = atom_N_W + atom_N_c :=
  Ntotal_eq_NW_plus_Nc

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: NUMERICAL VERIFICATIONS (defensive checks)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Sanity: `2 ∣ 126`. -/
theorem two_dvd_seesawDim : (2 : ℕ) ∣ seesawDim := by
  unfold seesawDim; decide

/-- Sanity: `3 ∣ 126` (via N_c² = 9 ∣ 126). -/
theorem three_dvd_seesawDim : (3 : ℕ) ∣ seesawDim := by
  unfold seesawDim; decide

/-- Sanity: `7 ∣ 126` (the disc clause spelled out). -/
theorem seven_dvd_seesawDim : (7 : ℕ) ∣ seesawDim := by
  unfold seesawDim; decide

/-- Sanity: numerical evaluation `disc = 7`. -/
theorem dict_disc_value : atom_disc = 7 := rfl

/-- Sanity: numerical evaluation `N_total = 5`. -/
theorem dict_Ntotal_value : atom_N_total = 5 := rfl

/-- Sanity: numerical evaluation `d_eff = 4`. -/
theorem dict_d_eff_value : atom_d_eff = 4 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: MASTER STATEMENT (expanded variant)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Restatement of the dictionary as a flat conjunction with the
    numerical values inlined.  Useful when a downstream file needs
    the concrete integers (2, 3, 16, 126, 7) rather than the
    framework names. -/

/-- **Numerical form of the dictionary.**  All nine clauses with the
    framework atoms evaluated to their explicit integer values. -/
theorem atomicOperationalDictionary_numerical :
    atom_N_W = 2 ∧
    atom_N_c = 3 ∧
    atom_N_total = 5 ∧
    atom_d_eff = 4 ∧
    atom_disc = 7 ∧
    singleGenDim = 16 ∧
    seesawDim = 126 ∧
    atom_disc ∣ seesawDim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact singleGenDim_eq_sixteen
  · exact seesawDim_eq_126
  · exact disc_prime_factor_of_seesawDim

end UnifiedTheory.LayerC.AtomicOperationalDictionary
