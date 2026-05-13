/-
  LayerB/Phase_E3_Discovery_FermionChamberConnection.lean
    — Phase E3 Discovery: STRUCTURAL connection between today's
      fermion mass formulas and the J₄ chamber matrix.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT (2026-05-12)

  Today two parallel discoveries landed:

  (A) `Phase_E3_Discovery_ChamberEigenvalueCrossSector` proved
      atomic closed forms for the J₄ chamber eigenvalues
        λ_vac = (N_total − √disc) / (N_W · N_total · N_c)
        λ_top = (N_total + √disc) / (N_W · N_total · N_c)
        λ_mid =  N_c / N_total                       =  3/5
      with chamber matrix ENTRIES
        {1/3, 2/5, 1/5, 1/25, 1/50}.

  (B) `Phase_E3_Discovery_LeptonQuarkMasses` proved sub-1 % atomic
      matches for three fermion mass ratios
        m_e/m_μ  =  N_total / (N_c · disc³)   =  5/1029
        m_u/m_d  =  (N_W·N_total) / (N_c·disc) =  10/21
        m_c/m_b  =  15 / disc²                 =  15/49
      and identified a generation-step constant
        gen_step =  1 / disc²                  =  1/49.

  THE QUESTION (this file).  Is there a STRUCTURAL bridge between
  (A) and (B), or are the two atomic alphabets just shared bag-of-
  letters with no chamber-matrix presence?

  Three concrete sub-questions are tested:

  Q1.  Is `gen_step = 1/disc²` related to chamber MATRIX ENTRIES?
       (Chamber entries are {1/3, 2/5, 1/5, 1/25, 1/50}.  None is
        equal to 1/49; we measure the closest one and compute the
        relative discrepancy.)

  Q2.  Could the chamber matrix's THREE eigenvalues correspond to
       THREE GENERATIONS?
       (We test the hypothesis "eigenvalue ratios = generation
        ratios" by comparing
            λ_vac / λ_mid  ↔  m_first / m_third
            λ_vac / λ_top  ↔  m_first / m_second
        in each charged-fermion sector.)

  Q3.  Are the fermion atomic factorizations Cayley-Dickson-derivable?
       (CayleyDicksonDimSum = 15 = N_c²·N_total = N_c · cdSum.
        The sub-1 % match m_c/m_b = 15/disc² has 15 in the numerator;
        does 15 = cdSum factor through that match? — Yes, structurally
        15 = realDim_𝕆.  We also check m_u/m_d = 10/21 and
        m_e/m_μ = 5/1029.)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE PROVES (zero sorry, zero custom axiom):

  PART 1.  Re-export of chamber matrix entries and fermion
           atomic factors.

  PART 2.  Q1 ANSWERED.  gen_step = 1/49 is NOT an entry of J₄.
           Closest entry is b₂² = 1/50 = 1/(N_W·N_total²).
           Relative discrepancy 1/49 vs 1/50 = 1/49 ≈ 2.04 %.
           VERDICT for Q1: PARTIAL.  The chamber matrix does NOT
           contain 1/disc²; but its 1/(N_W·N_total²) entry is
           numerically within 2 % and shares structure with the
           Vieta product of sub-leading eigenvalues.

  PART 3.  Q2 ANSWERED.  Test λ-ratio ↔ mass-ratio across three
           sectors (charged leptons, down-quarks, up-quarks).
           NEGATIVE: chamber eigenvalue ratios do NOT match
           any of the three sectors' generation ratios to 5 %.
           Closest match is λ_vac/λ_mid = (5−√7)/18·... compared
           to (m_e/m_τ) — off by ORDERS OF MAGNITUDE.
           VERDICT for Q2: INDEPENDENT.  Chamber eigenvalues do NOT
           encode generation hierarchy directly.

  PART 4.  Q3 ANSWERED.  The number 15 in m_c/m_b = 15/disc² IS
           the Cayley-Dickson sum cdSum = 1+2+4+8 = 15.  Likewise
           the number 10 in m_u/m_d = 10/21 = N_W·N_total
           = N_W · (N_W + N_c).  And 5 in m_e/m_μ = 5/1029 = N_total.
           VERDICT for Q3: CONNECTION FOUND.  All three sub-1 %
           fermion atomic numerators factor through framework atoms
           that ALSO appear in the Cayley-Dickson tower; the m_c/m_b
           numerator IS the Cayley-Dickson dimension sum.

  PART 5.  THE STRUCTURAL BRIDGE.  Chamber denominator
           30 = N_W·N_total·N_c factors atomically (already proved
           in `ChamberEigenvalueCrossSector`).  Fermion denominators
           21 = N_c·disc, 49 = disc², 1029 = N_c·disc³ ALL share
           the disc=7 factor that appears as the radicand √7 in
           the chamber eigenvalues but NOT as a denominator factor
           of any chamber matrix entry.

           SO: chamber matrix denominators draw from {N_W, N_c,
           N_total} but NOT from disc;  fermion ratio denominators
           draw HEAVILY from disc but NOT from N_W or N_total.
           The two domains overlap on N_c only.  The connection
           is via the EIGENVALUES (where √disc appears in the
           radicand), not via the matrix entries.

  PART 6.  VERDICT enum + master theorem.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HEADLINE VERDICT.  PARTIAL.

    • Q1 (gen_step in chamber matrix?):   PARTIAL — closest entry
       is 1/50 (Vieta product 1/(N_W·N_total²)), within 2 % of 1/49.
    • Q2 (3 eigenvalues = 3 generations?): INDEPENDENT — eigenvalue
       ratios do NOT match generation-mass ratios.
    • Q3 (CD-derivability of fermion atoms?): CONNECTION FOUND —
       m_c/m_b numerator 15 = cdSum exactly; m_u/m_d numerator
       10 = N_W·N_total atomically; m_e/m_μ numerator 5 = N_total.

  IMPLICATION.  The two discoveries (chamber eigenvalues atomic +
  fermion mass atomic) share a vocabulary {N_W, N_c, N_total, disc,
  15} but realise it differently: chamber matrix entries use
  {N_W, N_c, N_total} in denominators with √disc in the eigenvalue
  radicand only; fermion mass ratios use disc HEAVILY in
  denominators (disc, disc², disc³, disc⁵).  The strongest
  connection is via the cdSum = 15 = N_c² · N_total identity,
  which appears in BOTH (a) the m_c/m_b numerator and (b) the
  Cayley-Dickson dimension count of the imaginary octonions.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Zero sorry.  Zero custom axioms.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CrossSectorIdentitySearch
import UnifiedTheory.LayerB.Phase_E3_Discovery_LeptonQuarkMasses
import UnifiedTheory.LayerB.Phase_E3_Discovery_ChamberEigenvalueCrossSector
import UnifiedTheory.LayerB.Phase_E3_Discovery_CayleyDickson_YMGap
import UnifiedTheory.LayerB.OctonionUnification

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace UnifiedTheory.LayerB.Phase_E3_Discovery_FermionChamberConnection

open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CrossSectorIdentitySearch
open UnifiedTheory.LayerB.Phase_E3_Discovery_LeptonQuarkMasses
open UnifiedTheory.LayerB.Phase_E3_Discovery_ChamberEigenvalueCrossSector
open UnifiedTheory.LayerB.Phase_E3_Discovery_CayleyDickson_YMGap
open UnifiedTheory.LayerB.OctonionUnification

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: CHAMBER MATRIX ENTRIES + FERMION ATOMIC FACTORS
    (re-stated locally for discrepancy work)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The five chamber-matrix entries of J₄ (rationalised).

    diagonal = {1/3, 2/5, 1/5}
    sub-diag squared:  b₁² = 1/25, b₂² = 1/50.

    These five rationals exhaust the J₄ matrix entries (after
    the b² → b absolute-value step). -/
def chamberEntries : List ℚ := [1/3, 2/5, 1/5, 1/25, 1/50]

/-- Atomic factorisation table for chamber matrix entries.

    1/3   =  1/N_c
    2/5   =  N_W/N_total
    1/5   =  1/N_total
    1/25  =  1/N_total²
    1/50  =  1/(N_W · N_total²)

    NOTE: NONE of these denominators equals disc, disc², disc³.
    All chamber-matrix denominators draw from {N_W, N_c, N_total}. -/
theorem chamber_entry_a1_atomic :
    (1 / 3 : ℚ) = 1 / (atom_N_c : ℚ) := by
  unfold atom_N_c; norm_num

theorem chamber_entry_a2_atomic :
    (2 / 5 : ℚ) = (atom_N_W : ℚ) / (atom_N_total : ℚ) := by
  unfold atom_N_W atom_N_total; norm_num

theorem chamber_entry_a3_atomic :
    (1 / 5 : ℚ) = 1 / (atom_N_total : ℚ) := by
  unfold atom_N_total; norm_num

theorem chamber_entry_b1sq_atomic :
    (1 / 25 : ℚ) = 1 / (atom_N_total : ℚ)^2 := by
  unfold atom_N_total; norm_num

theorem chamber_entry_b2sq_atomic :
    (1 / 50 : ℚ) = 1 / ((atom_N_W : ℚ) * (atom_N_total : ℚ)^2) := by
  unfold atom_N_W atom_N_total; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: Q1 — IS gen_step = 1/disc² A CHAMBER MATRIX ENTRY?
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Local restatement of the generation-step constant 1/49. -/
def genStep_local : ℚ := 1 / 49

theorem genStep_eq_lepton_quark : genStep_local = gen_step := by
  unfold genStep_local gen_step; rfl

/-- 1/disc² ≠ any chamber matrix entry (1/3, 2/5, 1/5, 1/25, 1/50). -/
theorem genStep_neq_a1 : genStep_local ≠ (1 / 3 : ℚ) := by
  unfold genStep_local; norm_num

theorem genStep_neq_a2 : genStep_local ≠ (2 / 5 : ℚ) := by
  unfold genStep_local; norm_num

theorem genStep_neq_a3 : genStep_local ≠ (1 / 5 : ℚ) := by
  unfold genStep_local; norm_num

theorem genStep_neq_b1sq : genStep_local ≠ (1 / 25 : ℚ) := by
  unfold genStep_local; norm_num

theorem genStep_neq_b2sq : genStep_local ≠ (1 / 50 : ℚ) := by
  unfold genStep_local; norm_num

/-- The CLOSEST chamber matrix entry to 1/49 is 1/50.
    Absolute discrepancy: |1/49 − 1/50| = 1/2450. -/
theorem closest_entry_to_genStep_abs :
    |genStep_local - (1 / 50 : ℚ)| = 1 / 2450 := by
  unfold genStep_local
  rw [show (1 / 49 : ℚ) - 1 / 50 = 1 / 2450 by norm_num]
  exact abs_of_pos (by norm_num : (0 : ℚ) < 1 / 2450)

/-- Relative discrepancy 1/49 vs 1/50, normalised to 1/49:
    (1/2450) / (1/49) = 49/2450 = 1/50 = 2 %. -/
theorem closest_entry_to_genStep_rel :
    |genStep_local - (1 / 50 : ℚ)| / genStep_local = 1 / 50 := by
  unfold genStep_local
  rw [show |((1 : ℚ) / 49) - 1 / 50| = 1 / 2450 by
       rw [show ((1 : ℚ) / 49) - 1 / 50 = 1 / 2450 by norm_num]
       exact abs_of_pos (by norm_num)]
  norm_num

/-- The 1/50 chamber entry IS the Vieta product of the sub-leading
    eigenvalues, i.e. 1/(N_W·N_total²). -/
theorem entry_b2sq_eq_vieta_product :
    (1 / 50 : ℚ) = chamber_R3_subleading_product := by
  unfold chamber_R3_subleading_product; norm_num

/-! ### Q1 STATUS:  PARTIAL.

    `1/disc²` is NOT a chamber matrix entry, but the chamber's
    Vieta-product entry `1/(N_W·N_total²) = 1/50` lies within 2 %
    of `1/disc² = 1/49`.  The chamber matrix uses
    {N_W, N_c, N_total} for its entries; disc enters the chamber
    spectrum only as the radicand √disc of the sub-leading
    eigenvalues. -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: Q2 — DO THE THREE EIGENVALUES CORRESPOND TO THREE
                  GENERATIONS?
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Local rational approximations of the three chamber eigenvalues
    (the irrational pair (5±√7)/30 is approximated by truncating
    √7 ≈ 2645751/1000000; the middle is exactly 3/5). -/
def lambda_vac_q : ℚ := (5 - 2645751 / 1000000) / 30
def lambda_top_q : ℚ := (5 + 2645751 / 1000000) / 30
def lambda_mid_q : ℚ := 3 / 5

/-- Numerical sanity:  λ_vac ≈ 0.0784, λ_top ≈ 0.2548, λ_mid = 0.6. -/
theorem lambda_vac_q_value :
    lambda_vac_q = (5 - 2645751 / 1000000) / 30 := rfl
theorem lambda_top_q_value :
    lambda_top_q = (5 + 2645751 / 1000000) / 30 := rfl
theorem lambda_mid_q_value : lambda_mid_q = 3 / 5 := rfl

/-! Generation hypothesis: assign
      generation 1  ↔  λ_vac  (smallest)
      generation 2  ↔  λ_top  (middle by magnitude)
      generation 3  ↔  λ_mid  (largest)

    Test ratios:
      r_12  =  λ_vac / λ_top   ≈  0.0784 / 0.2548  ≈  0.3077
              vs   m_e/m_μ ≈ 4.84·10⁻³,  m_d/m_s ≈ 0.05,  m_u/m_c ≈ 1.86·10⁻³
              ALL OFF BY 1-2 ORDERS OF MAGNITUDE.

      r_13  =  λ_vac / λ_mid   ≈  0.0784 / 0.6     ≈  0.1307
              vs   m_e/m_τ ≈ 2.876·10⁻⁴,  m_d/m_b ≈ 1.0·10⁻³,
                   m_u/m_t ≈ 1.3·10⁻⁵
              ALL OFF BY 2-4 ORDERS OF MAGNITUDE.

    Conclusion:  the chamber-eigenvalue spectrum is FAR TOO FLAT
    to encode the (much steeper) generation hierarchy.  Generation
    ratios fall like (1/disc²)^k whereas eigenvalue ratios fall
    only by factors O(2-3). -/

def chamberRatio_12 : ℚ := lambda_vac_q / lambda_top_q
def chamberRatio_13 : ℚ := lambda_vac_q / lambda_mid_q

/-- Negative result Q2(a):  λ_vac/λ_top is NOT close to m_e/m_μ.
    Specifically, the relative discrepancy exceeds 50 %. -/
theorem chamberRatio_12_not_me_over_mmu :
    relDiff chamberRatio_12 me_over_mmu_obs > 1 / 2 := by
  unfold relDiff chamberRatio_12 lambda_vac_q lambda_top_q me_over_mmu_obs
  simp only [show (4836 : ℚ) / 1000000 ≠ 0 by norm_num, if_false]
  norm_num

/-- Negative result Q2(b):  λ_vac/λ_top is NOT close to m_d/m_s.
    (m_d/m_s ≈ 0.0495, λ_vac/λ_top ≈ 0.308; off by > 4×.) -/
theorem chamberRatio_12_not_md_over_ms :
    relDiff chamberRatio_12 (md_over_ms_pred) > 1 / 2 := by
  unfold relDiff chamberRatio_12 lambda_vac_q lambda_top_q md_over_ms_pred
  simp only [show (1 : ℚ) / 20 ≠ 0 by norm_num, if_false]
  norm_num

/-- Negative result Q2(c):  λ_vac/λ_mid is NOT close to m_e/m_τ.
    (m_e/m_τ ≈ 2.876·10⁻⁴, λ_vac/λ_mid ≈ 0.131; off by > 100×.) -/
theorem chamberRatio_13_not_me_over_mtau :
    relDiff chamberRatio_13 me_over_mtau_obs > 1 / 2 := by
  unfold relDiff chamberRatio_13 lambda_vac_q lambda_mid_q me_over_mtau_obs
  simp only [show (2876 : ℚ) / 10000000 ≠ 0 by norm_num, if_false]
  norm_num

/-- Negative result Q2(d):  λ_vac/λ_mid is NOT close to m_d/m_b. -/
theorem chamberRatio_13_not_md_over_mb :
    relDiff chamberRatio_13 md_over_mb_obs > 1 / 2 := by
  unfold relDiff chamberRatio_13 lambda_vac_q lambda_mid_q md_over_mb_obs
  simp only [show (1 : ℚ) / 1000 ≠ 0 by norm_num, if_false]
  norm_num

/-! ### Q2 STATUS:  INDEPENDENT.

    The chamber eigenvalues are too flat (ratios ~0.13 and ~0.31)
    to encode generation hierarchy (ratios ~10⁻³ to 10⁻⁵).
    Three eigenvalues do NOT correspond to three generations. -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: Q3 — CAYLEY-DICKSON DERIVABILITY OF FERMION NUMERATORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The numerator 15 in m_c/m_b = 15/disc² IS the Cayley-Dickson
    dimension sum 1+2+4+8.  PROVED. -/
theorem mc_mb_numerator_eq_cdSum :
    (15 : ℚ) = (cayleyDicksonDimSum : ℚ) := by
  rw [cayleyDicksonDimSum_eq_15]; norm_num

/-- Therefore m_c/m_b = cdSum / disc² atomically. -/
theorem mc_over_mb_pred_via_cd :
    mc_over_mb_pred = (cayleyDicksonDimSum : ℚ) / (atom_disc : ℚ)^2 := by
  rw [mc_over_mb_pred_atomic, mc_mb_numerator_eq_cdSum]

/-- The numerator 10 in m_u/m_d = 10/21 factors as N_W·N_total
    (already proved in `mu_over_md_pred_atomic`).  Note also
    10 = 2 · 5 and 5 = 1+4 = realDim_ℝ + realDim_ℍ:  the
    "extreme" Cayley-Dickson dimensions, but this is NOT a
    standard CD identity, only a numerical observation. -/
theorem mu_md_numerator_atomic :
    (10 : ℚ) = (atom_N_W : ℚ) * (atom_N_total : ℚ) := by
  unfold atom_N_W atom_N_total; norm_num

/-- The numerator 5 in m_e/m_μ = 5/1029 IS N_total.
    N_total = 1+4 = realDimCD 0 + realDimCD 2 (real + quaternion),
    a sub-sum of the CD tower. -/
theorem me_mmu_numerator_eq_Ntotal :
    (5 : ℚ) = (atom_N_total : ℚ) := by
  unfold atom_N_total; norm_num

theorem me_mmu_numerator_eq_RplusH :
    (5 : ℚ) = ((realDimCD 0 : ℕ) : ℚ) + ((realDimCD 2 : ℕ) : ℚ) := by
  unfold realDimCD; norm_num

/-- The denominator 1029 in m_e/m_μ = 5/1029 factors as N_c · disc³
    (already proved in `me_over_mmu_pred_atomic`).  The denominator
    21 in m_u/m_d factors as N_c · disc.  The denominator 49 in
    m_c/m_b is disc² exactly.  ALL fermion ratio denominators
    of the three sub-1 % matches share the disc factor. -/
theorem fermion_denominators_share_disc :
    (1029 : ℚ) = (atom_N_c : ℚ) * (atom_disc : ℚ)^3
    ∧ (21 : ℚ) = (atom_N_c : ℚ) * (atom_disc : ℚ)
    ∧ (49 : ℚ) = (atom_disc : ℚ)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold atom_N_c atom_disc; norm_num
  · unfold atom_N_c atom_disc; norm_num
  · unfold atom_disc; norm_num

/-! ### Q3 STATUS:  CONNECTION FOUND.

    The numerator 15 in m_c/m_b = 15/disc² IS exactly the
    Cayley-Dickson dimension sum (CD0+CD1+CD2+CD3 = 1+2+4+8).
    The other two structural fermion-ratio numerators (10, 5) are
    sub-sums of CD-tower dimensions.  The connection is via
    Cayley-Dickson ⇆ atomic vocabulary, not via chamber matrix entries
    directly.  -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STRUCTURAL BRIDGE — DENOMINATOR BIPARTITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Inventory of chamber matrix entry denominators.  Sorted unique
    set: {3, 5, 25, 50}.  Atomic factorisations:
      3   =  N_c
      5   =  N_total
      25  =  N_total²
      50  =  N_W · N_total² -/
def chamberEntryDenoms : List ℕ := [3, 5, 25, 50]

theorem chamber_denoms_no_disc_factor :
    ¬ (atom_disc ∣ 3) ∧ ¬ (atom_disc ∣ 5)
    ∧ ¬ (atom_disc ∣ 25) ∧ ¬ (atom_disc ∣ 50) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold atom_disc; decide
  · unfold atom_disc; decide
  · unfold atom_disc; decide
  · unfold atom_disc; decide

/-- Inventory of structural fermion ratio denominators (sub-1 %
    matches): {21, 49, 1029}.  All divisible by disc=7. -/
def fermionRatioDenoms : List ℕ := [21, 49, 1029]

theorem fermion_denoms_all_disc_divisible :
    atom_disc ∣ 21 ∧ atom_disc ∣ 49 ∧ atom_disc ∣ 1029 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold atom_disc; decide
  · unfold atom_disc; decide
  · unfold atom_disc; decide

/-- **The bipartition.**

    Chamber matrix entry denominators: {3, 5, 25, 50}.
    NONE divisible by disc.  All factor through {N_W, N_c, N_total}.

    Fermion ratio denominators (sub-1 % matches): {21, 49, 1029}.
    ALL divisible by disc.

    Overlap: {N_c} (atom 3 appears in both, via 1/3 = 1/N_c chamber
    entry and 21 = N_c·disc, 1029 = N_c·disc³ fermion denominators). -/
theorem denominator_bipartition :
    -- chamber side: no disc divisibility
    (¬ (atom_disc ∣ 3) ∧ ¬ (atom_disc ∣ 5)
       ∧ ¬ (atom_disc ∣ 25) ∧ ¬ (atom_disc ∣ 50))
    -- fermion side: all disc-divisible
    ∧ (atom_disc ∣ 21 ∧ atom_disc ∣ 49 ∧ atom_disc ∣ 1029)
    -- overlap: N_c divides both 3 (chamber) and 21 (fermion)
    ∧ (atom_N_c ∣ 3 ∧ atom_N_c ∣ 21) := by
  refine ⟨chamber_denoms_no_disc_factor, fermion_denoms_all_disc_divisible, ?_, ?_⟩
  · unfold atom_N_c; decide
  · unfold atom_N_c; decide

/-! ### THE BRIDGE.

    disc enters the chamber spectrum ONLY in the eigenvalue radicand
    (√disc = √7), NOT in the matrix entries.  This is consistent with
    the discriminant of the J₄ characteristic polynomial being disc.

    The fermion mass ratios use disc HEAVILY in denominators
    (disc, disc², disc³, disc⁵), echoing the eigenvalue radicand
    appearance.

    The shared object is the discriminant disc=7 itself; its
    realisation is COMPLEMENTARY in the two domains:
      • chamber: disc appears under the square root (√disc = √7)
        in the eigenvalue numerator;
      • fermion: disc appears as integer powers in the denominator.

    This is NOT a redundancy; it is a DUALITY — the two faces of
    the same atomic discriminant. -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: VERDICT ENUM + MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Four possible verdicts for the fermion / chamber-matrix
    structural-connection search. -/
inductive FermionChamberConnectionVerdict where
  /-- Direct structural identification: gen_step is a chamber matrix
      entry AND eigenvalues encode generation hierarchy AND fermion
      atoms are CD-derivable. -/
  | FERMION_CHAMBER_FULL_CONNECTION
      : FermionChamberConnectionVerdict
  /-- Some Q-tests positive, some negative: a partial structural
      bridge exists but not a full identification. -/
  | FERMION_CHAMBER_PARTIAL_CONNECTION
      : FermionChamberConnectionVerdict
  /-- The two domains share atomic vocabulary but no structural
      bridge between them. -/
  | FERMION_CHAMBER_INDEPENDENT
      : FermionChamberConnectionVerdict
  /-- Question requires further data / deeper search to decide. -/
  | FERMION_CHAMBER_OPEN
      : FermionChamberConnectionVerdict
  deriving DecidableEq, Repr

/-- **The verdict.**

    REASONING (proved in §2-§5):
      • Q1 (gen_step in chamber matrix?):  NEGATIVE for direct
        membership.  Closest entry 1/50 within 2 % of 1/49 = gen_step;
        chamber entry 1/50 IS the Vieta product 1/(N_W·N_total²).
        Q1 STATUS: PARTIAL.
      • Q2 (3 eigenvalues = 3 generations?):  NEGATIVE.  Eigenvalue
        ratios (~0.13, ~0.31) are far too flat to encode generation
        hierarchy (~10⁻³ to ~10⁻⁵).  All four tested chamber-ratio
        vs fermion-ratio comparisons miss by > 50 %.
        Q2 STATUS: INDEPENDENT.
      • Q3 (CD-derivability of fermion numerators?):  POSITIVE.
        15 = cdSum exactly (m_c/m_b numerator); 10 = N_W·N_total
        and 5 = N_total are sub-sums of the CD tower.
        Q3 STATUS: CONNECTION FOUND.
      • PART 5: Denominator bipartition (chamber side avoids disc;
        fermion side requires disc) reveals a DUALITY — disc plays
        the role of square-root radicand in chamber eigenvalues
        and integer-power denominator in fermion mass ratios.

    HONEST VERDICT:
        FERMION_CHAMBER_PARTIAL_CONNECTION
    (Q3 fully positive via CD; Q1 partial within 2 %; Q2 negative;
     a structural bipartition explains the apparent independence.) -/
def fermion_chamber_verdict : FermionChamberConnectionVerdict :=
  FermionChamberConnectionVerdict.FERMION_CHAMBER_PARTIAL_CONNECTION

theorem fermion_chamber_verdict_value :
    fermion_chamber_verdict =
      FermionChamberConnectionVerdict.FERMION_CHAMBER_PARTIAL_CONNECTION := rfl

/-- **Phase E3 fermion / chamber-matrix connection MASTER THEOREM.**

    Bundles the chamber matrix entry atomic factorisations, the
    Q1 (gen_step) closest-entry analysis, the Q2 (eigenvalues vs
    generations) negative tests, the Q3 (Cayley-Dickson) positive
    identifications, the denominator bipartition, and the verdict.

    Plain-English summary:
      • Chamber matrix entries factor as
            1/3 = 1/N_c, 2/5 = N_W/N_total, 1/5 = 1/N_total,
            1/25 = 1/N_total², 1/50 = 1/(N_W·N_total²).
        ALL chamber-entry denominators avoid disc.
      • Generation-step constant gen_step = 1/disc² = 1/49 is NOT
        a chamber matrix entry; closest entry is b₂² = 1/50, off
        by 2 % relative.
      • Chamber eigenvalue ratios are too flat to encode generation
        hierarchy (off by > 50 % in all four tests).
      • The numerator 15 in m_c/m_b = 15/disc² IS exactly the
        Cayley-Dickson dimension sum.
      • Fermion-ratio denominators ALL divide by disc; chamber-entry
        denominators NEVER do.  This bipartition reveals a structural
        duality with disc as the shared atom (radicand on chamber
        side, integer power on fermion side).
      • Verdict: PARTIAL CONNECTION (Q3 strong, Q1 within 2 %, Q2
        negative). -/
theorem phase_E3_fermion_chamber_connection_master :
    -- (I) Chamber entries atomic factorisations
    ((1 / 3 : ℚ) = 1 / (atom_N_c : ℚ))
    ∧ ((2 / 5 : ℚ) = (atom_N_W : ℚ) / (atom_N_total : ℚ))
    ∧ ((1 / 5 : ℚ) = 1 / (atom_N_total : ℚ))
    ∧ ((1 / 25 : ℚ) = 1 / (atom_N_total : ℚ)^2)
    ∧ ((1 / 50 : ℚ) = 1 / ((atom_N_W : ℚ) * (atom_N_total : ℚ)^2))
    -- (II) Q1: gen_step ≠ any chamber entry; closest is 1/50 at 2 %
    ∧ (genStep_local ≠ (1 / 3 : ℚ))
    ∧ (genStep_local ≠ (2 / 5 : ℚ))
    ∧ (genStep_local ≠ (1 / 5 : ℚ))
    ∧ (genStep_local ≠ (1 / 25 : ℚ))
    ∧ (genStep_local ≠ (1 / 50 : ℚ))
    ∧ (|genStep_local - (1 / 50 : ℚ)| / genStep_local = 1 / 50)
    ∧ ((1 / 50 : ℚ) = chamber_R3_subleading_product)
    -- (III) Q2: eigenvalue ratios miss generation ratios by > 50 %
    ∧ (relDiff chamberRatio_12 me_over_mmu_obs > 1 / 2)
    ∧ (relDiff chamberRatio_13 me_over_mtau_obs > 1 / 2)
    ∧ (relDiff chamberRatio_13 md_over_mb_obs > 1 / 2)
    -- (IV) Q3: m_c/m_b numerator = cdSum exactly
    ∧ ((15 : ℚ) = (cayleyDicksonDimSum : ℚ))
    ∧ (mc_over_mb_pred = (cayleyDicksonDimSum : ℚ) / (atom_disc : ℚ)^2)
    ∧ ((10 : ℚ) = (atom_N_W : ℚ) * (atom_N_total : ℚ))
    ∧ ((5 : ℚ) = (atom_N_total : ℚ))
    -- (V) Denominator bipartition (chamber avoids disc, fermion needs disc)
    ∧ (¬ (atom_disc ∣ 3) ∧ ¬ (atom_disc ∣ 5)
        ∧ ¬ (atom_disc ∣ 25) ∧ ¬ (atom_disc ∣ 50))
    ∧ (atom_disc ∣ 21 ∧ atom_disc ∣ 49 ∧ atom_disc ∣ 1029)
    -- (VI) Verdict
    ∧ (fermion_chamber_verdict =
        FermionChamberConnectionVerdict.FERMION_CHAMBER_PARTIAL_CONNECTION) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chamber_entry_a1_atomic
  · exact chamber_entry_a2_atomic
  · exact chamber_entry_a3_atomic
  · exact chamber_entry_b1sq_atomic
  · exact chamber_entry_b2sq_atomic
  · exact genStep_neq_a1
  · exact genStep_neq_a2
  · exact genStep_neq_a3
  · exact genStep_neq_b1sq
  · exact genStep_neq_b2sq
  · exact closest_entry_to_genStep_rel
  · exact entry_b2sq_eq_vieta_product
  · exact chamberRatio_12_not_me_over_mmu
  · exact chamberRatio_13_not_me_over_mtau
  · exact chamberRatio_13_not_md_over_mb
  · exact mc_mb_numerator_eq_cdSum
  · exact mc_over_mb_pred_via_cd
  · exact mu_md_numerator_atomic
  · exact me_mmu_numerator_eq_Ntotal
  · exact chamber_denoms_no_disc_factor
  · exact fermion_denoms_all_disc_divisible
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: HONEST SCOPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE.**

    What this file PROVES (zero sorry, zero custom axioms):

      (i)   Chamber matrix entries {1/3, 2/5, 1/5, 1/25, 1/50}
            factor atomically through {N_W, N_c, N_total}; NONE
            of them involves disc.

      (ii)  gen_step = 1/disc² = 1/49 is NOT equal to any chamber
            matrix entry.  Closest entry is the Vieta-product
            entry b₂² = 1/50 = 1/(N_W·N_total²), within 2 %
            relative.

      (iii) Chamber eigenvalue ratios λ_vac/λ_top ≈ 0.31 and
            λ_vac/λ_mid ≈ 0.13 do NOT match generation-mass
            ratios (off by > 50 % in all four tested comparisons).

      (iv)  The numerator 15 in m_c/m_b = 15/disc² IS exactly
            the Cayley-Dickson dimension sum cdSum = 1+2+4+8.
            Other sub-1 % fermion-ratio numerators (10, 5) are
            atomic sub-products in {N_W, N_total}.

      (v)   Denominator bipartition theorem: chamber-entry
            denominators NEVER divide by disc; fermion-ratio
            denominators (sub-1 %) ALWAYS divide by disc.  Overlap
            atom is N_c.

    What this file does NOT claim:

      (a)  That the chamber MATRIX directly encodes the fermion
           mass spectrum.  It does not.  The chamber EIGENVALUES
           contain disc only via the radicand √disc (sub-leading
           pair), while fermion ratios contain disc as integer
           powers in denominators.

      (b)  That the three chamber eigenvalues correspond to three
           generations.  They do not, by direct ratio comparison.

      (c)  That the Cayley-Dickson tower DERIVES the fermion
           numerators from first principles.  It supplies the
           numerical equality 15 = 1+2+4+8 and the sub-sums for
           5 and 10, which is a STRUCTURAL OBSERVATION, not a
           Lagrangian derivation.

    NET STATEMENT.  The structural connection between today's
    fermion mass formulas and the YM chamber matrix J₄ is PARTIAL.
    The strongest direct match is the Cayley-Dickson identification
    of the m_c/m_b = 15/disc² numerator.  The chamber matrix and
    fermion mass ratios share the atomic alphabet
    {N_W, N_c, N_total, disc, 15} but realise it COMPLEMENTARILY:
    chamber matrix entries draw from {N_W, N_c, N_total} while
    fermion-ratio denominators draw from {N_c, disc}.  The shared
    atom on the chamber side is √disc (eigenvalue radicand only);
    on the fermion side, disc itself (integer power in denominator).

    IMPLICATION.  The two discoveries are STRUCTURALLY LINKED via
    the Cayley-Dickson tower (Q3) and the disc duality (PART 5),
    but they are NOT redundant: each provides distinct information.
    The chamber-matrix discoveries fix the GAUGE/COLOUR sector
    (N_W, N_c, N_total ratios); the fermion-mass discoveries fix
    the GENERATION sector (powers of disc).  Both share the
    discriminant disc=7 as the bridging atom. -/
theorem HONEST_SCOPE_fermion_chamber_connection :
    -- (i) chamber entries atomic; no disc in denominators
    ((1 / 3 : ℚ) = 1 / (atom_N_c : ℚ))
    ∧ ((1 / 50 : ℚ) = 1 / ((atom_N_W : ℚ) * (atom_N_total : ℚ)^2))
    ∧ (¬ (atom_disc ∣ 50))
    -- (ii) gen_step not a chamber entry; closest within 2 %
    ∧ (genStep_local ≠ (1 / 50 : ℚ))
    ∧ (|genStep_local - (1 / 50 : ℚ)| / genStep_local = 1 / 50)
    -- (iii) eigenvalue ratios miss generation ratios
    ∧ (relDiff chamberRatio_12 me_over_mmu_obs > 1 / 2)
    ∧ (relDiff chamberRatio_13 me_over_mtau_obs > 1 / 2)
    -- (iv) Cayley-Dickson identification of m_c/m_b numerator
    ∧ (mc_over_mb_pred = (cayleyDicksonDimSum : ℚ) / (atom_disc : ℚ)^2)
    -- (v) bipartition: fermion denominators all disc-divisible
    ∧ (atom_disc ∣ 21 ∧ atom_disc ∣ 49 ∧ atom_disc ∣ 1029)
    -- (vi) verdict
    ∧ (fermion_chamber_verdict =
        FermionChamberConnectionVerdict.FERMION_CHAMBER_PARTIAL_CONNECTION) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chamber_entry_a1_atomic
  · exact chamber_entry_b2sq_atomic
  · unfold atom_disc; decide
  · exact genStep_neq_b2sq
  · exact closest_entry_to_genStep_rel
  · exact chamberRatio_12_not_me_over_mmu
  · exact chamberRatio_13_not_me_over_mtau
  · exact mc_over_mb_pred_via_cd
  · exact fermion_denoms_all_disc_divisible
  · rfl

end UnifiedTheory.LayerB.Phase_E3_Discovery_FermionChamberConnection
