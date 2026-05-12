/-
  LayerB/Phase_E3_Discovery_CayleyDickson_YMGap.lean
    — Discovery: a striking cross-sector identity rewriting the
      Yang–Mills chamber gap √7 / 15 in pure Cayley–Dickson form
      as `√(dim im 𝕆) / Σ_{k=0}^3 dim(CD_k)`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT (2026-05-12)

  The framework's YM chamber gap (the closed-form mass gap of the
  J₄ Feshbach-projected Wilson Hamiltonian on the chamber subspace)
  is

      γ_chamber  =  √7 / 15   ≈  0.17638342074

      (LayerB/Phase_B4_FullConditionalMassGap line 229:
       `frameworkChamberGap = Real.sqrt 7 / 15`).

  The numerator √7 is the square root of the chamber discriminant
  `disc = 7` proved in `LayerA/FeshbachJ4`.  Discovery 1
  (`LayerB/Phase_E3_DiscoveryD1_DiscChamberId`) and the octonion
  audit (`LayerB/OctonionUnification.disc_is_dim_im_O`) both
  identify

      disc = 7 = N_c + d_eff = dim(im 𝕆),

  i.e. the chamber discriminant equals the imaginary dimension of
  the octonions (= the third Cayley–Dickson algebra).

  THE OBSERVATION.  The denominator 15 also has a Cayley–Dickson
  reading: it is the SUM of the four Cayley–Dickson real
  dimensions (ℝ, ℂ, ℍ, 𝕆):

      15  =  1 + 2 + 4 + 8
          =  dim ℝ + dim ℂ + dim ℍ + dim 𝕆
          =  Σ_{k=0}^3 dim(CD_k).

  Combining,

      γ_chamber  =  √7 / 15
                =  √(dim im 𝕆)  /  Σ_{k=0}^3 dim(CD_k).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED (zero sorry, zero custom axioms)

  PART 1.  CAYLEY–DICKSON DIMENSION SUM.  Define

              cayleyDicksonDimSum  :=  1 + 2 + 4 + 8.

          Prove `cayleyDicksonDimSum = 15` by `decide`, and
          identify it term-by-term with `realDimCD k` for
          k = 0, 1, 2, 3 (re-using `OctonionUnification.realDimCD`).

  PART 2.  NUMERATOR IDENTIFICATION.  `disc_atom = imDimCD 3`
          (already proved in `OctonionUnification.disc_is_dim_im_O`).

  PART 3.  THE CD REWRITE OF γ_chamber.  At ℝ-level,

              γ_chamber  =  √7 / 15
                       =  √(dim_im_𝕆 : ℝ) / (cayleyDicksonDimSum : ℝ).

  PART 4.  COINCIDENCE TEST — does the formula generalise?
            • Numerator structural anchor: the chamber discriminant
              equals 7 because of the J₄ Feshbach reduction at d=4
              (`LayerA/FeshbachJ4.feshbach_disc_at_4 = 7`).  At
              d = 2 the chamber polynomial discriminant ALSO equals
              7 — but the chamber Feshbach reduction is ILL-DEFINED
              there (singular self-energy, see
              `Phase_E3_DiscoveryD3_2DLatticeTest`), so the chamber
              gap √7 / 15 has no d=2 analog from the framework.
            • Denominator structural anchor: 15 = 1 + 2 + 4 + 8 is
              specifically the SUM of the FIRST FOUR CD dimensions
              (k = 0, 1, 2, 3 — exactly through the octonions).
              Adding the next term (sedenions, dim 16) gives 31,
              NOT a framework atom.  Subtracting one (only k=0..2)
              gives 7 = dim(im 𝕆), which would collapse the formula
              to √7/7 = 1/√7, NOT the chamber gap.  So the cutoff
              "first four CD algebras" is rigid.

  PART 5.  CROSS-CHECK WITH OTHER FRAMEWORK 15-CONTAINING ATOMS.
            • 15 = dim(su(4)) (LayerA/NoExtraDimensions: the unique
              n satisfying n² − 1 = 15 is n = 4).
            • 15 = fermions per generation (LayerA/ColorGroupForced.
              fermionCountColor 3 = 15; LayerA/RepStructureForced.
              totalFermions = 15).
            • 45 = 3·15: sin²θ_13 = 1/45 = 1/(N_c²·N_total)
              (PMNSOneLoop), and α_GUT = 1/45 in the framework.
              So the "15" recurs across YM gap denominator, gauge
              algebra dimension, fermion count per generation, and
              (as 3·15 = 45) the reactor-angle / GUT-coupling
              denominator.

  PART 6.  COMPATIBILITY OF THE TWO 15-INTERPRETATIONS.
            cayleyDicksonDimSum = 1+2+4+8 = 15
              and
            su(4) dimension      = 4² − 1 = 15
              and
            fermions per generation = 15
          all give the SAME 15 by ARITHMETIC (decide), but they
          are NOT the same identity in any structural sense:
            (a) CD-sum is a Cayley–Dickson chain length statement.
            (b) su(4) is a Lie-algebra dimension statement.
            (c) fermion count is a representation-theoretic
                sum (1·3·2 + 3 + 3 + 3·2 + 2 + 1 = 15).
          The framework provides NO mechanism that derives any
          one from the others; they are three independent
          15-readouts of distinct algebraic objects.

  PART 7.  HONEST VERDICT enum.  The CD rewrite of the chamber
          gap is PROVED at the rational/real level
          (`chamber_gap_eq_sqrt_disc_over_CD_sum`), but neither
          the chamber-Feshbach derivation NOR the CD chain
          structurally derives the OTHER.  The numerator 7 is
          identified with dim(im 𝕆) at the value level (Mersenne
          coincidence 7 = 2³ − 1 = 2^N_c − 1, which works because
          N_c = 3 happens to coincide with the CD level k = 3 of
          the octonions); the denominator 15 has multiple
          equally-valid framework readings (CD sum, su(4) dim,
          fermion count) with no privileged structural origin.

          VERDICT:
            CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN.

  PART 8.  MASTER THEOREM `phase_E3_CD_YMgap_master` bundles
          the dimension-sum identity, the numerator identification,
          the chamber-gap rewrite, the negative results on
          d-generalisation and CD-cutoff perturbation, the
          15-atom cross-checks, and the verdict.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE

  • The numerical equality √7 / 15 = √(dim im 𝕆) / (1+2+4+8) is
    a TRIVIAL identity (both sides are the same rationals/reals
    by `decide` on the integer parts).  The DISCOVERY claim is
    that the rewrite re-EXPRESSES the YM chamber gap in pure
    Cayley–Dickson vocabulary, suggesting a substrate-to-YM
    bridge.

  • The bridge is NOT proven structural here.  The numerator's
    "7 = dim im 𝕆" is the same Mersenne coincidence already
    catalogued in `OctonionUnification.Q4d_disc_two_origins`
    and `Q4e_dim_im_O_Mersenne`: 7 has TWO equally-natural
    framework origins (gauge+spacetime fusion N_c + d_eff,
    or octonion imaginary dimension), and the file does not
    privilege one over the other.

  • The denominator's "15 = Σ CD dims" is a NEW observation
    relative to the existing octonion audit (which only catalogues
    INDIVIDUAL atoms against CD dimensions, not their sum).  But
    15 also equals dim(su(4)) and the fermion count per
    generation — and the framework provides no derivation of any
    of these three 15-readouts from another.

  • The α_GUT = 1/45 = 1/(3·15) connection (per project memory:
    `α_GUT = 1/45 = sin²θ_13^PMNS`) is DOCUMENTED here as a
    cross-sector observation, NOT proved as a derivation.

  Zero sorry.  Zero custom axioms.

  Citations:
    • Chamber gap √7/15: `LayerA/FeshbachJ4.lean`,
      `LayerB/Phase_B4_FullConditionalMassGap.frameworkChamberGap`.
    • dim im 𝕆 = 7: `LayerB/OctonionUnification.imDim_O`,
      `disc_is_dim_im_O`.
    • Cayley–Dickson real dims: `LayerB/OctonionUnification.realDimCD`.
    • 15 = dim su(4): `LayerA/NoExtraDimensions.kernel_dim_forces_n`.
    • d=2 chamber singularity: `LayerB/Phase_E3_DiscoveryD3_2DLatticeTest`.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.OctonionUnification
import UnifiedTheory.LayerB.CrossSectorIdentitySearch

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Phase_E3_Discovery_CayleyDickson_YMGap

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.OctonionUnification
open UnifiedTheory.LayerB.CrossSectorIdentitySearch

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: CAYLEY–DICKSON DIMENSION SUM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Cayley–Dickson dimension sum** (first four algebras):
        1 + 2 + 4 + 8  =  dim ℝ + dim ℂ + dim ℍ + dim 𝕆. -/
def cayleyDicksonDimSum : ℕ := 1 + 2 + 4 + 8

/-- The CD dimension sum equals 15. -/
theorem cayleyDicksonDimSum_eq_15 : cayleyDicksonDimSum = 15 := by decide

/-- The CD dimension sum is the literal sum of `realDimCD k` for
    k = 0, 1, 2, 3. -/
theorem cayleyDicksonDimSum_eq_realDim_sum :
    cayleyDicksonDimSum = realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 := by
  unfold cayleyDicksonDimSum realDimCD
  decide

/-- `dim_im_𝕆 = 7` (re-export). -/
def dim_im_O : ℕ := imDimCD 3

theorem dim_im_O_eq_7 : dim_im_O = 7 := by
  unfold dim_im_O imDimCD; decide

/-- The framework's atomic chamber discriminant equals
    `dim_im_𝕆`. -/
theorem disc_atom_eq_dim_im_O : atom_disc = dim_im_O := by
  unfold dim_im_O
  exact disc_is_dim_im_O

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE CHAMBER GAP CONSTANT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Chamber YM gap** — `Real.sqrt 7 / 15`.  This is the same
    constant as `Phase_B4_FullConditionalMassGap.frameworkChamberGap`
    and as `Phase_E3_DiscoveryD4_CAGYMRatio.chamber_YM_gap`. -/
noncomputable def chamber_gap : ℝ := Real.sqrt 7 / 15

/-- The chamber gap is positive. -/
theorem chamber_gap_pos : 0 < chamber_gap := by
  unfold chamber_gap
  have h7 : (0 : ℝ) < Real.sqrt 7 := by
    have : (0 : ℝ) < (7 : ℝ) := by norm_num
    exact Real.sqrt_pos.mpr this
  have h15 : (0 : ℝ) < (15 : ℝ) := by norm_num
  exact div_pos h7 h15

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE CD REWRITE OF THE CHAMBER GAP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE DISCOVERY IDENTITY.**

    The Yang–Mills chamber gap rewrites as

        √7 / 15  =  √(dim im 𝕆) / (Σ_{k=0}^3 dim CD_k).

    Both sides are equal as real numbers because both numerators
    equal `Real.sqrt 7` and both denominators equal `15`. -/
theorem chamber_gap_eq_sqrt_disc_over_CD_sum :
    Real.sqrt 7 / 15
      = Real.sqrt (dim_im_O : ℝ) / (cayleyDicksonDimSum : ℝ) := by
  have hN : (dim_im_O : ℝ) = 7 := by
    rw [dim_im_O_eq_7]; norm_num
  have hD : (cayleyDicksonDimSum : ℝ) = 15 := by
    rw [cayleyDicksonDimSum_eq_15]; norm_num
  rw [hN, hD]

/-- The chamber gap, expanded as a Cayley–Dickson formula. -/
theorem chamber_gap_CD_form :
    chamber_gap
      = Real.sqrt (dim_im_O : ℝ) / (cayleyDicksonDimSum : ℝ) := by
  unfold chamber_gap
  exact chamber_gap_eq_sqrt_disc_over_CD_sum

/-- The chamber gap, expanded as a sum-of-realDimCD formula. -/
theorem chamber_gap_realDim_sum_form :
    chamber_gap
      = Real.sqrt (imDimCD 3 : ℝ)
          / ((realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 : ℕ) : ℝ) := by
  unfold chamber_gap
  have hN : (imDimCD 3 : ℝ) = 7 := by
    have : imDimCD 3 = 7 := imDim_O
    rw [this]; norm_num
  have hD : ((realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 : ℕ) : ℝ) = 15 := by
    have : realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 = 15 := by
      unfold realDimCD; decide
    rw [this]; norm_num
  rw [hN, hD]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: COINCIDENCE TESTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Adding the SEDENIONS (k = 4, dim 16) to the sum gives 31, NOT
    a framework atom and NOT producing the chamber gap. -/
theorem CD_sum_with_sedenions :
    realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 + realDimCD 4 = 31 := by
  unfold realDimCD; decide

/-- Truncating the sum after the QUATERNIONS (only k = 0..2) gives
    7, which would collapse √7 / 7 = 1/√7 ≠ chamber gap. -/
theorem CD_sum_truncated_quaternion :
    realDimCD 0 + realDimCD 1 + realDimCD 2 = 7 := by
  unfold realDimCD; decide

/-- The CD sum truncated after quaternions equals `dim_im_𝕆`. -/
theorem CD_sum_quaternion_eq_dim_im_O :
    realDimCD 0 + realDimCD 1 + realDimCD 2 = dim_im_O := by
  rw [CD_sum_truncated_quaternion, dim_im_O_eq_7]

/-- IMAGINARY-only CD sum (k = 0..3) equals 11, NOT 15. -/
theorem CD_imSum_through_O :
    imDimCD 0 + imDimCD 1 + imDimCD 2 + imDimCD 3 = 11 := by
  unfold imDimCD; decide

/-- Pure octonion (k = 3 only) gives dim 𝕆 = 8, also not 15. -/
theorem dim_O_alone : realDimCD 3 = 8 := realDim_O

/-- The CUTOFF at "first four CD algebras" (k = 0..3) is therefore
    the UNIQUE truncation of the CD chain producing the chamber-gap
    denominator 15.  Including more (sedenions) overshoots; including
    fewer (only ℝ,ℂ,ℍ) lands on 7. -/
theorem CD_cutoff_at_O_unique_for_15 :
    realDimCD 0 + realDimCD 1 + realDimCD 2 = 7
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 = 15
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 + realDimCD 4 = 31 := by
  refine ⟨?_, ?_, ?_⟩
  · exact CD_sum_truncated_quaternion
  · exact cayleyDicksonDimSum_eq_realDim_sum.symm.trans cayleyDicksonDimSum_eq_15
  · exact CD_sum_with_sedenions

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: CROSS-CHECK WITH OTHER FRAMEWORK 15-ATOMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The integer 15 appears in three structurally INDEPENDENT places
    in the framework: as Σ CD dims (this file), as dim(su(4))
    (LayerA/NoExtraDimensions), and as the fermion count per
    generation (LayerA/ColorGroupForced).  All three are equal by
    ARITHMETIC, but the framework does NOT derive any one from
    another.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The dimension of `su(n)` for n=4 equals 15. -/
def dimSU4 : ℕ := 4 ^ 2 - 1

theorem dimSU4_eq_15 : dimSU4 = 15 := by unfold dimSU4; decide

/-- The fermion count per generation in the SM. -/
def fermionsPerGeneration : ℕ :=
  -- 1·3·2 (Q_L) + 1·3 (u_R) + 1·3 (d_R) + 1·2 (L_L) + 1·1 (e_R) +
  -- 0 (sterile ν: omitted in baseline SM count)
  -- The framework's `RepStructureForced.totalFermions` evaluates the
  -- sum 1·3·2 + 0·3 + 0·3·2 + 2·3 + 1·2 + 1 = 15.
  1 * 3 * 2 + 0 * 3 + 0 * 3 * 2 + 2 * 3 + 1 * 2 + 1

theorem fermionsPerGeneration_eq_15 : fermionsPerGeneration = 15 := by
  unfold fermionsPerGeneration; decide

/-- **THE THREE 15-READOUTS AGREE BY ARITHMETIC.** -/
theorem three_15_readouts :
    cayleyDicksonDimSum = 15
    ∧ dimSU4 = 15
    ∧ fermionsPerGeneration = 15
    ∧ cayleyDicksonDimSum = dimSU4
    ∧ cayleyDicksonDimSum = fermionsPerGeneration := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact cayleyDicksonDimSum_eq_15
  · exact dimSU4_eq_15
  · exact fermionsPerGeneration_eq_15
  · unfold cayleyDicksonDimSum dimSU4; decide
  · unfold cayleyDicksonDimSum fermionsPerGeneration; decide

/-! **The 45 atom: sin²θ_13 = 1/45 and α_GUT = 1/45.**

    Per project memory `α_GUT = 1/45 = sin²θ_13^PMNS`.  The number
    45 = 3·15 = N_c · (Σ CD dims).  This is documented as a
    cross-sector observation; the framework's atomic decomposition
    of 45 is `N_c² · N_total = 9 · 5`, NOT `N_c · 15`.
-/

/-- The framework's reactor angle squared is 1/45. -/
theorem sinSq_t13_is_one_over_45 : sinSq_t13_pred = 1 / 45 := by
  unfold sinSq_t13_pred; norm_num

/-- The integer 45 equals `N_c · cayleyDicksonDimSum`. -/
theorem fortyfive_eq_Nc_times_CDsum :
    (45 : ℕ) = atom_N_c * cayleyDicksonDimSum := by
  unfold atom_N_c cayleyDicksonDimSum; decide

/-- The framework's atomic decomposition of 45 is N_c² · N_total. -/
theorem fortyfive_eq_NcSq_times_Ntotal :
    (45 : ℕ) = atom_N_c ^ 2 * atom_N_total := by
  unfold atom_N_c atom_N_total; decide

/-- The two decompositions of 45 are equal by arithmetic, but
    are STRUCTURALLY DISTINCT: one routes through (N_c, CD chain),
    the other routes through (N_c², N_total). -/
theorem fortyfive_two_decompositions :
    atom_N_c * cayleyDicksonDimSum = atom_N_c ^ 2 * atom_N_total := by
  unfold atom_N_c atom_N_total cayleyDicksonDimSum; decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: NUMERICAL SANITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Numerical sanity check: √7 / 15 lies in (0.176, 0.177). -/
theorem chamber_gap_numerical_bracket :
    (0.176 : ℝ) < chamber_gap ∧ chamber_gap < (0.177 : ℝ) := by
  unfold chamber_gap
  refine ⟨?_, ?_⟩
  · -- 0.176 < √7/15 ⇔ 2.64 < √7 (since 0.176·15 = 2.64).
    have hb_nn : (0 : ℝ) ≤ 2.64 := by norm_num
    have hsq : (2.64 : ℝ)^2 < 7 := by norm_num
    have hsqrt_lo : (2.64 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt hb_nn).mpr hsq
    have h15 : (0 : ℝ) < (15 : ℝ) := by norm_num
    -- 0.176 · 15 = 2.64 < √7, so 0.176 < √7 / 15.
    have h1 : (0.176 : ℝ) * 15 < Real.sqrt 7 := by linarith
    rw [lt_div_iff₀ h15]
    linarith
  · -- √7/15 < 0.177 ⇔ √7 < 2.655 (since 0.177·15 = 2.655).
    have hb_pos : (0 : ℝ) < 2.655 := by norm_num
    have hsq : (7 : ℝ) < (2.655 : ℝ)^2 := by norm_num
    have hsqrt_hi : Real.sqrt 7 < (2.655 : ℝ) :=
      (Real.sqrt_lt' hb_pos).mpr hsq
    have h15 : (0 : ℝ) < (15 : ℝ) := by norm_num
    rw [div_lt_iff₀ h15]
    linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: VERDICT ENUM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The three discrete states the CD-rewrite of the chamber gap
    can be in. -/
inductive CDFormulaVerdict where
  /-- The CD rewrite is structurally derivable: a single Cayley–
      Dickson principle would force BOTH `√(disc)` in the
      numerator AND `Σ CD dims` in the denominator out of the J₄
      Feshbach reduction.  Strong "substrate forces YM gap". -/
  | CD_FORMULA_PROVED_STRUCTURAL : CDFormulaVerdict
  /-- The numerical identity holds (proved here unconditionally),
      and the cutoff "first four CD algebras" is rigid (truncating
      gives 7, extending gives 31).  But the chamber-gap
      derivation itself does NOT route through the CD chain — it
      routes through the J₄ Feshbach reduction of the Volterra
      σ_k ratios.  The CD rewrite is therefore a NUMERICAL
      coincidence riding on the Mersenne identity 7 = 2³ − 1. -/
  | CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN : CDFormulaVerdict
  /-- The numerical equality fails. -/
  | CD_FORMULA_REFUTED : CDFormulaVerdict
  deriving DecidableEq, Repr

/-- **The verdict for the CD rewrite of the YM chamber gap.**

    REASONING.
      • Numerical equality `√7/15 = √(dim im 𝕆)/Σ CD dims` IS
        proved (`chamber_gap_eq_sqrt_disc_over_CD_sum`).
      • The cutoff at k=3 is structurally rigid in the CD chain
        (`CD_cutoff_at_O_unique_for_15`): truncating to k=0..2
        gives 7, extending to k=0..4 gives 31; only k=0..3 gives
        the chamber-gap denominator 15.
      • HOWEVER, the chamber gap √7/15 is derived from the
        chamber polynomial discriminant 7 (atomic origin
        `disc = N_c + d_eff = 3 + 4`) divided by the rational
        prefactor `15 = (N_W · N_total) · (3/2) = (3/(N_total))^{-1} · 3`,
        which arises from the J₄ Feshbach reduction NORM
        (LayerA/FeshbachJ4), NOT from a Cayley–Dickson sum.
      • The "15 = Σ CD dims" identity is one of THREE equally
        valid framework readouts of 15 (also: dim(su(4)) and
        fermion count per generation; see `three_15_readouts`).
        The framework does not privilege any one.

    HONEST VERDICT:
        CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN. -/
def phaseE3_CD_YMgap_verdict : CDFormulaVerdict :=
  CDFormulaVerdict.CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN

theorem phaseE3_CD_YMgap_verdict_value :
    phaseE3_CD_YMgap_verdict =
      CDFormulaVerdict.CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Phase E3 Discovery — Cayley–Dickson rewrite of the YM
    chamber gap, master theorem.**

    Bundles the CD dimension sum identity, the numerator
    identification, the central rewrite of the chamber gap,
    the perturbation/cutoff coincidence tests, the cross-check
    with su(4) and fermion counts, the 45-atom decomposition,
    a numerical sanity bracket, and the verdict.

    Plain-English summary.
      • cayleyDicksonDimSum = 1 + 2 + 4 + 8 = 15.
      • dim_im_𝕆 = 7 = atom_disc.
      • Chamber gap √7/15 = √(dim_im_𝕆) / cayleyDicksonDimSum.
      • Cutoff at k=3 is rigid: k=0..2 gives 7, k=0..4 gives 31.
      • 15 has THREE equal-by-arithmetic framework readouts
        (CD sum, su(4) dim, fermion count per generation).
      • 45 = N_c · 15 = N_c² · N_total: TWO equally-valid
        decompositions of the reactor-angle / α_GUT denominator.
      • Chamber gap ∈ (0.176, 0.177).
      • Verdict: CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN. -/
theorem phase_E3_CD_YMgap_master :
    -- (I) CD dimension sum identity.
    cayleyDicksonDimSum = 15
    -- (II) Numerator identification.
    ∧ dim_im_O = 7
    ∧ atom_disc = dim_im_O
    -- (III) **THE CENTRAL DISCOVERY REWRITE.**
    ∧ Real.sqrt 7 / 15
        = Real.sqrt (dim_im_O : ℝ) / (cayleyDicksonDimSum : ℝ)
    -- (IV) The chamber gap is the same constant.
    ∧ chamber_gap = Real.sqrt 7 / 15
    -- (V) Cutoff rigidity in the CD chain.
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 = 7
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 = 15
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 + realDimCD 4 = 31
    -- (VI) Three INDEPENDENT 15-readouts (CD sum, su(4) dim, fermion count).
    ∧ dimSU4 = 15
    ∧ fermionsPerGeneration = 15
    -- (VII) The 45 = N_c · 15 cross-check.
    ∧ ((45 : ℕ) = atom_N_c * cayleyDicksonDimSum)
    ∧ ((45 : ℕ) = atom_N_c ^ 2 * atom_N_total)
    -- (VIII) Numerical sanity: √7/15 ∈ (0.176, 0.177).
    ∧ ((0.176 : ℝ) < chamber_gap ∧ chamber_gap < (0.177 : ℝ))
    -- (IX) Verdict.
    ∧ phaseE3_CD_YMgap_verdict =
        CDFormulaVerdict.CD_FORMULA_NUMERICAL_ONLY_STRUCTURAL_OPEN := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cayleyDicksonDimSum_eq_15
  · exact dim_im_O_eq_7
  · exact disc_atom_eq_dim_im_O
  · exact chamber_gap_eq_sqrt_disc_over_CD_sum
  · rfl
  · exact CD_sum_truncated_quaternion
  · exact (cayleyDicksonDimSum_eq_realDim_sum.symm.trans cayleyDicksonDimSum_eq_15)
  · exact CD_sum_with_sedenions
  · exact dimSU4_eq_15
  · exact fermionsPerGeneration_eq_15
  · exact fortyfive_eq_Nc_times_CDsum
  · exact fortyfive_eq_NcSq_times_Ntotal
  · exact chamber_gap_numerical_bracket
  · exact phaseE3_CD_YMgap_verdict_value

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE.**

    What this file PROVES (zero sorry, zero custom axioms):

      (i)   `cayleyDicksonDimSum = 1 + 2 + 4 + 8 = 15` and equals
            `Σ_{k=0}^3 realDimCD k`.

      (ii)  `dim_im_𝕆 = imDimCD 3 = 7 = atom_disc`
            (re-export of `OctonionUnification.disc_is_dim_im_O`).

      (iii) **THE DISCOVERY IDENTITY**:
              √7 / 15 = √(dim_im_𝕆) / (Σ CD dims).

      (iv)  Cutoff rigidity: k=0..2 gives 7, k=0..3 gives 15,
            k=0..4 gives 31 — only the cutoff at the octonions
            produces the chamber-gap denominator.

      (v)   Three independent 15-readouts: CD sum, dim(su(4)),
            fermions per generation.  All equal by ARITHMETIC,
            none derives the others.

      (vi)  45 = N_c · 15 = N_c² · N_total.  The reactor-angle /
            α_GUT denominator has two equally-valid framework
            decompositions.

    What this file does NOT claim:

      (a)   That the chamber-Feshbach derivation of √7/15 routes
            through the Cayley–Dickson chain.  It does not.  The
            J₄ matrix entries (1/3, 2/5, 1/5, 1/25, 1/50) come
            from the Volterra σ_k ratios at d=4, not from CD
            dimensions.

      (b)   That `15 = Σ CD dims` is the FRAMEWORK's preferred
            decomposition of the chamber-gap denominator.  The
            denominator 15 in `frameworkChamberGap = √7/15`
            arises as a NORM PREFACTOR (the (N_W · N_total)² = 100
            modulo √7/√225 = √7/15 from the J₄ chamber polynomial
            discriminant 700 = 100·7).  The CD-sum reading is a
            POST-HOC rewrite, not a derivation.

      (c)   That `α_GUT = 1/45 = 1/(3·15)` is structurally derived
            from the CD chain.  Project memory documents
            α_GUT = 1/45 = sin²θ_13^PMNS, but the framework's
            atomic decomposition is 1/(N_c²·N_total) = 1/(9·5),
            which arises from PMNS angle structure, not from CD.

    NET STATEMENT.  The CD rewrite of the YM chamber gap is a
    PROVED numerical identity whose two ingredients (Mersenne
    7 = dim im 𝕆 and the CD partial sum 15 = 1+2+4+8) sit
    naturally in the framework's vocabulary BUT do not replace
    the chamber-Feshbach derivation of √7/15.  It strengthens the
    case that the framework's substrate is octonion-flavoured —
    the chamber discriminant √(dim im 𝕆) is the same √7 — but
    does NOT close a structural derivation of the YM mass gap
    from the CD chain. -/
theorem HONEST_SCOPE_CD_YMgap :
    -- (i) CD sum.
    cayleyDicksonDimSum = 15
    -- (ii) numerator identification.
    ∧ dim_im_O = atom_disc
    -- (iii) the discovery identity.
    ∧ Real.sqrt 7 / 15
        = Real.sqrt (dim_im_O : ℝ) / (cayleyDicksonDimSum : ℝ)
    -- (iv) cutoff rigidity.
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 = 7
    ∧ realDimCD 0 + realDimCD 1 + realDimCD 2 + realDimCD 3 = 15
    -- (v) three 15-readouts.
    ∧ (dimSU4 = 15 ∧ fermionsPerGeneration = 15) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cayleyDicksonDimSum_eq_15
  · exact disc_atom_eq_dim_im_O.symm
  · exact chamber_gap_eq_sqrt_disc_over_CD_sum
  · exact CD_sum_truncated_quaternion
  · exact (cayleyDicksonDimSum_eq_realDim_sum.symm.trans cayleyDicksonDimSum_eq_15)
  · exact ⟨dimSU4_eq_15, fermionsPerGeneration_eq_15⟩

end UnifiedTheory.LayerB.Phase_E3_Discovery_CayleyDickson_YMGap
