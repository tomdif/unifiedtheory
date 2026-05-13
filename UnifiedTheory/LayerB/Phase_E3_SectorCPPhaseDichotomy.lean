/-
  LayerB/Phase_E3_SectorCPPhaseDichotomy.lean

  ─────────────────────────────────────────────────────────────────
  E3 INVESTIGATION: SECTOR-DEPENDENT CP-PHASE DICHOTOMY
                    (PMNS = MAXIMAL,  CKM = STRUCTURED)
  ─────────────────────────────────────────────────────────────────

  CONTEXT.  Two prior LayerB files put the framework's two known
  Dirac CP phases on a sharp collision course:

    • `PMNSCPPhase`         (lepton sector)
        δ_CP^PMNS  =  −π/2     (master_cp_magnitude + sign rung)
        sin²(δ_CP^PMNS)  =  1                     (MAXIMAL CP)
        |J^PMNS|  =  √(1936 / 1 771 875) ≈ 0.0331

    • `Phase_E3_JCKMAtomicSearch`  (quark sector)
        sin(δ_CP^CKM)  =  7/8 = disc / N_W³        (primary atomic)
        sin²(δ_CP^CKM) =  49/64                   (STRUCTURED, not maximal)
        |J^CKM|  ≈  3.05 · 10⁻⁵   (PDG 1σ:  3.08 · 10⁻⁵)

  The PMNS sector is at the MAXIMAL-CP point; the CKM sector is at a
  STRUCTURED but non-maximal point.  This file investigates whether
  this dichotomy is a deeper unification or a coincidence, along the
  six axes specified by the survey question.

  ─────────────────────────────────────────────────────────────────
  CORE ATOMIC OBSERVATION
  ─────────────────────────────────────────────────────────────────

  The cross-sector ratio of squared CP-violating sines is

      sin²(δ_CP^PMNS) / sin²(δ_CP^CKM)
        =  1 / (49/64)
        =  64 / 49
        =  (N_W³ / disc)²                          [Theorem `sinSq_ratio_atomic`]

  Both 64 and 49 are framework atoms (powers of N_W=2 and disc=7).
  This is a CLEAN ATOMIC RATIO.  But: is the ratio STRUCTURAL or
  COINCIDENTAL?  Three further checks below.

  ─────────────────────────────────────────────────────────────────
  AXIS 1 — IS 64/49 SOMEWHERE ELSE IN THE CROSS-SECTOR CATALOG?
  ─────────────────────────────────────────────────────────────────

  Searched the framework for other quark↔lepton ratios equal to
  (N_W³/disc)² = 64/49 ≈ 1.306:

    quantity                      ratio                 hits 64/49?
    ─────────────────────────     ───────────────       ───────────
    m_t / m_τ                     ≈ 99.4                NO (> 100×)
    sin²θ_12^CKM / sin²θ_12^PMNS  (1/20)/(3/10)=1/6     NO (≠ 64/49)
    sin²θ_23^CKM / sin²θ_23^PMNS  (1/600)/(4/7)=7/2400  NO (different)
    sin²θ_13^CKM / sin²θ_13^PMNS  smaller still         NO
    α_em / α_W (Planck)           ≈ 3/(32π) / sin²θ_W
                                   = (3/32π) / (3/8)
                                   = 1 / (4π) ≈ 0.0796 NO

  No other quark↔lepton ratio in the framework equals 64/49.  The
  appearance of 64/49 in the CP sector is therefore NOT part of a
  larger pattern; it is a SINGLETON cross-sector identity.

  ─────────────────────────────────────────────────────────────────
  AXIS 2 — π/2 vs 7/8·π CONTRAST
  ─────────────────────────────────────────────────────────────────

  PMNS:  δ_CP^PMNS  =  −π/2          ≈ −1.5708 rad
  CKM:   δ_CP^CKM   =  arcsin(7/8)   ≈  1.0654 rad ≈ 61.04°

  Note:  PDG δ_CP^CKM ≈ 1.196 rad (68.5°).  arcsin(7/8) = 1.0654 rad
  (61.0°) is the framework's atomic candidate (taking the principal
  value in [0, π/2]); the second-quadrant lift π − arcsin(7/8)
  ≈ 2.076 rad is also consistent with sin = 7/8.  Either value
  carries sin² = 49/64.

  Angle ratio:
      |δ_CP^CKM_principal| / |δ_CP^PMNS|  =  1.0654 / 1.5708 ≈ 0.6783.
      49/64                                 = 0.7656.
      They DO NOT MATCH.

  The sin²-ratio is CLEAN (64/49), but the ANGLE-ratio is not — as
  it must be, since arcsin is non-linear.  The cross-sector relation
  lives at the level of sin² (= probability-amplitude² in the unitary
  parameterisation), NOT at the level of the angle itself.

  ─────────────────────────────────────────────────────────────────
  AXIS 3 — MAJORANA PHASES (THREE-GENERATION GENERALIZATION)
  ─────────────────────────────────────────────────────────────────

  Quark sector:  1 Dirac phase (δ_CP^CKM).
  Lepton sector: 1 Dirac phase (δ_CP^PMNS) + 2 Majorana phases (α_21, α_31)
                  if neutrinos are Majorana.

  Searched the codebase for Majorana-phase predictions:

    • `NeutrinoMass.lean` and `NeutrinoMassRefined.lean` mention only
      the Majorana MASS scale M_R, not the Majorana CP PHASES.
    • `PMNSCPPhase.lean` derives only the Dirac δ_CP^PMNS = −π/2.
    • `PMNSStructuralAudit.lean` audits the three angles and the
      Dirac CP phase, with no entry for Majorana phases.
    • `MassAndMixing.cp_requires_three` and
      `ThreeGenerations.nPhases` count ONLY Dirac CP phases
      (formula (N-1)(N-2)/2, gives 1 at N=3); Majorana phases are
      NOT counted.

  CONCLUSION on Majorana phases:  The framework currently makes
  NO atomic prediction for the two PMNS Majorana phases (α_21, α_31).
  The K/P "pure dressing is imaginary" derivation that pinned
  |δ_CP^PMNS| = π/2 (PMNSCPPhase.master_cp_magnitude) does NOT
  obviously extend to Majorana phases — those originate from the
  charge-conjugation structure of Majorana mass terms, not from
  the unitary mixing matrix's Dirac phase.  Predicting them would
  require an analogous K/P decomposition for the Majorana mass
  matrix, which has not been done.

  ─────────────────────────────────────────────────────────────────
  AXIS 4 — JARLSKOG INVARIANT, CROSS-SECTOR RATIO
  ─────────────────────────────────────────────────────────────────

  From `PMNSCPPhase.jarlskog_PMNS_sq_numerical`:
      J²_PMNS  =  1936 / 1 771 875
                =  44² / (N_c⁴ · N_total⁵ · disc)
              ≈ 1.093 · 10⁻³.
      |J^PMNS_pred|  ≈ 0.03306    (NuFIT 2024 J_max ≈ 0.0335: −1.4%)

  From `Phase_E3_JCKMAtomicSearch.JCKMsq_A_value` (primary candidate):
      J²_CKM  =  343 / 368 640 000 000
              =  disc³ / (2^19 · 3² · 5^7)
              ≈ 9.30 · 10⁻¹⁰.
      |J^CKM_pred|  ≈ 3.05 · 10⁻⁵  (PDG: 3.08 · 10⁻⁵: −1.0%)

  Squared cross-sector ratio:
      J²_PMNS / J²_CKM  =  (1936 / 1 771 875) · (368 640 000 000 / 343)
                        =  (2^23 · 5² · 11²) / (3² · 7⁴)
                        ≈  1.174 · 10⁶.
      |J^PMNS| / |J^CKM|  ≈ √(1.174·10⁶)  ≈  1083.

  The 11² in the numerator is NON-ATOMIC (11 ∉ {2, 3, 5, 7}); it
  arises as 44 = N_c²·N_total − 1, the same "subtraction" already
  flagged in `PMNSStructuralAudit` Part 3 as a structural observation
  rather than a clean atomic identity.  So:

      The 1000× factor between J_PMNS and J_CKM is REAL but is
      NOT itself a clean atomic ratio — it picks up the 44² factor
      from cos²θ_13^PMNS = 44/45.

  Verdict on Axis 4:  J_PMNS / J_CKM ≈ 1000 is reproduced by the
  framework, but the ratio is NOT a single atom — it's a composite
  driven by (a) the 64/49 sin²(δ_CP) ratio and (b) the very different
  mixing-angle magnitudes between sectors (CKM small angles, PMNS
  large angles).

  ─────────────────────────────────────────────────────────────────
  AXIS 5 — COUPLING-CONSTANT CROSS-SECTOR RATIOS
  ─────────────────────────────────────────────────────────────────

  At the unification (Planck) scale the framework predicts:
      α_em^Planck  =  3 / (32 π)         (`LayerA/FineStructure`)
      sin²θ_W      =  3 / 8              (`LayerA/WeinbergAngle`)
      α_W (= g²/4π at unification)  =  α_em / sin²θ_W  =  1 / (4 π)

  Hence:
      α_em / α_W  =  sin²θ_W  =  3 / 8  ≈  0.375.

  This is the framework's clean cross-sector electroweak ratio.
  It is NOT 64/49.  No coupling-constant ratio in the framework
  equals 64/49.

  Verdict on Axis 5:  The 64/49 sin²(δ_CP) ratio does NOT echo in
  the coupling-constant sector.

  ─────────────────────────────────────────────────────────────────
  AXIS 6 — STRONG-CP ANGLE θ_QCD
  ─────────────────────────────────────────────────────────────────

  From `LayerA/StrongCP.lean`:
      θ_QCD  =  0   (effectively, by parity-odd / topology arguments)

  In the framework's vocabulary, the THREE non-Majorana CP phases
  in the Standard Model carry RADICALLY DIFFERENT values:

      sector             CP phase                  framework value
      ────────────────   ─────────────────────     ────────────────
      QCD (strong)       θ_QCD                     0  (suppressed)
      CKM (quark mix)    δ_CP^CKM                  arcsin(7/8) ≈ 61°
      PMNS (lepton mix)  δ_CP^PMNS                 −π/2 (maximal)

  The KEY FRAMEWORK ATOMS controlling these are DIFFERENT in each
  sector:

      θ_QCD = 0:    parity-odd Tr[F·F̃] vs parity-even source functional;
                    discrete causal set has no instanton sectors.
      δ_CP^CKM:     CKM mixing matrix carries one Dirac phase;
                    framework's FREE (post-hoc) atomic candidate
                    sin = disc / N_W³ matches PDG to ≤1%.
      δ_CP^PMNS:    K/P amplitude decomposition forces purely
                    imaginary phase, |δ_CP| = π/2 RIGOROUSLY
                    (not a free fit).

  The dichotomy is therefore NOT controlled by a single framework
  atom.  Instead, three different mechanisms operate in the three
  sectors:

      (i)  STRONG-CP: TOPOLOGICAL PROTECTION (instantons absent on
           discrete causal set).
      (ii) PMNS-CP: K/P STRUCTURE FORCES MAXIMAL CP (pure-dressing
           amplitude is imaginary).
      (iii) CKM-CP: NO STRUCTURAL CONSTRAINT — the value sits at
           an atomically simple point inside the PDG window, but
           is post-hoc.

  ─────────────────────────────────────────────────────────────────
  DICHOTOMY EXPLANATION
  ─────────────────────────────────────────────────────────────────

  PMNS is MAXIMAL because the K/P decomposition forces the lepton-
  sector mixing amplitude to be PURELY IMAGINARY (the source
  functional vanishes on the dressing P-sector).  Imaginary amplitudes
  give arg = ±π/2, whence sin² δ_CP = 1.  This is RIGOROUS in the
  framework (PMNSCPPhase.master_cp_magnitude).

  CKM is STRUCTURED-NOT-MAXIMAL because the QUARK sector mixing is
  dominated by the SOURCE-functional (K-sector) part — which is
  REAL — with a small dressing correction.  The CP phase sits at
  the atomically natural value sin = 7/8 (post-hoc selection), but
  there is NO derivation that forces the value.

  The 64/49 ratio is therefore a NUMEROLOGICAL by-product of two
  independent atomic facts:
      (a) PMNS is at the K/P-forced maximal point sin² = 1 = 64/64,
      (b) CKM happens to sit (within PDG 1σ) at sin = disc/N_W³,
          giving sin² = 49/64.
  The ratio 64/49 = 1/(49/64) is then automatic.  It is NOT itself
  derived from a single framework mechanism — it is the QUOTIENT
  of two independent atomic facts.

  ─────────────────────────────────────────────────────────────────
  VERDICT
  ─────────────────────────────────────────────────────────────────

  STRUCTURAL on the PMNS side; POST-HOC on the CKM side; the 64/49
  ratio is an atomic CONSEQUENCE, not an atomic CAUSE.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace UnifiedTheory.LayerB.Phase_E3_SectorCPPhaseDichotomy

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: ATOMIC VOCABULARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Weak-isospin atom. -/
def NW : ℚ := 2

/-- Colour atom (= generation count). -/
def Nc : ℚ := 3

/-- N_total = N_W + N_c = 5. -/
def Nt : ℚ := 5

/-- Feshbach discriminant atom (disc = 7). -/
def disc : ℚ := 7

theorem NW_value : NW = 2 := rfl
theorem Nc_value : Nc = 3 := rfl
theorem Nt_value : Nt = 5 := rfl
theorem disc_value : disc = 7 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SECTOR CP-VIOLATING SINES (re-stated locally)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- PMNS Dirac CP-violating sine squared.  From `PMNSCPPhase`,
    sin(δ_CP^PMNS) = −1, so sin²(δ_CP^PMNS) = 1. -/
def sinSq_dCP_PMNS : ℚ := 1

/-- CKM Dirac CP-violating sine squared.  Primary atomic candidate
    from `Phase_E3_JCKMAtomicSearch` is sin = disc / N_W³ = 7/8,
    giving sin² = 49/64. -/
def sinSq_dCP_CKM : ℚ := (disc / NW^3)^2

theorem sinSq_dCP_PMNS_value : sinSq_dCP_PMNS = 1 := rfl

theorem sinSq_dCP_CKM_value : sinSq_dCP_CKM = 49 / 64 := by
  unfold sinSq_dCP_CKM disc NW; norm_num

theorem sinSq_dCP_CKM_pos : 0 < sinSq_dCP_CKM := by
  rw [sinSq_dCP_CKM_value]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE CORE SECTOR-CONTRAST RATIO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's cross-sector CP-violating sine ratio. -/
def cpRatio : ℚ := sinSq_dCP_PMNS / sinSq_dCP_CKM

/-- **CORE THEOREM** — the cross-sector ratio is exactly 64/49. -/
theorem cpRatio_eq_64_49 : cpRatio = 64 / 49 := by
  unfold cpRatio
  rw [sinSq_dCP_PMNS_value, sinSq_dCP_CKM_value]
  norm_num

/-- **STRUCTURAL FORM** — 64/49 = (N_W³ / disc)². -/
theorem cpRatio_eq_atomic : cpRatio = (NW^3 / disc)^2 := by
  rw [cpRatio_eq_64_49]
  unfold NW disc; norm_num

/-- **EQUIVALENT FORM** — 64/49 = N_W^6 / disc². -/
theorem cpRatio_factored : cpRatio = NW^6 / disc^2 := by
  rw [cpRatio_eq_64_49]
  unfold NW disc; norm_num

/-- The reciprocal sin²(δ_CP^CKM)/sin²(δ_CP^PMNS) = 49/64 = (disc/N_W³)². -/
theorem cpRatio_inv_eq : sinSq_dCP_CKM / sinSq_dCP_PMNS = 49 / 64 := by
  rw [sinSq_dCP_PMNS_value, sinSq_dCP_CKM_value]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: 64/49 IS NOT IN THE OTHER CROSS-SECTOR-RATIO CATALOG
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **RATIO sin²θ_12^CKM / sin²θ_12^PMNS = (1/20)/(3/10) = 1/6.**
    Not equal to 64/49. -/
theorem theta12_cross_sector_ratio :
    ((1 : ℚ) / 20) / ((3 : ℚ) / 10) = 1 / 6 := by norm_num

theorem theta12_ratio_ne_cpRatio :
    ((1 : ℚ) / 20) / ((3 : ℚ) / 10) ≠ cpRatio := by
  rw [cpRatio_eq_64_49]; norm_num

/-- **RATIO sin²θ_23^CKM / sin²θ_23^PMNS = (1/600)/(4/7) = 7/2400.**
    Not equal to 64/49. -/
theorem theta23_cross_sector_ratio :
    ((1 : ℚ) / 600) / ((4 : ℚ) / 7) = 7 / 2400 := by norm_num

theorem theta23_ratio_ne_cpRatio :
    ((1 : ℚ) / 600) / ((4 : ℚ) / 7) ≠ cpRatio := by
  rw [cpRatio_eq_64_49]; norm_num

/-- **The unification-scale electroweak coupling ratio**
    α_em / α_W = sin²θ_W = 3/8 (framework's
    `WeinbergAngle.sin2_weinberg_eq_three_eighths`).  Not 64/49. -/
theorem electroweak_coupling_ratio_ne_cpRatio :
    (3 : ℚ) / 8 ≠ cpRatio := by
  rw [cpRatio_eq_64_49]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: π/2 vs arcsin(7/8) — ANGLE-LEVEL CONTRAST
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The PMNS Dirac CP angle |δ_CP^PMNS| = π/2 (real-valued).
    From `PMNSCPPhase.abs_delta_CP_PMNS`. -/
noncomputable def absDeltaCP_PMNS : ℝ := Real.pi / 2

/-- The CKM atomic-candidate sine 7/8.  Cast as ℝ. -/
noncomputable def sinDeltaCP_CKM : ℝ := (7 : ℝ) / 8

/-- The principal CKM CP angle (in [0, π/2]) is arcsin(7/8). -/
noncomputable def absDeltaCP_CKM_principal : ℝ := Real.arcsin sinDeltaCP_CKM

/-- The CKM atomic sine is in [−1, 1] so arcsin is well-defined. -/
theorem sinDeltaCP_CKM_le_one : sinDeltaCP_CKM ≤ 1 := by
  unfold sinDeltaCP_CKM; norm_num

theorem sinDeltaCP_CKM_ge_neg_one : (-1 : ℝ) ≤ sinDeltaCP_CKM := by
  unfold sinDeltaCP_CKM; norm_num

/-- Real sine of the CKM principal CP angle is the atomic 7/8. -/
theorem sin_absDeltaCP_CKM_principal :
    Real.sin absDeltaCP_CKM_principal = 7 / 8 := by
  unfold absDeltaCP_CKM_principal sinDeltaCP_CKM
  exact Real.sin_arcsin sinDeltaCP_CKM_ge_neg_one sinDeltaCP_CKM_le_one

/-- Real sine of the PMNS CP angle (magnitude) is 1. -/
theorem sin_absDeltaCP_PMNS :
    Real.sin absDeltaCP_PMNS = 1 := by
  unfold absDeltaCP_PMNS
  exact Real.sin_pi_div_two

/-- **sin²(δ_CP^PMNS) = 1 at the real-valued level.** -/
theorem sinSq_real_PMNS :
    (Real.sin absDeltaCP_PMNS)^2 = 1 := by
  rw [sin_absDeltaCP_PMNS]; norm_num

/-- **sin²(δ_CP^CKM) = 49/64 at the real-valued level (principal value).** -/
theorem sinSq_real_CKM_principal :
    (Real.sin absDeltaCP_CKM_principal)^2 = 49 / 64 := by
  rw [sin_absDeltaCP_CKM_principal]; norm_num

/-- **Real-valued cross-sector sin² ratio is 64/49.** -/
theorem sinSq_ratio_real :
    (Real.sin absDeltaCP_PMNS)^2 / (Real.sin absDeltaCP_CKM_principal)^2 = 64 / 49 := by
  rw [sinSq_real_PMNS, sinSq_real_CKM_principal]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: JARLSKOG CROSS-SECTOR RATIO J²_PMNS / J²_CKM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Re-stated J²_PMNS from `PMNSCPPhase.jarlskog_PMNS_sq_numerical`. -/
def JsqPMNS : ℚ := 1936 / 1771875

/-- Re-stated primary J²_CKM from `Phase_E3_JCKMAtomicSearch.JCKMsq_A_value`. -/
def JsqCKM_A : ℚ := 343 / 368640000000

/-- Squared Jarlskog ratio in closed form.  The ratio carries an 11²
    factor (44 = N_c²·N_total − 1), which is non-atomic. -/
def JsqRatio : ℚ := JsqPMNS / JsqCKM_A

/-- **Closed numerical form of the squared Jarlskog ratio.**
    J²_PMNS / J²_CKM = (2^23 · 5² · 11²) / (3² · 7^4)
                    = 25 375 539 200 / 21 609. -/
theorem JsqRatio_value : JsqRatio = 25375539200 / 21609 := by
  unfold JsqRatio JsqPMNS JsqCKM_A; norm_num

/-- The 11² in the numerator is NOT in the framework atomic
    vocabulary {2, 3, 5, 7}.  The ratio is therefore NOT a clean
    atomic expression. -/
theorem JsqRatio_numerator_has_11 :
    (25375539200 : ℚ) = 2^23 * 5^2 * 11^2 := by norm_num

theorem JsqRatio_denominator_atomic :
    (21609 : ℚ) = 3^2 * 7^4 := by norm_num

/-- **Order-of-magnitude bracket** — J²_PMNS / J²_CKM lives in
    [1.17 · 10⁶, 1.18 · 10⁶], i.e. |J_PMNS|/|J_CKM| ≈ 1083 ≈ 1000×. -/
theorem JsqRatio_bracket :
    1170000 < JsqRatio ∧ JsqRatio < 1180000 := by
  rw [JsqRatio_value]
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: STRONG-CP ANGLE AND THE THREE-VALUE DICHOTOMY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Strong-CP angle in the framework (`LayerA/StrongCP`):
    θ_QCD effectively vanishes by the parity / topology arguments. -/
def thetaQCD : ℚ := 0

theorem thetaQCD_value : thetaQCD = 0 := rfl

/-- The three Dirac CP-phase sin² values in the Standard Model
    differ by a SECTOR-DEPENDENT FRAMEWORK MECHANISM in each case,
    NOT by a single atom. -/
theorem three_sectors_different_sin_sq :
    -- Strong-CP sin² is 0 (parity-odd / topological)
    (Real.sin (0 : ℝ))^2 = 0 ∧
    -- CKM sin² is 49/64 (atomic but post-hoc selection)
    (Real.sin absDeltaCP_CKM_principal)^2 = 49 / 64 ∧
    -- PMNS sin² is 1 (K/P-forced maximal)
    (Real.sin absDeltaCP_PMNS)^2 = 1 := by
  refine ⟨?_, sinSq_real_CKM_principal, sinSq_real_PMNS⟩
  rw [Real.sin_zero]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: SUMMARY LISTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Catalog of CP phases in the Standard Model under this framework. -/
def cp_phase_sectors : List String :=
  [ "(1) theta_QCD (strong-CP): VALUE 0; mechanism = parity-odd source "
        ++ "+ no instantons on discrete causal set (StrongCP.lean)."
  , "(2) delta_CP^CKM (quark Dirac): VALUE arcsin(7/8) ≈ 61° (or its "
        ++ "second-quadrant lift); mechanism = atomic post-hoc match to "
        ++ "PDG 1σ window (JCKMAtomicSearch.lean)."
  , "(3) delta_CP^PMNS (lepton Dirac): VALUE −π/2; mechanism = K/P "
        ++ "structure forces purely imaginary amplitude "
        ++ "(PMNSCPPhase.master_cp_magnitude)."
  , "(4) alpha_21 (PMNS Majorana): NOT PREDICTED by current framework."
  , "(5) alpha_31 (PMNS Majorana): NOT PREDICTED by current framework."
  , "(6) theta_strong_other (e.g. CP-violating BSM phases): NOT in framework."
  ]

/-- Atomic predictions for Majorana phases — currently empty. -/
def predicted_majorana_phases : List String :=
  [ "alpha_21: NO atomic prediction.  K/P decomposition pinning δ_CP^PMNS = −π/2 "
        ++ "applies to the unitary mixing matrix's Dirac phase, not to the "
        ++ "Majorana phases (which originate from the Majorana mass term, "
        ++ "not the mixing matrix).  Codebase search confirms no entry "
        ++ "in PMNSCPPhase, PMNSStructuralAudit, NeutrinoMass, "
        ++ "NeutrinoMassRefined, or ThreeGenerations."
  , "alpha_31: NO atomic prediction (same reason)."
  , "Future work: an analogous K/P decomposition for the Majorana mass "
        ++ "matrix could in principle pin |α_21|, |α_31| to multiples of "
        ++ "π/2; this has NOT been done."
  ]

/-- Best framework-level explanation for the sector dichotomy. -/
def dichotomy_explanation : String :=
  "PMNS-MAXIMAL is STRUCTURAL: the K/P amplitude decomposition forces the "
  ++ "lepton-sector mixing amplitude to be purely imaginary on the dressing "
  ++ "P-sector (the source functional vanishes there), so arg = ±π/2 RIGOROUSLY. "
  ++ "CKM-STRUCTURED is POST-HOC: the quark-sector mixing is dominated by the "
  ++ "K-sector (real-valued source functional) with no K/P theorem forcing the "
  ++ "phase value; the framework's atomic candidate sin = 7/8 = disc/N_W³ "
  ++ "matches PDG 1σ but is selected from a list of three sub-2% candidates, "
  ++ "not derived from a structural mechanism. "
  ++ "STRONG-CP θ_QCD = 0 is STRUCTURAL: parity-odd Tr[F·F̃] is orthogonal to "
  ++ "the parity-even source functional, AND the discrete causal set lacks "
  ++ "manifold topology to support instanton sectors. "
  ++ "Hence the three CP phases (0, ≈61°, ±90°) are pinned by THREE DIFFERENT "
  ++ "mechanisms, not a single overarching atom. "
  ++ "The clean atomic ratio sin²(δ_CP^PMNS)/sin²(δ_CP^CKM) = 64/49 = (N_W³/disc)² "
  ++ "is therefore the QUOTIENT of two independently-derived facts (PMNS = 1 from "
  ++ "K/P; CKM = 49/64 from post-hoc atomic fit), NOT itself a derived quantity. "
  ++ "This is consistent with the framework treating the two Dirac CP phases as "
  ++ "INDEPENDENT atomic forms, as flagged in Phase_E3_JCKMAtomicSearch.lean "
  ++ "Caveat (b)."

/-- Catalog of all cross-sector CP-related ratios checked. -/
def cross_sector_ratios_checked : List String :=
  [ "sin²(δ_CP^PMNS)/sin²(δ_CP^CKM) = 1/(49/64) = 64/49 = (N_W³/disc)²:  CLEAN ATOMIC ✓"
  , "δ_CP^CKM_principal/|δ_CP^PMNS| = arcsin(7/8)/(π/2) ≈ 0.678:  NOT 49/64 ≈ 0.766; "
        ++ "angle-level ratio is NOT atomic (arcsin is non-linear)."
  , "sin²θ_12^CKM/sin²θ_12^PMNS = (1/20)/(3/10) = 1/6:  NOT 64/49."
  , "sin²θ_23^CKM/sin²θ_23^PMNS = (1/600)/(4/7) = 7/2400:  NOT 64/49."
  , "sin²θ_13^CKM/sin²θ_13^PMNS:  even smaller; NOT 64/49."
  , "α_em/α_W (Planck) = sin²θ_W = 3/8:  NOT 64/49."
  , "J²_PMNS/J²_CKM_A = 25,375,539,200/21,609 ≈ 1.17·10⁶:  contains 11² in "
        ++ "numerator (NON-atomic), so |J_PMNS|/|J_CKM| ≈ 1083 (~1000×) is NOT "
        ++ "a clean atomic ratio.  Decomposes as (64/49) × (PMNS-mixing-angle "
        ++ "factor)/(CKM-mixing-angle factor) — the 1000× is driven by the very "
        ++ "different mixing-angle magnitudes between sectors, not by the CP phase."
  , "m_t/m_τ ≈ 99 ≈ 100 (existing literature):  NOT 64/49."
  , "VERDICT: 64/49 appears NOWHERE ELSE in the framework's cross-sector ratios; "
        ++ "it is a SINGLETON — a cross-sector identity by composition, not by structure."
  ]

/-- Final verdict on the sector CP-phase dichotomy. -/
def verdict : String :=
  "MIXED — STRUCTURAL on the PMNS side, POST-HOC on the CKM side. "
  ++ "The clean atomic ratio sin²(δ_CP^PMNS)/sin²(δ_CP^CKM) = 64/49 = (N_W³/disc)² "
  ++ "is REAL and machine-checked (theorem `cpRatio_eq_atomic`), but it is the "
  ++ "QUOTIENT of two INDEPENDENT atomic facts: "
  ++ "(a) PMNS sin² = 1 is RIGOROUSLY DERIVED from the K/P decomposition "
  ++ "(PMNSCPPhase.master_cp_magnitude), and "
  ++ "(b) CKM sin² = 49/64 is POST-HOC SELECTED from three sub-2% atomic "
  ++ "candidates inside the PDG 1σ window (Phase_E3_JCKMAtomicSearch). "
  ++ "Six adjacent investigations all return NEGATIVE: "
  ++ "(i) 64/49 appears NOWHERE ELSE in the cross-sector catalog (m_t/m_τ ≈ 99, "
  ++ "θ_12 cross-sector = 1/6, θ_23 cross-sector = 7/2400, α_em/α_W = 3/8 — all "
  ++ "different); "
  ++ "(ii) angle-level ratio arcsin(7/8)/(π/2) ≈ 0.678 ≠ 49/64 ≈ 0.766 because "
  ++ "arcsin is non-linear; "
  ++ "(iii) Majorana phases α_21, α_31 have NO atomic predictions in the codebase; "
  ++ "(iv) J_PMNS/J_CKM ≈ 1083 contains 11² (non-atomic 44 = N_c²·N_total − 1) — "
  ++ "the 1000× cross-sector enhancement is driven by mixing-angle magnitudes, "
  ++ "not by the CP-phase ratio; "
  ++ "(v) coupling-constant ratios at unification are 3/8 and 1/(4π), not 64/49; "
  ++ "(vi) θ_QCD = 0 is forced by a THIRD INDEPENDENT mechanism (parity-odd + "
  ++ "no-instantons on discrete causal set), confirming that the SM's three Dirac "
  ++ "CP phases (0, ≈61°, ±90°) are pinned by THREE DIFFERENT framework "
  ++ "mechanisms, not a single atom. "
  ++ "CONCLUSION: 64/49 is a clean atomic CONSEQUENCE of two independent atomic "
  ++ "facts, NOT itself a derived structural quantity.  No deeper unifying "
  ++ "structure emerges from this audit."

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER CONJUNCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM** — The sector CP-phase dichotomy summary
    bundles the core cross-sector identity, the negative
    cross-sector checks, and the J² ratio bracket. -/
theorem master_sector_cp_dichotomy :
    -- Atomic vocabulary
    NW = 2 ∧ Nc = 3 ∧ Nt = 5 ∧ disc = 7
    -- Sector sin² CP values
    ∧ sinSq_dCP_PMNS = 1
    ∧ sinSq_dCP_CKM = 49 / 64
    -- Core ratio = 64/49 = (N_W³/disc)²
    ∧ cpRatio = 64 / 49
    ∧ cpRatio = (NW^3 / disc)^2
    ∧ cpRatio = NW^6 / disc^2
    -- Real-valued CP sin² values
    ∧ (Real.sin absDeltaCP_PMNS)^2 = 1
    ∧ (Real.sin absDeltaCP_CKM_principal)^2 = 49 / 64
    -- Real-valued cross-sector ratio matches the rational one
    ∧ (Real.sin absDeltaCP_PMNS)^2 / (Real.sin absDeltaCP_CKM_principal)^2 = 64 / 49
    -- Negative cross-sector checks (64/49 nowhere else)
    ∧ ((1 : ℚ) / 20) / ((3 : ℚ) / 10) ≠ cpRatio
    ∧ ((1 : ℚ) / 600) / ((4 : ℚ) / 7) ≠ cpRatio
    ∧ (3 : ℚ) / 8 ≠ cpRatio
    -- J² ratio bracket
    ∧ JsqRatio = 25375539200 / 21609
    ∧ (1170000 < JsqRatio ∧ JsqRatio < 1180000)
    -- Strong-CP value
    ∧ thetaQCD = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact NW_value
  · exact Nc_value
  · exact Nt_value
  · exact disc_value
  · exact sinSq_dCP_PMNS_value
  · exact sinSq_dCP_CKM_value
  · exact cpRatio_eq_64_49
  · exact cpRatio_eq_atomic
  · exact cpRatio_factored
  · exact sinSq_real_PMNS
  · exact sinSq_real_CKM_principal
  · exact sinSq_ratio_real
  · exact theta12_ratio_ne_cpRatio
  · exact theta23_ratio_ne_cpRatio
  · exact electroweak_coupling_ratio_ne_cpRatio
  · exact JsqRatio_value
  · exact JsqRatio_bracket
  · exact thetaQCD_value

end UnifiedTheory.LayerB.Phase_E3_SectorCPPhaseDichotomy
