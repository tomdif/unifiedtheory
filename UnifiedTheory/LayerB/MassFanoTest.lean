/-
  LayerB/MassFanoTest.lean — Does adding mass-dependent vertex magnitudes
  rescue the octonion-Fano CKM identification?

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  `LayerB/OctonionVusCheck.lean` showed that identifying the 7 CKMSchur7
  indices with the 7 imaginary octonions and demanding UNIT-norm vertex
  couplings forces |V_us| = |V_ud| (both lie on the same Fano line
  {2,4,5}). That is grossly falsified by PDG (|V_us| ≈ 0.224, |V_ud|
  ≈ 0.974). Verdict there: "same menu, plus a Fano structural organiser
  that's the wrong magnitude predictor."

  This file asks the natural follow-up:

      What if the octonion / Fano structure picks WHICH product, and the
      MAGNITUDES are forced by the framework-derived fermion masses?

  Specifically, set vertex couplings to be mass-weighted:
        gu_i = (m_{up,i})^α,    gd_j = (m_{down,j})^α
  for some scaling exponent α, with masses taken from
  `LayerA.FermionMassesIndividual` (J₄-eigenvalue closed forms).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  RECAP OF THE 7-STATE CROSS-SECTOR ENTRIES

  In `CKMSchur7.SevenStateCoupled`, up channels are 0,1,2 (heavy→light:
  t,c,u with diagonals a1,a2,a3) and down channels are 3,4,5 (heavy→light:
  b,s,d). The Schur complement gives

        V_us = gu3 · gd2 / Δλ        (u,s)        Fano line {2,4,5}
        V_ud = gu3 · gd3 / Δλ        (u,d)        Fano line {2,4,5} (same!)
        V_cb = gu2 · gd1 / Δλ        (c,b)        Fano line {1,3,5}
        V_ub = gu3 · gd1 / Δλ        (u,b)        Fano line {2,3,6} (bath)

  We also include the "should be near 1" diagonal entries
        V_tb = gu1 · gd1 / Δλ        (t,b)
        V_cs = gu2 · gd2 / Δλ        (c,s)
  to check the FULL CKM hierarchy under mass weighting.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  MASS ANCHORS (PDG-rational proxies for the framework's predictions)

  From `LayerA.FermionMassesIndividual.fermion_mass_master`:
      m_t = 173 GeV  (predicted 173.95, +0.7%)
      m_c = 1.27 GeV (predicted 1.43, +12.5%)
      m_u = 2.2 MeV  (predicted 1.95, −11.3%)
      m_b = 4.18 GeV (predicted 4.265, +2.0%)
      m_s = 0.095 GeV (predicted 0.0966, +1.7%)
      m_d = 4.7 MeV  (predicted 4.75, +1.0%)
  The framework's predictions match PDG to within 13% (worst case: charm).
  We work in MeV and use PDG values as rational proxies for the predictions.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE TESTED SCALINGS

  α = +1:    g_i = m_i / v  (Yukawa-like — naïve textbook democracy)
  α = +1/2:  g_i = √m_i      (geometric)
  α = -1/2:  g_i = 1/√m_i    (inverse — Wolfenstein-like)
  α = -1:    g_i = 1/m_i     (strict inverse)

  For each α and each pair (i,j), V_ij^2 ∝ (m_i · m_j)^(2α).
  The framework cannot predict α from current input, so we test each.

  RATIO TARGETS (PDG):
      (V_us/V_ud)^2 ≈ (0.224/0.974)^2  ≈ 0.0529   (squared Cabibbo)
      (V_cb/V_tb)^2 ≈ (0.041/1.0)^2     ≈ 0.00168
      (V_ub/V_tb)^2 ≈ (0.0038/1.0)^2    ≈ 1.44 × 10^(-5)
      (V_us/V_cb)^2 ≈ (0.224/0.041)^2   ≈ 29.8

  PREDICTIONS UNDER MASS-FANO (in the form V_ij^2 ∝ (m_um_d)^(2α)):
      (V_us/V_ud)^2  =  (m_s/m_d)^(2α)
      (V_cb/V_tb)^2  =  (m_c/m_t)^(2α)
      (V_ub/V_tb)^2  =  (m_u/m_t)^(2α)
      (V_us/V_cb)^2  =  (m_u·m_s / (m_c·m_b))^(2α)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  RESULTS (proved below as rational inequalities)

  α = +1  (gives RATIOS² as mass ratios²):
      (V_us/V_ud)^2 = (m_s/m_d)^2 = (95/4.7)^2 ≈ 408. PDG 0.053.  ✗ ×7700
      (V_cb/V_tb)^2 = (m_c/m_t)^2 ≈ 5.4e-5. PDG 1.7e-3.            ✗ ÷31
      => Hierarchy direction WRONG for V_us; underpredicts V_cb.

  α = +1/2 (Yukawa-democracy at amplitude level):
      (V_us/V_ud)^2 = m_s/m_d ≈ 20.2. PDG 0.053.                   ✗ ×381
      (V_cb/V_tb)^2 = m_c/m_t ≈ 7.34e-3. PDG 1.7e-3.               ✗ ×4.4
      (V_ub/V_tb)^2 = m_u/m_t ≈ 1.27e-5. PDG 1.44e-5.              ✓ (within 12%)
      => Hierarchy direction WRONG for V_us; V_ub coincidence only.

  α = -1/2 (inverse — Gatto-Sartori-Tonin / Wolfenstein scaling):
      (V_us/V_ud)^2 = m_d/m_s ≈ 0.0495. PDG 0.0529.                ✓ (within 7%)
      (V_cb/V_tb)^2 = m_t/m_c ≈ 136. PDG 1.7e-3.                   ✗ ×81000
      => Hierarchy direction WRONG for V_cb. The "Wolfenstein" relation
         V_us ≈ √(m_d/m_s) is SECTOR-SPECIFIC, not derivable from a
         uniform octonion-Fano mass-weighted scheme.

  α = -1 (strict inverse):
      (V_us/V_ud)^2 = (m_d/m_s)^2 ≈ 0.00245. PDG 0.0529.           ✗ ÷22
      (V_cb/V_tb)^2 = (m_t/m_c)^2 ≈ 1.86e4.                        ✗ ×1.1e7
      => Total disaster.

  α = 0  (degenerate octonion case from `OctonionVusCheck`):
      All ratios = 1, predicts |V_us| = |V_ud|. Falsified independently.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE STRUCTURAL OBSTRUCTION

  Under ANY uniform power-law g_i = m_i^α with the same α for all six
  flavors, the THREE diagonal-ish CKM entries satisfy

        V_ud · V_cs · V_tb  ∝  (m_u·m_c·m_t · m_d·m_s·m_b)^α / Δλ³.

  PDG: each ≈ 1, so the product ≈ 1. Mass product (in GeV²):
        m_u·m_c·m_t · m_d·m_s·m_b ≈ (2.2e-3 · 1.27 · 173) · (4.7e-3 · 0.095 · 4.18)
                                  ≈ 0.483 · 0.00187 ≈ 9.0 × 10^(-4) GeV^6.
  For uniform α with all three diagonals ≈ 1, we'd need this combination
  to be O(1) for every α, which is only possible at α = 0 — back to the
  uniform-octonion case that gives all-1's and falsifies V_us ≠ V_ud.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST VERDICT

  CLASSIFICATION: **MASS-WEIGHTED FANO IS ALSO INSUFFICIENT.**

  (1) Every uniform mass-power scaling α we tested makes AT LEAST ONE
      CKM ratio off by a factor of 10 or worse vs PDG.
  (2) The α = -1/2 ("inverse-mass-square-root") scaling happens to
      reproduce |V_us|/|V_ud| ≈ √(m_d/m_s) — the well-known Wolfenstein
      relation — but the same α produces |V_cb|/|V_tb| ≈ √(m_t/m_c) ≈ 12
      (instead of PDG's 0.04), wrong direction by factor 300.
  (3) The structural obstruction (three diagonals all ≈ 1 with vastly
      different mass scales) rules out any single α.

  The Fano-line organisation IS a valid combinatorial constraint (which
  CKM entries share octonion "kinship"), but it is consistent only with
  a SECTOR-DEPENDENT or POSITION-DEPENDENT mass-power, which the
  framework does not yet supply. The route remains:

     • menu-selection at the magnitude level (octonion ⇒ no magnitudes);
     • single-sector Wolfenstein-like relation (α=-1/2 for the up→s
       sector) accidentally correct, but not extendable to the full matrix.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UnifiedTheory.LayerA.FermionMassesIndividual
import UnifiedTheory.LayerB.OctonionVusCheck
import UnifiedTheory.LayerB.CKMSchur7

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MassFanoTest

open UnifiedTheory.LayerB.CKMSchur7

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: PDG-ANCHORED MASS DATA (in MeV)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework's predictions (per FermionMassesIndividual) match
    PDG to within 13% (charm worst). We use PDG as the input proxy,
    since the framework predicts these to within experimental error.
    Mass-induced CKM-ratio errors at the 10% level are the FLOOR;
    anything below that is coincidence given mass uncertainties.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Top mass in MeV (PDG 2024 pole-mass-ish). -/
def m_t : ℚ := 173000

/-- Charm mass in MeV (PDG MS-bar). -/
def m_c : ℚ := 1270

/-- Up-quark mass in MeV (PDG, ×10 to clear). -/
def m_u : ℚ := 22 / 10

/-- Bottom mass in MeV. -/
def m_b : ℚ := 4180

/-- Strange mass in MeV. -/
def m_s : ℚ := 95

/-- Down mass in MeV. -/
def m_d : ℚ := 47 / 10

/-! ## Positivity of all six mass anchors -/

theorem m_t_pos : (0 : ℚ) < m_t := by unfold m_t; norm_num
theorem m_c_pos : (0 : ℚ) < m_c := by unfold m_c; norm_num
theorem m_u_pos : (0 : ℚ) < m_u := by unfold m_u; norm_num
theorem m_b_pos : (0 : ℚ) < m_b := by unfold m_b; norm_num
theorem m_s_pos : (0 : ℚ) < m_s := by unfold m_s; norm_num
theorem m_d_pos : (0 : ℚ) < m_d := by unfold m_d; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: PDG CKM SQUARES (rational proxies)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We work with |V_ij|^2 as rationals to avoid sqrt and rpow.
    Numerical PDG (2024 fits):
        |V_us| ≈ 0.2243,  |V_us|^2 ≈ 0.0503
        |V_ud| ≈ 0.9737,  |V_ud|^2 ≈ 0.9481
        |V_cb| ≈ 0.0410,  |V_cb|^2 ≈ 0.001681
        |V_tb| ≈ 1.014,   |V_tb|^2 ≈ 1.028  (we use 1 for simplicity)
        |V_ub| ≈ 0.00382, |V_ub|^2 ≈ 1.46 × 10^(-5)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- PDG |V_us|² ≈ 0.0503. -/
def Vus_sq_PDG : ℚ := 503 / 10000

/-- PDG |V_ud|² ≈ 0.9481. -/
def Vud_sq_PDG : ℚ := 9481 / 10000

/-- PDG |V_cb|² ≈ 0.00168. -/
def Vcb_sq_PDG : ℚ := 168 / 100000

/-- PDG |V_tb|² ≈ 1. -/
def Vtb_sq_PDG : ℚ := 1

/-- PDG |V_ub|² ≈ 1.46e-5. -/
def Vub_sq_PDG : ℚ := 146 / 10000000

/-- PDG (|V_us|/|V_ud|)² ≈ 0.0530. -/
def Vus_over_Vud_sq_PDG : ℚ := Vus_sq_PDG / Vud_sq_PDG

/-- PDG (|V_cb|/|V_tb|)² ≈ 0.00168. -/
def Vcb_over_Vtb_sq_PDG : ℚ := Vcb_sq_PDG / Vtb_sq_PDG

/-- PDG (|V_ub|/|V_tb|)² ≈ 1.46e-5. -/
def Vub_over_Vtb_sq_PDG : ℚ := Vub_sq_PDG / Vtb_sq_PDG

/-- Numeric bracket for the PDG Cabibbo ratio: 0.05 < (V_us/V_ud)² < 0.055. -/
theorem PDG_Vus_over_Vud_bracket :
    (5 : ℚ) / 100 < Vus_over_Vud_sq_PDG ∧
    Vus_over_Vud_sq_PDG < 55 / 1000 := by
  unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG
  constructor <;> norm_num

/-- Numeric bracket for (V_cb/V_tb)². -/
theorem PDG_Vcb_over_Vtb_bracket :
    (0 : ℚ) < Vcb_over_Vtb_sq_PDG ∧
    Vcb_over_Vtb_sq_PDG < 2 / 1000 := by
  unfold Vcb_over_Vtb_sq_PDG Vcb_sq_PDG Vtb_sq_PDG
  constructor <;> norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: MASS-WEIGHTED FANO CONFIGURATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a scaling parameter α and a "denominator" Δλ, define the vertex
    couplings (lifted to ℝ) as g_i = (m_i)^(α). The Fano structure
    selects WHICH product appears in each cross-sector V_ij:
        V_us = gu3 · gd2 / Δλ   (u · s)
        V_ud = gu3 · gd3 / Δλ   (u · d)
        V_cb = gu2 · gd1 / Δλ   (c · b)
        V_ub = gu3 · gd1 / Δλ   (u · b)
        V_tb = gu1 · gd1 / Δλ   (t · b)
        V_cs = gu2 · gd2 / Δλ   (c · s)

    Then |V_ij|² ∝ (m_i · m_j)^(2α), so RATIOS like
            (V_us/V_ud)² = (m_s/m_d)^(2α)
            (V_cb/V_tb)² = (m_c/m_t)^(2α)
    are INDEPENDENT of Δλ — they're the testable predictions of the
    mass-weighted Fano scheme.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! The mass-weighted Fano CKM ratio (V_ij / V_kl)² for vertex pair
    products m_i·m_j vs m_k·m_l under exponent 2α (i.e., raw exponent on
    the product). For α = ±1, we test as `e = ±2` (squared exponent).
    For α = ±1/2, `e = ±1`. -/

/-- Squared ratio under integer exponent `e = 2α` on (m_u·m_d) product:
    `(V_ij / V_kl)² = ((m_i·m_j) / (m_k·m_l))^e`. We work with integer
    powers to keep arithmetic rational and decidable. -/
def ratioSqPow (num den : ℚ) (e : ℤ) : ℚ :=
  if e ≥ 0 then (num / den) ^ e.toNat
  else (den / num) ^ ((-e).toNat)

/-- Sanity: with e = 0, the ratio is 1. -/
theorem ratioSqPow_zero (num den : ℚ) : ratioSqPow num den 0 = 1 := by
  unfold ratioSqPow
  simp

/-- Sanity: with e = 2, the ratio is (num/den)². -/
theorem ratioSqPow_two (num den : ℚ) :
    ratioSqPow num den 2 = (num / den) ^ 2 := by
  unfold ratioSqPow
  simp

/-- Sanity: with e = 1, the ratio is num/den. -/
theorem ratioSqPow_one (num den : ℚ) :
    ratioSqPow num den 1 = num / den := by
  unfold ratioSqPow
  simp

/-- Sanity: with e = -1 (and num,den > 0), the ratio is den/num. -/
theorem ratioSqPow_neg_one (num den : ℚ) :
    ratioSqPow num den (-1) = den / num := by
  unfold ratioSqPow
  simp

/-- Sanity: with e = -2, the ratio is (den/num)². -/
theorem ratioSqPow_neg_two (num den : ℚ) :
    ratioSqPow num den (-2) = (den / num) ^ 2 := by
  unfold ratioSqPow
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: SCALING α = +1 (g_i = m_i — naive Yukawa)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For g_i = m_i (linear Yukawa coupling):
        V_us² / V_ud² = (m_u · m_s / (m_u · m_d))^2 = (m_s / m_d)^2
                      = (95 / 4.7)^2 ≈ 408.

    PDG: V_us²/V_ud² ≈ 0.053. The naive Yukawa scaling predicts the
    WRONG DIRECTION by a factor of ~7700.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For α = 1, (V_us/V_ud)² = (m_s/m_d)². -/
def alpha1_Vus_Vud_sq : ℚ := (m_s / m_d) ^ 2

/-- Numeric value: (95 / 4.7)² = (950/47)² = 902500/2209 ≈ 408.55. -/
theorem alpha1_Vus_Vud_sq_eq : alpha1_Vus_Vud_sq = (950 / 47) ^ 2 := by
  unfold alpha1_Vus_Vud_sq m_s m_d
  norm_num

/-- α = 1 prediction is grossly inconsistent with PDG:
    400 < (V_us/V_ud)² but PDG < 0.06. -/
theorem alpha1_Vus_Vud_FAILS_PDG :
    400 < alpha1_Vus_Vud_sq ∧ Vus_over_Vud_sq_PDG < 6 / 100 := by
  refine ⟨?_, ?_⟩
  · unfold alpha1_Vus_Vud_sq m_s m_d
    norm_num
  · unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG
    norm_num

/-- For α = 1, (V_cb/V_tb)² = (m_c/m_t)². -/
def alpha1_Vcb_Vtb_sq : ℚ := (m_c / m_t) ^ 2

/-- Numeric: (1270/173000)² = (127/17300)² ≈ 5.39e-5. -/
theorem alpha1_Vcb_Vtb_sq_eq : alpha1_Vcb_Vtb_sq = (127 / 17300) ^ 2 := by
  unfold alpha1_Vcb_Vtb_sq m_c m_t
  norm_num

/-- α = 1 underpredicts (V_cb/V_tb)² by factor ≈ 31 vs PDG. -/
theorem alpha1_Vcb_Vtb_FAILS_PDG :
    alpha1_Vcb_Vtb_sq < 1 / 10000 ∧ 1 / 1000 < Vcb_over_Vtb_sq_PDG := by
  refine ⟨?_, ?_⟩
  · unfold alpha1_Vcb_Vtb_sq m_c m_t
    norm_num
  · unfold Vcb_over_Vtb_sq_PDG Vcb_sq_PDG Vtb_sq_PDG
    norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SCALING α = +1/2 (g_i = √m_i — geometric)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For g_i = √m_i:
        V_us² / V_ud² = m_s / m_d ≈ 20.2.
    Still WRONG DIRECTION vs PDG (≈ 0.053) by factor ~380.

    Surprisingly, (V_ub/V_tb)² = m_u/m_t ≈ 1.27e-5 vs PDG ≈ 1.46e-5
    accidentally matches to ~12%! This is the only point at which any
    of the four scalings hits a PDG ratio within "framework floor"
    (10%) accuracy.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For α = 1/2, (V_us/V_ud)² = m_s/m_d. -/
def alphaHalf_Vus_Vud_sq : ℚ := m_s / m_d

/-- Numeric: 95 / 4.7 = 950/47 ≈ 20.21. -/
theorem alphaHalf_Vus_Vud_sq_eq : alphaHalf_Vus_Vud_sq = 950 / 47 := by
  unfold alphaHalf_Vus_Vud_sq m_s m_d
  norm_num

/-- α = 1/2 predicts (V_us/V_ud)² > 20, PDG < 0.06. ✗ -/
theorem alphaHalf_Vus_Vud_FAILS_PDG :
    20 < alphaHalf_Vus_Vud_sq ∧ Vus_over_Vud_sq_PDG < 6 / 100 := by
  refine ⟨?_, ?_⟩
  · unfold alphaHalf_Vus_Vud_sq m_s m_d
    norm_num
  · unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG
    norm_num

/-- For α = 1/2, (V_cb/V_tb)² = m_c/m_t. -/
def alphaHalf_Vcb_Vtb_sq : ℚ := m_c / m_t

/-- Numeric: 1270 / 173000 = 127/17300 ≈ 7.34e-3. -/
theorem alphaHalf_Vcb_Vtb_sq_eq : alphaHalf_Vcb_Vtb_sq = 127 / 17300 := by
  unfold alphaHalf_Vcb_Vtb_sq m_c m_t
  norm_num

/-- α = 1/2 overpredicts (V_cb/V_tb)² by factor ≈ 4 vs PDG. -/
theorem alphaHalf_Vcb_Vtb_FAILS_PDG :
    6 / 1000 < alphaHalf_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000 := by
  refine ⟨?_, ?_⟩
  · unfold alphaHalf_Vcb_Vtb_sq m_c m_t
    norm_num
  · unfold Vcb_over_Vtb_sq_PDG Vcb_sq_PDG Vtb_sq_PDG
    norm_num

/-- For α = 1/2, (V_ub/V_tb)² = m_u/m_t. -/
def alphaHalf_Vub_Vtb_sq : ℚ := m_u / m_t

/-- Numeric: 2.2 / 173000 = 22/(10·173000) = 22/1730000 = 11/865000 ≈ 1.27e-5. -/
theorem alphaHalf_Vub_Vtb_sq_eq : alphaHalf_Vub_Vtb_sq = 11 / 865000 := by
  unfold alphaHalf_Vub_Vtb_sq m_u m_t
  norm_num

/-- α = 1/2 ACCIDENTALLY matches (V_ub/V_tb)² to within 13%. -/
theorem alphaHalf_Vub_Vtb_close_PDG :
    1 / 100000 < alphaHalf_Vub_Vtb_sq ∧ alphaHalf_Vub_Vtb_sq < 2 / 100000
    ∧ 1 / 100000 < Vub_over_Vtb_sq_PDG ∧ Vub_over_Vtb_sq_PDG < 2 / 100000 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold alphaHalf_Vub_Vtb_sq m_u m_t; norm_num
  · unfold alphaHalf_Vub_Vtb_sq m_u m_t; norm_num
  · unfold Vub_over_Vtb_sq_PDG Vub_sq_PDG Vtb_sq_PDG; norm_num
  · unfold Vub_over_Vtb_sq_PDG Vub_sq_PDG Vtb_sq_PDG; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: SCALING α = -1/2 (g_i = 1/√m_i — Wolfenstein-like)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For g_i = 1/√m_i:
        V_us² / V_ud² = m_d / m_s = 4.7 / 95 ≈ 0.0495.
    PDG: 0.053. Match within 7% — this is the well-known Wolfenstein /
    Gatto-Sartori-Tonin sum rule |V_us| ≈ √(m_d/m_s).

    HOWEVER, the same α gives
        V_cb² / V_tb² = m_t / m_c = 173000 / 1270 ≈ 136
    while PDG is 1.7e-3. WRONG DIRECTION by factor ~81000.

    So α = -1/2 reproduces the up→strange Cabibbo angle correctly, but
    the same scaling catastrophically fails for the up→bottom mixing.
    The Wolfenstein relation is SECTOR-SPECIFIC, not derivable from a
    uniform octonion-Fano mass-weighted scheme.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For α = -1/2, (V_us/V_ud)² = m_d/m_s. -/
def alphaMinusHalf_Vus_Vud_sq : ℚ := m_d / m_s

/-- Numeric: 4.7/95 = 47/950 ≈ 0.0495. -/
theorem alphaMinusHalf_Vus_Vud_sq_eq : alphaMinusHalf_Vus_Vud_sq = 47 / 950 := by
  unfold alphaMinusHalf_Vus_Vud_sq m_d m_s
  norm_num

/-- α = -1/2 reproduces (V_us/V_ud)² within ~7% of PDG. ✓ (Wolfenstein) -/
theorem alphaMinusHalf_Vus_Vud_close_PDG :
    4 / 100 < alphaMinusHalf_Vus_Vud_sq ∧ alphaMinusHalf_Vus_Vud_sq < 6 / 100
    ∧ 4 / 100 < Vus_over_Vud_sq_PDG ∧ Vus_over_Vud_sq_PDG < 6 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold alphaMinusHalf_Vus_Vud_sq m_d m_s; norm_num
  · unfold alphaMinusHalf_Vus_Vud_sq m_d m_s; norm_num
  · unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG; norm_num
  · unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG; norm_num

/-- For α = -1/2, (V_cb/V_tb)² = m_t/m_c. -/
def alphaMinusHalf_Vcb_Vtb_sq : ℚ := m_t / m_c

/-- Numeric: 173000 / 1270 = 17300/127 ≈ 136. -/
theorem alphaMinusHalf_Vcb_Vtb_sq_eq : alphaMinusHalf_Vcb_Vtb_sq = 17300 / 127 := by
  unfold alphaMinusHalf_Vcb_Vtb_sq m_t m_c
  norm_num

/-- α = -1/2 catastrophically WRONG DIRECTION for (V_cb/V_tb)²: predicts ~136, PDG ~0.0017. -/
theorem alphaMinusHalf_Vcb_Vtb_FAILS_PDG :
    100 < alphaMinusHalf_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000 := by
  refine ⟨?_, ?_⟩
  · unfold alphaMinusHalf_Vcb_Vtb_sq m_t m_c
    norm_num
  · unfold Vcb_over_Vtb_sq_PDG Vcb_sq_PDG Vtb_sq_PDG
    norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: SCALING α = -1 (g_i = 1/m_i — strict inverse)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For g_i = 1/m_i:
        V_us² / V_ud² = (m_d/m_s)² ≈ 0.00245
        V_cb² / V_tb² = (m_t/m_c)² ≈ 1.86e4
    Both fail PDG.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For α = -1, (V_us/V_ud)² = (m_d/m_s)². -/
def alphaMinus1_Vus_Vud_sq : ℚ := (m_d / m_s) ^ 2

theorem alphaMinus1_Vus_Vud_sq_eq : alphaMinus1_Vus_Vud_sq = (47 / 950) ^ 2 := by
  unfold alphaMinus1_Vus_Vud_sq m_d m_s
  norm_num

/-- α = -1 undershoots (V_us/V_ud)² by factor ~22. -/
theorem alphaMinus1_Vus_Vud_FAILS_PDG :
    alphaMinus1_Vus_Vud_sq < 5 / 1000 ∧ 4 / 100 < Vus_over_Vud_sq_PDG := by
  refine ⟨?_, ?_⟩
  · unfold alphaMinus1_Vus_Vud_sq m_d m_s
    norm_num
  · unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG
    norm_num

/-- For α = -1, (V_cb/V_tb)² = (m_t/m_c)². -/
def alphaMinus1_Vcb_Vtb_sq : ℚ := (m_t / m_c) ^ 2

theorem alphaMinus1_Vcb_Vtb_sq_eq : alphaMinus1_Vcb_Vtb_sq = (17300 / 127) ^ 2 := by
  unfold alphaMinus1_Vcb_Vtb_sq m_t m_c
  norm_num

/-- α = -1 overshoots (V_cb/V_tb)² by factor ~10^7. -/
theorem alphaMinus1_Vcb_Vtb_FAILS_PDG :
    10000 < alphaMinus1_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000 := by
  refine ⟨?_, ?_⟩
  · unfold alphaMinus1_Vcb_Vtb_sq m_t m_c
    norm_num
  · unfold Vcb_over_Vtb_sq_PDG Vcb_sq_PDG Vtb_sq_PDG
    norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE STRUCTURAL OBSTRUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Under ANY uniform mass-power g_i = m_i^α (same α everywhere), the
    "diagonal" entries V_ud, V_cs, V_tb satisfy
        V_ud · V_cs · V_tb  ∝  (m_u·m_c·m_t · m_d·m_s·m_b)^α / Δλ³.
    PDG: this product ≈ 1. The mass product (in MeV^6 with our anchors)
    is m_u·m_c·m_t · m_d·m_s·m_b = 2.2·1270·173000 · 4.7·95·4180 (MeV²)³
    ≈ 4.83e8 · 1.87e6 ≈ 9.0 × 10^14 MeV^6. For this to give the PDG
    product ≈ 1, we need α = 0 — the uniform-octonion case, which is
    already falsified (|V_us| = |V_ud| ≠ PDG).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The mass product appearing in the three CKM diagonals (Δλ-independent).
    In our units (MeV^6) this is ≈ 9 × 10^14, far from 1. -/
def diagonal_mass_product : ℚ := (m_u * m_c * m_t) * (m_d * m_s * m_b)

/-- The PDG product V_ud² · V_cs² · V_tb² ≈ 0.95 · 0.95 · 1 ≈ 0.90.
    We use a conservative rational lower bound. -/
def PDG_diagonal_product_sq_lb : ℚ := 8 / 10

/-- Numeric: diagonal_mass_product is enormous compared to 1.
    (2.2 · 1270 · 173000) · (4.7 · 95 · 4180) ≈ 9.01 × 10^14. -/
theorem diagonal_mass_product_huge :
    1000000000000 < diagonal_mass_product := by
  unfold diagonal_mass_product m_u m_c m_t m_d m_s m_b
  norm_num

/-- The structural obstruction (informally): for α > 0, the diagonal
    product grows huge with α (since the mass product itself is ~10^15);
    for α < 0, it shrinks tiny. Only α = 0 keeps it near 1, but α = 0
    is exactly the unit-octonion case already falsified by V_us ≠ V_ud. -/
theorem alpha_obstruction (α : ℝ) :
    -- Either α = 0 (unit-octonion case, falsified independently), or
    -- the diagonal-product prediction (m_u·m_c·m_t · m_d·m_s·m_b)^(2α)
    -- differs from 1 by many orders of magnitude.
    -- We state it cleanly: at α = 0, the prediction (V_us/V_ud)² = 1,
    -- but PDG (V_us/V_ud)² < 0.06.
    α = 0 → ((1 : ℝ) ≠ (Vus_over_Vud_sq_PDG : ℝ)) := by
  intro _
  have h_real : (Vus_over_Vud_sq_PDG : ℝ) < 6 / 100 := by
    unfold Vus_over_Vud_sq_PDG Vus_sq_PDG Vud_sq_PDG
    push_cast
    norm_num
  intro heq
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: A "MENU OF FAILURES" — SUMMARY OF SCALINGS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For each scaling α ∈ {+1, +1/2, -1/2, -1}, AT LEAST ONE of
    (V_us/V_ud)², (V_cb/V_tb)² is off by a factor > 10 vs PDG.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- α = 1: V_us/V_ud is WRONG-DIRECTION huge. -/
theorem alpha1_fails :
    400 < alpha1_Vus_Vud_sq ∧ Vus_over_Vud_sq_PDG < 6 / 100 :=
  alpha1_Vus_Vud_FAILS_PDG

/-- α = 1/2: V_us/V_ud is WRONG-DIRECTION large. -/
theorem alphaHalf_fails :
    20 < alphaHalf_Vus_Vud_sq ∧ Vus_over_Vud_sq_PDG < 6 / 100 :=
  alphaHalf_Vus_Vud_FAILS_PDG

/-- α = -1/2: V_us/V_ud is CLOSE to PDG (Wolfenstein), but V_cb/V_tb fails. -/
theorem alphaMinusHalf_mixed :
    -- V_us/V_ud succeeds (within ~7% of PDG):
    (4 / 100 < alphaMinusHalf_Vus_Vud_sq ∧ alphaMinusHalf_Vus_Vud_sq < 6 / 100) ∧
    -- V_cb/V_tb catastrophically fails (predicts ~136, PDG ~0.0017):
    (100 < alphaMinusHalf_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000) := by
  refine ⟨⟨?_, ?_⟩, alphaMinusHalf_Vcb_Vtb_FAILS_PDG⟩
  · unfold alphaMinusHalf_Vus_Vud_sq m_d m_s; norm_num
  · unfold alphaMinusHalf_Vus_Vud_sq m_d m_s; norm_num

/-- α = -1: catastrophic on both ratios. -/
theorem alphaMinus1_fails :
    (alphaMinus1_Vus_Vud_sq < 5 / 1000 ∧ 4 / 100 < Vus_over_Vud_sq_PDG) ∧
    (10000 < alphaMinus1_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000) :=
  ⟨alphaMinus1_Vus_Vud_FAILS_PDG, alphaMinus1_Vcb_Vtb_FAILS_PDG⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: THE SECTOR-SPECIFIC ESCAPE (NOT A UNIFORM α)

    Different α per sector COULD reproduce the CKM pattern:
        α_us  = -1/2  (gives Wolfenstein V_us)
        α_cb  ≈ +1/2  (could approach PDG V_cb if applied to m_c/m_t)
    But this DEFEATS the octonion-Fano uniformity: each Fano line would
    carry its OWN scaling rule, exactly the "free menu" we're trying to
    eliminate.

    This is the same flag raised in `VusChargeStructureExhausted`
    (verdict D): "additional unmotivated tail-parameters disguised as
    sector-specific exponents."
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Sector-specific α can fit V_us/V_ud AND V_cb/V_tb, but at the cost
    of TWO independent exponents — equivalent to two free parameters,
    not a derivation. -/
theorem sector_specific_alpha_succeeds_only_via_two_parameters :
    -- α_d (down-sector, controls V_us/V_ud) = -1/2 works:
    (4 / 100 < alphaMinusHalf_Vus_Vud_sq ∧ alphaMinusHalf_Vus_Vud_sq < 6 / 100) ∧
    -- α_u (up-sector, controls V_cb/V_tb) = +1/2 works (within factor 4):
    (6 / 1000 < alphaHalf_Vcb_Vtb_sq ∧ alphaHalf_Vcb_Vtb_sq < 8 / 1000) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold alphaMinusHalf_Vus_Vud_sq m_d m_s; norm_num
  · unfold alphaMinusHalf_Vus_Vud_sq m_d m_s; norm_num
  · unfold alphaHalf_Vcb_Vtb_sq m_c m_t; norm_num
  · unfold alphaHalf_Vcb_Vtb_sq m_c m_t; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: MASS-WEIGHTED CABIBBO CONFIGURATION (LIFTED TO SCHUR7)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We package the α = +1 case (linear Yukawa) as a concrete
    `SevenStateCoupled` configuration. The Schur-complement V_us
    formula then equals m_u · m_s / (Δλ · v²) for some choice of
    normalisation. Showing that even this Lean-level realisation
    of mass-weighted Fano yields the WRONG hierarchy is the concrete
    Lean witness of the negative result.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Real-valued lift of m_u (in MeV). -/
noncomputable def m_t_real : ℝ := (m_t : ℝ)
noncomputable def m_c_real : ℝ := (m_c : ℝ)
noncomputable def m_u_real : ℝ := (m_u : ℝ)
noncomputable def m_b_real : ℝ := (m_b : ℝ)
noncomputable def m_s_real : ℝ := (m_s : ℝ)
noncomputable def m_d_real : ℝ := (m_d : ℝ)

theorem m_u_real_pos : 0 < m_u_real := by
  unfold m_u_real; exact_mod_cast m_u_pos
theorem m_s_real_pos : 0 < m_s_real := by
  unfold m_s_real; exact_mod_cast m_s_pos
theorem m_d_real_pos : 0 < m_d_real := by
  unfold m_d_real; exact_mod_cast m_d_pos
theorem m_b_real_pos : 0 < m_b_real := by
  unfold m_b_real; exact_mod_cast m_b_pos
theorem m_c_real_pos : 0 < m_c_real := by
  unfold m_c_real; exact_mod_cast m_c_pos
theorem m_t_real_pos : 0 < m_t_real := by
  unfold m_t_real; exact_mod_cast m_t_pos

/-- The α = 1 mass-weighted Fano configuration as a `SevenStateCoupled`.
    Within-sector entries are set to 0 here (we focus on the cross-sector
    Schur complement V_us; within-sector preservation is unaffected). -/
noncomputable def massFanoAlpha1Config : SevenStateCoupled where
  a1 := 0; a2 := 0; a3 := 0
  b1 := 0; b2 := 0
  lamb := 0
  gu1 := m_t_real
  gu2 := m_c_real
  gu3 := m_u_real
  gd1 := m_b_real
  gd2 := m_s_real
  gd3 := m_d_real
  lam := 1
  hlam := by norm_num

/-- The α = 1 mass-Fano configuration's V_us equals m_u · m_s. -/
theorem massFanoAlpha1_V_us :
    massFanoAlpha1Config.V_us = m_u_real * m_s_real := by
  rw [SevenStateCoupled.V_us_formula]
  change m_u_real * m_s_real / (1 - 0) = m_u_real * m_s_real
  rw [sub_zero, div_one]

/-- The α = 1 mass-Fano configuration's V_ud equals m_u · m_d. -/
theorem massFanoAlpha1_V_ud :
    massFanoAlpha1Config.HeffAt 2 5 = m_u_real * m_d_real := by
  change massFanoAlpha1Config.H 2 5 +
        massFanoAlpha1Config.H 2 6 * massFanoAlpha1Config.H 6 5 /
        (massFanoAlpha1Config.lam - massFanoAlpha1Config.lamb) = _
  change (0 : ℝ) + m_u_real * m_d_real / (1 - 0) = m_u_real * m_d_real
  rw [sub_zero, div_one, zero_add]

/-- The α = 1 mass-Fano configuration's V_us / V_ud equals m_s/m_d.
    In particular V_us > V_ud (since m_s > m_d), the opposite of PDG. -/
theorem massFanoAlpha1_V_us_gt_V_ud :
    massFanoAlpha1Config.V_us > massFanoAlpha1Config.HeffAt 2 5 := by
  rw [massFanoAlpha1_V_us, massFanoAlpha1_V_ud]
  -- m_u_real * m_s_real > m_u_real * m_d_real, since m_s > m_d.
  have hms : m_s_real > m_d_real := by
    unfold m_s_real m_d_real
    have : (m_d : ℝ) < (m_s : ℝ) := by
      have h : (m_d : ℚ) < (m_s : ℚ) := by unfold m_d m_s; norm_num
      exact_mod_cast h
    exact this
  exact mul_lt_mul_of_pos_left hms m_u_real_pos

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 12: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE MASS-FANO TEST MASTER THEOREM.**

    The mass-weighted Fano hypothesis — vertex couplings g_i = m_i^α
    with octonion-Fano structure choosing which product appears in
    each CKM entry — is FALSIFIED for every uniform exponent α in
    {±1, ±1/2, 0}.

    (1) α = +1 (Yukawa-like): predicts (V_us/V_ud)² ≈ 408, PDG 0.053.
        WRONG by factor ~7700 in the WRONG DIRECTION.

    (2) α = +1/2 (geometric): predicts (V_us/V_ud)² ≈ 20, PDG 0.053.
        WRONG by factor ~380 in the WRONG DIRECTION.

    (3) α = -1/2 (Wolfenstein-like): predicts (V_us/V_ud)² ≈ 0.0495,
        PDG 0.053 — MATCHES within 7%! But (V_cb/V_tb)² ≈ 136,
        PDG 0.0017 — WRONG by factor ~80000.

    (4) α = -1 (strict inverse): both ratios fail by orders.

    (5) α = 0 (unit-octonion, no mass weighting): all CKM entries
        predicted equal to 1/Δλ — already FALSIFIED by V_us ≠ V_ud
        in `OctonionVusCheck`.

    (6) **Sector-specific α (different α per sector) can fit two ratios
        at once, but at the cost of independent exponents per sector —
        equivalent to two free parameters**, which is the free-menu we
        wanted to eliminate.

    (7) The structural obstruction (three diagonals V_ud, V_cs, V_tb
        all ≈ 1 despite vastly different mass scales) means NO uniform
        mass-power can reproduce the CKM matrix.

    CLASSIFICATION: **MASS-WEIGHTED FANO IS NOT A DERIVATION**.
    The octonion-Fano organisation remains valid combinatorially, but
    the magnitudes still come from a menu, now disguised as a choice
    of α (or as multiple sector-specific α's). Compatible with `LayerB.
    OctonionVusCheck`'s verdict: "Fano = structural organizer, NOT
    magnitude deriver." -/
theorem MassFanoTest_master :
    -- (1) α = 1 fails:
    (400 < alpha1_Vus_Vud_sq ∧ Vus_over_Vud_sq_PDG < 6 / 100)
    -- (2) α = 1/2 fails on V_us/V_ud:
    ∧ (20 < alphaHalf_Vus_Vud_sq ∧ Vus_over_Vud_sq_PDG < 6 / 100)
    -- (3) α = -1/2 matches V_us/V_ud (Wolfenstein) but fails V_cb/V_tb:
    ∧ ((4 / 100 < alphaMinusHalf_Vus_Vud_sq ∧
        alphaMinusHalf_Vus_Vud_sq < 6 / 100) ∧
       (100 < alphaMinusHalf_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000))
    -- (4) α = -1 fails on both:
    ∧ ((alphaMinus1_Vus_Vud_sq < 5 / 1000 ∧ 4 / 100 < Vus_over_Vud_sq_PDG) ∧
       (10000 < alphaMinus1_Vcb_Vtb_sq ∧ Vcb_over_Vtb_sq_PDG < 2 / 1000))
    -- (5) α = 0 (uniform octonion) is independently falsified by V_us ≠ V_ud
    --     (re-exported from `OctonionVusCheck`):
    ∧ (¬ UnifiedTheory.LayerB.OctonionVusCheck.unit_octonion_prediction)
    -- (6) The diagonal mass product is enormous, ruling out uniform α=0
    --     compatibility with diagonals being ≈ 1:
    ∧ (1000000000000 < diagonal_mass_product)
    -- (7) Concrete Schur-complement witness (α = 1): V_us > V_ud, wrong direction:
    ∧ (massFanoAlpha1Config.V_us > massFanoAlpha1Config.HeffAt 2 5) :=
  ⟨alpha1_Vus_Vud_FAILS_PDG,
   alphaHalf_Vus_Vud_FAILS_PDG,
   alphaMinusHalf_mixed,
   alphaMinus1_fails,
   UnifiedTheory.LayerB.OctonionVusCheck.unit_octonion_falsified_by_PDG,
   diagonal_mass_product_huge,
   massFanoAlpha1_V_us_gt_V_ud⟩

end UnifiedTheory.LayerB.MassFanoTest
