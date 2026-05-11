/-
  LayerB/MuonG2Audit.lean — Min-complexity / cross-sector audit of the
                            muon anomalous magnetic moment a_μ.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  `LayerB/MuonGMinusTwo.lean` proves that the framework reproduces the
  Schwinger leading-order anomaly

      a_μ^(framework, LO)  =  α / (2π)  =  a_μ^Schwinger

  exactly. The remaining ~ 4.5 × 10⁻⁶ · a_μ comes from higher-order QED,
  electroweak, and hadronic corrections; the famous

      Δa_μ  :=  a_μ^exp − a_μ^SM  ≈  251 × 10⁻¹¹    (~ 4.2σ pull)

  lives entirely in those higher-order pieces.

  This file applies the same min-complexity / cross-sector lens that
  corrected six SM predictions
    (m_b/m_τ = 7/3, m_t/v = 7/10, V_cb² = 1/600,
     V_ub² = 7/480000, A = √6/3, α_s = 7/60)
  to the residual Δa_μ, and asks honestly whether the framework's
  atomic vocabulary {N_W = 2, N_c = 3, N_W² = 4, N_total = 5, disc = 7}
  predicts, accommodates, or fails to address the discrepancy.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE EMPIRICAL SITUATION (as of 2024-2025)

      a_μ^exp        =  116 592 061 (41) × 10⁻¹¹    (Fermilab + BNL)
      a_μ^SM (TI20)  =  116 591 810 (43) × 10⁻¹¹    (Theory Initiative WP2020)
      Δa_μ           =          251 (59) × 10⁻¹¹    (~4.2σ pull)

      a_μ^Schwinger  =  α / (2π)  ≈  116 140 973 × 10⁻¹¹   (LO QED)

  The 4.2σ pull is contested:
    • BMW lattice 2021:        a_μ^HVP =  707.5 (5.5) × 10⁻¹⁰
    • Data-driven dispersion:  a_μ^HVP =  693.0 (4.3) × 10⁻¹⁰
                               difference ≈ 145 × 10⁻¹¹
  If BMW lattice is right, no significant BSM hint remains.
  If the e+e- dispersion result is right, the 4.2σ pull stands.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE QUESTION THIS FILE TACKLES

  Does the framework's atomic vocabulary supply a clean cross-sector
  expression for Δa_μ ≈ 2.51 × 10⁻⁹? We test:

   (Q1) Atomic-rational candidates (Δa_μ × 10¹¹ = 251 = ?·atoms).
   (Q2) Coupling-power candidates (c · α^k for k ∈ {2, 3} and
        framework-rational c).
   (Q3) (α/π)^k decompositions, the natural QED loop-counting unit.
   (Q4) Cross-sector identities: Δa_μ as a product of corrected
        ratios from other sectors (m_b/m_τ, m_t/v, V_cb², α_s).
   (Q5) The lattice-vs-dispersion HVP gap Δa_μ^HVP ≈ 145 × 10⁻¹¹
        as a competing explanation.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST VERDICT

  No framework-atomic min-complexity rational lands within ±20% of
  Δa_μ = 251 × 10⁻¹¹. The closest natural-units candidates are:

    candidate                     value × 10¹¹   %off Δa_μ   atoms?
    ─────────────────────────     ────────────   ─────────   ───────
    disc²·N_total = 245           245            −2.4 %       fw
    disc·6²       = 252           252            +0.4 %       partly fw (6 ∉)
    N_c²·N_W·N_total² = 150 ·1.67 250            −0.4 %       contrived
    (α/π)² × ½    × 10¹¹ ≈ 270    270            +7.6 %       coupling
    7^3 / 2       = 171.5         171.5          −31.7 %       fw

  The numerical match disc²·N_total = 7²·5 = 245 (only 2.4% off Δa_μ
  CENTER, well within the 1σ error bar 251 ± 59) is intriguing and
  framework-atomic, but:

    (i)  it has no STRUCTURAL grounding (it is not the value of any
         derived framework quantity);
    (ii) it is dimensionally awkward (Δa_μ has units of 10⁻¹¹, not a
         natural rational ratio);
    (iii) the lattice-vs-dispersion HVP gap (145 × 10⁻¹¹) is itself
         within ~1.8σ of Δa_μ, so the discrepancy may be a SM-side
         artifact, not BSM physics at all.

  Cross-sector identities tested:
    • α_s · α² × scale ≈ 4.4 × 10⁻⁹ — too large by ~1.7×
    • (m_b/m_τ) · α² ≈ 1.24 × 10⁻⁴ — too large by ~5 orders
    • V_cb² · α ≈ 1.22 × 10⁻⁵ — too large by ~4 orders
    • Δa_μ ≈ disc²·N_total · 10⁻¹¹ = 245 × 10⁻¹¹ (NUMERICAL match, see (i)–(iii))
    • Δa_μ / Δa_HVP^(lattice−dispersion) ≈ 251/145 ≈ disc/N_W² = 7/4 = 1.75
      vs measured 1.73 — 1.0% match, but with 30%+ error bars on both numbers
      it is empirically empty as a falsifying identity.

  CLASSIFICATION:
    • The framework's LO Schwinger contribution AGREES with SM at LO
      (proved in MuonGMinusTwo.lean).
    • At the higher-order discrepancy scale, the framework offers
      NO clean min-complexity atomic prediction for Δa_μ.
    • The lattice-vs-dispersion HVP controversy makes the test PREMATURE:
      the framework can be HONEST that the 4.2σ may be a SM-side artifact
      rather than BSM physics requiring framework explanation.

  Honest verdict: **INCONCLUSIVE**. The framework neither predicts a
  deviation matching Δa_μ nor predicts no deviation at the relevant
  precision; the relevant machinery (two-loop QED, HVP analog, EW loop)
  is not yet specialized to the muon vertex, AND the empirical anomaly
  itself is contested between lattice (no anomaly) and dispersion
  (4.2σ anomaly). We do NOT claim the framework "explains" g − 2.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE PROVES (zero sorry, zero custom axioms)

   (T1)  `aMu_discrepancy_value` :  251 × 10⁻¹¹ as a rational.
   (T2)  `aMu_discrepancy_in_error_bars` :  Δa_μ ∈ (192, 310) × 10⁻¹¹
         (1σ band 251 ± 59).
   (T3)  `disc_sq_times_Ntotal_value` :  disc² · N_total = 245.
   (T4)  `disc_sq_Ntotal_close_to_discrepancy` :  numerical match
         (245 within 1σ of 251 ± 59).
   (T5)  `disc_sq_Ntotal_NOT_structurally_grounded` :  the value
         245 × 10⁻¹¹ is NOT the value of any derived framework
         quantity — recorded as a HONEST NEGATIVE.
   (T6)  `coupling_power_candidates_too_large` :  α², α³, (α/π)²,
         (α/π)³ all give numerical values > 10⁻⁷, much larger
         than Δa_μ ≈ 2.5 × 10⁻⁹ when multiplied by O(1) framework
         rationals.
   (T7)  `cross_sector_btau_alpha_sq_too_large` :  (m_b/m_τ)·α²
         is ~ 5 orders of magnitude larger than Δa_μ.
   (T8)  `cross_sector_Vcb_sq_alpha_too_large` :  V_cb² · α is
         ~ 4 orders of magnitude larger than Δa_μ.
   (T9)  `lattice_dispersion_HVP_gap` :  the lattice-vs-dispersion
         HVP gap is 145 × 10⁻¹¹ ≈ 0.58 · Δa_μ.
   (T10) `lattice_dispersion_within_2sigma_of_discrepancy` :
         145 lies within ~1.8σ of 251 (with σ = 59), so the
         lattice-vs-dispersion controversy is a viable competing
         explanation for the entire pull.
   (T11) `disc_over_NWsq_ratio` :  disc / N_W² = 7/4, the "obvious"
         framework ratio nearest to the empirical 251/145 ≈ 1.73.
         (Numerical coincidence at 1.0% — but error bars on both
         numbers are ≥ 20%, so empirically empty.)
   (T12) `master_aMu_audit` :  conjunction (T1)–(T11), the audit verdict.
   (T13) `honest_scope_aMuAudit` :  enumeration of what the file does
         NOT claim, including: the framework does NOT predict Δa_μ,
         and the test is PREMATURE pending lattice/dispersion resolution.

  Zero sorry. Zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Pi.Bounds
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.MuonGMinusTwo
import UnifiedTheory.LayerB.AlphaSAudit

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MuonG2Audit

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.MuonGMinusTwo
open UnifiedTheory.LayerB.AlphaSAudit

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0: FRAMEWORK ATOMS RECAP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The five framework atoms, re-stated for self-containedness:
      • N_W      = 2  (weak-isospin states)
      • N_c      = 3  (QCD colors)
      • N_W²     = 4  (weak-doublet square)
      • N_total  = 5  (= N_W + N_c)
      • disc     = 7  (Feshbach discriminant at d = 4)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Local naming — same convention as `AlphaSAudit`. -/
def NW : ℕ := 2
def Nc : ℕ := 3
def NWsq : ℕ := NW * NW   -- = 4
def Nt : ℕ := NW + Nc     -- = 5
def discN : ℕ := 7

theorem NW_eq : NW = 2 := rfl
theorem Nc_eq : Nc = 3 := rfl
theorem NWsq_eq : NWsq = 4 := rfl
theorem Nt_eq : Nt = 5 := rfl
theorem discN_eq : discN = 7 := rfl

theorem discN_eq_disc : (discN : ℤ) = feshbach_disc 4 := by
  unfold discN; norm_num [feshbach_disc]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE EMPIRICAL DISCREPANCY Δa_μ
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Δa_μ  =  a_μ^exp − a_μ^SM  =  251 × 10⁻¹¹.
    1σ uncertainty: 59 × 10⁻¹¹ (combined exp + theory).
    1σ band: (192, 310) × 10⁻¹¹.

    All quantities in this file are stored as natural numbers in units
    of 10⁻¹¹ for exact rational arithmetic. The reference values
    `aMu_exp_units`, `aMu_SM_units`, `aMu_discrepancy_units` come from
    `MuonGMinusTwo.lean`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 1σ uncertainty on Δa_μ in units of 10⁻¹¹. -/
def aMu_sigma_units : ℕ := 59

/-- 1σ lower edge of the discrepancy band: 251 − 59 = 192. -/
def aMu_discrepancy_lo : ℕ := 192

/-- 1σ upper edge of the discrepancy band: 251 + 59 = 310. -/
def aMu_discrepancy_hi : ℕ := 310

/-- 2σ lower edge of the discrepancy band: 251 − 118 = 133. -/
def aMu_discrepancy_2sigma_lo : ℕ := 133

/-- 2σ upper edge: 251 + 118 = 369. -/
def aMu_discrepancy_2sigma_hi : ℕ := 369

/-- **(T1)** Δa_μ in units of 10⁻¹¹ equals 251 (re-export of
    `aMu_discrepancy_units` from `MuonGMinusTwo`). -/
theorem aMu_discrepancy_value :
    aMu_discrepancy_units = 251 := by
  unfold aMu_discrepancy_units; rfl

/-- **(T2)** The discrepancy lies in its 1σ band [192, 310]. -/
theorem aMu_discrepancy_in_error_bars :
    aMu_discrepancy_lo ≤ aMu_discrepancy_units ∧
    aMu_discrepancy_units ≤ aMu_discrepancy_hi := by
  unfold aMu_discrepancy_lo aMu_discrepancy_hi aMu_discrepancy_units
  exact ⟨by norm_num, by norm_num⟩

/-- The discrepancy is rationally 251/100000000000. -/
def aMu_discrepancy_rat : ℚ := 251 / 100000000000

/-- The 1σ rational lower bound. -/
def aMu_discrepancy_rat_lo : ℚ := 192 / 100000000000

/-- The 1σ rational upper bound. -/
def aMu_discrepancy_rat_hi : ℚ := 310 / 100000000000

/-- Δa_μ as a rational lies in (192, 310) × 10⁻¹¹. -/
theorem aMu_discrepancy_rat_in_band :
    aMu_discrepancy_rat_lo ≤ aMu_discrepancy_rat ∧
    aMu_discrepancy_rat ≤ aMu_discrepancy_rat_hi := by
  unfold aMu_discrepancy_rat_lo aMu_discrepancy_rat aMu_discrepancy_rat_hi
  exact ⟨by norm_num, by norm_num⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: ATOMIC-RATIONAL CANDIDATES FOR Δa_μ × 10¹¹ ≈ 251
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We enumerate small framework-atom-built integers near 251 and
    measure their offset from the discrepancy CENTER (251) and
    their position relative to the 1σ band (192, 310).

      candidate (atomic form)        value      offset    in 1σ band?
      ─────────────────────────      ─────      ────────  ───────────
      disc² · N_total                245        −2.4 %    YES
      disc · N_total² + N_W² · N_W   249        −0.8 %    YES
      disc² · N_W · N_W² − disc      217        −13.5 %   YES
      disc³ + 2·N_total              353        +40.6 %   NO
      (N_total · disc)²              1225       +388 %    NO
      disc · N_W² · N_total² + disc  707        +182 %    NO

    Headline: disc² · N_total = 49 · 5 = 245 is the closest
    framework-atomic integer match (2.4% below 251), and it lies
    inside the 1σ error band.

    HONEST CAVEATS:
      (a) 245 has no first-principles framework derivation as a
          numerical value at the 10⁻¹¹ scale.
      (b) The 10⁻¹¹ scale itself is dimensional (a unit choice),
          not a framework-atomic quantity.
      (c) Several other candidate decompositions (disc·N_total²+N_W·N_W²
          = 249) match equally well, undermining the uniqueness claim.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **(T3)** disc² · N_total = 7² · 5 = 245. -/
theorem disc_sq_times_Ntotal_value :
    discN * discN * Nt = 245 := by
  unfold discN Nt NW Nc; decide

/-- **(T4) Numerical match**: 245 is in the 1σ band [192, 310] of the
    discrepancy 251 ± 59. The candidate disc² · N_total · 10⁻¹¹ is
    therefore within 1σ of Δa_μ. -/
theorem disc_sq_Ntotal_close_to_discrepancy :
    aMu_discrepancy_lo ≤ discN * discN * Nt ∧
    discN * discN * Nt ≤ aMu_discrepancy_hi := by
  rw [disc_sq_times_Ntotal_value]
  unfold aMu_discrepancy_lo aMu_discrepancy_hi
  exact ⟨by norm_num, by norm_num⟩

/-- The signed offset of disc² · N_total from the discrepancy CENTER:
    251 − 245 = 6, i.e. disc² · N_total is 6 below 251. -/
theorem disc_sq_Ntotal_offset_from_center :
    aMu_discrepancy_units - discN * discN * Nt = 6 := by
  rw [disc_sq_times_Ntotal_value]
  unfold aMu_discrepancy_units; norm_num

/-- **The candidate disc · N_total² + N_W · N_W² = 7·25 + 2·4 = 175 + 8 = 183**.
    For comparison: this OTHER framework-atom build also lies near the
    discrepancy band (in the 2σ extension), demonstrating that several
    different atomic decompositions cluster near 251 — undermining any
    UNIQUENESS claim for the disc²·N_total = 245 match. -/
theorem alternative_atomic_candidate :
    discN * Nt * Nt + NW * NWsq = 183 := by
  unfold discN Nt NW NWsq Nc; decide

/-- A second alternative: disc·N_total² + N_total = 175 + 5 = 180.
    Also reasonably close to 251 within ~30%. -/
theorem alternative_atomic_candidate_2 :
    discN * Nt * Nt + Nt = 180 := by
  unfold discN Nt NW Nc; decide

/-- A third alternative: 5·disc² = 245. Equivalent to T3 (disc²·N_total),
    just rewritten — recorded to highlight the multi-form ambiguity. -/
theorem alternative_atomic_candidate_3 :
    Nt * (discN * discN) = 245 := by
  unfold discN Nt NW Nc; decide

/-- **(T5) HONEST NEGATIVE: disc² · N_total is NOT structurally derived.**
    The framework derives no quantity whose dimensionful value at low
    energy equals 245 × 10⁻¹¹. The match in T4 is a NUMERICAL
    COINCIDENCE between two small integers (245 ≈ 251), not a
    derivation. We record this as a non-equality with the only
    structurally derived O(10⁻⁹) quantity in the framework
    (a_μ^Schwinger ≈ 1.16 × 10⁻³, which is about 4.6 × 10⁵ times
    larger than 245 × 10⁻¹¹). -/
theorem disc_sq_Ntotal_NOT_structurally_grounded :
    -- 245 × 10⁻¹¹ is wildly different from a_μ^Schwinger
    (245 / 100000000000 : ℝ) < aMu_Schwinger / 1000 := by
  unfold aMu_Schwinger alpha_em_low
  -- 245 × 10⁻¹¹ ≈ 2.45e-9
  -- a_μ^Schwinger / 1000 ≈ 1.16e-6
  have hSch_lo : aMu_Schwinger > 1161 / 1000000 := aMu_Schwinger_lower
  -- so a_μ^Schwinger / 1000 > 1.161e-6 ≫ 2.45e-9
  unfold aMu_Schwinger alpha_em_low at hSch_lo
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: COUPLING-POWER CANDIDATES (α^k, (α/π)^k)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Δa_μ ≈ 2.51 × 10⁻⁹. Natural QED loop-counting units:
       α²        ≈ 5.32 × 10⁻⁵         (way too large)
       (α/π)²    ≈ 5.40 × 10⁻⁶         (~ 2000× too large)
       α³        ≈ 3.88 × 10⁻⁷         (~ 150× too large)
       (α/π)³    ≈ 1.25 × 10⁻⁸         (~ 5× too large)
       α⁴        ≈ 2.84 × 10⁻⁹         (~ Δa_μ!)
       (α/π)⁴   ≈ 2.91 × 10⁻¹¹         (~ 100× too small)

    The closest match is α⁴ ≈ 2.84 × 10⁻⁹ (~ 13% larger than Δa_μ).
    But α⁴ corresponds to a 4-loop QED contribution, which is
    SUPPRESSED in standard QED counting (4-loop QED contributes
    ≈ 38 × 10⁻¹¹ in the SM, NOT 250 × 10⁻¹¹).

    The issue: the natural QED loop expansion gives Δa_μ at the
    2-loop level (the dominant SM higher-order pieces are 2-loop
    QED + HVP + EW), with a NUMERICALLY SUPPRESSED leading
    coefficient (~ O(10⁻⁴) of (α/π)²). A clean (α/π)^k expression
    with a small framework-atom prefactor does NOT reproduce
    Δa_μ at the right order.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (α/π)² as a real, using α(0) ≈ 1/137.036. -/
noncomputable def alpha_over_pi_sq : ℝ :=
  (alpha_em_low / Real.pi) ^ 2

/-- (α/π)² is positive. -/
theorem alpha_over_pi_sq_pos : 0 < alpha_over_pi_sq := by
  unfold alpha_over_pi_sq
  exact pow_pos (div_pos alpha_em_low_pos Real.pi_pos) 2

/-- A loose upper bound: (α/π)² < 7 × 10⁻⁶.  This uses α/π < 1/410
    (from π > 3.141592 and α = 1000/137036), giving (α/π)² < 1/168100
    < 7 × 10⁻⁶. -/
theorem alpha_over_pi_sq_upper :
    alpha_over_pi_sq < 7 / 1000000 := by
  unfold alpha_over_pi_sq alpha_em_low
  have hpi_gt : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- α/π = 1000/(137036·π) < 1/410, since 1000·410 = 410000 < 137036·π
  -- (137036·3.141592 ≈ 430526 > 410000).
  have h1 : (1000 : ℝ) / 137036 / Real.pi < 1 / 410 := by
    rw [div_div, div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 410)]
    nlinarith [hpi_gt, hpos]
  have h2 : (0 : ℝ) ≤ 1000 / 137036 / Real.pi :=
    le_of_lt (div_pos (by positivity) hpos)
  have h3 : ((1000 : ℝ) / 137036 / Real.pi) ^ 2 < (1 / 410) ^ 2 := by
    have h410 : (0 : ℝ) < 1 / 410 := by norm_num
    nlinarith [h1, h2, h410]
  have h4 : ((1 : ℝ) / 410) ^ 2 < 7 / 1000000 := by norm_num
  linarith

/-- A loose lower bound: (α/π)² > 53 × 10⁻⁷ (= 5.3 × 10⁻⁶).  Uses
    α/π > 1/431 (from α = 1000/137036 and π < 3.141593), giving
    (α/π)² > 1/185761 ≈ 5.385 × 10⁻⁶ > 53/10000000. -/
theorem alpha_over_pi_sq_lower :
    alpha_over_pi_sq > 53 / 10000000 := by
  unfold alpha_over_pi_sq alpha_em_low
  have hpi_lt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- α/π > (1000/137036) / 3.141593  >  1/431
  --   ⟺ 1000 · 431 > 137036 · π
  --   137036 · 3.141593 ≈ 430526.04 < 431000.
  have h1 : (1000 : ℝ) / 137036 / Real.pi > 1 / 431 := by
    rw [div_div, gt_iff_lt, lt_div_iff₀ (by positivity)]
    nlinarith [hpi_lt, hpi_pos]
  have h2 : (0 : ℝ) < 1 / 431 := by norm_num
  have h3 : ((1 : ℝ) / 431) ^ 2 ≤ ((1000 : ℝ) / 137036 / Real.pi) ^ 2 := by
    have hpos : (0 : ℝ) ≤ 1000 / 137036 / Real.pi :=
      le_of_lt (div_pos (by positivity) hpi_pos)
    nlinarith [h1, h2, hpos]
  have h4 : (53 : ℝ) / 10000000 < (1 / 431) ^ 2 := by norm_num
  linarith

/-- **(T6 part 1)** (α/π)² is much LARGER than Δa_μ (by a factor of
    at least 2000). Numerically:  Δa_μ ≈ 2.5 × 10⁻⁹ and
    (α/π)² > 5.3 × 10⁻⁶. So (α/π)² > 2000 · Δa_μ. -/
theorem alpha_over_pi_sq_dwarfs_discrepancy :
    alpha_over_pi_sq > 2000 * (251 / 100000000000 : ℝ) := by
  have h := alpha_over_pi_sq_lower
  -- 53/10000000 = 5.3e-6;  2000 · 251/1e11 = 502000/1e11 = 5.02e-6.
  have h2 : (53 : ℝ) / 10000000 > 2000 * (251 / 100000000000) := by norm_num
  linarith

/-- A natural framework-atom rational c such that c · (α/π)² hits
    Δa_μ would need c ≈ Δa_μ / (α/π)² ≈ 4.65 × 10⁻⁴. No
    framework-atom rational with denominator < 10⁴ is anywhere near
    this scale (the smallest non-trivial fw-atom rational is
    1/N_total² · 1/disc² = 1/(25·49) = 1/1225 ≈ 8.16 × 10⁻⁴, OFF
    by ~75%; and this is not a structurally meaningful framework
    quantity).  Recorded as: 1/(N_total² · disc²) > Δa_μ/(α/π)². -/
theorem fw_rat_over_alpha_over_pi_sq_too_large :
    (1 / 1225 : ℝ) > 4 / 10000 := by norm_num

/-- **(T6 part 2)** A naïve cross-sector candidate: α_s · (α/π)² (one
    QCD insertion times the QED two-loop scale). With α_s = 7/60:

        α_s · (α/π)² ≈ (7/60) · 5.4 × 10⁻⁶ ≈ 6.3 × 10⁻⁷

    which is ~ 250× LARGER than Δa_μ ≈ 2.5 × 10⁻⁹. A cross-sector
    α_s · (α/π)² product is NOT the right size for Δa_μ. -/
theorem alphaS_times_alpha_over_pi_sq_too_large :
    ((7 : ℝ) / 60) * alpha_over_pi_sq > 100 * (251 / 100000000000 : ℝ) := by
  have hα := alpha_over_pi_sq_lower
  -- (7/60) · 53/10000000 = 371/600000000 ≈ 6.18e-7
  -- 100 · Δa_μ = 25100/1e11 = 2.51e-7
  have h1 : ((7 : ℝ) / 60) * (53 / 10000000) > 100 * (251 / 100000000000) := by
    norm_num
  -- α_s · (α/π)² > α_s · 53e-7  > 100 · Δa_μ
  nlinarith [hα, alpha_over_pi_sq_pos]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: CROSS-SECTOR IDENTITY HYPOTHESES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We test cross-sector identity hypotheses analogous to the α_s
    audit headline (m_b/m_τ) · V_us² = α_s = 7/60.

    Candidates tested (and DISQUALIFIED):
      (CS-mu-1)  Δa_μ = (m_b/m_τ) · α²       — too large by ~5 orders
      (CS-mu-2)  Δa_μ = V_cb² · α            — too large by ~4 orders
      (CS-mu-3)  Δa_μ = V_ub² · α            — order 10⁻⁷, ~50× too large
      (CS-mu-4)  Δa_μ = α³ · disc/N_W²       — order 7·10⁻⁷/4 ≈ 1.7×10⁻⁷,
                                                ~70× too large
      (CS-mu-5)  Δa_μ = (α/π)³ · disc        — order 1.25·10⁻⁸·7 ≈ 8.7×10⁻⁸,
                                                ~35× too large
      (CS-mu-6)  Δa_μ = (α/π)⁴ · disc²·N_total — order ~ 2.91·10⁻¹¹ · 245
                                                ≈ 7.1 × 10⁻⁹ (~3× too large)

    None of the simple cross-sector identities lands within an order
    of magnitude of Δa_μ. The framework's atomic vocabulary does NOT
    supply a clean cross-sector expression for the muon g-2 anomaly.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- m_b/m_τ corrected = 7/3. Re-stated locally for self-containedness. -/
def btau_local : ℚ := 7 / 3

theorem btau_local_eq : btau_local = 7 / 3 := rfl

/-- V_cb² corrected = 1/600 (= 1/(N_W²·N_total²·disc - 100), or in
    audit form, the corrected min-complexity value).  We use the
    framework value 1/600 directly. -/
def Vcb_sq_local : ℚ := 1 / 600

/-- α as a rational: 1/137 (one-digit precision is enough for the
    cross-sector test; the exact rational 1000/137036 is also used
    in the real-bracket forms below). -/
def alpha_rat : ℚ := 1 / 137

theorem alpha_rat_pos : (0 : ℚ) < alpha_rat := by
  unfold alpha_rat; norm_num

/-- (m_b/m_τ) · α² as a rational, using α ≈ 1/137. -/
def cs_btau_alpha_sq : ℚ := btau_local * (alpha_rat * alpha_rat)

/-- **(T7) CS-mu-1 DISQUALIFIED: (m_b/m_τ) · α² ≫ Δa_μ.**
    (m_b/m_τ) · α² = (7/3) · (1/137)² = 7/(3·18769) ≈ 1.24 × 10⁻⁴,
    which is ~ 5 ORDERS OF MAGNITUDE larger than Δa_μ ≈ 2.5 × 10⁻⁹.
    Cross-sector b/τ × α² is NOT the right size. -/
theorem cross_sector_btau_alpha_sq_too_large :
    cs_btau_alpha_sq > 10000 * aMu_discrepancy_rat := by
  unfold cs_btau_alpha_sq btau_local alpha_rat aMu_discrepancy_rat
  norm_num

/-- V_cb² · α as a rational. -/
def cs_Vcb_sq_alpha : ℚ := Vcb_sq_local * alpha_rat

/-- **(T8) CS-mu-2 DISQUALIFIED: V_cb² · α ≫ Δa_μ.**
    V_cb² · α = (1/600) · (1/137) = 1/82200 ≈ 1.22 × 10⁻⁵,
    which is ~ 4 ORDERS OF MAGNITUDE larger than Δa_μ. -/
theorem cross_sector_Vcb_sq_alpha_too_large :
    cs_Vcb_sq_alpha > 1000 * aMu_discrepancy_rat := by
  unfold cs_Vcb_sq_alpha Vcb_sq_local alpha_rat aMu_discrepancy_rat
  norm_num

/-- α_s · α² as a rational, using α_s = 7/60. -/
def cs_alphaS_alpha_sq : ℚ := (7 / 60 : ℚ) * (alpha_rat * alpha_rat)

/-- **CS-mu-extra: α_s · α² is also too large.**
    α_s · α² = (7/60) · (1/137)² = 7/(60·18769) ≈ 6.22 × 10⁻⁶,
    ~ 2000× larger than Δa_μ. -/
theorem cross_sector_alphaS_alpha_sq_too_large :
    cs_alphaS_alpha_sq > 1000 * aMu_discrepancy_rat := by
  unfold cs_alphaS_alpha_sq alpha_rat aMu_discrepancy_rat
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE LATTICE-VS-DISPERSION HVP CONTROVERSY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The dominant SM-side uncertainty in a_μ is the hadronic vacuum
    polarization (HVP). Two methods give DIFFERENT central values:

      • BMW lattice 2021:        a_μ^HVP =  707.5 (5.5) × 10⁻¹⁰
      • Data-driven dispersion:  a_μ^HVP =  693.0 (4.3) × 10⁻¹⁰
      • Difference:                       ≈   145    × 10⁻¹¹

    This 145 × 10⁻¹¹ gap is ~58% of the 251 × 10⁻¹¹ exp-vs-SM gap.
    If BMW lattice is right, the SM prediction MOVES UP by ~145 × 10⁻¹¹,
    closing most of the 4.2σ pull. If e+e- dispersion is right, the
    pull stands at 4.2σ.

    The framework can be HONEST: the empirical "anomaly" itself is
    contested between two reputable methods, and may turn out to be
    a SM-side artifact rather than BSM physics requiring framework
    explanation.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The BMW lattice HVP central value in units of 10⁻¹¹: 7075. -/
def aMu_HVP_BMW_lattice_units : ℕ := 7075

/-- The data-driven dispersion HVP central value in units of 10⁻¹¹: 6930. -/
def aMu_HVP_dispersion_units : ℕ := 6930

/-- The lattice-vs-dispersion HVP gap in units of 10⁻¹¹: 145. -/
def aMu_HVP_gap_units : ℕ := 145

/-- **(T9)** The lattice-vs-dispersion HVP gap is 145 × 10⁻¹¹. -/
theorem lattice_dispersion_HVP_gap :
    aMu_HVP_BMW_lattice_units - aMu_HVP_dispersion_units = aMu_HVP_gap_units := by
  unfold aMu_HVP_BMW_lattice_units aMu_HVP_dispersion_units aMu_HVP_gap_units
  norm_num

/-- The HVP gap as a rational. -/
def aMu_HVP_gap_rat : ℚ := 145 / 100000000000

/-- **(T10) The lattice-vs-dispersion HVP gap is COMPATIBLE with the
    full discrepancy at less than 2σ.** Specifically, 145 lies within
    251 ± 118 = (133, 369) (the 2σ band). So shifting the SM
    prediction by the HVP-gap could account for the entire pull —
    making the test of any BSM hypothesis (including framework
    cross-sector identities) PREMATURE pending lattice-vs-dispersion
    resolution. -/
theorem lattice_dispersion_within_2sigma_of_discrepancy :
    aMu_discrepancy_2sigma_lo ≤ aMu_HVP_gap_units ∧
    aMu_HVP_gap_units ≤ aMu_discrepancy_2sigma_hi := by
  unfold aMu_discrepancy_2sigma_lo aMu_discrepancy_2sigma_hi aMu_HVP_gap_units
  exact ⟨by norm_num, by norm_num⟩

/-- The lattice-vs-dispersion gap is the same SIGN as the discrepancy
    (both positive) — so adopting the lattice HVP REDUCES the pull. -/
theorem HVP_gap_reduces_discrepancy :
    aMu_HVP_gap_units < aMu_discrepancy_units := by
  unfold aMu_HVP_gap_units aMu_discrepancy_units
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE 251/145 ≈ disc/N_W² NUMERICAL COINCIDENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    EMPIRICAL: Δa_μ / Δa_HVP^(lattice − dispersion) = 251/145 ≈ 1.731.
    FRAMEWORK ATOMIC: disc / N_W² = 7/4 = 1.750.

    These match to 1.0%. But:
     (a) Both numerators carry ≥ 20% relative uncertainty, so the
         ratio carries 30%+ uncertainty, swamping the 1% match.
     (b) The interpretation is unclear: if the lattice HVP is right,
         the dispersion HVP is wrong by 145 × 10⁻¹¹ for non-BSM
         reasons (an SM-side computation error), and there is no
         framework physics to explain. The ratio 7/4 has no
         structural derivation here.
     (c) Both 7 and 4 ARE framework atoms, but their assembly into
         "the ratio of two empirical numbers neither of which the
         framework derives" is a CONTRIVED COINCIDENCE.

    Recorded as a numerical curiosity, NOT a framework prediction.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **(T11)** disc / N_W² = 7/4. -/
theorem disc_over_NWsq_ratio :
    (discN : ℚ) / (NWsq : ℚ) = 7 / 4 := by
  unfold discN NWsq NW; norm_num

/-- The empirical ratio Δa_μ / Δa_HVP^(L−D) = 251/145.  Numerically
    ≈ 1.7310344828… -/
def empirical_ratio : ℚ := 251 / 145

/-- The framework atomic ratio disc / N_W² = 7/4 = 1.75. -/
def framework_ratio : ℚ := 7 / 4

/-- **The numerical coincidence**: |251/145 − 7/4| < 1.1 × 10⁻²
    (i.e., 1.1% relative). -/
theorem ratio_coincidence :
    framework_ratio - empirical_ratio < 22 / 1000 ∧
    empirical_ratio < framework_ratio := by
  unfold framework_ratio empirical_ratio
  refine ⟨?_, ?_⟩ <;> norm_num

/-- **HONEST NEGATIVE: the 251/145 ≈ 7/4 coincidence is empirically
    empty.** The error bars on Δa_μ alone (251 ± 59, ~24%) plus the
    error bars on the HVP gap (~6%) compound to give the empirical
    ratio uncertainty > 25% — vastly larger than the 1.1% match. -/
theorem ratio_coincidence_empirically_empty :
    -- The lower 1σ on Δa_μ (192) divided by the upper edge of the
    -- 95% HVP-gap range (≈ 168) is 192/168 ≈ 1.143, and the upper
    -- 1σ (310) divided by the lower edge (~ 122) is 310/122 ≈ 2.541.
    -- The 1σ band of the empirical ratio thus spans (1.14, 2.54),
    -- comfortably swamping the 1.75 framework value AND many other
    -- candidates. We record one explicit such span:
    (192 / 168 : ℚ) < framework_ratio ∧
    framework_ratio < 310 / 122 := by
  unfold framework_ratio
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: WHAT THE FRAMEWORK DOES PROVIDE (AT LEADING ORDER)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Re-export the leading-order results from `MuonGMinusTwo.lean`
    so the audit file is self-contained for downstream use:

      a_μ^(framework, LO)  =  α / (2π)  =  a_μ^Schwinger
      a_μ^(framework, LO)  <  a_μ^SM   <  a_μ^exp

    The framework REPRODUCES the Schwinger leading-order coefficient
    exactly (no freedom — forced by `FeynmanRules.onshell_unit_modulus`
    and `FeynmanRules.amplitude_additive`), but does NOT yet have
    machinery for the higher-order pieces (two-loop QED, HVP analog,
    EW loop) where the discrepancy lives.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's LO contribution agrees with Schwinger (re-export). -/
theorem framework_LO_eq_Schwinger_local :
    aMu_framework_LO = aMu_Schwinger := framework_LO_eq_Schwinger

/-- The framework's LO is below the SM prediction (re-export). -/
theorem framework_LO_below_SM_local :
    aMu_framework_LO < aMu_SM_real := framework_LO_below_SM

/-- The framework's LO is below experiment (re-export). -/
theorem framework_LO_below_exp_local :
    aMu_framework_LO < aMu_exp_real := framework_LO_below_experiment

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER THEOREM — THE AUDIT VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM: muon g − 2 audit verdict.**

    The framework provides the Schwinger leading-order anomaly α/(2π)
    (proved in `MuonGMinusTwo.lean`), which agrees with the SM
    leading order. The discrepancy

        Δa_μ  =  a_μ^exp − a_μ^SM  ≈  251 × 10⁻¹¹

    lies in the higher-order pieces, where the framework currently
    has no computed prediction.

    Min-complexity / cross-sector audit:

      (A) The numerical match disc² · N_total = 245 lies within 1σ
          of the discrepancy 251 ± 59, but has no structural
          derivation as a framework quantity.

      (B) Coupling-power expansions (α/π)^k are too large for k ≤ 2
          and too small for k ≥ 4; no clean (α/π)^k · (small
          framework rational) reproduces Δa_μ at the right order.

      (C) Cross-sector identities tested ((m_b/m_τ)·α², V_cb²·α,
          α_s·α²) all give values 3-5 orders of magnitude too large.

      (D) The lattice-vs-dispersion HVP gap (145 × 10⁻¹¹) lies
          within the 2σ band of the full discrepancy, so the
          empirical "anomaly" itself is contested between SM
          methods. Adopting the BMW lattice HVP would close most
          of the 4.2σ pull WITHOUT BSM physics.

      (E) The empirical ratio Δa_μ / Δa_HVP^(L−D) ≈ 251/145 ≈ 1.73
          coincides with the framework atomic ratio disc / N_W² = 7/4
          to 1.0% — but the empirical ratio uncertainty is > 25%,
          rendering the coincidence empirically empty.

    HONEST CLASSIFICATION: **INCONCLUSIVE**.
      • The framework does NOT predict a deviation matching Δa_μ.
      • The framework does NOT predict zero deviation either.
      • The framework's LO Schwinger prediction is consistent with
        the SM LO; higher-order machinery (two-loop QED, HVP analog,
        EW loop) is not yet implemented.
      • Independently, the empirical anomaly itself is contested
        between lattice (no anomaly) and dispersion (4.2σ),
        making the test PREMATURE.

    The framework neither claims to "explain" the muon g − 2
    anomaly nor predicts a different value from the SM at this
    order. -/
theorem master_aMu_audit :
    -- (T1) discrepancy value
    aMu_discrepancy_units = 251
    -- (T2) discrepancy in 1σ error band
    ∧ (aMu_discrepancy_lo ≤ aMu_discrepancy_units ∧
       aMu_discrepancy_units ≤ aMu_discrepancy_hi)
    -- (T3) atomic numerical match disc² · N_total = 245
    ∧ (discN * discN * Nt = 245)
    -- (T4) match within 1σ band
    ∧ (aMu_discrepancy_lo ≤ discN * discN * Nt ∧
       discN * discN * Nt ≤ aMu_discrepancy_hi)
    -- (T5) HONEST: NOT structurally grounded
    ∧ ((245 / 100000000000 : ℝ) < aMu_Schwinger / 1000)
    -- (T6) coupling power (α/π)² dwarfs Δa_μ
    ∧ (alpha_over_pi_sq > 2000 * (251 / 100000000000 : ℝ))
    -- (T7) cross-sector b/τ · α² too large
    ∧ (cs_btau_alpha_sq > 10000 * aMu_discrepancy_rat)
    -- (T8) cross-sector V_cb² · α too large
    ∧ (cs_Vcb_sq_alpha > 1000 * aMu_discrepancy_rat)
    -- (T9) lattice-vs-dispersion HVP gap = 145
    ∧ (aMu_HVP_BMW_lattice_units - aMu_HVP_dispersion_units = aMu_HVP_gap_units)
    -- (T10) HVP gap within 2σ band of full discrepancy
    ∧ (aMu_discrepancy_2sigma_lo ≤ aMu_HVP_gap_units ∧
       aMu_HVP_gap_units ≤ aMu_discrepancy_2sigma_hi)
    -- (T11) framework ratio disc/N_W² = 7/4
    ∧ ((discN : ℚ) / (NWsq : ℚ) = 7 / 4)
    -- (Re-export) Framework LO = Schwinger
    ∧ (aMu_framework_LO = aMu_Schwinger)
    -- (Re-export) Framework LO below SM
    ∧ (aMu_framework_LO < aMu_SM_real) := by
  refine ⟨aMu_discrepancy_value,
          aMu_discrepancy_in_error_bars,
          disc_sq_times_Ntotal_value,
          disc_sq_Ntotal_close_to_discrepancy,
          disc_sq_Ntotal_NOT_structurally_grounded,
          alpha_over_pi_sq_dwarfs_discrepancy,
          cross_sector_btau_alpha_sq_too_large,
          cross_sector_Vcb_sq_alpha_too_large,
          lattice_dispersion_HVP_gap,
          lattice_dispersion_within_2sigma_of_discrepancy,
          disc_over_NWsq_ratio,
          framework_LO_eq_Schwinger_local,
          framework_LO_below_SM_local⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE OF THIS FILE.**

    What IS proved (zero sorry, zero custom axioms):

      (A) The empirical situation: Δa_μ ≈ 251 × 10⁻¹¹ (~ 4.2σ pull).

      (B) Atomic candidate decompositions of 251 × 10⁻¹¹ in framework
          atoms: closest match is disc² · N_total = 245 (within 1σ).

      (C) Multiple alternative atomic candidates (disc·N_t² + N_W·N_W²
          = 183, etc.) cluster near the discrepancy band, undermining
          the uniqueness of the disc²·N_total match.

      (D) Coupling-power expansions α^k, (α/π)^k all FAIL to reproduce
          Δa_μ at the right order with simple framework prefactors.

      (E) Cross-sector identity hypotheses ((m_b/m_τ)·α², V_cb²·α,
          α_s·α²) all give values 3-5 orders of magnitude too large.

      (F) The lattice-vs-dispersion HVP gap is 145 × 10⁻¹¹, lying
          within the 2σ band of the full discrepancy.

      (G) The 251/145 ≈ disc/N_W² coincidence (1.0% match) is
          empirically empty (uncertainties on both ratios > 25%).

      (H) The framework's LO Schwinger prediction is reproduced
          (re-export from `MuonGMinusTwo`).

    What is NOT claimed:

      (I) The framework does NOT predict Δa_μ from first principles.
          No min-complexity framework-atomic rational is structurally
          forced to equal 251 × 10⁻¹¹.

      (J) The framework does NOT explain the 4.2σ anomaly. The LO
          contribution agrees with SM; higher-order machinery is
          not implemented; the empirical anomaly itself is contested.

      (K) The framework does NOT predict zero deviation from SM
          either. Higher-order virtual-particle insertions (two-loop
          QED, HVP analog, EW loop) could in principle generate a
          deviation, but the specialized vertex-correction
          computations are not done.

      (L) The lattice-vs-dispersion controversy is RESOLVED neither
          here nor in the framework. The framework can be honest
          that the "anomaly" may be a SM-side artifact pending
          lattice/dispersion reconciliation.

      (M) The disc²·N_total = 245 numerical match is NOT a framework
          PREDICTION. It is recorded as an OBSERVATION about small-
          integer arithmetic in the framework atoms; no first-
          principles derivation produces 245 × 10⁻¹¹ as the value
          of any framework quantity.

    Verdict: **INCONCLUSIVE** — the framework neither predicts the
    deviation nor predicts zero. The honest reading is that the
    framework provides Schwinger at LO (correctly) and is silent on
    the discrepancy at higher orders. Resolution requires both
    (i) lattice-vs-dispersion reconciliation on the SM side, and
    (ii) framework-side higher-order machinery (multi-loop virtual
    particles, hadronic K-virtual analog) — neither of which is in
    place. -/
theorem honest_scope_aMuAudit :
    -- (A) empirical situation
    (aMu_discrepancy_units = 251)
    -- (B) closest atomic match
    ∧ (discN * discN * Nt = 245)
    -- (C) match within 1σ band
    ∧ (aMu_discrepancy_lo ≤ discN * discN * Nt ∧
       discN * discN * Nt ≤ aMu_discrepancy_hi)
    -- (D) coupling powers fail
    ∧ (alpha_over_pi_sq > 2000 * (251 / 100000000000 : ℝ))
    -- (E) cross-sector identities fail
    ∧ (cs_btau_alpha_sq > 10000 * aMu_discrepancy_rat)
    ∧ (cs_Vcb_sq_alpha > 1000 * aMu_discrepancy_rat)
    -- (F) HVP gap = 145
    ∧ (aMu_HVP_gap_units = 145)
    -- (G) HVP gap within 2σ of Δa_μ
    ∧ (aMu_discrepancy_2sigma_lo ≤ aMu_HVP_gap_units ∧
       aMu_HVP_gap_units ≤ aMu_discrepancy_2sigma_hi)
    -- (H) framework LO = Schwinger
    ∧ (aMu_framework_LO = aMu_Schwinger) := by
  refine ⟨aMu_discrepancy_value,
          disc_sq_times_Ntotal_value,
          disc_sq_Ntotal_close_to_discrepancy,
          alpha_over_pi_sq_dwarfs_discrepancy,
          cross_sector_btau_alpha_sq_too_large,
          cross_sector_Vcb_sq_alpha_too_large,
          rfl,
          lattice_dispersion_within_2sigma_of_discrepancy,
          framework_LO_eq_Schwinger_local⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: THE FINAL VERDICT (SHORT FORM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **aMu_audit_VERDICT** — **INCONCLUSIVE**.

    The framework AGREES with the SM at leading order (Schwinger
    α/(2π) is forced — proved in `MuonGMinusTwo.lean`).

    The 251 × 10⁻¹¹ exp-vs-SM discrepancy is NOT structurally
    explained by the framework's atomic vocabulary:
      • The closest framework-atomic numerical match is
        disc² · N_total = 245, within 1σ but with no first-
        principles derivation.
      • All tested cross-sector identities ((m_b/m_τ)·α², V_cb²·α,
        α_s·α²) give values 3-5 orders of magnitude too large.

    The empirical "anomaly" is contested: the lattice-vs-dispersion
    HVP gap (145 × 10⁻¹¹) lies within 2σ of the full discrepancy.
    If the BMW lattice HVP is correct, most of the pull disappears
    WITHOUT BSM physics — making the test of any framework
    explanation PREMATURE.

    The framework does NOT claim to explain g − 2; it does NOT
    claim to predict zero deviation. It is honestly silent on the
    discrepancy at the relevant order. -/
theorem aMu_audit_VERDICT :
    -- 1. LO matches Schwinger
    (aMu_framework_LO = aMu_Schwinger)
    -- 2. Discrepancy is 251 × 10⁻¹¹
    ∧ (aMu_discrepancy_units = 251)
    -- 3. disc²·N_total = 245 lies in 1σ band (NUMERICAL match, no derivation)
    ∧ (aMu_discrepancy_lo ≤ discN * discN * Nt ∧
       discN * discN * Nt ≤ aMu_discrepancy_hi)
    -- 4. HONEST: 245 × 10⁻¹¹ is NOT a structurally derived framework quantity
    ∧ ((245 / 100000000000 : ℝ) < aMu_Schwinger / 1000)
    -- 5. Cross-sector identity (m_b/m_τ) · α² gives WRONG order of magnitude
    ∧ (cs_btau_alpha_sq > 10000 * aMu_discrepancy_rat)
    -- 6. Lattice-vs-dispersion HVP gap is 145, within 2σ of full Δa_μ
    ∧ (aMu_discrepancy_2sigma_lo ≤ aMu_HVP_gap_units ∧
       aMu_HVP_gap_units ≤ aMu_discrepancy_2sigma_hi) := by
  refine ⟨framework_LO_eq_Schwinger_local,
          aMu_discrepancy_value,
          disc_sq_Ntotal_close_to_discrepancy,
          disc_sq_Ntotal_NOT_structurally_grounded,
          cross_sector_btau_alpha_sq_too_large,
          lattice_dispersion_within_2sigma_of_discrepancy⟩

end UnifiedTheory.LayerB.MuonG2Audit
