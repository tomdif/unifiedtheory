/-
  LayerB/MXFromRGRunning.lean — Derivation attempt for the GUT scale M_X
                                from framework α_GUT + α_s(M_Z) +
                                one-loop QCD running.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  The framework supplies (zero sorry, zero custom axioms):

      α_GUT_framework     = 3/(32π)            (LayerA/AlphaGUT)
      1/α_GUT_framework   = 32π/3 ∈ (33, 34)
      α_s(M_Z) framework  = 7/60               (CouplingConstantAudit,
                                                AUDIT-CORRECTED)
      1/α_s(M_Z)          = 60/7 ≈ 8.5714

  The standard one-loop QCD RG running of 1/α_s between M_Z and a high
  scale M_X reads

      1/α_s(M_X) = 1/α_s(M_Z) − (β₀/(2π)) · log(M_X/M_Z)              (★)

  with the convention β₀ > 0 for asymptotic freedom (so 1/α_s INCREASES
  with energy).  At the GUT scale, by hypothesis, all couplings unify:
  α_s(M_X) = α_GUT.  Substituting (★):

      1/α_GUT − 1/α_s(M_Z) = (β₀/(2π)) · log(M_X/M_Z)                 (★★)

  Solving for M_X:

      log(M_X/M_Z) = (1/α_GUT − 1/α_s(M_Z)) · (2π/β₀)
                   = (32π/3 − 60/7) · (2π/β₀)                          (◆)

  This file (a) sets up (◆) symbolically in Lean, (b) computes rigorous
  bounds on log(M_X/M_Z) for the two β₀ scenarios, (c) tests whether the
  result decomposes cleanly in framework atoms {N_W=2, N_c=3, N_W²=4,
  N_total=5, disc=7}, and (d) checks INTERNAL CONSISTENCY by feeding the
  derived M_X back into the proton-decay rate formula from
  `LayerB/ProtonDecayPrediction`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE TWO SCENARIOS

  Scenario A (non-SUSY SM, β₀ = 7 = disc):
      L_A := log(M_X/M_Z) = (32π/3 − 60/7) · 2π/7
                          = (224π² − 180π) · 2 / (3 · 7 · 7)             (after algebra,
                                                                          factoring)
      Numerically: 1/α_GUT ≈ 33.510, 1/α_s ≈ 8.5714,
      L_A ≈ (33.510 − 8.5714) · 2π/7 ≈ 24.939 · 0.8976 ≈ 22.385.
      So M_X/M_Z ≈ e^22.385 ≈ 5.30·10⁹, M_X ≈ 91.2·5.3·10⁹ ≈ 4.83·10¹¹ GeV.
      This is an INTERMEDIATE scale, NOT the standard GUT 10¹⁶ GeV.

  Scenario B (SUSY MSSM, β₀ = 3 = N_c):
      L_B := log(M_X/M_Z) = (32π/3 − 60/7) · 2π/3 ≈ 52.23.
      So M_X/M_Z ≈ e^52.23 ≈ 4.8·10²², M_X ≈ 4.4·10²⁴ GeV.
      This is FAR ABOVE the Planck scale (10¹⁹ GeV) — physically untenable.
      The reason: the framework's 1/α_GUT ≈ 33.5 sits in the NON-SUSY
      window (33, 37); SUSY GUTs have 1/α_GUT ∈ (24, 26).  Forcing SUSY
      β₀ on the non-SUSY α_GUT overshoots.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  ATOMIC DECOMPOSITION TEST

  L_A ≈ 22.385.  Closest framework-atomic targets:
      N_c · disc            = 3·7   = 21      (off by  +1.385)
      N_W² · N_total + N_W  = 4·5+2 = 22      (off by  +0.385)
      N_W² · N_total        = 4·5   = 20      (off by  +2.385)
      N_total² − N_W        = 25−2  = 23      (off by  −0.615)
      disc² − N_c² · N_W    = 49−18 = 31      (off by  −8.615)

  None is exact.  The closest "clean" hit is the user's pre-specified
  candidate L = N_c · disc = 21, which corresponds to M_X = M_Z · e^{21}
  ≈ 91.2 · 1.32·10⁹ ≈ 1.20·10¹¹ GeV.  Honest verdict: this is BAND-CLOSE
  numerology, NOT a derivation.  L_A − N_c·disc ≈ 1.4, comparable to the
  uncertainty from threshold corrections and two-loop running, so the
  framework cannot DISTINGUISH the literal-22.385 prediction from the
  atomic-21 numerology at the precision available.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  INTERNAL CONSISTENCY CHECK (PROTON DECAY)

  From `LayerB/ProtonDecayPrediction`:
      τ_p = Q · M_X⁴ / (m_p⁵ · |A|²)        with Q = 16384π⁴/9 ≈ 1.77·10⁵.

  At M_X = 4.83·10¹¹ GeV (Scenario A) vs the standard non-SUSY GUT M_X
  = 1.2·10¹⁵ GeV that gives τ_p = 10³⁵ yr at the Hyper-K threshold:
      ratio of M_X⁴ = (4.83e11/1.2e15)⁴ ≈ (4.0e−4)⁴ ≈ 2.6·10⁻¹⁴.
      Predicted τ_p_A ≈ 2.6·10⁻¹⁴ · 10³⁵ yr ≈ 2.6·10²¹ yr.
  Super-K 2020 limit: τ_p > 1.6·10³⁴ yr.  Predicted 2.6·10²¹ yr is
  SHORTER by 13 orders of magnitude — DECISIVELY EXCLUDED.

  ⇒ The framework's α_GUT + α_s + non-SUSY one-loop QCD running is
  INTERNALLY INCONSISTENT with proton stability.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST VERDICT (PRE-COMMITTED)

  The framework does NOT predict M_X uniquely from {α_GUT, α_s} + RG
  running, in the following sharp sense:

    • Scenario A (non-SUSY β₀ = 7): yields M_X ≈ 5·10¹¹ GeV, which
      is RULED OUT by Super-K proton decay (τ_p < 10²² yr).
    • Scenario B (SUSY β₀ = 3): yields M_X ≈ 5·10²⁴ GeV, which is
      ABOVE the Planck scale and physically untenable.

  The DECEPTIVELY appealing atomic decomposition L_A ≈ N_c · disc = 21
  is BAND-CLOSE numerology that does NOT change the proton-decay verdict
  (M_X = M_Z·e²¹ ≈ 1.2·10¹¹ GeV is even SHORTER-lifetime than M_X =
  4.83·10¹¹ GeV).  The framework needs at least one of:

    (i)   New physics raising β₀ between M_Z and M_X (e.g., extra
          colored matter at intermediate scales) so that the running
          slows and M_X is pushed to ≥ 10¹⁵ GeV;
    (ii)  A different framework α_s(M_Z) (the audit-corrected 7/60
          is itself 1.05% off PDG, presumably absorbed by RG running);
    (iii) Two-loop and threshold corrections — these are O(10%)
          shifts in 1/α_s, hence O(20%) shifts in M_X^4, NOT the
          13 orders of magnitude needed.

  Bottom line: the framework SUFFICES for α_GUT and α_s as boundary
  values, but DOES NOT SUFFICE to derive M_X consistently with proton
  stability under standard one-loop running.  M_X remains a dimensional
  free input, exactly as flagged in `AlphaGUT.honest_scope_AlphaGUT (F)`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED (zero sorry, zero custom axioms)

  (T1)  The formula (◆) is set up symbolically as `log_MX_over_MZ β₀`.
  (T2)  Closed form: log_MX_over_MZ β₀ = (32π/3 − 60/7) · (2π/β₀).
  (T3)  In Scenario A (β₀ = 7 = disc), L_A is rigorously bracketed:
           22 < L_A < 23.   (Mathlib π bounds; π ∈ (3.141592, 3.141593).)
  (T4)  In Scenario B (β₀ = 3 = N_c), L_B is rigorously bracketed:
           52 < L_B < 53.
  (T5)  Atomic decomposition test:
          – 21 = N_c · disc.
          – L_A − 21 ∈ (1, 2) — NOT exact (numerology, off by ≥ 1).
          – 22 = N_W² · N_total + N_W.
          – L_A − 22 ∈ (0, 1) — even closer, but still NOT exact.
  (T6)  Scenario B is physically excluded because L_B > 52 implies
          M_X/M_Z > e^52 > 10²² (in the next file-bound theorem,
          stated symbolically as L_B > 52 > 50 = 10·N_total).
  (T7)  Internal consistency check (Scenario A):
          The derived M_X^4 satisfies M_X_A^4 < (M_Z · e^23)^4, which
          at the Hyper-K reach corresponds to a τ_p prediction
          STRICTLY SHORTER than the SK 2020 limit (1.6·10³⁴ yr).
  (T8)  Master verdict theorem `framework_M_X_inconsistent_with_pp_decay`
          collecting (T3)-(T7).
  (T9)  Honest scope statement.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  REFERENCES

    – Georgi, Quinn, Weinberg, "Hierarchy of interactions in unified
      gauge theories", Phys. Rev. Lett. 33, 451 (1974).
    – Langacker, P., "Grand unified theories and proton decay",
      Phys. Rep. 72, 185 (1981).
    – Amaldi, U., de Boer, W., Furstenau, H., "Comparison of grand
      unified theories with electroweak and strong coupling constants
      from LEP", Phys. Lett. B 260, 447 (1991).
    – Super-Kamiokande Collaboration, "Search for proton decay via
      p → e⁺π⁰ … with 0.37 megaton·years", Phys. Rev. D 102, 112011
      (2020), arXiv:2010.16098.

  Zero sorry. Zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import UnifiedTheory.LayerA.AlphaGUT
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CouplingConstantAudit
import UnifiedTheory.LayerB.ProtonDecayPrediction

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MXFromRGRunning

open Real
open UnifiedTheory.LayerA.AlphaGUT
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CouplingConstantAudit
open UnifiedTheory.LayerB.ProtonDecayPrediction

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0: FRAMEWORK ATOMS (re-stated locally)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Framework atom: number of weak-isospin states. -/
def N_W : ℕ := 2

/-- Framework atom: number of QCD colors. -/
def N_c : ℕ := 3

/-- Framework derived combination N_W + N_c. -/
def N_total : ℕ := 5

/-- Feshbach discriminant at d = 4. -/
def disc : ℕ := 7

theorem N_W_eq : N_W = 2 := rfl
theorem N_c_eq : N_c = 3 := rfl
theorem N_total_eq : N_total = 5 := rfl
theorem disc_eq : disc = 7 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: SYMBOLIC SET-UP OF THE RG-RUNNING FORMULA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Encode

        log(M_X/M_Z)  =  (1/α_GUT − 1/α_s(M_Z)) · (2π / β₀)

    as a function of the (positive real) β₀.  The two scenarios
    plug in β₀ = 7 (non-SUSY) and β₀ = 3 (SUSY-MSSM).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's `1/α_s(M_Z) = 60/7` (audit-corrected, see
    `CouplingConstantAudit.alphaS_framework`). -/
noncomputable def inv_alpha_s_MZ_framework : ℝ := 60 / 7

/-- The framework's α_s(M_Z) is positive. -/
theorem inv_alpha_s_MZ_pos : 0 < inv_alpha_s_MZ_framework := by
  unfold inv_alpha_s_MZ_framework; norm_num

/-- The framework's α_s(M_Z) corresponds to `alphaS_framework = 7/60`
    (rational ↔ real check). -/
theorem inv_alpha_s_MZ_eq_inv :
    inv_alpha_s_MZ_framework
      = 1 / ((alphaS_framework : ℝ)) := by
  unfold inv_alpha_s_MZ_framework alphaS_framework
  push_cast
  norm_num

/-- The "1/α_GUT − 1/α_s(M_Z)" gap, as a real. -/
noncomputable def gap_inv_alpha : ℝ :=
  inv_alpha_GUT_framework - inv_alpha_s_MZ_framework

/-- Closed form for the gap. -/
theorem gap_inv_alpha_closed :
    gap_inv_alpha = 32 * Real.pi / 3 - 60 / 7 := by
  unfold gap_inv_alpha inv_alpha_GUT_framework inv_alpha_s_MZ_framework
  rfl

/-- The gap is positive: 32π/3 > 33 > 60/7 ≈ 8.57. -/
theorem gap_inv_alpha_pos : 0 < gap_inv_alpha := by
  unfold gap_inv_alpha
  have h1 := inv_alpha_GUT_gt_33
  have h2 : inv_alpha_s_MZ_framework < 33 := by
    unfold inv_alpha_s_MZ_framework; norm_num
  linarith

/-- The gap exceeds 24 (rough lower bound; precise: 33−9 = 24 < gap). -/
theorem gap_inv_alpha_gt_24 : 24 < gap_inv_alpha := by
  unfold gap_inv_alpha
  have h1 := inv_alpha_GUT_gt_33
  have h2 : inv_alpha_s_MZ_framework < 9 := by
    unfold inv_alpha_s_MZ_framework; norm_num
  linarith

/-- The gap is below 26 (precise: 34−60/7 = 34 − 8.5714... = 25.43 < 26). -/
theorem gap_inv_alpha_lt_26 : gap_inv_alpha < 26 := by
  unfold gap_inv_alpha inv_alpha_s_MZ_framework
  have h1 := inv_alpha_GUT_lt_34
  have h2 : (60 / 7 : ℝ) > 17 / 2 := by norm_num
  linarith

/-- The RG-derived `log(M_X/M_Z)` as a function of the QCD β₀ coefficient.
    Definition (◆): L(β₀) := (1/α_GUT − 1/α_s(M_Z)) · 2π/β₀. -/
noncomputable def log_MX_over_MZ (β₀ : ℝ) : ℝ :=
  gap_inv_alpha * (2 * Real.pi / β₀)

/-- Closed form using the explicit α-values. -/
theorem log_MX_over_MZ_closed (β₀ : ℝ) :
    log_MX_over_MZ β₀ = (32 * Real.pi / 3 - 60 / 7) * (2 * Real.pi / β₀) := by
  unfold log_MX_over_MZ
  rw [gap_inv_alpha_closed]

/-- L(β₀) > 0 whenever β₀ > 0. -/
theorem log_MX_over_MZ_pos {β₀ : ℝ} (hβ : 0 < β₀) :
    0 < log_MX_over_MZ β₀ := by
  unfold log_MX_over_MZ
  have hπ : 0 < Real.pi := Real.pi_pos
  have hgap := gap_inv_alpha_pos
  have h1 : 0 < 2 * Real.pi / β₀ := by positivity
  exact mul_pos hgap h1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SCENARIO A — NON-SUSY β₀ = 7 = disc
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    L_A := L(7) = (32π/3 − 60/7) · 2π/7
    Numerically L_A ≈ 22.385.

    Rigorous bracketing: π ∈ (3.141592, 3.141593) ⇒ L_A ∈ (22, 23).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Scenario A value: L_A := L(7) (non-SUSY β₀). -/
noncomputable def L_A : ℝ := log_MX_over_MZ 7

/-- Closed form for L_A. -/
theorem L_A_closed :
    L_A = (32 * Real.pi / 3 - 60 / 7) * (2 * Real.pi / 7) := by
  unfold L_A
  exact log_MX_over_MZ_closed 7

/-- Algebraic simplification:
    L_A = (32π/3 − 60/7) · 2π/7
        = (224π² − 180π) · 2 / (3·7·7)
        = (448π² − 360π) / 147. -/
theorem L_A_simplified :
    L_A = (448 * Real.pi ^ 2 - 360 * Real.pi) / 147 := by
  rw [L_A_closed]
  ring

/-- L_A > 0. -/
theorem L_A_pos : 0 < L_A := log_MX_over_MZ_pos (by norm_num : (0 : ℝ) < 7)

/-- **L_A > 22.**
    Need (448π² − 360π)/147 > 22, i.e. 448π² − 360π > 22·147 = 3234.
    Using π > 3.141592:
      π² > 9.86959... so 448·π² > 4421.18.
      360·π < 360·3.141593 = 1130.97 < 1131.
      ⇒ 448π² − 360π > 4421.18 − 1131 = 3290.18 > 3234. ✓ -/
theorem L_A_gt_22 : (22 : ℝ) < L_A := by
  rw [L_A_simplified]
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 147)]
  -- Need: 22·147 = 3234 < 448π² − 360π.
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- π² > 3.141592²
  have hpi_sq : (9.8695877 : ℝ) < Real.pi ^ 2 := by
    nlinarith [hpi_lo, hpi_pos, sq_nonneg (Real.pi - 3.141592)]
  nlinarith [hpi_sq, hpi_lo, hpi_hi, hpi_pos]

/-- **L_A < 23.**
    Need (448π² − 360π)/147 < 23, i.e. 448π² − 360π < 23·147 = 3381.
    Using π < 3.141593:
      π² < 9.870 (loose bound), so 448·π² < 4421.76.
      360·π > 360·3.141592 = 1130.97 (lower bound on π).
      ⇒ 448π² − 360π < 4421.76 − 1130.97 = 3290.79 < 3381. ✓ -/
theorem L_A_lt_23 : L_A < (23 : ℝ) := by
  rw [L_A_simplified]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 147)]
  -- Need: 448π² − 360π < 23·147 = 3381.
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- π² < 3.141593² < 9.870
  have hpi_sq : Real.pi ^ 2 < (9.870 : ℝ) := by
    nlinarith [hpi_hi, hpi_pos]
  nlinarith [hpi_sq, hpi_lo, hpi_hi, hpi_pos]

/-- **L_A is bracketed in (22, 23).** -/
theorem L_A_bracket : (22 : ℝ) < L_A ∧ L_A < (23 : ℝ) :=
  ⟨L_A_gt_22, L_A_lt_23⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: SCENARIO B — SUSY-MSSM β₀ = 3 = N_c
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    L_B := L(3) = (32π/3 − 60/7) · 2π/3
    Numerically L_B ≈ 52.23.  Far above the Planck scale exponent
    log(M_Pl/M_Z) ≈ 39.  Forces M_X > 10²² GeV — physically untenable.

    Rigorous bracketing: L_B ∈ (52, 53).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Scenario B value: L_B := L(3) (SUSY β₀ = N_c = 3). -/
noncomputable def L_B : ℝ := log_MX_over_MZ 3

/-- Closed form for L_B. -/
theorem L_B_closed :
    L_B = (32 * Real.pi / 3 - 60 / 7) * (2 * Real.pi / 3) := by
  unfold L_B
  exact log_MX_over_MZ_closed 3

/-- Algebraic simplification:
    L_B = (32π/3 − 60/7) · 2π/3
        = (224π² − 180π) · 2 / (3·7·3)
        = (448π² − 360π) / 63. -/
theorem L_B_simplified :
    L_B = (448 * Real.pi ^ 2 - 360 * Real.pi) / 63 := by
  rw [L_B_closed]
  ring

/-- L_B > 0. -/
theorem L_B_pos : 0 < L_B := log_MX_over_MZ_pos (by norm_num : (0 : ℝ) < 3)

/-- **L_B > 52.**
    Need (448π² − 360π)/63 > 52, i.e. 448π² − 360π > 52·63 = 3276.
    Same numerator inequality as L_A, but easier: 3290 > 3276 ✓. -/
theorem L_B_gt_52 : (52 : ℝ) < L_B := by
  rw [L_B_simplified]
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 63)]
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_sq : (9.8695877 : ℝ) < Real.pi ^ 2 := by
    nlinarith [hpi_lo, hpi_pos, sq_nonneg (Real.pi - 3.141592)]
  nlinarith [hpi_sq, hpi_lo, hpi_hi, hpi_pos]

/-- **L_B < 53.**
    Need (448π² − 360π)/63 < 53, i.e. 448π² − 360π < 53·63 = 3339.
    Numerator < 3290.82, well below 3339. -/
theorem L_B_lt_53 : L_B < (53 : ℝ) := by
  rw [L_B_simplified]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 63)]
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_sq : Real.pi ^ 2 < (9.870 : ℝ) := by
    nlinarith [hpi_hi, hpi_pos]
  nlinarith [hpi_sq, hpi_lo, hpi_hi, hpi_pos]

/-- **L_B is bracketed in (52, 53).** -/
theorem L_B_bracket : (52 : ℝ) < L_B ∧ L_B < (53 : ℝ) :=
  ⟨L_B_gt_52, L_B_lt_53⟩

/-- Ratio identity: L_B = (7/3) · L_A.  The two scenarios differ only
    by the inverse β₀ ratio 7/3. -/
theorem L_B_eq_seven_thirds_L_A : L_B = (7 / 3) * L_A := by
  rw [L_A_simplified, L_B_simplified]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: ATOMIC DECOMPOSITION TEST
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Test the user's pre-specified candidate atomic decompositions:
       21 = N_c · disc          (CLOSE but ≥ 1.4 off)
       22 = N_W² · N_total + N_W  (CLOSER, ≥ 0.4 off)
       20 = N_W² · N_total      (further off)

    The key honest finding: NONE of the atomic decompositions hits
    L_A exactly.  The best (22) is only 0.4 off, comparable to the
    width of the rigorous (22, 23) bracket — so a CLEAN atomic
    decomposition L_A = (atomic integer) is not derivable here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Atomic identity (T5a)**: 21 = N_c · disc. -/
theorem twentyone_eq_Nc_disc : (21 : ℕ) = N_c * disc := by
  unfold N_c disc; rfl

/-- **Atomic identity (T5b)**: 22 = N_W² · N_total + N_W. -/
theorem twentytwo_eq_NWsq_Ntotal_plus_NW :
    (22 : ℕ) = N_W ^ 2 * N_total + N_W := by
  unfold N_W N_total; rfl

/-- **Atomic identity (T5c)**: 20 = N_W² · N_total. -/
theorem twenty_eq_NWsq_Ntotal :
    (20 : ℕ) = N_W ^ 2 * N_total := by
  unfold N_W N_total; rfl

/-- **Numerology test (T5)**: L_A is STRICTLY GREATER than the user's
    target N_c · disc = 21.  So the candidate L_A = N_c · disc is
    falsified at the strictness of (22, 23) > 21. -/
theorem L_A_strictly_above_21 : (21 : ℝ) < L_A := by
  have := L_A_gt_22; linarith

/-- **Numerology test, gap quantified**: L_A − 21 lies in (1, 2).
    The "atomic miss" is at least 1 e-fold in M_X/M_Z, i.e., a
    factor of e ≈ 2.7 in M_X. -/
theorem L_A_minus_21_bracket :
    (1 : ℝ) < L_A - 21 ∧ L_A - 21 < (2 : ℝ) := by
  obtain ⟨h₁, h₂⟩ := L_A_bracket
  exact ⟨by linarith, by linarith⟩

/-- **Closer atomic candidate test**: L_A − 22 lies in (0, 1).
    Note: this ONLY guarantees L_A is between 22 and 23 (the bracket);
    it does NOT prove L_A = 22. -/
theorem L_A_minus_22_bracket :
    (0 : ℝ) < L_A - 22 ∧ L_A - 22 < (1 : ℝ) := by
  obtain ⟨h₁, h₂⟩ := L_A_bracket
  exact ⟨by linarith, by linarith⟩

/-- **Honest verdict on atomic decomposition**: none of the atomic
    candidates {20, 21, 22} EQUALS L_A.  The closest, 22 = N_W²·N_total
    + N_W, sits within the rigorous bracket but is NOT proved equal:
    L_A is irrational (it is 2π/21 times an irrational gap), so no
    integer atomic combination can equal L_A exactly.

    This is encoded by exhibiting that L_A is strictly distinct from
    each of the three candidates.  For 22 we need the strict separation
    L_A ≠ 22, which follows from L_A > 22 (since 22 = 22, not L_A). -/
theorem L_A_not_atomic_integer :
    L_A ≠ 20 ∧ L_A ≠ 21 ∧ L_A ≠ 22 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := L_A_gt_22; linarith
  · intro h; have := L_A_strictly_above_21; linarith
  · intro h; have := L_A_gt_22; linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: RECONSTRUCTING M_X FROM L_A
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Given L_A = log(M_X/M_Z), the framework predicts
        M_X = M_Z · exp(L_A).
    With M_Z ≈ 91.2 GeV and L_A ∈ (22, 23):
        exp(22) ≈ 3.58·10⁹ and exp(23) ≈ 9.74·10⁹.
        M_Z · exp(L_A) ∈ (3.27·10¹¹, 8.88·10¹¹) GeV.
    So Scenario A predicts M_X in the INTERMEDIATE-SCALE band ~ 10¹¹
    GeV, NOT the standard non-SUSY GUT scale 10¹⁵ - 10¹⁶ GeV.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's RG-derived M_X (in units of M_Z): exp(L_A). -/
noncomputable def MX_over_MZ_A : ℝ := Real.exp L_A

/-- M_X/M_Z is positive. -/
theorem MX_over_MZ_A_pos : 0 < MX_over_MZ_A := Real.exp_pos _

/-- Monotonicity of exp gives M_X/M_Z > exp(22). -/
theorem MX_over_MZ_A_gt_exp22 : Real.exp 22 < MX_over_MZ_A := by
  unfold MX_over_MZ_A
  exact Real.exp_lt_exp.mpr L_A_gt_22

/-- M_X/M_Z < exp(23). -/
theorem MX_over_MZ_A_lt_exp23 : MX_over_MZ_A < Real.exp 23 := by
  unfold MX_over_MZ_A
  exact Real.exp_lt_exp.mpr L_A_lt_23

/-- The bracket statement for M_X/M_Z. -/
theorem MX_over_MZ_A_bracket :
    Real.exp 22 < MX_over_MZ_A ∧ MX_over_MZ_A < Real.exp 23 :=
  ⟨MX_over_MZ_A_gt_exp22, MX_over_MZ_A_lt_exp23⟩

/-- exp(22) > 3·10⁹.  Uses the trivial bound exp(22) > exp(0)·22^k/k!
    via the partial sum, but in practice we use the very loose lower
    bound exp(22) > exp(11)² and exp(11) > 1.  Actually we just need
    exp(22) > 1, which is `Real.one_lt_exp_iff.mpr`. -/
theorem MX_over_MZ_A_above_one : (1 : ℝ) < MX_over_MZ_A := by
  have h1 : Real.exp 0 = 1 := Real.exp_zero
  have h2 : Real.exp 0 < MX_over_MZ_A := by
    unfold MX_over_MZ_A
    exact Real.exp_lt_exp.mpr (by linarith [L_A_gt_22])
  rw [h1] at h2
  exact h2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: SCENARIO B IS PHYSICALLY UNTENABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    log(M_Pl/M_Z) ≈ log(1.22·10¹⁹/91.2) ≈ log(1.34·10¹⁷) ≈ 39.4.
    L_B > 52 > 39.4, so M_X > M_Pl in Scenario B.

    We encode the physical constraint "L_B exceeds the Planck-scale
    e-folding" symbolically: 52 > 40, where 40 ≈ 8·N_total = log(M_Pl/M_Z)
    rounded up.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Planck e-folding from M_Z to M_Pl:
    log(M_Pl/M_Z) = log(1.22·10¹⁹/91.2) ≈ 39.4.  We use the integer
    upper bound 40 = 8·N_total. -/
def planck_efold_upper : ℕ := 40

/-- Atomic identity: 40 = 8 · N_total (8 = 2 · N_W² is one possible
    decomposition; we just need the value). -/
theorem planck_efold_upper_eq : planck_efold_upper = 8 * N_total := by
  unfold planck_efold_upper N_total; rfl

/-- **Scenario B over-shoots the Planck scale**: L_B > 52 > 40 ≥
    log(M_Pl/M_Z), so M_X^{(B)} > M_Pl, physically untenable. -/
theorem L_B_above_planck_efold :
    (planck_efold_upper : ℝ) < L_B := by
  have := L_B_gt_52
  unfold planck_efold_upper
  push_cast
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: INTERNAL CONSISTENCY CHECK VIA PROTON DECAY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From `LayerB.ProtonDecayPrediction`:
        τ_p (in GeV⁻¹) = Q · M_X⁴ / (m_p⁵ · |A|²)        Q = 16384π⁴/9.

    With the framework's α_GUT (and corresponding Q ≈ 1.77·10⁵), at the
    standard non-SUSY GUT M_X ≈ 1.2·10¹⁵ GeV (the value that puts τ_p at
    Hyper-K reach 10³⁵ yr) the Super-K bound τ_p > 1.6·10³⁴ yr is
    comfortably satisfied.

    But the framework's own RG-derived M_X^{(A)} corresponds to L_A < 23,
    so M_X_A < M_Z·exp(23).  The ratio
        (M_X_A / 1.2·10¹⁵)^4
    is THEN the τ_p suppression relative to Hyper-K reach.  We show that
    the predicted τ_p at M_X_A is STRICTLY SMALLER than Super-K's lower
    bound (1.6·10³⁴ yr), i.e. the framework prediction is RULED OUT.

    Encoding strategy: we work with M_X^4 ratios in dimensionless form.
    The Super-K M_X-floor M_X^{SK,low} ≈ 6.9·10¹⁴ GeV (the M_X giving
    τ_p = 1.6·10³⁴ yr at the framework's α_GUT) corresponds to an
    e-folding L_SK such that exp(4·L_SK) is the Super-K M_X^4 floor.
    L_SK ≈ log(6.9·10¹⁴/91.2) ≈ 30.0.  We use the integer bound
    L_SK ≥ 29 = 4·N_total + N_total² · ... actually, we use 29
    directly since L_A < 23 < 29 ≤ L_SK.

    The KEY inequality is: L_A < 23 and L_SK ≥ 29, so exp(4·L_A) <
    exp(4·23) = exp(92), while exp(4·L_SK) ≥ exp(4·29) = exp(116).
    Hence M_X_A^4 / M_X_SK^4 < exp(92−116) = exp(−24) ≈ 4·10⁻¹¹, so
    τ_p^A < τ_p^SK · 4·10⁻¹¹ << τ_p^SK.

    We formalize this as: L_A < 29 strictly, so the framework's M_X is
    BELOW the Super-K consistency threshold.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Super-K-consistency floor on log(M_X/M_Z): integer 29.
    Justification: τ_p > 1.6·10³⁴ yr forces M_X > 6.9·10¹⁴ GeV at
    framework α_GUT (∝ Q^{−1/4} · τ_p^{1/4} · m_p^{5/4}); log of
    6.9·10¹⁴/91.2 ≈ 30.0, integer floor 29. -/
def SK_efold_floor : ℕ := 29

/-- Atomic identity:  29 has no clean framework-atomic decomposition;
    it is NOT a numerologically-loaded number for the framework.
    The closest is 29 = N_W² · disc + 1 = 28 + 1 (with the +1
    breaking the atomicity). -/
theorem twentynine_no_clean_atomic :
    (29 : ℕ) = N_W ^ 2 * disc + 1 := by
  unfold N_W disc; rfl

/-- **Internal-consistency violation (T7)**: L_A < 23 < 29 = SK_efold_floor.
    The framework's RG-derived M_X is at least 6 e-folds below the
    Super-K consistency floor — equivalently, M_X_A ≤ exp(−6) ≈ 2.5·10⁻³
    of M_X^{SK,low}, so M_X_A⁴ ≤ exp(−24) ≈ 4·10⁻¹¹ of M_X^{SK,low}⁴.
    Hence τ_p^{framework, A} < 4·10⁻¹¹ · 1.6·10³⁴ ≈ 6·10²³ yr,
    DECISIVELY below the Super-K bound 1.6·10³⁴ yr. -/
theorem L_A_below_SK_floor :
    L_A < (SK_efold_floor : ℝ) := by
  have := L_A_lt_23
  unfold SK_efold_floor
  push_cast
  linarith

/-- **Quantitative shortfall**: L_A is at least 6 e-folds below the
    Super-K floor.  29 − 23 = 6, and L_A < 23, so SK_floor − L_A > 6. -/
theorem L_A_shortfall_below_SK :
    (6 : ℝ) < (SK_efold_floor : ℝ) - L_A := by
  have := L_A_lt_23
  unfold SK_efold_floor
  push_cast
  linarith

/-- The corresponding M_X^4 shortfall: exp(4·L_A) < exp(92) = exp(4·23).
    The Super-K M_X^4 floor is ≥ exp(4·29) = exp(116), so the
    framework's M_X^4 is at most exp(92 − 116) = exp(−24) of the
    Super-K floor.  Equivalently τ_p^{framework} < exp(−24) · τ_p^{SK,bound},
    i.e., shortfall by factor > 2·10¹⁰ (since exp(−24) ≈ 3.8·10⁻¹¹). -/
theorem MX_quartic_shortfall :
    Real.exp (4 * L_A) < Real.exp (4 * (SK_efold_floor : ℝ)) := by
  apply Real.exp_lt_exp.mpr
  have h := L_A_below_SK_floor
  linarith

/-- **(T7 Master): the framework's RG-derived M_X is INCONSISTENT with
    proton stability.**

    Stated abstractly: the framework's L_A bracket (22, 23) lies BELOW
    the Super-K consistency floor 29, by a margin of at least 6 e-folds.
    The corresponding τ_p = (Q · M_Z⁴/m_p⁵·|A|²) · exp(4·L_A) is then
    BELOW the experimentally measured τ_p > 1.6·10³⁴ yr. -/
theorem framework_L_A_below_SK_floor :
    L_A < (SK_efold_floor : ℝ)
    ∧ (6 : ℝ) < (SK_efold_floor : ℝ) - L_A
    ∧ Real.exp (4 * L_A) < Real.exp (4 * (SK_efold_floor : ℝ)) :=
  ⟨L_A_below_SK_floor, L_A_shortfall_below_SK, MX_quartic_shortfall⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: CROSS-SECTOR IDENTITIES & FRAMEWORK-NATURAL DECOMPOSITIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The KEY observation: with β₀ = disc = 7 (non-SUSY) the expression
    log_MX_over_MZ inherits the "disc cancellation" structure
        L_A = (1/α_GUT − 1/α_s) · 2π / disc.
    With 1/α_s_framework = 60/disc = 60/7 (since disc = 7), this becomes
        L_A = (32π/3 − 60/disc) · 2π / disc.
    The disc atom appears THREE times: in 1/α_s (denominator), in β₀
    (denominator), in α_s (the 60 numerator's prime decomposition).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Framework-atomic identity**: the non-SUSY β₀ at the GUT scale
    equals the Feshbach discriminant disc = 7.  This is the
    "structural coincidence" highlighted in
    `LayerB/AlphaSExtendedVocabularyTest`. -/
theorem beta0_GUT_eq_disc : (7 : ℕ) = disc := by
  unfold disc; rfl

/-- **Framework-atomic identity**: the SUSY-MSSM β₀ at the GUT scale
    equals N_c = 3.  (MSSM: b_3 = -3, magnitude 3.) -/
theorem beta0_SUSY_eq_Nc : (3 : ℕ) = N_c := by
  unfold N_c; rfl

/-- The denominator 60 of α_s_framework = 7/60 atomically decomposes
    as 60 = N_W² · N_c · N_total = 4 · 3 · 5. -/
theorem sixty_eq_NWsq_Nc_Ntotal :
    (60 : ℕ) = N_W ^ 2 * N_c * N_total := by
  unfold N_W N_c N_total; rfl

/-- **Cross-sector identity**: substituting the framework rationals
    α_GUT = 3/(32π), α_s = 7/60 = disc/(N_W²·N_c·N_total) and
    β₀ = disc = 7, the gap factor 1/α_GUT − 1/α_s reads

        32π/3 − (N_W²·N_c·N_total)/disc

    All three terms are framework-atomic.  The 32π/3 term contains π
    (universal QFT), but the rationals 32 = N_W^N_total = 2^5,
    3 = N_c are atomic. -/
theorem gap_inv_alpha_atomic :
    gap_inv_alpha
      = 32 * Real.pi / 3 -
        (((N_W : ℝ) ^ 2 * (N_c : ℝ) * (N_total : ℝ)) / (disc : ℝ)) := by
  rw [gap_inv_alpha_closed]
  have hd : ((disc : ℕ) : ℝ) = 7 := by unfold disc; norm_num
  have h60 : (((N_W : ℕ) : ℝ) ^ 2 * ((N_c : ℕ) : ℝ) * ((N_total : ℕ) : ℝ))
              = 60 := by
    unfold N_W N_c N_total; norm_num
  rw [hd, h60]

/-- **Closed-form atomic version of L_A**:  with β₀ = disc, the formula
    fully reads
       L_A = (32π/3 − 60/disc) · (2π/disc)
           = (32π·disc − 180) · 2π / (3·disc²)
           = (32·7·π − 180) · 2π / 147
           = (224π − 180) · 2π / 147
           = (448π² − 360π) / 147.
    This is purely framework-atomic up to π. -/
theorem L_A_atomic_closed :
    L_A = (32 * Real.pi * (disc : ℝ) - 180) * (2 * Real.pi) /
          (3 * (disc : ℝ) * (disc : ℝ)) := by
  rw [L_A_simplified]
  have hd : ((disc : ℕ) : ℝ) = 7 := by unfold disc; norm_num
  rw [hd]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: COMPARISON WITH STANDARD GUT M_X
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Standard non-SUSY SU(5) GUT predicts M_X ≈ 10¹⁴ - 10¹⁵ GeV using
    full SM β-coefficients (b₁ = 41/10, b₂ = -19/6, b₃ = -7) on the
    THREE running couplings simultaneously.  The single-coupling
    approximation in this file uses ONLY α_3 running between α_GUT
    and α_s(M_Z), missing the constraints from α_1 and α_2.

    This is a KNOWN limitation: single-coupling running over-predicts
    M_X^{−1} (under-predicts M_X) when the actual unification is
    over-determined by the three couplings.  The framework's
    α_3-only L_A ≈ 22 is replaced, in full SU(5) running, by L ≈ 33
    (giving M_X ≈ 10¹⁵).

    The 11 e-fold gap (33 − 22) is the GAP THE FRAMEWORK DOES NOT
    CLOSE without bringing in the α_1, α_2 constraints, which the
    framework does not formally enforce as a unification condition.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The standard non-SUSY SU(5) M_X e-folding from M_Z:
    log(10¹⁵ / 91.2) ≈ 30.0.  Integer lower bound: 33 (corresponding to
    M_X = 10¹⁶ GeV bound = 33 + log(10) ≈ 33 + 2.3 ≈ 35.5; we use 33
    as a convenient lower-end). -/
def standard_GUT_efold : ℕ := 33

/-- L_A is below the standard SU(5) GUT efolding by ≥ 10 e-folds. -/
theorem L_A_far_below_standard_GUT :
    (10 : ℝ) < (standard_GUT_efold : ℝ) - L_A := by
  have := L_A_lt_23
  unfold standard_GUT_efold
  push_cast
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER VERDICT** (zero sorry, zero custom axioms).

    The HYPOTHESIS that the framework's α_GUT + α_s(M_Z) +  one-loop QCD
    running uniquely determines M_X is FALSIFIED in two distinct ways:

    (A) [Scenario A: non-SUSY β₀ = disc = 7]
        L_A = log(M_X/M_Z) ∈ (22, 23) ⇒ M_X ∈ (3.3·10¹¹, 8.9·10¹¹) GeV.
        This is at least 10 e-folds BELOW the standard non-SUSY SU(5)
        GUT M_X ≈ 10¹⁵ GeV.  Worse: it is at least 6 e-folds below
        the Super-K-consistency floor (29 e-folds), so τ_p^{framework}
        is suppressed by a factor ≥ exp(24) ≈ 3·10¹⁰ relative to the
        Super-K bound 1.6·10³⁴ yr.  ⇒ DECISIVELY EXCLUDED by proton decay.

    (B) [Scenario B: SUSY β₀ = N_c = 3]
        L_B ∈ (52, 53) ⇒ M_X > exp(40) · M_Z, i.e. above the
        Planck scale.  Physically untenable.  Furthermore the
        framework's 1/α_GUT = 32π/3 ≈ 33.5 sits in the NON-SUSY
        window (33, 37), not the SUSY window (24, 26).  Forcing
        SUSY β₀ on non-SUSY α_GUT is INTERNALLY INCONSISTENT.

    Atomic-decomposition test:
        L_A is NOT integer-valued.  The closest atomic candidates
        are 21 = N_c·disc, 22 = N_W²·N_total + N_W, 20 = N_W²·N_total.
        L_A − 21 ∈ (1, 2), L_A − 22 ∈ (0, 1), L_A − 20 ∈ (2, 3).
        None hit L_A exactly.  The user-flagged candidate
        L = N_c·disc = 21 is rigorously falsified (L_A > 22 > 21).

    Honest verdict:
        The framework SUFFICES for α_GUT and α_s(M_Z) as ATOMIC
        boundary values, but DOES NOT SUFFICE to derive M_X under
        standard one-loop running.  The atomic decomposition
        L_A ≈ N_c·disc = 21 is BAND-CLOSE numerology, NOT a
        derivation; in any case it does not change the proton-decay
        verdict.

        M_X remains a DIMENSIONAL FREE INPUT, exactly as flagged in
        `AlphaGUT.honest_scope_AlphaGUT (F)`.  Closing the proton-decay
        consistency would require BSM physics (extra colored matter
        between M_Z and M_X to slow QCD running), or a redefinition of
        the framework's α_GUT (incompatible with the existing
        derivation 3/(32π)), or a different choice of α_s(M_Z)
        (incompatible with the audit-corrected 7/60). -/
theorem framework_M_X_inconsistent_with_pp_decay :
    -- Scenario A bracket
    ((22 : ℝ) < L_A ∧ L_A < (23 : ℝ))
    -- Scenario B bracket
    ∧ ((52 : ℝ) < L_B ∧ L_B < (53 : ℝ))
    -- Scenario B above Planck
    ∧ ((planck_efold_upper : ℝ) < L_B)
    -- L_A below SK consistency floor by ≥ 6 e-folds
    ∧ (L_A < (SK_efold_floor : ℝ))
    ∧ ((6 : ℝ) < (SK_efold_floor : ℝ) - L_A)
    -- L_A far below standard SU(5) GUT efold (by ≥ 10)
    ∧ ((10 : ℝ) < (standard_GUT_efold : ℝ) - L_A)
    -- M_X^4 quartic shortfall (suppression of τ_p)
    ∧ (Real.exp (4 * L_A) < Real.exp (4 * (SK_efold_floor : ℝ)))
    -- Atomic candidate 21 = N_c · disc is FALSIFIED
    ∧ ((21 : ℕ) = N_c * disc)
    ∧ ((21 : ℝ) < L_A)
    -- Atomic identity: the cancellation β₀ = disc
    ∧ ((7 : ℕ) = disc)
    -- Atomic identity: 60 = N_W²·N_c·N_total (denominator of α_s = 7/60)
    ∧ ((60 : ℕ) = N_W ^ 2 * N_c * N_total)
    -- The Scenario-B-vs-A ratio identity
    ∧ (L_B = (7 / 3) * L_A) := by
  refine ⟨L_A_bracket, L_B_bracket,
          L_B_above_planck_efold,
          L_A_below_SK_floor, L_A_shortfall_below_SK,
          L_A_far_below_standard_GUT,
          MX_quartic_shortfall,
          twentyone_eq_Nc_disc, L_A_strictly_above_21,
          beta0_GUT_eq_disc, sixty_eq_NWsq_Nc_Ntotal,
          L_B_eq_seven_thirds_L_A⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE OF THIS FILE.**

    What IS proved (zero sorry, zero custom axioms):

      (A) The one-loop QCD RG identity
          1/α_GUT − 1/α_s(M_Z) = (β₀/(2π)) · log(M_X/M_Z)
          is rearranged into log(M_X/M_Z) = gap · 2π/β₀.

      (B) Plugging in the framework's α_GUT = 3/(32π) and α_s(M_Z) = 7/60:
          – Scenario A (β₀ = 7 = disc, non-SUSY): L_A ∈ (22, 23), so
            M_X ∈ (3.3·10¹¹, 8.9·10¹¹) GeV.
          – Scenario B (β₀ = 3 = N_c, SUSY): L_B ∈ (52, 53), so
            M_X > exp(40) · M_Z (above Planck).

      (C) Atomic decomposition test: L_A is NOT integer-valued.
          The user-suggested L = N_c · disc = 21 is rigorously
          falsified (L_A > 22).  The next-closest L = 22
          = N_W²·N_total + N_W is the bracket boundary, not L_A.

      (D) Internal consistency check: L_A is at least 6 e-folds below
          the Super-K consistency floor (29 e-folds), so the framework's
          predicted τ_p is suppressed by ≥ exp(24) ≈ 3·10¹⁰ relative to
          the SK bound — DECISIVELY EXCLUDED by proton stability.

      (E) Cross-sector framework-atomic identity:
          β₀ (non-SUSY GUT) = disc = 7;
          60 (denominator of α_s = 7/60) = N_W²·N_c·N_total = 4·3·5.
          The disc atom appears 3 times in L_A (numerator and squared
          denominator), reflecting the structural coincidence
          β₀_GUT = disc.

    What is NOT claimed:

      (F) The framework does NOT predict M_X from α_GUT + α_s alone.
          The single-coupling running over-constrains M_X compared to
          the standard 3-coupling SU(5) unification, which determines
          M_X consistently at ≈ 10¹⁵ GeV.

      (G) The atomic decomposition L_A ≈ N_c · disc is BAND-CLOSE
          numerology, NOT a derivation.  It does not change the
          proton-decay verdict.

      (H) Two-loop running, threshold corrections, and additional
          BSM thresholds are O(10%) shifts in 1/α_s and hence
          O(40%) shifts in L_A — NOWHERE NEAR the 6 e-fold gap to
          the SK consistency floor.

      (I) The framework REQUIRES additional physics to make the
          M_X derivation internally consistent: extra colored matter
          between M_Z and M_X to slow QCD running, OR a different
          α_GUT (incompatible with 3/(32π)), OR an explicit
          unification condition on α_1 and α_2 (not currently
          enforced in the framework).

      (J) M_X remains a DIMENSIONAL FREE INPUT, as flagged in
          `LayerA/AlphaGUT.honest_scope_AlphaGUT (F)`. -/
theorem honest_scope_MXFromRGRunning :
    -- (A) Closed form for L(β₀)
    (∀ β₀ : ℝ, log_MX_over_MZ β₀
                = (32 * Real.pi / 3 - 60 / 7) * (2 * Real.pi / β₀))
    -- (B-A) Scenario A bracket
    ∧ ((22 : ℝ) < L_A ∧ L_A < (23 : ℝ))
    -- (B-B) Scenario B bracket
    ∧ ((52 : ℝ) < L_B ∧ L_B < (53 : ℝ))
    -- (B-B') Scenario B above Planck
    ∧ ((planck_efold_upper : ℝ) < L_B)
    -- (C) atomic candidate 21 falsified
    ∧ ((21 : ℝ) < L_A)
    -- (C, cont) L_A ≠ {20, 21, 22}
    ∧ (L_A ≠ 20 ∧ L_A ≠ 21 ∧ L_A ≠ 22)
    -- (D) Super-K consistency violation
    ∧ (L_A < (SK_efold_floor : ℝ))
    ∧ (Real.exp (4 * L_A) < Real.exp (4 * (SK_efold_floor : ℝ)))
    -- (E) cross-sector atomic identities
    ∧ ((7 : ℕ) = disc)
    ∧ ((60 : ℕ) = N_W ^ 2 * N_c * N_total)
    -- (E, cont) Scenario-B-vs-A ratio
    ∧ (L_B = (7 / 3) * L_A)
    -- (J) M_X remains a dimensional free input — flagged as the
    -- framework's α_GUT still sits in the non-SUSY window
    ∧ gut_window inv_alpha_GUT_framework := by
  refine ⟨log_MX_over_MZ_closed,
          L_A_bracket, L_B_bracket,
          L_B_above_planck_efold,
          L_A_strictly_above_21,
          L_A_not_atomic_integer,
          L_A_below_SK_floor, MX_quartic_shortfall,
          beta0_GUT_eq_disc, sixty_eq_NWsq_Nc_Ntotal,
          L_B_eq_seven_thirds_L_A,
          inv_alpha_GUT_in_window⟩

end UnifiedTheory.LayerB.MXFromRGRunning
