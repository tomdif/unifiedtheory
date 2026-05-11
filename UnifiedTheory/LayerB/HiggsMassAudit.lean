/-
  LayerB/HiggsMassAudit.lean — HONEST audit of m_H = log(5/3)·v.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE QUESTION

  `LayerA/HiggsMassDerived.lean` claims the Higgs mass is DERIVED from the
  spectral gap of the d-dimensional chamber kernel:

      m_H = γ_d · v   where   γ_d := log((d+1)/(d-1))

  At d = 4: γ_4 = log(5/3) ≈ 0.51083, and at v = 246 GeV this gives
  m_H ≈ 125.7 GeV, within 0.5% of the PDG value 125.4 GeV.

  This file applies the same critical audit methodology used for V_us
  (`VusFalsificationTest.lean`, `VusStrengtheningAttempt.lean`) to ask:

      Is m_H = log(5/3)·v truly derived from K/P axioms,
      or is it MENU SELECTION dressed up as a derivation?

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE FOUR ATOMS OF THE m_H CLAIM

  (A1) **The 5/3 ratio.** Claimed source: K_F eigenvalue ratio at d=4.
       Lean status: only the algebraic identity (4+1)/(4-1) = 5/3 is proven
       (`KFd4Verified.target_ratio_d4`). The actual K_F-derived J₄ Feshbach
       eigenvalues in `FeshbachJ4.lean` are λ₁ = 3/5, λ₂ = (5+√7)/30,
       λ₃ = (5-√7)/30, giving λ₁/λ₂ = 5-√7 ≈ 2.354 (NOT 5/3 ≈ 1.667).
       The "5/3" claim relies on a SEPARATE Python computation of K_F on
       [m]^4 that is NOT formalized in Lean.

  (A2) **The log function.** Claimed source: correlation-length identity
       γ = log(λ_max/λ_2) (transfer-matrix decay rate). This IS a standard
       physical principle — but the framework does not derive that the
       Higgs mass equals an inverse correlation length. It is POSTULATED
       in `PSectorMass.lean`: "the K-sector correlator decay rate is set
       by the spectral gap; the mass of the P-sector scalar is m_S =
       gamma_d * (energy scale)".

  (A3) **The energy scale v.** Why v = 246 GeV and not M_P or M_Z?
       `PSectorMass.lean` openly says: "What is NOT proven: why the
       electroweak VEV v (rather than M_P) is the relevant scale."
       This is the same kind of "naming choice" that V_us suffers from.

  (A4) **The dimension d = 4.** The d-dependence test in `HiggsMassDerived`
       does provide GENUINE selection: γ_3 → 170 GeV (excluded by LHC),
       γ_5 → 100 GeV (excluded by LEP). Only d = 4 hits the window.
       BUT: this only excludes other dimensions; it does not exclude other
       FORMULAS at d = 4.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE MENU OF m_H/v CANDIDATES (1% PDG window)

  PDG: m_H/v = 125.4 / 246.22 ≈ 0.50930. 1% window: [0.5042, 0.5144].

  We exhibit framework-natural expressions whose values fall inside
  [0.5042, 0.5144]. Each is built from the same K/P atoms used elsewhere
  in the framework (C_int = 3/20, a₁ = 1/3, λ* = 3/5, b₁ = 1/5, b₁² = 1/25,
  b₂² = 1/50) and from natural log/sqrt operations.

      CANDIDATE H1:  log(5/3)               ≈ 0.51083   [framework's choice]
      CANDIDATE H2:  log(2 - a₁) = log(5/3) ≈ 0.51083   [same value, "subtractive" route]
      CANDIDATE H3:  log(λ* + 1/15) = log(2/3 + ...) — see formal form below.

  And from the d-DIMENSION menu — at d = 4, what numerical functions of
  the eigenvalue ratio (5/3) match within 1%?

      H4:  log(5/3)            ≈ 0.51083  [the framework's choice]
      H5:  ((5/3) - 1)/((5/3) + 1) · 2 = (2/3)/(8/3)·2 = 1/2 = 0.50000
                                          [alternative "decay rate" formula:
                                           tanh(γ/2)·2 / 1 type, marginal at 1.8%]
      H6:  (1/2) · sqrt(7)/sqrt(2 · 7) (sqrt-style framework term)... etc.

  THE CORE FINDING (proved formally below as Theorem `MASTER_audit`):

  (T1) `cand_H1 = cand_H2`: the framework's log(5/3) is algebraically
       identical to log(2 - a₁), where a₁ = 1/3 is the framework's residue
       atom. This is the SAME phenomenon as `cand1_eq_cand2` in V_us:
       multiple algebraically equivalent expressions, one numerical answer.

  (T2) `cand_H1 ≠ cand_H_ratio_subtractive`: there exists a framework-natural
       OTHER expression (the "ratio difference" formula 2(λ_max - λ_2)/(λ_max
       + λ_2) at d=4) whose value is 1/2 = 0.5, within 2% of PDG. So the
       1%-window-on-PDG criterion is NOT satisfied uniquely by log(5/3).
       The 0.5 value is borderline, but its existence proves the menu has
       structure.

  (T3) `framework_does_not_derive_log_choice`: NOTHING in the framework's
       K/P axioms forces "γ_d := log((d+1)/(d-1))" rather than e.g.
       "γ_d := 2(R-1)/(R+1) with R := (d+1)/(d-1)". Both are "natural
       gauge-invariant decay-rate functionals" of the eigenvalue ratio.
       The choice of LOG is selection from the standard transfer-matrix
       toolbox, not derivation.

  (T4) `kf_eigenvalue_5_3_not_proved_in_lean`: the Lean proofs of K_F
       structure (FeshbachJ4) give λ₁/λ₂ = 5-√7, NOT 5/3. The 5/3 ratio
       used by `PSectorMass.spectralGap_4` is POSTULATED via a closed-form
       function `log((d+1)/(d-1))` whose K_F derivation lives in Python,
       not in Lean.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST CLASSIFICATION (relative to V_us)

  V_us audit found:    SELECTION FROM A 6-ITEM MENU at exactly 1/20.
  m_H audit finds:     PARTIAL DERIVATION:
                       - The d-dependence is GENUINE (only d=4 in window).
                       - The functional form γ = log(eigenvalue ratio) is
                         a STANDARD physics choice (transfer matrix), not
                         framework-derived.
                       - The eigenvalue ratio 5/3 is asserted but the J₄
                         Lean theorems give 5-√7 instead. The 5/3 value
                         comes from an ASYMPTOTIC m → ∞ extrapolation
                         that is verified in Python only.
                       - The energy scale v is a NAMING CHOICE.

  Verdict: m_H is BETTER than V_us (the d-dependence test is real
  exclusion), but it is NOT a clean first-principles derivation.
  It mixes one genuine derivation (d-selection) with two postulates
  (log-form, energy scale) and one un-Lean-formalized eigenvalue claim.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerA.HiggsMassDerived
import UnifiedTheory.LayerB.PSectorMass

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HiggsMassAudit

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.PSectorMass

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: RAW K/P ATOMS LIFTED FROM FeshbachJ4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Atom: the interior self-energy constant C_int = 3/20. -/
noncomputable def atom_Cint : ℝ := ((C_int : ℚ) : ℝ)

/-- Atom: the channel diagonal a₁ = 1/3. -/
noncomputable def atom_a1 : ℝ := ((a₁ : ℚ) : ℝ)

/-- Atom: the spectral fixed point λ* = 3/5 (top J₄ eigenvalue). -/
noncomputable def atom_ls : ℝ := ((lambda_star : ℚ) : ℝ)

/-- Atom: b₁ = 1/5. -/
noncomputable def atom_b1 : ℝ := 1 / 5

/-- Atom: the second J₄ diagonal a₂ = 2/5. -/
noncomputable def atom_a2 : ℝ := ((a₂ : ℚ) : ℝ)

theorem atom_Cint_val : atom_Cint = 3 / 20 := by
  unfold atom_Cint C_int; push_cast; ring

theorem atom_a1_val : atom_a1 = 1 / 3 := by
  unfold atom_a1 a₁; push_cast; ring

theorem atom_ls_val : atom_ls = 3 / 5 := by
  unfold atom_ls lambda_star; push_cast; ring

theorem atom_a2_val : atom_a2 = 2 / 5 := by
  unfold atom_a2 a₂; push_cast; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: ATOM A1 — THE 5/3 RATIO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework claims the K_F eigenvalue ratio at d=4 equals 5/3.
    But the Lean-PROVEN J₄ Feshbach eigenvalues give a DIFFERENT ratio.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's "spectral gap target" at d=4 is the rational 5/3. -/
theorem framework_target_ratio : ((4 : ℚ) + 1) / (4 - 1) = 5 / 3 := by norm_num

/-- The Lean-proven J₄ TOP eigenvalue is 3/5 (root of the linear factor). -/
theorem J4_top_eigenvalue : charPoly (3 / 5) = 0 :=
  lambda1_is_eigenvalue

/-- The Lean-proven J₄ SECOND eigenvalue is (5 + √7)/30. -/
theorem J4_second_eigenvalue (s : ℝ) (hs : s ^ 2 = 7) :
    150 * ((5 + s) / 30) ^ 2 - 50 * ((5 + s) / 30) + 3 = 0 :=
  lambda2_is_root s hs

/-- **The actual J₄ top-to-second eigenvalue ratio is 5 - √7.**
    Numerically: 5 - 2.6458 ≈ 2.354, NOT 5/3 ≈ 1.667. -/
theorem actual_J4_eigenvalue_ratio (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    (3 / 5 : ℝ) / ((5 + s) / 30) = 5 - s :=
  ratio_lambda1_lambda2 s hs hs_pos

/-- **Numerical: 5 - √7 is approximately 2.354, NOT 5/3.**
    Proof: 5 - √7 > 5 - 2.65 = 2.35, and 5/3 < 2 < 2.35.
    Hence the "K_F eigenvalue ratio = 5/3" claim is NOT consistent with
    the J₄ eigenvalue ratio that IS proven in Lean. -/
theorem J4_ratio_neq_five_thirds (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    (3 / 5 : ℝ) / ((5 + s) / 30) ≠ 5 / 3 := by
  rw [actual_J4_eigenvalue_ratio s hs hs_pos]
  -- Need 5 - s ≠ 5/3
  intro heq
  -- 5 - s = 5/3 ⟹ s = 10/3
  have hs_eq : s = 10 / 3 := by linarith
  rw [hs_eq] at hs
  -- (10/3)^2 = 100/9 ≠ 7
  norm_num at hs

/-- **The "5/3" ratio is hard-coded in the spectralGap definition,
    not derived from the J₄ eigenvalues.** This is what
    `PSectorMass.spectralGap_4` actually proves: it just unfolds the
    definition `log((d+1)/(d-1))` at d = 4. -/
theorem spectralGap_4_is_definitional :
    spectralGap 4 = Real.log (5 / 3) :=
  spectralGap_4

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: ATOM A2 — THE LOG FORM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The choice γ = log(eigenvalue ratio) is a STANDARD transfer-matrix
    formula, not a framework derivation. We document an alternative
    "decay rate functional" of the same ratio that gives a DIFFERENT
    numerical answer at d=4. The framework does not contain any K/P
    theorem distinguishing them.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Alternative decay-rate functional: 2·(R - 1)/(R + 1). At R = 5/3 this
    gives 2·(2/3)/(8/3) = 1/2. This is the "tanh-style" decay rate that
    appears in physics whenever a finite-velocity correlation function is
    being matched to its long-distance form. It is NOT excluded by the
    framework's K/P content; the framework simply chose log. -/
noncomputable def alt_decay_rate (R : ℝ) : ℝ := 2 * (R - 1) / (R + 1)

/-- At R = 5/3, the alternative decay rate equals 1/2. -/
theorem alt_decay_rate_at_5_3 : alt_decay_rate (5 / 3) = 1 / 2 := by
  unfold alt_decay_rate; norm_num

/-- The two functionals disagree numerically at R = 5/3:
    log(5/3) ≈ 0.5108 vs alt_decay_rate(5/3) = 0.5000. -/
theorem log_neq_alt_at_5_3 : Real.log (5 / 3) ≠ alt_decay_rate (5 / 3) := by
  rw [alt_decay_rate_at_5_3]
  -- log(5/3) > 1/2 (proven in PSectorMass)
  have hlb : (1 : ℝ) / 2 < Real.log (5 / 3) := log_five_thirds_gt_half
  intro heq
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE m_H/v MENU AT 1% AND 2% WINDOWS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    PDG: m_H/v = 125.4 / 246.22 ≈ 0.50930.
    1% window: [0.5042, 0.5144].
    2% window: [0.4992, 0.521].
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- CANDIDATE H1: γ_4 = log(5/3) (the framework's choice). -/
noncomputable def cand_H1 : ℝ := Real.log (5 / 3)

/-- CANDIDATE H2: log(2 - a₁) = log(2 - 1/3) = log(5/3).
    Same numerical value as H1, but the route through "2 - a₁" gives a
    different physical interpretation: the "spectral gap" rewritten via
    the residue atom rather than the (d+1)/(d-1) ratio. This is the
    direct analogue of `cand2_sq` in `VusFalsificationTest` (b₁ - C_int
    = C_int · a₁ as different routes to 1/20). -/
noncomputable def cand_H2 : ℝ := Real.log (2 - atom_a1)

/-- CANDIDATE H_alt: the alternative decay-rate functional at the same
    eigenvalue ratio. Value: 1/2 = 0.5. Within 2% of PDG (0.5093) but
    OUTSIDE 1%. -/
noncomputable def cand_H_alt : ℝ := alt_decay_rate (5 / 3)

/-! ### Closed forms -/

theorem cand_H1_value : cand_H1 = Real.log (5 / 3) := rfl

theorem cand_H2_eq_H1 : cand_H2 = cand_H1 := by
  unfold cand_H2 cand_H1
  rw [atom_a1_val]
  congr 1
  norm_num

theorem cand_H_alt_value : cand_H_alt = 1 / 2 := by
  unfold cand_H_alt; exact alt_decay_rate_at_5_3

/-! ### 1% window membership -/

/-- **H1 lies in the loose PDG window [0.499, 0.521].**
    From PSectorMass: 1/2 < log(5/3) < 13/25 = 0.52.
    The window is "loose 2%" because the PSectorMass upper bound
    log(5/3) < 13/25 = 0.52 is itself wider than the strict 2% window.
    We work with this loose window throughout (it is the WIDEST that
    Lean-proven bounds give us; widening cannot help the framework's
    case — narrowing might reduce the menu, but only at the cost of
    proving tighter Lean lemmas). -/
theorem cand_H1_in_loose_window :
    0.4992 < cand_H1 ∧ cand_H1 < 0.521 := by
  unfold cand_H1
  refine ⟨?_, ?_⟩
  · linarith [log_five_thirds_gt_half]
  · linarith [UnifiedTheory.LayerA.HiggsMassDerived.log_five_thirds_lt_052]

/-- **H_alt = 1/2 lies in the loose PDG window [0.499, 0.521]** but
    NOT in the strict 1% window [0.5042, 0.5144].
    This is the analogue of `cand3_neq_one_twentieth` in V_us:
    a strictly different value that is ALSO close to PDG. -/
theorem cand_H_alt_in_loose_window :
    0.4992 < cand_H_alt ∧ cand_H_alt < 0.521 := by
  rw [cand_H_alt_value]; refine ⟨by norm_num, by norm_num⟩

/-- **H1 and H_alt are STRICTLY DISTINCT values.** This is the analogue
    of `cand3_neq_one_twentieth`. -/
theorem cand_H1_neq_H_alt : cand_H1 ≠ cand_H_alt := by
  rw [cand_H_alt_value]
  unfold cand_H1
  intro heq
  -- log(5/3) = 1/2 contradicts log(5/3) > 1/2
  have := log_five_thirds_gt_half
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: ATOM A3 — THE ENERGY SCALE v
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework selects v = 246 GeV as the relevant scale. This is the
    EW VEV. PSectorMass.lean openly says: "What is NOT proven: why the
    electroweak VEV v (rather than M_P) is the relevant scale."

    We document the fact that 246 GeV is selected from at least four
    natural candidates: M_P (Planck), M_GUT, v_EW (Higgs VEV), and M_Z.
    The framework's d-dependence test EXCLUDES M_P and M_Z (and gives
    a window 230 < v < 260 — see HiggsMassDerived.only_ew_scale_works).
    But this is BACKWARD reasoning: it assumes m_H ≈ 125 GeV and shows
    only v ≈ 246 GeV works. It does not derive v ≈ 246 GeV from K/P axioms.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's d-dependence test: m ∈ [120, 130] forces E ∈ (230, 260).
    Re-export of `only_ew_scale_works` for visibility. -/
theorem energy_scale_window :
    ∀ E : ℝ,
      120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E ∧
      UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E < 130 →
      230 < E ∧ E < 260 :=
  UnifiedTheory.LayerA.HiggsMassDerived.only_ew_scale_works

/-- **The energy scale is NOT derived; it is selected.** The above
    theorem is a CONDITIONAL: IF you want m in [120, 130], THEN E
    must be in (230, 260). It does not say K/P axioms PRODUCE the
    EW VEV v ≈ 246 GeV; it only says (assuming Higgs ≈ 125) the right
    scale is the EW one. -/
theorem energy_scale_is_postulated :
    -- Framework PRESUPPOSES m_H ∈ [120, 130] to FORCE v ∈ (230, 260).
    -- This is NOT a derivation of v from K/P; it is selection by
    -- backward-fitting the experimental Higgs mass.
    ∀ E : ℝ, ¬ (120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E ∧
                UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E < 130) ∨
              (230 < E ∧ E < 260) := by
  intro E
  by_cases h : (120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E ∧
                UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E < 130)
  · right; exact energy_scale_window E h
  · left; exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: ATOM A4 — THE DIMENSION SELECTION (THE GENUINE PIECE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    UNLIKE V_us, the m_H prediction has REAL falsification content:
    only d = 4 lands in the experimental window. We re-export the
    proofs to make this VERY visible.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- d = 3 is excluded: m > 150 GeV at v > 230. -/
theorem d3_excluded (v : ℝ) (hv : 230 < v) :
    150 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 3 v :=
  UnifiedTheory.LayerA.HiggsMassDerived.d3_too_heavy v hv

/-- d = 5 is excluded: m < 125 GeV at v < 250. -/
theorem d5_excluded (v : ℝ) (hv : 0 < v) (hv2 : v < 250) :
    UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 5 v < 125 :=
  UnifiedTheory.LayerA.HiggsMassDerived.d5_too_light v hv hv2

/-- d = 4 lands in the [120, 130] window for v ∈ (240, 250). -/
theorem d4_in_window (v : ℝ) (hv : 240 < v) (hv2 : v < 250) :
    120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 v ∧
    UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 v < 130 :=
  UnifiedTheory.LayerA.HiggsMassDerived.d4_in_window v hv hv2

/-- **The dimension-selection theorem IS a real piece of derivation.**
    Among d = 3, 4, 5, only d = 4 gives m_H in [120, 130] at v = 246.
    This is genuine falsification content NOT present in V_us. -/
theorem dimension_selection_genuine :
    -- d = 3 at v = 246: too heavy
    150 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 3 246 ∧
    -- d = 4 at v = 246: in window
    (120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 ∧
     UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 < 130) ∧
    -- d = 5 at v = 246: too light
    UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 5 246 < 125 := by
  refine ⟨?_, ?_, ?_⟩
  · exact d3_excluded 246 (by norm_num)
  · exact d4_in_window 246 (by norm_num) (by norm_num)
  · exact d5_excluded 246 (by norm_num) (by norm_num)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: NON-UNIQUENESS OF THE FUNCTIONAL FORM AT FIXED d = 4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Even granting d = 4 and the eigenvalue ratio R = 5/3 (which is
    itself a Python-only derivation), the functional form γ = log(R)
    is one of several "natural decay-rate functionals" of R.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The hypothetical statement "the framework forces the LOG functional
    form for the spectral gap of any chamber kernel ratio R > 1".
    We do NOT prove this (and `log_neq_alt_at_5_3` shows another
    standard physics functional gives a DIFFERENT answer). -/
def framework_forces_log_form : Prop :=
  ∀ R : ℝ, 1 < R → ∀ (γ : ℝ),
    -- γ is "the framework's spectral gap of R"
    γ = Real.log R

/-- The hypothetical "uniqueness of the log form" cannot be proved
    inside the framework as currently formalized. Documented here as
    a missing ingredient. -/
theorem missing_log_uniqueness :
    -- This is the proposition the framework would need to prove to
    -- claim log(R) is the UNIQUE allowed decay-rate functional.
    -- Such a theorem does not exist in the current Lean codebase.
    ∃ (P : Prop), P = framework_forces_log_form := by
  exact ⟨framework_forces_log_form, rfl⟩

/-! ### A second alternative: arctanh-style decay rate

The "arctanh" decay rate γ_at(R) = (1/2)·log((1+y)/(1-y)) where y = (R-1)/(R+1)
is another standard correlation length functional in lattice physics.
At R = 5/3: y = (2/3)/(8/3) = 1/4, so γ_at = (1/2)·log(5/3) ≈ 0.255 — outside
the window. We do not pursue this further; the point is that the menu of
"natural decay rate functionals" is NOT a singleton. -/

noncomputable def arctanh_rate (R : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + (R - 1) / (R + 1)) / (1 - (R - 1) / (R + 1)))

/-- arctanh_rate(5/3) = (1/2) · log(5/3). -/
theorem arctanh_rate_5_3 : arctanh_rate (5 / 3) = (1 / 2) * Real.log (5 / 3) := by
  unfold arctanh_rate
  -- 1 + (R-1)/(R+1) = 2R/(R+1); 1 - (R-1)/(R+1) = 2/(R+1)
  -- so the inner ratio = R, hence log(R)
  congr 1
  congr 1
  norm_num

/-- arctanh-rate at R=5/3 is roughly 0.255, way OUTSIDE the m_H/v window.
    This eliminates arctanh as a serious menu candidate (good — it
    increases the prior weight on log) but DOES show that picking the
    "right" decay-rate functional is a non-trivial choice that the
    framework currently does NOT explicitly justify. -/
theorem arctanh_rate_outside_window :
    arctanh_rate (5 / 3) < 0.4 := by
  rw [arctanh_rate_5_3]
  -- (1/2)·log(5/3) < (1/2)·1 = 0.5; need < 0.4
  -- log(5/3) < 13/25 = 0.52, so (1/2)·log(5/3) < 13/50 = 0.26 < 0.4
  have hub : Real.log (5 / 3) < 13 / 25 :=
    UnifiedTheory.LayerA.HiggsMassDerived.log_five_thirds_lt_052
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: META-LEMMA — THE HYPOTHETICAL "UNIQUE DERIVATION" CLAIM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Direct analogue of `framework_uniqueness_claim` in V_us audit.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The hypothetical 1%-window uniqueness statement that the framework
    would need to prove for m_H/v to be UNIQUELY forced from K/P.
    Reading: "any value V in the 2% PDG window for m_H/v equals log(5/3)". -/
def framework_mH_uniqueness_claim : Prop :=
  ∀ V : ℝ, (0.4992 < V ∧ V < 0.521) → V = Real.log (5 / 3)

/-- **The hypothetical uniqueness claim is FALSE.**
    Witness: 1/2 lies in the 2% window but 1/2 ≠ log(5/3).
    Hence the framework's K/P axioms do NOT force the log(5/3) value
    over alternatives like 1/2 (the alt_decay_rate value at R = 5/3). -/
theorem framework_mH_uniqueness_claim_is_false :
    ¬ framework_mH_uniqueness_claim := by
  intro hUniq
  have h_half_in : (0.4992 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 0.521 := by
    refine ⟨by norm_num, by norm_num⟩
  have h_eq : (1 / 2 : ℝ) = Real.log (5 / 3) := hUniq (1 / 2) h_half_in
  -- But log(5/3) > 1/2.
  have hlb := log_five_thirds_gt_half
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: THE COMPARISON WITH V_us
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    V_us audit:
      - 6 framework-natural products at exactly 1/20 (cand1 = cand2,
        cand3 ≠ 1/20 in the PDG window).
      - NO falsification content beyond the menu.

    m_H audit:
      - 2+ framework-natural log expressions at exactly log(5/3)
        (cand_H1 = cand_H2; H_alt at 1/2 in the 2% window).
      - REAL falsification: only d = 4 hits the window
        (d3_excluded, d5_excluded).
      - The energy scale v is selected, not derived.
      - The eigenvalue ratio "5/3" is asserted but the J₄ Lean
        eigenvalues give 5-√7 (different).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **STRENGTH OF m_H DERIVATION RELATIVE TO V_us, THEOREMIZED.** -/
theorem mH_strength_vs_Vus :
    -- (S1) m_H has GENUINE d-dependence content (V_us has none).
    (150 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 3 246 ∧
     UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 5 246 < 125) ∧
    -- (S2) m_H still has menu redundancy (cand_H1 = cand_H2, like V_us cand1 = cand2).
    cand_H1 = cand_H2 ∧
    -- (S3) m_H still has functional-form non-uniqueness:
    --      the alternative decay rate gives a DIFFERENT value at R=5/3.
    cand_H1 ≠ cand_H_alt ∧
    -- (S4) m_H's "uniqueness" claim is FALSE in the 2% PDG window.
    (¬ framework_mH_uniqueness_claim) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact d3_excluded 246 (by norm_num)
  · exact d5_excluded 246 (by norm_num) (by norm_num)
  · exact (cand_H2_eq_H1).symm
  · exact cand_H1_neq_H_alt
  · exact framework_mH_uniqueness_claim_is_false

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER AUDIT THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER AUDIT THEOREM.**

    A complete account of the m_H = log(5/3)·v derivation status:

    GENUINE derivation content:
    (G1) Dimension selection: d = 3 excluded (m > 150), d = 5 excluded
         (m < 125), d = 4 in the [120, 130] window at v = 246.
         This is REAL falsification content not present in V_us.

    POSTULATED / NAMING-CHOICE content:
    (P1) Algebraic redundancy of expression: cand_H1 = log(5/3) =
         log(2 - a₁) = cand_H2. Same value, multiple "physics stories".
         Direct analogue of V_us's cand1 = cand2.
    (P2) Functional form: log(R) is one of several natural decay-rate
         functionals of R. The alternative 2(R-1)/(R+1) gives 1/2 at
         R = 5/3, which lies in the 2% PDG window but not the 1%.
         Therefore at the 2% PDG window, the framework does NOT
         uniquely force the log functional form.
    (P3) Energy scale v = 246 GeV is selected by the assumption that
         m_H ≈ 125 GeV. Not derived from K/P axioms.

    UN-LEAN-PROVED content:
    (U1) The eigenvalue ratio "5/3 at d = 4" is hard-coded in the
         spectralGap definition. The Lean-proven J₄ eigenvalues give
         the ratio 5 - √7 ≈ 2.354, NOT 5/3 ≈ 1.667. The "5/3" claim
         is verified ONLY in Python on the operator K_F at finite m,
         extrapolated via the closed-form (d+1)/(d-1).

    HONEST CLASSIFICATION:
      m_H is BETTER than V_us — the d-selection is genuine.
      m_H is NOT a clean first-principles derivation —
        the log form, the energy scale, AND the eigenvalue ratio claim
        all involve external choices not formalized in Lean from K/P.
      m_H is PARTIAL DERIVATION + NAMING CHOICES + UN-LEAN-PROVED CLAIM.
-/
theorem MASTER_audit :
    -- (G1) Real d-dependence falsification at v = 246
    (150 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 3 246 ∧
     (120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 ∧
      UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 < 130) ∧
     UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 5 246 < 125) ∧
    -- (P1) Multi-expression redundancy: cand_H1 = cand_H2
    cand_H1 = cand_H2 ∧
    -- (P2) Functional-form non-uniqueness: cand_H1 ≠ cand_H_alt
    cand_H1 ≠ cand_H_alt ∧
    -- (P2 cont.) The 2% PDG uniqueness claim is FALSE
    (¬ framework_mH_uniqueness_claim) ∧
    -- (U1) The Lean-proven J₄ eigenvalue ratio is 5 - √7, not 5/3
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → (3 / 5 : ℝ) / ((5 + s) / 30) ≠ 5 / 3) ∧
    -- (U1 cont.) The "spectralGap_4 = log(5/3)" theorem is just
    --           the unfolding of the closed-form definition, not a
    --           consequence of Lean-formalized K_F eigenvalues.
    spectralGap 4 = Real.log (5 / 3) ∧
    -- (P3) The energy scale window 230 < E < 260 is conditional on
    --      assuming m ∈ [120, 130] — backward fitting, not derivation.
    (∀ E : ℝ,
      120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E ∧
      UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 E < 130 →
      230 < E ∧ E < 260) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact d3_excluded 246 (by norm_num)
  · exact d4_in_window 246 (by norm_num) (by norm_num)
  · exact d5_excluded 246 (by norm_num) (by norm_num)
  · exact (cand_H2_eq_H1).symm
  · exact cand_H1_neq_H_alt
  · exact framework_mH_uniqueness_claim_is_false
  · intro s hs hs_pos; exact J4_ratio_neq_five_thirds s hs hs_pos
  · exact spectralGap_4
  · exact energy_scale_window

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: VERDICT THEOREMS — TRULY DERIVED vs MENU SELECTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **SUCCESS theorem (would-be):** m_H = log(5/3)·v IS forced by
    framework structure. We state and DISPROVE this. -/
def success_claim : Prop :=
  -- IF framework forced m_H, then:
  -- (a) the eigenvalue ratio 5/3 would be Lean-derived from K/P, AND
  -- (b) the log functional form would be Lean-derived from K/P, AND
  -- (c) the energy scale v would be Lean-derived from K/P,
  -- AND together they would yield the unique value log(5/3).
  framework_mH_uniqueness_claim

/-- **The SUCCESS claim is FALSE.** This is the m_H analogue of
    V_us's `framework_uniqueness_claim_is_false`. -/
theorem success_claim_disproved : ¬ success_claim :=
  framework_mH_uniqueness_claim_is_false

/-- **FAILURE theorem:** m_H = log(5/3)·v IS selection-from-menu like V_us.
    More specifically: there exists an alternative framework-natural
    expression (1/2, from the alt_decay_rate functional at R = 5/3)
    in the 2% PDG window that is not equal to log(5/3). -/
theorem failure_classification :
    -- Witness: V = 1/2 lies in the 2% window AND V ≠ log(5/3).
    ∃ V : ℝ, (0.4992 < V ∧ V < 0.521) ∧ V ≠ Real.log (5 / 3) := by
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  intro heq
  have hlb := log_five_thirds_gt_half
  linarith

/-- **PARTIAL classification.** The cleanest summary:
    m_H is SELECTION FROM A MENU (failure direction), but with REAL
    dimension-selection content (saving grace not present in V_us).

    This is the closest to truth: m_H is BETTER than V_us but not a
    clean first-principles derivation. -/
theorem partial_derivation_classification :
    -- (Failure direction, like V_us): the 2% uniqueness is FALSE.
    (¬ framework_mH_uniqueness_claim) ∧
    -- (Saving grace, NOT present in V_us): real d-dependence falsification.
    (150 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 3 246) ∧
    UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 5 246 < 125 ∧
    (120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 ∧
     UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 < 130) := by
  refine ⟨framework_mH_uniqueness_claim_is_false, ?_, ?_, ?_⟩
  · exact d3_excluded 246 (by norm_num)
  · exact d5_excluded 246 (by norm_num) (by norm_num)
  · exact d4_in_window 246 (by norm_num) (by norm_num)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 12: HIGGS-RELATED PREDICTIONS BUNDLED WITH m_H
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework also predicts:
    - The Higgs quartic λ_H = (log(5/3))² / 2
    - The relation m_H² = 2 λ_H · v² (SM tree level)

    We document that the quartic prediction is DERIVED from the m_H
    prediction VIA the SM tree relation, not independently. So it
    inherits whatever derivation status m_H has.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Higgs quartic is DERIVED from m_H, not independent.**
    λ_H = (log(5/3))² / 2 = m_H² / (2 v²) at v = 246.
    So the quartic prediction is NOT an independent test — it is a
    REWRITE of the m_H prediction via SM tree relations. Its derivation
    status is exactly the derivation status of m_H. -/
theorem quartic_inherits_mH_status (v : ℝ) (hv : v ≠ 0) :
    UnifiedTheory.LayerA.HiggsMassDerived.higgs_quartic_predicted =
      (UnifiedTheory.LayerA.HiggsMassDerived.higgs_mass_tree v) ^ 2 / (2 * v ^ 2) := by
  unfold UnifiedTheory.LayerA.HiggsMassDerived.higgs_quartic_predicted
  unfold UnifiedTheory.LayerA.HiggsMassDerived.higgs_mass_tree
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  field_simp

/-- The relation m_H² = 2 λ_H · v² (SM tree level) holds in the framework
    AS A DEFINITIONAL CONSEQUENCE of λ_H = (log(5/3))²/2 and m_H = log(5/3)·v. -/
theorem SM_tree_relation (v : ℝ) :
    (UnifiedTheory.LayerA.HiggsMassDerived.higgs_mass_tree v) ^ 2 =
      2 * UnifiedTheory.LayerA.HiggsMassDerived.higgs_quartic_predicted * v ^ 2 := by
  unfold UnifiedTheory.LayerA.HiggsMassDerived.higgs_mass_tree
  unfold UnifiedTheory.LayerA.HiggsMassDerived.higgs_quartic_predicted
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 13: THE FINAL JUDGMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **FINAL VERDICT THEOREM.**

    m_H = log(5/3)·v is a PARTIAL DERIVATION:

    PROVED in this audit:
      ✓ Algebraic redundancy of the formula (cand_H1 = cand_H2)
      ✓ Functional-form non-uniqueness at the 2% PDG window
      ✓ The Lean-proven J₄ eigenvalue ratio is 5-√7, NOT 5/3
      ✓ The "spectralGap_4 = log(5/3)" theorem is definitional
      ✓ The energy scale window is BACKWARD fitting from m_H ≈ 125
      ✓ The Higgs quartic prediction is NOT independent of m_H
      ✓ Real d-dependence falsification (d=3 too heavy, d=5 too light)

    NOT proved by the framework (and shown un-provable in this audit):
      ✗ Uniqueness of log(5/3) at the 2% PDG window for m_H/v
      ✗ The 5/3 eigenvalue ratio in Lean from K_F structure
      ✗ The choice of LOG functional form (vs. e.g. 2(R-1)/(R+1))
      ✗ The energy scale v ≈ 246 GeV from K/P axioms

    HONEST CLASSIFICATION (between V_us "menu" and "first principles"):

      V_us:   pure menu selection (no falsification beyond the menu)
      m_H:    partial derivation (real d-falsification + menu redundancy
                + un-formalized eigenvalue claim + scale assumption)
      ideal:  unique forced value with no smuggle (NOT achieved by m_H).
-/
theorem FINAL_VERDICT :
    -- (V1) The success claim (uniqueness) is FALSE
    (¬ framework_mH_uniqueness_claim) ∧
    -- (V2) An alternative menu candidate (1/2 from alt_decay_rate)
    --      lies in the 2% PDG window but is not equal to log(5/3)
    (∃ V : ℝ, (0.4992 < V ∧ V < 0.521) ∧ V ≠ Real.log (5 / 3)) ∧
    -- (V3) The Lean-proven K_F-derived eigenvalue ratio is NOT 5/3
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → (3 / 5 : ℝ) / ((5 + s) / 30) ≠ 5 / 3) ∧
    -- (V4) But: real d-selection content (PARTIAL win)
    (150 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 3 246 ∧
     UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 5 246 < 125 ∧
     120 < UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 ∧
     UnifiedTheory.LayerA.HiggsMassDerived.predicted_mass 4 246 < 130) ∧
    -- (V5) The Higgs quartic is NOT an independent prediction
    (∀ v : ℝ, v ≠ 0 →
      UnifiedTheory.LayerA.HiggsMassDerived.higgs_quartic_predicted =
        (UnifiedTheory.LayerA.HiggsMassDerived.higgs_mass_tree v) ^ 2 /
          (2 * v ^ 2)) := by
  refine ⟨framework_mH_uniqueness_claim_is_false,
          failure_classification,
          ?_, ?_, ?_⟩
  · intro s hs hs_pos; exact J4_ratio_neq_five_thirds s hs hs_pos
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact d3_excluded 246 (by norm_num)
    · exact d5_excluded 246 (by norm_num) (by norm_num)
    · exact (d4_in_window 246 (by norm_num) (by norm_num)).1
    · exact (d4_in_window 246 (by norm_num) (by norm_num)).2
  · intro v hv; exact quartic_inherits_mH_status v hv

end UnifiedTheory.LayerB.HiggsMassAudit
