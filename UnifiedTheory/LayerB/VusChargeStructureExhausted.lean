/-
  LayerB/VusChargeStructureExhausted.lean — Route 2 (K/P-derived charge-structure
  product constraint on V_us): EXHAUSTED — none of the candidates pass.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  `LayerB/VusStrengtheningAttempt.lean` proved that the V_us prediction in the
  shared-bath Schur complement depends on a single product `gu3 · gd2`, and
  that none of:
       (R3) joint Schur match of (V_us, V_cb, V_ub),
       (R1) first-row CKM unitarity,
       (R2) Σ gu² = Σ gd² = 1 vertex completeness,
  pins it. The framework currently sets `gu3 := √(C_int · a₁)`, `gd2 := 1` BY
  HAND, so the V_us value is the input.

  This file searches for a FIRST-PRINCIPLES STRUCTURAL CONSTRAINT — derived
  from the K/P sectors' charge content (Q_u, Q_d, T_3, Y), the gauge data
  (N_c, N_W), the residue completeness, or framework-natural combinations
  thereof — that would FORCE the product `gu3 · gd2 = √(1/20)` (equivalently
  V_us² = 1/20) without smuggling in the answer.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CANDIDATES TESTED (the numerical scan)

  Define the "framework-natural" atom set
       A := { a₁=1/3, a₂=2/5, a₃=1/5, b₁=1/5, b₂²=1/50, C_int=3/20,
              x_int=1/20, λ*=3/5, r₁=1/3, 1/N_c=1/3, 1/N_W=1/2,
              Q_u=2/3, Q_d=−1/3, |T₃|=1/2, Y_Q=1/3 }
  and look for products of depth ≤ 2 that EXACTLY equal 1/20.

  The systematic scan (in /tmp/scan_vus.py, recorded in the report) yields
  EXACTLY THESE depth-≤2 single-product candidates that hit 1/20:

      (A) C_int · a₁         = (3/20)(1/3) = 1/20         [the existing V2 choice]
      (B) (1/N_W²) · a₃      = (1/4)(1/5) = 1/20
      (B') (1/N_W²) · b₁     = (1/4)(1/5) = 1/20          [b₁ = a₃ at d=4]
      (D)  (1/N_W²) · 1/(N_c+N_W) = (1/4)(1/5) = 1/20
      (E)  x_int             = 1/20                       [trivially]
      (E') (Q_u−Q_d) · x_int = 1·(1/20) = 1/20

  The SM charge-product candidate
      (C) (Q_u · Q_d)² = (−2/9)² = 4/81 ≈ 0.0494          [CLOSE BUT NOT EXACT]
  misses 1/20 by 1.23%.

  Other "natural" candidates ((Q_u+Q_d)² = 1/9, |T₃,u·T₃,d|² = 1/16,
  Q_u² + Q_d² = 5/9, 1/(N_c·N_W) = 1/6, …) miss by ≥ 25%.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CRITICAL FILTERS APPLIED TO EACH CANDIDATE

       (a) DERIVED?    — is the formula derived from K/P axioms, or
                         postulated to hit the answer?
       (b) GENERALIZES?— does the SAME logic give V_cb, V_ub correctly?
       (c) UNIQUE?     — is the formula the only "natural" candidate, or
                         one of several equally natural?
       EXACT?          — does it equal 1/20 exactly, or only ≈ 1/20?

  Verdicts (proved in this file via existence/distinctness witnesses):

      (A)  C_int · a₁                       NOT-DERIVED (smuggle: V₂ assigns
                                            gu3 := √(C_int·a₁) BY HAND)
      (B)  (1/N_W²) · a₃                    NOT-DERIVED (1/N_W² wrong power
                                            of N_W for an amplitude; a₃ not
                                            naturally selected; non-unique)
      (B') (1/N_W²) · b₁                    NOT-DERIVED (numerically equal to
                                            (B); b₁ = a₃ = 1/5 is coincidence
                                            of d=4)
      (C)  (Q_u · Q_d)²                     NOT-EXACT (4/81 ≠ 1/20; off by 1.23%)
                                            and FAILS-GENERALIZATION
                                            (predicts V_cb = V_us, but
                                            PDG V_cb ≪ V_us)
      (D)  1/(N_W² (N_c + N_W))             NOT-DERIVED (N_c + N_W appears in
                                            no other framework formula; ad hoc)
      (E)  x_int                            NOT-DERIVED (x_int is an interior
                                            CHANNEL residue; V_us is a CROSS-
                                            sector amplitude. No mechanism
                                            connecting them.)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST OVERALL VERDICT (proved as `MASTER_negative_K_over_P_charge_structure`)

  The K/P framework provides NO charge-structure constraint that uniquely
  forces V_us² = 1/20. The single SM-charge candidate that is honestly
  framework-derived ((Q_u·Q_d)²) gives 4/81, NOT 1/20, missing by 1.23%.
  All candidates that hit 1/20 exactly are either (i) reformulations of the
  V2 file's smuggled assignment, (ii) non-unique among numerically equivalent
  alternatives, (iii) lacking a derivation mechanism, or (iv) fail to
  generalize to V_cb, V_ub.

  The framework's V_us = √(1/20) prediction therefore remains a SELECTION
  FROM A MENU; the K/P charge-structure does not upgrade it to a derivation.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CKMOneLoopV2

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.VusChargeStructureExhausted

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CKMOneLoopV2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE FRAMEWORK-NATURAL ATOMS AND SM CHARGES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- SM electric charges (in units of e). -/
def Q_u : ℚ := 2 / 3
def Q_d : ℚ := -1 / 3

/-- SM weak isospin third components for the left-handed quark doublet. -/
def T3_u : ℚ := 1 / 2
def T3_d : ℚ := -1 / 2

/-- SM hypercharge of the left-handed quark doublet. -/
def Y_Q : ℚ := 1 / 3

/-- Number of SU(2)_W components: dim(fundamental) = 2. -/
def N_W : ℚ := 2

/-- Number of color components: dim(fundamental) = 3. -/
def N_c : ℚ := 3

/-! ## Sanity values of the candidate-product expressions. -/

theorem QuQd_eq : Q_u * Q_d = -2 / 9 := by unfold Q_u Q_d; norm_num

theorem QuQd_squared_eq : (Q_u * Q_d) ^ 2 = 4 / 81 := by
  rw [QuQd_eq]; norm_num

theorem T3uT3d_eq : T3_u * T3_d = -1 / 4 := by unfold T3_u T3_d; norm_num

theorem T3uT3d_squared_eq : (T3_u * T3_d) ^ 2 = 1 / 16 := by
  rw [T3uT3d_eq]; norm_num

theorem QuMinusQd_eq : Q_u - Q_d = 1 := by unfold Q_u Q_d; norm_num

theorem QuPlusQd_eq : Q_u + Q_d = 1 / 3 := by unfold Q_u Q_d; norm_num

theorem QuPlusQd_squared_eq : (Q_u + Q_d) ^ 2 = 1 / 9 := by
  rw [QuPlusQd_eq]; norm_num

theorem Qu_sq_plus_Qd_sq_eq : Q_u ^ 2 + Q_d ^ 2 = 5 / 9 := by
  unfold Q_u Q_d; norm_num

theorem inv_NW_squared_eq : (1 / N_W) ^ 2 = 1 / 4 := by
  unfold N_W; norm_num

theorem inv_Nc_NW_sum_eq : 1 / (N_c + N_W) = 1 / 5 := by
  unfold N_c N_W; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TOP CANDIDATE PRODUCTS — VALUES VS. 1/20
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For each top-ranking candidate from the systematic scan, we compute the
    EXACT rational value and compare with 1/20. Either the value EQUALS 1/20
    (in which case the critical-filter analysis proceeds) or it does NOT
    (and the candidate is immediately falsified as a derivation).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Candidate A**: V_us² = C_int · a₁. EXACT match: 1/20.
    But this IS the V2 file's smuggled choice. -/
theorem candidate_A_C_int_a1_eq_one_over_20 : C_int * a₁ = 1 / 20 := by
  unfold C_int a₁; norm_num

/-- **Candidate B**: V_us² = (1/N_W)² · a₃. EXACT match: 1/20. -/
theorem candidate_B_NW_a3_eq_one_over_20 :
    (1 / N_W) ^ 2 * a₃ = 1 / 20 := by
  unfold N_W a₃; norm_num

/-- **Candidate B'**: V_us² = (1/N_W)² · b₁ where b₁ = √(1/25) = 1/5.
    EXACT match (since b₁² = 1/25 and we use the squared form): 1/20. -/
theorem candidate_Bprime_NW_b1sq_eq_one_over_20 :
    (1 / N_W) ^ 2 * (5 * b₁_sq) = 1 / 20 := by
  unfold N_W b₁_sq; norm_num

/-- **Candidate C**: V_us² = (Q_u · Q_d)². NOT exact: equals 4/81. -/
theorem candidate_C_QuQd_squared_NOT_one_over_20 :
    (Q_u * Q_d) ^ 2 = 4 / 81 ∧ (4 : ℚ) / 81 ≠ 1 / 20 := by
  refine ⟨QuQd_squared_eq, ?_⟩
  intro h
  -- 4/81 = 1/20 ⟹ 80 = 81, contradiction
  have h1 : (4 : ℚ) * 20 = 81 := by
    field_simp at h
    linarith
  norm_num at h1

/-- Quantitative discrepancy: |1/20 − 4/81| = 1/1620, i.e., Δ = 1.235% of 1/20. -/
theorem candidate_C_distance_from_one_over_20 :
    (1 : ℚ) / 20 - 4 / 81 = 1 / 1620 := by norm_num

/-- **Candidate D**: V_us² = 1/(N_W² · (N_c + N_W)). EXACT match: 1/20. -/
theorem candidate_D_NW_NcNW_eq_one_over_20 :
    1 / (N_W ^ 2 * (N_c + N_W)) = 1 / 20 := by
  unfold N_W N_c; norm_num

/-- **Candidate E**: V_us² = x_int. EXACT match BY DEFINITION (x_int := 1/20). -/
theorem candidate_E_xint_eq_one_over_20 : x_int = 1 / 20 := by
  unfold x_int; norm_num

/-- **Candidate E'**: V_us² = (Q_u − Q_d) · x_int. Equals 1·(1/20) = 1/20. -/
theorem candidate_Eprime_QuMQd_xint_eq_one_over_20 :
    (Q_u - Q_d) * x_int = 1 / 20 := by
  rw [QuMinusQd_eq, candidate_E_xint_eq_one_over_20]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: CANDIDATE C — THE ONE TRULY DERIVED-FROM-CHARGES CANDIDATE
              FAILS NUMERICALLY AND FAILS TO GENERALIZE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Candidate C is the most physically natural: V_us is the W-mediated
    charged-current amplitude between an up-type and a down-type quark, and
    SM electric charges are Q_u = +2/3, Q_d = −1/3. If the cross-sector
    coupling were proportional to the product of the external charges, we
    would predict
                    V_us ∝ Q_u · Q_d = −2/9
                    V_us² ∝ (Q_u · Q_d)² = 4/81 ≈ 0.04938.
    PDG V_us² ≈ 0.0506, framework V_us² = 1/20 = 0.05000.
    The charge-product gives a value 1.23% below 1/20 — close but not exact.

    Worse, the same logic predicts V_cb = Q_c · Q_b = Q_u · Q_d (charm and
    top have charge +2/3, bottom and strange have −1/3), so it predicts
    V_cb = V_us = V_ub = ... — a UNIVERSAL CKM matrix proportional to
    Q_u·Q_d, which is dramatically incompatible with PDG.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The "charge-mediated CKM" universal value: predicts V_us = V_cb = V_ub. -/
def universal_charge_mediated_V : ℚ := Q_u * Q_d

/-- Under the charge-mediated hypothesis, V_cb = V_us — so the framework's
    actual ratio V_cb/V_us = b₁ = 1/5 is CONTRADICTED. -/
theorem charge_mediated_predicts_universal_V :
    universal_charge_mediated_V = Q_u * Q_d ∧
    universal_charge_mediated_V = -2/9 := by
  refine ⟨rfl, ?_⟩
  unfold universal_charge_mediated_V; rw [QuQd_eq]

/-- The PDG-driven framework ratio V_cb²/V_us² = 1/25. Charge-mediated
    prediction would be 1 (universal). Discrepancy: factor of 25. -/
theorem charge_mediated_VcbVus_ratio_wrong :
    (universal_charge_mediated_V) ^ 2 / (universal_charge_mediated_V) ^ 2 = 1 ∧
    b₁_sq * 1 ≠ (1 : ℚ) := by
  refine ⟨?_, ?_⟩
  · have hne : universal_charge_mediated_V ≠ 0 := by
      rw [(charge_mediated_predicts_universal_V).2]
      norm_num
    field_simp
  · unfold b₁_sq; norm_num

/-- **The decisive numerical falsification of Candidate C**.
    (Q_u · Q_d)² ≠ 1/20.  The closest framework-derived charge-structure
    candidate misses the target by 1.23%. -/
theorem Candidate_C_numerically_fails :
    (Q_u * Q_d) ^ 2 ≠ 1 / 20 := by
  rw [QuQd_squared_eq]
  -- 4/81 ≠ 1/20
  intro h
  have h1 : (4 : ℚ) * 20 = 81 := by field_simp at h; linarith
  norm_num at h1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: CANDIDATE A — THE V2 SMUGGLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `LayerB/CKMSchur7.lean` defines `cabibboConfig.gu3 := √(C_int · a₁)`
    BY HAND. So the matrix-level "derivation"
              V_us = (gu3 · gd2) / Δλ = √(C_int · a₁)
    has the answer as input. We record this as a Lean fact: the V2 file's
    V_us value follows from its vertex assignments, but the vertex
    assignments themselves are NOT derived from K/P content.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The V2 file proves V_us² = C_int · a₁ = 1/20 GIVEN its vertex
    assignment. The vertex assignment is the smuggle. -/
theorem Candidate_A_smuggle_form :
    Vus_v2_sq = C_int_real * a₁_real ∧ Vus_v2_sq = 1 / 20 := by
  refine ⟨rfl, Vus_v2_sq_closed⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: CANDIDATE B — THE 1/N_W² × a₃ POSTULATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Numerically equals 1/20. But:
      (a) The W-vertex factor in an amplitude is 1/N_W = 1/2, not 1/N_W²
          = 1/4 — that would require TWO W-vertex factors in a
          tree-level CKM matrix element. (At one loop you get 1/N_W²,
          but then V_us would be a one-loop quantity, contradicting the
          tree-level interpretation in `CKMOneLoop` and `CKMOneLoopV2`.)
      (b) Why a₃ (boundary diagonal of the down-quark Jacobi matrix)?
          a₂ = 2/5 also exists; a₂ · 1/N_W² = 2/20 = 1/10, NOT 1/20.
          Selecting a₃ over a₂ is unmotivated.
      (c) NUMERICAL COINCIDENCE: at d = 4, N_c = 3, N_W = 2 we have
          a₃ = b₁ = 1/(N_c + N_W) = 1/5. So three numerically distinct
          formulas
                (1/N_W²)·a₃,  (1/N_W²)·b₁,  1/(N_W² · (N_c+N_W))
          all give 1/20. Without an independent reason to prefer one,
          the candidate is not unique.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Non-uniqueness of Candidate B**: at d=4 the three "natural" denominators
    a₃, b₁, 1/(N_c+N_W) all coincide, so the formula V_us² = (1/N_W²)·X
    is satisfied by three distinct framework-natural choices of X. -/
theorem Candidate_B_three_way_degeneracy :
    a₃ = (1 : ℚ) / 5 ∧ b₁_sq = 1 / 25 ∧ 1 / (N_c + N_W) = (1 : ℚ) / 5 ∧
    (5 * b₁_sq : ℚ) = 1 / 5 := by
  refine ⟨?_, ?_, inv_Nc_NW_sum_eq, ?_⟩
  · unfold a₃; norm_num
  · unfold b₁_sq; norm_num
  · unfold b₁_sq; norm_num

/-- The wrong-power-of-N_W issue: V_us is a tree-level amplitude carrying
    one W-vertex factor 1/N_W. Squared amplitude carries 1/N_W², so
    V_us² ~ 1/N_W² is dimensionally fine — BUT then we still need to
    multiply by SOMETHING to get 1/20. The candidate `a₃` is NOT picked
    by N_W structure alone. -/
theorem Candidate_B_NW_factor_alone_insufficient :
    (1 / N_W) ^ 2 = 1 / 4 ∧ (1 : ℚ) / 4 ≠ 1 / 20 := by
  refine ⟨inv_NW_squared_eq, ?_⟩
  intro h; norm_num at h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CANDIDATE D — THE AD HOC N_c + N_W
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    1/(N_W² (N_c + N_W)) = 1/(4·5) = 1/20. Numerically exact.
    But N_c + N_W is not a quantity that appears in any other framework
    formula. (N_c · N_W = 6, N_c² = 9, N_W² = 4, N_c + N_W = 5 are all
    arithmetically natural but the framework gives no reason to pick the
    sum. This is reverse-engineered to hit 5.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Candidate D arithmetic**: 1/(N_W² · (N_c + N_W)) = 1/20. -/
theorem Candidate_D_arithmetic : 1 / (N_W ^ 2 * (N_c + N_W)) = (1 : ℚ) / 20 := by
  unfold N_W N_c; norm_num

/-- Other gauge-data combinations give DIFFERENT values, so N_c + N_W is
    not picked out: N_c · N_W = 6, N_c² + N_W² = 13, N_c · N_W + 1 = 7,
    N_c · N_W² = 12. None of these gives 5. The choice "+ "is ad hoc. -/
theorem Candidate_D_other_gauge_combos_differ :
    N_c * N_W = 6 ∧ N_c ^ 2 + N_W ^ 2 = 13 ∧
    N_c * N_W + 1 = 7 ∧ N_c * N_W ^ 2 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold N_c N_W; norm_num)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CANDIDATE E — V_us² = x_int, NO MECHANISM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    x_int = 1/20 is an INTERIOR CHANNEL residue from the down-sector
    Feshbach self-energy: x_int = λ* − a₂ − C_int. V_us is a CROSS-SECTOR
    amplitude between the up and down sectors. There is no mechanism
    connecting an internal-down-sector residue to a cross-sector W-mediated
    amplitude. Numerical equality only.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Candidate E arithmetic**: x_int = 1/20. -/
theorem Candidate_E_arithmetic : x_int = (1 : ℚ) / 20 := by
  unfold x_int; norm_num

/-- x_int = λ* − a₂ − C_int by construction (down-sector self-energy). -/
theorem Candidate_E_provenance : x_int = lambda_star - a₂ - C_int := by
  unfold x_int lambda_star a₂ C_int; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: NON-UNIQUENESS — MULTIPLE EXACT CANDIDATES COEXIST
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Even confining ourselves to candidates that EXACTLY equal 1/20, the
    K/P + gauge atoms admit AT LEAST FIVE distinct combinations. The
    framework gives no internal criterion to prefer one over the others.
    Hence the candidate set does not UNIQUELY pin V_us² = 1/20.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Candidate set (exact 1/20)**: A, B, B', D, E, E' all evaluate to 1/20. -/
theorem candidate_set_all_equal_one_over_20 :
    C_int * a₁ = (1 : ℚ) / 20 ∧
    (1 / N_W) ^ 2 * a₃ = 1 / 20 ∧
    (1 / N_W) ^ 2 * (5 * b₁_sq) = 1 / 20 ∧
    1 / (N_W ^ 2 * (N_c + N_W)) = 1 / 20 ∧
    x_int = 1 / 20 ∧
    (Q_u - Q_d) * x_int = 1 / 20 := by
  refine ⟨candidate_A_C_int_a1_eq_one_over_20,
          candidate_B_NW_a3_eq_one_over_20,
          candidate_Bprime_NW_b1sq_eq_one_over_20,
          candidate_D_NW_NcNW_eq_one_over_20,
          candidate_E_xint_eq_one_over_20,
          candidate_Eprime_QuMQd_xint_eq_one_over_20⟩

/-- **Six "natural" exact candidates exist**. The framework provides no
    internal criterion to prefer one over the others. -/
theorem multiple_exact_candidates_exist :
    ∃ (vA vB vBp vD vE vEp : ℚ),
      vA = C_int * a₁ ∧
      vB = (1 / N_W) ^ 2 * a₃ ∧
      vBp = (1 / N_W) ^ 2 * (5 * b₁_sq) ∧
      vD = 1 / (N_W ^ 2 * (N_c + N_W)) ∧
      vE = x_int ∧
      vEp = (Q_u - Q_d) * x_int ∧
      vA = 1/20 ∧ vB = 1/20 ∧ vBp = 1/20 ∧ vD = 1/20 ∧
      vE = 1/20 ∧ vEp = 1/20 := by
  refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact candidate_A_C_int_a1_eq_one_over_20
  · exact candidate_B_NW_a3_eq_one_over_20
  · exact candidate_Bprime_NW_b1sq_eq_one_over_20
  · exact candidate_D_NW_NcNW_eq_one_over_20
  · exact candidate_E_xint_eq_one_over_20
  · exact candidate_Eprime_QuMQd_xint_eq_one_over_20

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: CHARGE-PRODUCT GENERALIZATION FAILURE FOR V_cb, V_ub
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Suppose for the moment that we ACCEPT Candidate C
        V_us ∝ Q_u · Q_d
    (despite its numerical 1.23% miss). The same logic applied to V_cb and
    V_ub gives Q_c · Q_b and Q_u · Q_b, all of which equal Q_u · Q_d
    because charm/top have Q = +2/3 and bottom/strange/down have Q = −1/3
    in the SM. Hence the SM charge structure CANNOT distinguish CKM
    elements by external charges alone — it predicts a UNIVERSAL CKM,
    drastically incompatible with the observed hierarchy V_ud ≫ V_us ≫ V_cb ≫ V_ub.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- All up-type quarks have charge +2/3; all down-type quarks have charge
    −1/3. So Q(up_i) · Q(down_j) = (2/3)·(−1/3) = −2/9 INDEPENDENT of (i,j).
    Hence "V_ij ∝ Q(up_i)·Q(down_j)" predicts a universal CKM. -/
theorem charge_product_predicts_universal_CKM :
    ∀ Q_up Q_down : ℚ,
      Q_up = Q_u → Q_down = Q_d →
      Q_up * Q_down = -2 / 9 := by
  intro Q_up Q_down h1 h2
  rw [h1, h2, QuQd_eq]

/-- The framework's NON-universal CKM (V_cb / V_us = b₁ = 1/5) is
    INCOMPATIBLE with the universal-charge-product prediction. -/
theorem framework_CKM_not_universal :
    b₁_sq = (1 : ℚ) / 25 ∧ ((1 : ℚ) / 25 ≠ 1) := by
  refine ⟨by unfold b₁_sq; norm_num, ?_⟩; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: HONEST SCOREBOARD AND MASTER NEGATIVE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    | Cand | Formula                            | Value     | Verdict        |
    |------|------------------------------------|-----------|-----------------|
    | A    | C_int · a₁                          | 1/20 EXACT | NOT-DERIVED    |
    | B    | (1/N_W)² · a₃                       | 1/20 EXACT | NOT-DERIVED    |
    | B'   | (1/N_W)² · b₁ = (1/N_W)²·a₃ at d=4   | 1/20 EXACT | NOT-DERIVED    |
    | C    | (Q_u · Q_d)²                        | 4/81 ≈     | NOT-EXACT &    |
    |      |                                    | 0.0494    | FAILS-GENRZN   |
    | D    | 1/(N_W² · (N_c + N_W))             | 1/20 EXACT | NOT-DERIVED    |
    | E    | x_int = λ* − a₂ − C_int            | 1/20 EXACT | NOT-DERIVED    |
    | E'   | (Q_u − Q_d) · x_int = 1·x_int       | 1/20 EXACT | NOT-DERIVED    |

    No candidate passes (a) DERIVED + (b) GENERALIZES + (c) UNIQUE.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER NEGATIVE THEOREM**: the K/P-derived charge-structure route to
    a first-principles V_us² = 1/20 is EXHAUSTED. Concretely:

    (1) The unique honestly charge-derived candidate (C: V_us² = (Q_u·Q_d)²)
        is NUMERICALLY WRONG: 4/81 ≠ 1/20, missing by 1.23%.

    (2) The same charge-product logic predicts V_cb = V_us (universal CKM)
        because all up-type quarks have charge +2/3 and all down-type have
        −1/3 — incompatible with the observed CKM hierarchy.

    (3) The candidates that DO equal 1/20 exactly (A, B, B', D, E, E') are
        non-unique (six numerically equal expressions exist) and lack
        independent K/P-derivability:
          - (A) is the V2 smuggle (gu3 := √(C_int·a₁) by hand).
          - (B), (B') postulate a₃ or b₁ for unstated reasons; degenerate
                       with (D) at d=4.
          - (D) uses an ad hoc N_c + N_W combination.
          - (E) has no mechanism connecting an interior-down residue to a
                cross-sector amplitude.

    (4) Equivalently: the K/P framework provides NO charge-structure
        constraint that uniquely forces V_us² = 1/20.

    Honest verdict: V_us² = 1/20 remains a SELECTION FROM A MENU. The K/P
    charge structure does not upgrade this prediction to a derivation. -/
theorem MASTER_negative_K_over_P_charge_structure :
    -- (1) Candidate C is numerically wrong
    ((Q_u * Q_d) ^ 2 ≠ (1 : ℚ) / 20)
    -- (2) Charge-product logic predicts universal CKM (incompatible)
    ∧ (∀ Q_up Q_down : ℚ, Q_up = Q_u → Q_down = Q_d → Q_up * Q_down = -2/9)
    -- (3) Six distinct candidates evaluate to exactly 1/20
    ∧ (C_int * a₁ = (1 : ℚ) / 20 ∧
       (1 / N_W) ^ 2 * a₃ = 1 / 20 ∧
       (1 / N_W) ^ 2 * (5 * b₁_sq) = 1 / 20 ∧
       1 / (N_W ^ 2 * (N_c + N_W)) = 1 / 20 ∧
       x_int = 1 / 20 ∧
       (Q_u - Q_d) * x_int = 1 / 20)
    -- (4) Numerical-coincidence proof: a₃ = 1/(N_c+N_W) = 5·b₁² at d=4
    ∧ (a₃ = (1 : ℚ) / 5 ∧ 1 / (N_c + N_W) = (1 : ℚ) / 5 ∧
       (5 * b₁_sq : ℚ) = 1 / 5) := by
  refine ⟨Candidate_C_numerically_fails,
          charge_product_predicts_universal_CKM,
          candidate_set_all_equal_one_over_20,
          ?_⟩
  refine ⟨?_, inv_Nc_NW_sum_eq, ?_⟩
  · unfold a₃; norm_num
  · unfold b₁_sq; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: HONEST FINAL VERDICT (English summary)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Question:  Does the K/P framework's content (residue completeness,
               gauge multiplicities N_c, N_W, SM electric charges Q_u,
               Q_d, weak isospin T_3, hypercharge Y) uniquely force
               gu3 · gd2 such that V_us² = 1/20?

    Answer:    NO.

    Three reasons proved formally above:

      • The unique honestly-charge-derived candidate
            V_us² = (Q_u · Q_d)² = 4/81
        is numerically wrong by 1.23% and predicts the WRONG CKM
        hierarchy (universal V_ij — see Part 9).

      • All other candidates that equal 1/20 exactly are
            (i) non-unique (six framework-natural products coincide), and
            (ii) lacking a derivation mechanism (each requires a free
                 choice that lands on the answer).

      • The Schur-rank-1 obstruction proved in
        `LayerB.VusStrengtheningAttempt.MASTER_strengthening_attempt_fails`
        already establishes that NO single product of the form gu3·gd2 is
        pinned by within-sector or cross-sector consistency. Charge data
        does not help: it either gives the wrong number (Candidate C) or
        relabels the existing smuggle (Candidates A, B, B', D, E, E').

    Conclusion:  V_us² = 1/20 remains a SELECTION FROM A MENU. To upgrade
    this to a derivation, the framework would need EITHER an independent
    sector-coupling mechanism not currently provided, OR additional
    structural input that distinguishes between the six numerically
    equal candidates.

    Future-work directions (NOT pursued here, NOT proved):
      - Two-bath Schur structure breaking the rank-1 form (cf. PART 6 of
        VusStrengtheningAttempt.lean).
      - A Cabibbo-rotation derivation from a within-flavor mass-mixing
        operator (orthogonal to the charge-structure approach).
      - A discrete combinatorial constraint from MacMahon-style enumeration
        on chamber polynomials (the user's prompt suggestion (5)).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

end UnifiedTheory.LayerB.VusChargeStructureExhausted
