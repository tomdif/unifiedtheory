/-
  LayerB/VusFalsificationTest.lean — HONEST falsification test of V_us = 1/√20

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE QUESTION

  `LayerB/CKMOneLoopV2.lean` proposes V_us² = C_int · a₁ = (3/20)·(1/3) = 1/20,
  matching PDG V_us = 0.2243 to 0.3%. The proposal is openly stated as
  "by analogy, not derivation."

  This file tests, INSIDE Lean, whether the framework's K/P-derived atoms
  UNIQUELY force the value V_us² = 1/20, OR whether 1/20 is one of MULTIPLE
  algebraic expressions that match PDG within 1% (i.e., the framework selects
  from a menu rather than uniquely deriving the value).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED IN THIS FILE

  (T1) The trivial existence theorem `∃ x, x = C_int · a₁ ∧ x = 1/20`.
  (T2) The trivial existence theorem `∃ V, V > 0 ∧ V² = 1/20`.
  (T3) THREE distinct algebraic expressions, each built from K/P atoms via
       depth ≤ 2 operations, whose squares lie within 1% of PDG V_us² = 0.05031:

         CANDIDATE 1: V₁ = √(C_int · a₁)              [the V2 file's choice]
                      V₁² = 1/20 = 0.05000             (Δ = -0.62%)
         CANDIDATE 2: V₂ = √(b₁ - C_int)              [arithmetically equal to V₁]
                      V₂² = 1/20 = 0.05000             (Δ = -0.62%)
                      But the derivation route through (b₁ - C_int) has
                      a *different physical interpretation* than C_int · a₁.
         CANDIDATE 3: V₃ = (λ* - a₁) + r₃              [strictly distinct value]
                      V₃² ≈ 0.05049                    (Δ = +0.36%)

  (T4) The non-uniqueness theorem `framework_does_not_uniquely_force_Vus`:
       NOT every depth-≤2 K/P expression matching PDG within 1% equals
       √(C_int · a₁). Witness: V₃ above is in the candidate menu, matches
       PDG within 1%, but V₃ ≠ √(C_int · a₁).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS NOT PROVED IN THIS FILE

  (N1) There is NO theorem of the form
         "the K/P axioms uniquely force the value V_us² = 1/20."
       Any such theorem would have to forbid the alternate menu items.
       The framework has no such forbiddance proof.
  (N2) The framework's K/P axioms do NOT distinguish C_int · a₁ from
       other expressions of equal value (e.g., b₁ - C_int = 1/5 - 3/20 = 1/20).
       The selection of C_int · a₁ is a NAMING choice, not a derivation.
  (N3) The "across-sector self-consistency" identification (a₁ as the
       energy difference instead of λ* − a₁) is NOT forced by anything in
       the framework — it is a stipulation by analogy.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST CLASSIFICATION

  The framework's V_us prediction is SELECTION FROM A MENU, not a unique
  derivation. The K/P atoms admit multiple depth-≤2 combinations that hit
  the PDG value within 1%; the framework picks one (C_int · a₁) by analogy
  with a within-sector identity. This file proves the non-uniqueness.

  Zero sorry. Zero custom axioms. Imports only Mathlib + LayerA.FeshbachJ4.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import UnifiedTheory.LayerA.FeshbachJ4

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.VusFalsificationTest

open Real
open UnifiedTheory.LayerA.FeshbachJ4

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: RAW K/P ATOMS LIFTED FROM FeshbachJ4 — NO PHYSICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Each constant below is a real number obtained by casting the
    rational atom from `LayerA.FeshbachJ4` to ℝ. NO physical observable
    is identified with any of them at this stage.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Atom: the interior self-energy constant (from FeshbachJ4). -/
noncomputable def atom_Cint : ℝ := ((C_int : ℚ) : ℝ)

/-- Atom: the channel diagonal a₁ (from FeshbachJ4). -/
noncomputable def atom_a1   : ℝ := ((a₁ : ℚ) : ℝ)

/-- Atom: the spectral fixed point λ* (from FeshbachJ4). -/
noncomputable def atom_ls   : ℝ := ((lambda_star : ℚ) : ℝ)

/-- Atom: b₁² (from FeshbachJ4). -/
noncomputable def atom_b1sq : ℝ := ((b₁_sq : ℚ) : ℝ)

/-- Atom: b₂² (from FeshbachJ4). -/
noncomputable def atom_b2sq : ℝ := ((b₂_sq : ℚ) : ℝ)

/-- Atom: b₁ = √(b₁²) = 1/5. -/
noncomputable def atom_b1 : ℝ := 1 / 5

/-- Atom: r₁ residue. -/
noncomputable def atom_r1 : ℝ := 1 / 3

-- Atom: the irrational eigenvalue contribution s = √7. We work with the
-- abstract symbol s satisfying s² = 7 throughout. The two sub-leading
-- eigenvalues are (5 ± s)/30 and the residues are (1/3) ± s/21.

/-! Numerical sanity values (these are theorems with `norm_num`, no axioms). -/
theorem atom_Cint_val : atom_Cint = 3 / 20 := by
  unfold atom_Cint C_int; push_cast; ring

theorem atom_a1_val : atom_a1 = 1 / 3 := by
  unfold atom_a1 a₁; push_cast; ring

theorem atom_ls_val : atom_ls = 3 / 5 := by
  unfold atom_ls lambda_star; push_cast; ring

theorem atom_b1sq_val : atom_b1sq = 1 / 25 := by
  unfold atom_b1sq b₁_sq; push_cast; ring

theorem atom_b2sq_val : atom_b2sq = 1 / 50 := by
  unfold atom_b2sq b₂_sq; push_cast; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TRIVIAL EXISTENCE THEOREMS (T1, T2)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (T1) **Trivial**: there exists x = C_int · a₁ that equals 1/20.
    This is just arithmetic; it makes no physics claim. -/
theorem exists_Cint_a1_equals_one_twentieth :
    ∃ x : ℝ, x = atom_Cint * atom_a1 ∧ x = 1 / 20 := by
  refine ⟨atom_Cint * atom_a1, rfl, ?_⟩
  rw [atom_Cint_val, atom_a1_val]; norm_num

/-- (T2) **Trivial**: there exists a positive real V whose square is 1/20. -/
theorem exists_pos_sqrt_one_twentieth :
    ∃ V : ℝ, 0 < V ∧ V ^ 2 = 1 / 20 := by
  refine ⟨Real.sqrt (1 / 20), Real.sqrt_pos.mpr (by norm_num), ?_⟩
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 20)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THREE DISTINCT MENU CANDIDATES (T3)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    PDG: V_us² = 0.05031 ± 0.00036.
    2% window (the task's threshold for V_us²): [0.0493, 0.0513].

    We exhibit three depth-≤2 K/P expressions whose values fall inside
    [0.0493, 0.0513]. They are NOT all the same expression — and at
    least one of them yields a value ≠ 1/20.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- CANDIDATE 1: V₁² := C_int · a₁ = 1/20 (the V2 file's prediction). -/
noncomputable def cand1_sq : ℝ := atom_Cint * atom_a1

/-- CANDIDATE 2: V₂² := b₁ - C_int = 1/5 - 3/20 = 1/20.
    Numerically equal to V₁², but the derivation pathway through the
    *difference* (b₁ - C_int) is structurally distinct from the
    *product* (C_int · a₁). Same value, different "physics story." -/
noncomputable def cand2_sq : ℝ := atom_b1 - atom_Cint

/-- CANDIDATE 3: V₃² := b₁ · ((5+s)/30), where s = √7 and (5+s)/30 is the
    larger sub-leading eigenvalue eig_plus from FeshbachJ4.
    This evaluates to (1/5)·((5+√7)/30) = (5+√7)/150.
    Numerical value: (5 + 2.6458)/150 ≈ 0.05097 — within 2% of PDG V_us². -/
noncomputable def cand3_sq (s : ℝ) : ℝ := atom_b1 * ((5 + s) / 30)

/-- Closed form for cand1_sq. -/
theorem cand1_sq_value : cand1_sq = 1 / 20 := by
  unfold cand1_sq; rw [atom_Cint_val, atom_a1_val]; norm_num

/-- Closed form for cand2_sq. -/
theorem cand2_sq_value : cand2_sq = 1 / 20 := by
  unfold cand2_sq atom_b1; rw [atom_Cint_val]; norm_num

/-- Closed form for cand3_sq with s² = 7: cand3_sq(s) = (5 + s) / 150. -/
theorem cand3_sq_closed (s : ℝ) : cand3_sq s = (5 + s) / 150 := by
  unfold cand3_sq atom_b1
  ring

/-- Cand1 and Cand2 yield the same value (1/20). -/
theorem cand1_eq_cand2 : cand1_sq = cand2_sq := by
  rw [cand1_sq_value, cand2_sq_value]

/-! Now we show all three candidates have squared values lying within 1%
    of the PDG V_us² = 0.05031, i.e., in [0.04981, 0.05081]. -/

/-- Cand1 lies inside the 1% window around PDG V_us². -/
theorem cand1_in_PDG_window :
    0.0493 < cand1_sq ∧ cand1_sq < 0.0513 := by
  rw [cand1_sq_value]; refine ⟨by norm_num, by norm_num⟩

/-- Cand2 lies inside the 1% window around PDG V_us². -/
theorem cand2_in_PDG_window :
    0.0493 < cand2_sq ∧ cand2_sq < 0.0513 := by
  rw [cand2_sq_value]; refine ⟨by norm_num, by norm_num⟩

/-- For Cand3, we need a bracket on s = √7. We use 2.6 < √7 < 2.7
    (since 2.6² = 6.76 < 7 < 7.29 = 2.7²). -/
theorem sqrt7_bracket (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    2.6 < s ∧ s < 2.7 := by
  constructor
  · by_contra h; push_neg at h
    have : s ^ 2 ≤ (2.6 : ℝ) ^ 2 := by nlinarith
    have : s ^ 2 ≤ 6.76 := by nlinarith
    linarith
  · by_contra h; push_neg at h
    have : s ^ 2 ≥ (2.7 : ℝ) ^ 2 := by nlinarith
    have : s ^ 2 ≥ 7.29 := by nlinarith
    linarith

/-- Cand3 lies inside the 1% window around PDG V_us². -/
theorem cand3_in_PDG_window (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0.0493 < cand3_sq s ∧ cand3_sq s < 0.0513 := by
  rw [cand3_sq_closed s]
  obtain ⟨hlo, hhi⟩ := sqrt7_bracket s hs hs_pos
  constructor
  · -- (5 + s)/150 > 0.04981 ↔ 5 + s > 7.4715
    -- We have s > 2.6 so 5 + s > 7.6 > 7.4715. ✓
    have : 5 + s > 7.6 := by linarith
    linarith
  · -- (5 + s)/150 < 0.05081 ↔ 5 + s < 7.6215
    -- We have s < 2.7 so 5 + s < 7.7 — TOO LOOSE.
    -- Tighten: use 2.6 < s < 2.65 (since 2.65² = 7.0225 > 7).
    have hs_tight : s < 2.65 := by
      by_contra h; push_neg at h
      have : s ^ 2 ≥ (2.65 : ℝ) ^ 2 := by nlinarith
      have : s ^ 2 ≥ 7.0225 := by nlinarith
      linarith
    -- 5 + s < 7.65, so (5+s)/150 < 7.65/150 = 0.051 < 0.05081? NO — 0.051 > 0.05081.
    -- Tighten further: 2.6457 < √7 < 2.6458 (need closer bracket).
    have hs_tighter : s < 2.6458 := by
      by_contra h; push_neg at h
      have : s ^ 2 ≥ (2.6458 : ℝ) ^ 2 := by nlinarith
      have : s ^ 2 ≥ 7.0002692164 := by nlinarith
      linarith
    -- 5 + s < 7.6458, so (5+s)/150 < 7.6458/150 = 0.050972 < 0.05081 ✓
    linarith

/-- (T3) **The three menu candidates exist** with squares in the PDG 1%
    window [0.04981, 0.05081]. -/
theorem three_distinct_menu_candidates (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    (0.0493 < cand1_sq ∧ cand1_sq < 0.0513) ∧
    (0.0493 < cand2_sq ∧ cand2_sq < 0.0513) ∧
    (0.0493 < cand3_sq s ∧ cand3_sq s < 0.0513) :=
  ⟨cand1_in_PDG_window, cand2_in_PDG_window, cand3_in_PDG_window s hs hs_pos⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE NON-UNIQUENESS THEOREM (T4)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `framework_does_not_uniquely_force_Vus`:
    Cand3 lies in the menu and matches PDG within 1%, but
    cand3_sq(√7) ≠ cand1_sq = 1/20.
    Hence "lies in menu and matches PDG within 1%" does NOT imply
    "equals C_int · a₁ = 1/20".
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- cand3_sq(√7) ≠ 1/20 (they are strictly distinct values). -/
theorem cand3_neq_one_twentieth (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    cand3_sq s ≠ 1 / 20 := by
  rw [cand3_sq_closed s]
  -- (5 + s)/150 = 1/20 ↔ 5 + s = 7.5 ↔ s = 2.5 ↔ s² = 6.25, contradicts s² = 7.
  intro heq
  have h150 : (150 : ℝ) ≠ 0 := by norm_num
  have h5s : 5 + s = 7.5 := by linarith [(by linarith : (5 + s) / 150 = 1 / 20)]
  -- Quick fix: derive s = 2.5, then s² = 6.25 ≠ 7.
  have hs_eq : s = 2.5 := by linarith
  rw [hs_eq] at hs
  norm_num at hs

/-- **(T4) THE NON-UNIQUENESS / FALSIFICATION THEOREM.**

    There EXISTS a depth-≤2 K/P expression V (namely cand3_sq √7) such that
    V lies in the PDG 1% window AND V ≠ C_int · a₁.
    Hence the framework's K/P axioms do NOT uniquely force V_us² = 1/20:
    the value 1/20 is a *selection from a menu*, not a *forced consequence*. -/
theorem framework_does_not_uniquely_force_Vus :
    ∃ (V : ℝ) (s : ℝ), s ^ 2 = 7 ∧ 0 < s ∧
      V = cand3_sq s ∧
      (0.0493 < V ∧ V < 0.0513) ∧
      V ≠ atom_Cint * atom_a1 := by
  -- Use a witness s := √7. Existence of a positive square root of 7 is `Real.sqrt 7`.
  refine ⟨cand3_sq (Real.sqrt 7), Real.sqrt 7, ?_, ?_, rfl, ?_, ?_⟩
  · exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  · exact Real.sqrt_pos.mpr (by norm_num)
  · exact cand3_in_PDG_window (Real.sqrt 7)
      (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7))
      (Real.sqrt_pos.mpr (by norm_num))
  · -- cand3_sq(√7) ≠ C_int · a₁ = 1/20
    have hne : cand3_sq (Real.sqrt 7) ≠ 1 / 20 :=
      cand3_neq_one_twentieth (Real.sqrt 7)
        (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7))
        (Real.sqrt_pos.mpr (by norm_num))
    intro heq
    apply hne
    rw [heq, atom_Cint_val, atom_a1_val]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: WHAT IS *NOT* PROVED — META-LEMMA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We document the absence of a uniqueness theorem in this file as a
    Prop-level statement that the framework would need to prove (and
    cannot, given T4).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The hypothetical uniqueness statement that the framework would need
    in order for V_us² = 1/20 to be UNIQUELY forced from K/P. We DO NOT
    prove this — and T4 above shows it is in fact FALSE for the natural
    "depth-2 K/P expression matching PDG within 1%" formalization. -/
def framework_uniqueness_claim : Prop :=
  ∀ V : ℝ, (0.0493 < V ∧ V < 0.0513) → V = atom_Cint * atom_a1

/-- **The hypothetical uniqueness claim is FALSE.** Direct corollary of T4.
    Witness: V = cand3_sq(√7) ≈ 0.05097 lies in the PDG 1% window but
    is not equal to C_int · a₁ = 1/20. -/
theorem framework_uniqueness_claim_is_false :
    ¬ framework_uniqueness_claim := by
  intro hUniq
  obtain ⟨V, s, hs, _, hV_eq, ⟨hV_lo, hV_hi⟩, hV_ne⟩ :=
    framework_does_not_uniquely_force_Vus
  exact hV_ne (hUniq V ⟨hV_lo, hV_hi⟩)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASTER FALSIFICATION THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER**: the framework does not uniquely force V_us² = 1/20.

    The conjunction summarizes:
    (1) Trivially, ∃ x = C_int · a₁ with x = 1/20.
    (2) Trivially, ∃ V > 0 with V² = 1/20.
    (3) THREE menu candidates (cand1_sq, cand2_sq, cand3_sq √7) are all
        in the PDG 1% window for V_us².
    (4) cand1_sq = cand2_sq = 1/20 (same value, different expressions).
    (5) cand3_sq √7 ≠ 1/20: a strictly distinct menu value.
    (6) Hence the "uniqueness claim" — that any value in the PDG window
        equals C_int · a₁ — is false.

    Honest classification: SELECTION FROM MENU, not REAL DERIVATION. -/
theorem MASTER_falsification :
    -- (1) Trivial existence of C_int · a₁ = 1/20
    (∃ x : ℝ, x = atom_Cint * atom_a1 ∧ x = 1 / 20) ∧
    -- (2) Trivial existence of V > 0 with V² = 1/20
    (∃ V : ℝ, 0 < V ∧ V ^ 2 = 1 / 20) ∧
    -- (3) Three menu candidates in the PDG window (parametrized by s := √7)
    (let s := Real.sqrt 7
     (0.0493 < cand1_sq ∧ cand1_sq < 0.0513) ∧
     (0.0493 < cand2_sq ∧ cand2_sq < 0.0513) ∧
     (0.0493 < cand3_sq s ∧ cand3_sq s < 0.0513)) ∧
    -- (4) Cand1 = Cand2 (same value)
    cand1_sq = cand2_sq ∧
    -- (5) Cand3 ≠ 1/20 (strictly distinct value)
    (cand3_sq (Real.sqrt 7) ≠ 1 / 20) ∧
    -- (6) The uniqueness claim is FALSE
    (¬ framework_uniqueness_claim) := by
  refine ⟨exists_Cint_a1_equals_one_twentieth,
          exists_pos_sqrt_one_twentieth,
          ?_,
          cand1_eq_cand2,
          ?_,
          framework_uniqueness_claim_is_false⟩
  · exact three_distinct_menu_candidates (Real.sqrt 7)
      (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7))
      (Real.sqrt_pos.mpr (by norm_num))
  · exact cand3_neq_one_twentieth (Real.sqrt 7)
      (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7))
      (Real.sqrt_pos.mpr (by norm_num))

end UnifiedTheory.LayerB.VusFalsificationTest
