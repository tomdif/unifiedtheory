/-
  UnifiedTheory/LayerC/SingletNoGlobalSection.lean
  ─────────────────────────────────────────────────

  **CLOSING THE ANATOMY'S ONE SCHEMATIC EDGE: THE QUANTUM SINGLET HAS NO
  GLOBAL SECTION — STRUCTURALLY, NOT JUST QUANTITATIVELY.**

  In `NoGoAnatomy.lean` the singlet was connected to the global-section
  obstruction only *quantitatively*: `singlet_chsh_abs_gt_two` says the
  singlet's CHSH scalar `BellTheorem.chshValue` satisfies `2 < |chshValue|`,
  and `singlet_exceeds_globalSection_ceiling` notes this exceeds the
  global-section ceiling `2` — but that singlet value lived as a bare real
  number, NOT as a `NoSignallingCorrelation`, so the structural theorem
  `globalSection_chsh_le_two` could not be applied to it.  That file flags
  this honestly:

      "the singlet CHSH is a *single real number* `chshValue` … not a
       four-cell probability table, so the structural hypothesis of
       `globalSection_chsh_le_two` cannot be applied verbatim."

  THIS FILE CLOSES THAT GAP.  We build the singlet's CHSH measurement
  statistics as a genuine `NoSignallingCorrelation` (the four-cell joint
  probability tables `P(a,b|x,y)`), reproducing the singlet correlators

      E(0,0) = E(0,1) = E(1,0) = +1/√2,    E(1,1) = −1/√2

  (the standard CHSH angles for the |Ψ⁻⟩ singlet, `E(x,y) = −cos(θ_x−θ_y)`,
  at the optimal settings).  The local marginals are all `1/2` (the singlet
  is maximally mixed locally), so the no-signalling axioms hold.  Then:

    • `singletCorrelation_chsh`   :  `singletCorrelation.CHSH = 2√2`,
    • `singletCorrelation_chsh_abs`:  `|singletCorrelation.CHSH| = 2√2`,
    • `singlet_no_global_section` :  `¬ HasBipartiteGlobalSection
                                       singletCorrelation`

  the last by the **contrapositive of `globalSection_chsh_le_two`**:
  a global section would force `|CHSH| ≤ 2`, but `|CHSH| = 2√2 > 2`.

  This is the GENUINE STRUCTURAL CONNECTION the anatomy was missing: the
  quantum singlet, packaged as an empirical model, *is* a global-section
  obstruction — the same `¬HasBipartiteGlobalSection` shape as the PR box,
  not merely a number exceeding a ceiling.

  Zero `sorry`.  Zero custom `axiom`.
-/
import UnifiedTheory.LayerC.NoGoAnatomy

namespace UnifiedTheory.LayerC.SingletNoGlobalSection

open UnifiedTheory.LayerC.NoGoAnatomy
open UnifiedTheory.LayerC.PRBox

open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE SINGLET'S CHSH CORRELATORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the singlet |Ψ⁻⟩ with measurement directions at angles `θ_x`, the
    two-party correlator is `E(x, y) = −cos(θ_x − θ_y)`.  The optimal CHSH
    settings (`θ_a = 0, θ_a' = π/2, θ_b = π/4, θ_b' = −π/4`, up to the usual
    conventions) give

        E(0,0) = E(0,1) = E(1,0) = 1/√2,    E(1,1) = −1/√2,

    so that  CHSH = E(0,0) + E(0,1) + E(1,0) − E(1,1) = 4·(1/√2) = 2√2.

    We package this `±1/√2` correlator pattern as `singletE`. -/

/-- The singlet CHSH correlator value at settings `(x, y)`: `+1/√2` for the
    three "aligned" contexts and `−1/√2` for the `(1,1)` context.  This is the
    `E(x,y)` pattern that yields `CHSH = 2√2`. -/
noncomputable def singletE (x y : Fin 2) : ℝ :=
  if x = 1 ∧ y = 1 then -(1 / Real.sqrt 2) else (1 / Real.sqrt 2)

/-- `1/√2 ≤ 1`, so the correlator lies in `[-1, 1]` — needed for the joint
    table `(1 ± E)/4` to be a genuine probability (nonnegative). -/
lemma inv_sqrt_two_le_one : (1 / Real.sqrt 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  -- 1 ≤ √2 since 1 = √1 ≤ √2.
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)

/-- `0 ≤ 1/√2`. -/
lemma inv_sqrt_two_nonneg : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity

/-- The singlet correlator is bounded: `|singletE x y| ≤ 1`. -/
lemma singletE_abs_le_one (x y : Fin 2) : |singletE x y| ≤ 1 := by
  unfold singletE
  split
  · rw [abs_neg, abs_of_nonneg inv_sqrt_two_nonneg]; exact inv_sqrt_two_le_one
  · rw [abs_of_nonneg inv_sqrt_two_nonneg]; exact inv_sqrt_two_le_one

/-- `-1 ≤ singletE x y`. -/
lemma neg_one_le_singletE (x y : Fin 2) : -1 ≤ singletE x y :=
  (abs_le.mp (singletE_abs_le_one x y)).1

/-- `singletE x y ≤ 1`. -/
lemma singletE_le_one (x y : Fin 2) : singletE x y ≤ 1 :=
  (abs_le.mp (singletE_abs_le_one x y)).2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  THE SINGLET JOINT PROBABILITY TABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Given a target correlator `E = singletE x y` with marginals `1/2`, the
    unique symmetric joint table with uniform marginals is

        P(0,0|x,y) = P(1,1|x,y) = (1 + E)/4,
        P(0,1|x,y) = P(1,0|x,y) = (1 − E)/4.

    This reproduces:
      • normalisation:  4 cells sum to (1+E)/4·2 + (1−E)/4·2 = 1;
      • marginals:      ∑_b P(a,b) = (1+E)/4 + (1−E)/4 = 1/2 (every a, x, y),
                        and symmetrically for Bob — so NO-SIGNALLING holds;
      • correlation:    P(0,0)+P(1,1) − P(0,1) − P(1,0)
                        = (1+E)/2 − (1−E)/2 = E.
    Nonnegativity holds because |E| = 1/√2 ≤ 1.
-/

/-- The singlet joint probability table `P(a, b | x, y)`:
    `(1 + E)/4` on the "same-parity" cells `(0,0), (1,1)`, and `(1 − E)/4`
    on the "different-parity" cells `(0,1), (1,0)`, where `E = singletE x y`. -/
noncomputable def singletP (a b x y : Fin 2) : ℝ :=
  if a = b then (1 + singletE x y) / 4 else (1 - singletE x y) / 4

/-- Nonnegativity: `(1 ± E)/4 ≥ 0` since `|E| ≤ 1`. -/
lemma singletP_nonneg (a b x y : Fin 2) : 0 ≤ singletP a b x y := by
  unfold singletP
  split
  · have := singletE_le_one x y; have := neg_one_le_singletE x y; linarith
  · have := singletE_le_one x y; have := neg_one_le_singletE x y; linarith

/-- Normalisation: the four cells sum to 1 for every setting `(x, y)`. -/
lemma singletP_sum_one (x y : Fin 2) :
    (∑ a, ∑ b, singletP a b x y) = 1 := by
  simp only [Fin.sum_univ_two, singletP]
  -- (a=0,b=0): same; (a=0,b=1): diff; (a=1,b=0): diff; (a=1,b=1): same.
  norm_num
  ring

/-- Alice's marginal `∑_b P(a, b | x, y) = 1/2` for every `(a, x, y)` —
    independent of Bob's setting `y` (the singlet is locally maximally
    mixed).  This is the no-signalling Bob → Alice content. -/
lemma singletP_marginal_A (a x y : Fin 2) :
    (∑ b, singletP a b x y) = (1 : ℝ) / 2 := by
  fin_cases a <;>
    simp only [Fin.sum_univ_two, singletP] <;>
    norm_num <;> ring

/-- Bob's marginal `∑_a P(a, b | x, y) = 1/2` for every `(b, x, y)` —
    independent of Alice's setting `x`.  No-signalling Alice → Bob. -/
lemma singletP_marginal_B (b x y : Fin 2) :
    (∑ a, singletP a b x y) = (1 : ℝ) / 2 := by
  fin_cases b <;>
    simp only [Fin.sum_univ_two, singletP] <;>
    norm_num <;> ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  THE SINGLET AS A NO-SIGNALLING CORRELATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE SINGLET'S CHSH STATISTICS AS A NO-SIGNALLING CORRELATION.**

    The four-cell joint probability tables for the singlet measured at the
    optimal CHSH angles.  Both marginals are constantly `1/2`
    (`singletP_marginal_A`, `singletP_marginal_B`), so the two no-signalling
    axioms reduce to `1/2 = 1/2`.  This is the genuine empirical-model
    packaging of the singlet that `NoGoAnatomy.lean` was missing. -/
noncomputable def singletCorrelation : NoSignallingCorrelation where
  P := singletP
  P_nonneg := singletP_nonneg
  P_sum_one := singletP_sum_one
  no_sig_A := by
    intro a x y y'
    rw [singletP_marginal_A a x y, singletP_marginal_A a x y']
  no_sig_B := by
    intro b x x' y
    rw [singletP_marginal_B b x y, singletP_marginal_B b x' y]

/-- The packaged correlation reproduces the singlet correlator `E(x,y)`:
    `singletCorrelation.correlation x y = singletE x y`. -/
lemma singletCorrelation_correlation (x y : Fin 2) :
    singletCorrelation.correlation x y = singletE x y := by
  change singletCorrelation.P 0 0 x y + singletCorrelation.P 1 1 x y
       - singletCorrelation.P 0 1 x y - singletCorrelation.P 1 0 x y
       = singletE x y
  change singletP 0 0 x y + singletP 1 1 x y - singletP 0 1 x y - singletP 1 0 x y
       = singletE x y
  simp only [singletP]
  norm_num
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  THE SINGLET CHSH VALUE IS 2√2
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `4 / √2 = 2√2`.  Algebraic identity used to evaluate the singlet CHSH:
    `4 · (1/√2) = 4/√2 = 2·(2/√2) = 2·√2`.  Proof via `√2·√2 = 2`. -/
lemma four_div_sqrt_two : (4 : ℝ) * (Real.sqrt 2)⁻¹ = 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  -- goal: 4 = 2 * √2 * √2  (or a rearrangement); use √2·√2 = 2.
  nlinarith [h2]

/-- **THE SINGLET'S CHSH VALUE IS EXACTLY `2√2`.**

    `CHSH = E(0,0) + E(0,1) + E(1,0) − E(1,1)`
          ` = 1/√2 + 1/√2 + 1/√2 − (−1/√2) = 4/√2 = 2√2`. -/
theorem singletCorrelation_chsh :
    singletCorrelation.CHSH = 2 * Real.sqrt 2 := by
  change singletCorrelation.correlation 0 0 + singletCorrelation.correlation 0 1
       + singletCorrelation.correlation 1 0 - singletCorrelation.correlation 1 1
       = 2 * Real.sqrt 2
  rw [singletCorrelation_correlation, singletCorrelation_correlation,
      singletCorrelation_correlation, singletCorrelation_correlation]
  -- E(0,0)=E(0,1)=E(1,0)=1/√2 (not (1,1)); E(1,1)=−1/√2.
  simp only [singletE]
  norm_num
  -- goal reduces to (√2)⁻¹ + (√2)⁻¹ + (√2)⁻¹ + (√2)⁻¹ = 2√2.
  rw [show (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹
        + (Real.sqrt 2)⁻¹ = 4 * (Real.sqrt 2)⁻¹ by ring]
  exact four_div_sqrt_two

/-- The singlet CHSH value in absolute value: `|CHSH| = 2√2`. -/
theorem singletCorrelation_chsh_abs :
    |singletCorrelation.CHSH| = 2 * Real.sqrt 2 := by
  rw [singletCorrelation_chsh]
  exact abs_of_nonneg (by positivity)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  THE STRUCTURAL RESULT — NO GLOBAL SECTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE STRUCTURAL RESULT: THE QUANTUM SINGLET HAS NO GLOBAL SECTION.**

    Applying `NoGoAnatomy.globalSection_chsh_le_two` to the genuine
    `NoSignallingCorrelation` packaging of the singlet: a bipartite global
    section would force `|CHSH| ≤ 2`, but the singlet attains
    `|CHSH| = 2√2 > 2` (`singletCorrelation_chsh_abs`, with `2 < 2√2` from
    `PRBox.two_lt_tsirelson`).  Contradiction.

    This UPGRADES `NoGoAnatomy.singlet_chsh_abs_gt_two` — a purely
    *quantitative* statement about a bare scalar `chshValue` — to a genuine
    *structural* `¬HasBipartiteGlobalSection` about the singlet's empirical
    model.  The singlet now sits in the anatomy on exactly the same footing
    as the PR box (`prBox_no_global_section`): it IS a global-section
    obstruction, not merely a number above a ceiling. -/
theorem singlet_no_global_section :
    ¬ HasBipartiteGlobalSection singletCorrelation := by
  intro h
  have hle : |singletCorrelation.CHSH| ≤ 2 := globalSection_chsh_le_two _ h
  rw [singletCorrelation_chsh_abs] at hle
  -- 2√2 ≤ 2 contradicts 2 < 2√2.
  exact absurd hle (by have := two_lt_tsirelson; linarith)

/-- **THE SINGLET IS A NO-SIGNALLING CORRELATION THAT IS GLOBAL-SECTION-FREE.**

    The singlet halves of the anatomy headline, now BOTH structural:
    consistent marginals (`IsNoSignalling` — local maximal mixing) yet no
    global classical joint distribution (`¬HasBipartiteGlobalSection`).  This
    is the singlet's exact analogue of `prBox_noSignalling_no_global_section`,
    so the singlet now participates in the anatomy as a full structural
    witness, not a quantitative footnote. -/
theorem singlet_noSignalling_no_global_section :
    IsNoSignalling singletCorrelation ∧
    ¬ HasBipartiteGlobalSection singletCorrelation :=
  ⟨noSignallingCorrelation_isNoSignalling singletCorrelation,
   singlet_no_global_section⟩

/-- **THE SINGLET ANATOMY, COMPLETE.**

    The full structural picture for the quantum singlet, closing the
    schematic edge flagged in `NoGoAnatomy.lean`:

      (1) the singlet's CHSH statistics ARE a genuine no-signalling
          correlation with `|CHSH| = 2√2`  (`singletCorrelation_chsh_abs`);
      (2) `2√2 > 2`, the global-section ceiling  (`two_lt_tsirelson`);
      (3) therefore the singlet has NO bipartite global section
          (`singlet_no_global_section`) — a structural `¬HasGlobalSection`,
          derived via `globalSection_chsh_le_two`, NOT merely `|CHSH| > 2`;
      (4) yet it remains no-signalling (`IsNoSignalling`): consistent local
          marginals.

    Conclusion: the quantum singlet keeps no-signalling/locality while
    failing global classical definiteness — exactly the anatomy's thesis,
    now PROVED structurally for the singlet itself. -/
theorem singlet_anatomy_complete :
    |singletCorrelation.CHSH| = 2 * Real.sqrt 2
    ∧ (2 : ℝ) < 2 * Real.sqrt 2
    ∧ ¬ HasBipartiteGlobalSection singletCorrelation
    ∧ IsNoSignalling singletCorrelation :=
  ⟨singletCorrelation_chsh_abs,
   two_lt_tsirelson,
   singlet_no_global_section,
   noSignallingCorrelation_isNoSignalling singletCorrelation⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms singletCorrelation_chsh
#print axioms singlet_no_global_section
#print axioms singlet_anatomy_complete

end UnifiedTheory.LayerC.SingletNoGlobalSection
