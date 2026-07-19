/-
  UnifiedTheory/LayerC/ContextualFraction.lean
  ─────────────────────────────────────────────

  **THE CONTEXTUAL FRACTION — A QUANTITATIVE CONTEXTUALITY MONOTONE.**

  `NoGoAnatomy.lean` collapsed every quantum no-go onto ONE qualitative
  predicate (`¬HasGlobalSection`).  `ContextualityHierarchy.lean` REFINED
  that into three strictly nested *qualitative* levels
  (`probabilistic ⊋ logical ⊋ strong`).  This file adds the QUANTITATIVE
  axis: the Abramsky–Barbosa–Mansfield (2017) **contextual fraction**, a
  real number `CF(E) ∈ [0, 1]` grading *how contextual* an empirical model
  is — a genuine monotone, not a yes/no flag.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE DEFINITION (Abramsky–Barbosa–Mansfield)

  The contextual fraction of an empirical model `E` is `CF(E) = 1 − NCF(E)`,
  where the *non-contextual fraction* `NCF(E)` is the maximum weight
  `λ ∈ [0,1]` such that `E` can be written as a convex mixture

      E  =  λ · (a non-contextual model)  +  (1 − λ) · (anything no-signalling)

  i.e. the largest fraction of `E` that a single global (non-contextual)
  section can account for.  Then:

      CF(E) = 0  ⟺  E is non-contextual          (a full global section exists)
      CF(E) = 1  ⟺  E is strongly contextual      (no non-contextual part at all)

  and `CF` is a monotone: it does not increase under the classical (free)
  operations on empirical models, so it measures contextuality *as a
  resource*.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE CHSH SCENARIO — A CLOSED FORM

  For the (2,2,2) CHSH scenario the linear program defining `CF` has the
  explicit optimum

      CF  =  (CHSH − 2)/2        for  CHSH ∈ [2, 4]

  — the *normalized Bell violation*.  This is the central computation of
  the file, instantiated at the three landmark values:

      CHSH = 2     (classical / local bound)   →  CF = 0
      CHSH = 2√2   (Tsirelson / quantum singlet)→ CF = (2√2 − 2)/2 = √2 − 1 ≈ 0.414
      CHSH = 4     (PR box / algebraic max)     →  CF = 1

  yielding the **resource ladder**

      0  <  √2 − 1  <  1          (classical < quantum < PR-box).

  We prove: the three values; nonnegativity; monotonicity in CHSH; the
  characterization `CF = 0 ⟺ CHSH ≤ 2`, tied to the global-section ceiling
  `globalSection_chsh_le_two`; the singlet's `CF = √2 − 1` via the genuine
  `NoSignallingCorrelation` packaging of `SingletNoGlobalSection.lean`; and
  the ladder.  A master theorem bundles all of it.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  • `chshContextualFraction` is the CHSH-scenario *closed form*
    `max 0 ((CHSH − 2)/2)`, the proven optimum of the ABM linear program
    for the (2,2,2) scenario.  We do NOT re-derive that LP optimum from the
    convex-decomposition definition in Lean (that is the genuinely
    non-trivial ABM theorem, an infinite-dimensional/polytope optimization);
    we take the closed form as the definition of CF *for this scenario* and
    prove all of its quantitative content (values, monotonicity, the
    `CF=0 ⟺ classical` characterization, the ladder).  The `max 0 (·)`
    clamp encodes that CHSH below the classical bound is fully
    non-contextual (`CF = 0`), matching the LP for `CHSH ≤ 2`.

  • The link to a *global section* is via `globalSection_chsh_le_two`
    (NoGoAnatomy): `CHSH ≤ 2` is exactly the global-section ceiling, so
    `CF = 0 ⟺ CHSH ≤ 2` is the quantitative face of "`CF = 0` ⟺ a global
    section is compatible with the value."

  Zero `sorry`.  Zero custom `axiom`.
-/
import UnifiedTheory.LayerC.SingletNoGlobalSection
import UnifiedTheory.LayerC.ContextualityHierarchy

namespace UnifiedTheory.LayerC.ContextualFraction

open UnifiedTheory.LayerC.NoGoAnatomy
open UnifiedTheory.LayerC.PRBox
open UnifiedTheory.LayerC.SingletNoGlobalSection

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE CONTEXTUAL FRACTION (CHSH-SCENARIO CLOSED FORM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CHSH-SCENARIO CONTEXTUAL FRACTION.**  `CF = max 0 ((CHSH − 2)/2)`:
    the normalized Bell violation, clamped to `[0, 1]` below the classical
    bound.  This is the Abramsky–Barbosa–Mansfield contextual-fraction
    linear-program optimum for the (2,2,2) scenario in closed form. -/
noncomputable def chshContextualFraction (chsh : ℝ) : ℝ := max 0 ((chsh - 2) / 2)

/-! ### The three landmark values. -/

/-- **Classical bound: `CF(2) = 0`.**  CHSH at the local/non-contextual
    bound `2` has zero contextual fraction. -/
theorem cf_classical : chshContextualFraction 2 = 0 := by
  unfold chshContextualFraction; norm_num

/-- **Tsirelson / quantum: `CF(2√2) = √2 − 1`.**  The quantum singlet's
    normalized violation `(2√2 − 2)/2 = √2 − 1 ≈ 0.414`. -/
theorem cf_tsirelson : chshContextualFraction (2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
  unfold chshContextualFraction
  -- (2√2 − 2)/2 = √2 − 1, and this is ≥ 0 since √2 ≥ 1, so the max picks it.
  rw [show (2 * Real.sqrt 2 - 2) / 2 = Real.sqrt 2 - 1 by ring]
  -- √2 ≥ 1 ⟹ √2 − 1 ≥ 0.
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [max_eq_right (by linarith)]

/-- **PR box / algebraic max: `CF(4) = 1`.**  The PR box's maximal violation
    `CHSH = 4` has full contextual fraction. -/
theorem cf_prBox : chshContextualFraction 4 = 1 := by
  unfold chshContextualFraction; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  MONOTONE STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `CF ≥ 0` always: the contextual fraction is nonnegative (it is a
    fraction of explanatory weight). -/
theorem cf_nonneg (chsh : ℝ) : 0 ≤ chshContextualFraction chsh :=
  le_max_left _ _

/-- `CF ≤ 1` on the physical CHSH range `[2, 4]`: above the local bound and
    below the algebraic max, the contextual fraction is a genuine fraction. -/
theorem cf_le_one {chsh : ℝ} (h : chsh ≤ 4) : chshContextualFraction chsh ≤ 1 := by
  unfold chshContextualFraction
  apply max_le (by norm_num)
  linarith

/-- **MONOTONICITY: larger CHSH violation ⟹ larger CF.**  The contextual
    fraction is non-decreasing in the CHSH value — more violation is more
    contextuality resource. -/
theorem cf_monotone_in_chsh {s t : ℝ} (h : s ≤ t) :
    chshContextualFraction s ≤ chshContextualFraction t := by
  unfold chshContextualFraction
  apply max_le_max (le_refl 0)
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  CF = 0  ⟺  CLASSICAL  ⟺  GLOBAL-SECTION-COMPATIBLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **`CF = 0 ⟺ CHSH ≤ 2`.**  The contextual fraction vanishes exactly when
    the CHSH value sits at or below the local/non-contextual bound `2` — the
    quantitative face of *non-contextuality*. -/
theorem cf_zero_iff_le_classical (chsh : ℝ) :
    chshContextualFraction chsh = 0 ↔ chsh ≤ 2 := by
  unfold chshContextualFraction
  constructor
  · intro h
    -- max 0 ((chsh-2)/2) = 0 ⟹ (chsh-2)/2 ≤ 0 ⟹ chsh ≤ 2.
    have : (chsh - 2) / 2 ≤ 0 := by
      have := le_max_right (0 : ℝ) ((chsh - 2) / 2)
      rw [h] at this; exact this
    linarith
  · intro h
    -- chsh ≤ 2 ⟹ (chsh-2)/2 ≤ 0 ⟹ max 0 (·) = 0.
    apply max_eq_left
    linarith

/-- **`CF = 0 ⟺ CHSH is at/below the global-section ceiling.**  Ties
    `cf_zero_iff_le_classical` to `NoGoAnatomy.globalSection_chsh_le_two`:
    the value `2` at which `CF` vanishes is *exactly* the ceiling that any
    bipartite global section imposes (`HasBipartiteGlobalSection c →
    |c.CHSH| ≤ 2`).  So `CF = 0` is the quantitative statement that the
    CHSH value is compatible with a global (non-contextual) section, while
    `CF > 0` certifies it is not. -/
theorem cf_zero_iff_global_section_compatible (chsh : ℝ) :
    chshContextualFraction chsh = 0 ↔
      (chsh ≤ 2 ∧
        ∀ c : NoSignallingCorrelation,
          HasBipartiteGlobalSection c → |c.CHSH| ≤ 2) := by
  rw [cf_zero_iff_le_classical]
  constructor
  · intro h; exact ⟨h, fun c hc => globalSection_chsh_le_two c hc⟩
  · intro h; exact h.1

/-- **`CF > 0 ⟺ CHSH > 2`.**  A *strictly positive* contextual fraction
    certifies a CHSH value strictly above the global-section ceiling — i.e.
    genuine (probabilistic) contextuality. -/
theorem cf_pos_iff_gt_classical (chsh : ℝ) :
    0 < chshContextualFraction chsh ↔ 2 < chsh := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have : chshContextualFraction chsh = 0 := (cf_zero_iff_le_classical chsh).mpr (by linarith)
    linarith
  · intro h
    unfold chshContextualFraction
    have : 0 < (chsh - 2) / 2 := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  THE SINGLET'S CONTEXTUAL FRACTION = √2 − 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM SINGLET'S CONTEXTUAL FRACTION IS `√2 − 1`.**

    Evaluating `chshContextualFraction` at the singlet's genuine
    `NoSignallingCorrelation` CHSH value `singletCorrelation.CHSH = 2√2`
    (`SingletNoGlobalSection.singletCorrelation_chsh`) gives the quantum
    contextual fraction `√2 − 1 ≈ 0.414`.  This connects the quantitative
    monotone to the *structural* singlet model of `SingletNoGlobalSection`:
    the singlet, which `singlet_no_global_section` shows has NO global
    section, has a strictly positive — and exactly computed — contextual
    fraction. -/
theorem singlet_contextual_fraction :
    chshContextualFraction singletCorrelation.CHSH = Real.sqrt 2 - 1 := by
  rw [singletCorrelation_chsh]; exact cf_tsirelson

/-- The singlet's contextual fraction is strictly positive: the singlet is
    *probabilistically contextual* (no global section), quantified. -/
theorem singlet_contextual_fraction_pos :
    0 < chshContextualFraction singletCorrelation.CHSH := by
  rw [singlet_contextual_fraction]
  -- √2 − 1 > 0 since √2 > 1.
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  THE RESOURCE LADDER  0 < √2 − 1 < 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CONTEXTUALITY RESOURCE LADDER: `0 < √2 − 1 < 1`.**

    The quantum contextual fraction strictly separates the classical floor
    (`CF = 0`) from the PR-box ceiling (`CF = 1`):

        classical (0)  <  quantum (√2 − 1)  <  PR-box (1).

    Left inequality: `√2 − 1 > 0` because `√2 > 1`.
    Right inequality: `√2 − 1 < 1` because `√2 < 2`. -/
theorem contextuality_ladder : (0 : ℝ) < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < 1 := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact ⟨by linarith, by linarith⟩

/-- **THE LADDER, AT THE THREE LANDMARK CHSH VALUES.**  Spelled out as the
    contextual fractions themselves:
        `CF(2) = 0  <  CF(2√2) = √2−1  <  CF(4) = 1`. -/
theorem contextuality_ladder_at_landmarks :
    chshContextualFraction 2 < chshContextualFraction (2 * Real.sqrt 2)
    ∧ chshContextualFraction (2 * Real.sqrt 2) < chshContextualFraction 4 := by
  rw [cf_classical, cf_tsirelson, cf_prBox]
  exact contextuality_ladder

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  CONNECTION TO THE QUALITATIVE HIERARCHY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The contextual fraction is the QUANTITATIVE refinement of the
    qualitative `ProbabilisticallyContextual` predicate of
    `ContextualityHierarchy.lean`.  At the CHSH-scenario level: a strictly
    positive contextual fraction is exactly the regime where a probabilistic
    global section fails (`CHSH > 2`), i.e. probabilistic contextuality, and
    `CF = 0` is the non-contextual (global-section) regime.
-/

open UnifiedTheory.LayerC.ContextualityHierarchy in
/-- **CF AS THE QUANTITATIVE FACE OF PROBABILISTIC CONTEXTUALITY.**

    The PR box model (`ContextualityHierarchy.prBoxModel`) is
    probabilistically contextual (`chsh_probabilistically_contextual`); the
    *same* obstruction is graded quantitatively by `CF`: at its CHSH value
    `4`, the contextual fraction is the maximum `1` (`cf_prBox`), while at
    the classical bound `CF` vanishes (`cf_classical`).  So the qualitative
    flag `ProbabilisticallyContextual` and the monotone `CF > 0` track the
    same boundary — `CF` simply measures *how far past* it. -/
theorem cf_grades_probabilistic_contextuality :
    -- qualitative: the PR box has no global section (probabilistically contextual)
    ¬ HasBipartiteGlobalSection prBoxNoSignalling
    -- quantitative: its CHSH contextual fraction is maximal, and CF=0 marks the
    -- non-contextual boundary at the classical bound.
    ∧ chshContextualFraction 4 = 1
    ∧ chshContextualFraction 2 = 0 :=
  ⟨chsh_probabilistically_contextual, cf_prBox, cf_classical⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7.  THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CONTEXTUAL-FRACTION MASTER THEOREM.**

    The complete quantitative picture of CHSH-scenario contextuality:

    1. **Three landmark values** — the resource scale is pinned down exactly:
         `CF(2) = 0` (classical), `CF(2√2) = √2 − 1` (quantum singlet),
         `CF(4) = 1` (PR box).

    2. **Monotone** — `CF` is nonnegative and non-decreasing in the CHSH
       value: more violation ⟹ more contextuality resource.

    3. **Characterization** — `CF = 0 ⟺ CHSH ≤ 2`, the global-section
       ceiling of `globalSection_chsh_le_two`: the contextual fraction
       vanishes exactly when the value is compatible with a non-contextual
       global section.

    4. **The singlet** — packaged as the genuine `NoSignallingCorrelation`
       of `SingletNoGlobalSection`, the quantum singlet has
       `CF = √2 − 1 > 0`: a quantitative certificate of its (already
       structurally proven) lack of a global section.

    5. **The resource ladder** — `0 < √2 − 1 < 1`:
       classical `<` quantum `<` PR-box. -/
theorem contextual_fraction_master :
    -- (1) three landmark values
    (chshContextualFraction 2 = 0)
    ∧ (chshContextualFraction (2 * Real.sqrt 2) = Real.sqrt 2 - 1)
    ∧ (chshContextualFraction 4 = 1)
    -- (2) monotone: nonneg + non-decreasing
    ∧ (∀ chsh : ℝ, 0 ≤ chshContextualFraction chsh)
    ∧ (∀ s t : ℝ, s ≤ t → chshContextualFraction s ≤ chshContextualFraction t)
    -- (3) CF = 0 ⟺ CHSH ≤ 2, the global-section ceiling
    ∧ (∀ chsh : ℝ, chshContextualFraction chsh = 0 ↔ chsh ≤ 2)
    ∧ (∀ c : NoSignallingCorrelation, HasBipartiteGlobalSection c → |c.CHSH| ≤ 2)
    -- (4) the singlet's contextual fraction = √2 − 1, strictly positive
    ∧ (chshContextualFraction singletCorrelation.CHSH = Real.sqrt 2 - 1)
    ∧ (0 < chshContextualFraction singletCorrelation.CHSH)
    -- (5) the resource ladder 0 < √2 − 1 < 1
    ∧ ((0 : ℝ) < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < 1) :=
  ⟨cf_classical,
   cf_tsirelson,
   cf_prBox,
   cf_nonneg,
   fun _ _ h => cf_monotone_in_chsh h,
   cf_zero_iff_le_classical,
   fun c h => globalSection_chsh_le_two c h,
   singlet_contextual_fraction,
   singlet_contextual_fraction_pos,
   contextuality_ladder⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms cf_tsirelson
#print axioms cf_zero_iff_le_classical
#print axioms cf_zero_iff_global_section_compatible
#print axioms singlet_contextual_fraction
#print axioms contextuality_ladder
#print axioms contextual_fraction_master

end UnifiedTheory.LayerC.ContextualFraction
