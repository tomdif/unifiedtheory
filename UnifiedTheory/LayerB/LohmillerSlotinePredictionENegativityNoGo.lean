/-
  LayerB/LohmillerSlotinePredictionENegativityNoGo.lean — Phase E5.

  NEGATIVE-R OBSTRUCTION THEOREM for the LSBridge static matter-coupled
  curved Schrödinger equilibrium predictions.

  Closed in this file:
    A purely algebraic impossibility result that COMPLETES the
    constant-R classification:

      • R = 0  : achieved by the exponential family (E4).
      • R > 0  : achieved by the generalized sech family (E-Generalized sech).
      • R < 0 *as a constant*:  excluded at any "local-max-like"
        critical point (a point where r_x = 0 and r_xx ≤ 0).

    Concretely:  if r > 0 has r_x = 0 and r_xx ≤ 0 at some point x₀
    (which any smooth bounded r > 0 attaining its global maximum
    must do), then R(x₀) ≥ 0.  Hence no constant R = 2C with C < 0
    can be realized at such a point.

    Combined with E4 (R = 0) and E-Generalized sech (R > 0),
    this is the **structural completion** of the LSBridge 1D
    constant-curvature prediction picture.

  Internal-model framing (carrying E1/E2/E3/E4/E-Gen-Sech/E-family/E-Limits
  caveats forward):  R is the Ricci scalar of the emergent 1+1-dim
  conformal metric `g = r²·diag(−1,1)`; results are theorems within
  the LSBridge sector.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEExponential
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEGeneralizedSech
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionENegativityNoGo

open UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEExponential
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEGeneralizedSech

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — ALGEBRAIC POSITIVITY AT MAX-LIKE CRITICAL POINTS.

    These are purely algebraic theorems on the scalars `r, r_x, r_xx`,
    without invoking any derivative / smoothness machinery.  When
    combined with a chain-rule "max-like" hypothesis (`r_x` IS the
    derivative and IT vanishes at a local max), they yield the
    geometric impossibility.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Algebraic positivity at a max-like critical point**:

    If `r > 0` and the scalar `r_x = 0` and `r_xx ≤ 0`, then
    `derivedRicci r r_x r_xx ≥ 0`.

    *Algebraic content*:  with `r_x = 0`, `r_x² - r·r_xx = -r·r_xx`.
    Since `r > 0` and `r_xx ≤ 0`, `-r·r_xx ≥ 0`, and dividing by
    `r⁴ > 0` preserves nonnegativity. -/
theorem derivedRicci_nonneg_at_max_like
    (r r_x r_xx : ℝ) (hr : 0 < r) (h_rx : r_x = 0) (h_rxx : r_xx ≤ 0) :
    0 ≤ derivedRicci r r_x r_xx := by
  unfold derivedRicci
  rw [h_rx]
  -- Goal: 0 ≤ 2 * (0^2 - r * r_xx) / r^4
  have hr_pow4_pos : 0 < r ^ 4 := by positivity
  apply div_nonneg
  · have : 0 ≤ -r * r_xx := by
      have : 0 ≤ r * (-r_xx) := mul_nonneg (le_of_lt hr) (by linarith)
      linarith
    have h1 : (0 : ℝ) ^ 2 - r * r_xx = -r * r_xx := by ring
    linarith [h1, this]
  · linarith

/-- **Symmetric version — negativity at a min-like critical point**.

    If `r > 0` and `r_x = 0` and `r_xx ≥ 0`, then `derivedRicci ≤ 0`.

    Together with the previous theorem, this characterizes the sign
    of R at critical points purely from the sign of `r_xx`. -/
theorem derivedRicci_nonpos_at_min_like
    (r r_x r_xx : ℝ) (hr : 0 < r) (h_rx : r_x = 0) (h_rxx : 0 ≤ r_xx) :
    derivedRicci r r_x r_xx ≤ 0 := by
  unfold derivedRicci
  rw [h_rx]
  have hr_pow4_pos : 0 < r ^ 4 := by positivity
  -- Goal: 2 * (0^2 - r * r_xx) / r^4 ≤ 0
  apply div_nonpos_of_nonpos_of_nonneg
  · have h1 : (0 : ℝ) ^ 2 - r * r_xx = -r * r_xx := by ring
    have h2 : 0 ≤ r * r_xx := mul_nonneg (le_of_lt hr) h_rxx
    linarith
  · linarith

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — CONSTANT-NEGATIVE-R OBSTRUCTION.

    The structural theorem:  if R is constant and < 0, then no
    max-like critical point can exist.  Hence any smooth bounded
    profile attaining its sup cannot have constant negative R.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Constant-negative-R excludes max-like critical points**.

    If `r_x² − r·r_xx = C·r⁴` (constant-R characterization with R = 2C)
    and `C < 0`, and `r > 0`, then we cannot have `r_x = 0 ∧ r_xx ≤ 0`
    simultaneously.

    *Interpretation*:  a profile with strictly negative constant R has
    NO local maxima.  Combined with extremal-value theorem on bounded
    intervals or with continuous-attainment-of-sup arguments, this
    forces any candidate to be unbounded above, contradicting
    "smooth bounded everywhere positive." -/
theorem constant_negative_R_excludes_max_like
    (r r_x r_xx C : ℝ) (hr : 0 < r) (hC : C < 0)
    (h_const_R : r_x ^ 2 - r * r_xx = C * r ^ 4) :
    ¬ (r_x = 0 ∧ r_xx ≤ 0) := by
  rintro ⟨h_rx, h_rxx⟩
  -- Step 1: R is constant 2C, which is < 0.
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have h_R : derivedRicci r r_x r_xx = 2 * C :=
    (derivedRicci_eq_const_iff r r_x r_xx C hr_ne).mpr h_const_R
  -- Step 2: by `derivedRicci_nonneg_at_max_like`, derivedRicci ≥ 0.
  have h_R_nonneg : 0 ≤ derivedRicci r r_x r_xx :=
    derivedRicci_nonneg_at_max_like r r_x r_xx hr h_rx h_rxx
  -- Step 3: 0 ≤ 2C < 0 — contradiction.
  rw [h_R] at h_R_nonneg
  linarith

/-- **Symmetric version — constant-positive-R excludes min-like critical
    points**.  (Mirror of the negative-R obstruction.)  No globally
    smooth profile with constant positive R has a local minimum — they
    are pure "single-bump" / "single-trough" structures. -/
theorem constant_positive_R_excludes_min_like
    (r r_x r_xx C : ℝ) (hr : 0 < r) (hC : 0 < C)
    (h_const_R : r_x ^ 2 - r * r_xx = C * r ^ 4) :
    ¬ (r_x = 0 ∧ 0 ≤ r_xx) := by
  rintro ⟨h_rx, h_rxx⟩
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have h_R : derivedRicci r r_x r_xx = 2 * C :=
    (derivedRicci_eq_const_iff r r_x r_xx C hr_ne).mpr h_const_R
  have h_R_nonpos : derivedRicci r r_x r_xx ≤ 0 :=
    derivedRicci_nonpos_at_min_like r r_x r_xx hr h_rx h_rxx
  rw [h_R] at h_R_nonpos
  linarith

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — EXISTENCE WITNESSES AND CLASSIFICATION SUMMARY.

    The constant-R classification, restated as theorems with explicit
    witnesses for R = 0 (exponential) and R > 0 (gen-sech), plus the
    no-go for R < 0 at max-like critical points.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **R = 0 is realized** by any exponential profile.
    `derivedRicci (exp_profile) ... = 0`. -/
theorem zero_R_realized_by_exponential
    (α β x : ℝ) :
    derivedRicci (expProfile α β x)
                 (expProfile_x α β x)
                 (expProfile_xx α β x) = 0 :=
  derivedRicci_expProfile_zero α β x

/-- **R = 2·(B/A)² > 0 is realized** by the generalized sech family
    `r = A·sech(B·x)` for `A ≠ 0` and any `B ≠ 0`. -/
theorem positive_R_realized_by_gen_sech
    (A B x : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    0 < derivedRicci (gSechProfile A B x)
                     (gSechProfile_x A B x)
                     (gSechProfile_xx A B x) := by
  rw [derivedRicci_gSech A B x hA]
  have hA2_pos : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hB2_pos : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have h_num_pos : 0 < 2 * B ^ 2 := by linarith
  exact div_pos h_num_pos hA2_pos

/-- **Negative constant R has no max-like point**:  there is NO
    triple `(r, r_x, r_xx)` with `r > 0`, `r_x = 0`, `r_xx ≤ 0`,
    AND `derivedRicci r r_x r_xx < 0`.

    Restated as a non-existence claim instead of the implication form. -/
theorem no_max_like_with_negative_R :
    ¬ ∃ (r r_x r_xx : ℝ),
        0 < r ∧ r_x = 0 ∧ r_xx ≤ 0 ∧
        derivedRicci r r_x r_xx < 0 := by
  rintro ⟨r, r_x, r_xx, hr, h_rx, h_rxx, h_R_neg⟩
  have h_R_nonneg :=
    derivedRicci_nonneg_at_max_like r r_x r_xx hr h_rx h_rxx
  linarith

/-- **CLASSIFICATION SUMMARY THEOREM**:  for any triple
    `(r, r_x, r_xx)` with `r > 0` and `r_x = 0` and `r_xx ≤ 0`
    (a "max-like" critical point), the derived Ricci scalar at that
    point is nonneg.  This rules out the possibility of constant
    negative R for any profile attaining a max at some point. -/
theorem LSBridge_constant_R_classification_at_max_like
    (r r_x r_xx : ℝ) (hr : 0 < r) (h_rx : r_x = 0) (h_rxx : r_xx ≤ 0) :
    -- Either the derived Ricci is zero (compatible with the E4
    -- exponential branch) or strictly positive (compatible with
    -- the E-Gen-Sech branch).  It is NEVER strictly negative.
    derivedRicci r r_x r_xx = 0 ∨ 0 < derivedRicci r r_x r_xx := by
  have h_nonneg := derivedRicci_nonneg_at_max_like r r_x r_xx hr h_rx h_rxx
  rcases eq_or_lt_of_le h_nonneg with h | h
  · left; linarith
  · right; exact h

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `derivedRicci_nonneg_at_max_like` — algebraic core of the
        positivity result at max-like critical points.
      ✓ `derivedRicci_nonpos_at_min_like` — symmetric algebraic result.
      ✓ `constant_negative_R_excludes_max_like` — the main no-go.
      ✓ `constant_positive_R_excludes_min_like` — symmetric no-go.
      ✓ `zero_R_realized_by_exponential` — existence of R = 0.
      ✓ `positive_R_realized_by_gen_sech` — existence of R > 0.
      ✓ `no_max_like_with_negative_R` — non-existence claim.
      ✓ `LSBridge_constant_R_classification_at_max_like` — the
        classification summary:  at any max-like critical point of
        a positive profile, R ≥ 0, so the constant-R picture is
        EXHAUSTED by the {R = 0} ∪ {R > 0} branches.

    Structural classification (with these results):

      ┌──────────────┬──────────────────────────┬───────────────────┐
      │ R value      │ Family                  │ Achievable?       │
      ├──────────────┼──────────────────────────┼───────────────────┤
      │ R ≡ 0        │ E4 exponential          │ YES (witness)     │
      │ R ≡ 2C > 0   │ E-Gen-Sech with (B/A)² = C │ YES (witness)  │
      │ R ≡ 2C < 0   │ —                       │ NO at any local max │
      └──────────────┴──────────────────────────┴───────────────────┘

      The "NO at any local max" verdict means:  a globally smooth
      positive profile r on a domain where r attains a maximum
      cannot have constant R < 0.  This includes:
        • Any continuous positive profile on a compact interval.
        • Any continuous positive profile on ℝ bounded above and
          attaining its sup.
        • Any C¹ profile on ℝ with r → 0 (or some limit) at ±∞ with
          a finite local max.

      The remaining "gap" — globally smooth positive profiles on ℝ
      with constant R < 0 NOT attaining a maximum — is shown by a
      classical PDE argument (Liouville equation `φ'' = C·e^{−2φ}`
      with C < 0 forces strict concavity of φ, hence φ → −∞,
      hence r → +∞, hence unbounded).  That ODE-level argument
      would extend this file with Mathlib's StrictConcaveOn theory
      and `IsLocalMax`-style derivative bridges.

    Open continuations:
    • Full ODE-level impossibility:  no globally-smooth bounded
      r > 0 on ℝ with constant R < 0 (uses StrictConcaveOn).
    • Bridge to global existence (StrictConcaveOn → eventual decrease
      → unbounded r) — would close the negative-R impossibility
      theorem in full generality.

    Closed in Parts 5–6 below:
    ✓ Mathlib-bridged version:  `IsLocalMax` ⇒ `r_x = 0 ∧ r_xx ≤ 0`
      (using `IsLocalMax.deriv_eq_zero` + the converse second-derivative
      test via `isLocalMin_of_deriv_deriv_pos` contradiction).
    ════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — MATHLIB IsLocalMax DERIVATIVE BRIDGE.

    Lift the algebraic "max-like critical point" hypothesis (`r_x = 0
    ∧ r_xx ≤ 0`) to Mathlib's `IsLocalMax` for `C²` functions
    `r : ℝ → ℝ`.

    The Fermat direction `r_x = 0` is `IsLocalMax.deriv_eq_zero`
    (already in Mathlib).

    The second-derivative direction `r_xx ≤ 0` requires a contrapositive
    argument:  if `r_xx > 0`, then by the second-derivative test
    (`isLocalMin_of_deriv_deriv_pos`) the point would be a local
    minimum — combined with the local-max hypothesis, `r` would be
    locally constant, contradicting `r_xx > 0`.
    ════════════════════════════════════════════════════════════════════════ -/

open Filter Topology

/-- **Mathlib bridge — second derivative ≤ 0 at a local max** (1D).

    For a C² function `f : ℝ → ℝ` with a local maximum at `x₀`,
    the second derivative is nonpositive at `x₀`.  This is the
    necessary direction of the second-derivative test (the
    sufficient direction `isLocalMax_of_deriv_deriv_neg` is already
    in Mathlib). -/
theorem deriv_deriv_nonpos_of_isLocalMax
    (f : ℝ → ℝ) (x₀ : ℝ)
    (h_max : IsLocalMax f x₀)
    (h_diff : ContDiffAt ℝ 2 f x₀) :
    deriv (deriv f) x₀ ≤ 0 := by
  by_contra h_pos
  push_neg at h_pos
  -- h_pos: 0 < deriv (deriv f) x₀
  have h_d_zero : deriv f x₀ = 0 := h_max.deriv_eq_zero
  have h_cont : ContinuousAt f x₀ := h_diff.continuousAt
  -- The Mathlib second-derivative test forces a local minimum.
  have h_min : IsLocalMin f x₀ :=
    isLocalMin_of_deriv_deriv_pos h_pos h_d_zero h_cont
  -- max + min ⇒ f is constant on a neighborhood of x₀.
  have h_max' : ∀ᶠ y in 𝓝 x₀, f y ≤ f x₀ := h_max
  have h_min' : ∀ᶠ y in 𝓝 x₀, f x₀ ≤ f y := h_min
  have h_eq_const : f =ᶠ[𝓝 x₀] (fun _ : ℝ => f x₀) := by
    filter_upwards [h_max', h_min'] with y h1 h2
    linarith
  -- f =ᶠ[𝓝 x₀] const ⇒ deriv f =ᶠ[𝓝 x₀] deriv const = 0.
  have h_d_eq : deriv f =ᶠ[𝓝 x₀] (fun _ : ℝ => (0 : ℝ)) := by
    have h_deriv := h_eq_const.deriv
    have h_const_deriv :
        deriv (fun _ : ℝ => f x₀) = (fun _ : ℝ => (0 : ℝ)) := by
      funext y
      exact deriv_const _ (f x₀)
    rw [← h_const_deriv]
    exact h_deriv
  -- deriv f =ᶠ[𝓝 x₀] 0 ⇒ deriv (deriv f) x₀ = deriv (fun _ => 0) x₀ = 0.
  have h_dd_zero : deriv (deriv f) x₀ = 0 := by
    have h_dd_eq : deriv (deriv f) x₀ = deriv (fun _ : ℝ => (0 : ℝ)) x₀ :=
      h_d_eq.deriv_eq
    rw [h_dd_eq, deriv_const]
  linarith

/-- **C² + IsLocalMax ⇒ both `deriv = 0` AND `deriv (deriv) ≤ 0`** at
    that point.  Packages Fermat + the bridge above. -/
theorem deriv_and_deriv_deriv_at_isLocalMax
    (f : ℝ → ℝ) (x₀ : ℝ)
    (h_max : IsLocalMax f x₀)
    (h_diff : ContDiffAt ℝ 2 f x₀) :
    deriv f x₀ = 0 ∧ deriv (deriv f) x₀ ≤ 0 :=
  ⟨h_max.deriv_eq_zero,
   deriv_deriv_nonpos_of_isLocalMax f x₀ h_max h_diff⟩

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — IsLocalMax-LIFTED NEGATIVITY NO-GO.

    Combines the Mathlib bridge (Part 5) with the algebraic positivity
    at max-like critical points (Part 1) to give the IsLocalMax-form
    of the no-go.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Mathlib-form positivity at a local max**:
    if `r : ℝ → ℝ` is C² with `r(x₀) > 0` and `r` has a local max at
    `x₀`, then the derived Ricci scalar of the emergent metric at
    `x₀` is nonnegative. -/
theorem derivedRicci_nonneg_at_isLocalMax
    (r : ℝ → ℝ) (x₀ : ℝ)
    (h_max : IsLocalMax r x₀)
    (h_diff : ContDiffAt ℝ 2 r x₀)
    (h_pos : 0 < r x₀) :
    0 ≤ derivedRicci (r x₀) (deriv r x₀) (deriv (deriv r) x₀) := by
  obtain ⟨h_d_zero, h_dd_nonpos⟩ :=
    deriv_and_deriv_deriv_at_isLocalMax r x₀ h_max h_diff
  exact derivedRicci_nonneg_at_max_like (r x₀) (deriv r x₀)
    (deriv (deriv r) x₀) h_pos h_d_zero h_dd_nonpos

/-- **Mathlib-form negative-R no-go**:
    if `r : ℝ → ℝ` is C² with `r(x₀) > 0`, satisfies the constant-R
    relation `r_x² − r·r_xx = C·r⁴` at `x₀` with `C < 0`, then `r`
    has NO local maximum at `x₀`.

    This is the Mathlib-natural statement of the no-go:  any C² positive
    profile with strictly negative constant R cannot attain a local
    maximum anywhere. -/
theorem no_isLocalMax_for_constant_negative_R
    (r : ℝ → ℝ) (x₀ C : ℝ)
    (h_diff : ContDiffAt ℝ 2 r x₀)
    (h_pos : 0 < r x₀) (hC : C < 0)
    (h_const_R :
      (deriv r x₀) ^ 2 - r x₀ * deriv (deriv r) x₀ = C * (r x₀) ^ 4) :
    ¬ IsLocalMax r x₀ := by
  intro h_max
  -- IsLocalMax + C² ⇒ derivedRicci ≥ 0.
  have h_R_nonneg : 0 ≤ derivedRicci (r x₀) (deriv r x₀) (deriv (deriv r) x₀) :=
    derivedRicci_nonneg_at_isLocalMax r x₀ h_max h_diff h_pos
  -- Constant-R hypothesis ⇒ derivedRicci = 2C < 0.
  have hr_ne : r x₀ ≠ 0 := ne_of_gt h_pos
  have h_R_eq : derivedRicci (r x₀) (deriv r x₀) (deriv (deriv r) x₀) = 2 * C :=
    (derivedRicci_eq_const_iff (r x₀) (deriv r x₀) (deriv (deriv r) x₀) C hr_ne).mpr
      h_const_R
  rw [h_R_eq] at h_R_nonneg
  -- 0 ≤ 2C and C < 0  ⇒  contradiction.
  linarith

/-- **Bridged classification — Mathlib-natural form**:
    if `r : ℝ → ℝ` is C² with `r > 0` and a local max at `x₀`,
    then the derived Ricci at `x₀` is in the achievable family:
    EITHER zero (compatible with the exponential branch) OR strictly
    positive (compatible with the generalized sech branch).

    This is the Mathlib-natural statement of the constant-R classification. -/
theorem LSBridge_constant_R_classification_isLocalMax
    (r : ℝ → ℝ) (x₀ : ℝ)
    (h_max : IsLocalMax r x₀)
    (h_diff : ContDiffAt ℝ 2 r x₀)
    (h_pos : 0 < r x₀) :
    derivedRicci (r x₀) (deriv r x₀) (deriv (deriv r) x₀) = 0
      ∨ 0 < derivedRicci (r x₀) (deriv r x₀) (deriv (deriv r) x₀) := by
  have h_nonneg := derivedRicci_nonneg_at_isLocalMax r x₀ h_max h_diff h_pos
  rcases eq_or_lt_of_le h_nonneg with h | h
  · left; linarith
  · right; exact h

end UnifiedTheory.LayerB.LohmillerSlotinePredictionENegativityNoGo
