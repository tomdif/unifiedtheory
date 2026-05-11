/-
  LayerB/TsirelsonBound.lean — The quantum (Tsirelson) bound |S| ≤ 2√2
  for the framework's singlet correlations.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/BellTheorem.lean` derived the singlet correlation function
      E(θ_a, θ_b) = -cos(θ_a - θ_b)
  from the Born rule applied to the framework's singlet state, and
  computed `chshValue = -4·cos(π/4) = -2√2` at the optimal angles
  (θ_a, θ_a', θ_b, θ_b') = (0, π/2, π/4, -π/4), giving S² = 8.

  `LayerB/SeparableCHSH.lean` proved the *classical* CHSH bound
  |S| ≤ 2 for any factorizable correlation e(a, b) = f(a)·g(b)
  with |f|, |g| ≤ 1.

  This file proves the *quantum* CHSH bound (Tsirelson's bound)
  for the framework's specific singlet correlation function:

      For ANY four angles (θ_a, θ_a', θ_b, θ_b'), the CHSH expression
        S = E(a,b) + E(a,b') + E(a',b) - E(a',b')
      with E(θ, φ) = -cos(θ - φ) satisfies |S| ≤ 2√2.

  Combined with `BellTheorem.tsirelson_value` (which gives S² = 8 at
  the optimal angles, i.e. |S| = 2√2), we obtain saturation: the
  optimal singlet correlation EXACTLY achieves the Tsirelson bound.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `abs_cos_add_abs_sin_le_sqrt_two`: |cos β| + |sin β| ≤ √2
    (the load-bearing trig lemma; proved via Cauchy–Schwarz applied
    to (|cos β|, |sin β|) and (1, 1) using the Pythagorean identity)
  – `tsirelsonChshSinglet`: the CHSH expression for the singlet
    correlation E(θ, φ) = -cos(θ - φ) at any four angles
  – `tsirelson_bound`: |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2·√2
    for all real angles
  – `singlet_saturates_tsirelson`:
        tsirelsonChshSinglet 0 (π/2) (π/4) (-(π/4)) = -2·√2
    (the framework's singlet at the optimal angles ATTAINS the bound)
  – `singlet_value_eq_chshValue`: the same value equals
    `BellTheorem.chshValue`, linking the new theorem to the existing
    Bell-violation chain.
  – `tsirelson_master_theorem`: the full Bell trichotomy in one place:
        (a) classical bound: |S| ≤ 2 for factorizable correlations
        (b) Tsirelson bound: |S| ≤ 2√2 for singlet correlations
        (c) saturation: singlet at optimal angles equals -2√2

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – This is the trigonometric Tsirelson bound for the SPECIFIC singlet
    correlation function E(θ, φ) = -cos(θ - φ) derived in BellTheorem.
    The full operator-theoretic Tsirelson bound (Tsirelson 1980) holds
    for ANY pair of bounded self-adjoint operators with |A|, |A'|, |B|,
    |B'| ≤ 1, not just rotated spin-1/2 measurements; that statement
    requires C*-algebraic structure beyond the scope of this file.
  – The trig version IS what is actually computed in BellTheorem and
    what governs the framework's concrete spin-1/2 singlet predictions.
  – Real angles only (matching BellTheorem's real-amplitude setup).

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.BellTheorem
import UnifiedTheory.LayerB.SeparableCHSH
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TsirelsonBound

open Real
open UnifiedTheory.LayerB.BellTheorem
open UnifiedTheory.LayerB.SeparableCHSH

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE LOAD-BEARING TRIGONOMETRIC LEMMA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Cauchy–Schwarz for two reals**: for any x, y ≥ 0,
    (x + y)² ≤ 2·(x² + y²).  Equivalently, x + y ≤ √(2(x²+y²)).
    The proof is just expansion + (x − y)² ≥ 0. -/
lemma sq_add_le_two_mul_sq_add (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

/-- **Trigonometric Cauchy–Schwarz**: for any β ∈ ℝ,
        |cos β| + |sin β| ≤ √2.

    Proof: by `sq_add_le_two_mul_sq_add` applied to (|cos β|, |sin β|),
    we have (|cos β| + |sin β|)² ≤ 2·(cos²β + sin²β) = 2.  Take square
    roots; both sides are nonnegative. -/
lemma abs_cos_add_abs_sin_le_sqrt_two (β : ℝ) :
    |cos β| + |sin β| ≤ Real.sqrt 2 := by
  set c := |cos β|
  set s := |sin β|
  have hc : 0 ≤ c := abs_nonneg _
  have hs : 0 ≤ s := abs_nonneg _
  have hsum_nn : 0 ≤ c + s := add_nonneg hc hs
  -- Pythagorean identity in absolute-value form: c² + s² = 1.
  have hpyth : c ^ 2 + s ^ 2 = 1 := by
    have h := sin_sq_add_cos_sq β
    -- |x|² = x²
    have hcsq : c ^ 2 = (cos β) ^ 2 := by rw [show c = |cos β| from rfl]; exact sq_abs _
    have hssq : s ^ 2 = (sin β) ^ 2 := by rw [show s = |sin β| from rfl]; exact sq_abs _
    rw [hcsq, hssq]; linarith
  -- (c + s)² ≤ 2 by Cauchy–Schwarz + Pythagorean.
  have hsum_sq_le : (c + s) ^ 2 ≤ 2 := by
    have := sq_add_le_two_mul_sq_add c s
    rw [hpyth] at this
    linarith
  -- Take square roots.  c+s ≥ 0 and √2 ≥ 0, and (c+s)² ≤ (√2)² gives c+s ≤ √2.
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2nn
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  -- Use Real.sqrt monotonicity: take √ of both sides.
  have hsqrt_le : Real.sqrt ((c + s) ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hsum_sq_le
  rwa [Real.sqrt_sq hsum_nn] at hsqrt_le

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE SINGLET CHSH EXPRESSION AND ITS SUM-TO-PRODUCT FORM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's singlet correlation function (one-line restatement
    of `correlation_from_born_rule`): E(θ_a, θ_b) = -cos(θ_a - θ_b). -/
noncomputable def singletCorrelation (θa θb : ℝ) : ℝ := -cos (θa - θb)

/-- The CHSH expression evaluated on the singlet correlation function
    at four arbitrary angles:
        S(θ_a, θ_a', θ_b, θ_b')
        = E(a,b) + E(a,b') + E(a',b) - E(a',b')
        = -[cos(a-b) + cos(a-b') + cos(a'-b) - cos(a'-b')].

    This is the quantity the Tsirelson bound bounds. -/
noncomputable def tsirelsonChshSinglet (θa θa' θb θb' : ℝ) : ℝ :=
  singletCorrelation θa θb + singletCorrelation θa θb'
    + singletCorrelation θa' θb - singletCorrelation θa' θb'

/-- Direct expansion: the CHSH expression equals
        -[cos(a-b) + cos(a-b') + cos(a'-b) - cos(a'-b')]. -/
lemma tsirelsonChshSinglet_expand (θa θa' θb θb' : ℝ) :
    tsirelsonChshSinglet θa θa' θb θb' =
      -(cos (θa - θb) + cos (θa - θb') + cos (θa' - θb) - cos (θa' - θb')) := by
  unfold tsirelsonChshSinglet singletCorrelation
  ring

/-- Sum-to-product (one direction): cos(x + y) + cos(x − y) = 2·cos(x)·cos(y).
    Proved by direct expansion via `cos_add` and `cos_sub`. -/
lemma cos_add_plus_cos_sub (x y : ℝ) :
    cos (x + y) + cos (x - y) = 2 * cos x * cos y := by
  rw [cos_add, cos_sub]; ring

/-- Sum-to-product (other direction): cos(x + y) − cos(x − y) = −2·sin(x)·sin(y).
    Proved by direct expansion via `cos_add` and `cos_sub`. -/
lemma cos_add_minus_cos_sub (x y : ℝ) :
    cos (x + y) - cos (x - y) = -(2 * sin x * sin y) := by
  rw [cos_add, cos_sub]; ring

/-- **Sum-to-product factorization of the CHSH cosine sum.**

    With the change of variables
        A  := θ_a  - (θ_b + θ_b')/2
        A' := θ_a' - (θ_b + θ_b')/2
        β  := (θ_b' - θ_b)/2
    the four-cosine combination factors as:

        cos(a-b) + cos(a-b') + cos(a'-b) - cos(a'-b')
        = 2·cos(A)·cos(β) - 2·sin(A')·sin(β).

    Proof: apply the standard identities
        cos X + cos Y = 2 cos((X+Y)/2) cos((X-Y)/2)
        cos X - cos Y = -2 sin((X+Y)/2) sin((X-Y)/2)
    to the (a-b, a-b') and (a'-b, a'-b') pairs separately. -/
lemma chsh_cos_sum_factorization (θa θa' θb θb' : ℝ) :
    cos (θa - θb) + cos (θa - θb')
      + cos (θa' - θb) - cos (θa' - θb') =
    2 * cos (θa - (θb + θb') / 2) * cos ((θb' - θb) / 2)
      - 2 * sin (θa' - (θb + θb') / 2) * sin ((θb' - θb) / 2) := by
  -- Step 1: rewrite each cosine argument as (sum-half) ± (diff-half).
  have hab  : θa  - θb  =
      (θa  - (θb + θb') / 2) + ((θb' - θb) / 2) := by ring
  have hab' : θa  - θb' =
      (θa  - (θb + θb') / 2) - ((θb' - θb) / 2) := by ring
  have ha'b : θa' - θb  =
      (θa' - (θb + θb') / 2) + ((θb' - θb) / 2) := by ring
  have ha'b': θa' - θb' =
      (θa' - (θb + θb') / 2) - ((θb' - θb) / 2) := by ring
  rw [hab, hab', ha'b, ha'b']
  -- Step 2: apply the two ABSTRACT sum-to-product lemmas (so the inner
  -- subterms (θ_a − (θ_b+θ_b')/2) etc. are atoms during the rewrite).
  rw [cos_add_plus_cos_sub (θa - (θb + θb') / 2) ((θb' - θb) / 2)]
  -- Goal:  2*cos A*cos β + (cos(A'+β) - cos(A'-β)) = 2*cos A*cos β - 2*sin A'*sin β
  have hcs := cos_add_minus_cos_sub (θa' - (θb + θb') / 2) ((θb' - θb) / 2)
  linarith [hcs]

/-- The CHSH expression in factored form:
        S = -2·cos(A)·cos(β) + 2·sin(A')·sin(β)
    where A, A', β are the half-angle sum-difference abbreviations. -/
lemma tsirelsonChshSinglet_factored (θa θa' θb θb' : ℝ) :
    tsirelsonChshSinglet θa θa' θb θb' =
      -(2 * cos (θa - (θb + θb') / 2) * cos ((θb' - θb) / 2))
      + 2 * sin (θa' - (θb + θb') / 2) * sin ((θb' - θb) / 2) := by
  rw [tsirelsonChshSinglet_expand, chsh_cos_sum_factorization]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE TSIRELSON BOUND |S| ≤ 2√2
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Pointwise bound: |cos x| ≤ 1, restated for `linarith`. -/
private lemma abs_cos_le_one' (x : ℝ) : |cos x| ≤ 1 := abs_cos_le_one x

/-- Pointwise bound: |sin x| ≤ 1, restated for `linarith`. -/
private lemma abs_sin_le_one' (x : ℝ) : |sin x| ≤ 1 := abs_sin_le_one x

/-- **THE TSIRELSON BOUND** (trigonometric form, framework singlet):

        For any four angles (θ_a, θ_a', θ_b, θ_b'):
            |S(θ_a, θ_a', θ_b, θ_b')| ≤ 2·√2.

    Proof outline:
    1.  Factor: S = -2 cos(A) cos(β) + 2 sin(A') sin(β).
    2.  Triangle inequality:
            |S| ≤ 2|cos A||cos β| + 2|sin A'||sin β|
                ≤ 2|cos β|        + 2|sin β|        (since |cos|, |sin| ≤ 1)
                = 2(|cos β| + |sin β|).
    3.  Trig Cauchy–Schwarz: |cos β| + |sin β| ≤ √2
        (lemma `abs_cos_add_abs_sin_le_sqrt_two`).
    4.  Hence |S| ≤ 2√2. -/
theorem tsirelson_bound (θa θa' θb θb' : ℝ) :
    |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2 := by
  -- Step 1: rewrite via the factored form.
  rw [tsirelsonChshSinglet_factored]
  -- Set the abbreviations.
  set A  := θa  - (θb + θb') / 2 with hA_def
  set A' := θa' - (θb + θb') / 2 with hA'_def
  set β  := (θb' - θb) / 2       with hβ_def
  -- Express S = 2·(sin A' · sin β - cos A · cos β) (factor of 2 out).
  have hrewrite :
      -(2 * cos A * cos β) + 2 * sin A' * sin β
      = 2 * (sin A' * sin β - cos A * cos β) := by ring
  rw [hrewrite]
  -- Step 2a: |2 · z| = 2 · |z| (factor scalar out of abs).
  have h_abs2 : |2 * (sin A' * sin β - cos A * cos β)|
              = 2 * |sin A' * sin β - cos A * cos β| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h_abs2]
  -- Goal:  2 * |sin A' · sin β - cos A · cos β| ≤ 2 * √2
  -- Step 2b: triangle inequality for `a - b`.
  have h_tri : |sin A' * sin β - cos A * cos β|
             ≤ |sin A' * sin β| + |cos A * cos β| := abs_sub _ _
  -- Step 2c: factor abs through products.
  have h_eq1 : |sin A' * sin β| = |sin A'| * |sin β| := abs_mul _ _
  have h_eq2 : |cos A * cos β| = |cos A| * |cos β| := abs_mul _ _
  -- Step 2d: bound |sin A'|, |cos A| ≤ 1.
  have h_sA' : |sin A'| ≤ 1 := abs_sin_le_one A'
  have h_cA  : |cos A|  ≤ 1 := abs_cos_le_one A
  have h_sβ_nn : 0 ≤ |sin β| := abs_nonneg _
  have h_cβ_nn : 0 ≤ |cos β| := abs_nonneg _
  have h_bound1 : |sin A'| * |sin β| ≤ 1 * |sin β| :=
    mul_le_mul_of_nonneg_right h_sA' h_sβ_nn
  have h_bound2 : |cos A| * |cos β| ≤ 1 * |cos β| :=
    mul_le_mul_of_nonneg_right h_cA h_cβ_nn
  -- Step 2e: chain to |sin β| + |cos β|.
  have h_sum_le : |sin A' * sin β| + |cos A * cos β|
                ≤ |sin β| + |cos β| := by
    rw [h_eq1, h_eq2]; linarith
  -- Step 3: trig Cauchy–Schwarz on β.  We have |cos β| + |sin β| ≤ √2,
  -- which is the same as |sin β| + |cos β| ≤ √2.
  have h_cs : |sin β| + |cos β| ≤ Real.sqrt 2 := by
    have := abs_cos_add_abs_sin_le_sqrt_two β; linarith
  -- Step 4: conclude
  have h_chain : |sin A' * sin β - cos A * cos β| ≤ Real.sqrt 2 := by
    calc |sin A' * sin β - cos A * cos β|
        ≤ |sin A' * sin β| + |cos A * cos β| := h_tri
      _ ≤ |sin β| + |cos β|                 := h_sum_le
      _ ≤ Real.sqrt 2                        := h_cs
  -- The remaining step: 2 · |...| ≤ 2 · √2.
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  exact (mul_le_mul_of_nonneg_left h_chain h2nn)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: SATURATION AT THE FRAMEWORK'S OPTIMAL ANGLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A small bridge: 2·cos(π/4) = √2 (since cos(π/4) = √2 / 2). -/
lemma two_mul_cos_pi_four_eq_sqrt_two : 2 * cos (π / 4) = Real.sqrt 2 := by
  rw [Real.cos_pi_div_four]
  -- 2 · (√2 / 2) = √2
  field_simp

/-- **Saturation of the Tsirelson bound at the framework's optimal angles.**

    With (θ_a, θ_a', θ_b, θ_b') = (0, π/2, π/4, -π/4):

        tsirelsonChshSinglet 0 (π/2) (π/4) (-(π/4))
            = -(cos(0-π/4) + cos(0-(-π/4)) + cos(π/2-π/4) - cos(π/2-(-π/4)))
            = -(cos(π/4)   + cos(π/4)    + cos(π/4)     - cos(3π/4))
            = -(cos(π/4)   + cos(π/4)    + cos(π/4)     + cos(π/4))
            = -4 cos(π/4)
            = -2 √2.

    This MATCHES the bound 2·√2 in absolute value: |S| = 2√2. -/
theorem singlet_saturates_tsirelson :
    tsirelsonChshSinglet 0 (π / 2) (π / 4) (-(π / 4)) = -(2 * Real.sqrt 2) := by
  rw [tsirelsonChshSinglet_expand]
  -- Reduce each cosine to cos(π/4) (using cos_neg, cos_pi_sub).
  have h1 : cos ((0 : ℝ) - π / 4) = cos (π / 4) := by
    rw [show (0 : ℝ) - π / 4 = -(π / 4) by ring]; exact cos_neg _
  have h2 : cos ((0 : ℝ) - -(π / 4)) = cos (π / 4) := by
    rw [show (0 : ℝ) - -(π / 4) = π / 4 by ring]
  have h3 : cos (π / 2 - π / 4) = cos (π / 4) := by
    rw [show π / 2 - π / 4 = π / 4 by ring]
  have h4 : cos (π / 2 - -(π / 4)) = -cos (π / 4) := by
    rw [show π / 2 - -(π / 4) = 3 * π / 4 by ring]
    exact cos_three_pi_four
  rw [h1, h2, h3, h4]
  -- Now: -(cos(π/4) + cos(π/4) + cos(π/4) - (-cos(π/4))) = -4 cos(π/4)
  -- and 4 cos(π/4) = 2 · (2 cos(π/4)) = 2 · √2.
  have hkey : 2 * cos (π / 4) = Real.sqrt 2 := two_mul_cos_pi_four_eq_sqrt_two
  linarith [hkey]

/-- **Bridge to BellTheorem**: the singlet's CHSH value at the optimal
    angles equals `BellTheorem.chshValue` exactly.  This certifies that
    the new `tsirelsonChshSinglet` definition is the same quantity that
    `BellTheorem` was computing, modulo unfolding. -/
theorem singlet_value_eq_chshValue :
    tsirelsonChshSinglet 0 (π / 2) (π / 4) (-(π / 4)) = chshValue := by
  -- chshValue := -4 cos(π/4) = -(2 · (2 cos(π/4))) = -(2 · √2).
  rw [singlet_saturates_tsirelson]
  unfold chshValue
  rw [← two_mul_cos_pi_four_eq_sqrt_two]
  ring

/-- **Saturation in absolute value**: |S| = 2√2 at the optimal angles. -/
theorem singlet_abs_eq_two_sqrt_two :
    |tsirelsonChshSinglet 0 (π / 2) (π / 4) (-(π / 4))| = 2 * Real.sqrt 2 := by
  rw [singlet_saturates_tsirelson]
  rw [abs_neg]
  rw [abs_of_nonneg]
  positivity

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE FRAMEWORK MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM** — the complete CHSH trichotomy for the
    framework's singlet correlation function:

      (1) **Classical bound**:  any factorizable correlation
          e(a, b) = f(a)·g(b) with |f|, |g| ≤ 1 satisfies |S| ≤ 2.
          (`SeparableCHSH.chsh_factorizable_bound`)

      (2) **Tsirelson bound**:  the framework's singlet correlation
          E(θ_a, θ_b) = -cos(θ_a − θ_b) satisfies |S| ≤ 2·√2 at ALL
          quadruples of angles.  (`tsirelson_bound`, this file)

      (3) **Saturation**:  the framework's singlet at the optimal
          angles (0, π/2, π/4, -π/4) ATTAINS the Tsirelson bound,
          with S = -2·√2 (so |S| = 2√2).  (`singlet_saturates_tsirelson`,
          `singlet_abs_eq_two_sqrt_two`, this file)

    Together with `BellTheorem.bell_violation` (which gives S² = 8 > 4
    at the optimal angles), this establishes the full structure:

        classical achievable bound 2  <  singlet value 2√2  =  Tsirelson bound

    confirming that the framework's quantum predictions strictly
    exceed any local hidden variable model AND saturate the quantum
    upper bound — the Bell trichotomy in one statement. -/
theorem tsirelson_master_theorem :
    -- (1) Classical bound: factorizable correlations are bounded by 2.
    (∀ f g : Bool → ℝ, (∀ x, |f x| ≤ 1) → (∀ y, |g y| ≤ 1) →
        |chshExpr (fun x y => f x * g y)| ≤ 2)
    -- (2) Tsirelson bound: the singlet's CHSH satisfies |S| ≤ 2√2 always.
    ∧ (∀ θa θa' θb θb' : ℝ,
          |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2)
    -- (3) Saturation: at the optimal angles, |S| = 2√2 EXACTLY.
    ∧ |tsirelsonChshSinglet 0 (π / 2) (π / 4) (-(π / 4))| = 2 * Real.sqrt 2
    -- (4) Consistency: that value coincides with `chshValue` from
    --     BellTheorem (no double-counting; one computation, two names).
    ∧ tsirelsonChshSinglet 0 (π / 2) (π / 4) (-(π / 4)) = chshValue :=
  ⟨chsh_factorizable_bound,
   tsirelson_bound,
   singlet_abs_eq_two_sqrt_two,
   singlet_value_eq_chshValue⟩

end UnifiedTheory.LayerB.TsirelsonBound
