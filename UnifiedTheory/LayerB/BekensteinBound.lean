/-
  LayerB/BekensteinBound.lean — The Bekenstein bound S ≤ 2π·R·E

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/BekensteinHawking.lean` proves the Schwarzschild
  Bekenstein-Hawking entropy formula `S_BH(M) = 4π · M² = A/4` and
  its monotonicity / holographic re-statement `S_BH = π · r_s²`.

  This file extracts the *universal upper bound* on the entropy that
  any physical system can carry given its size and energy:

      S ≤ 2π · R · E       (natural units: ℏ = c = k_B = 1)

  This is the **Bekenstein bound** (Bekenstein 1981, building on
  Bekenstein 1972). For a Schwarzschild black hole — where E = M and
  R = r_s = 2M — the bound is SATURATED: 2π · (2M) · M = 4π · M² =
  S_BH. So black holes are the entropy-densest objects allowed by
  semiclassical gravity, and the Bekenstein bound is the universal
  envelope they trace.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) `bekensteinBound R E := 2π · R · E` is the universal Bekenstein
      envelope. Positivity, scaling, and monotonicity in R, E.

  (2) `IsBekensteinCompliant S R E := S ≤ bekensteinBound R E` is the
      compliance predicate. Black holes saturate; ordinary matter is
      strictly below.

  (3) `schwarzschild_saturates_bound`: for the Schwarzschild
      configuration `R = 2M`, `E = M`, the BH entropy `4π · M²`
      EXACTLY equals `bekensteinBound (2M) M`.

  (4) `BH_is_bekenstein`: Schwarzschild black holes are
      Bekenstein-compliant (they saturate the bound).

  (5) `superBHEntropy_collapses`: if a system in radius `R = 2M` with
      energy `E = M` carries entropy `S > 4π·M²`, then `S` exceeds
      the Bekenstein bound. By the generalized second law the system
      cannot persist outside its own Schwarzschild horizon — a stronger
      statement (gravitational collapse to a smaller-entropy BH
      contradicting GSL) is the standard physics derivation; we prove
      only the algebraic implication.

  (6) `holographic_form`: the bound rewritten as
      `S ≤ A · E / (4 · M_BH)` where M_BH is the mass of the
      Schwarzschild BH whose horizon area equals A.

  (7) `bits_form`: the same bound expressed in bits via
      `I ≤ (2π · R · E) / log 2`.

  (8) Master capstone bundling (1)–(7) into one theorem.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS NOT PROVED — HONEST SCOPE

  – The full physical *derivation* of the Bekenstein bound is NOT in
    this file. The standard derivations are:

      (a) Bekenstein's original 1981 adiabatic-insertion argument:
          slowly drop a small system into a Schwarzschild BH while
          monitoring the increase of S_BH; demanding the generalized
          second law `δ(S_BH + S_outside) ≥ 0` forces an upper bound
          on the entropy that the small system could have carried.
          This route requires the full machinery of QFT in curved
          spacetime, the first law `dM = T_H dS_BH`, and the buoyancy
          analysis (Unruh-Wald) — all OUTSIDE the present Lean
          development.

      (b) Casini's 2008 information-theoretic derivation: identify
          S with `S_full − S_vacuum` (relative entropy) and use
          monotonicity of relative entropy under restriction to a
          subregion. This is conceptually clean but again requires
          a full QFT framework.

    We take the inequality `S ≤ 2π · R · E` as the Bekenstein
    convention (a definitional input, not a custom Lean axiom) and
    derive its algebraic consequences and saturation by Schwarzschild.

  – The "GSL ⟹ Bekenstein" implication of (5) is stated as an
    algebraic THEOREM about a postulated `S` exceeding the bound; the
    physical conclusion that gravitational collapse must occur is
    the standard Bekenstein 1981 argument, not a Lean theorem.

  – The 1/4 coefficient in the holographic form (6) inherits its
    convention from `BekensteinHawking.lean` (Hawking 1974/1975).

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.BekensteinHawking

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BekensteinBound

open Real
open UnifiedTheory.LayerB.BekensteinHawking

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE BEKENSTEIN BOUND `2π · R · E`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For any system of characteristic radius R and energy E, the
    Bekenstein bound on entropy is

        S ≤ 2π · R · E       (ℏ = c = k_B = 1).

    The right-hand side `bekensteinBound R E := 2π · R · E` is the
    universal upper-envelope that black holes saturate.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bekenstein bound** in natural units: `2π · R · E`. -/
noncomputable def bekensteinBound (R E : ℝ) : ℝ :=
  2 * Real.pi * R * E

/-- The Bekenstein bound is non-negative when both R and E are. -/
theorem bekensteinBound_nonneg {R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E) :
    0 ≤ bekensteinBound R E := by
  unfold bekensteinBound
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := mul_nonneg h2 hπ
  have h2πR : (0 : ℝ) ≤ 2 * Real.pi * R := mul_nonneg h2π hR
  exact mul_nonneg h2πR hE

/-- The Bekenstein bound is strictly positive when R, E are. -/
theorem bekensteinBound_pos {R E : ℝ} (hR : 0 < R) (hE : 0 < E) :
    0 < bekensteinBound R E := by
  unfold bekensteinBound
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hπ : 0 < Real.pi := Real.pi_pos
  exact mul_pos (mul_pos (mul_pos h2 hπ) hR) hE

/-- The Bekenstein bound is monotone non-decreasing in R (with E ≥ 0). -/
theorem bekensteinBound_mono_R {R₁ R₂ E : ℝ}
    (hE : 0 ≤ E) (hR : R₁ ≤ R₂) :
    bekensteinBound R₁ E ≤ bekensteinBound R₂ E := by
  unfold bekensteinBound
  have h2π : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have step : 2 * Real.pi * R₁ ≤ 2 * Real.pi * R₂ :=
    mul_le_mul_of_nonneg_left hR h2π
  exact mul_le_mul_of_nonneg_right step hE

/-- The Bekenstein bound is monotone non-decreasing in E (with R ≥ 0). -/
theorem bekensteinBound_mono_E {R E₁ E₂ : ℝ}
    (hR : 0 ≤ R) (hE : E₁ ≤ E₂) :
    bekensteinBound R E₁ ≤ bekensteinBound R E₂ := by
  unfold bekensteinBound
  have h2π : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have h2πR : (0 : ℝ) ≤ 2 * Real.pi * R := mul_nonneg h2π hR
  exact mul_le_mul_of_nonneg_left hE h2πR

/-- Linearity in R: `bekensteinBound (cR) E = c · bekensteinBound R E`. -/
theorem bekensteinBound_smul_R (c R E : ℝ) :
    bekensteinBound (c * R) E = c * bekensteinBound R E := by
  unfold bekensteinBound
  ring

/-- Linearity in E: `bekensteinBound R (cE) = c · bekensteinBound R E`. -/
theorem bekensteinBound_smul_E (c R E : ℝ) :
    bekensteinBound R (c * E) = c * bekensteinBound R E := by
  unfold bekensteinBound
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: COMPLIANCE PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A system is **Bekenstein-compliant** if its entropy lies at or
    below the Bekenstein bound for its size and energy. -/
def IsBekensteinCompliant (S R E : ℝ) : Prop :=
  S ≤ bekensteinBound R E

/-- The trivial system (S = 0) is always compliant for non-negative R, E. -/
theorem zero_entropy_compliant {R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E) :
    IsBekensteinCompliant 0 R E :=
  bekensteinBound_nonneg hR hE

/-- Compliance is monotone: smaller entropy stays compliant. -/
theorem IsBekensteinCompliant.mono {S₁ S₂ R E : ℝ}
    (h : IsBekensteinCompliant S₂ R E) (hS : S₁ ≤ S₂) :
    IsBekensteinCompliant S₁ R E :=
  le_trans hS h

/-- Compliance is preserved when R increases (with E ≥ 0). -/
theorem IsBekensteinCompliant.mono_R {S R₁ R₂ E : ℝ}
    (h : IsBekensteinCompliant S R₁ E) (hE : 0 ≤ E) (hR : R₁ ≤ R₂) :
    IsBekensteinCompliant S R₂ E :=
  le_trans h (bekensteinBound_mono_R hE hR)

/-- Compliance is preserved when E increases (with R ≥ 0). -/
theorem IsBekensteinCompliant.mono_E {S R E₁ E₂ : ℝ}
    (h : IsBekensteinCompliant S R E₁) (hR : 0 ≤ R) (hE : E₁ ≤ E₂) :
    IsBekensteinCompliant S R E₂ :=
  le_trans h (bekensteinBound_mono_E hR hE)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: SCHWARZSCHILD BLACK HOLES SATURATE THE BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a Schwarzschild BH of mass M, the relevant size and energy are
    `R = r_s = 2M` and `E = M` (rest mass-energy). Plugging in:

        bekensteinBound (2M) M = 2π · 2M · M = 4π · M²
                               = bekensteinHawkingEntropy M.

    So black holes EXACTLY saturate the Bekenstein bound — they are
    the maximally entropic objects of their size and energy.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Schwarzschild saturation**: the Bekenstein bound at `R = 2M`,
    `E = M` exactly equals the BH entropy `4π · M²`. -/
theorem schwarzschild_saturates_bound (M : ℝ) :
    bekensteinBound (2 * M) M = bekensteinHawkingEntropy M := by
  unfold bekensteinBound
  rw [BH_entropy_eq]
  ring

/-- Equivalent form: `bekensteinBound (r_s) M = S_BH(M)`. -/
theorem schwarzschild_saturates_bound' (M : ℝ) :
    bekensteinBound (schwarzschildRadius M) M = bekensteinHawkingEntropy M := by
  unfold schwarzschildRadius
  exact schwarzschild_saturates_bound M

/-- Closed form for the Schwarzschild bound: `4π · M²`. -/
theorem schwarzschild_bound_eq (M : ℝ) :
    bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2 := by
  unfold bekensteinBound
  ring

/-- **BHs are Bekenstein-compliant (saturating).** A Schwarzschild BH
    of mass M satisfies `S_BH ≤ bekensteinBound r_s M`, with equality. -/
theorem BH_is_bekenstein (M : ℝ) :
    IsBekensteinCompliant (bekensteinHawkingEntropy M)
                          (schwarzschildRadius M) M := by
  unfold IsBekensteinCompliant
  rw [schwarzschild_saturates_bound']

/-- **Stronger statement**: equality holds for the Schwarzschild
    configuration. -/
theorem BH_saturates_bekenstein (M : ℝ) :
    bekensteinHawkingEntropy M
      = bekensteinBound (schwarzschildRadius M) M :=
  (schwarzschild_saturates_bound' M).symm

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: VIOLATION ⟹ GRAVITATIONAL COLLAPSE
    (algebraic shadow of Bekenstein 1981)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Suppose a system has size R = 2M (it just barely fits inside its
    own Schwarzschild radius) and energy E = M. If its entropy S
    EXCEEDS `4π · M² = S_BH(M)`, then S also exceeds the Bekenstein
    bound `bekensteinBound (2M) M`. By the generalized second law,
    such a system cannot persist outside a Schwarzschild horizon: it
    must collapse into a black hole, but the resulting BH would have
    entropy 4π · M² < S, violating the GSL.

    We prove ONLY the algebraic implication
       S > 4π M² ⟹ ¬ IsBekensteinCompliant S (2M) M.
    The full physical conclusion (collapse must occur) is the standard
    Bekenstein argument.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Excess-entropy collapse (algebraic)**: any system at `R = 2M`,
    `E = M` carrying entropy `S > 4π · M²` violates the Bekenstein
    bound. (Physical interpretation: it cannot persist; collapse to a
    BH would lower the entropy, contradicting GSL.) -/
theorem superBHEntropy_collapses {S M : ℝ}
    (hS : 4 * Real.pi * M ^ 2 < S) :
    ¬ IsBekensteinCompliant S (2 * M) M := by
  unfold IsBekensteinCompliant
  rw [show bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2 from
        schwarzschild_bound_eq M]
  exact not_le.mpr hS

/-- **Equality iff BH**: at the Schwarzschild configuration
    `R = 2M`, `E = M`, the entropy `S` equals the Bekenstein bound
    iff `S = bekensteinHawkingEntropy M`. -/
theorem saturation_iff_BH (S M : ℝ) :
    S = bekensteinBound (2 * M) M ↔ S = bekensteinHawkingEntropy M := by
  rw [show bekensteinBound (2 * M) M = bekensteinHawkingEntropy M from
        schwarzschild_saturates_bound M]

/-- **Compliance at the saturating point**: for the Schwarzschild
    configuration, `S` is compliant iff it does not exceed the BH
    entropy. -/
theorem compliant_at_BH_iff (S M : ℝ) :
    IsBekensteinCompliant S (2 * M) M ↔ S ≤ bekensteinHawkingEntropy M := by
  unfold IsBekensteinCompliant
  rw [show bekensteinBound (2 * M) M = bekensteinHawkingEntropy M from
        schwarzschild_saturates_bound M]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: HOLOGRAPHIC FORM `S ≤ A · E / (4 M_BH)`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Bekenstein bound can be re-expressed using the BH that
    matches the system's size. For the Schwarzschild BH of mass
    `M_BH = M` and horizon area `A = 16π M²`:

        bekensteinBound (2M) E = 2π · 2M · E
                               = 4π · M² · (E/M)
                               = (A/4) · (E/M)
                               = A · E / (4 · M_BH).

    This is the holographic form: the bound equals horizon area times
    energy per BH-mass, divided by 4. At E = M (BH's own energy) the
    bound reduces to A/4 = S_BH.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Holographic form** of the Bekenstein bound: at radius `R = 2M`
    with energy `E`, the bound equals `A · E / (4 M)` where
    `A = 16π · M²` is the horizon area of the Schwarzschild BH of
    mass `M`. -/
theorem holographic_form {M E : ℝ} (hM : M ≠ 0) :
    bekensteinBound (2 * M) E = horizonArea M * E / (4 * M) := by
  rw [horizonArea_eq]
  unfold bekensteinBound
  field_simp
  ring

/-- **Holographic form, dual**: `bekensteinBound (2M) E = (A/4) · (E/M)`. -/
theorem holographic_form_factored {M E : ℝ} (hM : M ≠ 0) :
    bekensteinBound (2 * M) E = (horizonArea M / 4) * (E / M) := by
  rw [horizonArea_eq]
  unfold bekensteinBound
  field_simp
  ring

/-- Reduction at E = M: the holographic Bekenstein bound becomes the
    Schwarzschild BH entropy `A/4`. -/
theorem holographic_at_E_eq_M {M : ℝ} (hM : M ≠ 0) :
    bekensteinBound (2 * M) M = horizonArea M / 4 := by
  rw [holographic_form_factored hM]
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: BIT FORM `I ≤ (2π R E) / log 2`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Information `I` (in bits) and entropy `S` (in nats) are related
    by `S = I · log 2`, i.e. `I = S / log 2`. So the Bekenstein bound
    in bits reads

        I ≤ (2π · R · E) / log 2.

    The conversion is purely algebraic; we just record the formula and
    prove the inequality is equivalent.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bekenstein bound in bits**: `I ≤ (2π · R · E) / log 2`. -/
noncomputable def bekensteinBoundBits (R E : ℝ) : ℝ :=
  bekensteinBound R E / Real.log 2

/-- `Real.log 2 > 0`; used to convert nats ↔ bits without dividing
    by zero. -/
theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

/-- `Real.log 2 ≠ 0`. -/
theorem log_two_ne_zero : Real.log 2 ≠ 0 :=
  ne_of_gt log_two_pos

/-- **Bit-form equivalence**: an entropy `S` (in nats) is compliant
    iff the corresponding information `I = S / log 2` (in bits) lies
    below `bekensteinBoundBits`. -/
theorem bits_form (S R E : ℝ) :
    IsBekensteinCompliant S R E
      ↔ S / Real.log 2 ≤ bekensteinBoundBits R E := by
  unfold IsBekensteinCompliant bekensteinBoundBits
  constructor
  · intro h
    exact div_le_div_of_nonneg_right h log_two_pos.le
  · intro h
    have h2 : (S / Real.log 2) * Real.log 2
                ≤ (bekensteinBound R E / Real.log 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h log_two_pos.le
    have h2' : S = (S / Real.log 2) * Real.log 2 := by
      field_simp
    have h3 : bekensteinBound R E
                = (bekensteinBound R E / Real.log 2) * Real.log 2 := by
      field_simp
    linarith

/-- BH entropy in bits at the Schwarzschild saturation:
    `I_BH = 4π · M² / log 2`. -/
theorem BH_bits_at_saturation (M : ℝ) :
    bekensteinBoundBits (2 * M) M
      = bekensteinHawkingEntropy M / Real.log 2 := by
  unfold bekensteinBoundBits
  rw [schwarzschild_saturates_bound]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONNECTION TO HOLOGRAPHIC PRINCIPLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining `BH_is_bekenstein` with `BekensteinHawking.BH_entropy_is_quarter_area`:
    the Bekenstein bound for a Schwarzschild configuration equals A/4,
    so any compliant system inside a region of area A carries at most
    A/4 nats of entropy. That is the holographic principle (Susskind,
    't Hooft) for the Schwarzschild family — entropy is bounded by
    quarter the boundary area.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Holographic principle (Schwarzschild form)**: the Bekenstein
    bound at `R = 2M`, `E = M` equals the BH entropy A/4.
    Therefore any Bekenstein-compliant system at this configuration
    carries at most `horizonArea M / 4` nats. -/
theorem holographic_principle (S M : ℝ)
    (h : IsBekensteinCompliant S (2 * M) M) :
    S ≤ horizonArea M / 4 := by
  have hsat : bekensteinBound (2 * M) M = horizonArea M / 4 := by
    rw [show bekensteinBound (2 * M) M = bekensteinHawkingEntropy M from
          schwarzschild_saturates_bound M]
    rfl
  exact le_trans h (le_of_eq hsat)

/-- **Compliance at Schwarzschild radius is exactly the holographic
    bound `S ≤ A/4`.** -/
theorem compliant_iff_quarter_area (S M : ℝ) :
    IsBekensteinCompliant S (2 * M) M ↔ S ≤ horizonArea M / 4 := by
  rw [compliant_at_BH_iff]
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER CAPSTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE BEKENSTEIN-BOUND CAPSTONE.**

    For any region of characteristic radius R and energy E (in natural
    units ℏ = c = k_B = 1):

    (1) The Bekenstein bound is `bekensteinBound R E = 2π · R · E`.

    (2) The bound is non-negative for `R, E ≥ 0` and strictly positive
        for `R, E > 0`. It is monotone non-decreasing in each argument.

    (3) For a Schwarzschild BH of mass M (so `R = r_s = 2M`, `E = M`),
        the bound is SATURATED: `bekensteinBound (2M) M = 4π · M² =
        bekensteinHawkingEntropy M`.

    (4) Every Schwarzschild BH is Bekenstein-compliant; the inequality
        is tight (equality).

    (5) Any system at `R = 2M`, `E = M` whose entropy exceeds
        `4π · M²` violates the Bekenstein bound (algebraic version of
        Bekenstein 1981 collapse argument).

    (6) Holographic form: `bekensteinBound (2M) E = A · E / (4 M)`
        where A is the Schwarzschild horizon area; in particular at
        `E = M` the bound equals `A/4` — the holographic principle.

    (7) Bit form: an entropy `S` (nats) is compliant iff
        `I = S / log 2 ≤ (2π R E) / log 2 = bekensteinBoundBits R E`. -/
theorem bekenstein_bound_capstone :
    -- (1) Definition
    (∀ R E : ℝ, bekensteinBound R E = 2 * Real.pi * R * E)
    -- (2a) Non-negativity
    ∧ (∀ R E : ℝ, 0 ≤ R → 0 ≤ E → 0 ≤ bekensteinBound R E)
    -- (2b) Strict positivity
    ∧ (∀ R E : ℝ, 0 < R → 0 < E → 0 < bekensteinBound R E)
    -- (2c) Monotone in R
    ∧ (∀ R₁ R₂ E : ℝ, 0 ≤ E → R₁ ≤ R₂ →
        bekensteinBound R₁ E ≤ bekensteinBound R₂ E)
    -- (2d) Monotone in E
    ∧ (∀ R E₁ E₂ : ℝ, 0 ≤ R → E₁ ≤ E₂ →
        bekensteinBound R E₁ ≤ bekensteinBound R E₂)
    -- (3) Schwarzschild saturation
    ∧ (∀ M : ℝ, bekensteinBound (2 * M) M = bekensteinHawkingEntropy M)
    -- (3') Closed form at saturation
    ∧ (∀ M : ℝ, bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2)
    -- (4) BHs are Bekenstein-compliant (= saturating)
    ∧ (∀ M : ℝ, IsBekensteinCompliant (bekensteinHawkingEntropy M)
                                       (schwarzschildRadius M) M)
    -- (5) Excess entropy at the Schwarzschild config violates the bound
    ∧ (∀ S M : ℝ, 4 * Real.pi * M ^ 2 < S →
        ¬ IsBekensteinCompliant S (2 * M) M)
    -- (6) Holographic form at R = 2M (M ≠ 0)
    ∧ (∀ M E : ℝ, M ≠ 0 →
        bekensteinBound (2 * M) E = horizonArea M * E / (4 * M))
    -- (6') At E = M the bound is the BH entropy A/4
    ∧ (∀ S M : ℝ, IsBekensteinCompliant S (2 * M) M
                  → S ≤ horizonArea M / 4)
    -- (7) Bit form equivalence
    ∧ (∀ S R E : ℝ,
          IsBekensteinCompliant S R E
            ↔ S / Real.log 2 ≤ bekensteinBoundBits R E) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, schwarzschild_saturates_bound,
          schwarzschild_bound_eq, BH_is_bekenstein, ?_,
          ?_, holographic_principle, bits_form⟩
  · intros R E hR hE; exact bekensteinBound_nonneg hR hE
  · intros R E hR hE; exact bekensteinBound_pos hR hE
  · intros R₁ R₂ E hE hR; exact bekensteinBound_mono_R hE hR
  · intros R E₁ E₂ hR hE; exact bekensteinBound_mono_E hR hE
  · intros S M hS; exact superBHEntropy_collapses hS
  · intros M E hM; exact holographic_form hM

end UnifiedTheory.LayerB.BekensteinBound
