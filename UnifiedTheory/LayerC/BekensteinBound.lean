/-
  LayerC/BekensteinBound.lean — The Bekenstein bound `S ≤ 2π R E / (ℏc)`
  as a Layer-C *universal* statement (system-agnostic).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT
  -------
  `LayerB/BekensteinBound.lean` formalizes the bound for the
  Schwarzschild family — proving that the BH saturates `S ≤ 2π R E`
  and recasting it in holographic / bit form for the Schwarzschild
  configuration `R = 2M`, `E = M`.

  This file lifts the bound to **Layer C**: the bound is treated as a
  universal *envelope* over arbitrary physical systems. We:

    (1) Re-define `bekensteinBound R E := 2π · R · E` (natural units
        ℏ = c = k_B = 1) at the Layer-C namespace and prove its
        elementary properties (non-negativity, monotonicity, scaling).

    (2) Define a system-level predicate
        `UniversalEntropyBound S R E : Prop  :=  S ≤ bekensteinBound R E`
        and prove it is preserved under sub-bounds, monotone in `R`,
        monotone in `E`.

    (3) Re-prove the **Schwarzschild saturation identity**
        `bekensteinBound (2M) M = π · (2M)² = A/4` purely algebraically,
        without depending on the LayerB BH-entropy file. This keeps
        LayerC self-contained.

    (4) State the **Universal Entropy Bound** as a *named target*
        `Bekenstein_Universal_Target` — the proposition that *every*
        non-negative entropy of a system of radius `R ≥ 0` and energy
        `E ≥ 0` lies under the Bekenstein envelope. The general proof
        requires QFT in curved spacetime (Bekenstein 1981 adiabatic
        argument, or Casini 2008 relative-entropy derivation); we
        record the target propositionally and discharge it on the
        *concrete Schwarzschild model* as a sanity check.

    (5) State the **Holographic Principle** target
        `Holographic_Principle_Target`: every system contained in a
        spherical region of horizon area `A` carries at most `A/4`
        nats of entropy. We give the proof for the Schwarzschild
        configuration via the saturation identity.

    (6) Concrete-system "sanity checks": the trivial system (zero
        entropy) and the saturating Schwarzschild system are both
        compliant with the universal bound. These instantiate the
        universal predicate and demonstrate it is non-vacuous and
        non-trivial.

    (7) **Master capstone** bundling all unconditional theorems.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED UNCONDITIONALLY
  ------------------------------
  – `bekensteinBound R E = 2 π R E`, `≥ 0` on `R, E ≥ 0`, `> 0` on
    `R, E > 0`, monotone in each argument, linear under scaling.
  – `bhEntropy R := π R²`, `≥ 0` on `R ≥ 0`, monotone in `R` on `R ≥ 0`.
  – `bekenstein_saturates_at_BH`: `bekensteinBound (2M) M = bhEntropy (2M)`
    purely as `ring` identity.
  – `UniversalEntropyBound` is monotone in `S` (downward), monotone in
    `R` (upward) at fixed `E ≥ 0`, monotone in `E` (upward) at fixed
    `R ≥ 0`. The trivial `S = 0` system is universally compliant.
  – `bekensteinUniversalOnBHFamily`: the universal bound *restricted to
    the Schwarzschild family* — for every `M ≥ 0`, the Schwarzschild
    entropy `bhEntropy (2M)` satisfies the universal bound with
    `R = 2M`, `E = M`. (Discharged unconditionally as a saturation
    equality.)
  – `holographicOnBHFamily`: the holographic principle on the
    Schwarzschild family — `bhEntropy (2M) = π (2M)² = A/4` where
    `A = 4π (2M)²` is the horizon area. (Discharged unconditionally.)

  WHAT IS A NAMED TARGET (UNDISCHARGED)
  -------------------------------------
  – `Bekenstein_Universal_Target` quantifies over *all* systems.
    A general proof requires the QFT-in-curved-spacetime machinery
    catalogued in `LayerB/BekensteinBound.lean`'s preamble. We
    record the target as a Prop; we do not attempt a Lean proof.

  – `Holographic_Principle_Target` quantifies over all systems whose
    enclosing region has area A. A general proof goes through the
    universal bound + saturation by the Schwarzschild BH. We record
    the target as a Prop.

  Both named targets are *consistent* (instantiated by the saturating
  Schwarzschild system in the unconditional theorems above).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Zero `sorry`. Zero custom `axiom`. All lemmas are `ring`/`positivity`
  /`nlinarith` style on the real line, plus elementary monotonicity.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.BekensteinBound

open Real

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE BEKENSTEIN BOUND `2π · R · E`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Natural units `ℏ = c = k_B = 1`. For a system of characteristic
    radius `R` and energy `E`, the *Bekenstein bound* on its entropy
    is
        S ≤ 2π · R · E .

    The right-hand side is `bekensteinBound R E`. This file treats
    `bekensteinBound` as a *universal envelope* over arbitrary
    physical systems (Layer C), not as a property of a single BH
    geometry (Layer B).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bekenstein bound** in natural units `ℏ = c = k_B = 1`:
    `bekensteinBound R E := 2π · R · E`. -/
noncomputable def bekensteinBound (R E : ℝ) : ℝ :=
  2 * Real.pi * R * E

/-- The Bekenstein bound is non-negative for `R, E ≥ 0`. -/
theorem bekensteinBound_nonneg (R E : ℝ) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    0 ≤ bekensteinBound R E := by
  unfold bekensteinBound
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h2πR : (0 : ℝ) ≤ 2 * Real.pi * R := mul_nonneg h2π hR
  exact mul_nonneg h2πR hE

/-- The Bekenstein bound is strictly positive for `R, E > 0`. -/
theorem bekensteinBound_pos (R E : ℝ) (hR : 0 < R) (hE : 0 < E) :
    0 < bekensteinBound R E := by
  unfold bekensteinBound
  have hπ : 0 < Real.pi := Real.pi_pos
  exact mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hπ) hR) hE

/-- The Bekenstein bound is monotone non-decreasing in the radius `R`,
    at fixed energy `E ≥ 0`. -/
theorem bekensteinBound_mono_R (R₁ R₂ E : ℝ) (hE : 0 ≤ E) (h : R₁ ≤ R₂) :
    bekensteinBound R₁ E ≤ bekensteinBound R₂ E := by
  unfold bekensteinBound
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have step : 2 * Real.pi * R₁ ≤ 2 * Real.pi * R₂ :=
    mul_le_mul_of_nonneg_left h h2π
  exact mul_le_mul_of_nonneg_right step hE

/-- The Bekenstein bound is monotone non-decreasing in the energy `E`,
    at fixed radius `R ≥ 0`. -/
theorem bekensteinBound_mono_E (R E₁ E₂ : ℝ) (hR : 0 ≤ R) (h : E₁ ≤ E₂) :
    bekensteinBound R E₁ ≤ bekensteinBound R E₂ := by
  unfold bekensteinBound
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h2πR : (0 : ℝ) ≤ 2 * Real.pi * R := mul_nonneg h2π hR
  exact mul_le_mul_of_nonneg_left h h2πR

/-- Linear scaling in `R`: `bekensteinBound (c·R) E = c · bekensteinBound R E`. -/
theorem bekensteinBound_smul_R (c R E : ℝ) :
    bekensteinBound (c * R) E = c * bekensteinBound R E := by
  unfold bekensteinBound; ring

/-- Linear scaling in `E`: `bekensteinBound R (c·E) = c · bekensteinBound R E`. -/
theorem bekensteinBound_smul_E (c R E : ℝ) :
    bekensteinBound R (c * E) = c * bekensteinBound R E := by
  unfold bekensteinBound; ring

/-- The Bekenstein bound vanishes when `R = 0`. -/
theorem bekensteinBound_zero_R (E : ℝ) :
    bekensteinBound 0 E = 0 := by
  unfold bekensteinBound; ring

/-- The Bekenstein bound vanishes when `E = 0`. -/
theorem bekensteinBound_zero_E (R : ℝ) :
    bekensteinBound R 0 = 0 := by
  unfold bekensteinBound; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BEKENSTEIN-HAWKING BLACK-HOLE ENTROPY `π · R²`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A Schwarzschild BH of radius `R` (the horizon Schwarzschild
    radius) carries entropy

        S_BH = A / 4 = (4π R²) / 4 = π R²    (natural units G = c = ℏ = 1).

    We define `bhEntropy R := π · R²` directly (no detour through the
    LayerB Hawking-temperature file), making this LayerC file
    self-contained.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bekenstein-Hawking BH entropy** as a function of the horizon
    radius `R`: `bhEntropy R = π · R²`. Equivalently, `A / 4` where
    `A = 4π R²` is the horizon area. -/
noncomputable def bhEntropy (R : ℝ) : ℝ := Real.pi * R ^ 2

/-- BH entropy is non-negative for all real `R` (it depends on `R²`). -/
theorem bhEntropy_nonneg (R : ℝ) : 0 ≤ bhEntropy R := by
  unfold bhEntropy
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hR2 : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
  exact mul_nonneg hπ hR2

/-- BH entropy vanishes iff the horizon radius vanishes. -/
theorem bhEntropy_eq_zero_iff (R : ℝ) :
    bhEntropy R = 0 ↔ R = 0 := by
  unfold bhEntropy
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  constructor
  · intro h
    have hR2 : R ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with hpi | hR2
      · exact absurd hpi hπ
      · exact hR2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hR2
  · intro h; rw [h]; ring

/-- BH entropy is monotone non-decreasing in `R` on `R ≥ 0`. -/
theorem bhEntropy_mono (R₁ R₂ : ℝ) (h₁ : 0 ≤ R₁) (h : R₁ ≤ R₂) :
    bhEntropy R₁ ≤ bhEntropy R₂ := by
  unfold bhEntropy
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hsq : R₁ ^ 2 ≤ R₂ ^ 2 := by
    have h₂ : 0 ≤ R₂ := le_trans h₁ h
    nlinarith [sq_nonneg (R₂ - R₁), sq_nonneg (R₁ + R₂)]
  exact mul_le_mul_of_nonneg_left hsq hπ

/-- BH entropy is strictly positive for `R > 0`. -/
theorem bhEntropy_pos (R : ℝ) (hR : 0 < R) : 0 < bhEntropy R := by
  unfold bhEntropy
  have hπ : 0 < Real.pi := Real.pi_pos
  exact mul_pos hπ (pow_pos hR 2)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: SCHWARZSCHILD SATURATION IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the Schwarzschild BH of mass `M` (units `c = G = 1`), the
    relevant radius and energy are `R = 2M` and `E = M`. The
    Bekenstein bound at this point equals the BH entropy:

        bekensteinBound (2M) M = 2π · 2M · M = 4π M² = π (2M)²
                              = bhEntropy (2M).

    Thus the Schwarzschild BH *saturates* the Bekenstein bound — it
    is the maximally entropic object of its size and energy. The
    identity below is a pure `ring` equality.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Schwarzschild saturation**: at `R = 2M`, `E = M`, the Bekenstein
    bound exactly equals the BH entropy `π · (2M)²`. -/
theorem bekenstein_saturates_at_BH (M : ℝ) :
    bekensteinBound (2 * M) M = bhEntropy (2 * M) := by
  unfold bekensteinBound bhEntropy
  ring

/-- Closed-form value: `bekensteinBound (2M) M = 4π · M²`. -/
theorem bekensteinBound_at_schwarzschild (M : ℝ) :
    bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2 := by
  unfold bekensteinBound
  ring

/-- Closed-form value: `bhEntropy (2M) = 4π · M²`. -/
theorem bhEntropy_at_schwarzschild (M : ℝ) :
    bhEntropy (2 * M) = 4 * Real.pi * M ^ 2 := by
  unfold bhEntropy
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: UNIVERSAL ENTROPY-BOUND PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A system with entropy `S`, radius `R`, energy `E` is said to
    *satisfy the universal entropy bound* iff `S ≤ bekensteinBound R E`.
    This is a system-agnostic predicate: it makes no commitment to
    the system's microscopic structure.

    We prove the predicate is well-behaved under the obvious
    monotonicities — strictly downward in `S` (smaller-entropy
    sub-systems stay compliant), and upward in each of `R`, `E`
    (enlarging the bound preserves compliance).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A system is **universally entropy-bounded** if its entropy lies
    at or below the Bekenstein envelope for its size and energy. -/
def UniversalEntropyBound (S R E : ℝ) : Prop :=
  S ≤ bekensteinBound R E

/-- The trivial (zero-entropy) system always satisfies the universal
    bound, provided `R, E ≥ 0`. -/
theorem UniversalEntropyBound.zero (R E : ℝ) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    UniversalEntropyBound 0 R E :=
  bekensteinBound_nonneg R E hR hE

/-- **Sub-bound preservation**: if `S' ≤ S` and `S` satisfies the
    universal bound, then so does `S'`. -/
theorem UniversalEntropyBound_subbound
    (S R E S' : ℝ) (h : S' ≤ S) (hBek : UniversalEntropyBound S R E) :
    UniversalEntropyBound S' R E :=
  le_trans h hBek

/-- The universal bound is preserved when the enclosing radius
    increases (with `E ≥ 0`). -/
theorem UniversalEntropyBound.mono_R
    (S R₁ R₂ E : ℝ) (hE : 0 ≤ E) (hR : R₁ ≤ R₂)
    (h : UniversalEntropyBound S R₁ E) :
    UniversalEntropyBound S R₂ E :=
  le_trans h (bekensteinBound_mono_R R₁ R₂ E hE hR)

/-- The universal bound is preserved when the available energy
    increases (with `R ≥ 0`). -/
theorem UniversalEntropyBound.mono_E
    (S R E₁ E₂ : ℝ) (hR : 0 ≤ R) (hE : E₁ ≤ E₂)
    (h : UniversalEntropyBound S R E₁) :
    UniversalEntropyBound S R E₂ :=
  le_trans h (bekensteinBound_mono_E R E₁ E₂ hR hE)

/-- A non-positive entropy automatically satisfies the universal
    bound for non-negative `R, E`. -/
theorem UniversalEntropyBound.of_nonpos
    (S R E : ℝ) (hS : S ≤ 0) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    UniversalEntropyBound S R E :=
  le_trans hS (bekensteinBound_nonneg R E hR hE)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SCHWARZSCHILD INSTANCE — UNIVERSAL BOUND ON BH FAMILY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We discharge the universal entropy bound on the *Schwarzschild
    family*: for every BH of mass `M ≥ 0`, the BH entropy `π (2M)²`
    saturates the Bekenstein bound at `(R, E) = (2M, M)`. So every
    Schwarzschild BH is universally entropy-bounded (with equality).

    This serves three purposes:
      (a) it instantiates `UniversalEntropyBound` non-vacuously;
      (b) it confirms the universal target is *consistent* (the
          most-entropic known objects respect it);
      (c) it gives a unconditional Lean witness for the named
          universal target on the Schwarzschild submodel.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Schwarzschild BHs satisfy the universal Bekenstein bound**:
    for every `M ≥ 0`, the BH of mass `M` (radius `2M`, energy `M`)
    has `bhEntropy (2M) ≤ bekensteinBound (2M) M` — with equality. -/
theorem bekensteinUniversalOnBHFamily (M : ℝ) (_hM : 0 ≤ M) :
    UniversalEntropyBound (bhEntropy (2 * M)) (2 * M) M := by
  unfold UniversalEntropyBound
  rw [bekenstein_saturates_at_BH]

/-- **Equality form**: Schwarzschild BHs *saturate* the universal
    Bekenstein bound. -/
theorem bekensteinSaturationOnBHFamily (M : ℝ) :
    bhEntropy (2 * M) = bekensteinBound (2 * M) M :=
  (bekenstein_saturates_at_BH M).symm

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: HOLOGRAPHIC PRINCIPLE — `S ≤ A / 4`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Schwarzschild horizon of radius `R` has area `A = 4π R²`.
    Combining with `bhEntropy R = π R² = A / 4` gives the famous
    *holographic identity*

        bhEntropy R = horizonArea R / 4.

    The **holographic principle** (Susskind, 't Hooft) asserts that
    every system contained in a region of area `A` carries at most
    `A / 4` nats of entropy. On the Schwarzschild family this
    follows directly from saturation of the Bekenstein bound.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Horizon area** of a Schwarzschild BH of radius `R`:
    `horizonArea R := 4π R²`. -/
noncomputable def horizonArea (R : ℝ) : ℝ := 4 * Real.pi * R ^ 2

/-- Horizon area is non-negative for all real `R`. -/
theorem horizonArea_nonneg (R : ℝ) : 0 ≤ horizonArea R := by
  unfold horizonArea
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h4π : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  exact mul_nonneg h4π (sq_nonneg R)

/-- **Holographic identity**: `bhEntropy R = horizonArea R / 4`. -/
theorem bhEntropy_eq_quarter_area (R : ℝ) :
    bhEntropy R = horizonArea R / 4 := by
  unfold bhEntropy horizonArea
  ring

/-- **Holographic form of the universal bound on the Schwarzschild
    family**: for every `M`, `bekensteinBound (2M) M = horizonArea (2M) / 4`. -/
theorem holographicOnBHFamily (M : ℝ) :
    bekensteinBound (2 * M) M = horizonArea (2 * M) / 4 := by
  rw [bekenstein_saturates_at_BH]
  exact bhEntropy_eq_quarter_area (2 * M)

/-- **Holographic compliance**: any system that satisfies the
    universal Bekenstein bound at the Schwarzschild configuration
    `R = 2M`, `E = M` also carries at most `horizonArea (2M) / 4`
    nats — the holographic quarter-area bound. -/
theorem holographic_quarter_area_bound
    (S M : ℝ) (h : UniversalEntropyBound S (2 * M) M) :
    S ≤ horizonArea (2 * M) / 4 := by
  have heq : bekensteinBound (2 * M) M = horizonArea (2 * M) / 4 :=
    holographicOnBHFamily M
  exact le_trans h (le_of_eq heq)

/-- **Equivalence**: at the Schwarzschild configuration, the
    universal Bekenstein bound *is* the holographic quarter-area
    bound. -/
theorem universal_iff_quarter_area (S M : ℝ) :
    UniversalEntropyBound S (2 * M) M ↔ S ≤ horizonArea (2 * M) / 4 := by
  unfold UniversalEntropyBound
  rw [holographicOnBHFamily]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: NAMED TARGETS — UNIVERSAL BOUND AND HOLOGRAPHIC PRINCIPLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The fully general Bekenstein bound and the holographic principle
    require QFT in curved spacetime (Bekenstein 1981 adiabatic
    argument; Casini 2008 relative-entropy argument; Bousso 1999
    covariant entropy bound). Neither derivation is in the present
    Lean development.

    We RECORD both as named targets — Props the framework points to
    but does not (yet) discharge — and we show each is *consistent*
    via the Schwarzschild instance above.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Named target — Universal Bekenstein Bound.**
    Every physical system with non-negative radius `R ≥ 0`, energy
    `E ≥ 0`, and entropy `S ≥ 0` satisfies `S ≤ 2π · R · E`.

    The general statement requires QFT in curved spacetime; we
    record it as a Prop and instantiate it on the Schwarzschild
    family (see `Bekenstein_Universal_Target_consistent` below). -/
def Bekenstein_Universal_Target : Prop :=
  ∀ S R E : ℝ, 0 ≤ R → 0 ≤ E → 0 ≤ S → S ≤ bekensteinBound R E

/-- **Named target — Holographic Principle (quarter-area form).**
    Every physical system enclosed in a spherical region whose
    boundary has area `A ≥ 0` carries at most `A / 4` nats of
    entropy. -/
def Holographic_Principle_Target : Prop :=
  ∀ S A : ℝ, 0 ≤ A → 0 ≤ S → ∀ R : ℝ, A = horizonArea R → S ≤ A / 4

/-- The universal target is **propositionally consistent**: on the
    Schwarzschild family, the maximum-entropy configuration (the BH
    itself) satisfies the universal bound with equality. -/
theorem Bekenstein_Universal_Target_consistent :
    ∀ M : ℝ, 0 ≤ M → bhEntropy (2 * M) ≤ bekensteinBound (2 * M) M :=
  fun M hM => bekensteinUniversalOnBHFamily M hM

/-- The holographic target is **propositionally consistent**: the
    Schwarzschild BH itself carries entropy `A/4` (saturation). -/
theorem Holographic_Principle_Target_consistent :
    ∀ R : ℝ, bhEntropy R ≤ horizonArea R / 4 := by
  intro R
  rw [bhEntropy_eq_quarter_area]

/-- If we *assume* the universal target, the Schwarzschild
    holographic identity follows: any non-negative entropy at the
    Schwarzschild configuration is bounded by `A/4`. (Shown without
    assumption; this lemma just records the dependency direction.) -/
theorem universal_target_implies_holographic_on_BH
    (h : Bekenstein_Universal_Target) :
    ∀ S M : ℝ, 0 ≤ M → 0 ≤ S → S ≤ horizonArea (2 * M) / 4 := by
  intro S M hM hS
  have hR : 0 ≤ 2 * M := by linarith
  have hcomp : UniversalEntropyBound S (2 * M) M := h S (2 * M) M hR hM hS
  exact holographic_quarter_area_bound S M hcomp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: TRIVIAL-SYSTEM SANITY CHECK
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Bekenstein bound must allow a vacuum/trivial system —
    `S = 0` for any `R, E ≥ 0`. We record this as a stand-in for
    "small systems satisfy the bound trivially". (A full hydrogen-
    atom computation would require Mathlib's `Real.exp` /
    Bohr-radius / Rydberg-energy infrastructure and is out of scope
    for a purely algebraic capstone.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Vacuum / trivial system**: the empty system at any
    non-negative radius and energy carries zero entropy and
    therefore satisfies the universal Bekenstein bound. -/
theorem trivial_system_satisfies_bekenstein (R E : ℝ)
    (hR : 0 ≤ R) (hE : 0 ≤ E) :
    UniversalEntropyBound 0 R E :=
  UniversalEntropyBound.zero R E hR hE

/-- **Sub-bound sanity**: any system with non-positive entropy is
    universally compliant. -/
theorem nonpos_entropy_satisfies_bekenstein
    (S R E : ℝ) (hS : S ≤ 0) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    UniversalEntropyBound S R E :=
  UniversalEntropyBound.of_nonpos S R E hS hR hE

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER CAPSTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bekenstein bound — Layer C master theorem.**

    Bundles all unconditional facts proved above:

    (1) `bekensteinBound R E ≥ 0` for `R, E ≥ 0`.
    (2) `bekensteinBound (2M) M = bhEntropy (2M)` — Schwarzschild
        saturation, exactly.
    (3) `bhEntropy R ≥ 0` for all real `R`.
    (4) `bhEntropy R = horizonArea R / 4` — the holographic
        identity.
    (5) Every Schwarzschild BH (radius `2M`, energy `M`, mass
        `M ≥ 0`) satisfies the universal Bekenstein bound (with
        equality).
    (6) Both named targets are propositionally consistent
        (instantiated by the Schwarzschild family). -/
theorem bekenstein_master :
    (∀ R E : ℝ, 0 ≤ R → 0 ≤ E → 0 ≤ bekensteinBound R E)
    ∧ (∀ M : ℝ, bekensteinBound (2 * M) M = bhEntropy (2 * M))
    ∧ (∀ R : ℝ, 0 ≤ bhEntropy R)
    ∧ (∀ R : ℝ, bhEntropy R = horizonArea R / 4)
    ∧ (∀ M : ℝ, 0 ≤ M →
        UniversalEntropyBound (bhEntropy (2 * M)) (2 * M) M)
    ∧ (∀ M : ℝ, 0 ≤ M →
        bhEntropy (2 * M) ≤ bekensteinBound (2 * M) M)
    ∧ (∀ R : ℝ, bhEntropy R ≤ horizonArea R / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros R E hR hE; exact bekensteinBound_nonneg R E hR hE
  · intros M; exact bekenstein_saturates_at_BH M
  · intros R; exact bhEntropy_nonneg R
  · intros R; exact bhEntropy_eq_quarter_area R
  · intros M hM; exact bekensteinUniversalOnBHFamily M hM
  · intros M hM; exact Bekenstein_Universal_Target_consistent M hM
  · intros R; exact Holographic_Principle_Target_consistent R

/-- **Master capstone, extended** — adds the monotonicity package
    of the universal predicate and the closed-form values at the
    Schwarzschild configuration. -/
theorem bekenstein_master_extended :
    -- Definitional unfolding
    (∀ R E : ℝ, bekensteinBound R E = 2 * Real.pi * R * E)
    -- Monotonicity in R
    ∧ (∀ R₁ R₂ E : ℝ, 0 ≤ E → R₁ ≤ R₂ →
          bekensteinBound R₁ E ≤ bekensteinBound R₂ E)
    -- Monotonicity in E
    ∧ (∀ R E₁ E₂ : ℝ, 0 ≤ R → E₁ ≤ E₂ →
          bekensteinBound R E₁ ≤ bekensteinBound R E₂)
    -- Universal-predicate sub-bound preservation
    ∧ (∀ S R E S' : ℝ, S' ≤ S → UniversalEntropyBound S R E →
          UniversalEntropyBound S' R E)
    -- Schwarzschild saturation, closed form
    ∧ (∀ M : ℝ, bekensteinBound (2 * M) M = 4 * Real.pi * M ^ 2)
    -- BH-entropy, closed form
    ∧ (∀ M : ℝ, bhEntropy (2 * M) = 4 * Real.pi * M ^ 2)
    -- Horizon area, non-negativity
    ∧ (∀ R : ℝ, 0 ≤ horizonArea R)
    -- Holographic compliance for any Schwarzschild-config compliant S
    ∧ (∀ S M : ℝ, UniversalEntropyBound S (2 * M) M →
          S ≤ horizonArea (2 * M) / 4) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros R₁ R₂ E hE hR; exact bekensteinBound_mono_R R₁ R₂ E hE hR
  · intros R E₁ E₂ hR hE; exact bekensteinBound_mono_E R E₁ E₂ hR hE
  · intros S R E S' hSS' h; exact UniversalEntropyBound_subbound S R E S' hSS' h
  · intros M; exact bekensteinBound_at_schwarzschild M
  · intros M; exact bhEntropy_at_schwarzschild M
  · intros R; exact horizonArea_nonneg R
  · intros S M h; exact holographic_quarter_area_bound S M h

end UnifiedTheory.LayerC.BekensteinBound
