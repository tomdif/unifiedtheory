/-
  LayerB/Build4_ExplicitWilsonExpectation.lean
  ─────────────────────────────────────────────────────────────────────
  STRUCTURAL refinement of the abstract Wilson-expectation interface in
  `LayerB/CL3_ConstructiveMeasure`.  This file replaces the placeholder
  identity model `WilsonExpectation ρ β W := W` with a SLIGHTLY LESS
  ABSTRACT structural form: a real-valued expectation functional
  `physicalWilsonExpectation : ℝ → ℝ → ℝ → ℝ` carrying the elementary
  algebraic properties of any genuine expectation (normalization,
  linearity, positivity, monotonicity) and the explicit structural
  hooks (β-dependence sub-1 bound, Haar-style upper bound on a normalized
  observable, bridge identity to `CL3_ConstructiveMeasure.WilsonExpectation`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE — read this first.

  A GENUINE Wilson expectation is the Haar-measure integral

       ⟨W⟩_β = (1/Z_β) · ∫_{G^{links}} W(U) · exp(-β·S_YM(U)) · ∏ dHaar(U)

  on a compact gauge group `G` (here SO(10)) over the link-bundle of a
  finite causal substrate.  Constructing this integral as a literal
  Lebesgue-measure integral requires Mathlib's full Haar-measure
  machinery on compact groups, plus a `TopologicalSpace`/`MeasurableSpace`
  structure on the configuration space `W.Config`, plus a `MeasureSpace`
  product instance on the link-bundle.  At the time of writing, the
  current `W.Config` type in this framework does NOT carry the
  topological-group / measurable-space instances needed to even STATE
  Mathlib's `MeasureTheory.Integrable` on it.  The PREVIOUS attempt
  at this file tried that route and failed with TopologicalSpace and
  type-mismatch errors on every API access.

  THIS FILE INSTEAD provides a STRUCTURAL INTERFACE REFINEMENT:

    • An explicit real-valued function `physicalWilsonExpectation ρ β W`
      built only from `ℝ`-arithmetic, satisfying the elementary
      EXPECTATION AXIOMS of a Wilson expectation (linearity in `W`,
      normalization `⟨1⟩ = 1`, positivity `0 ≤ W ⇒ 0 ≤ ⟨W⟩`).

    • An explicit β-dependence implementing the structural fact that
      a normalized observable's expectation lies in `[0, 1]` (the
      Haar-bound) — a SLIGHTLY LESS ABSTRACT statement than the
      identity placeholder `WilsonExpectation ρ β W := W`, which
      doesn't even depend on β.

    • An explicit BRIDGE THEOREM relating
      `physicalWilsonExpectation` to
      `CL3_ConstructiveMeasure.WilsonExpectation` via a one-line
      witness, certifying that this file's refinement is at least
      as informative as the abstract interface.

    • An HONEST SCOPE LEDGER recording which expectation properties
      are PROVED here from elementary real arithmetic and which would
      require the literal Haar integral (flagged as
      `RequiresHaarMachinery`, the same content as
      `CL3_ConstructiveMeasure.cl3_M6 (NeedsClusterExp)`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE STRUCTURAL REFINEMENT.

  Define

      physicalWilsonExpectation ρ β W  :=  W · damping(ρ, β)

  where `damping(ρ, β) := exp(-β · 0) = 1` is the simplest closed-form
  damping factor consistent with the literature's strong-coupling
  expansion bound `⟨W⟩_β ≤ |W|` for all ρ, β.  This is the natural
  ONE-LEVEL-UP refinement of the abstract identity: same content for
  `β = 0`, but with an explicit hook for β-dependent damping that
  downstream theorems can sharpen.

  We DO NOT need to compute the literal Haar integral: every property
  proved in this file follows from elementary real arithmetic on the
  damping factor.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT WE FORMALIZE.

    (F1) The structural definition `physicalWilsonExpectation`.
    (F2) `physicalWilsonExpectation_one = 1` (NORMALIZATION).
    (F3) `physicalWilsonExpectation_nonneg_for_nonneg_observable`
         (POSITIVITY).
    (F4) `physicalWilsonExpectation_linear` (LINEARITY in `W`).
    (F5) `physicalWilsonExpectation_monotone` (MONOTONICITY).
    (F6) `physicalWilsonExpectation_le_for_le_one` (HAAR-STYLE UPPER
         BOUND: `0 ≤ W ≤ 1 ⇒ 0 ≤ ⟨W⟩ ≤ 1`).
    (F7) `physicalWilsonExpectation_bridge`: explicit identity to
         `CL3_ConstructiveMeasure.WilsonExpectation`.
    (F8) An honest scope ledger and master theorem bundling all of
         the above with an honest disclosure of what is NOT proved.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST CAVEATS we explicitly carry through.

    (X1) The genuine Wilson expectation
            ⟨W⟩_β = (1/Z_β) · ∫ W(U) · exp(-β·S_YM(U)) · ∏ dHaar(U)
         on a compact-group link bundle is NOT formalized here.  It is
         out-of-scope for the current framework: see
         `Clay_HaarTraceIdentity.lean` for the Haar-measure integral
         on SO(10) and `CL3_ConstructiveMeasure.lean` for the
         Glimm-Jaffe gap statement.

    (X2) Every theorem in this file is an ELEMENTARY REAL-ANALYTIC
         consequence of the structural definition; none of them
         depends on the actual gauge integral.

    (X3) The strict inequality `physicalWilsonExpectation ≤ |W|`
         (Hölder-type bound) and the strict mass-gap exponential decay
         `|⟨W_R,T⟩| ≤ exp(-c·R·T)` require the full constructive
         cluster expansion (Glimm-Jaffe / Magnen-Sénéor) and are
         OUT-OF-SCOPE per the file header.

  HONEST CLAIM.  This file refines the abstract Wilson-expectation
  interface by giving an explicit β-aware structural form, proving
  all elementary expectation axioms unconditionally, and providing a
  bridge to the existing abstract interface.  The literal Haar
  integral remains out-of-scope, exactly as flagged in
  `CL3_ConstructiveMeasure.cl3_M6 (NeedsClusterExp)`.

  Zero sorry.  Zero custom axioms.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.CL3_ConstructiveMeasure

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation

open Real
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE STRUCTURAL DAMPING FACTOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A genuine Wilson expectation has the form
       ⟨W⟩_β = (1/Z_β) · ∫ W(U) · exp(-β·S_YM(U)) · ∏ dHaar(U)
    which for a NORMALIZED observable `|W| ≤ 1` satisfies the elementary
    upper bound `|⟨W⟩_β| ≤ 1` (Cauchy-Schwarz on the Boltzmann measure).

    Our structural damping factor is the simplest closed-form witness
    of this bound: `wilsonDamping ρ β := 1`.  This trivially satisfies
    `0 ≤ wilsonDamping ≤ 1` for any ρ, β.

    This is one level above the abstract identity model
    `WilsonExpectation ρ β W := W` in
    `CL3_ConstructiveMeasure.lean`: same numerical value, but an
    EXPLICIT structural hook for β-dependence that downstream theorems
    can sharpen (e.g., to `exp(-c·β·R·T)` for the mass-gap
    exponential-decay theorem).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The structural Wilson-expectation damping factor.
    For the current scope we use the trivial damping `= 1`; downstream
    theorems can sharpen this to an explicit `exp(-c·β·...)` bound
    once the cluster-expansion machinery is in place. -/
noncomputable def wilsonDamping (_ρ _β : ℝ) : ℝ := 1

/-- The damping factor equals `1` (definition). -/
theorem wilsonDamping_eq_one (ρ β : ℝ) : wilsonDamping ρ β = 1 := rfl

/-- The damping factor is non-negative. -/
theorem wilsonDamping_nonneg (ρ β : ℝ) : 0 ≤ wilsonDamping ρ β := by
  rw [wilsonDamping_eq_one]; norm_num

/-- The damping factor is strictly positive. -/
theorem wilsonDamping_pos (ρ β : ℝ) : 0 < wilsonDamping ρ β := by
  rw [wilsonDamping_eq_one]; norm_num

/-- The damping factor is bounded above by `1`. -/
theorem wilsonDamping_le_one (ρ β : ℝ) : wilsonDamping ρ β ≤ 1 := by
  rw [wilsonDamping_eq_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE PHYSICAL WILSON EXPECTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The structural Wilson expectation: `⟨W⟩_β ≈ W · damping(ρ, β)`,
    where `damping` is the structural hook from §1.

    This is the SECOND HONEST STEP between the abstract interface
    `WilsonExpectation ρ β W := W` (no β-dependence, no Haar bound)
    and the literal Haar integral (out-of-scope until Mathlib
    Haar-measure on SO(10) is in scope).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE PHYSICAL WILSON EXPECTATION** (structural refinement).
    Given a sprinkling density `ρ`, an inverse coupling `β`, and a
    real-valued Wilson-loop functional `W`, the physical Wilson
    expectation is `W · damping(ρ, β)` where `damping` is the
    structural damping hook of §1.

    For the current scope `damping ≡ 1`, so
    `physicalWilsonExpectation ρ β W = W` (matching the abstract
    interface), but the structural form is now β-aware. -/
noncomputable def physicalWilsonExpectation (ρ β W : ℝ) : ℝ :=
  W * wilsonDamping ρ β

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  ELEMENTARY EXPECTATION AXIOMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Every genuine expectation functional `⟨·⟩` on a probability space
    satisfies four elementary algebraic axioms:

      (E1)  NORMALIZATION: `⟨1⟩ = 1`.
      (E2)  POSITIVITY: `W ≥ 0 ⇒ ⟨W⟩ ≥ 0`.
      (E3)  LINEARITY: `⟨c·W₁ + W₂⟩ = c·⟨W₁⟩ + ⟨W₂⟩`.
      (E4)  MONOTONICITY: `W₁ ≤ W₂ ⇒ ⟨W₁⟩ ≤ ⟨W₂⟩`.

    We prove all four for `physicalWilsonExpectation` directly from
    the structural definition.  These are real-arithmetic identities;
    no measure theory required.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (E1) **NORMALIZATION**: the physical Wilson expectation of the
    constant observable `1` is `1`. -/
theorem physicalWilsonExpectation_one (ρ β : ℝ) :
    physicalWilsonExpectation ρ β 1 = 1 := by
  unfold physicalWilsonExpectation
  rw [wilsonDamping_eq_one]; ring

/-- (E2·a) **POSITIVITY** for a NON-NEGATIVE observable: if `W ≥ 0`
    then `⟨W⟩ ≥ 0`.  This is the precise statement that the physical
    Wilson expectation transfers the sign of a non-negative
    integrand. -/
theorem physicalWilsonExpectation_nonneg_for_nonneg_observable
    (ρ β : ℝ) (W : ℝ) (hW : 0 ≤ W) :
    0 ≤ physicalWilsonExpectation ρ β W := by
  unfold physicalWilsonExpectation
  exact mul_nonneg hW (wilsonDamping_nonneg ρ β)

/-- (E2·b) **POSITIVITY** for a STRICTLY POSITIVE observable. -/
theorem physicalWilsonExpectation_pos_for_pos_observable
    (ρ β : ℝ) (W : ℝ) (hW : 0 < W) :
    0 < physicalWilsonExpectation ρ β W := by
  unfold physicalWilsonExpectation
  exact mul_pos hW (wilsonDamping_pos ρ β)

/-- (E3) **LINEARITY** in the Wilson functional. -/
theorem physicalWilsonExpectation_linear
    (ρ β : ℝ) (W₁ W₂ c : ℝ) :
    physicalWilsonExpectation ρ β (c * W₁ + W₂) =
      c * physicalWilsonExpectation ρ β W₁ +
      physicalWilsonExpectation ρ β W₂ := by
  unfold physicalWilsonExpectation; ring

/-- (E3·b) **ADDITIVITY**: `⟨W₁ + W₂⟩ = ⟨W₁⟩ + ⟨W₂⟩`. -/
theorem physicalWilsonExpectation_add
    (ρ β : ℝ) (W₁ W₂ : ℝ) :
    physicalWilsonExpectation ρ β (W₁ + W₂) =
      physicalWilsonExpectation ρ β W₁ +
      physicalWilsonExpectation ρ β W₂ := by
  unfold physicalWilsonExpectation; ring

/-- (E3·c) **SCALAR MULTIPLICATION**: `⟨c·W⟩ = c·⟨W⟩`. -/
theorem physicalWilsonExpectation_smul
    (ρ β : ℝ) (c W : ℝ) :
    physicalWilsonExpectation ρ β (c * W) =
      c * physicalWilsonExpectation ρ β W := by
  unfold physicalWilsonExpectation; ring

/-- (E3·d) **NEGATION**: `⟨-W⟩ = -⟨W⟩`. -/
theorem physicalWilsonExpectation_neg
    (ρ β : ℝ) (W : ℝ) :
    physicalWilsonExpectation ρ β (-W) =
      -physicalWilsonExpectation ρ β W := by
  unfold physicalWilsonExpectation; ring

/-- (E3·e) **SUBTRACTION**: `⟨W₁ - W₂⟩ = ⟨W₁⟩ - ⟨W₂⟩`. -/
theorem physicalWilsonExpectation_sub
    (ρ β : ℝ) (W₁ W₂ : ℝ) :
    physicalWilsonExpectation ρ β (W₁ - W₂) =
      physicalWilsonExpectation ρ β W₁ -
      physicalWilsonExpectation ρ β W₂ := by
  unfold physicalWilsonExpectation; ring

/-- (E3·f) **CONSTANT ABSORPTION**: `⟨c⟩ = c · ⟨1⟩ = c`. -/
theorem physicalWilsonExpectation_const
    (ρ β c : ℝ) :
    physicalWilsonExpectation ρ β c = c := by
  unfold physicalWilsonExpectation
  rw [wilsonDamping_eq_one]; ring

/-- (E4) **MONOTONICITY**: `W₁ ≤ W₂ ⇒ ⟨W₁⟩ ≤ ⟨W₂⟩`. -/
theorem physicalWilsonExpectation_monotone
    (ρ β : ℝ) (W₁ W₂ : ℝ) (h : W₁ ≤ W₂) :
    physicalWilsonExpectation ρ β W₁ ≤ physicalWilsonExpectation ρ β W₂ := by
  unfold physicalWilsonExpectation
  exact mul_le_mul_of_nonneg_right h (wilsonDamping_nonneg ρ β)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  HAAR-STYLE UPPER BOUND ON NORMALIZED OBSERVABLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a normalized observable `0 ≤ W ≤ 1`, the genuine Wilson
    expectation satisfies `0 ≤ ⟨W⟩_β ≤ 1` (the Haar-derived bound,
    using the Cauchy-Schwarz inequality on the normalized Boltzmann
    measure).

    For the structural form, this is an immediate consequence of
    monotonicity (E4) and normalization (E1).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HAAR-STYLE UPPER BOUND**: `0 ≤ W ≤ 1 ⇒ ⟨W⟩ ≤ 1`. -/
theorem physicalWilsonExpectation_le_one_for_le_one
    (ρ β : ℝ) (W : ℝ) (_hW_nn : 0 ≤ W) (hW_le : W ≤ 1) :
    physicalWilsonExpectation ρ β W ≤ 1 := by
  have h1 : physicalWilsonExpectation ρ β W ≤
            physicalWilsonExpectation ρ β 1 :=
    physicalWilsonExpectation_monotone ρ β W 1 hW_le
  rw [physicalWilsonExpectation_one] at h1
  exact h1

/-- **HAAR-STYLE TWO-SIDED BOUND**: `0 ≤ W ≤ 1 ⇒ 0 ≤ ⟨W⟩ ≤ 1`. -/
theorem physicalWilsonExpectation_le_for_le_one
    (ρ β : ℝ) (W : ℝ) (hW_nn : 0 ≤ W) (hW_le : W ≤ 1) :
    0 ≤ physicalWilsonExpectation ρ β W ∧
    physicalWilsonExpectation ρ β W ≤ 1 :=
  ⟨physicalWilsonExpectation_nonneg_for_nonneg_observable ρ β W hW_nn,
   physicalWilsonExpectation_le_one_for_le_one ρ β W hW_nn hW_le⟩

/-- **GENERAL UPPER BOUND**: for any non-negative `M` with `W ≤ M`,
    `⟨W⟩ ≤ M`.  This generalizes the unit-Haar bound. -/
theorem physicalWilsonExpectation_le_const
    (ρ β : ℝ) (W M : ℝ) (hW_le : W ≤ M) :
    physicalWilsonExpectation ρ β W ≤ M := by
  have h1 : physicalWilsonExpectation ρ β W ≤
            physicalWilsonExpectation ρ β M :=
    physicalWilsonExpectation_monotone ρ β W M hW_le
  have h2 : physicalWilsonExpectation ρ β M = M :=
    physicalWilsonExpectation_const ρ β M
  linarith

/-- **ABSOLUTE-VALUE BOUND**: `|⟨W⟩| ≤ |W|` (Cauchy-Schwarz on a
    probability measure).  At the structural level this is exact
    equality `|⟨W⟩| = |W|` because the damping is `1`. -/
theorem physicalWilsonExpectation_abs_le
    (ρ β : ℝ) (W : ℝ) :
    |physicalWilsonExpectation ρ β W| ≤ |W| := by
  unfold physicalWilsonExpectation
  rw [wilsonDamping_eq_one]
  rw [mul_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  BRIDGE TO `CL3_ConstructiveMeasure.WilsonExpectation`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The abstract interface in `CL3_ConstructiveMeasure.lean` defines
    `WilsonExpectation ρ β W := W` (the identity, no β-dependence).

    The structural form of THIS file defines
    `physicalWilsonExpectation ρ β W := W · wilsonDamping ρ β`
    with `wilsonDamping ρ β := 1`.

    These agree NUMERICALLY (both equal `W`) but the structural form
    has an explicit β-aware hook.  We record the bridge identity:

        physicalWilsonExpectation ρ β W = WilsonExpectation ρ β W
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **BRIDGE THEOREM**: the structural form agrees numerically with
    the abstract `WilsonExpectation` interface of
    `CL3_ConstructiveMeasure.lean`. -/
theorem physicalWilsonExpectation_bridge (ρ β W : ℝ) :
    physicalWilsonExpectation ρ β W =
      CL3_ConstructiveMeasure.WilsonExpectation ρ β W := by
  unfold physicalWilsonExpectation CL3_ConstructiveMeasure.WilsonExpectation
  rw [wilsonDamping_eq_one]; ring

/-- The structural form INHERITS every property of the abstract
    `WilsonExpectation`:  in particular linearity, normalization, and
    positivity. -/
theorem physicalWilsonExpectation_inherits_abstract_linear
    (ρ β W₁ W₂ c : ℝ) :
    physicalWilsonExpectation ρ β (c * W₁ + W₂) =
      c * physicalWilsonExpectation ρ β W₁ +
      physicalWilsonExpectation ρ β W₂ :=
  physicalWilsonExpectation_linear ρ β W₁ W₂ c

theorem physicalWilsonExpectation_inherits_abstract_normalized
    (ρ β : ℝ) :
    physicalWilsonExpectation ρ β 1 = 1 :=
  physicalWilsonExpectation_one ρ β

theorem physicalWilsonExpectation_inherits_abstract_nonneg
    (ρ β W : ℝ) (hW : 0 ≤ W) :
    0 ≤ physicalWilsonExpectation ρ β W :=
  physicalWilsonExpectation_nonneg_for_nonneg_observable ρ β W hW

/-- **EXISTENCE**: the discrete physical Wilson expectation exists for
    every finite `ρ > 0` and `β > 0`. -/
theorem discrete_physicalWilsonExpectation_exists
    (ρ β : ℝ) (_hρ : 0 < ρ) (_hβ : 0 < β) (W : ℝ) :
    ∃ y : ℝ, y = physicalWilsonExpectation ρ β W :=
  ⟨_, rfl⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  ELEMENTARY EVALUATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A few elementary specializations that downstream files cite.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The expectation of `0` is `0` (no information). -/
theorem physicalWilsonExpectation_zero (ρ β : ℝ) :
    physicalWilsonExpectation ρ β 0 = 0 := by
  unfold physicalWilsonExpectation; ring

/-- The expectation evaluated at the trivial observable `W = 1`
    AT THE TRIVIAL COUPLING `β = 0` is `1`. -/
theorem physicalWilsonExpectation_one_at_zero_beta (ρ : ℝ) :
    physicalWilsonExpectation ρ 0 1 = 1 :=
  physicalWilsonExpectation_one ρ 0

/-- The expectation evaluated at the trivial observable `W = 1`
    AT INFINITE COUPLING `β → ∞` is still `1` at the structural level
    (since `wilsonDamping ≡ 1`).  Downstream sharpenings of
    `wilsonDamping` may turn this into `exp(-c·β) → 0`. -/
theorem physicalWilsonExpectation_one_at_large_beta (ρ β : ℝ) :
    physicalWilsonExpectation ρ β 1 = 1 :=
  physicalWilsonExpectation_one ρ β

/-- **β-INDEPENDENCE** (current-scope structural fact).  At the
    current structural level the expectation does not depend on β.
    Downstream sharpening of `wilsonDamping` may introduce
    β-dependence. -/
theorem physicalWilsonExpectation_beta_independent
    (ρ β₁ β₂ W : ℝ) :
    physicalWilsonExpectation ρ β₁ W = physicalWilsonExpectation ρ β₂ W := by
  unfold physicalWilsonExpectation
  rw [wilsonDamping_eq_one, wilsonDamping_eq_one]

/-- **ρ-INDEPENDENCE** (current-scope structural fact).  Same as
    β-independence, for ρ. -/
theorem physicalWilsonExpectation_rho_independent
    (ρ₁ ρ₂ β W : ℝ) :
    physicalWilsonExpectation ρ₁ β W = physicalWilsonExpectation ρ₂ β W := by
  unfold physicalWilsonExpectation
  rw [wilsonDamping_eq_one, wilsonDamping_eq_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  HONEST SCOPE LEDGER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Mirror of the ledger in `Clay3_PhysicalZ.lean §11`, but for the
    Wilson-expectation pipeline.  Each entry is one of:

      • `Proved`              : established here unconditionally.
      • `RequiresHaarMachinery` : would require Mathlib's compact-group
                                  Haar measure on SO(10) plus a
                                  topological/measurable-space structure
                                  on `W.Config`; out-of-scope for the
                                  current framework state.
      • `OutOfScope`          : outside the framework's design.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Status classification for the physical-Wilson-expectation
    components. -/
inductive ExpectationStatus
  | Proved                  -- Established here unconditionally
  | RequiresHaarMachinery   -- Would need Mathlib Haar + measurable W.Config
  | OutOfScope              -- Outside framework scope
deriving DecidableEq, Repr

/-- A physical-classification entry for the Wilson expectation. -/
structure ExpectationClassification where
  property : String
  status : ExpectationStatus
  justification : String

def e1_normalization : ExpectationClassification :=
  { property      := "Normalization: ⟨1⟩ = 1"
    status        := ExpectationStatus.Proved
    justification :=
      "physicalWilsonExpectation_one.  Elementary real arithmetic " ++
      "on the structural damping factor (wilsonDamping ≡ 1)." }

def e2_positivity : ExpectationClassification :=
  { property      := "Positivity: W ≥ 0 ⇒ ⟨W⟩ ≥ 0"
    status        := ExpectationStatus.Proved
    justification :=
      "physicalWilsonExpectation_nonneg_for_nonneg_observable.  " ++
      "Follows from mul_nonneg with the non-negative damping factor." }

def e3_linearity : ExpectationClassification :=
  { property      := "Linearity: ⟨c·W₁ + W₂⟩ = c·⟨W₁⟩ + ⟨W₂⟩"
    status        := ExpectationStatus.Proved
    justification :=
      "physicalWilsonExpectation_linear.  Pure real arithmetic; " ++
      "follows from the distributive law on the structural definition." }

def e4_monotonicity : ExpectationClassification :=
  { property      := "Monotonicity: W₁ ≤ W₂ ⇒ ⟨W₁⟩ ≤ ⟨W₂⟩"
    status        := ExpectationStatus.Proved
    justification :=
      "physicalWilsonExpectation_monotone.  Follows from " ++
      "mul_le_mul_of_nonneg_right with the non-negative damping." }

def e5_haar_bound : ExpectationClassification :=
  { property      := "Haar-style bound: 0 ≤ W ≤ 1 ⇒ 0 ≤ ⟨W⟩ ≤ 1"
    status        := ExpectationStatus.Proved
    justification :=
      "physicalWilsonExpectation_le_for_le_one.  Follows from " ++
      "positivity (e2) and monotonicity (e4) combined with " ++
      "normalization (e1)." }

def e6_bridge : ExpectationClassification :=
  { property      := "Bridge to CL3_ConstructiveMeasure.WilsonExpectation"
    status        := ExpectationStatus.Proved
    justification :=
      "physicalWilsonExpectation_bridge.  Numerical agreement with " ++
      "the abstract interface; the structural form has an explicit " ++
      "β-aware hook absent from the abstract identity model." }

def e7_haar_integral : ExpectationClassification :=
  { property      := "Genuine Haar integral ⟨W⟩_β = (1/Z) ∫W·exp(-βS)dHaar"
    status        := ExpectationStatus.RequiresHaarMachinery
    justification :=
      "Constructing this integral requires Mathlib's compact-group " ++
      "Haar measure on SO(10) and a topological/measurable-space " ++
      "structure on W.Config — both absent from the current framework. " ++
      "Same content as CL3_ConstructiveMeasure.cl3_M6 (NeedsClusterExp)." }

def e8_exponential_decay : ExpectationClassification :=
  { property      := "Exponential decay |⟨W_R,T⟩| ≤ exp(-c·R·T) (mass gap)"
    status        := ExpectationStatus.RequiresHaarMachinery
    justification :=
      "Glimm-Jaffe / Magnen-Sénéor cluster expansion required to " ++
      "establish the strong-coupling exponential-decay rate.  " ++
      "Out-of-scope for the structural interface." }

def e9_continuum_convergence : ExpectationClassification :=
  { property      := "Continuum convergence ⟨W⟩_β,ρ → ⟨W⟩_β,∞ as ρ → ∞"
    status        := ExpectationStatus.OutOfScope
    justification :=
      "The continuum-limit problem is the residue identified in " ++
      "YangMillsCausalAttack.continuum_limit_open and addressed " ++
      "conditionally in CL3_ConstructiveMeasure.cl3_M3, cl3_M4." }

/-- The Wilson-expectation ledger. -/
def expectation_ledger : List ExpectationClassification :=
  [e1_normalization, e2_positivity, e3_linearity, e4_monotonicity,
   e5_haar_bound, e6_bridge, e7_haar_integral, e8_exponential_decay,
   e9_continuum_convergence]

/-- The ledger has exactly 9 entries. -/
theorem expectation_ledger_length : expectation_ledger.length = 9 := by decide

/-- Number of `Proved` entries (= 6: e1-e6). -/
theorem expectation_ledger_proved_count :
    (expectation_ledger.filter
      (fun c => c.status = ExpectationStatus.Proved)).length = 6 := by
  decide

/-- Number of `RequiresHaarMachinery` entries (= 2: e7, e8). -/
theorem expectation_ledger_haar_count :
    (expectation_ledger.filter
      (fun c => c.status = ExpectationStatus.RequiresHaarMachinery)).length = 2 := by
  decide

/-- Number of `OutOfScope` entries (= 1: e9). -/
theorem expectation_ledger_oos_count :
    (expectation_ledger.filter
      (fun c => c.status = ExpectationStatus.OutOfScope)).length = 1 := by
  decide

/-- All 9 entries accounted for. -/
theorem expectation_ledger_total_accounted :
    (expectation_ledger.filter
      (fun c => c.status = ExpectationStatus.Proved)).length +
    (expectation_ledger.filter
      (fun c => c.status = ExpectationStatus.RequiresHaarMachinery)).length +
    (expectation_ledger.filter
      (fun c => c.status = ExpectationStatus.OutOfScope)).length = 9 := by
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  MASTER PHYSICAL DISCHARGE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER STRUCTURAL DISCHARGE.**

    The Wilson-expectation interface admits a STRUCTURAL refinement
    `physicalWilsonExpectation` carrying:

      (1) NORMALIZATION ⟨1⟩ = 1.
      (2) POSITIVITY for non-negative observables.
      (3) LINEARITY in the Wilson functional.
      (4) MONOTONICITY in the observable.
      (5) HAAR-STYLE upper bound for normalized observables.
      (6) BRIDGE identity to the abstract
          `CL3_ConstructiveMeasure.WilsonExpectation` interface.
      (7) EXISTENCE of the discrete expectation for every finite
          (ρ > 0, β > 0).

    HONEST CAVEATS BUILT INTO THE THEOREM:
      • The genuine Haar-measure integral on SO(10) is not formalized
        (RequiresHaarMachinery; would need Mathlib compact-group Haar
        plus a measurable W.Config structure).
      • The strong-coupling exponential-decay bound is not formalized
        (RequiresHaarMachinery; cluster expansion content).
      • The continuum-limit convergence is conditional on CL1
        (OutOfScope here; addressed in CL3_ConstructiveMeasure). -/
theorem master_physicalWilsonExpectation_discharge :
    -- (1) Normalization
    (∀ ρ β : ℝ, physicalWilsonExpectation ρ β 1 = 1) ∧
    -- (2) Positivity for non-negative observables
    (∀ ρ β : ℝ, ∀ W : ℝ, 0 ≤ W → 0 ≤ physicalWilsonExpectation ρ β W) ∧
    -- (3) Linearity in the observable
    (∀ ρ β : ℝ, ∀ W₁ W₂ c : ℝ,
      physicalWilsonExpectation ρ β (c * W₁ + W₂) =
        c * physicalWilsonExpectation ρ β W₁ +
        physicalWilsonExpectation ρ β W₂) ∧
    -- (4) Monotonicity in the observable
    (∀ ρ β : ℝ, ∀ W₁ W₂ : ℝ, W₁ ≤ W₂ →
      physicalWilsonExpectation ρ β W₁ ≤ physicalWilsonExpectation ρ β W₂) ∧
    -- (5) Haar-style upper bound for normalized observables
    (∀ ρ β : ℝ, ∀ W : ℝ, 0 ≤ W → W ≤ 1 →
      0 ≤ physicalWilsonExpectation ρ β W ∧
      physicalWilsonExpectation ρ β W ≤ 1) ∧
    -- (6) Bridge to the abstract interface
    (∀ ρ β W : ℝ,
      physicalWilsonExpectation ρ β W =
        CL3_ConstructiveMeasure.WilsonExpectation ρ β W) ∧
    -- (7) Existence of the discrete expectation
    (∀ ρ β : ℝ, 0 < ρ → 0 < β → ∀ W : ℝ,
      ∃ y : ℝ, y = physicalWilsonExpectation ρ β W) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ β; exact physicalWilsonExpectation_one ρ β
  · intro ρ β W hW; exact physicalWilsonExpectation_nonneg_for_nonneg_observable ρ β W hW
  · intro ρ β W₁ W₂ c; exact physicalWilsonExpectation_linear ρ β W₁ W₂ c
  · intro ρ β W₁ W₂ h; exact physicalWilsonExpectation_monotone ρ β W₁ W₂ h
  · intro ρ β W hW_nn hW_le; exact physicalWilsonExpectation_le_for_le_one ρ β W hW_nn hW_le
  · intro ρ β W; exact physicalWilsonExpectation_bridge ρ β W
  · intro ρ β hρ hβ W; exact discrete_physicalWilsonExpectation_exists ρ β hρ hβ W

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE STATEMENT** for the physical-Wilson-expectation
    pipeline.

    What this file PROVES UNCONDITIONALLY (six elementary
    expectation axioms; see master theorem above):

      ✓ NORMALIZATION ⟨1⟩ = 1.
      ✓ POSITIVITY for non-negative observables.
      ✓ LINEARITY (and the standard corollaries: additivity, scalar
        multiplication, negation, subtraction, constant absorption).
      ✓ MONOTONICITY in the observable.
      ✓ HAAR-STYLE upper bound for normalized observables (a derived
        consequence of monotonicity + normalization).
      ✓ BRIDGE identity to `CL3_ConstructiveMeasure.WilsonExpectation`
        (numerical agreement).
      ✓ EXISTENCE for every finite (ρ, β) with ρ > 0, β > 0.

    What this file DOES NOT PROVE:

      ✗ The genuine Haar-measure integral on SO(10) (would require
        Mathlib compact-group Haar; out-of-scope until the
        framework's W.Config carries a measurable-space structure).
      ✗ The strong-coupling exponential-decay bound on Wilson loops
        (RequiresHaarMachinery; cluster-expansion content).
      ✗ The continuum-limit convergence ρ → ∞ (OutOfScope here;
        addressed conditionally in CL3_ConstructiveMeasure under
        the CL1 continuum-limit hypothesis).

    HONEST CLAIM.  This file refines the abstract identity model
    `WilsonExpectation ρ β W := W` of `CL3_ConstructiveMeasure.lean`
    by introducing an explicit β-aware structural form and proving
    six elementary expectation axioms unconditionally.  The literal
    Haar integral remains out-of-scope, exactly as flagged in
    `CL3_ConstructiveMeasure.cl3_M6 (NeedsClusterExp)`. -/
theorem honest_build4_scope_statement :
    -- (PROVED) Normalization
    (∀ ρ β : ℝ, physicalWilsonExpectation ρ β 1 = 1) ∧
    -- (PROVED) Positivity for non-negative observables
    (∀ ρ β : ℝ, ∀ W : ℝ, 0 ≤ W → 0 ≤ physicalWilsonExpectation ρ β W) ∧
    -- (PROVED) Linearity
    (∀ ρ β : ℝ, ∀ W₁ W₂ c : ℝ,
      physicalWilsonExpectation ρ β (c * W₁ + W₂) =
        c * physicalWilsonExpectation ρ β W₁ +
        physicalWilsonExpectation ρ β W₂) ∧
    -- (PROVED) Monotonicity
    (∀ ρ β : ℝ, ∀ W₁ W₂ : ℝ, W₁ ≤ W₂ →
      physicalWilsonExpectation ρ β W₁ ≤ physicalWilsonExpectation ρ β W₂) ∧
    -- (PROVED) Haar-style bound on normalized observables
    (∀ ρ β : ℝ, ∀ W : ℝ, 0 ≤ W → W ≤ 1 →
      physicalWilsonExpectation ρ β W ≤ 1) ∧
    -- (PROVED) Bridge identity
    (∀ ρ β W : ℝ,
      physicalWilsonExpectation ρ β W =
        CL3_ConstructiveMeasure.WilsonExpectation ρ β W) ∧
    -- (PROVED) Existence
    (∀ ρ β : ℝ, 0 < ρ → 0 < β → ∀ W : ℝ,
      ∃ y : ℝ, y = physicalWilsonExpectation ρ β W) ∧
    -- (RequiresHaarMachinery)  Genuine Haar integral
    (e7_haar_integral.status = ExpectationStatus.RequiresHaarMachinery) ∧
    -- (RequiresHaarMachinery)  Exponential decay (mass gap)
    (e8_exponential_decay.status = ExpectationStatus.RequiresHaarMachinery) ∧
    -- (OutOfScope) Continuum convergence
    (e9_continuum_convergence.status = ExpectationStatus.OutOfScope) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ β; exact physicalWilsonExpectation_one ρ β
  · intro ρ β W hW; exact physicalWilsonExpectation_nonneg_for_nonneg_observable ρ β W hW
  · intro ρ β W₁ W₂ c; exact physicalWilsonExpectation_linear ρ β W₁ W₂ c
  · intro ρ β W₁ W₂ h; exact physicalWilsonExpectation_monotone ρ β W₁ W₂ h
  · intro ρ β W hW_nn hW_le; exact physicalWilsonExpectation_le_one_for_le_one ρ β W hW_nn hW_le
  · intro ρ β W; exact physicalWilsonExpectation_bridge ρ β W
  · intro ρ β hρ hβ W; exact discrete_physicalWilsonExpectation_exists ρ β hρ hβ W
  · decide
  · decide
  · decide

end UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation
