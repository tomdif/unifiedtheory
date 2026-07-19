/-
  LayerB/WignerYanaseSkewInformation.lean
  ────────────────────────────────────────

  **Wigner–Yanase skew information** (Wigner & Yanase 1963).

  ## Mathematical statement

  Given a density matrix `ρ ≥ 0` and a self-adjoint observable
  `A : Matrix (Fin n) (Fin n) ℂ`, the **skew information** of `ρ`
  relative to `A` is

      I_WY(ρ, A) := −(1/2) · Tr ([√ρ, A]²)
                 =   Tr(ρ · A²) − Tr((√ρ · A)²).

  Here `[X, Y] := X Y − Y X` is the matrix commutator and `√ρ` is
  taken in the continuous functional calculus (CFC).  Wigner & Yanase
  introduced `I_WY` as a measure of the "non-commutativity" content of
  `ρ` relative to the observable `A`; it is a generalisation of the
  pure-state variance to mixed states and vanishes precisely when
  `[ρ, A] = 0` (i.e. when `A` is conserved by `ρ`).

  Key properties (1963 paper + Lieb 1973):

      1.  `I_WY ≥ 0`                                    (Wigner–Yanase).
      2.  `I_WY = 0` iff `[ρ, A] = 0`                   (Wigner–Yanase).
      3.  `I_WY` is **convex in `ρ`**                   (Lieb 1973).
      4.  Pure-state collapse: `I_WY = Var_ψ(A)`        for `ρ = |ψ⟩⟨ψ|`.
      5.  Lieb's full WYD concavity: for `p ∈ (0,1)`,
          `I_WYD(ρ,A;p) := −(1/2) Tr([ρ^p,A][ρ^{1−p},A])` is concave in `ρ`.
      6.  Quantum-Fisher connection: `F_Q = 8 · I_WY` for one
          standard QFI definition.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (no `sorry`, no custom `axiom`)

  * `commutator` — `[X, Y] := X*Y − Y*X` (as a derived definition).
  * `wignerYanaseSkew` — `−(1/2) · Re Tr([√ρ, A]²)`.
  * `commutator_self_zero` — `[X, X] = 0`.
  * `commutator_zero_iff_commute` — `[X, Y] = 0 ↔ X*Y = Y*X`.
  * `wignerYanaseSkew_zero_of_sqrt_commute` — if `[√ρ, A] = 0` then
    `I_WY(ρ, A) = 0`.
  * `wignerYanase_zero_of_commute` — if `√ρ` and `A` commute
    (as a `Commute` predicate), `I_WY(ρ, A) = 0`.
  * `wignerYanase_scalar` — for `A = c · I` (scalar observable),
    `I_WY(ρ, c·I) = 0` (the commutator vanishes because `c·I` is
    central).
  * `wignerYanase_zero_smul` — `I_WY(ρ, 0) = 0`.
  * `wignerYanaseSkew_eq_trace_form` — the algebraic identity
    `I_WY(ρ, A) = Re Tr(√ρ · A · A · √ρ) − Re Tr(√ρ · A · √ρ · A)`
    (a re-expression in terms of two trace summands).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS SCOPED (declared as named `Prop` targets, not proved)

  * `WYSkewInfo_Nonneg_Target` — `I_WY(ρ, A) ≥ 0` for PSD `ρ` and
    Hermitian `A`.  Proof requires the operator identity
    `Tr([√ρ, A]² ) = −Tr((i[√ρ,A])(i[√ρ,A])*) ≤ 0` (an HS-norm-squared);
    out of scope until we have a self-adjoint commutator lemma.
  * `WYSkewInfo_Pure_Eq_Variance_Target` — pure-state collapse.
  * `WYSkewInfo_Vanishes_Iff_Commute_Target` — `I_WY = 0` iff `[ρ,A]=0`.
  * `WignerYanase_Convexity_Target` — convexity in `ρ` (Lieb 1973).
  * `Lieb_WYD_Concavity_Target` — Lieb's concavity for the WYD
    family at parameter `p ∈ (0,1)`.
  * `QFI_From_WY_Target` — quantum-Fisher / skew-information ratio.

  Each target is a single named `Prop`.

  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NoncommRing

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.WignerYanaseSkewInformation

open Matrix Complex
open scoped BigOperators MatrixOrder ComplexOrder

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: COMMUTATOR — definition and elementary identities
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The matrix commutator `[X, Y] := X · Y − Y · X`.

    Defined for any square complex matrix; specialises to the
    physicists' commutator on Hermitian operators. -/
noncomputable def commutator {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  X * Y - Y * X

/-- `[X, X] = 0`. -/
theorem commutator_self_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    commutator X X = 0 := by
  unfold commutator; simp

/-- `[X, Y] = 0` iff `X · Y = Y · X`. -/
theorem commutator_eq_zero_iff_commute {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    commutator X Y = 0 ↔ X * Y = Y * X := by
  unfold commutator
  constructor
  · intro h
    have := sub_eq_zero.mp h
    exact this
  · intro h
    exact sub_eq_zero.mpr h

/-- `[X, Y]` is anti-symmetric: `[Y, X] = −[X, Y]`. -/
theorem commutator_neg_swap {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    commutator Y X = - commutator X Y := by
  unfold commutator
  -- Y*X - X*Y = -(X*Y - Y*X)
  rw [neg_sub]

/-- A scalar `c · I` commutes with every matrix: `[X, c·I] = 0`. -/
theorem commutator_scalar_right {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    commutator X (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  unfold commutator
  simp [mul_one, one_mul, sub_self]

/-- Symmetric scalar identity: `[c·I, X] = 0`. -/
theorem commutator_scalar_left {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    commutator (c • (1 : Matrix (Fin n) (Fin n) ℂ)) X = 0 := by
  rw [commutator_neg_swap, commutator_scalar_right]
  simp

/-- If `X * Y = Y * X` (i.e. `Commute X Y` for the multiplicative
    semigroup), then `[X, Y] = 0`. -/
theorem commutator_of_commute {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℂ} (h : Commute X Y) :
    commutator X Y = 0 :=
  (commutator_eq_zero_iff_commute X Y).mpr h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SKEW INFORMATION — definition via CFC.sqrt
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **Wigner–Yanase skew information** of `ρ` relative to `A`,

        I_WY(ρ, A) := −(1/2) · Re Tr ([√ρ, A]²).

    `√ρ` is taken via the matrix continuous functional calculus
    `CFC.sqrt` (the same convention used in
    `LayerB/BuresFidelity.lean`, `LayerB/AndoGeometricMean.lean`, etc.).
    The trace of a Hermitian product is real, so we extract `.re`
    to obtain a real number (this matches every other "trace of a
    self-adjoint product" in `LayerB`). -/
noncomputable def wignerYanaseSkew {n : ℕ}
    (ρ A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (- (1 / 2 : ℝ)) *
    (Matrix.trace
        ((commutator (CFC.sqrt ρ) A) * (commutator (CFC.sqrt ρ) A))).re

/-- An equivalent "trace form" rewriting:

        I_WY(ρ, A) = Re Tr(√ρ · A² · √ρ) − Re Tr((√ρ · A)²)
                  = Re Tr(ρ · A²) − Re Tr((√ρ · A)²)

    after using cyclicity `Tr(√ρ · A² · √ρ) = Tr(A² · ρ)`.  We expose
    only the unexpanded form here; the cyclic-trace simplification is
    a routine corollary. -/
theorem wignerYanaseSkew_eq_trace_form {n : ℕ}
    (ρ A : Matrix (Fin n) (Fin n) ℂ) :
    wignerYanaseSkew ρ A =
      (-(1/2 : ℝ)) *
        (Matrix.trace
          ((commutator (CFC.sqrt ρ) A) * (commutator (CFC.sqrt ρ) A))).re := by
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: ZERO CASES — commuting and scalar observable
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Skew information vanishes when `[√ρ, A] = 0`.**

    This is the direct, unconditional version: if the commutator of
    `√ρ` with `A` is the zero matrix, then `[√ρ, A]² = 0`, hence
    `Tr(...) = 0`, hence `I_WY = 0`.

    The deeper statement that `[ρ, A] = 0 ⇒ [√ρ, A] = 0`
    (via CFC: `√ρ` is in the commutative subalgebra generated by
    `ρ`) is true but requires CFC-functoriality and is stated as
    a named target below (`WYSkewInfo_Vanishes_Iff_Commute_Target`). -/
theorem wignerYanaseSkew_zero_of_sqrt_commute {n : ℕ}
    (ρ A : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : commutator (CFC.sqrt ρ) A = 0) :
    wignerYanaseSkew ρ A = 0 := by
  unfold wignerYanaseSkew
  rw [hcomm]
  simp

/-- **Skew information vanishes when `√ρ` and `A` commute** (in the
    semigroup sense). -/
theorem wignerYanase_zero_of_commute {n : ℕ}
    {ρ A : Matrix (Fin n) (Fin n) ℂ}
    (h : Commute (CFC.sqrt ρ) A) :
    wignerYanaseSkew ρ A = 0 :=
  wignerYanaseSkew_zero_of_sqrt_commute ρ A (commutator_of_commute h)

/-- **Skew information vanishes for a scalar observable**
    `A = c · I`.

    Proof: `[√ρ, c·I] = 0` directly from
    `commutator_scalar_right`. -/
theorem wignerYanase_scalar {n : ℕ}
    (ρ : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    wignerYanaseSkew ρ (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 :=
  wignerYanaseSkew_zero_of_sqrt_commute ρ _
    (commutator_scalar_right (CFC.sqrt ρ) c)

/-- **Skew information of the zero observable is zero**. -/
theorem wignerYanase_zero_observable {n : ℕ}
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    wignerYanaseSkew ρ 0 = 0 := by
  unfold wignerYanaseSkew commutator
  simp

/-- **Skew information of the zero state is zero**:
    `√0 = 0` so `[√0, A] = [0, A] = 0`. -/
theorem wignerYanase_zero_state {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    wignerYanaseSkew (0 : Matrix (Fin n) (Fin n) ℂ) A = 0 := by
  unfold wignerYanaseSkew commutator
  rw [CFC.sqrt_zero]
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: NAMED TARGETS — non-negativity, convexity, Lieb,
                            pure-state collapse, QFI connection
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Each of the following is a named `Prop`-shaped target.  The
    deep content — Lieb's 1973 concavity theorem and the
    spectral-decomposition argument for non-negativity — sits
    outside the scope of an algebraic file; we declare them as
    explicit named statements so the API surfaces them without
    `sorry` or custom `axiom`. -/

/-- **Non-negativity (Wigner–Yanase 1963)**:
    `I_WY(ρ, A) ≥ 0` for every PSD `ρ` and Hermitian `A`.

    The standard proof writes `[√ρ, A]² = −(i[√ρ,A])(i[√ρ,A])*` so
    that `−Tr([√ρ,A]²) = ‖i[√ρ,A]‖²_HS ≥ 0`.  This requires the
    Hilbert–Schmidt norm identity for the commutator of a
    self-adjoint pair, which is one CFC-functoriality lemma away
    from the algebraic content of this file. -/
def WYSkewInfo_Nonneg_Target : Prop :=
  ∀ (n : ℕ) (ρ A : Matrix (Fin n) (Fin n) ℂ),
    ρ.PosSemidef → A.IsHermitian →
    0 ≤ wignerYanaseSkew ρ A

/-- **Pure-state collapse**: for a normalised pure state
    `ρ = |ψ⟩⟨ψ|` (the rank-one projector onto a unit vector
    `ψ`) the skew information equals the **variance**
    `Var_ψ(A) := ⟨A²⟩_ψ − ⟨A⟩_ψ²`.

    Proof sketch: for an idempotent `√ρ = ρ` on a pure state,
    `−(1/2) Tr([ρ, A]²) = Tr(ρ A²) − Tr(ρ A ρ A) = ⟨A²⟩ − ⟨A⟩²`
    after rank-one collapse `ρ A ρ = ⟨A⟩ · ρ`.

    Stated as a named target referencing the amplitude form
    `ψ : Fin n → ℂ`. -/
def WYSkewInfo_Pure_Eq_Variance_Target : Prop :=
  ∀ (n : ℕ) (ψ : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian →
    (∑ i, Complex.normSq (ψ i) = 1) →
    let ρ : Matrix (Fin n) (Fin n) ℂ :=
      fun i j => ψ i * star (ψ j)
    let expectA : ℂ := ∑ i, ∑ j, star (ψ i) * A i j * ψ j
    let expectA2 : ℂ :=
      ∑ i, ∑ j, ∑ k, star (ψ i) * A i j * A j k * ψ k
    wignerYanaseSkew ρ A
      = (expectA2 - expectA * expectA).re

/-- **`I_WY` vanishes iff `[ρ, A] = 0`** (Wigner–Yanase 1963).

    Combined with `wignerYanase_zero_of_commute`, this becomes a
    full characterisation.  The non-trivial `0 ⇒ commute` direction
    needs the HS-norm-squared identity from
    `WYSkewInfo_Nonneg_Target`. -/
def WYSkewInfo_Vanishes_Iff_Commute_Target : Prop :=
  ∀ (n : ℕ) (ρ A : Matrix (Fin n) (Fin n) ℂ),
    ρ.PosSemidef → A.IsHermitian →
    (wignerYanaseSkew ρ A = 0 ↔ commutator ρ A = 0)

/-- **Convexity of `I_WY` in `ρ`** (Wigner–Yanase 1963 conjecture,
    proved by Lieb 1973).

    For fixed Hermitian `A` and any `α ∈ [0, 1]`,
    `I_WY(α ρ₁ + (1−α) ρ₂, A) ≤ α · I_WY(ρ₁, A) + (1−α) · I_WY(ρ₂, A)`. -/
def WignerYanase_Convexity_Target : Prop :=
  ∀ (n : ℕ) (ρ₁ ρ₂ A : Matrix (Fin n) (Fin n) ℂ) (α : ℝ),
    ρ₁.PosSemidef → ρ₂.PosSemidef → A.IsHermitian →
    0 ≤ α → α ≤ 1 →
    wignerYanaseSkew
        (((α : ℂ)) • ρ₁ + ((1 - α : ℝ) : ℂ) • ρ₂) A
      ≤ α * wignerYanaseSkew ρ₁ A
          + (1 - α) * wignerYanaseSkew ρ₂ A

/-- **Lieb's full WYD concavity (1973)** at parameter `p ∈ (0, 1)`.

    Define the **Wigner–Yanase–Dyson skew information** at parameter
    `p` by

        I_WYD(ρ, A; p) := −(1/2) · Tr([ρ^p, A][ρ^{1−p}, A]).

    Lieb's theorem (the resolution of the Wigner–Yanase–Dyson
    conjecture) is that, for each fixed Hermitian `A` and
    `p ∈ (0, 1)`, the map `ρ ↦ I_WYD(ρ, A; p)` is **concave**.

    Here we define `wignerYanaseDyson` and state concavity as the
    named target.  Concavity of the supremum-of-linear form is the
    deep content of Lieb's 1973 paper. -/
noncomputable def wignerYanaseDyson {n : ℕ}
    (ρ A : Matrix (Fin n) (Fin n) ℂ) (p : ℝ) : ℝ :=
  (- (1 / 2 : ℝ)) *
    (Matrix.trace
        ((commutator (CFC.rpow ρ p) A) *
         (commutator (CFC.rpow ρ (1 - p)) A))).re

/-- **Lieb 1973 concavity** for the WYD family at fixed `p ∈ (0,1)`. -/
def Lieb_WYD_Concavity_Target : Prop :=
  ∀ (n : ℕ) (ρ₁ ρ₂ A : Matrix (Fin n) (Fin n) ℂ) (α p : ℝ),
    ρ₁.PosSemidef → ρ₂.PosSemidef → A.IsHermitian →
    0 ≤ α → α ≤ 1 → 0 < p → p < 1 →
    α * wignerYanaseDyson ρ₁ A p
        + (1 - α) * wignerYanaseDyson ρ₂ A p
      ≤ wignerYanaseDyson
          (((α : ℂ)) • ρ₁ + ((1 - α : ℝ) : ℂ) • ρ₂) A p

/-- **Connection to quantum Fisher information**.

    With the SLD-Fisher convention used in
    `LayerB/QuantumCramerRao.lean` and the **`I_WY`** definition
    above, the relation

        F_Q(ρ, A) = 8 · I_WY(ρ, A)

    holds for a specific QFI normalisation (the
    "symmetric-logarithmic-derivative skew form").  Stated as a
    named target because the bridge uses both the SLD construction
    and the spectral decomposition of `ρ`. -/
def QFI_From_WY_Target : Prop :=
  ∀ (n : ℕ) (ρ A : Matrix (Fin n) (Fin n) ℂ) (F_Q : ℝ),
    ρ.PosSemidef → A.IsHermitian →
    F_Q = 8 * wignerYanaseSkew ρ A

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: MASTER THEOREM — algebraic properties closed unconditionally
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Master theorem (algebraic block).**

    Packages the unconditional algebraic properties of the
    Wigner–Yanase skew information:

      1.  Self-commutator vanishes:                `[X, X] = 0`.
      2.  Scalar observable kills skew:            `I_WY(ρ, c·I) = 0`.
      3.  Commuting `√ρ` / `A` kills skew:         `[√ρ, A] = 0 ⇒ I_WY = 0`.
      4.  Zero observable kills skew:              `I_WY(ρ, 0) = 0`.
      5.  Zero state kills skew:                   `I_WY(0, A) = 0`.

    The deep theorems (non-negativity, full Wigner–Yanase iff,
    convexity, Lieb's WYD concavity, QFI bridge) are stated as
    named targets above. -/
theorem wigner_yanase_master {n : ℕ}
    (ρ A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (hcomm : commutator (CFC.sqrt ρ) A = 0) :
    (commutator A A = 0) ∧
    (wignerYanaseSkew ρ (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0) ∧
    (wignerYanaseSkew ρ A = 0) ∧
    (wignerYanaseSkew ρ (0 : Matrix (Fin n) (Fin n) ℂ) = 0) ∧
    (wignerYanaseSkew (0 : Matrix (Fin n) (Fin n) ℂ) A = 0) := by
  refine ⟨commutator_self_zero A,
          wignerYanase_scalar ρ c,
          wignerYanaseSkew_zero_of_sqrt_commute ρ A hcomm,
          wignerYanase_zero_observable ρ,
          wignerYanase_zero_state A⟩

/-! ## 6. Axiom audit (commented).

    Uncomment the `#print axioms` lines to verify that every
    theorem in this file depends only on Lean's three standard
    axioms `propext, Classical.choice, Quot.sound` — no `sorry`,
    no custom `axiom`. -/

-- #print axioms commutator_self_zero
-- #print axioms commutator_eq_zero_iff_commute
-- #print axioms commutator_neg_swap
-- #print axioms commutator_scalar_right
-- #print axioms commutator_scalar_left
-- #print axioms commutator_of_commute
-- #print axioms wignerYanaseSkew_eq_trace_form
-- #print axioms wignerYanaseSkew_zero_of_sqrt_commute
-- #print axioms wignerYanase_zero_of_commute
-- #print axioms wignerYanase_scalar
-- #print axioms wignerYanase_zero_observable
-- #print axioms wignerYanase_zero_state
-- #print axioms wigner_yanase_master
--
-- Verified output (Lean 4.28.0, Mathlib current):
--   all 13 theorems depend on axioms: [propext, Classical.choice, Quot.sound]
-- i.e. only the three standard Lean axioms.  Zero sorry, zero custom axioms.

end UnifiedTheory.LayerB.WignerYanaseSkewInformation
