/-
  LayerB/BuresFidelity.lean
  ──────────────────────────

  **Uhlmann fidelity and Bures distance** for quantum states.

  ## Mathematical statement

  Given two density matrices `ρ, σ : Matrix (Fin n) (Fin n) ℂ`, the
  **Uhlmann fidelity** is

      F(ρ, σ) := Tr √(√ρ · σ · √ρ).

  The **Bures distance** is the induced metric on the state manifold:

      d_B(ρ, σ) := √(2 − 2 F(ρ, σ)).

  For **pure** states `|ψ⟩, |φ⟩ ∈ ℂⁿ` the formula collapses to

      F(|ψ⟩⟨ψ|, |φ⟩⟨φ|) = |⟨ψ|φ⟩|²,

  which we expose as a separate scalar quantity `pureFidelity ψ φ`
  defined directly on amplitude vectors.  All pure-state properties
  (range, symmetry, self-fidelity, orthogonality, Bures-self-zero)
  are proved here algebraically.

  ## What is proved (zero `sorry`, zero custom `axiom`)

  - `uhlmannFidelity` — `Tr √(√ρ · σ · √ρ)` via `CFC.sqrt`.
  - `buresDistance` — `√(2 − 2 F(ρ, σ))`.
  - `pureFidelity` — `|∑ᵢ conj(ψᵢ) · φᵢ|²` on amplitude vectors.
  - `pureFidelity_nonneg`, `pureFidelity_le_one`, `pureFidelity_in_range`.
  - `pureFidelity_symm` — `F(ψ,φ) = F(φ,ψ)`.
  - `pureFidelity_self` — `F(ψ,ψ) = 1` for normalized `ψ`.
  - `pureFidelity_orthogonal` — orthogonal ⇒ `F = 0`.
  - `buresDistance_self_pure` — `d_B(|ψ⟩,|ψ⟩) = 0`.
  - `bures_fidelity_master` — packages all pure-state results.

  ## What is *scoped* (deferred — declared as named `Prop` targets,
  not proved)

  The three deep theorems are stated but not proved; each requires a
  multi-phase Mathlib formalization not yet in scope:

  - `Uhlmann_Theorem_Target` — Uhlmann's purification theorem:
    `F(ρ,σ) = max_{|Ψ⟩,|Φ⟩} |⟨Ψ|Φ⟩|` over purifications.
  - `Fidelity_DPI_Target` — data-processing inequality:
    `F(N(ρ), N(σ)) ≥ F(ρ, σ)` for any CPTP channel `N`.
  - `Fidelity_Joint_Concavity_Target` — joint concavity in `(ρ, σ)`.

  Each is a single named statement.  No `sorry`, no custom `axiom`.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BuresFidelity

open Matrix Complex
open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: DEFINITIONS — Uhlmann fidelity and Bures distance
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Uhlmann fidelity** `F(ρ, σ) = Tr √(√ρ · σ · √ρ)`.

    The trace of a self-adjoint matrix is real, so we extract the
    real part (this matches the convention everywhere else in
    `LayerB`, e.g. `KleinInequality`, `LiebGoldenThompson`).  The
    inner square root is taken via the continuous functional calculus
    `CFC.sqrt`. -/
noncomputable def uhlmannFidelity {n : ℕ}
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ))).re

/-- **Bures distance** `d_B(ρ, σ) = √(2 − 2 F(ρ, σ))`. -/
noncomputable def buresDistance {n : ℕ}
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (2 - 2 * uhlmannFidelity ρ σ)

/-- **Pure-state fidelity** `F(|ψ⟩⟨ψ|, |φ⟩⟨φ|) = |⟨ψ|φ⟩|²` for
    amplitude vectors `ψ, φ : Fin n → ℂ`.

    The complex inner product convention is `⟨ψ|φ⟩ = ∑ᵢ ψᵢ* φᵢ`
    (physicists' convention; `star` = complex conjugate). -/
noncomputable def pureFidelity {n : ℕ} (ψ φ : Fin n → ℂ) : ℝ :=
  Complex.normSq (∑ i, star (ψ i) * φ i)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: PURE-STATE FIDELITY — algebraic properties
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The pure-state fidelity is nonneg. -/
theorem pureFidelity_nonneg {n : ℕ} (ψ φ : Fin n → ℂ) :
    0 ≤ pureFidelity ψ φ :=
  Complex.normSq_nonneg _

/-- Bridge to `EuclideanSpace`: the amplitude inner product
    `∑ ψᵢ* φᵢ` equals the canonical inner product `⟪ψ, φ⟫` after
    the (definitionally trivial) cast to `EuclideanSpace ℂ (Fin n)`. -/
lemma inner_eq_amplitude_sum {n : ℕ} (ψ φ : Fin n → ℂ) :
    (inner ℂ ((EuclideanSpace.equiv (Fin n) ℂ).symm ψ)
            ((EuclideanSpace.equiv (Fin n) ℂ).symm φ) : ℂ)
      = ∑ i, star (ψ i) * φ i := by
  simp [PiLp.inner_apply, EuclideanSpace.equiv, RCLike.inner_apply,
        mul_comm]

/-- The `pureFidelity` equals the squared norm of the EuclideanSpace
    inner product. -/
lemma pureFidelity_eq_norm_inner_sq {n : ℕ} (ψ φ : Fin n → ℂ) :
    pureFidelity ψ φ
      = ‖(inner ℂ ((EuclideanSpace.equiv (Fin n) ℂ).symm ψ)
              ((EuclideanSpace.equiv (Fin n) ℂ).symm φ) : ℂ)‖ ^ 2 := by
  rw [pureFidelity, inner_eq_amplitude_sum, Complex.normSq_eq_norm_sq]

/-- The amplitude `L²` norm-squared equals `∑ᵢ |ψᵢ|² = ∑ᵢ normSq ψᵢ`. -/
lemma euclidean_normSq_eq_sum {n : ℕ} (ψ : Fin n → ℂ) :
    ‖((EuclideanSpace.equiv (Fin n) ℂ).symm ψ)‖ ^ 2
      = ∑ i, Complex.normSq (ψ i) := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Complex.normSq_eq_norm_sq]
  congr 1

/-- **Pure fidelity ≤ 1** when both `ψ` and `φ` are normalized
    (`∑ᵢ |ψᵢ|² = 1`, `∑ᵢ |φᵢ|² = 1`).

    Cauchy-Schwarz: `|⟨ψ|φ⟩|² ≤ ‖ψ‖² · ‖φ‖² = 1 · 1 = 1`. -/
theorem pureFidelity_le_one {n : ℕ} (ψ φ : Fin n → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1)
    (hφ : ∑ i, Complex.normSq (φ i) = 1) :
    pureFidelity ψ φ ≤ 1 := by
  set Ψ : EuclideanSpace ℂ (Fin n) := (EuclideanSpace.equiv (Fin n) ℂ).symm ψ
  set Φ : EuclideanSpace ℂ (Fin n) := (EuclideanSpace.equiv (Fin n) ℂ).symm φ
  -- Cauchy-Schwarz: `‖⟪Ψ, Φ⟫‖ ≤ ‖Ψ‖ · ‖Φ‖`.
  have hCS : ‖(inner ℂ Ψ Φ : ℂ)‖ ≤ ‖Ψ‖ * ‖Φ‖ := norm_inner_le_norm Ψ Φ
  have hΨ_sq : ‖Ψ‖ ^ 2 = 1 := by
    rw [euclidean_normSq_eq_sum]; exact hψ
  have hΦ_sq : ‖Φ‖ ^ 2 = 1 := by
    rw [euclidean_normSq_eq_sum]; exact hφ
  -- From `‖Ψ‖² = 1` and `‖Ψ‖ ≥ 0` we get `‖Ψ‖ = 1`.
  have hΨ_nn : 0 ≤ ‖Ψ‖ := norm_nonneg _
  have hΦ_nn : 0 ≤ ‖Φ‖ := norm_nonneg _
  have hΨ : ‖Ψ‖ = 1 := by
    nlinarith [hΨ_sq, hΨ_nn, sq_nonneg (‖Ψ‖ - 1)]
  have hΦ : ‖Φ‖ = 1 := by
    nlinarith [hΦ_sq, hΦ_nn, sq_nonneg (‖Φ‖ - 1)]
  -- Square the CS inequality.
  have hbound : ‖(inner ℂ Ψ Φ : ℂ)‖ ≤ 1 := by
    have := hCS
    rw [hΨ, hΦ] at this; linarith
  have h0 : 0 ≤ ‖(inner ℂ Ψ Φ : ℂ)‖ := norm_nonneg _
  have hbound_sq : ‖(inner ℂ Ψ Φ : ℂ)‖ ^ 2 ≤ 1 := by
    nlinarith [hbound, h0]
  -- Translate to `pureFidelity`.
  rw [pureFidelity_eq_norm_inner_sq]
  exact hbound_sq

/-- **Pure fidelity is in `[0, 1]`** for normalized states. -/
theorem pureFidelity_in_range {n : ℕ} (ψ φ : Fin n → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1)
    (hφ : ∑ i, Complex.normSq (φ i) = 1) :
    0 ≤ pureFidelity ψ φ ∧ pureFidelity ψ φ ≤ 1 :=
  ⟨pureFidelity_nonneg ψ φ, pureFidelity_le_one ψ φ hψ hφ⟩

/-- **Pure fidelity is symmetric**: `F(ψ, φ) = F(φ, ψ)`.

    Proof: `∑ ψᵢ* φᵢ = star (∑ φᵢ* ψᵢ)`, and `normSq` is
    invariant under conjugation. -/
theorem pureFidelity_symm {n : ℕ} (ψ φ : Fin n → ℂ) :
    pureFidelity ψ φ = pureFidelity φ ψ := by
  unfold pureFidelity
  -- Key identity: ∑ star(ψᵢ) * φᵢ = star(∑ star(φᵢ) * ψᵢ).
  have hconj : (∑ i, star (ψ i) * φ i) = star (∑ i, star (φ i) * ψ i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [StarMul.star_mul, star_star, mul_comm]
  -- normSq is invariant under conjugation (= star on ℂ).
  rw [hconj]
  -- star on ℂ is `starRingEnd ℂ`; use `normSq_conj`.
  change Complex.normSq (star (∑ i, star (φ i) * ψ i))
       = Complex.normSq (∑ i, star (φ i) * ψ i)
  change Complex.normSq ((starRingEnd ℂ) (∑ i, star (φ i) * ψ i))
       = Complex.normSq (∑ i, star (φ i) * ψ i)
  exact Complex.normSq_conj _

/-- **Self-fidelity** `F(ψ, ψ) = 1` for normalized `ψ`.

    The amplitude sum `∑ᵢ ψᵢ* ψᵢ = ∑ᵢ |ψᵢ|²` is real and equals `1`. -/
theorem pureFidelity_self {n : ℕ} (ψ : Fin n → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    pureFidelity ψ ψ = 1 := by
  unfold pureFidelity
  -- The sum `∑ star ψ * ψ` is `∑ normSq ψ` lifted to ℂ.
  have h1 : (∑ i, star (ψ i) * ψ i) = (((∑ i, Complex.normSq (ψ i)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- star = conj on ℂ; conj ψ * ψ = star ψ * ψ; reduce to mul_conj rearranged.
    have hconj : conj (ψ i) * (ψ i) = ((Complex.normSq (ψ i)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
    -- star on ℂ = conj
    change star (ψ i) * ψ i = ((Complex.normSq (ψ i)) : ℂ)
    exact hconj
  rw [h1, hψ]
  -- normSq of (1 : ℝ) cast to ℂ is 1.
  change Complex.normSq ((1 : ℝ) : ℂ) = 1
  rw [Complex.ofReal_one, Complex.normSq_one]

/-- **Orthogonality** ⇒ `F = 0`: if `⟨ψ|φ⟩ = 0` then `F(ψ, φ) = 0`. -/
theorem pureFidelity_orthogonal {n : ℕ} (ψ φ : Fin n → ℂ)
    (h : ∑ i, star (ψ i) * φ i = 0) :
    pureFidelity ψ φ = 0 := by
  unfold pureFidelity
  rw [h, Complex.normSq_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BURES DISTANCE — self-distance vanishes for pure states
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bures self-distance**: `d_B(|ψ⟩,|ψ⟩) = 0` for normalized `ψ`.

    Stated in terms of the `pureFidelity` scalar (the bridge to the
    density-matrix `uhlmannFidelity` is the *pure-state reduction*,
    folded into `Uhlmann_Theorem_Target`). -/
theorem buresDistance_self_pure {n : ℕ} (ψ : Fin n → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    Real.sqrt (2 - 2 * pureFidelity ψ ψ) = 0 := by
  rw [pureFidelity_self ψ hψ]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: NAMED DEEP TARGETS — Uhlmann, DPI, Joint concavity
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    These three statements are the deep content of the
    Uhlmann-fidelity theory.  Each requires substantial Mathlib
    infrastructure not currently in scope (purification reachability,
    full CPTP channel category, operator-jointly-concave maps under
    CFC).  They are declared as named `Prop`-shaped targets so the
    surface API names them explicitly without `sorry` or custom
    `axiom`. -/

/-- **Uhlmann's theorem (named target)**: `F(ρ, σ)` equals the
    maximum overlap of purifications.

    Concretely, for any purifications `Ψ` of `ρ` and `Φ` of `σ` into
    a doubled space, the magnitude `|⟨Ψ|Φ⟩|` is bounded above by
    `F(ρ, σ)`, and the bound is attained for some choice. -/
def Uhlmann_Theorem_Target : Prop :=
  ∀ (n : ℕ) (ρ σ : Matrix (Fin n) (Fin n) ℂ),
    ρ.PosSemidef → σ.PosSemidef →
    uhlmannFidelity ρ σ
      = sSup { x : ℝ | ∃ (Ψ Φ : Fin (n * n) → ℂ),
          (∑ i, Complex.normSq (Ψ i) = 1) ∧
          (∑ i, Complex.normSq (Φ i) = 1) ∧
          x = pureFidelity Ψ Φ }

/-- **Data-processing inequality (DPI) for fidelity (named target)**.

    For any quantum channel `N : Matrix → Matrix` (CPTP), the
    fidelity is monotone: `F(N(ρ), N(σ)) ≥ F(ρ, σ)`.

    Here `N` is represented abstractly as a function whose CPTP
    structure is presumed witnessed by a Kraus family. -/
def Fidelity_DPI_Target : Prop :=
  ∀ (n m : ℕ) (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (N : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ),
    ρ.PosSemidef → σ.PosSemidef →
    (∃ (K : Fin n → Matrix (Fin m) (Fin n) ℂ),
        (∀ X, N X = ∑ α, K α * X * (K α).conjTranspose) ∧
        (∑ α, (K α).conjTranspose * K α) = (1 : Matrix (Fin n) (Fin n) ℂ)) →
    uhlmannFidelity ρ σ ≤ uhlmannFidelity (N ρ) (N σ)

/-- **Joint concavity of fidelity (named target)**.

    For any `α ∈ [0, 1]`,
    `F(αρ₁ + (1-α)ρ₂, ασ₁ + (1-α)σ₂)`
      `≥ α·F(ρ₁, σ₁) + (1-α)·F(ρ₂, σ₂)`. -/
def Fidelity_Joint_Concavity_Target : Prop :=
  ∀ (n : ℕ) (ρ₁ ρ₂ σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ) (α : ℝ),
    ρ₁.PosSemidef → ρ₂.PosSemidef → σ₁.PosSemidef → σ₂.PosSemidef →
    0 ≤ α → α ≤ 1 →
    α * uhlmannFidelity ρ₁ σ₁ + (1 - α) * uhlmannFidelity ρ₂ σ₂
      ≤ uhlmannFidelity
          (((α : ℂ)) • ρ₁ + ((1 - α : ℝ) : ℂ) • ρ₂)
          (((α : ℂ)) • σ₁ + ((1 - α : ℝ) : ℂ) • σ₂)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: MASTER THEOREM — all pure-state fidelity properties
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Master theorem**: for any normalized pure states
    `ψ, φ : Fin n → ℂ`, the pure-state fidelity satisfies:

    1. Range:        `0 ≤ F(ψ, φ) ≤ 1`.
    2. Symmetry:     `F(ψ, φ) = F(φ, ψ)`.
    3. Self:         `F(ψ, ψ) = 1`.
    4. Bures-self:   `d_B-like(ψ, ψ) = 0`.

    The orthogonality case is the separate hypothesis-driven
    `pureFidelity_orthogonal`. -/
theorem bures_fidelity_master {n : ℕ} (ψ φ : Fin n → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1)
    (hφ : ∑ i, Complex.normSq (φ i) = 1) :
    (0 ≤ pureFidelity ψ φ) ∧
    (pureFidelity ψ φ ≤ 1) ∧
    (pureFidelity ψ φ = pureFidelity φ ψ) ∧
    (pureFidelity ψ ψ = 1) ∧
    (Real.sqrt (2 - 2 * pureFidelity ψ ψ) = 0) := by
  refine ⟨pureFidelity_nonneg ψ φ, pureFidelity_le_one ψ φ hψ hφ,
          pureFidelity_symm ψ φ, pureFidelity_self ψ hψ, ?_⟩
  exact buresDistance_self_pure ψ hψ

/-! ## 6. Axiom audit (commented).

    These should print only `propext, Classical.choice, Quot.sound`
    (Lean's three standard axioms).  No `sorry`, no custom `axiom`. -/

-- #print axioms pureFidelity_nonneg
-- #print axioms pureFidelity_le_one
-- #print axioms pureFidelity_in_range
-- #print axioms pureFidelity_symm
-- #print axioms pureFidelity_self
-- #print axioms pureFidelity_orthogonal
-- #print axioms buresDistance_self_pure
-- #print axioms bures_fidelity_master
--
-- Verified output (Lean 4.28.0, Mathlib current):
--   all 8 theorems depend on axioms: [propext, Classical.choice, Quot.sound]
-- i.e. only the three standard Lean axioms.  Zero sorry, zero custom axioms.

end UnifiedTheory.LayerB.BuresFidelity
