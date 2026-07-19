/-
  UnifiedTheory/LayerC/QuantumReferenceFrames.lean
  ────────────────────────────────────────────────

  **Quantum reference frames** — covariance of quantum predictions
  under group actions transforming reference frames
  (Bartlett-Rudolph-Spekkens, *Reference frames, superselection
  rules, and quantum information*, Rev. Mod. Phys. 79, 555 (2007),
  arXiv:quant-ph/0610030).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  When a measurement is performed on a quantum system in the
  absence of a shared reference frame for some symmetry group `G`
  (e.g. a phase reference for `U(1)`, a Cartesian frame for
  `SO(3)`), the only operationally-accessible measurements are
  those whose outcome statistics do not depend on the choice of
  reference frame.  Equivalently, an operator `A` is operationally
  accessible iff it commutes with the action of `G`:

      ∀ g ∈ G,  U_g · A · U_g†  =  A.

  Such an `A` is called **G-covariant** (or **G-invariant**).

  The canonical construction of G-covariant operators from
  arbitrary operators is the **G-twirl**:

      𝒯[A]  :=  (1/|G|)  Σ_{g ∈ G}  U_g · A · U_g†       (finite G)

  The twirl is the projector onto the G-covariant subspace.
  Operationally, twirling an arbitrary measurement is the unique
  reference-frame-independent measurement that agrees with the
  original on G-invariant states.  Twirling is also the *Petz
  recovery map* for the conditional expectation onto the algebra
  of `G`-covariant operators.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (zero `sorry`, zero custom axiom)

  Tier 1 — DEFINITIONS:
    • `IsGCovariant U A`         — `U g · A · (U g)† = A` for all g
    • `twirl U A`                — finite-group average of conjugates
    • `IsUnitaryRep U`           — a packaging Prop for a unitary
                                    representation of a finite group

  Tier 2 — STRUCTURAL THEOREMS:
    • `isGCovariant_add`         — closed under addition
    • `isGCovariant_smul`        — closed under complex scalars
    • `isGCovariant_zero`        — `0` is G-covariant
    • `isGCovariant_neg`         — closed under negation
    • `isGCovariant_sub`         — closed under subtraction
    • `isGCovariant_one`         — the identity matrix is G-covariant
    • `isGCovariant_mul`         — closed under matrix product
    • `twirl_isGCovariant`       — `𝒯[A]` is G-covariant
    • `twirl_gcovariant_eq`      — `IsGCovariant A → 𝒯[A] = A`
                                    (idempotence on G-covariants)
    • `twirl_idempotent`         — `𝒯[𝒯[A]] = 𝒯[A]`

  Tier 3 — OPERATIONAL INVARIANCE:
    • `trace_gcovariant_conj`    — for any G-covariant A and any g,
                                    `Tr(A · U_g·ρ·U_g†) = Tr(A · ρ)`
                                    — the reference-frame-rotation
                                    invariance of expectation values
    • `covariance_invariance`    — the headline corollary: a
                                    G-covariant measurement gives
                                    operationally identical
                                    predictions on a state and on
                                    any G-rotation of it.

  Tier 4 — INSTANTIATION:
    • `trivialRep`               — the trivial unitary representation
                                    (every operator is G-covariant
                                    trivially); diagnostic check.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  The Lie-group (continuous) case requires the Haar measure on `G`
  and Bochner integration over matrix-valued functions, which is a
  separate multi-week formalisation.  We ship the **finite group**
  case in full, which already captures the Bartlett-Rudolph-Spekkens
  structural content (their Sec. III is stated for general locally
  compact groups but the discrete case is the conceptual heart and
  is what is used in essentially every concrete application — finite
  Abelian (Z_N), finite non-Abelian (the symmetric group S_n, the
  Pauli group), and discrete projective representations of compact
  Lie groups (e.g. icosahedral subgroups of SO(3) for spin reference
  frames)).

  Specific Lie groups (U(1) for charge superselection, SU(2) for
  spin reference frames) are deferred to follow-on files.
-/

import UnifiedTheory.LayerB.UnitaryInvariance
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.QuantumReferenceFrames

open Matrix
open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0:  AMBIENT TYPES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {n : ℕ} {G : Type*}

/-- **Unitary representation** of a group `G` on `ℂⁿ`: a map
    `G → Matrix (Fin n) (Fin n) ℂ` that is multiplicative and
    lands in the unitary group.  We package these conditions as
    explicit hypothesis fields rather than as a `MonoidHom` so
    that the conjugate-transpose `(U g)†` is what appears in the
    G-covariance condition (matching the physics literature). -/
structure IsUnitaryRep (U : G → Matrix (Fin n) (Fin n) ℂ) [Group G] : Prop where
  hom      : ∀ g h, U (g * h) = U g * U h
  one      : U 1 = 1
  unitary  : ∀ g, U g * (U g)ᴴ = 1
  unitary' : ∀ g, (U g)ᴴ * U g = 1

namespace IsUnitaryRep

variable [Group G] {U : G → Matrix (Fin n) (Fin n) ℂ}

/-- `U` of an inverse equals the conjugate-transpose: `U g⁻¹ = (U g)†`. -/
lemma inv_eq_conjTranspose (hU : IsUnitaryRep U) (g : G) :
    U g⁻¹ = (U g)ᴴ := by
  -- From `U g * U g⁻¹ = U 1 = 1` and `U g * (U g)† = 1`, cancel on the left.
  have h1 : U g * U g⁻¹ = 1 := by
    rw [← hU.hom g g⁻¹, mul_inv_cancel, hU.one]
  have h2 : U g * (U g)ᴴ = 1 := hU.unitary g
  -- Multiply both equalities by (U g)† on the left:
  have := congrArg (fun M => (U g)ᴴ * M) h1
  simp only at this
  rw [← Matrix.mul_assoc, hU.unitary' g, Matrix.one_mul] at this
  -- this : U g⁻¹ = (U g)ᴴ * 1
  rw [this]
  -- Now show (U g)ᴴ * 1 = (U g)ᴴ
  rw [Matrix.mul_one]

end IsUnitaryRep

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1:  G-COVARIANT OPERATORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **G-covariance.**  An operator `A` is G-covariant under the
    unitary representation `U` iff conjugation by every `U g` fixes
    it:  `U g · A · (U g)† = A`. -/
def IsGCovariant [Group G] (U : G → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ g, U g * A * (U g)ᴴ = A

namespace IsGCovariant

variable [Group G] {U : G → Matrix (Fin n) (Fin n) ℂ}

/-- Closure under addition. -/
lemma add {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsGCovariant U A) (hB : IsGCovariant U B) :
    IsGCovariant U (A + B) := by
  intro g
  have : U g * (A + B) * (U g)ᴴ = U g * A * (U g)ᴴ + U g * B * (U g)ᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [this, hA g, hB g]

/-- Closure under negation. -/
lemma neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGCovariant U A) :
    IsGCovariant U (-A) := by
  intro g
  have hneg : U g * (-A) * (U g)ᴴ = -(U g * A * (U g)ᴴ) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [hneg, hA g]

/-- Closure under subtraction. -/
lemma sub {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsGCovariant U A) (hB : IsGCovariant U B) :
    IsGCovariant U (A - B) := by
  simpa [sub_eq_add_neg] using hA.add hB.neg

/-- Closure under complex scalar multiplication. -/
lemma smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGCovariant U A) (c : ℂ) :
    IsGCovariant U (c • A) := by
  intro g
  have : U g * (c • A) * (U g)ᴴ = c • (U g * A * (U g)ᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [this, hA g]

/-- `0` is G-covariant. -/
lemma zero : IsGCovariant U (0 : Matrix (Fin n) (Fin n) ℂ) := by
  intro g
  simp

/-- `1` (the identity matrix) is G-covariant for any unitary
    representation:  `U g · 1 · (U g)† = U g · (U g)† = 1`. -/
lemma one (hU : IsUnitaryRep U) : IsGCovariant U (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro g
  rw [Matrix.mul_one]; exact hU.unitary g

/-- Closure under matrix product:  if `A` and `B` are G-covariant
    then so is `A · B`.  The argument inserts `(U g)† · U g = 1`. -/
lemma mul (hU : IsUnitaryRep U) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsGCovariant U A) (hB : IsGCovariant U B) :
    IsGCovariant U (A * B) := by
  intro g
  -- U g · (A · B) · (U g)† = U g · A · ((U g)† · U g) · B · (U g)†
  --                       = (U g · A · (U g)†) · (U g · B · (U g)†)
  --                       = A · B
  have hkey : U g * (A * B) * (U g)ᴴ
            = (U g * A * (U g)ᴴ) * (U g * B * (U g)ᴴ) := by
    have h1 : (U g * A * (U g)ᴴ) * (U g * B * (U g)ᴴ)
            = U g * A * ((U g)ᴴ * U g) * B * (U g)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [h1, hU.unitary' g, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [hkey, hA g, hB g]

end IsGCovariant

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2:  THE G-TWIRL (finite-group average of conjugates)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **G-twirl**:  the uniform average of `U g · A · (U g)†` over a
    finite group `G`.  This is the Banach projector onto the
    G-covariant subspace.  Concretely:

        𝒯[A]  :=  (1 / |G|)  ·  Σ_{g ∈ G}  U g · A · (U g)†.

    For `|G| = 0` (i.e., `G` empty, which contradicts `[Group G]`
    but the definition is still typeable for general `Fintype G`)
    the average is `0`.  In practice `[Group G]` forces `G`
    nonempty (it contains `1`) so `|G| ≥ 1` always. -/
noncomputable def twirl [Fintype G] (U : G → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, U g * A * (U g)ᴴ

/-! ### 2.1  Twirl is G-covariant -/

/-- **Key index-substitution lemma.**  Reindexing the twirl sum by
    `g ↦ g₀⁻¹ · g` (for fixed `g₀ ∈ G`) leaves the sum invariant. -/
lemma sum_smul_index_eq [Group G] [Fintype G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) (_hU : IsUnitaryRep U)
    (A : Matrix (Fin n) (Fin n) ℂ) (g₀ : G) :
    ∑ g, U (g₀ * g) * A * (U (g₀ * g))ᴴ
      = ∑ g, U g * A * (U g)ᴴ := by
  -- Reindex `g ↦ g₀ * g`; this is a bijection on `G`.
  -- `Fintype.sum_bijective e he f g (h : ∀ x, f x = g (e x)) : ∑ x, f x = ∑ x, g x`.
  classical
  refine Fintype.sum_bijective (fun g => g₀ * g)
    (Group.mulLeft_bijective _)
    (fun g => U (g₀ * g) * A * (U (g₀ * g))ᴴ)
    (fun g => U g * A * (U g)ᴴ)
    ?_
  intro g
  rfl

/-- **The twirl is G-covariant.**  For any `g₀ ∈ G`,
    `U g₀ · 𝒯[A] · (U g₀)† = 𝒯[A]`. -/
theorem twirl_isGCovariant [Group G] [Fintype G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitaryRep U)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    IsGCovariant U (twirl U A) := by
  intro g₀
  unfold twirl
  -- LHS = U g₀ · ((1/|G|) Σ_g U g · A · (U g)†) · (U g₀)†
  --     = (1/|G|) · Σ_g (U g₀ · U g) · A · (U g · (U g₀)†)†   [bring inside]
  --     = (1/|G|) · Σ_g U (g₀ g) · A · (U (g₀ g))†             [hom, †-prod]
  --     = (1/|G|) · Σ_g' U g' · A · (U g')†                    [reindex]
  --     = 𝒯[A].
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  -- Now: U g₀ * (∑ g, U g * A * (U g)ᴴ) * (U g₀)ᴴ = ∑ g, U g * A * (U g)ᴴ.
  -- Distribute U g₀ across the sum on the LEFT, then (U g₀)ᴴ on the RIGHT.
  rw [Matrix.mul_sum]
  -- Now: (∑ g, U g₀ * (U g * A * (U g)ᴴ)) * (U g₀)ᴴ = ∑ g, U g * A * (U g)ᴴ.
  rw [Matrix.sum_mul]
  -- Now: ∑ g, U g₀ * (U g * A * (U g)ᴴ) * (U g₀)ᴴ = ∑ g, U g * A * (U g)ᴴ.
  -- Each summand equals U (g₀ * g) * A * (U (g₀ * g))ᴴ; reindex via g ↦ g₀⁻¹ * g.
  have hexpand : ∀ g : G, U g₀ * (U g * A * (U g)ᴴ) * (U g₀)ᴴ
                        = U (g₀ * g) * A * (U (g₀ * g))ᴴ := by
    intro g
    rw [hU.hom g₀ g, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl (fun g _ => hexpand g)]
  exact sum_smul_index_eq U hU A g₀

/-! ### 2.2  Twirl is identity on G-covariant operators -/

/-- **Idempotence on G-covariants.**  If `A` is G-covariant then
    `𝒯[A] = A`. -/
theorem twirl_gcovariant_eq [Group G] [Fintype G] [Nonempty G]
    (U : G → Matrix (Fin n) (Fin n) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGCovariant U A) :
    twirl U A = A := by
  unfold twirl
  -- Each summand equals A; the sum is `|G| • A` (Nat smul); the prefactor
  -- `(1/|G|)` cancels.
  have hconst : ∀ g : G, U g * A * (U g)ᴴ = A := hA
  rw [Finset.sum_congr rfl (fun g _ => hconst g)]
  -- Goal: (Fintype.card G : ℂ)⁻¹ • ∑ g, A = A.
  rw [Finset.sum_const, Finset.card_univ]
  -- Goal: (Fintype.card G : ℂ)⁻¹ • (Fintype.card G • A) = A.
  -- Convert Nat smul to ℂ smul, then cancel.
  have hne : (Fintype.card G : ℂ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul,
      inv_mul_cancel₀ hne, one_smul]

/-- **Twirl idempotence.**  `𝒯[𝒯[A]] = 𝒯[A]`. -/
theorem twirl_idempotent [Group G] [Fintype G] [Nonempty G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitaryRep U)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    twirl U (twirl U A) = twirl U A :=
  twirl_gcovariant_eq U (twirl_isGCovariant U hU A)

/-! ### 2.3  Twirl is linear -/

/-- The twirl is additive in `A`. -/
theorem twirl_add [Group G] [Fintype G]
    (U : G → Matrix (Fin n) (Fin n) ℂ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    twirl U (A + B) = twirl U A + twirl U B := by
  unfold twirl
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros g _
  rw [Matrix.mul_add, Matrix.add_mul]

/-- The twirl commutes with scalar multiplication. -/
theorem twirl_smul [Group G] [Fintype G]
    (U : G → Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    twirl U (c • A) = c • twirl U A := by
  unfold twirl
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intros g _
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The twirl of `0` is `0`. -/
@[simp] theorem twirl_zero [Group G] [Fintype G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) :
    twirl U (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  unfold twirl
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3:  OPERATIONAL INVARIANCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The key physical content: when the measurement operator `A` is
    G-covariant, the expectation `Tr(A · ρ)` is invariant under
    G-rotations of `ρ`.  This is the operational content of the
    statement "G-covariant observables do not see G-rotations."   -/

/-- **Trace cyclicity for unitary conjugation.**  For any unitary
    `U g` and any matrices `A`, `ρ`, applying `U g` to `ρ` from the
    left can be undone by applying `(U g)†` to `A` from the right
    inside the trace.  Specialised consequence: if `U g · A · (U g)† = A`
    then `Tr(A · U g · ρ · (U g)†) = Tr(A · ρ)`. -/
theorem trace_gcovariant_conj [Group G]
    {U : G → Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitaryRep U)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGCovariant U A)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    Matrix.trace (A * (U g * ρ * (U g)ᴴ)) = Matrix.trace (A * ρ) := by
  -- Step 1: cycle `(U g)†` to the front of the trace.
  -- Tr(A · U g · ρ · (U g)†) = Tr((U g)† · A · U g · ρ).
  have h_cycle : Matrix.trace (A * (U g * ρ * (U g)ᴴ))
               = Matrix.trace ((U g)ᴴ * A * U g * ρ) := by
    -- Rearrange to (A · U g · ρ) · (U g)† then use trace cyclicity.
    have hrearr : A * (U g * ρ * (U g)ᴴ) = (A * U g * ρ) * (U g)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [hrearr, Matrix.trace_mul_cycle]
    -- After cycle: Tr((U g)† · (A · U g · ρ)) — reassociate.
    simp only [Matrix.mul_assoc]
  -- Step 2: identify `(U g)† · A · U g` with `A` using G-covariance.
  -- From `U g · A · (U g)† = A`, multiplying on left by `(U g)†` and on right by `U g`:
  --   `(U g)† · U g · A · (U g)† · U g = (U g)† · A · U g`
  --   `A = (U g)† · A · U g` (using unitarity twice).
  have h_inner : (U g)ᴴ * A * U g = A := by
    have h1 : U g * A * (U g)ᴴ = A := hA g
    -- Multiply on left by (U g)† and on right by U g.
    have := congrArg (fun M => (U g)ᴴ * M * U g) h1
    simp only at this
    -- this : (U g)ᴴ * (U g * A * (U g)ᴴ) * U g = (U g)ᴴ * A * U g
    -- Simplify LHS using unitarity.
    rw [show (U g)ᴴ * (U g * A * (U g)ᴴ) * U g
            = ((U g)ᴴ * U g) * A * ((U g)ᴴ * U g) from by
          simp only [Matrix.mul_assoc],
        hU.unitary' g, Matrix.one_mul, Matrix.mul_one] at this
    exact this.symm
  rw [h_cycle, h_inner]

/-- **Reference-frame covariance** (the BRS operational principle).

    The operational predictions of a G-covariant measurement `A` on
    a state `ρ` are invariant under G-rotations of the state:

        ⟨A⟩_{U g · ρ · (U g)†}  =  ⟨A⟩_ρ.

    Physically: a measurement that does not single out a reference
    frame for `G` (i.e., is G-covariant) cannot distinguish a state
    from any of its G-rotations.  This is the rigorous content of
    Bartlett-Rudolph-Spekkens §III.A. -/
theorem covariance_invariance [Group G]
    {U : G → Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitaryRep U)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGCovariant U A)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    Matrix.trace (A * (U g * ρ * (U g)ᴴ)) = Matrix.trace (A * ρ) :=
  trace_gcovariant_conj hU hA ρ g

/-- **Dual formulation.**  Equivalently — by trace cyclicity — a
    G-rotation of `A` does not change `Tr(A · ρ)` either.  For any
    matrix `A` (not assumed G-covariant) and any state `ρ`:

        Tr((U g · A · (U g)†) · ρ)  =  Tr(A · (U g)† · ρ · U g).

    Specialising `A` to G-covariant makes the LHS equal `Tr(A · ρ)`. -/
theorem trace_conj_dual [Group G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) (_hU : IsUnitaryRep U)
    (A ρ : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    Matrix.trace ((U g * A * (U g)ᴴ) * ρ)
      = Matrix.trace (A * ((U g)ᴴ * ρ * U g)) := by
  -- Standard trace cyclicity: Tr(U · X) = Tr(X · U).  With
  --   X := A · (U g)† · ρ  and  cycle = U g  yields
  --   Tr(U g · A · (U g)† · ρ)  =  Tr(A · (U g)† · ρ · U g).
  -- Apply trace_mul_cycle to (U g * A * ((U g)ᴴ * ρ)):
  --   Tr(U g · A · ((U g)† · ρ))  =  Tr(((U g)† · ρ) · U g · A)  ✗ wrong cycle.
  -- Use trace_mul_comm to swap U g to the right.
  have hrearr : (U g * A * (U g)ᴴ) * ρ = U g * (A * (U g)ᴴ * ρ) := by
    simp only [Matrix.mul_assoc]
  rw [hrearr, Matrix.trace_mul_comm]
  -- Now: Tr((A · (U g)† · ρ) · U g) = Tr(A · ((U g)† · ρ · U g)).
  congr 1
  simp only [Matrix.mul_assoc]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4:  EXISTENCE — THE TRIVIAL REPRESENTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    To witness that the framework is consistent (no vacuous
    quantifier), we exhibit the trivial representation: `U g = 1`
    for all `g`.  Under it every operator is G-covariant. -/

/-- The **trivial unitary representation** `g ↦ 1`. -/
def trivialRep (G : Type*) (n : ℕ) :
    G → Matrix (Fin n) (Fin n) ℂ := fun _ => 1

/-- The trivial representation is unitary. -/
lemma trivialRep_isUnitaryRep [Group G] (n : ℕ) :
    IsUnitaryRep (trivialRep G n) where
  hom := fun _ _ => by simp [trivialRep]
  one := rfl
  unitary := fun _ => by simp [trivialRep]
  unitary' := fun _ => by simp [trivialRep]

/-- Under the trivial representation, every operator is G-covariant. -/
lemma isGCovariant_trivialRep [Group G]
    (A : Matrix (Fin n) (Fin n) ℂ) :
    IsGCovariant (trivialRep G n) A := by
  intro _
  simp [trivialRep]

/-- Under the trivial representation, twirling is the identity. -/
lemma twirl_trivialRep [Group G] [Fintype G] [Nonempty G]
    (A : Matrix (Fin n) (Fin n) ℂ) :
    twirl (trivialRep G n) A = A :=
  twirl_gcovariant_eq (trivialRep G n) (isGCovariant_trivialRep A)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5:  CONNECTION TO `unitaryConjugate`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.RobertsonSchrodinger

/-- An operator `A` is G-covariant iff `A` is `unitaryConjugate`-fixed
    by every `U g` (viewed as conjugation on operators).  We don't
    package `U g` as `Matrix.unitaryGroup` here — that requires lifting
    each `U g` to a subtype membership.  Instead we record the direct
    equivalence on matrices. -/
lemma isGCovariant_iff_conj_fixed [Group G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) (_hU : IsUnitaryRep U)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    IsGCovariant U A ↔ ∀ g, U g * A * (U g)ᴴ = A :=
  Iff.rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6:  AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    All deliverables in this file depend only on the standard
    Lean / Mathlib axioms (`propext`, `Classical.choice`,
    `Quot.sound`).  No custom `axiom` is introduced.  Re-check
    with the diagnostic `#print axioms` commands below. -/

-- Verified: every theorem in this file depends only on
--   [propext, Classical.choice, Quot.sound]
-- Re-check by uncommenting:
-- #print axioms twirl_isGCovariant
-- #print axioms twirl_gcovariant_eq
-- #print axioms twirl_idempotent
-- #print axioms covariance_invariance
-- #print axioms trace_gcovariant_conj
-- #print axioms trace_conj_dual

end UnifiedTheory.LayerC.QuantumReferenceFrames
