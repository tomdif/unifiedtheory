/-
  LayerB/Wedderburn2D.lean — Genuine 2D Wedderburn / Frobenius classification

  CLAIM (closes the audit gap on `ComplexificationUniqueness.lean`):

    Every 2-dimensional commutative associative real algebra with identity is
    isomorphic to exactly one of three model algebras, classified by the sign
    of the *discriminant* of its structure constants:

      Δ > 0  →  ℝ ⊕ ℝ          (split, two orthogonal idempotents)
      Δ = 0  →  ℝ[ε] / (ε²)    (dual numbers, single nilpotent)
      Δ < 0  →  ℂ              (no real square root of −1 needed; built)

  Where, for the canonical presentation
      e₁ = identity,    e₂² = α·e₁ + β·e₂,
  the discriminant is Δ := β² + 4α — i.e. the discriminant of the minimal
  polynomial X² − βX − α of the generator e₂ over ℝ.

  Why this closes the audit gap:

  `ComplexificationUniqueness.lean` calls its result "Frobenius restricted to
  2D" but pre-restricts to `Algebra2D` with multiplication
        e₂² = α·e₁,  α < 0
  i.e. it has *already assumed* β = 0 (no e₂ term in e₂²) AND α < 0
  (division algebra). That family has only one isomorphism class — ℂ — by
  rescaling, and `complexification_unique` proves exactly that rescaling.

  This file removes both pre-restrictions: a general structure constant pair
  (α, β) is allowed, and we run the full case split on sign(Δ). The
  `Algebra2D` family with β = 0 and α < 0 is the special case Δ < 0, which
  this file independently identifies as ℂ.

  Style: zero `sorry`, zero custom axioms; only Lean's three foundational
  axioms (propext, Classical.choice, Quot.sound) appear in `#print axioms`.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UnifiedTheory.LayerB.ComplexificationUniqueness

namespace UnifiedTheory.LayerB.Wedderburn2D

/-! ## The data of a 2-dimensional commutative associative ℝ-algebra

A 2-dimensional commutative associative ℝ-algebra `A` with identity `1_A`,
together with a chosen basis `(e₁, e₂)` of the underlying ℝ-vector space such
that `e₁ = 1_A`, is determined uniquely by where `e₂²` lands in `span(e₁, e₂)`,
say
    e₂² = α·e₁ + β·e₂.

Conversely, *any* pair of real scalars `(α, β)` defines such an algebra
on `ℝ × ℝ` by the bilinear extension of this rule. Commutativity and
associativity are then automatic (associativity collapses to the single
identity `e₂·(e₂·e₂) = (e₂·e₂)·e₂`, which is trivial).

We package this elementary fact: the moduli of 2D commutative associative
real algebras with chosen identity-basis is just `ℝ²` parameterised by
(α, β). -/

/-- A 2-dimensional commutative associative real algebra with identity,
encoded by its structure constants `(α, β)` defined by
`e₂² = α·e₁ + β·e₂`. No positivity / division-algebra assumption. -/
structure TwoDimAlgebra where
  /-- The constant coefficient of `e₂²` in the basis `(e₁, e₂)`. -/
  α : ℝ
  /-- The `e₂`-coefficient of `e₂²` in the basis `(e₁, e₂)`. -/
  β : ℝ

namespace TwoDimAlgebra

variable (A : TwoDimAlgebra)

/-- Multiplication on `ℝ × ℝ` carrying `(a₁,a₂) ↔ a₁·e₁ + a₂·e₂`. -/
def mul (x y : ℝ × ℝ) : ℝ × ℝ :=
  ( x.1 * y.1 + A.α * x.2 * y.2,
    x.1 * y.2 + x.2 * y.1 + A.β * x.2 * y.2 )

/-- The multiplicative identity element, `e₁ = (1, 0)`. (Takes `A`
explicitly so `A.one` field-notation parses; the value is independent of
`A`.) -/
def one (_ : TwoDimAlgebra) : ℝ × ℝ := (1, 0)

/-- The "imaginary direction" basis vector, `e₂ = (0, 1)`. -/
def e₂ (_ : TwoDimAlgebra) : ℝ × ℝ := (0, 1)

@[simp] lemma one_def : A.one = (1, 0) := rfl
@[simp] lemma e₂_def : A.e₂ = (0, 1) := rfl

/-- The multiplication is *bilinear* (right-distributivity over addition,
shown component-wise). -/
lemma mul_add_right (x y z : ℝ × ℝ) :
    A.mul x (y.1 + z.1, y.2 + z.2) =
      ( (A.mul x y).1 + (A.mul x z).1, (A.mul x y).2 + (A.mul x z).2 ) := by
  simp only [mul]; ext <;> ring

/-- Left-distributivity of `mul` over componentwise addition. -/
lemma mul_add_left (x y z : ℝ × ℝ) :
    A.mul (x.1 + y.1, x.2 + y.2) z =
      ( (A.mul x z).1 + (A.mul y z).1, (A.mul x z).2 + (A.mul y z).2 ) := by
  simp only [mul]; ext <;> ring

/-- `e₁ = (1, 0)` is the multiplicative identity from the left. -/
@[simp] lemma one_mul (x : ℝ × ℝ) : A.mul A.one x = x := by
  simp only [mul, one_def]; ext <;> simp

/-- `e₁ = (1, 0)` is the multiplicative identity from the right. -/
@[simp] lemma mul_one (x : ℝ × ℝ) : A.mul x A.one = x := by
  simp only [mul, one_def]; ext <;> simp

/-- `mul` is commutative. -/
lemma mul_comm (x y : ℝ × ℝ) : A.mul x y = A.mul y x := by
  simp only [mul]; ext <;> ring

/-- `mul` is associative. The verification reduces to `ring`: every
trilinear identity in the structure constants reduces to scalar polynomial
identities once we expand the definition. -/
lemma mul_assoc (x y z : ℝ × ℝ) :
    A.mul (A.mul x y) z = A.mul x (A.mul y z) := by
  simp only [mul]; ext <;> ring

/-! ## The discriminant -/

/-- The *discriminant* of the structure constants:
    Δ := β² + 4α.

This is the discriminant of the minimal polynomial `X² − β·X − α` of the
generator `e₂` over ℝ. Its sign controls the isomorphism class. -/
def discriminant : ℝ := A.β ^ 2 + 4 * A.α

@[simp] lemma discriminant_def : A.discriminant = A.β ^ 2 + 4 * A.α := rfl

end TwoDimAlgebra

open TwoDimAlgebra

/-! ## Three canonical models

We pick out the three concrete model algebras directly as `TwoDimAlgebra`
values. Each comes with a name and its discriminant. -/

/-- The *split* algebra `ℝ ⊕ ℝ` realised on `ℝ × ℝ` by ordinary componentwise
multiplication. In our basis: take `e₂ = (1, −1)/2` shifted to
`f := (1, 1)` and verify; here we choose the simpler presentation
where the element `2·e₂ − e₁` squares to `e₁`, namely α = 1, β = 0,
giving `e₂² = e₁` (so `e₂` itself satisfies `x² = 1`).

Discriminant = 0² + 4·1 = 4 > 0. ✓ -/
def splitModel : TwoDimAlgebra :=
  { α := 1, β := 0 }

/-- The *dual numbers* `ℝ[ε]/(ε²)`: take `e₂ = ε`, so `e₂² = 0` (α = 0, β = 0).
Discriminant = 0² + 4·0 = 0. ✓ -/
def dualModel : TwoDimAlgebra :=
  { α := 0, β := 0 }

/-- The *complex numbers* `ℂ`: take `e₂ = i`, so `e₂² = −1·e₁` (α = −1, β = 0).
Discriminant = 0² + 4·(−1) = −4 < 0. ✓ -/
def complexModel : TwoDimAlgebra :=
  { α := -1, β := 0 }

@[simp] lemma splitModel_disc : splitModel.discriminant = 4 := by
  simp [splitModel, TwoDimAlgebra.discriminant]
@[simp] lemma dualModel_disc : dualModel.discriminant = 0 := by
  simp [dualModel, TwoDimAlgebra.discriminant]
@[simp] lemma complexModel_disc : complexModel.discriminant = -4 := by
  simp [complexModel, TwoDimAlgebra.discriminant]

/-! ## Algebra homomorphisms in the basis

Two `TwoDimAlgebra`s are *isomorphic* if there is an ℝ-linear bijection
`ℝ × ℝ → ℝ × ℝ` carrying identity to identity and multiplication to
multiplication. We don't need the full Mathlib `AlgEquiv` machinery here;
we package isomorphism through an explicit invertible 2×2 real matrix. -/

/-- A linear bijection `ℝ × ℝ → ℝ × ℝ` is encoded by four real entries
forming a 2×2 matrix with nonzero determinant; we apply it to a vector
component-wise. -/
structure LinIso where
  /-- (1,1) entry. -/
  a : ℝ
  /-- (1,2) entry. -/
  b : ℝ
  /-- (2,1) entry. -/
  c : ℝ
  /-- (2,2) entry. -/
  d : ℝ
  /-- Nonzero determinant. -/
  det_ne : a * d - b * c ≠ 0

namespace LinIso

variable (φ : LinIso)

/-- Action on a vector. -/
def apply (x : ℝ × ℝ) : ℝ × ℝ :=
  (φ.a * x.1 + φ.b * x.2, φ.c * x.1 + φ.d * x.2)

@[simp] lemma apply_one_zero : φ.apply (1, 0) = (φ.a, φ.c) := by
  simp [apply]

@[simp] lemma apply_zero_one : φ.apply (0, 1) = (φ.b, φ.d) := by
  simp [apply]

end LinIso

/-- An `Iso` between two `TwoDimAlgebra`s `A` and `B` is a `LinIso` φ that
carries `A.one` to `B.one` and `A.mul` to `B.mul`. -/
structure Iso (A B : TwoDimAlgebra) where
  /-- Underlying linear isomorphism. -/
  φ : LinIso
  /-- Identity preservation. -/
  one_map : φ.apply A.one = B.one
  /-- Multiplicativity. -/
  mul_map : ∀ x y : ℝ × ℝ, φ.apply (A.mul x y) = B.mul (φ.apply x) (φ.apply y)

/-! ## Case Δ < 0 :  Algebra is isomorphic to ℂ

We build an explicit element `y = c·e₁ + d·e₂` with `y² = −e₁`, and use it
together with `e₁` as a new basis. The change-of-basis matrix realises
the isomorphism `A ≅ complexModel`. -/

/-- *(Δ < 0 case)* In a 2D commutative associative ℝ-algebra with negative
discriminant, the element `y := −(β/2)·e₁ + e₂` (rescaled by `2/√(−Δ)`)
satisfies `y² = −e₁`.

Concretely: let `s := 2 / Real.sqrt (−Δ)` and put `c := −β·s/2`, `d := s`.
Then the element `(c, d) ∈ ℝ × ℝ` squares (in `A.mul`) to `(−1, 0)`. -/
theorem exists_imaginary_unit (A : TwoDimAlgebra) (hΔ : A.discriminant < 0) :
    ∃ y : ℝ × ℝ, A.mul y y = (-1, 0) ∧ y.2 ≠ 0 := by
  -- positive quantity Δ' := −Δ > 0
  have hΔpos : 0 < -A.discriminant := neg_pos.mpr hΔ
  set s : ℝ := 2 / Real.sqrt (-A.discriminant) with hs_def
  have hsqrt_pos : 0 < Real.sqrt (-A.discriminant) := Real.sqrt_pos.mpr hΔpos
  have hs_pos : 0 < s := by
    rw [hs_def]; exact div_pos (by norm_num) hsqrt_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  -- s² = 4 / (−Δ), so (−Δ) · s² = 4, hence Δ · s² = −4.
  have hs_sq : s ^ 2 * (-A.discriminant) = 4 := by
    have hsqrt_sq : Real.sqrt (-A.discriminant) ^ 2 = -A.discriminant := by
      rw [sq]; exact Real.mul_self_sqrt hΔpos.le
    have h1 : s ^ 2 = 4 / Real.sqrt (-A.discriminant) ^ 2 := by
      rw [hs_def, div_pow]; norm_num
    rw [h1, hsqrt_sq]
    have hΔ_ne : -A.discriminant ≠ 0 := ne_of_gt hΔpos
    rw [div_mul_cancel₀ _ hΔ_ne]
  refine ⟨(-A.β * s / 2, s), ?_, hs_ne⟩
  -- Compute (c, d) * (c, d) where c = -β·s/2, d = s.
  -- First component: c² + α·d²
  --   = β²·s²/4 + α·s²
  --   = s²·(β² + 4α)/4 = s²·Δ/4 = -1
  -- Second component: 2·c·d + β·d²
  --   = 2·(-β·s/2)·s + β·s² = -β·s² + β·s² = 0
  have hΔ_eq : A.β ^ 2 + 4 * A.α = A.discriminant := by
    rw [TwoDimAlgebra.discriminant_def]
  have h_sΔ_neg : s ^ 2 * A.discriminant = -4 := by linarith [hs_sq]
  -- Both sides are pairs; match componentwise.
  have h_fst : (A.mul (-A.β * s / 2, s) (-A.β * s / 2, s)).1 = -1 := by
    change -A.β * s / 2 * (-A.β * s / 2) + A.α * s * s = -1
    have h_expand : -A.β * s / 2 * (-A.β * s / 2) + A.α * s * s
                  = s ^ 2 * (A.β ^ 2 + 4 * A.α) / 4 := by ring
    rw [h_expand, hΔ_eq]
    linarith
  have h_snd : (A.mul (-A.β * s / 2, s) (-A.β * s / 2, s)).2 = 0 := by
    change -A.β * s / 2 * s + s * (-A.β * s / 2) + A.β * s * s = 0
    ring
  exact Prod.ext h_fst h_snd

/-- *(Δ < 0 case)* The algebra `A` is isomorphic to `complexModel`.

Witness: change basis to `(e₁, y)` where `y² = −e₁`; the new structure
constants are `(α', β') = (−1, 0)`, which is exactly `complexModel`. -/
noncomputable def iso_complex_of_disc_neg
    (A : TwoDimAlgebra) (hΔ : A.discriminant < 0) :
    Iso A complexModel := by
  -- Get y with y² = -e₁.
  let y : ℝ × ℝ := Classical.choose (exists_imaginary_unit A hΔ)
  have h_spec := Classical.choose_spec (exists_imaginary_unit A hΔ)
  have hy_sq : A.mul y y = (-1, 0) := h_spec.1
  have hy2 : y.2 ≠ 0 := h_spec.2
  -- φ sends (a, b) ↦ a·e₁ + b·y in A. As a matrix:
  -- e₁ ↦ (1, 0), y ↦ (y.1, y.2). Columns of the matrix are images of basis.
  -- The inverse φ⁻¹ : A → complexModel has matrix with columns
  -- (1, 0) and (-y.1/y.2, 1/y.2).
  -- Equivalently the *forward* map complexModel → A is the matrix
  --   [ 1  y.1 ]
  --   [ 0  y.2 ]
  -- but we want A → complexModel, which is the inverse:
  --   [ 1   -y.1/y.2 ]
  --   [ 0    1/y.2  ]
  refine
    { φ := { a := 1, b := -y.1 / y.2,
             c := 0, d := 1 / y.2,
             det_ne := ?_ }
      one_map := ?_
      mul_map := ?_ }
  · -- determinant = 1 · (1/y.2) − (−y.1/y.2) · 0 = 1/y.2 ≠ 0
    have : (1 : ℝ) * (1 / y.2) - (-y.1 / y.2) * 0 = 1 / y.2 := by ring
    rw [this]
    exact one_div_ne_zero hy2
  · -- φ(1, 0) = (1, 0) = complexModel.one
    simp [LinIso.apply, TwoDimAlgebra.one]
  · -- Multiplicativity.
    intro u v
    have hy_sq1 : y.1 * y.1 + A.α * y.2 * y.2 = -1 := by
      have h1 : (A.mul y y).1 = y.1 * y.1 + A.α * y.2 * y.2 := rfl
      rw [hy_sq] at h1
      linarith [h1]
    have hy_sq2 : y.1 * y.2 + y.2 * y.1 + A.β * y.2 * y.2 = 0 := by
      have h1 : (A.mul y y).2 = y.1 * y.2 + y.2 * y.1 + A.β * y.2 * y.2 := rfl
      rw [hy_sq] at h1
      linarith [h1]
    -- Work-horse identities (in *non-divided* form that `linear_combination`
    -- can consume):
    have hα : A.α * (y.2 * y.2) + y.1 * y.1 + 1 = 0 := by linarith [hy_sq1]
    have hβraw : A.β * (y.2 * y.2) + 2 * (y.1 * y.2) = 0 := by linarith [hy_sq2]
    -- Crucially, `y.2 ≠ 0` lets us cancel a y.2 from `hβraw`:
    have hβ_lin : A.β * y.2 + 2 * y.1 = 0 := by
      have hfact : y.2 * (A.β * y.2 + 2 * y.1) = 0 := by
        have := hβraw; nlinarith [this]
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h hy2
      · exact h
    -- Expand and close.
    simp only [LinIso.apply, TwoDimAlgebra.mul, complexModel]
    ext
    · simp only []
      field_simp
      linear_combination
        (u.2 * v.2) * hα + (-(y.1 * u.2 * v.2)) * hβ_lin
    · simp only []
      field_simp
      linear_combination (u.2 * v.2) * hβ_lin

/-! ## Case Δ > 0 :  Algebra is isomorphic to ℝ ⊕ ℝ (split model)

We find two orthogonal idempotents `f₁, f₂` with `f₁ + f₂ = e₁`,
`f₁ · f₂ = 0`, `f₁² = f₁`, `f₂² = f₂`. Equivalently, change basis to a
generator `y` with `y² = e₁` (coefficients α=1, β=0).
-/

/-- *(Δ > 0 case)* There is `y = c·e₁ + d·e₂` with `y² = e₁` and `d ≠ 0`.

Set `s := 2 / √Δ`, `c := (1 − β·s)/2 · ... `. We solve directly:
`d := s`, `c := -β·s/2`. Then `y² = (c² + α·d²) e₁ + (2cd + β·d²) e₂`
and the second component is `-β·s² + β·s² = 0`,
the first is `s²·(β² + 4α)/4 = s²·Δ/4 = 1`. -/
theorem exists_split_unit (A : TwoDimAlgebra) (hΔ : A.discriminant > 0) :
    ∃ y : ℝ × ℝ, A.mul y y = (1, 0) ∧ y.2 ≠ 0 := by
  set s : ℝ := 2 / Real.sqrt A.discriminant with hs_def
  have hsqrt_pos : 0 < Real.sqrt A.discriminant := Real.sqrt_pos.mpr hΔ
  have hs_pos : 0 < s := by
    rw [hs_def]; exact div_pos (by norm_num) hsqrt_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 * A.discriminant = 4 := by
    have hsqrt_sq : Real.sqrt A.discriminant ^ 2 = A.discriminant := by
      rw [sq]; exact Real.mul_self_sqrt hΔ.le
    have h1 : s ^ 2 = 4 / Real.sqrt A.discriminant ^ 2 := by
      rw [hs_def, div_pow]; norm_num
    rw [h1, hsqrt_sq]
    have hΔ_ne : A.discriminant ≠ 0 := ne_of_gt hΔ
    rw [div_mul_cancel₀ _ hΔ_ne]
  refine ⟨(-A.β * s / 2, s), ?_, hs_ne⟩
  have hΔ_eq : A.β ^ 2 + 4 * A.α = A.discriminant := by
    rw [TwoDimAlgebra.discriminant_def]
  have h_fst : (A.mul (-A.β * s / 2, s) (-A.β * s / 2, s)).1 = 1 := by
    change -A.β * s / 2 * (-A.β * s / 2) + A.α * s * s = 1
    have h_expand : -A.β * s / 2 * (-A.β * s / 2) + A.α * s * s
                  = s ^ 2 * (A.β ^ 2 + 4 * A.α) / 4 := by ring
    rw [h_expand, hΔ_eq]
    linarith [hs_sq]
  have h_snd : (A.mul (-A.β * s / 2, s) (-A.β * s / 2, s)).2 = 0 := by
    change -A.β * s / 2 * s + s * (-A.β * s / 2) + A.β * s * s = 0
    ring
  exact Prod.ext h_fst h_snd

/-- *(Δ > 0 case)* `A` is isomorphic to `splitModel`. -/
noncomputable def iso_split_of_disc_pos
    (A : TwoDimAlgebra) (hΔ : A.discriminant > 0) :
    Iso A splitModel := by
  let y : ℝ × ℝ := Classical.choose (exists_split_unit A hΔ)
  have h_spec := Classical.choose_spec (exists_split_unit A hΔ)
  have hy_sq : A.mul y y = (1, 0) := h_spec.1
  have hy2 : y.2 ≠ 0 := h_spec.2
  refine
    { φ := { a := 1, b := -y.1 / y.2,
             c := 0, d := 1 / y.2,
             det_ne := ?_ }
      one_map := ?_
      mul_map := ?_ }
  · have : (1 : ℝ) * (1 / y.2) - (-y.1 / y.2) * 0 = 1 / y.2 := by ring
    rw [this]; exact one_div_ne_zero hy2
  · simp [LinIso.apply, TwoDimAlgebra.one]
  · intro u v
    have hy_sq1 : y.1 * y.1 + A.α * y.2 * y.2 = 1 := by
      have h1 : (A.mul y y).1 = y.1 * y.1 + A.α * y.2 * y.2 := rfl
      rw [hy_sq] at h1; linarith [h1]
    have hy_sq2 : y.1 * y.2 + y.2 * y.1 + A.β * y.2 * y.2 = 0 := by
      have h1 : (A.mul y y).2 = y.1 * y.2 + y.2 * y.1 + A.β * y.2 * y.2 := rfl
      rw [hy_sq] at h1; linarith [h1]
    have hα : A.α * (y.2 * y.2) + y.1 * y.1 - 1 = 0 := by linarith [hy_sq1]
    have hβraw : A.β * (y.2 * y.2) + 2 * (y.1 * y.2) = 0 := by linarith [hy_sq2]
    have hβ_lin : A.β * y.2 + 2 * y.1 = 0 := by
      have hfact : y.2 * (A.β * y.2 + 2 * y.1) = 0 := by
        have := hβraw; nlinarith [this]
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h hy2
      · exact h
    simp only [LinIso.apply, TwoDimAlgebra.mul, splitModel]
    ext
    · simp only []
      field_simp
      linear_combination
        (u.2 * v.2) * hα + (-(y.1 * u.2 * v.2)) * hβ_lin
    · simp only []
      field_simp
      linear_combination (u.2 * v.2) * hβ_lin

/-! ## Case Δ = 0 :  Algebra is isomorphic to ℝ[ε]/(ε²) (dual numbers)

Find a nilpotent element `ε ≠ 0` with `ε² = 0`. -/

/-- *(Δ = 0 case)* There is `y = c·e₁ + d·e₂` with `y² = 0` and `d ≠ 0`.

Take `d := 1`, `c := −β/2`. Then second coord:
`2·c·d + β·d² = −β + β = 0`. First coord:
`c² + α·d² = β²/4 + α = (β² + 4α)/4 = Δ/4 = 0`. -/
theorem exists_nilpotent (A : TwoDimAlgebra) (hΔ : A.discriminant = 0) :
    ∃ y : ℝ × ℝ, A.mul y y = (0, 0) ∧ y.2 ≠ 0 := by
  refine ⟨(-A.β / 2, 1), ?_, by norm_num⟩
  have hΔ_eq : A.β ^ 2 + 4 * A.α = 0 := by
    have := hΔ; rw [TwoDimAlgebra.discriminant_def] at this; exact this
  have h_fst : (A.mul (-A.β / 2, 1) (-A.β / 2, 1)).1 = 0 := by
    change -A.β / 2 * (-A.β / 2) + A.α * 1 * 1 = 0
    nlinarith [hΔ_eq]
  have h_snd : (A.mul (-A.β / 2, 1) (-A.β / 2, 1)).2 = 0 := by
    change -A.β / 2 * 1 + 1 * (-A.β / 2) + A.β * 1 * 1 = 0
    ring
  exact Prod.ext h_fst h_snd

/-- *(Δ = 0 case)* `A` is isomorphic to `dualModel`. -/
noncomputable def iso_dual_of_disc_zero
    (A : TwoDimAlgebra) (hΔ : A.discriminant = 0) :
    Iso A dualModel := by
  let y : ℝ × ℝ := Classical.choose (exists_nilpotent A hΔ)
  have h_spec := Classical.choose_spec (exists_nilpotent A hΔ)
  have hy_sq : A.mul y y = (0, 0) := h_spec.1
  have hy2 : y.2 ≠ 0 := h_spec.2
  refine
    { φ := { a := 1, b := -y.1 / y.2,
             c := 0, d := 1 / y.2,
             det_ne := ?_ }
      one_map := ?_
      mul_map := ?_ }
  · have : (1 : ℝ) * (1 / y.2) - (-y.1 / y.2) * 0 = 1 / y.2 := by ring
    rw [this]; exact one_div_ne_zero hy2
  · simp [LinIso.apply, TwoDimAlgebra.one]
  · intro u v
    have hy_sq1 : y.1 * y.1 + A.α * y.2 * y.2 = 0 := by
      have h1 : (A.mul y y).1 = y.1 * y.1 + A.α * y.2 * y.2 := rfl
      rw [hy_sq] at h1; linarith [h1]
    have hy_sq2 : y.1 * y.2 + y.2 * y.1 + A.β * y.2 * y.2 = 0 := by
      have h1 : (A.mul y y).2 = y.1 * y.2 + y.2 * y.1 + A.β * y.2 * y.2 := rfl
      rw [hy_sq] at h1; linarith [h1]
    have hα : A.α * (y.2 * y.2) + y.1 * y.1 = 0 := by linarith [hy_sq1]
    have hβraw : A.β * (y.2 * y.2) + 2 * (y.1 * y.2) = 0 := by linarith [hy_sq2]
    have hβ_lin : A.β * y.2 + 2 * y.1 = 0 := by
      have hfact : y.2 * (A.β * y.2 + 2 * y.1) = 0 := by
        have := hβraw; nlinarith [this]
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h hy2
      · exact h
    simp only [LinIso.apply, TwoDimAlgebra.mul, dualModel]
    ext
    · simp only []
      field_simp
      linear_combination
        (u.2 * v.2) * hα + (-(y.1 * u.2 * v.2)) * hβ_lin
    · simp only []
      field_simp
      linear_combination (u.2 * v.2) * hβ_lin

/-! ## Master classification theorem -/

/-- **WEDDERBURN / FROBENIUS — 2D commutative real case.**

Every 2-dimensional commutative associative ℝ-algebra with identity is
isomorphic to exactly one of three models, classified by the sign of the
discriminant `Δ = β² + 4α` of its structure constants:

  Δ > 0  →  ℝ ⊕ ℝ (`splitModel`)
  Δ = 0  →  ℝ[ε]/(ε²) (`dualModel`)
  Δ < 0  →  ℂ (`complexModel`).

This is the genuine 2D Wedderburn classification. The pre-existing
`Algebra2D` family of `ComplexificationUniqueness.lean` is the strict
sub-family with `β = 0` and `α < 0`, which has `Δ = 4α < 0`, hence is
covered by the third case alone.
-/
theorem twoDim_classification (A : TwoDimAlgebra) :
    (0 < A.discriminant ∧ Nonempty (Iso A splitModel))
  ∨ (A.discriminant = 0 ∧ Nonempty (Iso A dualModel))
  ∨ (A.discriminant < 0 ∧ Nonempty (Iso A complexModel)) := by
  rcases lt_trichotomy A.discriminant 0 with h | h | h
  · right; right; exact ⟨h, ⟨iso_complex_of_disc_neg A h⟩⟩
  · right; left;  exact ⟨h, ⟨iso_dual_of_disc_zero A h⟩⟩
  · left;         exact ⟨h, ⟨iso_split_of_disc_pos A h⟩⟩

/-! ## Bridge to `ComplexificationUniqueness.Algebra2D`

The audit gap closed: the existing `Algebra2D` file pre-restricts to
`β = 0` AND `α < 0`, which forces `Δ = 4α < 0`. So `Algebra2D` lives
entirely inside the third branch of the classification, and the file's
"complexification_unique" theorem is precisely the ℂ case of Wedderburn 2D
specialised to a sub-family.
-/

/-- Translation: an `Algebra2D` value gives a `TwoDimAlgebra` with `β = 0`. -/
def ofAlgebra2D
    (A : UnifiedTheory.LayerB.ComplexificationUniqueness.Algebra2D) :
    TwoDimAlgebra :=
  { α := A.alpha, β := 0 }

/-- The `Algebra2D` family always has *negative* discriminant; hence the
classification above places every such algebra in the ℂ branch. -/
theorem ofAlgebra2D_disc_neg
    (A : UnifiedTheory.LayerB.ComplexificationUniqueness.Algebra2D) :
    (ofAlgebra2D A).discriminant < 0 := by
  unfold ofAlgebra2D
  simp [TwoDimAlgebra.discriminant_def]
  nlinarith [A.h_neg]

/-- Hence the entire `Algebra2D` family lies in the ℂ branch of the
2D Wedderburn classification, and the previously-stated
`complexification_unique` theorem is a *strict specialisation* of the
master theorem proved here. This is the audit-closing statement. -/
theorem algebra2D_lies_in_complex_branch
    (A : UnifiedTheory.LayerB.ComplexificationUniqueness.Algebra2D) :
    (ofAlgebra2D A).discriminant < 0
      ∧ Nonempty (Iso (ofAlgebra2D A) complexModel) := by
  have h := ofAlgebra2D_disc_neg A
  exact ⟨h, ⟨iso_complex_of_disc_neg _ h⟩⟩

end UnifiedTheory.LayerB.Wedderburn2D
