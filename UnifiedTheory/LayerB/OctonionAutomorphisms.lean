/-
  LayerB/OctonionAutomorphisms.lean — The automorphism group Aut(𝕆) = G₂.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PURPOSE

  `ColorFromG2.lean` and `GenerationsEqualColors.lean` rest on the fact
  that colour SU(3) is the subgroup of G₂ = Aut(𝕆) stabilizing a unit
  imaginary octonion. This file CONSTRUCTS the automorphism group of the
  octonion algebra `𝕆` built in `Octonions.lean`, as a genuine group
  object, and proves its defining structural properties.

  An octonion automorphism is an ℝ-linear bijection φ : 𝕆 → 𝕆 that
  preserves the Cayley–Dickson product, φ(x·y) = φ(x)·φ(y). The set of
  these is a subgroup `octAut` of the group `𝕆 ≃ₗ[ℝ] 𝕆` of ℝ-linear
  automorphisms (Mathlib's `LinearEquiv.automorphismGroup`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (zero sorry, zero custom axioms)

   • `octAut` — Aut(𝕆) as a `Subgroup (𝕆 ≃ₗ[ℝ] 𝕆)`: closed under identity,
     composition and inverse (i.e. it IS a group).
   • `aut_fixes_one` — every automorphism fixes the unit, φ(1) = 1.
   • `omul_ostar` — the norm-from-multiplication identity
     x · x̄ = N(x)·1, the algebraic source of the orthogonal structure.
   • `aut_preserves_norm_of_commutes_conj` — an automorphism that commutes
     with conjugation preserves the norm (orthogonality). This isolates
     the exact residual fact (φ∘(·)̄ = (·)̄∘φ, equivalently φ preserves the
     real-part splitting) behind the embedding Aut(𝕆) ↪ O(7) ⊃ G₂.
   • `aut_G2_bridge` — the dimension data of G₂ in framework atoms.

  WHAT IS CITED (standard Lie theory; Mathlib has no G₂):
    Aut(𝕆) ≅ G₂, the 14-dimensional compact exceptional Lie group, acting
    on im 𝕆 ≅ ℝ⁷ as the 7-dim irrep, with the norm-preservation
    (orthogonality) holding unconditionally. This file builds the group
    and proves everything except the conjugation-commutation, which it
    reduces to and flags.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.Octonions
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.OctonionAutomorphisms

open UnifiedTheory.LayerB.Octonions

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE AUTOMORPHISM GROUP AS A SUBGROUP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Aut(𝕆) = G₂.** The ℝ-linear automorphisms of 𝕆 preserving the
    Cayley–Dickson product, as a subgroup of the linear automorphism group
    `𝕆 ≃ₗ[ℝ] 𝕆`. Closure under identity / composition / inverse is exactly
    the statement that the octonion automorphisms form a group. -/
def octAut : Subgroup (Octonion ≃ₗ[ℝ] Octonion) where
  carrier := {f | ∀ x y, f (omul x y) = omul (f x) (f y)}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro f g hf hg x y
    simp only [LinearEquiv.mul_apply]
    rw [hg x y, hf (g x) (g y)]
  inv_mem' := by
    intro f hf x y
    simp only [LinearEquiv.coe_inv]
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hf (f.symm x) (f.symm y),
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Membership unfolding: `f ∈ octAut` is exactly the multiplicativity. -/
theorem mem_octAut {f : Octonion ≃ₗ[ℝ] Octonion} :
    f ∈ octAut ↔ ∀ x y, f (omul x y) = omul (f x) (f y) := Iff.rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: AUTOMORPHISMS FIX THE UNIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Every octonion automorphism fixes the unit:** φ(1) = 1.
    Proof: φ(1) is a left identity (φ(1)·y = y for all y, since φ is onto),
    and the left identity is unique. -/
theorem aut_fixes_one {f : Octonion ≃ₗ[ℝ] Octonion} (hf : f ∈ octAut) :
    f oone = oone := by
  have h : ∀ y, omul (f oone) y = y := by
    intro y
    obtain ⟨x, hx⟩ := f.surjective y
    rw [← hx, ← hf oone x, oone_omul]
  have h1 := h oone
  rwa [omul_oone] at h1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE NORM-FROM-MULTIPLICATION IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **x · x̄ = N(x)·1.** The octonion times its conjugate is its norm
    (times the unit). This is the algebraic identity from which the
    orthogonal/metric structure of 𝕆 — and hence the action of Aut(𝕆) on
    the 7-sphere of unit imaginary octonions — descends. -/
theorem omul_ostar (x : Octonion) : omul x (ostar x) = onormSq x • oone := by
  obtain ⟨a, b⟩ := x
  have e1 : a * star a - star (-b) * b
      = (Quaternion.normSq a + Quaternion.normSq b) • (1 : Quaternion ℝ) := by
    rw [star_neg, neg_mul, sub_neg_eq_add, Quaternion.self_mul_star,
        Quaternion.star_mul_self]
    ext <;> simp
  have e2 : (-b) * a + b * star (star a) = (0 : Quaternion ℝ) := by
    rw [star_star, neg_mul, neg_add_cancel]
  show ((a * star a - star (-b) * b), ((-b) * a + b * star (star a)))
      = onormSq (a, b) • oone
  rw [e1, e2]
  ext <;> simp [onormSq, oone]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: ORTHOGONALITY (NORM PRESERVATION) — THE REDUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem oone_ne_zero : (oone : Octonion) ≠ 0 := by
  simp only [oone, ne_eq, Prod.mk_eq_zero, not_and]
  intro h; exact absurd h one_ne_zero

/-- **An automorphism commuting with conjugation preserves the norm**
    (orthogonality). Since N(φx)·1 = φx·(φx)̄ = φx·φ(x̄) = φ(x·x̄) =
    φ(N(x)·1) = N(x)·1, and `• 1` is injective. This is the embedding
    Aut(𝕆) ↪ O(7); the unconditional conjugation-commutation (φ preserves
    the real-part splitting 𝕆 = ℝ1 ⊕ im 𝕆) is the one remaining cited
    Lie-theoretic input. -/
theorem aut_preserves_norm_of_commutes_conj
    {f : Octonion ≃ₗ[ℝ] Octonion} (hf : f ∈ octAut)
    (hconj : ∀ z, f (ostar z) = ostar (f z)) (x : Octonion) :
    onormSq (f x) = onormSq x := by
  have key : onormSq (f x) • (oone : Octonion) = onormSq x • oone := by
    calc onormSq (f x) • oone
        = omul (f x) (ostar (f x)) := (omul_ostar (f x)).symm
      _ = omul (f x) (f (ostar x)) := by rw [hconj]
      _ = f (omul x (ostar x)) := (hf x (ostar x)).symm
      _ = f (onormSq x • oone) := by rw [omul_ostar]
      _ = onormSq x • f oone := by rw [map_smul]
      _ = onormSq x • oone := by rw [aut_fixes_one hf]
  exact smul_left_injective ℝ oone_ne_zero key

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: G₂ BRIDGE (dimension data; group identity cited)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

def N_W : ℕ := 2
def disc : ℕ := 7

/-- **Aut(𝕆) ≅ G₂ — dimension data in framework atoms** (group identity
    cited from Lie theory). dim G₂ = 14 = N_W·disc, rank G₂ = 2 = N_W, and
    G₂ acts on im 𝕆 of real dimension 7 = disc; that 7-space is exactly the
    `dim_im_octonion` of the constructed algebra. -/
theorem aut_G2_bridge :
    (14 : ℕ) = N_W * disc
    ∧ (2 : ℕ) = N_W
    ∧ Module.finrank ℝ Octonion - 1 = disc := by
  refine ⟨?_, ?_, ?_⟩
  · unfold N_W disc; decide
  · unfold N_W; rfl
  · unfold disc; rw [dim_octonion]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE AUTOMORPHISM GROUP OF 𝕆, CONSTRUCTED.**

    The octonion automorphisms form a group `octAut ≤ 𝕆 ≃ₗ[ℝ] 𝕆`; each
    fixes the unit; the norm-from-multiplication identity x·x̄ = N(x)·1
    holds; and any automorphism commuting with conjugation is an isometry
    (orthogonality). Classically this group is G₂ (dim 14 = N_W·disc,
    rank 2 = N_W) acting on im 𝕆 ≅ ℝ⁷ = ℝ^disc — the substrate that
    `ColorFromG2`/`GenerationsEqualColors` invoke for colour SU(3).

    Zero sorry. Zero custom axioms. -/
theorem octonion_automorphisms_master :
    -- the automorphisms form a group (identity, composition, inverse closed)
    (1 : Octonion ≃ₗ[ℝ] Octonion) ∈ octAut
    ∧ (∀ f g, f ∈ octAut → g ∈ octAut → f * g ∈ octAut)
    ∧ (∀ f, f ∈ octAut → f⁻¹ ∈ octAut)
    -- automorphisms fix the unit
    ∧ (∀ f, f ∈ octAut → f oone = oone)
    -- norm-from-multiplication identity
    ∧ (∀ x : Octonion, omul x (ostar x) = onormSq x • oone)
    -- G₂ dimension data
    ∧ (14 : ℕ) = N_W * disc ∧ (2 : ℕ) = N_W := by
  refine ⟨octAut.one_mem, fun f g hf hg => octAut.mul_mem hf hg,
          fun f hf => octAut.inv_mem hf, fun f hf => aut_fixes_one hf,
          omul_ostar, ?_, ?_⟩
  · unfold N_W disc; decide
  · unfold N_W; rfl

end UnifiedTheory.LayerB.OctonionAutomorphisms
