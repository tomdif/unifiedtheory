/-
  LayerB/OctonionOrthogonal.lean — Octonion automorphisms are isometries
                                    (Aut(𝕆) ⊆ O(7)), unconditionally.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PURPOSE

  `OctonionAutomorphisms.lean` reduced "automorphisms preserve the norm"
  to the hypothesis that they commute with conjugation. This file removes
  that hypothesis: EVERY octonion automorphism preserves the norm. The key
  is the QUADRATIC MINIMAL POLYNOMIAL — every octonion satisfies

      x²  =  t(x)·x  −  N(x)·1                                  (oquadratic)

  with real trace t(x) = 2·Re(x) and norm N(x) = onormSq x. This is the
  precise sense in which the real line ℝ·1 is canonical (𝕆 is a "quadratic
  algebra"): t and N are algebraically determined, so any automorphism —
  being ℝ-linear, unital and multiplicative — must preserve them. Applying
  φ to the quadratic and using ℝ-linear independence of {φx, 1} (for
  x ∉ ℝ·1) forces N(φx) = N(x). The result is the embedding Aut(𝕆) ↪ O(7)
  underlying G₂ ⊂ SO(7).

  WHAT IS PROVED (zero sorry, zero custom axioms)
   • `oquadratic` — x² = t(x)·x − N(x)·1 for every octonion.
   • `onormSq_smul`, `onormSq_oone` — the norm of r·1 is r².
   • `aut_preserves_norm` — N(φx) = N(x) for every φ ∈ Aut(𝕆),
     UNCONDITIONALLY. (Upgrades `aut_preserves_norm_of_commutes_conj`.)

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.OctonionAutomorphisms
import Mathlib.Tactic.Module

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.OctonionOrthogonal

open UnifiedTheory.LayerB.Octonions
open UnifiedTheory.LayerB.OctonionAutomorphisms

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: TRACE AND THE QUADRATIC MINIMAL POLYNOMIAL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The octonion trace t(x) = 2·Re(x) (twice the real part of the first
    Cayley–Dickson component). -/
def otrace (x : Octonion) : ℝ := 2 * x.1.re

/-- **The quadratic minimal polynomial:** x·x = t(x)·x − N(x)·1.
    Every octonion is a root of a real quadratic — the structural origin
    of trace, norm and the canonical real line ℝ·1. -/
theorem oquadratic (x : Octonion) :
    omul x x = otrace x • x - onormSq x • oone := by
  obtain ⟨a, b⟩ := x
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · show a * a - star b * b
        = (2 * a.re) • a - (Quaternion.normSq a + Quaternion.normSq b) • (1 : Quaternion ℝ)
    ext <;>
      simp only [nsq, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
                 Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
                 Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_sub,
                 Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
                 Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
                 Quaternion.imK_smul, Quaternion.one_re, Quaternion.one_imI,
                 Quaternion.one_imJ, Quaternion.one_imK, smul_eq_mul] <;>
      ring
  · show b * a + b * star a
        = (2 * a.re) • b - (Quaternion.normSq a + Quaternion.normSq b) • (0 : Quaternion ℝ)
    ext <;>
      simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
                 Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
                 Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_add,
                 Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                 Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
                 Quaternion.imK_smul, smul_zero, sub_zero, smul_eq_mul] <;>
      ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: NORM OF SCALARS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem onormSq_smul (r : ℝ) (x : Octonion) : onormSq (r • x) = r ^ 2 * onormSq x := by
  obtain ⟨a, b⟩ := x
  simp only [onormSq, Prod.smul_fst, Prod.smul_snd, Quaternion.normSq_smul]
  ring

theorem onormSq_oone : onormSq (oone : Octonion) = 1 := by
  simp only [onormSq, oone, map_one, map_zero, add_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: AUTOMORPHISMS PRESERVE THE NORM (UNCONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- An automorphism maps the real line to itself, fixing it pointwise. -/
theorem aut_symm_fixes_one {f : Octonion ≃ₗ[ℝ] Octonion} (hf : f ∈ octAut) :
    f.symm oone = oone := by
  have h := aut_fixes_one (octAut.inv_mem hf)
  rwa [LinearEquiv.coe_inv] at h

/-- **Aut(𝕆) ⊆ O(7): every octonion automorphism is an isometry.**
    N(φx) = N(x), unconditionally. -/
theorem aut_preserves_norm {f : Octonion ≃ₗ[ℝ] Octonion} (hf : f ∈ octAut)
    (x : Octonion) : onormSq (f x) = onormSq x := by
  by_cases hx : ∃ r : ℝ, x = r • oone
  · obtain ⟨r, rfl⟩ := hx
    rw [map_smul, aut_fixes_one hf]
  · -- Apply φ to the quadratic for x; compare with the quadratic for φx.
    have hq : otrace x • f x - onormSq x • oone
            = otrace (f x) • f x - onormSq (f x) • oone := by
      have h1 : f (omul x x) = omul (f x) (f x) := hf x x
      rw [oquadratic, map_sub, map_smul, map_smul, aut_fixes_one hf, oquadratic] at h1
      exact h1
    have h0 : (otrace x - otrace (f x)) • f x + (onormSq (f x) - onormSq x) • oone = 0 := by
      have hsub := sub_eq_zero.mpr hq
      rw [← hsub]; module
    -- φx is not in ℝ·1 (else x would be)
    have hfx : ¬ ∃ s : ℝ, f x = s • oone := by
      rintro ⟨s, hs⟩
      exact hx ⟨s, by rw [← aut_symm_fixes_one hf, ← map_smul, ← hs, f.symm_apply_apply]⟩
    -- linear independence of {φx, 1}: both coefficients of h0 vanish
    by_cases hα : otrace x - otrace (f x) = 0
    · rw [hα, zero_smul, zero_add] at h0
      rcases smul_eq_zero.mp h0 with hγ | hone
      · exact sub_eq_zero.mp hγ
      · exact absurd hone oone_ne_zero
    · exfalso
      apply hfx
      refine ⟨-(onormSq (f x) - onormSq x) / (otrace x - otrace (f x)), ?_⟩
      have key : (otrace x - otrace (f x)) • f x = (-(onormSq (f x) - onormSq x)) • oone := by
        rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
      rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hα, one_smul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: MASTER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE OCTONION QUADRATIC LAW AND AUTOMORPHISM ISOMETRY.**

    Every octonion satisfies x² = t(x)·x − N(x)·1 (so ℝ·1 is the canonical
    real line of a quadratic algebra), and consequently every automorphism
    preserves the norm, N(φx) = N(x) — unconditionally. This is the
    embedding Aut(𝕆) ↪ O(7) beneath G₂ ⊂ SO(7), now proven without the
    conjugation-commutation hypothesis.

    Zero sorry. Zero custom axioms. -/
theorem octonion_orthogonal_master :
    (∀ x : Octonion, omul x x = otrace x • x - onormSq x • oone)
    ∧ onormSq (oone : Octonion) = 1
    ∧ (∀ {f : Octonion ≃ₗ[ℝ] Octonion}, f ∈ octAut →
        ∀ x : Octonion, onormSq (f x) = onormSq x) :=
  ⟨oquadratic, onormSq_oone, fun hf x => aut_preserves_norm hf x⟩

end UnifiedTheory.LayerB.OctonionOrthogonal
