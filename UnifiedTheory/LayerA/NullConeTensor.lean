/-
  Layer A.3 — Null-cone tensor lemma (1+1 dimensional version)

  In ℝ^{1+1} with Minkowski form η(v) = -v₀² + v₁²:

  If a symmetric quadratic form S(v) = a·v₀² + 2b·v₀v₁ + c·v₁²
  vanishes on all null vectors (η(v) = 0), then S = λ·η.

  Proof: evaluate at (1,1) and (1,-1), extract b = 0 and c = -a.

  This is the concrete linear-algebra core of the null-cone determination
  theorem. The general n+1 dimensional version follows the same strategy.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace UnifiedTheory.LayerA

section NullCone

/-- Minkowski quadratic form on ℝ^{1+1}. -/
def minkQuad (v : Fin 2 → ℝ) : ℝ := -(v 0) ^ 2 + (v 1) ^ 2

/-- Minkowski bilinear form on ℝ^{1+1}. -/
def minkBilin (v w : Fin 2 → ℝ) : ℝ := -(v 0) * (w 0) + (v 1) * (w 1)

/-- General symmetric quadratic form on ℝ², parametrized by (a, b, c). -/
def genQuad (a b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  a * (v 0) ^ 2 + 2 * b * (v 0) * (v 1) + c * (v 1) ^ 2

/-- General symmetric bilinear form on ℝ², parametrized by (a, b, c). -/
def genBilin (a b c : ℝ) (v w : Fin 2 → ℝ) : ℝ :=
  a * (v 0) * (w 0) + b * ((v 0) * (w 1) + (v 1) * (w 0)) + c * (v 1) * (w 1)

/-- The quadratic form is the diagonal of the bilinear form. -/
lemma genQuad_eq_genBilin (a b c : ℝ) (v : Fin 2 → ℝ) :
    genQuad a b c v = genBilin a b c v v := by
  simp only [genQuad, genBilin]; ring

/-- Similarly for Minkowski. -/
lemma minkQuad_eq_minkBilin (v : Fin 2 → ℝ) :
    minkQuad v = minkBilin v v := by
  simp only [minkQuad, minkBilin]; ring

/-- Test vector (1, 1): the constant-1 function. -/
private def v_pp : Fin 2 → ℝ := fun _ => 1

/-- Test vector (1, -1). -/
private def v_pm : Fin 2 → ℝ := fun i => if i = (0 : Fin 2) then 1 else -1

private lemma v_pp_0 : v_pp 0 = 1 := rfl
private lemma v_pp_1 : v_pp 1 = 1 := rfl
private lemma v_pm_0 : v_pm 0 = 1 := if_pos rfl
private lemma v_pm_1 : v_pm 1 = -1 := by
  simp only [v_pm, ite_eq_right_iff]
  decide

private lemma v_pp_null : minkQuad v_pp = 0 := by
  simp only [minkQuad, v_pp_0, v_pp_1]; ring

private lemma v_pm_null : minkQuad v_pm = 0 := by
  simp only [minkQuad, v_pm_0, v_pm_1]; ring

/-- Coefficient extraction: null-vanishing forces b = 0 and c = -a. -/
theorem null_cone_coeffs (a b c : ℝ)
    (h : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a b c v = 0) :
    b = 0 ∧ c = -a := by
  have h1 := h v_pp v_pp_null
  have h2 := h v_pm v_pm_null
  simp only [genQuad, v_pp_0, v_pp_1, v_pm_0, v_pm_1] at h1 h2
  constructor <;> nlinarith

/-- Null-cone theorem (quadratic form version, 1+1 dim):
    If a symmetric quadratic form vanishes on all null vectors,
    it is proportional to the Minkowski quadratic form. -/
theorem null_cone_quad_1plus1 (a b c : ℝ)
    (h : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a b c v = 0) :
    ∀ v, genQuad a b c v = (-a) * minkQuad v := by
  obtain ⟨hb, hc⟩ := null_cone_coeffs a b c h
  intro v
  simp only [genQuad, minkQuad, hb, hc]
  ring

/-- Null-cone theorem (bilinear form version, 1+1 dim):
    If a symmetric bilinear form vanishes on all null vectors,
    it is proportional to the Minkowski bilinear form. -/
theorem null_cone_bilin_1plus1 (a b c : ℝ)
    (h : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a b c v = 0) :
    ∀ v w, genBilin a b c v w = (-a) * minkBilin v w := by
  obtain ⟨hb, hc⟩ := null_cone_coeffs a b c h
  intro v w
  simp only [genBilin, minkBilin, hb, hc]
  ring

/-- The full null-cone determination theorem (1+1 dim, existential form):
    Any symmetric bilinear form whose quadratic form vanishes on the
    null cone is proportional to the Minkowski form. -/
theorem null_determines_up_to_trace_1plus1 (a b c : ℝ)
    (h : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a b c v = 0) :
    ∃ c₀ : ℝ, ∀ v w, genBilin a b c v w = c₀ * minkBilin v w :=
  ⟨-a, null_cone_bilin_1plus1 a b c h⟩

end NullCone

end UnifiedTheory.LayerA
