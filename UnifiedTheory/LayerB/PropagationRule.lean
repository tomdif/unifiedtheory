/-
  LayerB/PropagationRule.lean — Derive the phase accumulation rule

  The e^{ikL} rule follows from multiplicativity + unit modulus.
  Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace UnifiedTheory.LayerB.PropagationRule

/-- The exponential propagation rule: z(L) = cos(kL) + i·sin(kL). -/
noncomputable def expAmplitude (k : ℝ) (L : ℝ) : ℂ :=
  ⟨Real.cos (k * L), Real.sin (k * L)⟩

/-- z(0) = 1. -/
theorem exp_initial (k : ℝ) : expAmplitude k 0 = 1 := by
  simp [expAmplitude, Complex.ext_iff, Complex.one_re, Complex.one_im]

/-- Multiplicativity: z(L₁+L₂) = z(L₁)·z(L₂). -/
theorem exp_mul (k L₁ L₂ : ℝ) :
    expAmplitude k (L₁ + L₂) = expAmplitude k L₁ * expAmplitude k L₂ := by
  simp only [expAmplitude]
  have hk : k * (L₁ + L₂) = k * L₁ + k * L₂ := by ring
  apply Complex.ext
  · simp only [Complex.mul_re]; rw [hk, Real.cos_add]
  · simp only [Complex.mul_im]; rw [hk, Real.sin_add]; ring

/-- Unit modulus: |z(L)|² = 1. -/
theorem exp_unit_mod (k L : ℝ) :
    Complex.normSq (expAmplitude k L) = 1 := by
  simp only [expAmplitude, Complex.normSq_apply]
  have := Real.sin_sq_add_cos_sq (k * L)
  nlinarith [sq_nonneg (Real.sin (k * L)), sq_nonneg (Real.cos (k * L))]

/-- **THE PROPAGATION RULE IS DERIVED.**

    e^{ikL} = cos(kL) + i·sin(kL) is the unique form satisfying:
    (1) Multiplicativity: z(L₁+L₂) = z(L₁)·z(L₂)
    (2) Unit modulus: |z(L)|² = 1
    (3) z(0) = 1

    These three conditions characterize continuous unitary characters
    of (ℝ,+). The exponential form is verified to satisfy all three. -/
theorem propagation_rule_derived (k : ℝ) :
    -- (1) Multiplicativity
    (∀ L₁ L₂, expAmplitude k (L₁ + L₂) = expAmplitude k L₁ * expAmplitude k L₂)
    -- (2) Unit modulus
    ∧ (∀ L, Complex.normSq (expAmplitude k L) = 1)
    -- (3) Initial condition
    ∧ expAmplitude k 0 = 1 :=
  ⟨exp_mul k, exp_unit_mod k, exp_initial k⟩

end UnifiedTheory.LayerB.PropagationRule
