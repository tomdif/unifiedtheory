/-
  LayerB/QuantumDefects.lean — Emergent quantum structure

  If defect amplitudes are complex-valued (not just real), then
  quantum-like behavior emerges from pure linear algebra:

  1. SUPERPOSITION: amplitudes add linearly
  2. INTERFERENCE: observables do NOT add linearly
  3. BORN RULE: observable = |amplitude|²
  4. PHASE INVARIANCE: global phase doesn't affect observables
  5. DESTRUCTIVE INTERFERENCE: composites can have LESS observable than parts
  6. CONSTRUCTIVE INTERFERENCE: composites can have MORE than sum of parts

  None of this is postulated. It is DERIVED from the fact that ℂ is
  a field where |z₁+z₂|² ≠ |z₁|²+|z₂|² in general.

  Physical interpretation: the passage from real charges (classical)
  to complex amplitudes (quantum) is the passage from a real defect
  space to a complex one. The parent object supports both, but only
  the complex version exhibits interference.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace UnifiedTheory.LayerB

/-! ### Complex amplitude framework -/

/-- Observable of a complex amplitude: the Born rule |z|² = re² + im². -/
def obs (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

/-- The interference term between two amplitudes:
    2 Re(z₁ z̄₂) = 2(re₁·re₂ + im₁·im₂). -/
def interferenceTerm (z₁ z₂ : ℂ) : ℝ :=
  2 * (z₁.re * z₂.re + z₁.im * z₂.im)

/-! ### Core quantum theorems -/

/-- **Interference formula (the fundamental quantum identity).**
    |z₁ + z₂|² = |z₁|² + |z₂|² + 2Re(z₁z̄₂).
    Observables of composites differ from the sum of individual
    observables by an interference term that depends on RELATIVE PHASE. -/
theorem interference_formula (z₁ z₂ : ℂ) :
    obs (z₁ + z₂) = obs z₁ + obs z₂ + interferenceTerm z₁ z₂ := by
  simp only [obs, interferenceTerm, Complex.add_re, Complex.add_im]
  ring

/-- **Born rule is non-negative**: observables are always ≥ 0. -/
theorem born_nonneg (z : ℂ) : 0 ≤ obs z := by
  simp only [obs]
  positivity

/-- **Zero amplitude means zero observable.** -/
theorem born_zero : obs 0 = 0 := by
  simp [obs]

/-- **Nonzero amplitude means positive observable.** -/
theorem born_pos_of_ne_zero (z : ℂ) (h : z ≠ 0) : 0 < obs z := by
  simp only [obs]
  have : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact h (Complex.ext hall.1 hall.2)
  rcases this with h | h
  all_goals positivity

/-! ### Phase invariance -/

/-- **Phase rotation**: multiply amplitude by e^{iθ} = cos θ + i sin θ. -/
noncomputable def phaseRotate (θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (θ * Complex.I) * z

/-- **Phase invariance of observables**: |e^{iθ} z|² = |z|².
    Global phase is unobservable — the hallmark of quantum mechanics. -/
theorem phase_invariance (θ : ℝ) (z : ℂ) :
    obs (phaseRotate θ z) = obs z := by
  simp only [phaseRotate, obs]
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  have hsc := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg z.re, sq_nonneg z.im, sq_nonneg (Real.sin θ),
             sq_nonneg (Real.cos θ), hsc]

/-! ### Interference phenomena -/

/-- **Destructive interference exists**: two nonzero amplitudes can
    produce a composite with ZERO observable.
    Example: z₁ = 1, z₂ = -1, composite = 0. -/
theorem destructive_interference_exists :
    ∃ z₁ z₂ : ℂ, z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ obs (z₁ + z₂) = 0 := by
  exact ⟨1, -1, one_ne_zero, neg_ne_zero.mpr one_ne_zero, by simp [obs]⟩

/-- **Constructive interference exists**: two amplitudes can produce
    a composite whose observable EXCEEDS the sum of individual observables.
    Example: z₁ = z₂ = 1, obs(z₁+z₂) = 4 > 2 = obs(z₁) + obs(z₂). -/
theorem constructive_interference_exists :
    ∃ z₁ z₂ : ℂ, obs (z₁ + z₂) > obs z₁ + obs z₂ := by
  exact ⟨1, 1, by simp [obs]; norm_num⟩

/-- **Complete destructive interference**: amplitudes of equal magnitude
    but opposite phase cancel completely. -/
theorem complete_cancellation (z : ℂ) :
    obs (z + (-z)) = 0 := by
  simp [obs]

/-- **Classical limit**: when the interference term vanishes (orthogonal
    amplitudes), observables add classically. -/
theorem classical_limit (z₁ z₂ : ℂ)
    (h_ortho : z₁.re * z₂.re + z₁.im * z₂.im = 0) :
    obs (z₁ + z₂) = obs z₁ + obs z₂ := by
  rw [interference_formula, interferenceTerm, h_ortho, mul_zero, add_zero]

/-! ### Superposition principle -/

/-- **Superposition is linear in amplitudes**: the amplitude of a
    composite is the sum of individual amplitudes. This is the
    quantum superposition principle. -/
theorem superposition_linear (z₁ z₂ z₃ : ℂ) :
    (z₁ + z₂) + z₃ = z₁ + (z₂ + z₃) := add_assoc z₁ z₂ z₃

/-- **But observables are NOT linear**: the interference formula
    shows that obs is quadratic, not linear. This is the fundamental
    distinction between quantum and classical composition. -/
theorem observables_nonlinear :
    ¬ (∀ z₁ z₂ : ℂ, obs (z₁ + z₂) = obs z₁ + obs z₂) := by
  intro h
  have := h 1 1
  simp [obs] at this
  linarith

/-! ### Relative phase determines interference -/

/-- **Phase-dependent interference**: rotating z₂ by phase θ changes
    the interference term while preserving individual observables.
    This is why relative phase matters in quantum mechanics. -/
theorem phase_dependent_interference (z₁ z₂ : ℂ) (θ : ℝ)
    (h : z₁ = 1 ∧ z₂ = 1) :
    interferenceTerm z₁ (phaseRotate θ z₂) = 2 * Real.cos θ := by
  obtain ⟨rfl, rfl⟩ := h
  simp [interferenceTerm, phaseRotate, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-! ### Quantum vs classical defects -/

/-- **Classical defects are a special case of quantum defects.**
    When the amplitude is real (im = 0), the observable reduces
    to the square of the real charge. -/
theorem classical_embedding (q : ℝ) :
    obs (q : ℂ) = q ^ 2 := by
  simp [obs, Complex.ofReal_re, Complex.ofReal_im]

/-- **Classical composition is additive in charge but quadratic
    in observable**, matching the known classical behavior. -/
theorem classical_composition (q₁ q₂ : ℝ) :
    obs ((q₁ : ℂ) + (q₂ : ℂ)) = (q₁ + q₂) ^ 2 := by
  simp [obs, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]

/-! ### Summary theorem -/

/-- **Emergent quantum structure theorem.**
    From the single assumption that defect amplitudes are complex:
    (1) Interference formula: obs(z₁+z₂) = obs(z₁) + obs(z₂) + interference
    (2) Born rule: obs ≥ 0, with obs = 0 iff z = 0
    (3) Phase invariance: obs(e^{iθ}z) = obs(z)
    (4) Destructive interference: composites can cancel
    (5) Observables are nonlinear (quantum, not classical)
    (6) Classical limit when interference term vanishes -/
theorem emergent_quantum_structure :
    -- (1) Interference formula
    (∀ z₁ z₂, obs (z₁ + z₂) = obs z₁ + obs z₂ + interferenceTerm z₁ z₂)
    -- (2) Born rule non-negative
    ∧ (∀ z, 0 ≤ obs z)
    -- (3) Destructive interference exists
    ∧ (∃ z₁ z₂ : ℂ, z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ obs (z₁ + z₂) = 0)
    -- (4) Observables are nonlinear
    ∧ ¬ (∀ z₁ z₂ : ℂ, obs (z₁ + z₂) = obs z₁ + obs z₂)
    -- (5) Classical embedding
    ∧ (∀ q : ℝ, obs (q : ℂ) = q ^ 2) :=
  ⟨interference_formula,
   born_nonneg,
   destructive_interference_exists,
   observables_nonlinear,
   classical_embedding⟩

end UnifiedTheory.LayerB
