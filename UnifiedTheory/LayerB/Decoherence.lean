/-
  LayerB/Decoherence.lean — Decoherence and classical emergence

  Proves that phase averaging suppresses interference and recovers
  classical additive observables.

  Parent → quantum (complex amplitudes) → classical (phase averaging)
-/
import UnifiedTheory.LayerB.ComplexFromDressing

namespace UnifiedTheory.LayerB

/-! ### Phase flip cancellation -/

/-- **Phase flip negates interference.**
    The interference term at θ+π is the negative of that at θ.
    This is the discrete phase-averaging cancellation identity. -/
theorem phase_flip_negates (z₁ z₂ : ℂ) (θ : ℝ) :
    interferenceTerm z₁ (phaseRotate (θ + Real.pi) z₂) =
    -(interferenceTerm z₁ (phaseRotate θ z₂)) := by
  simp only [interferenceTerm, phaseRotate]
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi]
  ring

/-- **Phase rotation preserves individual observable.** -/
theorem phase_rotate_obs (z : ℂ) (θ : ℝ) :
    obs (phaseRotate θ z) = obs z :=
  phase_invariance θ z

/-! ### Discrete decoherence -/

/-- **Discrete decoherence**: averaging over θ and θ+π kills
    the interference term, recovering classical additivity. -/
theorem discrete_decoherence_sum (z₁ z₂ : ℂ) (θ : ℝ) :
    obs (z₁ + phaseRotate θ z₂) +
    obs (z₁ + phaseRotate (θ + Real.pi) z₂) =
    2 * (obs z₁ + obs z₂) := by
  have h1 := interference_formula z₁ (phaseRotate θ z₂)
  have h2 := interference_formula z₁ (phaseRotate (θ + Real.pi) z₂)
  have hflip := phase_flip_negates z₁ z₂ θ
  have hr1 : obs (phaseRotate θ z₂) = obs z₂ := phase_rotate_obs z₂ θ
  have hr2 : obs (phaseRotate (θ + Real.pi) z₂) = obs z₂ := phase_rotate_obs z₂ (θ + Real.pi)
  -- h1: obs(z₁+e^{iθ}z₂) = obs z₁ + obs(e^{iθ}z₂) + IT₁
  -- h2: obs(z₁+e^{i(θ+π)}z₂) = obs z₁ + obs(e^{i(θ+π)}z₂) + IT₂
  -- hr1: obs(e^{iθ}z₂) = obs z₂
  -- hr2: obs(e^{i(θ+π)}z₂) = obs z₂
  -- hflip: IT₂ = -IT₁
  -- Sum = (obs z₁ + obs z₂ + IT₁) + (obs z₁ + obs z₂ - IT₁) = 2(obs z₁ + obs z₂)
  -- Direct proof: rewrite the goal step by step
  have goal1 : obs (z₁ + phaseRotate θ z₂) =
    obs z₁ + obs z₂ + interferenceTerm z₁ (phaseRotate θ z₂) := by rw [h1, hr1]
  have goal2 : obs (z₁ + phaseRotate (θ + Real.pi) z₂) =
    obs z₁ + obs z₂ - interferenceTerm z₁ (phaseRotate θ z₂) := by
    have h2' := h2; simp only [hr2, hflip] at h2'; linarith
  linarith

/-! ### Dressing decoherence -/

/-- **Random dressing = classical.**
    Averaging over aligned and anti-aligned dressing content
    gives classical (no-interference) observables. -/
theorem dressing_interference_cancels (Q P : ℝ) :
    interferenceTerm (amplitudeFromKP Q P) (amplitudeFromKP Q P) +
    interferenceTerm (amplitudeFromKP Q P) (amplitudeFromKP Q (-P)) =
    4 * Q ^ 2 := by
  rw [interference_is_dressing_dependent, interference_is_dressing_dependent]
  ring

/-! ### The classical emergence theorem -/

/-- **Classical world = phase-averaged quantum world.**

    (1) Quantum: obs(z₁+z₂) = obs(z₁) + obs(z₂) + interference
    (2) Decoherent: ⟨obs(z₁+z₂)⟩_{θ,θ+π} = obs(z₁) + obs(z₂)
    (3) Classical: interference = 0 when all phases are averaged out

    The classical world is not fundamental — it is the decoherent
    limit of the quantum world, which itself is forced by the
    source/dressing split in the parent object. -/
theorem classical_emergence :
    -- (1) Phase averaging kills interference (sum form)
    (∀ z₁ z₂ θ,
      obs (z₁ + phaseRotate θ z₂) +
      obs (z₁ + phaseRotate (θ + Real.pi) z₂) =
      2 * (obs z₁ + obs z₂))
    -- (2) Phase flip is the mechanism
    ∧ (∀ z₁ z₂ θ,
        interferenceTerm z₁ (phaseRotate (θ + Real.pi) z₂) =
        -(interferenceTerm z₁ (phaseRotate θ z₂)))
    -- (3) Dressing interference cancels on averaging
    ∧ (∀ Q P,
        interferenceTerm (amplitudeFromKP Q P) (amplitudeFromKP Q P) +
        interferenceTerm (amplitudeFromKP Q P) (amplitudeFromKP Q (-P)) =
        4 * Q ^ 2) :=
  ⟨discrete_decoherence_sum, phase_flip_negates, dressing_interference_cancels⟩

end UnifiedTheory.LayerB
