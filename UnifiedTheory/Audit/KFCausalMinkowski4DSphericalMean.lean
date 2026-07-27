/-
  Audit/KFCausalMinkowski4DSphericalMean.lean — the spherical-mean r²-expansion

  The 4D BDG gate consumes the field only through its S²-average.  This file
  proves the mean-value expansion at jet level, with the sphere average DEFINED
  by the explicit parametrization

    M[φ](r) = (1/4π) ∫₀^π ∫₀^{2π} φ(r sinθ cosψ, r sinθ sinψ, r cosθ) sinθ dψ dθ,

  (the standard surface measure `sinθ dθ dψ`, total mass 4π): for the full
  quadratic jet

    φ = c₀ + b·x + ½ xᵀHx,

  the off-diagonal and linear terms average to zero and

    M[φ](r) = c₀ + (r²/6)·tr H          (exactly — no remainder at jet level).

  This is the `M = φ + r²Δφ/6` input of the gate dictionary
  (`gate_spherical_value`): the trace `tr H = Δφ` enters with the coefficient
  `1/6` that the jet dictionary turns into the Lorentz-invariant `□φ`.

  All integrals are elementary FTC/trig evaluations — no axioms beyond Mathlib.
-/
import Mathlib

open MeasureTheory Real Set intervalIntegral

namespace UnifiedTheory.Audit.KFCausalMinkowski4DSphericalMean

/-- The spherical mean over the radius-`r` sphere, in the explicit
`(θ, ψ)`-parametrization with surface element `sinθ dθ dψ` and normalization
`1/4π`. -/
noncomputable def sphericalMean (φ : ℝ → ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  (1/(4*π)) * ∫ θ in (0:ℝ)..π, (∫ ψ in (0:ℝ)..(2*π),
    φ (r * Real.sin θ * Real.cos ψ) (r * Real.sin θ * Real.sin ψ)
      (r * Real.cos θ)) * Real.sin θ

/-! ## The five ψ-atoms -/

theorem psi_cos : ∫ ψ in (0:ℝ)..(2*π), Real.cos ψ = 0 := by
  rw [integral_cos, Real.sin_two_pi, Real.sin_zero, sub_zero]

theorem psi_sin : ∫ ψ in (0:ℝ)..(2*π), Real.sin ψ = 0 := by
  rw [integral_sin, Real.cos_two_pi, Real.cos_zero, sub_self]

theorem psi_cos_sq : ∫ ψ in (0:ℝ)..(2*π), Real.cos ψ ^ 2 = π := by
  rw [integral_cos_sq]
  simp [Real.sin_two_pi, Real.cos_two_pi]

theorem psi_sin_sq : ∫ ψ in (0:ℝ)..(2*π), Real.sin ψ ^ 2 = π := by
  rw [integral_sin_sq]
  simp [Real.sin_two_pi, Real.cos_two_pi]

theorem psi_sin_cos : ∫ ψ in (0:ℝ)..(2*π), Real.sin ψ * Real.cos ψ = 0 := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) (2*π), HasDerivAt (fun t => Real.sin t ^ 2 / 2)
      (Real.sin x * Real.cos x) x := by
    intro x _
    have h := ((Real.hasDerivAt_sin x).pow 2).div_const 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [Real.sin_two_pi]

/-! ## The four θ-atoms -/

theorem theta_sin : ∫ θ in (0:ℝ)..π, Real.sin θ = 2 := by
  rw [integral_sin, Real.cos_pi, Real.cos_zero]
  ring

theorem theta_cos_sin : ∫ θ in (0:ℝ)..π, Real.cos θ * Real.sin θ = 0 := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) π, HasDerivAt (fun t => Real.sin t ^ 2 / 2)
      (Real.cos x * Real.sin x) x := by
    intro x _
    have h := ((Real.hasDerivAt_sin x).pow 2).div_const 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [Real.sin_pi]

theorem theta_cossq_sin : ∫ θ in (0:ℝ)..π, Real.cos θ ^ 2 * Real.sin θ = 2/3 := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) π, HasDerivAt (fun t => -(Real.cos t ^ 3) / 3)
      (Real.cos x ^ 2 * Real.sin x) x := by
    intro x _
    have h := (((Real.hasDerivAt_cos x).pow 3).div_const 3).neg
    simpa [neg_div, mul_comm, mul_assoc, mul_left_comm] using h
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [Real.cos_pi]
  norm_num

theorem theta_sin_cubed : ∫ θ in (0:ℝ)..π, Real.sin θ ^ 3 = 4/3 := by
  have hcong : ∀ θ ∈ uIcc (0:ℝ) π,
      Real.sin θ ^ 3 = Real.sin θ - Real.cos θ ^ 2 * Real.sin θ := by
    intro θ _
    have h := Real.sin_sq_add_cos_sq θ
    linear_combination Real.sin θ * h
  rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    theta_sin, theta_cossq_sin]
  norm_num

/-! ## The jet expansion -/

/-- **The spherical-mean r²-expansion at jet level**: for the full quadratic jet,

    M[c₀ + b·x + ½xᵀHx](r) = c₀ + (r²/6)·(H₁₁ + H₂₂ + H₃₃).

The linear and off-diagonal terms average to zero; the diagonal second-order
terms each contribute `r²/6` of their coefficient — the `Δφ/6` of the classical
mean-value expansion, exact for jets. -/
theorem sphericalMean_quadratic (c₀ b₁ b₂ b₃ h₁₁ h₂₂ h₃₃ h₁₂ h₁₃ h₂₃ r : ℝ) :
    sphericalMean (fun x y z => c₀ + b₁*x + b₂*y + b₃*z
      + (1/2)*(h₁₁*x^2 + h₂₂*y^2 + h₃₃*z^2) + h₁₂*x*y + h₁₃*x*z + h₂₃*y*z) r
    = c₀ + r^2/6 * (h₁₁ + h₂₂ + h₃₃) := by
  unfold sphericalMean
  have hπ : (0:ℝ) < π := Real.pi_pos
  -- inner ψ-integral, for fixed θ
  have hinner : ∀ θ : ℝ, (∫ ψ in (0:ℝ)..(2*π),
      (c₀ + b₁*(r * Real.sin θ * Real.cos ψ) + b₂*(r * Real.sin θ * Real.sin ψ)
        + b₃*(r * Real.cos θ)
        + (1/2)*(h₁₁*(r * Real.sin θ * Real.cos ψ)^2
          + h₂₂*(r * Real.sin θ * Real.sin ψ)^2 + h₃₃*(r * Real.cos θ)^2)
        + h₁₂*(r * Real.sin θ * Real.cos ψ)*(r * Real.sin θ * Real.sin ψ)
        + h₁₃*(r * Real.sin θ * Real.cos ψ)*(r * Real.cos θ)
        + h₂₃*(r * Real.sin θ * Real.sin ψ)*(r * Real.cos θ)))
      = (2*π) * (c₀ + b₃*(r*Real.cos θ) + (1/2)*h₃₃*(r*Real.cos θ)^2)
        + (π/2) * r^2 * Real.sin θ^2 * (h₁₁ + h₂₂) := by
    intro θ
    have hexp : ∀ ψ : ℝ,
        (c₀ + b₁*(r * Real.sin θ * Real.cos ψ) + b₂*(r * Real.sin θ * Real.sin ψ)
          + b₃*(r * Real.cos θ)
          + (1/2)*(h₁₁*(r * Real.sin θ * Real.cos ψ)^2
            + h₂₂*(r * Real.sin θ * Real.sin ψ)^2 + h₃₃*(r * Real.cos θ)^2)
          + h₁₂*(r * Real.sin θ * Real.cos ψ)*(r * Real.sin θ * Real.sin ψ)
          + h₁₃*(r * Real.sin θ * Real.cos ψ)*(r * Real.cos θ)
          + h₂₃*(r * Real.sin θ * Real.sin ψ)*(r * Real.cos θ))
        = (c₀ + b₃*(r*Real.cos θ) + (1/2)*h₃₃*(r*Real.cos θ)^2)
          + (b₁*r*Real.sin θ + h₁₃*r^2*Real.sin θ*Real.cos θ) * Real.cos ψ
          + (b₂*r*Real.sin θ + h₂₃*r^2*Real.sin θ*Real.cos θ) * Real.sin ψ
          + ((1/2)*h₁₁*r^2*Real.sin θ^2) * Real.cos ψ^2
          + ((1/2)*h₂₂*r^2*Real.sin θ^2) * Real.sin ψ^2
          + (h₁₂*r^2*Real.sin θ^2) * (Real.sin ψ * Real.cos ψ) := by
      intro ψ
      ring
    rw [intervalIntegral.integral_congr (fun ψ _ => hexp ψ)]
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      psi_cos, psi_sin, psi_cos_sq, psi_sin_sq, psi_sin_cos]
    simp only [smul_eq_mul, mul_zero, add_zero, sub_zero]
    ring
  -- substitute the inner value and integrate over θ
  have houter : (∫ θ in (0:ℝ)..π, (∫ ψ in (0:ℝ)..(2*π),
      (fun x y z => c₀ + b₁*x + b₂*y + b₃*z
        + (1/2)*(h₁₁*x^2 + h₂₂*y^2 + h₃₃*z^2) + h₁₂*x*y + h₁₃*x*z + h₂₃*y*z)
        (r * Real.sin θ * Real.cos ψ) (r * Real.sin θ * Real.sin ψ)
        (r * Real.cos θ)) * Real.sin θ)
      = ∫ θ in (0:ℝ)..π,
        ((2*π*c₀) * Real.sin θ
          + (2*π*b₃*r) * (Real.cos θ * Real.sin θ)
          + (π*h₃₃*r^2) * (Real.cos θ^2 * Real.sin θ)
          + ((π/2)*r^2*(h₁₁+h₂₂)) * Real.sin θ^3) := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [hinner θ]
    have hs3 : Real.sin θ^3 = Real.sin θ^2 * Real.sin θ := by ring
    rw [hs3]
    ring
  rw [houter,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    theta_sin, theta_cos_sin, theta_cossq_sin, theta_sin_cubed]
  field_simp
  ring

#print axioms sphericalMean_quadratic

end UnifiedTheory.Audit.KFCausalMinkowski4DSphericalMean
