/-
  Audit/KFCausalCSpecPoissonLayerRpow.lean   (Volume sector → the FRACTIONAL layer law)

  Correction of the natural-power layer scaling: the causal-set discreteness scale
  `ℓ² = ρ^{-2/d}` is FRACTIONAL (`ρ^{-1/2}` at `d = 4`), so it CANNOT come from a
  natural-power monomial `t^n` (which gives only `ρ^{-(n+1)}`, `n ∈ ℕ`).  The correct
  object is the real-power Poisson-layer integral, built on Mathlib's real-power Gamma
  integral `Real.integral_rpow_mul_exp_neg_mul_Ioi`.

  `poissonLayer_rpow`:  for `ρ, α > 0` and layer index `k : ℕ`,

      ∫_0^∞ e^{-ρ v} (ρ v)^k/k! · v^{α-1} dv  =  (Γ(k+α)/k!) · (1/ρ)^α.

  Every layer `k` has the SAME scaling `(1/ρ)^α = ρ^{-α}`; its coefficient is the explicit
  Gamma ratio `Γ(k+α)/k!`.  Setting `α = 2/d` gives the common `ρ^{-2/d} = ℓ²` layer law --
  now a proved fractional-power identity, the object the discreteness residue actually
  needs.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory Real Set Nat

namespace UnifiedTheory.Audit.KFCausalCSpecPoissonLayerRpow

/-- **Fractional Poisson-layer law.**  `∫_0^∞ e^{-ρ v} (ρ v)^k/k! · v^{α-1} dv =
(Γ(k+α)/k!)·(1/ρ)^α`.  Common fractional scaling `ρ^{-α}` across layers `k`, coefficient
the explicit Gamma ratio.  Setting `α = 2/d` yields the `ℓ² = ρ^{-2/d}` layer law. -/
theorem poissonLayer_rpow (ρ α : ℝ) (hρ : 0 < ρ) (hα : 0 < α) (k : ℕ) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-(ρ * v)) * ((ρ * v) ^ k / (k ! : ℝ)) * v ^ (α - 1)
      = Real.Gamma ((k : ℝ) + α) / (k ! : ℝ) * (1 / ρ) ^ α := by
  have hk : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hkα : 0 < (k : ℝ) + α := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun v => (ρ ^ k / (k ! : ℝ)) * (v ^ ((k : ℝ) + α - 1) * Real.exp (-(ρ * v)))) ?_]
  · rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hkα hρ]
    have h1 : ((1 : ℝ) / ρ) ^ ((k : ℝ) + α) = (1 / ρ) ^ k * (1 / ρ) ^ α := by
      rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    rw [h1, div_pow, one_pow]
    have hρk : ρ ^ k ≠ 0 := pow_ne_zero k hρ.ne'
    field_simp
  · intro v hv
    rw [mem_Ioi] at hv
    dsimp only
    rw [mul_pow, ← Real.rpow_natCast v k,
      show ((k : ℝ) + α - 1) = ((k : ℝ) + (α - 1)) by ring, Real.rpow_add hv]
    ring

/-- **The `α = 2/d` specialization: the `ℓ²` layer law.**  In dimension `d ≥ 1`, every
Poisson layer scales as `(1/ρ)^{2/d} = ρ^{-2/d} = ℓ²`, with coefficient `Γ(k+2/d)/k!`. -/
theorem poissonLayer_ell_squared (ρ : ℝ) (hρ : 0 < ρ) (d k : ℕ) (hd : 1 ≤ d) :
    ∫ v in Ioi (0 : ℝ),
        Real.exp (-(ρ * v)) * ((ρ * v) ^ k / (k ! : ℝ)) * v ^ ((2 / (d : ℝ)) - 1)
      = Real.Gamma ((k : ℝ) + 2 / (d : ℝ)) / (k ! : ℝ) * (1 / ρ) ^ (2 / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact poissonLayer_rpow ρ (2 / (d : ℝ)) hρ (by positivity) k

/-- Scaled Gamma-integrand integrability: `v ↦ v^{β-1} e^{-ρ v}` is integrable on `(0,∞)`.
Derived from Mathlib's `GammaIntegral_convergent` by the change of variables `x = ρ v`. -/
theorem integrableOn_rpow_exp (ρ β : ℝ) (hρ : 0 < ρ) (hβ : 0 < β) :
    IntegrableOn (fun v => v ^ (β - 1) * Real.exp (-(ρ * v))) (Ioi (0 : ℝ)) := by
  have hconv : IntegrableOn (fun x => Real.exp (-x) * x ^ (β - 1)) (Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent hβ
  have hscaled : IntegrableOn (fun v => Real.exp (-(ρ * v)) * (ρ * v) ^ (β - 1)) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x => Real.exp (-x) * x ^ (β - 1)) 0 hρ).mpr
    simp only [mul_zero] at h
    exact h hconv
  refine IntegrableOn.congr_fun (hscaled.const_mul ((ρ ^ (β - 1))⁻¹)) ?_ measurableSet_Ioi
  intro v hv
  rw [mem_Ioi] at hv
  dsimp only
  rw [Real.mul_rpow hρ.le hv.le]
  have hρβ : ρ ^ (β - 1) ≠ 0 := (Real.rpow_pos_of_pos hρ _).ne'
  field_simp

/-- **Remainder bound (controlled asymptotic extraction).**  If a shell remainder is
dominated by a power, `|R(v)| ≤ C · v^{β-1}` on `(0,∞)`, then its Laplace transform is
bounded by the corresponding Gamma term: `|∫_0^∞ e^{-ρ v} R(v) dv| ≤ C · Γ(β) · (1/ρ)^β`.
This controls the non-monomial tail of a local shell expansion `w = A v^{α-1} + …`, the
piece beyond the exact `poissonLayer_rpow` monomials. -/
theorem laplace_remainder_bound (ρ C β : ℝ) (hρ : 0 < ρ) (hβ : 0 < β) (R : ℝ → ℝ)
    (hbound : ∀ v ∈ Ioi (0 : ℝ), |R v| ≤ C * v ^ (β - 1)) :
    |∫ v in Ioi (0 : ℝ), Real.exp (-(ρ * v)) * R v| ≤ C * Real.Gamma β * (1 / ρ) ^ β := by
  have hgint : IntegrableOn (fun v => C * (v ^ (β - 1) * Real.exp (-(ρ * v)))) (Ioi (0 : ℝ)) :=
    (integrableOn_rpow_exp ρ β hρ hβ).const_mul C
  have hnorm : ∀ v ∈ Ioi (0 : ℝ),
      ‖Real.exp (-(ρ * v)) * R v‖ ≤ C * (v ^ (β - 1) * Real.exp (-(ρ * v))) := by
    intro v hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(ρ * v)) * |R v|
        ≤ Real.exp (-(ρ * v)) * (C * v ^ (β - 1)) :=
          mul_le_mul_of_nonneg_left (hbound v hv) (Real.exp_pos _).le
      _ = C * (v ^ (β - 1) * Real.exp (-(ρ * v))) := by ring
  calc |∫ v in Ioi (0 : ℝ), Real.exp (-(ρ * v)) * R v|
      = ‖∫ v in Ioi (0 : ℝ), Real.exp (-(ρ * v)) * R v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ v in Ioi (0 : ℝ), C * (v ^ (β - 1) * Real.exp (-(ρ * v))) :=
        norm_integral_le_of_norm_le hgint
          (ae_restrict_of_forall_mem measurableSet_Ioi hnorm)
    _ = C * Real.Gamma β * (1 / ρ) ^ β := by
        rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hβ hρ]
        ring

#print axioms poissonLayer_rpow
#print axioms poissonLayer_ell_squared
#print axioms integrableOn_rpow_exp
#print axioms laplace_remainder_bound

end UnifiedTheory.Audit.KFCausalCSpecPoissonLayerRpow
