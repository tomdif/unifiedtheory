/-
  Audit/KFCausalMinkowski4DMoments.lean   (Volume sector → the 4D layer moments)

  The 4D Benincasa–Dowker layer cancellations — the first rung of carrying the
  (closed, machine-checked) 2D operator ladder to the physical dimension.

  THE 4D SMEARING FUNCTION.  The 4D BDG operator weights the first four past layers
  with `(1, −9, 16, −8)`; the Poisson layer expectation (`E[c_N]`, `N ~ Poisson(ξ)`)
  is

      f4D(ξ) = e^{−ξ} ( 1 − 9ξ + 8ξ² − (4/3)ξ³ ),

  the coefficients being `c_k/k!` (`f4D_layer_form`).

  THE MOMENT STRUCTURE (this file, all unconditional).  The Mellin transform is

      ∫₀^∞ ξ^{s−1} f4D(ξ) dξ = Γ(s) − 9Γ(s+1) + 8Γ(s+2) − (4/3)Γ(s+3),

  a cubic-in-`s` multiple of `Γ(s)` with roots exactly at `s = 1/2, 1, 3/2`:

      ∫ ξ^{−1/2} f4D dξ = 0        (s = 1/2 — a HALF-INTEGER/fractional moment)
      ∫          f4D dξ = 0        (s = 1)
      ∫ ξ^{+1/2} f4D dξ = 0        (s = 3/2 — fractional)
      ∫ ξ        f4D dξ = −1       (s = 2 — the SURVIVOR).

  In 4D the interval volume scales as `V ∝ τ⁴`, so the cone integrals produce
  HALF-INTEGER Mellin moments (`s = (k+4)/4`) — the fractional-power structure the
  `PoissonLayerRpow` tier-3 analytics anticipated.  The three zeros are the
  necessary cancellation conditions (they kill the divergent `ρ`-powers); the
  surviving `−1` at `s = 2` is the seed of the `□`-normalization (which the
  `4/√6` prefactor and the 4D cone geometry convert to the d'Alembertian).

  UNIQUENESS (`layer_uniqueness`) — the derivation, not just the check: ANY
  four-layer smearing whose `s = 1/2, 1, 3/2` Mellin moments vanish has
  coefficients proportional to `(1, −9, 16, −8)`.  The 4D BDG weights are FORCED
  by the three cancellation conditions; they are not a choice.

  HONEST SCOPE.  These are the necessary moment conditions and the coefficient
  uniqueness — the exact 4D analogue of `KFCausalMinkowskiAngular2D`'s moments
  (0, 0, 2), whose 2D ladder then closed the full operator theorem.  The full 4D
  operator theorem additionally needs the 4D cone geometry (angular integration,
  curved-interval volume expansion) — the R3 wall; not claimed here.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski2DOperator

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Real Set

namespace UnifiedTheory.Audit.KFCausalMinkowski4DMoments

/-- The standard 4D BDG smearing function `f4D(ξ) = e^{−ξ}(1 − 9ξ + 8ξ² − (4/3)ξ³)`. -/
noncomputable def f4D (ξ : ℝ) : ℝ :=
  Real.exp (-ξ) * (1 - 9 * ξ + 8 * ξ ^ 2 - (4 / 3) * ξ ^ 3)

/-- `f4D` is the Poisson layer expectation of the 4D layer weights `(1, −9, 16, −8)`:
`f4D(ξ) = e^{−ξ}(1·ξ⁰/0! − 9·ξ¹/1! + 16·ξ²/2! − 8·ξ³/3!)`. -/
theorem f4D_layer_form (ξ : ℝ) :
    f4D ξ = Real.exp (-ξ) *
      (1 * ξ ^ 0 / (Nat.factorial 0 : ℝ) - 9 * ξ ^ 1 / (Nat.factorial 1 : ℝ)
        + 16 * ξ ^ 2 / (Nat.factorial 2 : ℝ) - 8 * ξ ^ 3 / (Nat.factorial 3 : ℝ)) := by
  unfold f4D
  norm_num [Nat.factorial]
  ring

/-! ## The generic four-layer Mellin transform -/

/-- **Generic four-layer Mellin transform.**  For `s > 0` and layer coefficients
`c₀..c₃`, the Mellin moment of the generic smearing
`e^{−ξ}(c₀ + c₁ξ + (c₂/2)ξ² + (c₃/6)ξ³)` is the Gamma combination
`c₀Γ(s) + c₁Γ(s+1) + (c₂/2)Γ(s+2) + (c₃/6)Γ(s+3)`. -/
theorem generic_mellin (s : ℝ) (hs : 0 < s) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) *
        (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3))
      = c₀ * Real.Gamma s + c₁ * Real.Gamma (s + 1)
        + (c₂ / 2) * Real.Gamma (s + 2) + (c₃ / 6) * Real.Gamma (s + 3) := by
  have hs1 : (0:ℝ) < s + 1 := by linarith
  have hs2 : (0:ℝ) < s + 2 := by linarith
  have hs3 : (0:ℝ) < s + 3 := by linarith
  have i0 : IntegrableOn (fun ξ => c₀ * (Real.exp (-ξ) * ξ ^ (s - 1))) (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent hs).const_mul c₀
  have i1 : IntegrableOn (fun ξ => c₁ * (Real.exp (-ξ) * ξ ^ (s + 1 - 1))) (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent hs1).const_mul c₁
  have i2 : IntegrableOn (fun ξ => (c₂ / 2) * (Real.exp (-ξ) * ξ ^ (s + 2 - 1))) (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent hs2).const_mul (c₂ / 2)
  have i3 : IntegrableOn (fun ξ => (c₃ / 6) * (Real.exp (-ξ) * ξ ^ (s + 3 - 1))) (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent hs3).const_mul (c₃ / 6)
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun ξ => c₀ * (Real.exp (-ξ) * ξ ^ (s - 1)) + c₁ * (Real.exp (-ξ) * ξ ^ (s + 1 - 1))
      + (c₂ / 2) * (Real.exp (-ξ) * ξ ^ (s + 2 - 1))
      + (c₃ / 6) * (Real.exp (-ξ) * ξ ^ (s + 3 - 1)))
    ?_]
  · rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, ← Real.Gamma_eq_integral hs,
      ← Real.Gamma_eq_integral hs1, ← Real.Gamma_eq_integral hs2, ← Real.Gamma_eq_integral hs3]
    all_goals (first
      | exact i0 | exact i1 | exact i2 | exact i3
      | exact i0.add i1 | exact (i0.add i1).add i2)
  · intro ξ hξ
    rw [mem_Ioi] at hξ
    dsimp only
    have e1 : ξ ^ (s + 1 - 1) = ξ ^ (s - 1) * ξ := by
      rw [show s + 1 - 1 = (s - 1) + 1 from by ring, Real.rpow_add hξ, Real.rpow_one]
    have e2 : ξ ^ (s + 2 - 1) = ξ ^ (s - 1) * ξ ^ (2:ℕ) := by
      rw [show s + 2 - 1 = (s - 1) + ((2:ℕ):ℝ) from by push_cast; ring, Real.rpow_add hξ,
        Real.rpow_natCast]
    have e3 : ξ ^ (s + 3 - 1) = ξ ^ (s - 1) * ξ ^ (3:ℕ) := by
      rw [show s + 3 - 1 = (s - 1) + ((3:ℕ):ℝ) from by push_cast; ring, Real.rpow_add hξ,
        Real.rpow_natCast]
    rw [e1, e2, e3]
    ring

/-- The Mellin transform of `f4D`: `Γ(s) − 9Γ(s+1) + 8Γ(s+2) − (4/3)Γ(s+3)`. -/
theorem f4D_mellin (s : ℝ) (hs : 0 < s) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) * f4D ξ
      = Real.Gamma s - 9 * Real.Gamma (s + 1) + 8 * Real.Gamma (s + 2)
        - (4 / 3) * Real.Gamma (s + 3) := by
  have h := generic_mellin s hs 1 (-9) 16 (-8)
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun ξ => ξ ^ (s - 1) *
      (Real.exp (-ξ) * (1 + (-9) * ξ + ((16:ℝ) / 2) * ξ ^ 2 + ((-8:ℝ) / 6) * ξ ^ 3)))
    (fun ξ _ => by dsimp only; unfold f4D; ring)]
  rw [h]
  ring

/-! ## Gamma values keyed to the exact argument shapes -/

theorem G_half_1 : Real.Gamma ((1:ℝ)/2 + 1) = (1/2) * Real.sqrt π := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]

theorem G_half_2 : Real.Gamma ((1:ℝ)/2 + 2) = (3/4) * Real.sqrt π := by
  rw [show ((1:ℝ)/2 + 2) = ((1:ℝ)/2 + 1) + 1 from by ring, Real.Gamma_add_one (by norm_num),
    G_half_1]
  ring

theorem G_half_3 : Real.Gamma ((1:ℝ)/2 + 3) = (15/8) * Real.sqrt π := by
  rw [show ((1:ℝ)/2 + 3) = ((1:ℝ)/2 + 2) + 1 from by ring, Real.Gamma_add_one (by norm_num),
    G_half_2]
  ring

theorem G_3half_0 : Real.Gamma ((3:ℝ)/2) = (1/2) * Real.sqrt π := by
  rw [show ((3:ℝ)/2) = (1:ℝ)/2 + 1 from by ring, G_half_1]

theorem G_3half_1 : Real.Gamma ((3:ℝ)/2 + 1) = (3/4) * Real.sqrt π := by
  rw [show ((3:ℝ)/2 + 1) = (1:ℝ)/2 + 2 from by ring, G_half_2]

theorem G_3half_2 : Real.Gamma ((3:ℝ)/2 + 2) = (15/8) * Real.sqrt π := by
  rw [show ((3:ℝ)/2 + 2) = (1:ℝ)/2 + 3 from by ring, G_half_3]

theorem G_3half_3 : Real.Gamma ((3:ℝ)/2 + 3) = (105/16) * Real.sqrt π := by
  rw [show ((3:ℝ)/2 + 3) = ((3:ℝ)/2 + 2) + 1 from by ring, Real.Gamma_add_one (by norm_num),
    G_3half_2]
  ring

theorem G_1_1 : Real.Gamma ((1:ℝ) + 1) = 1 := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one]
  norm_num

theorem G_1_2 : Real.Gamma ((1:ℝ) + 2) = 2 := by
  rw [show ((1:ℝ) + 2) = ((1:ℝ) + 1) + 1 from by ring, Real.Gamma_add_one (by norm_num), G_1_1]
  norm_num

theorem G_1_3 : Real.Gamma ((1:ℝ) + 3) = 6 := by
  rw [show ((1:ℝ) + 3) = ((1:ℝ) + 2) + 1 from by ring, Real.Gamma_add_one (by norm_num), G_1_2]
  norm_num

theorem G_2_0 : Real.Gamma (2:ℝ) = 1 := by
  rw [show (2:ℝ) = (1:ℝ) + 1 from by ring, G_1_1]

theorem G_2_1 : Real.Gamma ((2:ℝ) + 1) = 2 := by
  rw [show ((2:ℝ) + 1) = (1:ℝ) + 2 from by ring, G_1_2]

theorem G_2_2 : Real.Gamma ((2:ℝ) + 2) = 6 := by
  rw [show ((2:ℝ) + 2) = (1:ℝ) + 3 from by ring, G_1_3]

theorem G_2_3 : Real.Gamma ((2:ℝ) + 3) = 24 := by
  rw [show ((2:ℝ) + 3) = ((2:ℝ) + 2) + 1 from by ring, Real.Gamma_add_one (by norm_num), G_2_2]
  norm_num

/-! ## The three cancellation zeros and the survivor -/

/-- **Zero at `s = 1/2` (fractional).**  `∫ ξ^{−1/2} f4D dξ = 0`. -/
theorem f4D_moment_half : ∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) * f4D ξ = 0 := by
  rw [f4D_mellin (1/2) (by norm_num), Real.Gamma_one_half_eq, G_half_1, G_half_2, G_half_3]
  ring

/-- **Zero at `s = 1` (annihilates constants).**  `∫ f4D dξ = 0`. -/
theorem f4D_moment_one : ∫ ξ in Ioi (0:ℝ), f4D ξ = 0 := by
  have h := f4D_mellin 1 (by norm_num)
  simp only [show (1:ℝ) - 1 = 0 from by norm_num, Real.rpow_zero, one_mul] at h
  rw [h, Real.Gamma_one, G_1_1, G_1_2, G_1_3]
  ring

/-- **Zero at `s = 3/2` (fractional).**  `∫ ξ^{1/2} f4D dξ = 0`. -/
theorem f4D_moment_threehalf : ∫ ξ in Ioi (0:ℝ), ξ ^ ((3:ℝ)/2 - 1) * f4D ξ = 0 := by
  rw [f4D_mellin (3/2) (by norm_num), G_3half_0, G_3half_1, G_3half_2, G_3half_3]
  ring

/-- **The survivor at `s = 2`.**  `∫ ξ f4D dξ = −1` — the seed of the 4D
`□`-normalization (which the `4/√6` prefactor and the 4D cone geometry convert to
the d'Alembertian coefficient). -/
theorem f4D_moment_two : ∫ ξ in Ioi (0:ℝ), ξ * f4D ξ = -1 := by
  have h := f4D_mellin 2 (by norm_num)
  simp only [show (2:ℝ) - 1 = 1 from by norm_num, Real.rpow_one] at h
  rw [h, G_2_0, G_2_1, G_2_2, G_2_3]
  ring

/-! ## Uniqueness — the 4D layer weights are FORCED -/

/-- **The 4D layer coefficients are forced by the cancellation conditions.**  Any
four-layer smearing `e^{−ξ}(c₀ + c₁ξ + (c₂/2)ξ² + (c₃/6)ξ³)` whose Mellin moments
vanish at `s = 1/2, 1, 3/2` has `(c₁, c₂, c₃) = c₀·(−9, 16, −8)`: the BDG weights
`(1, −9, 16, −8)` are the UNIQUE solution (up to normalization), not a choice. -/
theorem layer_uniqueness (c₀ c₁ c₂ c₃ : ℝ)
    (h1 : ∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) *
        (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3)) = 0)
    (h2 : ∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ) - 1) *
        (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3)) = 0)
    (h3 : ∫ ξ in Ioi (0:ℝ), ξ ^ ((3:ℝ)/2 - 1) *
        (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3)) = 0) :
    c₁ = -9 * c₀ ∧ c₂ = 16 * c₀ ∧ c₃ = -8 * c₀ := by
  have hsqrt : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  -- s = 1/2 condition → rational equation (cancel √π)
  rw [generic_mellin (1/2) (by norm_num) c₀ c₁ c₂ c₃, Real.Gamma_one_half_eq, G_half_1,
    G_half_2, G_half_3] at h1
  have e1 : c₀ + (1/2) * c₁ + (3/8) * c₂ + (5/16) * c₃ = 0 := by
    have hfac : Real.sqrt π * (c₀ + (1/2) * c₁ + (3/8) * c₂ + (5/16) * c₃) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (ne_of_gt hsqrt)
    · exact h
  -- s = 1 condition → rational equation
  rw [generic_mellin 1 (by norm_num) c₀ c₁ c₂ c₃, Real.Gamma_one, G_1_1, G_1_2, G_1_3] at h2
  have e2 : c₀ + c₁ + c₂ + c₃ = 0 := by linear_combination h2
  -- s = 3/2 condition → rational equation (cancel √π; note the factor 2)
  rw [generic_mellin (3/2) (by norm_num) c₀ c₁ c₂ c₃, G_3half_0, G_3half_1, G_3half_2,
    G_3half_3] at h3
  have e3 : c₀ + (3/2) * c₁ + (15/8) * c₂ + (35/16) * c₃ = 0 := by
    have hfac : Real.sqrt π * (c₀ + (3/2) * c₁ + (15/8) * c₂ + (35/16) * c₃) = 0 := by
      linear_combination 2 * h3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (ne_of_gt hsqrt)
    · exact h
  -- solve the 3×3 linear system (determinant 1/64 ≠ 0)
  refine ⟨by linarith, by linarith, by linarith⟩

#print axioms f4D_layer_form
#print axioms generic_mellin
#print axioms f4D_mellin
#print axioms f4D_moment_half
#print axioms f4D_moment_one
#print axioms f4D_moment_threehalf
#print axioms f4D_moment_two
#print axioms layer_uniqueness

end UnifiedTheory.Audit.KFCausalMinkowski4DMoments
