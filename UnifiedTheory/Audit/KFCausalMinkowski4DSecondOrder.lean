/-
  Audit/KFCausalMinkowski4DSecondOrder.lean — the shared Mellin foundation of
  the FLUCTUATION and CURVATURE campaigns

  Campaign 2 (fluctuations): the variance's diagonal (Campbell) term is
  governed by the squared-weight smearing

    f4Dsq(ξ) = e^{−ξ}(1 + 81ξ + 128ξ² + (32/3)ξ³)      (weights (1,81,256,64)),

  the Poisson expectation `E[w(N)²]`.  THE SQUARES DESTROY THE MELLIN ZERO:

    M[f4Dsq](½) = (315/2)·√π ≠ 0,

  so the boost integral that the mean's `s = ½` zero rendered finite is now
  log-divergent — the analytic root of the causal-set fluctuation problem.

  Campaign 3 (curvature): the O(τ²) corrections to the interval volume feed
  the gate through `ξ·f4D′(ξ)`, whose Mellin transform obeys the exact shift

    M[ξ·f4D′](s) = −s·M[f4D](s),

  so the flat-space zeros at `s = ½, 1, 3/2` kill the same correction channels
  and only the `s = 2` survivor (`M[f4D](2) = −1`) feeds the `−½R` term.

  This file proves the quartic Mellin engine, both layer functions' moments,
  the fluctuation mass, and the shift identity — the inputs of both campaigns.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DMoments

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments

namespace UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder

/-- The squared-weight smearing function: `E[w(N)²]` for `N ~ Poisson(ξ)` with
layer weights `(1, −9, 16, −8)`, i.e. squared weights `(1, 81, 256, 64)`. -/
noncomputable def f4Dsq (ξ : ℝ) : ℝ :=
  Real.exp (-ξ) * (1 + 81 * ξ + 128 * ξ ^ 2 + (32 / 3) * ξ ^ 3)

/-- `f4Dsq` is the Poisson layer expectation of the squared weights. -/
theorem f4Dsq_layer_form (ξ : ℝ) :
    f4Dsq ξ = Real.exp (-ξ) *
      (1 * ξ ^ 0 / (Nat.factorial 0 : ℝ) + 81 * ξ ^ 1 / (Nat.factorial 1 : ℝ)
        + 256 * ξ ^ 2 / (Nat.factorial 2 : ℝ)
        + 64 * ξ ^ 3 / (Nat.factorial 3 : ℝ)) := by
  unfold f4Dsq
  norm_num [Nat.factorial]
  ring

/-- The Mellin transform of `f4Dsq`. -/
theorem f4Dsq_mellin (s : ℝ) (hs : 0 < s) :
    (∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) * f4Dsq ξ)
      = 1 * Real.Gamma s + 81 * Real.Gamma (s + 1)
        + 128 * Real.Gamma (s + 2) + (32/3) * Real.Gamma (s + 3) := by
  have h := generic_mellin s hs 1 81 256 64
  have he : (fun ξ => ξ ^ (s - 1) *
      (Real.exp (-ξ) * (1 + 81 * ξ + (256 / 2) * ξ ^ 2 + (64 / 6) * ξ ^ 3)))
      = fun ξ => ξ ^ (s - 1) * f4Dsq ξ := by
    funext ξ
    unfold f4Dsq
    ring
  rw [he] at h
  rw [h]
  norm_num

/-- **THE FLUCTUATION MASS**: `M[f4Dsq](½) = (315/2)·√π ≠ 0` — the squares
destroy the `s = ½` zero, and with it the finiteness of the boost integral. -/
theorem f4Dsq_mass_half :
    (∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * f4Dsq ξ) = (315/2) * Real.sqrt π := by
  rw [f4Dsq_mellin (1/2) one_half_pos]
  have hg12 : Real.Gamma (1/2) = Real.sqrt π := Real.Gamma_one_half_eq
  have hg32 : Real.Gamma ((1:ℝ)/2 + 1) = (1/2) * Real.sqrt π := by
    rw [Real.Gamma_add_one (by norm_num), hg12]
  have hg52 : Real.Gamma ((1:ℝ)/2 + 2) = (3/4) * Real.sqrt π := by
    rw [show (1:ℝ)/2 + 2 = ((1:ℝ)/2 + 1) + 1 from by ring,
      Real.Gamma_add_one (by norm_num), hg32]
    ring
  have hg72 : Real.Gamma ((1:ℝ)/2 + 3) = (15/8) * Real.sqrt π := by
    rw [show (1:ℝ)/2 + 3 = ((1:ℝ)/2 + 2) + 1 from by ring,
      Real.Gamma_add_one (by norm_num), hg52]
    ring
  rw [hg12, hg32, hg52, hg72]
  ring

/-- The fluctuation mass is strictly positive: the variance channel is open. -/
theorem f4Dsq_mass_half_pos :
    0 < ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * f4Dsq ξ := by
  rw [f4Dsq_mass_half]
  have := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- The quartic Mellin engine (extends `generic_mellin` by one degree, for the
curvature channel's `ξ·f4D′`). -/
theorem generic_mellin4 (s : ℝ) (hs : 0 < s) (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) *
        (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3
          + (c₄ / 24) * ξ ^ 4))
      = c₀ * Real.Gamma s + c₁ * Real.Gamma (s + 1)
        + (c₂ / 2) * Real.Gamma (s + 2) + (c₃ / 6) * Real.Gamma (s + 3)
        + (c₄ / 24) * Real.Gamma (s + 4) := by
  have hcube := generic_mellin s hs c₀ c₁ c₂ c₃
  have hs4 : (0:ℝ) < s + 4 := by linarith
  have hquart : IntegrableOn (fun ξ => (c₄ / 24) *
      (Real.exp (-ξ) * ξ ^ ((s + 4) - 1))) (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent hs4).const_mul _
  have hcubeInt : IntegrableOn (fun ξ => ξ ^ (s - 1) *
      (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3)))
      (Ioi (0:ℝ)) := by
    have i0 : IntegrableOn (fun ξ => c₀ * (Real.exp (-ξ) * ξ ^ (s - 1)))
        (Ioi (0:ℝ)) := (Real.GammaIntegral_convergent hs).const_mul _
    have i1 : IntegrableOn (fun ξ => c₁ * (Real.exp (-ξ) * ξ ^ ((s + 1) - 1)))
        (Ioi (0:ℝ)) := (Real.GammaIntegral_convergent (by linarith)).const_mul _
    have i2 : IntegrableOn (fun ξ => (c₂/2) * (Real.exp (-ξ) * ξ ^ ((s + 2) - 1)))
        (Ioi (0:ℝ)) := (Real.GammaIntegral_convergent (by linarith)).const_mul _
    have i3 : IntegrableOn (fun ξ => (c₃/6) * (Real.exp (-ξ) * ξ ^ ((s + 3) - 1)))
        (Ioi (0:ℝ)) := (Real.GammaIntegral_convergent (by linarith)).const_mul _
    have hsum := ((i0.add i1).add i2).add i3
    apply MeasureTheory.IntegrableOn.congr_fun hsum ?_ measurableSet_Ioi
    intro ξ hξ
    rw [mem_Ioi] at hξ
    have estep : ∀ y : ℝ, ξ ^ (y + 1) = ξ ^ y * ξ :=
      fun y => Real.rpow_add_one (ne_of_gt hξ) y
    have e1 : ξ ^ ((s + 1) - 1) = ξ ^ (s - 1) * ξ := by
      rw [show (s + 1) - 1 = (s - 1) + 1 from by ring, estep]
    have e2 : ξ ^ ((s + 2) - 1) = ξ ^ (s - 1) * ξ ^ 2 := by
      rw [show (s + 2) - 1 = ((s - 1) + 1) + 1 from by ring, estep, estep]
      ring
    have e3 : ξ ^ ((s + 3) - 1) = ξ ^ (s - 1) * ξ ^ 3 := by
      rw [show (s + 3) - 1 = (((s - 1) + 1) + 1) + 1 from by ring,
        estep, estep, estep]
      ring
    simp only [Pi.add_apply]
    rw [e1, e2, e3]
    ring
  have hsplit : (fun ξ => ξ ^ (s - 1) *
      (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3
        + (c₄ / 24) * ξ ^ 4)))
      = fun ξ => (ξ ^ (s - 1) *
        (Real.exp (-ξ) * (c₀ + c₁ * ξ + (c₂ / 2) * ξ ^ 2 + (c₃ / 6) * ξ ^ 3)))
        + (c₄ / 24) * (Real.exp (-ξ) * (ξ ^ (s - 1) * ξ ^ 4)) := by
    funext ξ
    ring
  have e4 : ∀ ξ : ℝ, 0 < ξ → ξ ^ ((s + 4) - 1) = ξ ^ (s - 1) * ξ ^ 4 := by
    intro ξ hξ
    have estep : ∀ y : ℝ, ξ ^ (y + 1) = ξ ^ y * ξ :=
      fun y => Real.rpow_add_one (ne_of_gt hξ) y
    rw [show (s + 4) - 1 = ((((s - 1) + 1) + 1) + 1) + 1 from by ring,
      estep, estep, estep, estep]
    ring
  rw [hsplit, integral_add hcubeInt]
  · rw [hcube]
    have h4 : (∫ ξ in Ioi (0:ℝ), (c₄ / 24) *
        (Real.exp (-ξ) * (ξ ^ (s - 1) * ξ ^ 4)))
        = (c₄ / 24) * Real.Gamma (s + 4) := by
      rw [Real.Gamma_eq_integral hs4, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ξ hξ
      rw [mem_Ioi] at hξ
      dsimp only
      rw [e4 ξ hξ]
    rw [h4]
  · apply MeasureTheory.IntegrableOn.congr_fun hquart ?_ measurableSet_Ioi
    intro ξ hξ
    rw [mem_Ioi] at hξ
    dsimp only
    rw [e4 ξ hξ]

/-- The curvature channel's integrand: `ξ·f4D′(ξ)` as an explicit quartic. -/
theorem xi_f4D_deriv (ξ : ℝ) :
    ξ * (Real.exp (-ξ) * (-10 + 25 * ξ - 12 * ξ ^ 2 + (4/3) * ξ ^ 3))
      = Real.exp (-ξ) * ((-10) * ξ + 25 * ξ ^ 2 - 12 * ξ ^ 3 + (4/3) * ξ ^ 4) := by
  ring

/-- `f4D′` certificate: the derivative of the smearing function. -/
theorem f4D_hasDerivAt (ξ : ℝ) :
    HasDerivAt f4D (Real.exp (-ξ) * (-10 + 25 * ξ - 12 * ξ ^ 2 + (4/3) * ξ ^ 3)) ξ := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DMoments.f4D
  have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-ξ)) ξ := by
    simpa using ((Real.hasDerivAt_exp (-ξ)).comp ξ (hasDerivAt_id ξ).neg)
  have hp : HasDerivAt (fun x : ℝ => 1 - 9 * x + 8 * x ^ 2 - (4/3) * x ^ 3)
      (-9 + 16 * ξ - 4 * ξ ^ 2) ξ := by
    have h1 : HasDerivAt (fun x : ℝ => x) 1 ξ := hasDerivAt_id ξ
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ξ) ξ := by
      simpa using hasDerivAt_pow 2 ξ
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * ξ ^ 2) ξ := by
      simpa using hasDerivAt_pow 3 ξ
    have hp0 := (((h1.const_mul (9:ℝ)).const_sub 1).add
      (h2.const_mul (8:ℝ))).sub (h3.const_mul ((4:ℝ)/3))
    exact hp0.congr_deriv (by ring)
  have := he.mul hp
  convert this using 1
  ring

/-- **THE MELLIN SHIFT IDENTITY**: `M[ξ·f4D′](s) = −s·M[f4D](s)` — verified by
direct quartic evaluation.  Consequence: the flat-space zeros at
`s = ½, 1, 3/2` annihilate the same curvature-correction channels, and only
the `s = 2` survivor feeds the `−½R` term of the Benincasa–Dowker action. -/
theorem mellin_shift (s : ℝ) (hs : 0 < s) :
    (∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) *
        (Real.exp (-ξ) * ((-10) * ξ + 25 * ξ ^ 2 - 12 * ξ ^ 3 + (4/3) * ξ ^ 4)))
      = -s * ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) * f4D ξ := by
  have hL := generic_mellin4 s hs 0 (-10) 50 (-72) 32
  have heL : (fun ξ => ξ ^ (s - 1) *
      (Real.exp (-ξ) * ((0:ℝ) + (-10) * ξ + (50 / 2) * ξ ^ 2 + ((-72) / 6) * ξ ^ 3
        + ((32:ℝ) / 24) * ξ ^ 4)))
      = fun ξ => ξ ^ (s - 1) *
        (Real.exp (-ξ) * ((-10) * ξ + 25 * ξ ^ 2 - 12 * ξ ^ 3 + (4/3) * ξ ^ 4)) := by
    funext ξ
    ring
  rw [heL] at hL
  have hR := generic_mellin s hs 1 (-9) 16 (-8)
  have heR : (fun ξ => ξ ^ (s - 1) *
      (Real.exp (-ξ) * (1 + (-9) * ξ + ((16:ℝ) / 2) * ξ ^ 2 + ((-8) / 6) * ξ ^ 3)))
      = fun ξ => ξ ^ (s - 1) * f4D ξ := by
    funext ξ
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DMoments.f4D
    ring
  rw [heR] at hR
  rw [hL, hR]
  have g1 : Real.Gamma (s + 1) = s * Real.Gamma s := Real.Gamma_add_one (ne_of_gt hs)
  have g2 : Real.Gamma (s + 2) = (s + 1) * Real.Gamma (s + 1) := by
    rw [show s + 2 = (s + 1) + 1 from by ring,
      Real.Gamma_add_one (by linarith)]
  have g3 : Real.Gamma (s + 3) = (s + 2) * Real.Gamma (s + 2) := by
    rw [show s + 3 = (s + 2) + 1 from by ring,
      Real.Gamma_add_one (by linarith)]
  have g4 : Real.Gamma (s + 4) = (s + 3) * Real.Gamma (s + 3) := by
    rw [show s + 4 = (s + 3) + 1 from by ring,
      Real.Gamma_add_one (by linarith)]
  rw [g4, g3, g2, g1]
  ring

#print axioms f4Dsq_mass_half
#print axioms f4Dsq_mass_half_pos
#print axioms generic_mellin4
#print axioms mellin_shift

end UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder
