/-
  Audit/KFCausalMinkowski4DMesoscale.lean — THE MESOSCALE SCALING LAW
  (fluctuation campaign: the ε-damped kernel family, exact masses)

  The Aslanbeigi–Saravani–Sorkin smeared 4D operator at nonlocality parameter
  `ε = ρ_k/ρ = (ℓ_p/ℓ_k)⁴` has continuum mean pair kernel `ε·f4D(εξ)`
  (an EXACT Poisson-expectation identity, no approximation) and continuum
  variance kernel `ε²·g4sq(εξ)` with `g4sq = f4D²`.  This file proves:

  1.  `g4sq_mass_half`:  M[f4D²](½) = (315/512)·√2·√π — the damped variance
      channel's critical mass (compare the sharp atomic mass (315/2)·√π).
  2.  `mellin_scale`:  M[F(ε·)](s) = ε^{−s}·M[F](s) — Mellin zeros CARRY
      under damping, so the damped mean family still converges to `□`.
  3.  `damped_moment_half/one/threehalf`:  the mean kernel's zeros at
      s = ½, 1, 3/2 survive for EVERY ε > 0.
  4.  `damped_survivor`:  M[ε·f4D(ε·)](2) = −ε⁻¹ — the survivor scales as
      ε⁻¹, forcing the `1/ℓ_k²` normalization of the damped operator.
  5.  `mesoscale_suppression`:  the damped variance mass at the critical
      point is EXACTLY ε^{3/2}·(315/512)·√2·√π — the mesoscale scaling law:
      damping suppresses the fluctuation channel by (ℓ_p/ℓ_k)⁶.
  6.  `damped_variance_mass_pos`:  the suppressed mass is still strictly
      positive — damping suppresses but can NEVER cancel the channel
      (consistent with the `no_self_averaging` no-go).
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DMoments

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments

namespace UnifiedTheory.Audit.KFCausalMinkowski4DMesoscale

/-- The continuum damped variance kernel: `g4sq = (f4D)²` in closed
polynomial form `e^{−2z}·(1 − 18z + 97z² − (440/3)z³ + 88z⁴ − (64/3)z⁵
+ (16/9)z⁶)`. -/
noncomputable def g4sq (z : ℝ) : ℝ :=
  Real.exp (-(2*z)) * (1 - 18*z + 97*z^2 - (440/3)*z^3 + 88*z^4
    - (64/3)*z^5 + (16/9)*z^6)

/-- `g4sq` is the square of the BDG smearing function. -/
theorem g4sq_eq_sq (z : ℝ) : g4sq z = (f4D z)^2 := by
  unfold g4sq f4D
  rw [mul_pow, pow_two (Real.exp (-z)), ← Real.exp_add,
    show -z + -z = -(2*z) from by ring]
  ring

/-- The degree-6 Mellin engine at exponential rate 2:
`∫ ξ^{s−1} e^{−2ξ} Σ cₖξᵏ = Σ cₖ (1/2)^{s+k} Γ(s+k)`. -/
theorem mellin_exp2_six (s : ℝ) (hs : 0 < s) (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) *
        (Real.exp (-(2*ξ)) * (c₀ + c₁*ξ + c₂*ξ^2 + c₃*ξ^3 + c₄*ξ^4
          + c₅*ξ^5 + c₆*ξ^6))
      = c₀ * ((1/2:ℝ)^s * Real.Gamma s)
        + c₁ * ((1/2:ℝ)^(s+1) * Real.Gamma (s+1))
        + c₂ * ((1/2:ℝ)^(s+2) * Real.Gamma (s+2))
        + c₃ * ((1/2:ℝ)^(s+3) * Real.Gamma (s+3))
        + c₄ * ((1/2:ℝ)^(s+4) * Real.Gamma (s+4))
        + c₅ * ((1/2:ℝ)^(s+5) * Real.Gamma (s+5))
        + c₆ * ((1/2:ℝ)^(s+6) * Real.Gamma (s+6)) := by
  have hint : ∀ t : ℝ, 0 < t → IntegrableOn
      (fun z : ℝ => z ^ (t - 1) * Real.exp (-(2*z))) (Ioi (0:ℝ)) := by
    intro t ht
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (by linarith : (-1:ℝ) < t - 1) (le_refl (1:ℝ)) two_pos
    apply MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro x _
    dsimp only
    rw [Real.rpow_one, neg_mul]
  have hs1 : (0:ℝ) < s + 1 := by linarith
  have hs2 : (0:ℝ) < s + 2 := by linarith
  have hs3 : (0:ℝ) < s + 3 := by linarith
  have hs4 : (0:ℝ) < s + 4 := by linarith
  have hs5 : (0:ℝ) < s + 5 := by linarith
  have hs6 : (0:ℝ) < s + 6 := by linarith
  have i0 : IntegrableOn (fun ξ => c₀ * (ξ ^ (s - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint s hs).const_mul c₀
  have i1 : IntegrableOn (fun ξ => c₁ * (ξ ^ (s + 1 - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint (s+1) hs1).const_mul c₁
  have i2 : IntegrableOn (fun ξ => c₂ * (ξ ^ (s + 2 - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint (s+2) hs2).const_mul c₂
  have i3 : IntegrableOn (fun ξ => c₃ * (ξ ^ (s + 3 - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint (s+3) hs3).const_mul c₃
  have i4 : IntegrableOn (fun ξ => c₄ * (ξ ^ (s + 4 - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint (s+4) hs4).const_mul c₄
  have i5 : IntegrableOn (fun ξ => c₅ * (ξ ^ (s + 5 - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint (s+5) hs5).const_mul c₅
  have i6 : IntegrableOn (fun ξ => c₆ * (ξ ^ (s + 6 - 1) * Real.exp (-(2*ξ))))
      (Ioi (0:ℝ)) := (hint (s+6) hs6).const_mul c₆
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun ξ => c₀ * (ξ ^ (s - 1) * Real.exp (-(2*ξ)))
      + c₁ * (ξ ^ (s + 1 - 1) * Real.exp (-(2*ξ)))
      + c₂ * (ξ ^ (s + 2 - 1) * Real.exp (-(2*ξ)))
      + c₃ * (ξ ^ (s + 3 - 1) * Real.exp (-(2*ξ)))
      + c₄ * (ξ ^ (s + 4 - 1) * Real.exp (-(2*ξ)))
      + c₅ * (ξ ^ (s + 5 - 1) * Real.exp (-(2*ξ)))
      + c₆ * (ξ ^ (s + 6 - 1) * Real.exp (-(2*ξ))))
    ?_]
  · rw [integral_add, integral_add, integral_add, integral_add, integral_add,
      integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs two_pos,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs1 two_pos,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs2 two_pos,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs3 two_pos,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs4 two_pos,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs5 two_pos,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs6 two_pos]
    all_goals (first
      | exact i0 | exact i1 | exact i2 | exact i3 | exact i4 | exact i5
      | exact i6
      | exact i0.add i1
      | exact (i0.add i1).add i2
      | exact ((i0.add i1).add i2).add i3
      | exact (((i0.add i1).add i2).add i3).add i4
      | exact ((((i0.add i1).add i2).add i3).add i4).add i5)
  · intro ξ hξ
    rw [mem_Ioi] at hξ
    dsimp only
    have e1 : ξ ^ (s + 1 - 1) = ξ ^ (s - 1) * ξ := by
      rw [show s + 1 - 1 = (s - 1) + 1 from by ring, Real.rpow_add hξ,
        Real.rpow_one]
    have e2 : ξ ^ (s + 2 - 1) = ξ ^ (s - 1) * ξ ^ (2:ℕ) := by
      rw [show s + 2 - 1 = (s - 1) + ((2:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_add hξ, Real.rpow_natCast]
    have e3 : ξ ^ (s + 3 - 1) = ξ ^ (s - 1) * ξ ^ (3:ℕ) := by
      rw [show s + 3 - 1 = (s - 1) + ((3:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_add hξ, Real.rpow_natCast]
    have e4 : ξ ^ (s + 4 - 1) = ξ ^ (s - 1) * ξ ^ (4:ℕ) := by
      rw [show s + 4 - 1 = (s - 1) + ((4:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_add hξ, Real.rpow_natCast]
    have e5 : ξ ^ (s + 5 - 1) = ξ ^ (s - 1) * ξ ^ (5:ℕ) := by
      rw [show s + 5 - 1 = (s - 1) + ((5:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_add hξ, Real.rpow_natCast]
    have e6 : ξ ^ (s + 6 - 1) = ξ ^ (s - 1) * ξ ^ (6:ℕ) := by
      rw [show s + 6 - 1 = (s - 1) + ((6:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_add hξ, Real.rpow_natCast]
    rw [e1, e2, e3, e4, e5, e6]
    ring

/-- The Mellin transform of the damped variance kernel `g4sq = f4D²`. -/
theorem g4sq_mellin (s : ℝ) (hs : 0 < s) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) * g4sq ξ
      = (1/2:ℝ)^s * Real.Gamma s
        - 18 * ((1/2:ℝ)^(s+1) * Real.Gamma (s+1))
        + 97 * ((1/2:ℝ)^(s+2) * Real.Gamma (s+2))
        - (440/3) * ((1/2:ℝ)^(s+3) * Real.Gamma (s+3))
        + 88 * ((1/2:ℝ)^(s+4) * Real.Gamma (s+4))
        - (64/3) * ((1/2:ℝ)^(s+5) * Real.Gamma (s+5))
        + (16/9) * ((1/2:ℝ)^(s+6) * Real.Gamma (s+6)) := by
  have h := mellin_exp2_six s hs 1 (-18) 97 (-440/3) 88 (-64/3) (16/9)
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun ξ => ξ ^ (s - 1) *
      (Real.exp (-(2*ξ)) * (1 + (-18)*ξ + 97*ξ^2 + (-440/3)*ξ^3 + 88*ξ^4
        + (-64/3)*ξ^5 + (16/9)*ξ^6)))
    (fun ξ _ => by dsimp only; unfold g4sq; ring)]
  rw [h]
  ring

/-- **The damped variance channel's critical mass**:
`M[f4D²](½) = (315/512)·√2·√π ≈ 1.5422` — compare the sharp atomic mass
`(315/2)·√π`; the same `315` survives the squaring. -/
theorem g4sq_mass_half :
    ∫ z in Ioi (0:ℝ), z ^ ((1/2:ℝ) - 1) * g4sq z
      = (315/512) * (Real.sqrt 2 * Real.sqrt π) := by
  have hg1 : Real.Gamma ((1:ℝ)/2 + 1) = (1/2) * Real.sqrt π := G_half_1
  have hg2 : Real.Gamma ((1:ℝ)/2 + 2) = (3/4) * Real.sqrt π := G_half_2
  have hg3 : Real.Gamma ((1:ℝ)/2 + 3) = (15/8) * Real.sqrt π := G_half_3
  have hg4 : Real.Gamma ((1:ℝ)/2 + 4) = (105/16) * Real.sqrt π := by
    rw [show (1:ℝ)/2 + 4 = ((1:ℝ)/2 + 3) + 1 from by ring,
      Real.Gamma_add_one (by norm_num), hg3]
    ring
  have hg5 : Real.Gamma ((1:ℝ)/2 + 5) = (945/32) * Real.sqrt π := by
    rw [show (1:ℝ)/2 + 5 = ((1:ℝ)/2 + 4) + 1 from by ring,
      Real.Gamma_add_one (by norm_num), hg4]
    ring
  have hg6 : Real.Gamma ((1:ℝ)/2 + 6) = (10395/64) * Real.sqrt π := by
    rw [show (1:ℝ)/2 + 6 = ((1:ℝ)/2 + 5) + 1 from by ring,
      Real.Gamma_add_one (by norm_num), hg5]
    ring
  have hp0 : ((1/2:ℝ)) ^ ((1/2:ℝ)) = Real.sqrt (1/2) :=
    (Real.sqrt_eq_rpow _).symm
  have hp1 : ((1/2:ℝ)) ^ ((1/2:ℝ)+1) = Real.sqrt (1/2) * (1/2) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 1/2), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hp2 : ((1/2:ℝ)) ^ ((1/2:ℝ)+2) = Real.sqrt (1/2) * (1/4) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 1/2), ← Real.sqrt_eq_rpow,
      show ((1/2:ℝ)) ^ ((2:ℝ)) = ((1/2:ℝ))^(2:ℕ) from by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]]
    norm_num
  have hp3 : ((1/2:ℝ)) ^ ((1/2:ℝ)+3) = Real.sqrt (1/2) * (1/8) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 1/2),
      show (3:ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
    norm_num
  have hp4 : ((1/2:ℝ)) ^ ((1/2:ℝ)+4) = Real.sqrt (1/2) * (1/16) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 1/2),
      show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
    norm_num
  have hp5 : ((1/2:ℝ)) ^ ((1/2:ℝ)+5) = Real.sqrt (1/2) * (1/32) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 1/2),
      show (5:ℝ) = ((5:ℕ):ℝ) from by norm_num, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
    norm_num
  have hp6 : ((1/2:ℝ)) ^ ((1/2:ℝ)+6) = Real.sqrt (1/2) * (1/64) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 1/2),
      show (6:ℝ) = ((6:ℕ):ℝ) from by norm_num, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
    norm_num
  have h2 : Real.sqrt (1/2:ℝ) = Real.sqrt 2 / 2 := by
    rw [show (1/2:ℝ) = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_eq_one_div,
      div_eq_div_iff (Real.sqrt_pos.mpr two_pos).ne' two_ne_zero, one_mul,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [g4sq_mellin (1/2:ℝ) one_half_pos, Real.Gamma_one_half_eq,
    hg1, hg2, hg3, hg4, hg5, hg6, hp0, hp1, hp2, hp3, hp4, hp5, hp6, h2]
  ring

/-- **Mellin zeros carry under damping**: `M[F(ε·)](s) = ε^{−s}·M[F](s)`.
The generic scaling identity behind the whole damped family. -/
theorem mellin_scale (F : ℝ → ℝ) (s ε : ℝ) (hε : 0 < ε) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) * F (ε * ξ)
      = ε ^ (-s) * ∫ z in Ioi (0:ℝ), z ^ (s - 1) * F z := by
  have hcomp := integral_comp_mul_left_Ioi
    (fun z => z ^ (s - 1) * F z) 0 hε
  rw [mul_zero, smul_eq_mul] at hcomp
  have hpoint : (∫ ξ in Ioi (0:ℝ), (fun z => z ^ (s - 1) * F z) (ε * ξ))
      = ∫ ξ in Ioi (0:ℝ), ε ^ (s - 1) * (ξ ^ (s - 1) * F (ε * ξ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ hξ
    rw [mem_Ioi] at hξ
    dsimp only
    rw [Real.mul_rpow hε.le hξ.le]
    ring
  rw [hpoint, MeasureTheory.integral_const_mul] at hcomp
  have hne : ε ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  have hsolve : ∫ ξ in Ioi (0:ℝ), ξ ^ (s - 1) * F (ε * ξ)
      = (ε ^ (s - 1))⁻¹ * (ε⁻¹ * ∫ z in Ioi (0:ℝ), z ^ (s - 1) * F z) := by
    rw [← hcomp, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hsolve, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg hε.le, ← Real.rpow_neg_one ε, ← Real.rpow_add hε]
  congr 1
  ring

/-- The damped mean kernel's zero at the critical point `s = ½` survives for
every `ε > 0`: the damped family still kills the boost-divergent channel. -/
theorem damped_moment_half (ε : ℝ) (hε : 0 < ε) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) * (ε * f4D (ε * ξ)) = 0 := by
  have h1 : (∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) * (ε * f4D (ε * ξ)))
      = ε * ∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) * f4D (ε * ξ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ _
    ring
  rw [h1, mellin_scale f4D ((1:ℝ)/2) ε hε, f4D_moment_half, mul_zero, mul_zero]

/-- The damped mean kernel's zero at `s = 1` survives for every `ε > 0`. -/
theorem damped_moment_one (ε : ℝ) (hε : 0 < ε) :
    ∫ ξ in Ioi (0:ℝ), ε * f4D (ε * ξ) = 0 := by
  have hcomp := integral_comp_mul_left_Ioi f4D 0 hε
  rw [mul_zero, smul_eq_mul, f4D_moment_one, mul_zero] at hcomp
  rw [MeasureTheory.integral_const_mul, hcomp, mul_zero]

/-- The damped mean kernel's zero at `s = 3/2` survives for every `ε > 0`. -/
theorem damped_moment_threehalf (ε : ℝ) (hε : 0 < ε) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ ((3:ℝ)/2 - 1) * (ε * f4D (ε * ξ)) = 0 := by
  have h1 : (∫ ξ in Ioi (0:ℝ), ξ ^ ((3:ℝ)/2 - 1) * (ε * f4D (ε * ξ)))
      = ε * ∫ ξ in Ioi (0:ℝ), ξ ^ ((3:ℝ)/2 - 1) * f4D (ε * ξ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ _
    ring
  rw [h1, mellin_scale f4D ((3:ℝ)/2) ε hε, f4D_moment_threehalf, mul_zero,
    mul_zero]

/-- **The damped survivor**: `M[ε·f4D(ε·)](2) = −ε⁻¹`.  The surviving moment
scales as `ε⁻¹ = (ℓ_k/ℓ_p)⁴`, which is exactly what forces the damped
operator's `1/ℓ_k²` normalization (mesoscale, not Planck scale). -/
theorem damped_survivor (ε : ℝ) (hε : 0 < ε) :
    ∫ ξ in Ioi (0:ℝ), ξ * (ε * f4D (ε * ξ)) = -ε⁻¹ := by
  have h1 : (∫ ξ in Ioi (0:ℝ), ξ * (ε * f4D (ε * ξ)))
      = ε * ∫ ξ in Ioi (0:ℝ), ξ ^ ((2:ℝ) - 1) * f4D (ε * ξ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ hξ
    rw [mem_Ioi] at hξ
    dsimp only
    rw [show (2:ℝ) - 1 = 1 from by norm_num, Real.rpow_one]
    ring
  have h2 : (∫ z in Ioi (0:ℝ), z ^ ((2:ℝ) - 1) * f4D z) = -1 := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun z => z * f4D z) ?_]
    · exact f4D_moment_two
    · intro z hz
      rw [mem_Ioi] at hz
      dsimp only
      rw [show (2:ℝ) - 1 = 1 from by norm_num, Real.rpow_one]
  rw [h1, mellin_scale f4D 2 ε hε, h2]
  rw [show ε ^ (-(2:ℝ)) = (ε^2)⁻¹ from by
    rw [Real.rpow_neg hε.le, show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num,
      Real.rpow_natCast]]
  field_simp

/-- **THE MESOSCALE SCALING LAW**: the damped variance channel's critical
mass is EXACTLY

    M[ε²·g4sq(ε·)](½) = ε^{3/2} · (315/512)·√2·√π.

With `ε = ρ_k/ρ = (ℓ_p/ℓ_k)⁴` this is a suppression by `(ℓ_p/ℓ_k)⁶`: the
damped operator's fluctuation amplitude carries `(ℓ_p/ℓ_k)³` relative to the
undamped one.  Damping wins polynomially — but only polynomially. -/
theorem mesoscale_suppression (ε : ℝ) (hε : 0 < ε) :
    ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * (ε^2 * g4sq (ε * ξ))
      = (ε * Real.sqrt ε) * ((315/512) * (Real.sqrt 2 * Real.sqrt π)) := by
  have h1 : (∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * (ε^2 * g4sq (ε * ξ)))
      = ε^2 * ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * g4sq (ε * ξ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ _
    ring
  rw [h1, mellin_scale g4sq (1/2:ℝ) ε hε, g4sq_mass_half, ← mul_assoc]
  have hpow : ε^2 * ε ^ (-(1/2:ℝ)) = ε * Real.sqrt ε := by
    have hr : ε * Real.sqrt ε = ε ^ ((1:ℝ) + 1/2) := by
      rw [Real.rpow_add hε, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hr, ← Real.rpow_natCast ε 2, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  rw [hpow]

/-- The suppressed variance mass is still strictly positive: damping can
shrink the fluctuation channel by any power of the mesoscale but can never
close it — the quantitative face of the no-self-averaging no-go. -/
theorem damped_variance_mass_pos (ε : ℝ) (hε : 0 < ε) :
    0 < ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * (ε^2 * g4sq (ε * ξ)) := by
  rw [mesoscale_suppression ε hε]
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hπ : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsε : (0:ℝ) < Real.sqrt ε := Real.sqrt_pos.mpr hε
  positivity

/-- **The IR-decoupling zero**: the mean kernel's null-boundary w-mass
vanishes, `∫₀^∞ f4D(w²)dw = ½·M[f4D](½) = 0`.  Consequence (the off-diagonal
covariance structure): at separated points the deep-cone contribution to the
fluctuation covariance integrates the MEAN kernel along the second null shell
— and this zero kills it.  The covariance of the BDG noise is IR-FINITE and
short-ranged (correlation length ≈ the mesoscale), even though the per-point
variance diverges with the IR depth: per-point no-self-averaging coexists
with full self-averaging of every extended observable. -/
theorem f4D_w_mass_zero :
    (∫ w in Ioi (0:ℝ), f4D (w^2)) = 0 := by
  have hsub := integral_comp_rpow_Ioi
    (fun ξ => ξ ^ ((1:ℝ)/2 - 1) * f4D ξ) (p := 2) (by norm_num)
  rw [f4D_moment_half] at hsub
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      ((fun ξ => ξ ^ ((1:ℝ)/2 - 1) * f4D ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 2 * f4D (x^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [smul_eq_mul]
    have h21 : x ^ ((2:ℝ)-1) = x := by
      rw [show (2:ℝ)-1 = (1:ℝ) from by norm_num, Real.rpow_one]
    have hpow : (x ^ (2:ℝ)) ^ ((1:ℝ)/2 - 1) = x⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt hx),
        show (2:ℝ) * ((1:ℝ)/2 - 1) = -1 from by norm_num, Real.rpow_neg_one]
    have hx2 : x ^ (2:ℝ) = x^2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    rw [h21, hpow, hx2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp
  rw [key, integral_const_mul] at hsub
  linarith [hsub]

#print axioms f4D_w_mass_zero

#print axioms g4sq_mass_half
#print axioms mellin_scale
#print axioms damped_moment_half
#print axioms damped_survivor
#print axioms mesoscale_suppression
#print axioms damped_variance_mass_pos

end UnifiedTheory.Audit.KFCausalMinkowski4DMesoscale
