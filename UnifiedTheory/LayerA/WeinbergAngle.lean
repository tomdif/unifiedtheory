/-
  LayerA/WeinbergAngle.lean — sin^2 theta_W = 3/8 at unification from SM hypercharges

  THE ARGUMENT:

  At the unification scale where g_1 = g_2 (GUT normalization), the
  Weinberg angle is determined by the relative normalization of U(1)
  hypercharge vs SU(2) isospin.

  Step 1: Compute the hypercharge sum over one SM generation:
    k_1 = Sum of (color mult) * (weak mult) * Y^2
        = N_c * N_w * Y_Q^2 + N_c * Y_u^2 + N_c * Y_d^2 + N_w * Y_L^2 + Y_e^2
    With SM hypercharges Y_Q=1/6, Y_u=-2/3, Y_d=1/3, Y_L=-1/2, Y_e=1:
    k_1 = 3*2*(1/36) + 3*(4/9) + 3*(1/9) + 2*(1/4) + 1 = 10/3

  Step 2: Compute the isospin sum over one SM generation:
    k_2 = Sum of (color mult) * (T_3)^2 over doublet components
        = N_c * 2 * (1/2)^2 + 2 * (1/2)^2 = 3/2 + 1/2 = 2

  Step 3: The GUT normalization factor is k_1 / k_2 = (10/3)/2 = 5/3.
    With this normalization, g_1 = sqrt(5/3) * g', so
    g'^2 = (3/5) * g_1^2.

  Step 4: At unification g_1 = g_2 = g:
    sin^2 theta_W = g'^2 / (g^2 + g'^2)
                  = (3/5 * g^2) / (g^2 + 3/5 * g^2)
                  = (3/5) / (1 + 3/5)
                  = (3/5) / (8/5)
                  = 3/8

  All proofs are pure rational arithmetic. Zero sorry. Zero custom axioms.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.WeinbergAngle

/-! ## 1. SM hypercharges and multiplicities -/

/-- SM hypercharges for one generation (rational values). -/
def Y_Q : ℚ := 1 / 6
def Y_u : ℚ := -(2 / 3)
def Y_d : ℚ := 1 / 3
def Y_L : ℚ := -(1 / 2)
def Y_e : ℚ := 1

/-- Number of colors. -/
def Nc : ℚ := 3

/-- Number of weak doublet components. -/
def Nw : ℚ := 2

/-! ## 2. Hypercharge sum: k₁ = Σ d_c · d_w · Y² = 10/3 -/

/-- The hypercharge sum over one SM generation, weighted by color
    and weak multiplicities:
    k₁ = Nc·Nw·Y_Q² + Nc·Y_u² + Nc·Y_d² + Nw·Y_L² + Y_e² -/
def hyperchargeSum : ℚ :=
  Nc * Nw * Y_Q ^ 2 + Nc * Y_u ^ 2 + Nc * Y_d ^ 2 +
  Nw * Y_L ^ 2 + Y_e ^ 2

/-- The hypercharge sum equals 10/3. -/
theorem hyperchargeSum_eq : hyperchargeSum = 10 / 3 := by
  unfold hyperchargeSum Nc Nw Y_Q Y_u Y_d Y_L Y_e
  norm_num

/-! ## 3. Isospin sum: k₂ = Σ d_c · T₃² = 2 -/

/-- The isospin (T₃²) sum over one SM generation.
    Each doublet has two components with T₃ = ±1/2.
    Quark doublets: Nc colors × 2 components × (1/2)²
    Lepton doublets: 2 components × (1/2)²
    k₂ = Nc · 2 · (1/2)² + 2 · (1/2)² = Nc/2 + 1/2 = 2 -/
def isospinSum : ℚ :=
  Nc * Nw * (1 / 2) ^ 2 + Nw * (1 / 2) ^ 2

/-- The isospin sum equals 2. -/
theorem isospinSum_eq : isospinSum = 2 := by
  unfold isospinSum Nc Nw
  norm_num

/-! ## 4. GUT normalization factor = 5/3 -/

/-- The GUT normalization factor: the ratio k₁/k₂ that rescales the
    U(1) coupling so that Tr(T₁²) = Tr(T₂²) in the unified group.
    At unification, g₁ = √(5/3) · g', equivalently g'² = (3/5) · g₁². -/
def gutNormalization : ℚ := hyperchargeSum / isospinSum

/-- The GUT normalization factor equals 5/3. -/
theorem gutNormalization_eq : gutNormalization = 5 / 3 := by
  unfold gutNormalization
  rw [hyperchargeSum_eq, isospinSum_eq]
  norm_num

/-! ## 5. sin²θ_W = 3/8 at unification -/

/-- The Weinberg angle at the unification scale.
    sin²θ_W = g'²/(g² + g'²).
    With GUT normalization g'² = (3/5)·g² at unification (g₁ = g₂ = g):
    sin²θ_W = (3/5)/(1 + 3/5) = (3/5)/(8/5) = 3/8.

    We express this as: sin²θ_W = 1/(1 + k₁/k₂) = k₂/(k₁ + k₂). -/
def sin2_weinberg : ℚ := isospinSum / (hyperchargeSum + isospinSum)

/-- **Main theorem**: sin²θ_W = 3/8 at the unification scale. -/
theorem sin2_weinberg_eq : sin2_weinberg = 3 / 8 := by
  unfold sin2_weinberg
  rw [hyperchargeSum_eq, isospinSum_eq]
  norm_num

/-- Equivalent formulation: sin²θ_W = 3/(3+5) from the GUT normalization. -/
theorem sin2_weinberg_from_normalization :
    (3 : ℚ) / (3 + 5) = 3 / 8 := by norm_num

/-- The direct computation: with g'² = (3/5)·g² at unification,
    g'²/(g² + g'²) = (3/5·g²)/(g² + 3/5·g²) = (3/5)/(8/5) = 3/8.
    We prove this for any nonzero g². -/
theorem sin2_from_coupling_ratio (g_sq : ℚ) (hg : g_sq ≠ 0) :
    (3 / 5 * g_sq) / (g_sq + 3 / 5 * g_sq) = 3 / 8 := by
  have h8 : g_sq + 3 / 5 * g_sq = 8 / 5 * g_sq := by ring
  rw [h8]
  field_simp

/-! ## 6. sin²θ_W ≠ 1/4 (ruling out other values) -/

/-- sin²θ_W ≠ 1/4 — ruling out the commonly guessed alternative. -/
theorem sin2_weinberg_ne_quarter : sin2_weinberg ≠ 1 / 4 := by
  rw [sin2_weinberg_eq]
  norm_num

/-- sin²θ_W ≠ 1/3. -/
theorem sin2_weinberg_ne_third : sin2_weinberg ≠ 1 / 3 := by
  rw [sin2_weinberg_eq]
  norm_num

/-- sin²θ_W ≠ 1/2. -/
theorem sin2_weinberg_ne_half : sin2_weinberg ≠ 1 / 2 := by
  rw [sin2_weinberg_eq]
  norm_num

/-! ## 7. Parametric derivation: k₁ and k₂ from general hypercharges -/

/-- The hypercharge sum as a function of five arbitrary hypercharges
    and multiplicities Nc, Nw. -/
def hyperchargeSumGen (nc nw yQ yu yd yL ye : ℚ) : ℚ :=
  nc * nw * yQ ^ 2 + nc * yu ^ 2 + nc * yd ^ 2 +
  nw * yL ^ 2 + ye ^ 2

/-- With SM values, the generic formula reduces to 10/3. -/
theorem hyperchargeSumGen_sm :
    hyperchargeSumGen 3 2 (1/6) (-(2/3)) (1/3) (-(1/2)) 1 = 10 / 3 := by
  unfold hyperchargeSumGen
  norm_num

/-- The isospin sum as a function of Nc and Nw. -/
def isospinSumGen (nc nw : ℚ) : ℚ :=
  nc * nw * (1 / 2) ^ 2 + nw * (1 / 2) ^ 2

/-- With SM values Nc=3, Nw=2, the isospin sum is 2. -/
theorem isospinSumGen_sm : isospinSumGen 3 2 = 2 := by
  unfold isospinSumGen
  norm_num

/-- The Weinberg angle from general sums. -/
def sin2Gen (k1 k2 : ℚ) : ℚ := k2 / (k1 + k2)

/-- With k₁ = 10/3 and k₂ = 2, sin²θ_W = 3/8. -/
theorem sin2Gen_sm : sin2Gen (10/3) 2 = 3 / 8 := by
  unfold sin2Gen
  norm_num

/-! ## 8. The relation to integer hypercharge ratios -/

/-- SM hypercharges in units of y_Q = 1/6 are (1, -4, 2, -3, 6).
    The hypercharge sum in these integer units:
    Nc·Nw·1² + Nc·4² + Nc·2² + Nw·3² + 6² = 6 + 48 + 12 + 18 + 36 = 120.
    Then k₁ = 120 · y_Q² = 120/36 = 10/3. -/
theorem hyperchargeSum_from_integers :
    (3 : ℚ) * 2 * 1 ^ 2 + 3 * 4 ^ 2 + 3 * 2 ^ 2 + 2 * 3 ^ 2 + 6 ^ 2 = 120 := by
  norm_num

theorem hyperchargeSum_from_integers_rescaled :
    (120 : ℚ) * (1 / 6) ^ 2 = 10 / 3 := by norm_num

/-! ## 9. Summary theorem -/

/-- sin²θ_W lies strictly between 0 and 1/2 (below maximal mixing). -/
theorem sin2_weinberg_in_range :
    (0 : ℚ) < sin2_weinberg ∧ sin2_weinberg < 1 / 2 := by
  rw [sin2_weinberg_eq]; constructor <;> norm_num

/-- sin²θ_W × 8 = 3: the angle has small-integer structure. -/
theorem sin2_weinberg_times_eight :
    sin2_weinberg * 8 = 3 := by
  rw [sin2_weinberg_eq]; norm_num

/-- Perturbed hypercharge sum: shift Y_Q by δ from its SM value 1/6. -/
def hyperchargeSumPerturbed (δ : ℚ) : ℚ :=
  3 * 2 * (1/6 + δ)^2 + 3 * (2/3)^2 + 3 * (1/3)^2 + 2 * (1/2)^2 + 1^2

/-- Perturbed Weinberg angle. -/
def sin2_perturbed (δ : ℚ) : ℚ :=
  isospinSum / (hyperchargeSumPerturbed δ + isospinSum)

/-- At δ = 0, the perturbed angle equals SM value 3/8. -/
theorem sin2_perturbed_at_zero : sin2_perturbed 0 = 3 / 8 := by
  native_decide

/-- At δ = -1/3, the perturbed angle also equals 3/8 (sign-flip of Y_Q). -/
theorem sin2_perturbed_at_neg_third : sin2_perturbed (-1/3) = 3 / 8 := by
  native_decide

/-- At δ = 1/6, the perturbed angle is NOT 3/8 (concrete perturbation check). -/
theorem sin2_perturbed_ne_at_sixth : sin2_perturbed (1/6) ≠ 3 / 8 := by
  native_decide

/-- At δ = -1/6, the perturbed angle is NOT 3/8 (concrete perturbation check). -/
theorem sin2_perturbed_ne_at_neg_sixth : sin2_perturbed (-1/6) ≠ 3 / 8 := by
  native_decide

/-- At δ = 1/3, the perturbed angle is NOT 3/8. -/
theorem sin2_perturbed_ne_at_third : sin2_perturbed (1/3) ≠ 3 / 8 := by
  native_decide

end UnifiedTheory.LayerA.WeinbergAngle
