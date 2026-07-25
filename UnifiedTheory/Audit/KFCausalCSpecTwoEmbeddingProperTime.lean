/-
  Audit/KFCausalCSpecTwoEmbeddingProperTime.lean   (Volume sector — the F3 bypass)

  A machine-checked replacement for Madsen's condition F3 (longest chains track proper
  time).  Madsen (arXiv:2607.05840, §2.2) leaves open whether F2 (counts track volumes)
  already supplies the distance information F3 was assumed to give.  This unit answers
  it in the affirmative under bounded geometry: the SAME intrinsic interval count `N`,
  read in two order- and volume-faithful embeddings, pins the two proper times to an
  explicit ratio band that collapses to `1` in the high-density / sub-curvature limit --
  WITHOUT ever invoking longest chains.

  Physical setup (same causally related pair x < y in both embeddings i = 1, 2):
    * small-diamond volume law with curvature error:  Vol_i = C_d τ_i^d (1 + κ_i),
      |κ_i| ≤ β   (β is the Step-1 curvature remainder ~ C_d' τ^2 / λ^2 -- an ANALYTIC
      INPUT taken here as a hypothesis, not proved: it is Roy-Sinha-Surya geometry);
    * count law with Poisson error:  N = ρ C_d Vol_i (1 + δ_i), |δ_i| ≤ ε   (ε from the
      completed count-concentration machinery).

  Since the integer `N` is intrinsic to the causal set, both embeddings satisfy
  `N = ρ C_d τ_i^d (1+κ_i)(1+δ_i)`, and the shared `N` forces

      ((1-β)(1-ε) / ((1+β)(1+ε)))^(1/d) ≤ τ_1/τ_2 ≤ ((1+β)(1+ε) / ((1-β)(1-ε)))^(1/d).

  As β, ε → 0 the band collapses to `τ_1 = τ_2` (`two_embedding_properTime_exact`).

  This does NOT prove the naive universal finite Hauptvermutung (Müller
  arXiv:2503.01719 showed that is false); it proves the quantitative bounded-geometry
  order-plus-number version -- the F3-free distance-comparison step.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Real

namespace UnifiedTheory.Audit.KFCausalCSpecTwoEmbeddingProperTime

/-- **Two-embedding proper-time ratio band (F3 bypass).**  One intrinsic interval count
`N`, read in two order- and volume-faithful embeddings with curvature error `β` and
count error `ε`, pins the proper-time ratio to an explicit band -- no longest chains. -/
theorem two_embedding_properTime_ratio_band
    (d : ℕ) (hd : 1 ≤ d)
    (N ρ Cd τ₁ τ₂ κ₁ κ₂ δ₁ δ₂ β ε : ℝ)
    (hρ : 0 < ρ) (hCd : 0 < Cd) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hβ1 : β < 1) (hε1 : ε < 1)
    (hκ₁ : |κ₁| ≤ β) (hκ₂ : |κ₂| ≤ β) (hδ₁ : |δ₁| ≤ ε) (hδ₂ : |δ₂| ≤ ε)
    (hN₁ : N = ρ * Cd * τ₁ ^ d * ((1 + κ₁) * (1 + δ₁)))
    (hN₂ : N = ρ * Cd * τ₂ ^ d * ((1 + κ₂) * (1 + δ₂))) :
    ((1 - β) * (1 - ε) / ((1 + β) * (1 + ε))) ^ ((d : ℝ)⁻¹) ≤ τ₁ / τ₂
    ∧ τ₁ / τ₂ ≤ ((1 + β) * (1 + ε) / ((1 - β) * (1 - ε))) ^ ((d : ℝ)⁻¹) := by
  obtain ⟨hκ₁l, hκ₁u⟩ := abs_le.mp hκ₁
  obtain ⟨hκ₂l, hκ₂u⟩ := abs_le.mp hκ₂
  obtain ⟨hδ₁l, hδ₁u⟩ := abs_le.mp hδ₁
  obtain ⟨hδ₂l, hδ₂u⟩ := abs_le.mp hδ₂
  have hβ0 : 0 ≤ β := le_trans (abs_nonneg κ₁) hκ₁
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg δ₁) hδ₁
  have p1β : (0:ℝ) < 1 - β := by linarith
  have p1ε : (0:ℝ) < 1 - ε := by linarith
  have hden₁ : (0:ℝ) < (1 + κ₁) * (1 + δ₁) := mul_pos (by linarith) (by linarith)
  have hden₂ : (0:ℝ) < (1 + β) * (1 + ε) := mul_pos (by linarith) (by linarith)
  have hdenP : (0:ℝ) < (1 - β) * (1 - ε) := mul_pos p1β p1ε
  have hApos : (0:ℝ) < (1 + κ₂) * (1 + δ₂) := mul_pos (by linarith) (by linarith)
  -- reduce the two count laws to the shared-N constraint (ρ, C_d cancel)
  have hN : τ₁ ^ d * ((1 + κ₁) * (1 + δ₁)) = τ₂ ^ d * ((1 + κ₂) * (1 + δ₂)) := by
    apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hρ) (ne_of_gt hCd))
    linear_combination hN₁.symm.trans hN₂
  -- (τ₁/τ₂)^d equals the error ratio M
  have hM : (τ₁ / τ₂) ^ d = (1 + κ₂) * (1 + δ₂) / ((1 + κ₁) * (1 + δ₁)) := by
    rw [div_pow, div_eq_div_iff (pow_pos hτ₂ d).ne' hden₁.ne']
    linear_combination hN
  -- recover τ₁/τ₂ = ((τ₁/τ₂)^d)^(1/d)
  have hpos : (0:ℝ) < τ₁ / τ₂ := div_pos hτ₁ hτ₂
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrec : τ₁ / τ₂ = ((τ₁ / τ₂) ^ d) ^ ((d : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast (τ₁ / τ₂) d, ← Real.rpow_mul hpos.le, mul_inv_cancel₀ hd0,
      Real.rpow_one]
  -- the four product bounds
  have hAlow : (1 - β) * (1 - ε) ≤ (1 + κ₂) * (1 + δ₂) :=
    mul_le_mul (by linarith) (by linarith) p1ε.le (by linarith)
  have hBhigh : (1 + κ₁) * (1 + δ₁) ≤ (1 + β) * (1 + ε) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hAhigh : (1 + κ₂) * (1 + δ₂) ≤ (1 + β) * (1 + ε) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hBlow : (1 - β) * (1 - ε) ≤ (1 + κ₁) * (1 + δ₁) :=
    mul_le_mul (by linarith) (by linarith) p1ε.le (by linarith)
  -- band on M
  have hMlow : (1 - β) * (1 - ε) / ((1 + β) * (1 + ε))
      ≤ (1 + κ₂) * (1 + δ₂) / ((1 + κ₁) * (1 + δ₁)) := by
    rw [div_le_iff₀ hden₂, div_mul_eq_mul_div, le_div_iff₀ hden₁]
    exact mul_le_mul hAlow hBhigh hden₁.le hApos.le
  have hMhigh : (1 + κ₂) * (1 + δ₂) / ((1 + κ₁) * (1 + δ₁))
      ≤ (1 + β) * (1 + ε) / ((1 - β) * (1 - ε)) := by
    rw [div_le_iff₀ hden₁, div_mul_eq_mul_div, le_div_iff₀ hdenP]
    exact mul_le_mul hAhigh hBlow hdenP.le hden₂.le
  have hz : (0:ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  rw [hrec, hM]
  exact ⟨Real.rpow_le_rpow (div_nonneg (mul_nonneg p1β.le p1ε.le) hden₂.le) hMlow hz,
    Real.rpow_le_rpow (div_pos hApos hden₁).le hMhigh hz⟩

/-- **High-density / sub-curvature limit point.**  With no curvature or count error the
two embeddings agree exactly on proper time: `τ₁ = τ₂`.  This is the band's collapse to
`[1, 1]` as `β, ε → 0`. -/
theorem two_embedding_properTime_exact
    (d : ℕ) (hd : 1 ≤ d) (N ρ Cd τ₁ τ₂ : ℝ)
    (hρ : 0 < ρ) (hCd : 0 < Cd) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hN₁ : N = ρ * Cd * τ₁ ^ d) (hN₂ : N = ρ * Cd * τ₂ ^ d) :
    τ₁ = τ₂ := by
  have hpow : τ₁ ^ d = τ₂ ^ d := by
    apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hρ) (ne_of_gt hCd))
    linear_combination hN₁.symm.trans hN₂
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e1 : τ₁ = (τ₁ ^ d) ^ ((d : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast τ₁ d, ← Real.rpow_mul hτ₁.le, mul_inv_cancel₀ hd0, Real.rpow_one]
  have e2 : τ₂ = (τ₂ ^ d) ^ ((d : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast τ₂ d, ← Real.rpow_mul hτ₂.le, mul_inv_cancel₀ hd0, Real.rpow_one]
  rw [e1, e2, hpow]

#print axioms two_embedding_properTime_ratio_band
#print axioms two_embedding_properTime_exact

end UnifiedTheory.Audit.KFCausalCSpecTwoEmbeddingProperTime
