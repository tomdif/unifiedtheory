/-
  Audit/KFCausalSmearedNoGo.lean
  — THE SMEARED-4D NO-GO AT ALL DEPTHS (the funding theorem)

  The physically-smeared 4D action-phase growth system is infeasible at
  every depth and every in-window phase, because its TRUNCATION-2
  subsystem — the root equation plus the equations of the 2-chain and
  the 2-antichain, five real constraints on seven nonnegative
  amplitudes — is already contradictory.  Since these equations appear
  verbatim in the system at every depth, infeasibility is inherited by
  all of them: no wrap scale, no depth race, no enumeration needed.

  Setup (φ = 2πj + δ, channel of smeared precursor size s has phase
  angle δ − sφ): with β = W(0)φ − δ (the cover channel), γ = (W(0) +
  W(1))φ − δ (the 2-chain timid channel), η = 2W(0)φ − δ (the Λ
  channel), the six real equations are

    root:  x₁cos β + x₂cos δ = 1,          x₂sin δ = x₁sin β
    2-ch:  v cos β + t cos γ + L cos δ = x₁,  L sin δ = v sin β + t sin γ
    2-ac:  a cos δ + 2L cos β + λ cos η = x₂, a sin δ = 2L sin β + λ sin η

  Elimination gives the funding identity

    v·sinβ·sin(δ+β) + t·(2sinγ·sin(δ+β) − sinβ·sin(δ+γ))
                    + λ·sinδ·sin(δ+η) = 0,

  and — USING β < γ, which is equivalent to W_ε(1) = ε(1 − 10ε) > 0,
  i.e. ε < 1/10 — all three coefficients are strictly positive (the
  middle one equals sinδ·(sinγcosβ + sin(γ−β)) + cosδ·sinβ·sinγ, whose
  positivity is exactly sin(γ−β) > 0; first-quadrant membership alone
  does NOT suffice),
  forcing v = t = λ = 0, hence L = x₁ = x₂ = 0, contradicting the root
  normalization.

  HYPOTHESIS SCOPE (strengthened 2026-08-01): the coefficient
  positivity needs cos only of δ and β; the angles γ and δ+η may leave
  the first quadrant.  The hypotheses are therefore 0 < δ < π/2,
  0 < β < π/2, β < γ, 0 < η, γ + δ < π, η + δ < π.  For in-window
  phases (δ < W₀φ, β = W₀φ − δ, γ = (W₀+W₁)φ − δ, η = 2W₀φ − δ) with
  W₁/W₀ < 1 — which holds for every smeared dimension, since
  W₁/W₀ = 1 − (1+|C₂|)ε — these hypotheses hold for ALL cover windings
  W₀φ < π/2.  The theorem thus kills the entire sub-quadrant winding
  region, matching the numerically exact feasibility boundary at
  W₀φ = π/2 from below (trunc2_hbar_window.py): the lower edge of the
  ℏ-window is theorem-exact.  The boundary phases δ = 0 and β = 0
  are excluded — exactly where the dust and broom spines survive.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSmearedNoGo

open Real

/-- **THE FUNDING THEOREM** (smeared-4D no-go at all depths).  The
truncation-2 subsystem of in-window smeared action-phase growth is
infeasible: no nonnegative amplitudes satisfy the root, 2-chain and
2-antichain equations. -/
theorem smeared_truncation2_infeasible
    (δ β γ η x₁ x₂ v t L a lam : ℝ)
    (hδ : 0 < δ) (hδq : δ < π / 2) (hβ : 0 < β) (hβq : β < π / 2)
    (hβγ : β < γ) (hη : 0 < η)
    (hq1 : γ + δ < π) (hq2 : η + δ < π)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hv : 0 ≤ v) (ht : 0 ≤ t)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hlam : 0 ≤ lam)
    (Rre : x₁ * Real.cos β + x₂ * Real.cos δ = 1)
    (Rim : x₂ * Real.sin δ = x₁ * Real.sin β)
    (Cre : v * Real.cos β + t * Real.cos γ + L * Real.cos δ = x₁)
    (Cim : L * Real.sin δ = v * Real.sin β + t * Real.sin γ)
    (Are : a * Real.cos δ + 2 * L * Real.cos β + lam * Real.cos η = x₂)
    (Aim : a * Real.sin δ = 2 * L * Real.sin β + lam * Real.sin η) :
    False := by
  have hπ : (0:ℝ) < π / 2 := by positivity
  have sδ : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have sβ : 0 < Real.sin β :=
    Real.sin_pos_of_pos_of_lt_pi hβ (by linarith [Real.pi_pos])
  have sγ : 0 < Real.sin γ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have cδ : 0 < Real.cos δ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδq⟩
  have cβ : 0 < Real.cos β :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβq⟩
  have sδβ : 0 < Real.sin (δ + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sδγ : 0 < Real.sin (δ + γ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sδη : 0 < Real.sin (δ + η) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sγβ : 0 < Real.sin (γ - β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- (C*): x₁ sin δ = v sin(δ+β) + t sin(δ+γ)
  have e1 := Real.sin_add δ β
  have e2 := Real.sin_add δ γ
  have e3 := Real.sin_add δ η
  have e4 := Real.sin_sub γ β
  have hCstar : x₁ * Real.sin δ
      = v * Real.sin (δ + β) + t * Real.sin (δ + γ) := by
    rw [e1, e2]
    linear_combination (-Real.sin δ) * Cre + Real.cos δ * Cim
  -- (A*): x₂ sin δ = 2L sin(δ+β) + lam sin(δ+η)
  have hAstar : x₂ * Real.sin δ
      = 2 * L * Real.sin (δ + β) + lam * Real.sin (δ + η) := by
    rw [e1, e3]
    linear_combination (-Real.sin δ) * Are + Real.cos δ * Aim
  -- the funding identity
  have hkey : v * (Real.sin β * Real.sin (δ + β))
      + t * (2 * Real.sin γ * Real.sin (δ + β)
             - Real.sin β * Real.sin (δ + γ))
      + lam * (Real.sin δ * Real.sin (δ + η)) = 0 := by
    linear_combination Real.sin β * hCstar - Real.sin δ * hAstar
      + Real.sin δ * Rim - 2 * Real.sin (δ + β) * Cim
  -- coefficient positivity
  have hcv : 0 < Real.sin β * Real.sin (δ + β) := mul_pos sβ sδβ
  have hct : 0 < 2 * Real.sin γ * Real.sin (δ + β)
      - Real.sin β * Real.sin (δ + γ) := by
    have expand : 2 * Real.sin γ * Real.sin (δ + β)
        - Real.sin β * Real.sin (δ + γ)
        = Real.sin δ * (Real.sin γ * Real.cos β + Real.sin (γ - β))
          + Real.cos δ * (Real.sin β * Real.sin γ) := by
      rw [e1, e2, e4]
      ring
    rw [expand]
    have h1 : 0 < Real.sin γ * Real.cos β + Real.sin (γ - β) :=
      add_pos (mul_pos sγ cβ) sγβ
    exact add_pos (mul_pos sδ h1) (mul_pos cδ (mul_pos sβ sγ))
  have hcl : 0 < Real.sin δ * Real.sin (δ + η) := mul_pos sδ sδη
  -- all three amplitudes vanish (nonneg terms summing to zero)
  have tv := mul_nonneg hv hcv.le
  have tt := mul_nonneg ht hct.le
  have tl := mul_nonneg hlam hcl.le
  have hv0 : v = 0 := by
    refine le_antisymm ?_ hv
    have hle : v * (Real.sin β * Real.sin (δ + β))
        ≤ 0 * (Real.sin β * Real.sin (δ + β)) := by
      rw [zero_mul]; linarith [hkey, tt, tl]
    exact le_of_mul_le_mul_right hle hcv
  have ht0 : t = 0 := by
    refine le_antisymm ?_ ht
    have hle : t * (2 * Real.sin γ * Real.sin (δ + β)
        - Real.sin β * Real.sin (δ + γ))
        ≤ 0 * (2 * Real.sin γ * Real.sin (δ + β)
        - Real.sin β * Real.sin (δ + γ)) := by
      rw [zero_mul]; linarith [hkey, tv, tl]
    exact le_of_mul_le_mul_right hle hct
  have hlam0 : lam = 0 := by
    refine le_antisymm ?_ hlam
    have hle : lam * (Real.sin δ * Real.sin (δ + η))
        ≤ 0 * (Real.sin δ * Real.sin (δ + η)) := by
      rw [zero_mul]; linarith [hkey, tv, tt]
    exact le_of_mul_le_mul_right hle hcl
  -- cascade to the root contradiction
  have hL0 : L = 0 := by
    have : L * Real.sin δ = 0 := by rw [Cim, hv0, ht0]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h sδ.ne'
  have hx10 : x₁ = 0 := by rw [← Cre, hv0, ht0, hL0]; ring
  have hx20 : x₂ = 0 := by
    have : x₂ * Real.sin δ = 0 := by rw [Rim, hx10]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h sδ.ne'
  rw [hx10, hx20] at Rre
  simp at Rre

#print axioms smeared_truncation2_infeasible

end UnifiedTheory.Audit.KFCausalSmearedNoGo
