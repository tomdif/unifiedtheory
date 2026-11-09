/- Transfer boundedness from a stronger Hilbert norm to an embedded physical
norm when both an operator and its physical adjoint act on the stronger space. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEmbeddedAdjointBound
noncomputable section
open Filter Topology

theorem exponential_log_convex_bound (u : ℕ → ℝ) (b C : ℝ) (hb : 0 ≤ b)
    (hu : ∀ n, 0 ≤ u n) (hlog : ∀ n, u (n+1)^2 ≤ u n*u (n+2))
    (hbound : ∀ n, u n ≤ C*b^n) : u 1 ≤ b*u 0 := by
  by_cases hzero : u 0 = 0
  · have hsq := hlog 0
    simp only [hzero,zero_mul] at hsq
    have hz : u 1 = 0 := by nlinarith [hu 1,sq_nonneg (u 1)]
    simp only [hz,hzero,mul_zero,le_refl]
  have h0 : 0 < u 0 := lt_of_le_of_ne (hu 0) (Ne.symm hzero)
  by_contra hn
  have hlt : b*u 0 < u 1 := lt_of_not_ge hn
  let r := u 1/u 0
  have hrb : b < r := (lt_div_iff₀ h0).mpr hlt
  have hr : 0 < r := lt_of_le_of_lt hb hrb
  have hri : r*u 0 = u 1 := div_mul_cancel₀ _ hzero
  have hstep : ∀ n, 0 < u n ∧ r*u n ≤ u (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,hri.le⟩
    | succ n ih =>
      have hp : 0 < u (n+1) := lt_of_lt_of_le (mul_pos hr ih.1) ih.2
      refine ⟨hp,?_⟩
      have hmul := mul_le_mul_of_nonneg_right ih.2 (hu (n+1))
      have hs := hlog n
      have hh : u n*(r*u (n+1)) ≤ u n*u (n+2) := by nlinarith only [hmul,hs]
      exact le_of_mul_le_mul_left hh ih.1
  have hlow (n : ℕ) : u 0*r^n ≤ u n := by
    induction n with
    | zero => simp only [pow_zero,mul_one,le_refl]
    | succ n ih =>
      calc
        u 0*r^(n+1) = r*(u 0*r^n) := by rw [pow_succ]; ring
        _ ≤ r*u n := mul_le_mul_of_nonneg_left ih hr.le
        _ ≤ u (n+1) := (hstep n).2
  have hquot (n : ℕ) : u 0 ≤ C*(b/r)^n := by
    have hh := (hlow n).trans (hbound n)
    rw [div_pow,← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos hr n)).mpr hh
  have hlim : Tendsto (fun n : ℕ => C*(b/r)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hb hr.le) ((div_lt_one hr).mpr hrb)).const_mul C
  have hz : u 0 ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hquot)
  linarith

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem symmetric_bound (J : V →L[ℂ] H) (B : V →L[ℂ] V)
    (hsym : ∀ x y, inner ℂ (J (B x)) (J y) = inner ℂ (J x) (J (B y)))
    (x : V) : ‖J (B x)‖ ≤ ‖B‖*‖J x‖ := by
  have hlog (n : ℕ) : ‖J ((B^(n+1)) x)‖^2 ≤
      ‖J ((B^n) x)‖*‖J ((B^(n+2)) x)‖ := by
    have he := hsym ((B^n) x) ((B^(n+1)) x)
    simp only [← ContinuousLinearMap.mul_apply,← pow_succ'] at he
    have hre := congrArg Complex.re he
    exact ((norm_sq_eq_re_inner (𝕜 := ℂ) _).trans hre).le.trans
      (re_inner_le_norm (𝕜 := ℂ) (J ((B^n) x)) (J ((B^(n+2)) x)))
  have hp (n : ℕ) : ‖(B^n) x‖ ≤ ‖B‖^n*‖x‖ := by
    induction n with
    | zero => simp only [pow_zero,ContinuousLinearMap.one_apply,one_mul,le_refl]
    | succ n ih =>
      rw [pow_succ',ContinuousLinearMap.mul_apply,pow_succ']
      exact (B.le_opNorm _).trans (by nlinarith only [ih,norm_nonneg B])
  have hb (n : ℕ) : ‖J ((B^n) x)‖ ≤ (‖J‖*‖x‖)*‖B‖^n := by
    calc
      ‖J ((B^n) x)‖ ≤ ‖J‖*‖(B^n) x‖ := J.le_opNorm _
      _ ≤ ‖J‖*(‖B‖^n*‖x‖) := mul_le_mul_of_nonneg_left (hp n) (norm_nonneg _)
      _ = (‖J‖*‖x‖)*‖B‖^n := by ring
  simpa only [pow_one,pow_zero,ContinuousLinearMap.one_apply] using
    exponential_log_convex_bound (fun n => ‖J ((B^n) x)‖) ‖B‖ (‖J‖*‖x‖)
      (norm_nonneg _) (fun n => norm_nonneg _) hlog hb

theorem adjoint_pair_bound (J : V →L[ℂ] H) (T S : V →L[ℂ] V)
    (hpair : ∀ x y, inner ℂ (J (T x)) (J y) = inner ℂ (J x) (J (S y)))
    (x : V) : ‖J (T x)‖^2 ≤ (‖S‖*‖T‖)*‖J x‖^2 := by
  have hsym : ∀ x y, inner ℂ (J ((S*T) x)) (J y) = inner ℂ (J x) (J ((S*T) y)) := by
    intro v w
    have he := congrArg (starRingEnd ℂ) (hpair w (T v))
    simp only [inner_conj_symm,ContinuousLinearMap.mul_apply] at he ⊢
    exact he.symm.trans (hpair v (T w))
  have hnorm := symmetric_bound J (S*T) hsym x
  have he := congrArg Complex.re (hpair x (T x))
  calc
    ‖J (T x)‖^2 = (inner ℂ (J x) (J ((S*T) x))).re :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans he
    _ ≤ ‖J x‖*‖J ((S*T) x)‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖J x‖*(‖S*T‖*‖J x‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ ‖J x‖*((‖S‖*‖T‖)*‖J x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (norm_mul_le S T) (norm_nonneg _)) (norm_nonneg _)
    _ = (‖S‖*‖T‖)*‖J x‖^2 := by ring

#print axioms exponential_log_convex_bound
#print axioms symmetric_bound
#print axioms adjoint_pair_bound
end
end UnifiedTheory.Audit.KFCausalEmbeddedAdjointBound
