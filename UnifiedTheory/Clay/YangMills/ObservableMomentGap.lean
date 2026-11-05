/- Observable-dependent power-moment decay forces a Hilbert-space contraction.
No uniform prefactor, compactness, spectral decomposition or operator-norm
bound is assumed. Scalar convexity lemmas also apply before L2 completion. -/
import UnifiedTheory.Clay.YangMills.TransferEnergySurvival
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Topology.Closure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ObservableMomentGap
noncomputable section
open scoped InnerProductSpace

/-- A bounded-above convex sequence cannot increase at its first step. -/
theorem bounded_convex_initial_le (s : ℕ → ℝ) (C : ℝ)
    (hc : ∀ k, 2 * s (k + 1) ≤ s k + s (k + 2)) (hb : ∀ k, s k ≤ C) :
    s 1 ≤ s 0 := by
  by_contra h
  have hd : 0 < s 1 - s 0 := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨k, hk⟩ := exists_nat_gt ((C - s 0) / (s 1 - s 0))
  have hl := TransferEnergySurvival.convex_sequence_lower s hc k
  have hh := (div_lt_iff₀ hd).mp hk
  linarith [hb k]

/-- Weighted convexity and a geometric upper bound remove the prefactor completely. -/
theorem geometric_convex_initial_le (s : ℕ → ℝ) (r C : ℝ) (hr : 0 < r)
    (hc : ∀ k, 2 * r * s (k + 1) ≤ r ^ 2 * s k + s (k + 2))
    (hb : ∀ k, s k ≤ C * r ^ k) : s 1 ≤ r * s 0 := by
  let t : ℕ → ℝ := fun k => s k / r ^ k
  have ht (k : ℕ) : t k ≤ C := (div_le_iff₀ (pow_pos hr k)).mpr (hb k)
  have htconv (k : ℕ) : 2 * t (k + 1) ≤ t k + t (k + 2) := by
    have hleft : 2 * t (k + 1) = (2 * r * s (k + 1)) / r ^ (k + 2) := by
      dsimp only [t]
      simp only [pow_add, pow_one]
      field_simp
    have hright : t k + t (k + 2) = (r ^ 2 * s k + s (k + 2)) / r ^ (k + 2) := by
      dsimp only [t]
      simp only [pow_add]
      field_simp
    rw [hleft, hright]
    exact div_le_div_of_nonneg_right (hc k) (pow_nonneg hr.le _)
  have h := bounded_convex_initial_le t C htconv ht
  have hdiv : s 1 / r ≤ s 0 := by simpa only [t, pow_one, pow_zero, div_one] using h
  simpa only [mul_comm] using (div_le_iff₀ hr).mp hdiv

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Symmetry propagates to powers of the actual continuous linear operator. -/
theorem power_symmetric (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (k : ℕ) (x y : H) :
    inner 𝕜 ((A ^ k) x) y = inner 𝕜 x ((A ^ k) y) := by
  have hA : (A : H →ₗ[𝕜] H).IsSymmetric := hs
  simpa only [ContinuousLinearMap.coe_pow, Module.End.coe_pow] using hA.pow k x y

/-- Even moments are the genuine squared power norms. -/
theorem even_moment (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (f : H) (k : ℕ) :
    RCLike.re (inner 𝕜 f ((A ^ (2 * k)) f)) = ‖(A ^ k) f‖ ^ 2 := by
  rw [show 2 * k = k + k by omega, pow_add, ContinuousLinearMap.mul_apply,
    ← power_symmetric A hs k]
  exact inner_self_eq_norm_sq (𝕜 := 𝕜) _

/-- The neighboring-pair identity alone supplies weighted convexity for a vector sequence. -/
theorem sequence_weighted_convex (u : ℕ → H)
    (hp : ∀ k, RCLike.re (inner 𝕜 (u k) (u (k + 2))) = ‖u (k + 1)‖ ^ 2)
    (r : ℝ) (k : ℕ) :
    2 * r * ‖u (k + 1)‖ ^ 2 ≤ r ^ 2 * ‖u k‖ ^ 2 + ‖u (k + 2)‖ ^ 2 := by
  have h := norm_sub_sq (𝕜 := 𝕜) ((r : 𝕜) • u k) (u (k + 2))
  rw [norm_smul, RCLike.norm_ofReal, inner_smul_real_left, RCLike.smul_re, hp k] at h
  simp only [mul_pow, sq_abs] at h
  nlinarith [sq_nonneg ‖(r : 𝕜) • u k - u (k + 2)‖]

/-- This vector-sequence version needs no completed bounded operator construction. -/
theorem sequence_norm_le_of_geometric_bound (u : ℕ → H)
    (hp : ∀ k, RCLike.re (inner 𝕜 (u k) (u (k + 2))) = ‖u (k + 1)‖ ^ 2)
    (q C : ℝ) (hq : 0 ≤ q) (hb : ∀ k, ‖u k‖ ^ 2 ≤ C * q ^ (2 * k)) :
    ‖u 1‖ ≤ q * ‖u 0‖ := by
  rcases hq.eq_or_lt with hq | hq
  · have h := hb 1
    rw [← hq] at h
    simp only [mul_one, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    have hz : ‖u 1‖ = 0 := by nlinarith [norm_nonneg (u 1)]
    simp [← hq, hz]
  · have h := geometric_convex_initial_le (fun k => ‖u k‖ ^ 2) (q ^ 2) C
      (sq_pos_of_pos hq) (sequence_weighted_convex u hp (q ^ 2))
      (fun k => by simpa only [pow_mul] using hb k)
    nlinarith [norm_nonneg (u 1), norm_nonneg (u 0), mul_nonneg hq.le (norm_nonneg (u 0))]

/-- The same sequence data yield a Dirichlet gap before completion of the observable space. -/
theorem sequence_quadratic_gap (u : ℕ → H)
    (hp : ∀ k, RCLike.re (inner 𝕜 (u k) (u (k + 2))) = ‖u (k + 1)‖ ^ 2)
    (q C : ℝ) (hq : 0 ≤ q) (hb : ∀ k, ‖u k‖ ^ 2 ≤ C * q ^ (2 * k)) :
    (1 - q) * ‖u 0‖ ^ 2 ≤ RCLike.re (inner 𝕜 (u 0) (u 0 - u 1)) := by
  have hn := sequence_norm_le_of_geometric_bound u hp q C hq hb
  have hi : RCLike.re (inner 𝕜 (u 0) (u 1)) ≤ q * ‖u 0‖ ^ 2 := by
    calc
      _ ≤ ‖inner 𝕜 (u 0) (u 1)‖ := RCLike.re_le_norm _
      _ ≤ ‖u 0‖ * ‖u 1‖ := norm_inner_le_norm _ _
      _ ≤ ‖u 0‖ * (q * ‖u 0‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by ring
  rw [inner_sub_right, map_sub, inner_self_eq_norm_sq]
  nlinarith

/-- Symmetry identifies the neighboring power pairing exactly. -/
theorem adjacent_power_pairing (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (f : H) (k : ℕ) :
    RCLike.re (inner 𝕜 ((A ^ k) f) ((A ^ (k + 2)) f)) =
      ‖(A ^ (k + 1)) f‖ ^ 2 := by
  have h1 : (A ^ (k + 1)) f = A ((A ^ k) f) := by
    rw [pow_succ', ContinuousLinearMap.mul_apply]
  have h2 : (A ^ (k + 2)) f = A (A ((A ^ k) f)) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ', ContinuousLinearMap.mul_apply, h1]
  rw [h2, ← hs, h1]
  exact inner_self_eq_norm_sq (𝕜 := 𝕜) _

/-- Reversibility gives every weighted convexity inequality, not just unit scaling. -/
theorem power_norm_weighted_convex (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (f : H) (r : ℝ) (k : ℕ) :
    2 * r * ‖(A ^ (k + 1)) f‖ ^ 2 ≤
      r ^ 2 * ‖(A ^ k) f‖ ^ 2 + ‖(A ^ (k + 2)) f‖ ^ 2 :=
  sequence_weighted_convex (fun k => (A ^ k) f) (adjacent_power_pairing A hs f) r k

/-- A geometric bound on this vector's squared power norms forces its one-step contraction. -/
theorem norm_le_of_power_bound (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (f : H)
    (q C : ℝ) (hq : 0 ≤ q) (hb : ∀ k, ‖(A ^ k) f‖ ^ 2 ≤ C * q ^ (2 * k)) :
    ‖A f‖ ≤ q * ‖f‖ := by
  simpa only [pow_one, pow_zero, ContinuousLinearMap.one_apply] using
    sequence_norm_le_of_geometric_bound (fun k => (A ^ k) f)
      (adjacent_power_pairing A hs f) q C hq hb

/-- The prefactor may depend arbitrarily on the observable; even moments suffice. -/
theorem norm_le_of_moment_bound (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (f : H)
    (q C : ℝ) (hq : 0 ≤ q)
    (hb : ∀ k, ‖inner 𝕜 f ((A ^ k) f)‖ ≤ C * q ^ k) : ‖A f‖ ≤ q * ‖f‖ := by
  apply norm_le_of_power_bound A hs f q C hq
  intro k
  rw [← even_moment A hs f k]
  exact (RCLike.re_le_norm _).trans (hb (2 * k))

/-- Moment decay on a dense test set implies contraction everywhere by continuity. -/
theorem contraction_of_dense_moments (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (q : ℝ) (hq : 0 ≤ q)
    (D : Set H) (hD : Dense D)
    (hb : ∀ f ∈ D, ∃ C : ℝ, ∀ k, ‖inner 𝕜 f ((A ^ k) f)‖ ≤ C * q ^ k) :
    ∀ f, ‖A f‖ ≤ q * ‖f‖ := by
  intro f
  refine hD.induction (P := fun g => ‖A g‖ ≤ q * ‖g‖) ?_ ?_ f
  · intro f hf
    obtain ⟨C, hC⟩ := hb f hf
    exact norm_le_of_moment_bound A hs f q C hq hC
  · exact isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)

/-- No uniform bound on the observable prefactors is needed for the operator norm. -/
theorem operator_norm_le_of_dense_moments (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (q : ℝ) (hq : 0 ≤ q)
    (D : Set H) (hD : Dense D)
    (hb : ∀ f ∈ D, ∃ C : ℝ, ∀ k, ‖inner 𝕜 f ((A ^ k) f)‖ ≤ C * q ^ k) :
    ‖A‖ ≤ q :=
  A.opNorm_le_bound hq (contraction_of_dense_moments A hs q hq D hD hb)

/-- On a centered space, q < 1 makes this the positive variance/Dirichlet gap. -/
theorem quadratic_gap_of_dense_moments (A : H →L[𝕜] H)
    (hs : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (A y)) (q : ℝ) (hq : 0 ≤ q)
    (D : Set H) (hD : Dense D)
    (hb : ∀ f ∈ D, ∃ C : ℝ, ∀ k, ‖inner 𝕜 f ((A ^ k) f)‖ ≤ C * q ^ k)
    (f : H) : (1 - q) * ‖f‖ ^ 2 ≤ RCLike.re (inner 𝕜 f (f - A f)) := by
  have hnorm := contraction_of_dense_moments A hs q hq D hD hb f
  have hinner : RCLike.re (inner 𝕜 f (A f)) ≤ q * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖inner 𝕜 f (A f)‖ := RCLike.re_le_norm _
      _ ≤ ‖f‖ * ‖A f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (q * ‖f‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg f)
      _ = _ := by ring
  rw [inner_sub_right, map_sub, inner_self_eq_norm_sq]
  nlinarith

end
end UnifiedTheory.Clay.YangMills.ObservableMomentGap
