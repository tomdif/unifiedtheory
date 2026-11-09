/- Positivity of the stationary discrete two-point covariance associated with
a symmetric contraction. The stronger Schur bound also proves that reflection
positivity is compatible with an ordinary positive covariance. No random-field
measure or spacetime locality is asserted here. -/
import UnifiedTheory.Audit.KFCausalResolventReflectionKernel
import Mathlib.Data.Nat.Dist

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalResolventStationaryCovariance
noncomputable section
open scoped BigOperators InnerProduct
open KFCausalResolventReflectionKernel
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def boundary (R : X →L[ℂ] X) (u : ℕ → X) (N : ℕ) : X :=
  ∑ i ∈ Finset.range N, (R ^ i) (u i)

/-- All insertions on a finite integer time interval, with vector-valued sources.
Complex scalar test coefficients are included by scaling the source vectors. -/
def covariance (R : X →L[ℂ] X) (u : ℕ → X) (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    inner ℂ (u i) ((R ^ Nat.dist i j) (u j))

theorem boundary_succ (R : X →L[ℂ] X) (u : ℕ → X) (N : ℕ) :
    boundary R u (N+1) = u 0 + R (boundary R (fun i => u (i+1)) N) := by
  simp only [boundary, Finset.sum_range_succ', pow_zero, ContinuousLinearMap.one_apply,
    map_sum, pow_succ', ContinuousLinearMap.mul_apply]
  abel

theorem covariance_succ (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (u : ℕ → X) (N : ℕ) :
    covariance R u (N+1) =
      inner ℂ (u 0) (u 0) +
      inner ℂ (u 0) (R (boundary R (fun i => u (i+1)) N)) +
      inner ℂ (R (boundary R (fun i => u (i+1)) N)) (u 0) +
      covariance R (fun i => u (i+1)) N := by
  simp only [covariance, Finset.sum_range_succ', Nat.dist_zero_left, Nat.dist_zero_right,
    Nat.dist_succ_succ, pow_zero, ContinuousLinearMap.one_apply, Finset.sum_add_distrib,
    boundary, map_sum, inner_sum, sum_inner, pow_succ', ContinuousLinearMap.mul_apply]
  have he : (∑ i ∈ Finset.range N, inner ℂ (u (i+1)) (R ((R ^ i) (u 0)))) =
      ∑ i ∈ Finset.range N, inner ℂ (R ((R ^ i) (u (i+1)))) (u 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
      (power_pairing R hs (i+1) (u (i+1)) (u 0)).symm
  rw [he]
  abel

theorem covariance_schur_lower (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))
    (hc : ∀ x, ‖R x‖ ≤ ‖x‖) (u : ℕ → X) (N : ℕ) :
    ‖boundary R u N‖^2 ≤ (covariance R u N).re := by
  induction N generalizing u with
  | zero => simp [boundary, covariance]
  | succ N ih =>
      rw [boundary_succ, covariance_succ R hs]
      let b := boundary R (fun i => u (i+1)) N
      have hi := ih (fun i => u (i+1))
      have hn := hc b
      have hn0 := norm_nonneg (R b)
      have hb0 := norm_nonneg b
      have he := norm_add_sq (𝕜 := ℂ) (u 0) (R b)
      have hr := inner_re_symm (𝕜 := ℂ) (R b) (u 0)
      have hx := inner_self_eq_norm_sq (𝕜 := ℂ) (u 0)
      change ‖u 0 + R b‖^2 = ‖u 0‖^2 + 2*(inner ℂ (u 0) (R b)).re + ‖R b‖^2 at he
      change (inner ℂ (R b) (u 0)).re = (inner ℂ (u 0) (R b)).re at hr
      change (inner ℂ (u 0) (u 0)).re = ‖u 0‖^2 at hx
      have hsq : ‖R b‖^2 ≤ ‖b‖^2 := (sq_le_sq₀ hn0 hb0).mpr hn
      change ‖b‖^2 ≤ _ at hi
      change ‖u 0 + R b‖^2 ≤ _
      simp only [Complex.add_re]
      change ‖u 0 + R b‖^2 ≤ (inner ℂ (u 0) (u 0)).re +
        (inner ℂ (u 0) (R b)).re + (inner ℂ (R b) (u 0)).re + _
      linarith

theorem covariance_nonnegative (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))
    (hc : ∀ x, ‖R x‖ ≤ ‖x‖) (u : ℕ → X) (N : ℕ) :
    0 ≤ (covariance R u N).re :=
  (sq_nonneg _).trans (covariance_schur_lower R hs hc u N)

theorem covariance_real (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (u : ℕ → X) (N : ℕ) :
    starRingEnd ℂ (covariance R u N) = covariance R u N := by
  induction N generalizing u with
  | zero => simp [covariance]
  | succ N ih =>
      rw [covariance_succ R hs]
      simp only [map_add, inner_conj_symm, ih]
      abel

end
end UnifiedTheory.Audit.KFCausalResolventStationaryCovariance
