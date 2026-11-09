/- A quantitative continuum survival criterion from the one-step transfer
Dirichlet form. This proves the bridge; it does not assume or prove that the
physical Wilson transfer operators satisfy the required O(a) energy estimate. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.TransferEnergySurvival
noncomputable section
open Filter
open scoped Topology

/-- A convex sequence lies above the affine line through its first two values. -/
theorem convex_sequence_lower (q : ℕ → ℝ)
    (hq : ∀ n, 2*q (n+1) ≤ q n+q (n+2)) (n : ℕ) :
    q 0+(n : ℝ)*(q 1-q 0) ≤ q n := by
  have hd (m : ℕ) : q 1-q 0 ≤ q (m+1)-q m := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hh := hq m
      simp only [Nat.succ_eq_add_one] at *
      linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := hd n
    simp only [Nat.cast_succ]
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Iterates are kept explicit so no functional calculus or spectral measure
is supplied as an extra assumption. -/
def iterate (T : E →L[ℂ] E) : ℕ → E → E
  | 0, w => w
  | n+1, w => T (iterate T n w)

@[simp] theorem iterate_zero (T : E →L[ℂ] E) (w : E) : iterate T 0 w = w := rfl
@[simp] theorem iterate_succ (T : E →L[ℂ] E) (n : ℕ) (w : E) :
    iterate T (n+1) w = T (iterate T n w) := rfl

theorem iterate_add (T : E →L[ℂ] E) (n m : ℕ) (w : E) :
    iterate T (n+m) w = iterate T n (iterate T m w) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Nat.succ_add, iterate_succ] using congrArg T ih

theorem iterate_symmetric (T : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (n : ℕ) (x y : E) :
    inner ℂ (iterate T n x) y = inner ℂ x (iterate T n y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ, hs, ih]
    congr 1
    have hh := iterate_add T n 1 y
    have hh' := iterate_add T 1 n y
    simpa only [iterate_succ, iterate_zero, Nat.add_comm] using hh.symm.trans (by simpa only [Nat.add_comm] using hh')

def dirichlet (T : E →L[ℂ] E) (w : E) : ℝ :=
  ‖w‖^2-(inner ℂ w (T w)).re

theorem even_pairing (T : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (n : ℕ) (w : E) :
    (inner ℂ w (iterate T (2*n) w)).re = ‖iterate T n w‖^2 := by
  rw [show 2*n = n+n by omega, iterate_add, ← iterate_symmetric T hs]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem norm_square_convex (T : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (w : E) (n : ℕ) :
    2*‖iterate T (n+1) w‖^2 ≤ ‖iterate T n w‖^2+‖iterate T (n+2) w‖^2 := by
  have he : (inner ℂ (iterate T n w) (iterate T (n+2) w)).re =
      ‖iterate T (n+1) w‖^2 := by
    change (inner ℂ (iterate T n w) (T (T (iterate T n w)))).re = ‖T (iterate T n w)‖^2
    rw [← hs]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hh := norm_sub_sq (𝕜 := ℂ) (iterate T n w) (iterate T (n+2) w)
  change ‖iterate T n w-iterate T (n+2) w‖^2 =
    ‖iterate T n w‖^2-2*(inner ℂ (iterate T n w) (iterate T (n+2) w)).re+
    ‖iterate T (n+2) w‖^2 at hh
  rw [he] at hh
  nlinarith [sq_nonneg ‖iterate T n w-iterate T (n+2) w‖]

theorem one_step_loss (T : E →L[ℂ] E) (w : E) :
    ‖w‖^2-‖T w‖^2 ≤ 2*dirichlet T w := by
  have hh := norm_sub_sq (𝕜 := ℂ) w (T w)
  change ‖w-T w‖^2 = ‖w‖^2-2*(inner ℂ w (T w)).re+‖T w‖^2 at hh
  unfold dirichlet
  nlinarith [sq_nonneg ‖w-T w‖]

/-- A one-step Dirichlet estimate controls a number of steps growing like
inverse spacing. No strictly positive correlation is assumed. -/
theorem propagated_lower (T : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (w : E) (n : ℕ) :
    ‖w‖^2-2*(n : ℝ)*dirichlet T w ≤ (inner ℂ w (iterate T (2*n) w)).re := by
  have hh := convex_sequence_lower (fun m => ‖iterate T m w‖^2) (norm_square_convex T hs w) n
  simp only [iterate_zero, iterate_succ] at hh
  rw [even_pairing T hs]
  have hstep := mul_le_mul_of_nonneg_left (one_step_loss T w) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem physical_time_lower (T : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (w : E)
    (a C tau : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (htime : 2*(n : ℝ)*a ≤ tau)
    (henergy : dirichlet T w ≤ C*a*‖w‖^2) :
    (1-C*tau)*‖w‖^2 ≤ (inner ℂ w (iterate T (2*n) w)).re := by
  have he := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 2*(n : ℝ) by positivity)
  have ht := mul_le_mul_of_nonneg_right htime (mul_nonneg hC (sq_nonneg ‖w‖))
  have hp := propagated_lower T hs w n
  nlinarith

/-- Uniform positive input norm and O(a) relative transfer energy give an
actual uniform reflected floor over a fixed short physical time interval. -/
theorem half_norm_survives (T : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (w : E)
    (a C tau c : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (htime : 2*(n : ℝ)*a ≤ tau) (hsmall : C*tau ≤ 1/2)
    (henergy : dirichlet T w ≤ C*a*‖w‖^2) (hnorm : c ≤ ‖w‖^2) :
    c/2 ≤ (inner ℂ w (iterate T (2*n) w)).re := by
  have hp := physical_time_lower T hs w a C tau hC n htime henergy
  have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖w‖)
  nlinarith

theorem iterate_contraction (T : E →L[ℂ] E) (hc : ∀ x, ‖T x‖ ≤ ‖x‖)
    (n : ℕ) (w : E) : ‖iterate T n w‖ ≤ ‖w‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (hc _).trans ih

end
end UnifiedTheory.Clay.YangMills.TransferEnergySurvival
