/- Averaging Gaussian cutoffs over dyadic scales retains a cancellation
that is lost when each cutoff derivative is estimated separately.
The sum of the differentiated weights is bounded independently of the
number of scales and the smallest positive cutoff. -/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalDyadicHeatCancellation
noncomputable section
open scoped BigOperators

def width (δ : ℝ) (j : ℕ) : ℝ := δ*2^j

theorem width_pos (δ : ℝ) (hδ : 0 < δ) (j : ℕ) : 0 < width δ j := by
  unfold width
  positivity

theorem weighted_exp_difference (x : ℝ) :
    x*Real.exp (-2*x) ≤ Real.exp (-x)-Real.exp (-2*x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-2*x)).le
  rw [← Real.exp_add,show x+(-2*x) = -x by ring] at h
  nlinarith

theorem dyadic_sum_telescopes (δ r : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (Real.exp (-width δ j*r)-Real.exp (-2*width δ j*r)) =
      Real.exp (-δ*r)-Real.exp (-width δ N*r) := by
  induction N with
  | zero => simp [width]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    have hw : width δ (N+1) = 2*width δ N := by simp [width,pow_succ]; ring
    rw [hw]
    ring_nf

theorem dyadic_sum_bound (δ r : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (N : ℕ) :
    ∑ j ∈ Finset.range N, width δ j*r*Real.exp (-2*width δ j*r) ≤ 1 := by
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        (Real.exp (-width δ j*r)-Real.exp (-2*width δ j*r)) := by
      apply Finset.sum_le_sum
      intro j _
      convert weighted_exp_difference (width δ j*r) using 1 <;> ring
    _ = Real.exp (-δ*r)-Real.exp (-width δ N*r) := dyadic_sum_telescopes δ r N
    _ ≤ 1 := by
      have he : Real.exp (-δ*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith [Real.exp_pos (-width δ N*r)]

def average (δ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (N:ℂ)⁻¹ * ∑ j ∈ Finset.range N, Complex.exp ((-2*width δ j:ℝ)*z)

def slope (δ : ℝ) (N : ℕ) (z w : ℂ) : ℂ :=
  (N:ℂ)⁻¹ * ∑ j ∈ Finset.range N,
    ((-2*width δ j:ℝ)*w)*Complex.exp ((-2*width δ j:ℝ)*z)

theorem average_derivative (δ : ℝ) (N : ℕ) (A : ℂ → ℂ) (q z w : ℂ)
    (hA : HasDerivAt A w q) (hz : A q = z) :
    HasDerivAt (fun x => average δ N (A x)) (slope δ N z w) q := by
  have hj (j : ℕ) : HasDerivAt (fun x => Complex.exp ((-2*width δ j:ℝ)*A x))
      (((-2*width δ j:ℝ)*w)*Complex.exp ((-2*width δ j:ℝ)*z)) q := by
    simpa only [hz,mul_comm] using ((hA.const_mul ((-2*width δ j:ℝ):ℂ)).cexp)
  simpa only [average,slope,Finset.sum_apply] using
    (HasDerivAt.sum (fun j (_ : j ∈ Finset.range N) => hj j)).const_mul (N:ℂ)⁻¹

theorem slope_bound (δ K : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (z w : ℂ) (hz : 0 ≤ z.re) (hw : ‖w‖ ≤ K*z.re) :
    ‖slope δ N z w‖ ≤ 2*K/(N:ℝ) := by
  have hj (j : ℕ) :
      ‖((-2*width δ j:ℝ)*w)*Complex.exp ((-2*width δ j:ℝ)*z)‖ ≤
        2*K*(width δ j*z.re*Real.exp (-2*width δ j*z.re)) := by
    have hd : 0 ≤ width δ j := by unfold width; positivity
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg hd,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    norm_num
    calc
      _ ≤ (2*width δ j)*(K*z.re)*Real.exp (-2*width δ j*z.re) := by
        simpa only [neg_mul] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*width δ j by positivity))
          (Real.exp_pos (-2*width δ j*z.re)).le
      _ = _ := by ring
  have hs : ‖∑ j ∈ Finset.range N,
      ((-2*width δ j:ℝ)*w)*Complex.exp ((-2*width δ j:ℝ)*z)‖ ≤ 2*K := by
    calc
      _ ≤ ∑ j ∈ Finset.range N,
          ‖((-2*width δ j:ℝ)*w)*Complex.exp ((-2*width δ j:ℝ)*z)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N,
          2*K*(width δ j*z.re*Real.exp (-2*width δ j*z.re)) :=
        Finset.sum_le_sum (fun j _ => hj j)
      _ = 2*K*∑ j ∈ Finset.range N,
          width δ j*z.re*Real.exp (-2*width δ j*z.re) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2*K := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (dyadic_sum_bound δ z.re hδ hz N)
          (by positivity : 0 ≤ 2*K)
  rw [slope,norm_mul,norm_inv,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

#print axioms width_pos
#print axioms weighted_exp_difference
#print axioms dyadic_sum_telescopes
#print axioms dyadic_sum_bound
#print axioms average_derivative
#print axioms slope_bound

end
end UnifiedTheory.Audit.KFCausalDyadicHeatCancellation
