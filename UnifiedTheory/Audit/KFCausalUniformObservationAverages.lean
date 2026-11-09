/- Uniform Hilbert-space comparison transfers averages of bounded
squared-norm observations on a fixed normalized time interval. -/
import UnifiedTheory.Audit.KFCausalMassObservableDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalUniformObservationAverages
noncomputable section
open Filter MeasureTheory
open scoped Topology
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem square_difference (A : H →L[ℂ] K) (x y : H) :
    |‖A x‖^2-‖A y‖^2| ≤ ‖A‖^2*(‖x‖+‖y‖)*‖x-y‖ := by
  have hb := KFCausalMassObservableDerivative.quadratic_difference_bound
    (ContinuousLinearMap.id ℂ K) (fun _ => le_rfl) (A x) (A y)
  simp only [ContinuousLinearMap.id_apply,inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re] at hb
  have hd : ‖A x-A y‖ ≤ ‖A‖*‖x-y‖ := by rw [← map_sub]; exact A.le_opNorm _
  exact hb.trans ((mul_le_mul (add_le_add (A.le_opNorm x) (A.le_opNorm y)) hd
    (norm_nonneg _) (by positivity)).trans_eq (by ring))

theorem integral_error_bound (A : H →L[ℂ] K) (x y : ℝ → H) (M δ : ℝ)
    (hM : 0 ≤ M)
    (hx : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖x r‖ ≤ M)
    (hy : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖y r‖ ≤ M)
    (hd : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖x r-y r‖ ≤ δ) :
    ‖∫ r in (0:ℝ)..1, (‖A (x r)‖^2-‖A (y r)‖^2)‖ ≤ (2*‖A‖^2*M)*δ := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := (2*‖A‖^2*M)*δ) (f := fun r => ‖A (x r)‖^2-‖A (y r)‖^2)
    (fun r hr => by
      rw [Set.uIoc_of_le zero_le_one] at hr
      have ht : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2⟩
      rw [Real.norm_eq_abs]
      exact (square_difference A (x r) (y r)).trans
        ((mul_le_mul
          (mul_le_mul_of_nonneg_left (add_le_add (hx r ht) (hy r ht)) (sq_nonneg ‖A‖))
          (hd r ht) (norm_nonneg _) (by positivity)).trans_eq (by ring)))
  simpa only [sub_zero,abs_one,mul_one] using hi

theorem average_difference_limit (A : H →L[ℂ] K) (x y : ℕ → ℝ → H) (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ n r, r ∈ Set.Icc (0:ℝ) 1 → ‖x n r‖ ≤ M)
    (hy : ∀ n r, r ∈ Set.Icc (0:ℝ) 1 → ‖y n r‖ ≤ M)
    (hix : ∀ n, IntervalIntegrable (fun r => ‖A (x n r)‖^2) volume 0 1)
    (hiy : ∀ n, IntervalIntegrable (fun r => ‖A (y n r)‖^2) volume 0 1)
    (herr : TendstoUniformlyOn (fun n r => x n r-y n r) (fun _ => 0) atTop (Set.Icc 0 1)) :
    Tendsto (fun n => (∫ r in (0:ℝ)..1, ‖A (x n r)‖^2)-
      (∫ r in (0:ℝ)..1, ‖A (y n r)‖^2)) atTop (𝓝 0) := by
  let C := 2*‖A‖^2*M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [Metric.tendstoUniformlyOn_iff] at herr
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [herr (η/(C+1)) (by positivity)] with n hn
  rw [dist_zero_right,← intervalIntegral.integral_sub (hix n) (hiy n)]
  have hb := integral_error_bound A (x n) (y n) M (η/(C+1)) hM
    (hx n) (hy n) (fun r hr => by
      have he := hn r hr
      rw [dist_zero_left] at he
      exact he.le)
  apply hb.trans_lt
  change C*(η/(C+1)) < η
  rw [← mul_div_assoc,div_lt_iff₀ (by positivity : 0 < C+1)]
  nlinarith only [hη]

#print axioms square_difference
#print axioms integral_error_bound
#print axioms average_difference_limit
end
end UnifiedTheory.Audit.KFCausalUniformObservationAverages
