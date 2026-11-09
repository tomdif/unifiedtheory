/- Exponential Fourier decay implies the actual exponential momentum
square-integrability condition, with an explicit width margin. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalExponentialFourierDomain
noncomputable section
open MeasureTheory Set

theorem integrable_exp_neg_abs (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c*|x|)) := by
  have hl : IntegrableOn (fun x : ℝ => Real.exp (-c*|x|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro x hx
    change x ≤ 0 at hx
    dsimp only
    rw [abs_of_nonpos hx]
    congr 1
    ring
  have hr : IntegrableOn (fun x : ℝ => Real.exp (-c*|x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    dsimp only
    rw [abs_of_pos hx]
  simpa only [Iic_union_Ioi,integrableOn_univ] using hl.union hr

theorem weighted_square_bound (F : ℝ → ℂ) (d M hbar : ℝ) (hM : 0 ≤ M)
    (hb : ∀ k, ‖F k‖ ≤ Real.exp (-2*Real.pi*d*|k|)*M) (k : ℝ) :
    Real.exp (2*Real.pi*hbar*k)*‖F k‖^2 ≤
      M^2*Real.exp (-(2*Real.pi*(2*d-|hbar|))*|k|) := by
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hM)).mpr (hb k)
  have he : (Real.exp (-2*Real.pi*d*|k|))^2 = Real.exp (-4*Real.pi*d*|k|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [mul_pow,he] at hs
  have hk : hbar*k ≤ |hbar| *|k| := by simpa only [abs_mul] using le_abs_self (hbar*k)
  calc
    _ ≤ Real.exp (2*Real.pi*hbar*k)*(Real.exp (-4*Real.pi*d*|k|)*M^2) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = M^2*Real.exp (2*Real.pi*hbar*k+(-4*Real.pi*d*|k|)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]

theorem weighted_square_integrable (F : ℝ → ℂ) (hF : Continuous F)
    (d M hbar : ℝ) (hM : 0 ≤ M) (hh : |hbar| < 2*d)
    (hb : ∀ k, ‖F k‖ ≤ Real.exp (-2*Real.pi*d*|k|)*M) :
    Integrable (fun k => Real.exp (2*Real.pi*hbar*k)*‖F k‖^2) := by
  have hm : 0 < 2*d-|hbar| := sub_pos.mpr hh
  have hc : 0 < 2*Real.pi*(2*d-|hbar|) := by positivity
  have hi := (integrable_exp_neg_abs _ hc).const_mul (M^2)
  apply hi.mono' (show Continuous (fun k => Real.exp (2*Real.pi*hbar*k)*‖F k‖^2) by
    fun_prop).aestronglyMeasurable
  filter_upwards [] with k
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact weighted_square_bound F d M hbar hM hb k

#print axioms integrable_exp_neg_abs
#print axioms weighted_square_bound
#print axioms weighted_square_integrable

end
end UnifiedTheory.Audit.KFCausalExponentialFourierDomain
