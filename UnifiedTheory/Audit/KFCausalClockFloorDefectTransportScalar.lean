/- Uniform scalar differentiation of the actual clock defect along the
complete longitudinal transport. The quadratic remainder is uniform in
the starting configuration; it can therefore control L2 multiplication. -/
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

def drift (ε d : ℝ) : ℝ := -(d^2*(1-d))/ε
def transported (ε : ℝ) (hε : 0 < ε) (s t : ℝ) : ℝ := defect ε (logFlow ε hε s t)

theorem transported_initial (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    transported ε hε s 0 = defect ε s := by rw [transported,logFlow_initial]

theorem transported_bounds (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    0 ≤ transported ε hε s t ∧ transported ε hε s t ≤ 1 := by
  have hp := defect_positive ε (logFlow ε hε s t) hε
  have hr := (response_bounds ε (logFlow ε hε s t) hε).1
  have he := response_add_defect ε (logFlow ε hε s t) hε.le
  constructor
  · exact hp.le
  · change defect ε (logFlow ε hε s t) ≤ 1
    linarith

theorem transported_derivative (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    HasDerivAt (transported ε hε s) (drift ε (transported ε hε s t)) t := by
  have hd := ((positive_clock_transport_derivative ε hε s t).inv
    (clock_positive ε (logFlow ε hε s t) hε.le).ne').const_mul ε
  change HasDerivAt (transported ε hε s) _ t at hd
  convert hd using 1
  unfold drift transported defect response
  have hc := (clock_positive ε (logFlow ε hε s t) hε.le).ne'
  unfold clock at *
  field_simp
  ring

theorem drift_bound (ε d : ℝ) (hε : 0 < ε) (hd : 0 ≤ d ∧ d ≤ 1) :
    |drift ε d| ≤ 1/ε := by
  have hp : 0 ≤ d^2*(1-d) := mul_nonneg (sq_nonneg d) (by linarith)
  have hs : d^2 ≤ 1 := by nlinarith [sq_nonneg (1-d)]
  have hb : d^2*(1-d) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (show 1-d ≤ 1 by linarith) (sq_nonneg d)).trans (by simpa using hs)
  rw [drift,abs_div,abs_neg,abs_of_nonneg hp,abs_of_pos hε]
  exact div_le_div_of_nonneg_right hb hε.le

theorem drift_difference (ε d e : ℝ) (hε : 0 < ε)
    (hd : 0 ≤ d ∧ d ≤ 1) (he : 0 ≤ e ∧ e ≤ 1) :
    |drift ε d-drift ε e| ≤ (5/ε)*|d-e| := by
  have hde : 0 ≤ d*e := mul_nonneg hd.1 he.1
  have hde1 : d*e ≤ 1 := by nlinarith [mul_nonneg (show 0 ≤ 1-d by linarith) he.1]
  have hd2 : d^2 ≤ 1 := by nlinarith [sq_nonneg (1-d)]
  have he2 : e^2 ≤ 1 := by nlinarith [sq_nonneg (1-e)]
  have hb : |d^2+d*e+e^2-d-e| ≤ 5 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg d,sq_nonneg e]
  have hf : drift ε d-drift ε e = (d-e)*(d^2+d*e+e^2-d-e)/ε := by unfold drift; ring
  rw [hf,abs_div,abs_mul,abs_of_pos hε]
  calc
    _ ≤ (|d-e| * 5)/ε := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) hε.le
    _ = _ := by ring

theorem transported_difference (ε : ℝ) (hε : 0 < ε) (s t u : ℝ) :
    |transported ε hε s t-transported ε hε s u| ≤ (1/ε)*|t-u| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (transported_derivative ε hε s r).hasDerivWithinAt)
    (fun r _ => show ‖drift ε (transported ε hε s r)‖ ≤ 1/ε by
      simpa only [Real.norm_eq_abs] using drift_bound ε _ hε (transported_bounds ε hε s r))
    (Set.mem_univ u) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using h

theorem transported_remainder (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    |transported ε hε s t-defect ε s-t*drift ε (defect ε s)| ≤ (5/ε^2)*|t|^2 := by
  let f : ℝ → ℝ := fun r => transported ε hε s r-defect ε s-r*drift ε (defect ε s)
  have hd (r : ℝ) : HasDerivAt f (drift ε (transported ε hε s r)-drift ε (defect ε s)) r := by
    convert ((transported_derivative ε hε s r).sub_const (defect ε s)).sub
      ((hasDerivAt_id r).mul_const (drift ε (defect ε s))) using 1
    simp only [one_mul]
  have hb (r : ℝ) (hr : r ∈ Set.uIcc 0 t) :
      ‖drift ε (transported ε hε s r)-drift ε (defect ε s)‖ ≤ (5/ε^2)*|t| := by
    have h0 := transported_bounds ε hε s 0
    rw [transported_initial] at h0
    have hh := transported_difference ε hε s r 0
    rw [transported_initial,sub_zero] at hh
    have hrt : |r| ≤ |t| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (5/ε)*|transported ε hε s r-defect ε s| :=
        drift_difference ε _ _ hε (transported_bounds ε hε s r) h0
      _ ≤ (5/ε)*((1/ε)*|r|) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ (5/ε)*((1/ε)*|t|) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrt (by positivity)) (by positivity)
      _ = _ := by ring
  have h := (convex_uIcc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r).hasDerivWithinAt) hb (left_mem_uIcc) (right_mem_uIcc)
  simpa only [f,transported_initial,zero_mul,sub_self,sub_zero,Real.norm_eq_abs,pow_two,mul_assoc] using h

#print axioms transported_initial
#print axioms transported_bounds
#print axioms transported_derivative
#print axioms drift_bound
#print axioms drift_difference
#print axioms transported_difference
#print axioms transported_remainder

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar
