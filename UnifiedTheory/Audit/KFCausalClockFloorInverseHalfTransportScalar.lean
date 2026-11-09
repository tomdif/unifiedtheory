/- Uniform differentiation of C^(-1/2) under the actual longitudinal
transport. This supplies a bounded multiplier commutator on the maximal
momentum domain; transport time is not Hamiltonian evolution time. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

def value (ε s : ℝ) : ℝ := (Real.sqrt (clock ε s))⁻¹
def drift (ε r : ℝ) : ℝ := -r^3/2+ε*r^5/2
def bound (ε : ℝ) : ℝ := (Real.sqrt ε)⁻¹
def speedBound (ε : ℝ) : ℝ := ((bound ε)^3+ε*(bound ε)^5)/2
def slopeBound (ε : ℝ) : ℝ := (3*(bound ε)^2+5*ε*(bound ε)^4)/2
def transported (ε : ℝ) (hε : 0 < ε) (s t : ℝ) : ℝ := value ε (logFlow ε hε s t)

theorem value_bounds (ε s : ℝ) (hε : 0 < ε) : 0 < value ε s ∧ value ε s ≤ bound ε := by
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr (clock_positive ε s hε.le)),?_⟩
  apply inv_anti₀ (Real.sqrt_pos.mpr hε)
  apply Real.sqrt_le_sqrt
  unfold clock
  linarith [Real.exp_pos s]

theorem drift_identity (ε s : ℝ) (hε : 0 < ε) :
    drift ε (value ε s) = -(1/(2*ε))*defect ε s*response ε s*value ε s := by
  have hc := clock_positive ε s hε.le
  have hs := Real.sq_sqrt hc.le
  have hr := (Real.sqrt_pos.mpr hc).ne'
  unfold drift value defect response
  field_simp
  rw [show Real.exp s = clock ε s-ε by unfold clock; ring]
  have h4 : Real.sqrt (clock ε s)^4 = (clock ε s)^2 := by
    rw [show Real.sqrt (clock ε s)^4 = (Real.sqrt (clock ε s)^2)^2 by ring,hs]
  rw [hs,h4]
  ring

theorem transported_initial (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    transported ε hε s 0 = value ε s := by rw [transported,logFlow_initial]

theorem transported_derivative (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    HasDerivAt (transported ε hε s) (drift ε (transported ε hε s t)) t := by
  have hc := clock_positive ε (logFlow ε hε s t) hε.le
  have hr := (Real.sqrt_pos.mpr hc).ne'
  have hs := Real.sq_sqrt hc.le
  have hd := ((positive_clock_transport_derivative ε hε s t).sqrt hc.ne').inv hr
  change HasDerivAt (transported ε hε s) _ t at hd
  convert hd using 1
  rw [transported,drift_identity ε _ hε]
  unfold value defect
  field_simp
  rw [hs]
  ring

theorem drift_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 ≤ r ∧ r ≤ bound ε) :
    |drift ε r| ≤ speedBound ε := by
  have h3 := pow_le_pow_left₀ hr.1 hr.2 3
  have h5 := pow_le_pow_left₀ hr.1 hr.2 5
  calc
    _ ≤ |(-r^3/2)|+|ε*r^5/2| := abs_add_le _ _
    _ = (r^3+ε*r^5)/2 := by
      rw [abs_div,abs_neg,abs_pow,abs_of_nonneg hr.1,abs_div,abs_mul,
        abs_of_pos hε,abs_pow,abs_of_nonneg hr.1]
      norm_num
      ring
    _ ≤ speedBound ε := by unfold speedBound; nlinarith [mul_le_mul_of_nonneg_left h5 hε.le]

theorem drift_difference (ε r q : ℝ) (hε : 0 < ε)
    (hr : 0 ≤ r ∧ r ≤ bound ε) (hq : 0 ≤ q ∧ q ≤ bound ε) :
    |drift ε r-drift ε q| ≤ slopeBound ε*|r-q| := by
  have hd (x : ℝ) : HasDerivAt (drift ε) (-3*x^2/2+5*ε*x^4/2) x := by
    convert (((hasDerivAt_id x).pow 3).neg.div_const 2).add
      ((((hasDerivAt_id x).pow 5).const_mul ε).div_const 2) using 1
    simp only [id_eq]
    ring
  have hb (x : ℝ) (hx : x ∈ Icc 0 (bound ε)) : ‖-3*x^2/2+5*ε*x^4/2‖ ≤ slopeBound ε := by
    have h2 := pow_le_pow_left₀ hx.1 hx.2 2
    have h4 := pow_le_pow_left₀ hx.1 hx.2 4
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |(-3*x^2/2)|+|5*ε*x^4/2| := abs_add_le _ _
      _ = (3*x^2+5*ε*x^4)/2 := by
        rw [abs_div,abs_mul,abs_pow,abs_of_nonneg hx.1,abs_div,abs_mul,abs_mul,
          abs_of_pos hε,abs_pow,abs_of_nonneg hx.1]
        norm_num
        ring
      _ ≤ slopeBound ε := by unfold slopeBound; nlinarith [mul_le_mul_of_nonneg_left h4 hε.le]
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) (bound ε)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hd x).hasDerivWithinAt) hb hq hr

theorem transported_difference (ε : ℝ) (hε : 0 < ε) (s t u : ℝ) :
    |transported ε hε s t-transported ε hε s u| ≤ speedBound ε*|t-u| := by
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (transported_derivative ε hε s x).hasDerivWithinAt)
      (fun x _ => show ‖drift ε (transported ε hε s x)‖ ≤ speedBound ε by
        exact (Real.norm_eq_abs _).trans_le (drift_bound ε _ hε
          ⟨(value_bounds ε _ hε).1.le,(value_bounds ε _ hε).2⟩)) (mem_univ u) (mem_univ t)

theorem transported_remainder (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    |transported ε hε s t-value ε s-t*drift ε (value ε s)| ≤
      (slopeBound ε*speedBound ε)*t^2 := by
  let f : ℝ → ℝ := fun r => transported ε hε s r-value ε s-r*drift ε (value ε s)
  have hd (r : ℝ) : HasDerivAt f (drift ε (transported ε hε s r)-drift ε (value ε s)) r := by
    simpa only [one_mul] using ((transported_derivative ε hε s r).sub_const (value ε s)).sub
      ((hasDerivAt_id r).mul_const (drift ε (value ε s)))
  have hS : 0 ≤ speedBound ε := by unfold speedBound bound; positivity
  have hL : 0 ≤ slopeBound ε := by unfold slopeBound bound; positivity
  have hb (r : ℝ) (hr : r ∈ uIcc 0 t) :
      ‖drift ε (transported ε hε s r)-drift ε (value ε s)‖ ≤ (slopeBound ε*speedBound ε)*|t| := by
    have hh := transported_difference ε hε s r 0
    rw [transported_initial,sub_zero] at hh
    have hrt : |r| ≤ |t| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
    rw [Real.norm_eq_abs]
    exact (drift_difference ε _ _ hε
      ⟨(value_bounds ε _ hε).1.le,(value_bounds ε _ hε).2⟩
      ⟨(value_bounds ε s hε).1.le,(value_bounds ε s hε).2⟩).trans
      ((mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left hrt hS)) hL).trans_eq (by ring))
  have he := (convex_uIcc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  simpa only [f,transported_initial,zero_mul,sub_self,sub_zero,Real.norm_eq_abs,
    mul_assoc,← pow_two,sq_abs] using he

#print axioms value_bounds
#print axioms drift_identity
#print axioms transported_initial
#print axioms transported_derivative
#print axioms drift_bound
#print axioms drift_difference
#print axioms transported_difference
#print axioms transported_remainder
end
end UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar
