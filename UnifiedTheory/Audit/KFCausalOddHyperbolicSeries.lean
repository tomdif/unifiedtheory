/- Odd hyperbolic partial fractions from the established cotangent expansion. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOddHyperbolicSeries
noncomputable section
open Filter Set
open scoped Topology BigOperators

private theorem pi_complex_ne : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

theorem rotated_integerComplement (w : ℂ) (hw : |w.im| < Real.pi) (hw0 : w ≠ 0) :
    w*Complex.I/(Real.pi:ℂ) ∈ Complex.integerComplement := by
  rintro ⟨k,hk⟩
  have he : w*Complex.I = (k:ℂ)*(Real.pi:ℂ) := ((eq_div_iff pi_complex_ne).mp hk).symm
  have hwk : w = -(k:ℂ)*(Real.pi:ℂ)*Complex.I := by
    calc
      w = -(w*Complex.I)*Complex.I := by rw [neg_mul,mul_assoc,Complex.I_mul_I]; ring
      _ = _ := by rw [he]; ring
  have hr := congrArg Complex.im hwk
  norm_num [Complex.mul_re,Complex.mul_im] at hr
  have hb : |(k:ℝ)| *Real.pi < Real.pi := by
    simpa only [hr,abs_neg,abs_mul,abs_of_pos Real.pi_pos] using hw
  have hkabs : |(k:ℝ)| < 1 := by nlinarith [Real.pi_pos]
  have hklo : (-1:ℤ) < k := by exact_mod_cast (abs_lt.mp hkabs).1
  have hkhi : k < (1:ℤ) := by exact_mod_cast (abs_lt.mp hkabs).2
  have hk0 : k = 0 := by omega
  subst k
  exact hw0 (by simpa using hwk)

theorem sinh_ne_zero (w : ℂ) (hw : |w.im| < Real.pi) (hw0 : w ≠ 0) :
    Complex.sinh w ≠ 0 := by
  have hs := sin_pi_mul_ne_zero (rotated_integerComplement w hw hw0)
  intro h
  apply hs
  rw [show (Real.pi:ℂ)*(w*Complex.I/(Real.pi:ℂ)) = w*Complex.I by field_simp,
    Complex.sin_mul_I,h,zero_mul]

def cothTerm (w : ℂ) (n : ℕ) : ℂ :=
  2*w/(((n:ℂ)+1)^2*(Real.pi:ℂ)^2+w^2)

def cothPartial (w : ℂ) (N : ℕ) : ℂ := 1/w+∑ n ∈ Finset.range N, cothTerm w n

private theorem cotTerm_scaled (w : ℂ) (hw : |w.im| < Real.pi) (hw0 : w ≠ 0) (n : ℕ) :
    (Complex.I/(Real.pi:ℂ))*cotTerm (w*Complex.I/(Real.pi:ℂ)) n = cothTerm w n := by
  let x := w*Complex.I/(Real.pi:ℂ)
  have hx := rotated_integerComplement w hw hw0
  have hp : x+((n:ℂ)+1) ≠ 0 := by
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using
      Complex.integerComplement_add_ne_zero hx ((n:ℤ)+1)
  have hm : x-((n:ℂ)+1) ≠ 0 := by
    simpa only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,sub_eq_add_neg] using
      Complex.integerComplement_add_ne_zero hx (-((n:ℤ)+1))
  have hd : ((n:ℂ)+1)^2*(Real.pi:ℂ)^2+w^2 ≠ 0 := by
    have he : ((n:ℂ)+1)^2*(Real.pi:ℂ)^2+w^2 =
        -(Real.pi:ℂ)^2*(x+((n:ℂ)+1))*(x-((n:ℂ)+1)) := by
      dsimp [x]
      field_simp
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ pi_complex_ne)) hp) hm
  change (Complex.I/(Real.pi:ℂ))*(1/(x-((n:ℂ)+1))+1/(x+((n:ℂ)+1))) = _
  rw [div_add_div _ _ hm hp,← mul_div_assoc]
  unfold cothTerm
  apply (div_eq_div_iff (mul_ne_zero hm hp) hd).mpr
  dsimp [x]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem cot_scaled (w : ℂ) (hw : |w.im| < Real.pi) (hw0 : w ≠ 0) :
    (Complex.I/(Real.pi:ℂ))*((Real.pi:ℂ)*Complex.cot
      ((Real.pi:ℂ)*(w*Complex.I/(Real.pi:ℂ)))-1/(w*Complex.I/(Real.pi:ℂ)))+1/w =
      Complex.cosh w/Complex.sinh w := by
  rw [show (Real.pi:ℂ)*(w*Complex.I/(Real.pi:ℂ)) = w*Complex.I by field_simp,
    Complex.cot,Complex.cos_mul_I,Complex.sin_mul_I]
  field_simp [hw0,sinh_ne_zero w hw hw0]
  ring

theorem cothPartial_tendsto (w : ℂ) (hw : |w.im| < Real.pi) (hw0 : w ≠ 0) :
    Tendsto (cothPartial w) atTop (𝓝 (Complex.cosh w/Complex.sinh w)) := by
  have h := ((tendsto_logDeriv_euler_cot_sub (rotated_integerComplement w hw hw0)).const_mul
    (Complex.I/(Real.pi:ℂ))).add_const (1/w)
  rw [cot_scaled w hw hw0] at h
  convert h using 1
  funext N
  unfold cothPartial
  rw [Finset.mul_sum]
  simp only [cotTerm_scaled w hw hw0]
  ring

def oddPartial (w : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, 8*w/((2*(n:ℂ)+1)^2*(Real.pi:ℂ)^2+4*w^2)

private theorem cothPartial_succ (w : ℂ) (N : ℕ) :
    cothPartial w (N+1) = cothPartial w N+cothTerm w N := by
  simp only [cothPartial,Finset.sum_range_succ]
  ring

private theorem cothTerm_even (w : ℂ) (N : ℕ) :
    2*cothTerm (2*w) (2*N+1) = cothTerm w N := by
  unfold cothTerm
  push_cast
  rw [show ((2*(N:ℂ)+1)+1)^2*(Real.pi:ℂ)^2+(2*w)^2 =
    4*(((N:ℂ)+1)^2*(Real.pi:ℂ)^2+w^2) by ring,div_mul_eq_div_div]
  ring

private theorem cothTerm_odd (w : ℂ) (N : ℕ) :
    2*cothTerm (2*w) (2*N) = 8*w/((2*(N:ℂ)+1)^2*(Real.pi:ℂ)^2+4*w^2) := by
  unfold cothTerm
  push_cast
  rw [show (2*w)^2 = 4*w^2 by ring]
  ring

theorem oddPartial_identity (w : ℂ) (hw0 : w ≠ 0) (N : ℕ) :
    oddPartial w N = 2*cothPartial (2*w) (2*N)-cothPartial w N := by
  induction N with
  | zero => simp [oddPartial,cothPartial]; field_simp; ring
  | succ N ih =>
    rw [show 2*(N+1) = (2*N+1)+1 by omega,cothPartial_succ,cothPartial_succ,cothPartial_succ]
    have he := cothTerm_even w N
    have ho := cothTerm_odd w N
    have ht : oddPartial w (N+1) = oddPartial w N+
        8*w/((2*(N:ℂ)+1)^2*(Real.pi:ℂ)^2+4*w^2) := by
      exact Finset.sum_range_succ _ _
    rw [ht,ih]
    linear_combination -he-ho

private theorem coth_double_sub (w : ℂ) (hw : |w.im| < Real.pi/2) (hw0 : w ≠ 0) :
    2*(Complex.cosh (2*w)/Complex.sinh (2*w))-Complex.cosh w/Complex.sinh w =
      Complex.tanh w := by
  have hw2 : |(2*w).im| < Real.pi := by
    norm_num [Complex.mul_im,abs_mul]
    linarith
  have hw20 : 2*w ≠ 0 := mul_ne_zero (by norm_num) hw0
  have hs := sinh_ne_zero w (by linarith [Real.pi_pos]) hw0
  have hs2 := sinh_ne_zero (2*w) hw2 hw20
  have hc : Complex.cosh w ≠ 0 := by
    intro h
    apply hs2
    rw [Complex.sinh_two_mul,h,mul_zero]
  rw [Complex.cosh_two_mul,Complex.sinh_two_mul,Complex.tanh_eq_sinh_div_cosh]
  field_simp [hs,hc]
  ring

theorem oddPartial_tendsto (w : ℂ) (hw : |w.im| < Real.pi/2) :
    Tendsto (oddPartial w) atTop (𝓝 (Complex.tanh w)) := by
  by_cases hw0 : w = 0
  · subst w
    have he : oddPartial 0 = fun _ => (0:ℂ) := by funext N; simp [oddPartial]
    rw [he]
    simp
  · have hw2 : |(2*w).im| < Real.pi := by
      norm_num [Complex.mul_im,abs_mul]
      linarith
    have hco : Tendsto (fun N : ℕ => 2*N) atTop atTop := by
      apply tendsto_atTop.mpr
      intro M
      exact eventually_atTop.mpr ⟨M,fun N hN => by omega⟩
    have h := (((cothPartial_tendsto (2*w) hw2 (mul_ne_zero (by norm_num) hw0)).comp hco).const_mul 2).sub (cothPartial_tendsto w (by linarith [Real.pi_pos]) hw0)
    rw [coth_double_sub w hw hw0] at h
    change Tendsto (fun N => 2*cothPartial (2*w) (2*N)-cothPartial w N) atTop _ at h
    simpa only [← oddPartial_identity w hw0] using h

#print axioms rotated_integerComplement
#print axioms sinh_ne_zero
#print axioms cothPartial_tendsto
#print axioms oddPartial_identity
#print axioms oddPartial_tendsto
end
end UnifiedTheory.Audit.KFCausalOddHyperbolicSeries
