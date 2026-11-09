/- Uniform physical field bounds on the sheared complex Gaussian. The
real inverse clock and the real part of its complex continuation stay a
bounded distance apart on the fixed strip. This controls every continuous
linear transverse field by the positive real Gaussian quadratic. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
import UnifiedTheory.Audit.KFCausalClockFloorFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFieldBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow

theorem inverse_real_distance (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    |(complexInverse ε q).re-(chartIso ε hε).symm q.re| ≤ Real.pi/3 := by
  have hr : (q.re:ℂ) ∈ targetStrip ε := by
    change |(q.re:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have hb := complexInverse_norm_bound ε hε q (q.re:ℂ) (third_strip_subset ε hε q hq) hr
  have hi := Complex.abs_re_le_norm (complexInverse ε q-complexInverse ε (q.re:ℂ))
  rw [Complex.sub_re,complexInverse_real ε hε,Complex.ofReal_re] at hi
  have he : q-(q.re:ℂ) = (q.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hb
  rw [complexInverse_real ε hε] at hb
  exact (hi.trans hb).trans ((div_le_iff₀ hε).mpr (by nlinarith))

theorem inverse_real_exp_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    Real.exp ((chartIso ε hε).symm q.re) ≤ Real.exp (Real.pi/3)*Real.exp (complexInverse ε q).re := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := (abs_le.mp (inverse_real_distance ε hε q hq)).1
  linarith

theorem complexScale_re_square_bound (z : ℂ) : (complexScale z).re^2 ≤ Real.exp z.re := by
  have hb := (sq_le_sq₀ (abs_nonneg (complexScale z).re) (norm_nonneg (complexScale z))).mpr
    (Complex.abs_re_le_norm (complexScale z))
  simpa only [sq_abs,complexScale_norm_square] using hb

def flowBound : ℝ := 32*(Real.exp (Real.pi/3)+1)
def momentBound (α β : ℝ) : ℝ := 2/β+4*flowBound/α

theorem flowBound_positive : 0 < flowBound := by unfold flowBound; positivity

theorem momentBound_positive (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < momentBound α β := by
  unfold momentBound
  have := flowBound_positive
  positivity

theorem flow_norm_square_bound (s : ℝ) (z : ℂ)
    (he : Real.exp s ≤ Real.exp (Real.pi/3)*Real.exp z.re) (x : Charged) (r : ℝ) :
    ‖flow s ![x 0,x 1,x 2,x 3,r]‖^2 ≤
      2*(r+shift z x)^2+flowBound*Real.exp z.re*squared x := by
  have hs := squared_nonnegative x
  have hm := mix_square_bound x
  have hb := complexScale_re_square_bound z
  have hscale : (scale s)^2 = Real.exp s := by
    rw [scale,← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hd : (scale s-(complexScale z).re)^2 ≤ 2*(Real.exp s+Real.exp z.re) := by
    nlinarith [sq_nonneg (scale s+(complexScale z).re)]
  have hdm := mul_le_mul hd hm (sq_nonneg (mix x)) (by positivity)
  have hu : (r+2*(scale s-1)*mix x)^2 ≤
      2*(r+shift z x)^2+32*(Real.exp s+Real.exp z.re)*squared x := by
    unfold shift
    nlinarith [sq_nonneg ((r+2*((complexScale z).re-1)*mix x)-2*(scale s-(complexScale z).re)*mix x)]
  have ht : 32*(Real.exp s+Real.exp z.re)*squared x ≤ flowBound*Real.exp z.re*squared x := by
    apply mul_le_mul_of_nonneg_right _ hs
    unfold flowBound
    nlinarith
  have hcoord (i : Fin 4) : (x i)^2 ≤ squared x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hc (i : Fin 4) : (scale s*x i)^2 ≤
      2*(r+shift z x)^2+flowBound*Real.exp z.re*squared x := by
    have h := mul_le_mul_of_nonneg_left (hcoord i) (Real.exp_pos s).le
    rw [mul_pow,hscale]
    have hx : Real.exp s*squared x ≤ 32*(Real.exp s+Real.exp z.re)*squared x := by
      have hh : Real.exp s ≤ 32*(Real.exp s+Real.exp z.re) := by
        nlinarith [Real.exp_pos s,Real.exp_pos z.re]
      exact mul_le_mul_of_nonneg_right hh hs
    linarith [sq_nonneg (r+shift z x)]
  have hall (i : Fin 5) : (flow s ![x 0,x 1,x 2,x 3,r] i)^2 ≤
      2*(r+shift z x)^2+flowBound*Real.exp z.re*squared x := by
    fin_cases i
    · simpa only [flow,Fin.reduceEq,ite_false,Matrix.cons_val_zero] using hc 0
    · simpa only [flow,Fin.reduceEq,ite_false,Matrix.cons_val_succ,Matrix.cons_val_zero] using hc 1
    · simpa only [flow,Fin.reduceEq,ite_false,Matrix.cons_val_succ,Matrix.cons_val_zero] using hc 2
    · simpa only [flow,Fin.reduceEq,ite_false,Matrix.cons_val_succ,Matrix.cons_val_zero] using hc 3
    · simpa only [flow,Fin.reduceEq,ite_true,Matrix.cons_val_succ,Matrix.cons_val_zero,mix] using
        (show (r+2*(scale s-1)*mix x)^2 ≤ 2*(r+shift z x)^2+flowBound*Real.exp z.re*squared x from by linarith)
  have hpos : 0 ≤ 2*(r+shift z x)^2+flowBound*Real.exp z.re*squared x := by
    have := flowBound_positive
    positivity
  have hn : ‖flow s ![x 0,x 1,x 2,x 3,r]‖ ≤
      Real.sqrt (2*(r+shift z x)^2+flowBound*Real.exp z.re*squared x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (hall i)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn
  simpa only [Real.sq_sqrt hpos] using hsq

theorem flow_quadratic_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3)
    (he : Real.exp s ≤ Real.exp (Real.pi/3)*Real.exp z.re) (x : Charged) (r : ℝ) :
    ‖flow s ![x 0,x 1,x 2,x 3,r]‖^2 ≤ momentBound α β*(quadratic α β z x r).re := by
  have hm := momentBound_positive α β hα hβ
  have hc := flowBound_positive
  have hs := squared_nonnegative x
  have hαb : flowBound ≤ momentBound α β*(α/4) := by
    have hid : momentBound α β*(α/4) = α/(2*β)+flowBound := by
      unfold momentBound
      field_simp
      ring
    rw [hid]
    exact le_add_of_nonneg_left (by positivity)
  have hβb : 2 ≤ momentBound α β*β := by
    have hid : momentBound α β*β = 2+4*flowBound*β/α := by
      unfold momentBound
      field_simp
    rw [hid]
    exact le_add_of_nonneg_right (by positivity)
  have hl := mul_le_mul_of_nonneg_left (quadratic_re_lower α β hα.le hβ.le hw z hz x r) hm.le
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hαb (Real.exp_pos z.re).le) hs
  have h2 := mul_le_mul_of_nonneg_right hβb (sq_nonneg (r+shift z x))
  have hf := flow_norm_square_bound s z he x r
  nlinarith

theorem field_quadratic_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3)
    (he : Real.exp s ≤ Real.exp (Real.pi/3)*Real.exp z.re) (x : Charged) (r : ℝ)
    (l : Transverse →L[ℝ] ℝ) :
    (l (flow s ![x 0,x 1,x 2,x 3,r]))^2 ≤
      (‖l‖^2*momentBound α β)*(quadratic α β z x r).re := by
  have hl := pow_le_pow_left₀ (norm_nonneg _) (l.le_opNorm (flow s ![x 0,x 1,x 2,x 3,r])) 2
  simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hl
  have hb := mul_le_mul_of_nonneg_left (flow_quadratic_bound α β hα hβ hw s z hz he x r) (sq_nonneg ‖l‖)
  exact hl.trans (by simpa only [mul_assoc] using hb)

#print axioms inverse_real_distance
#print axioms inverse_real_exp_bound
#print axioms complexScale_re_square_bound
#print axioms flowBound_positive
#print axioms momentBound_positive
#print axioms flow_norm_square_bound
#print axioms flow_quadratic_bound
#print axioms field_quadratic_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorFieldBounds
