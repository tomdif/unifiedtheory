/- Algebraic barrier for the actual linear-field circle moment determinant.
The Riccati boundary derivative is strictly positive at every positive
zero. The analytic circle ODE and its global barrier attachment are not
assumed or concluded by this algebraic supplier. -/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalAngularMassDeterminant
noncomputable section

def determinant (x y : ℝ) : ℝ := (4*x+3)*y^2+(4*x+8)*y-4*x^2

def threshold (y : ℝ) : ℝ := y*(y+24)/(2*(y+4))

def quartic (y : ℝ) : ℝ := y^4+30*y^3+116*y^2-136*y+64

def riccati (x y : ℝ) : ℝ := (x-y^2)/(2*x)

def transport (x y : ℝ) : ℝ :=
  4*y^2+4*y-8*x+((8*x+6)*y+4*x+8)*riccati x y

theorem quartic_positive (y : ℝ) (hy : 0 ≤ y) : 0 < quartic y := by
  have he : quartic y = y^4+30*y^3+116*(y-17/29)^2+700/29 := by
    unfold quartic
    ring
  rw [he]
  positivity

theorem threshold_positive (y : ℝ) (hy : 0 < y) : 0 < threshold y := by
  unfold threshold
  positivity

theorem threshold_evaluation (y : ℝ) (hy : 0 ≤ y) :
    determinant (threshold y) y = 2*y*quartic y/(y+4)^2 := by
  have hn : y+4 ≠ 0 := by positivity
  unfold determinant threshold quartic
  field_simp
  ring

theorem threshold_determinant_positive (y : ℝ) (hy : 0 < y) :
    0 < determinant (threshold y) y := by
  rw [threshold_evaluation y hy.le]
  exact div_pos (mul_pos (by positivity) (quartic_positive y hy.le)) (by positivity)

theorem root_lower (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : determinant x y = 0) : y^2+y < x := by
  have he : 4*x*(x-y^2-y) = 3*y^2+8*y := by
    unfold determinant at hp
    nlinarith only [hp]
  have hh : 0 < 4*x*(x-y^2-y) := by rw [he]; positivity
  have := (mul_pos_iff_of_pos_left (show 0 < 4*x by positivity)).mp hh
  linarith

theorem root_above_threshold (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : determinant x y = 0) : threshold y < x := by
  have hr := root_lower x y hx hy hp
  have hd := threshold_determinant_positive y hy
  by_contra hn
  have hle : x ≤ threshold y := le_of_not_gt hn
  have hs : 0 ≤ threshold y-x := sub_nonneg.mpr hle
  have hn' : 0 < threshold y+x-y^2-y := by linarith
  have hprod := mul_nonneg hs hn'.le
  have he : determinant (threshold y) y-determinant x y =
      -4*(threshold y-x)*(threshold y+x-y^2-y) := by
    unfold determinant
    ring
  rw [hp,sub_zero] at he
  nlinarith only [he,hd,hprod]

theorem transport_identity (x y : ℝ) (hx : x ≠ 0) :
    2*x*transport x y =
      (2*x*(y+4)-y^2-24*y)+(3-2*y)*determinant x y := by
  unfold transport riccati determinant
  field_simp
  ring

theorem transport_positive_at_zero (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : determinant x y = 0) : 0 < transport x y := by
  have ht := root_above_threshold x y hx hy hp
  have hb : 0 < 2*x*(y+4)-y^2-24*y := by
    unfold threshold at ht
    have hm := (div_lt_iff₀ (show 0 < 2*(y+4) by positivity)).mp ht
    nlinarith only [hm]
  have he := transport_identity x y hx.ne'
  rw [hp,mul_zero,add_zero] at he
  have hm : 0 < 2*x*transport x y := he ▸ hb
  exact (mul_pos_iff_of_pos_left (show 0 < 2*x by positivity)).mp hm

theorem determinant_hasDerivAt {f : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f (riccati x (f x)) x) :
    HasDerivAt (fun t => determinant t (f t)) (transport x (f x)) x := by
  have hd := (((((hasDerivAt_id x).const_mul 4).add_const 3).mul (hf.pow 2)).add
    ((((hasDerivAt_id x).const_mul 4).add_const 8).mul hf)).sub
      (((hasDerivAt_id x).pow 2).const_mul 4)
  convert hd using 1
  norm_num [transport,Pi.pow_apply]
  ring

theorem derivative_positive_at_zero {f : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hy : 0 < f x) (hp : determinant x (f x) = 0)
    (hf : HasDerivAt f (riccati x (f x)) x) :
    0 < deriv (fun t => determinant t (f t)) x := by
  rw [(determinant_hasDerivAt hf).deriv]
  exact transport_positive_at_zero x (f x) hx hy hp

#print axioms quartic_positive
#print axioms threshold_positive
#print axioms threshold_evaluation
#print axioms threshold_determinant_positive
#print axioms root_lower
#print axioms root_above_threshold
#print axioms transport_identity
#print axioms transport_positive_at_zero
#print axioms determinant_hasDerivAt
#print axioms derivative_positive_at_zero
end
end UnifiedTheory.Audit.KFCausalAngularMassDeterminant
