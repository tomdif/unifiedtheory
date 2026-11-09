/- The full complex transverse Gaussian for the optional clock-floor
flow, including the neutral matter shear. A small positive neutral width
controls the imaginary shear without changing the four equal charged
widths. No charge-domain or Hamiltonian statement is assumed here. -/
import UnifiedTheory.Audit.KFCausalClockInverseStripBounds
import UnifiedTheory.Audit.KFCausalClockFloorFlow
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShearBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow

abbrev Charged := Fin 4 → ℝ
abbrev Grouped := Charged × ℝ

def squared (x : Charged) : ℝ := ∑ i, (x i)^2
def mix (x : Charged) : ℝ := x 2 + x 3
def complexScale (z : ℂ) : ℂ := Complex.exp (z/2)
def shift (z : ℂ) (x : Charged) : ℝ := 2*((complexScale z).re-1)*mix x
def quadratic (α β : ℝ) (z : ℂ) (x : Charged) (r : ℝ) : ℂ :=
  (α:ℂ)*Complex.exp z*(squared x:ℂ) +
    (β:ℂ)*((r:ℂ)+2*(complexScale z-1)*(mix x:ℂ))^2
def packet (α β : ℝ) (z : ℂ) (x : Grouped) : ℂ :=
  Complex.exp (-quadratic α β z x.1 x.2)

theorem squared_nonnegative (x : Charged) : 0 ≤ squared x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem mix_square_bound (x : Charged) : (mix x)^2 ≤ 2*squared x := by
  simp only [mix,squared,Fin.sum_univ_succ]
  norm_num
  change (x 2+x 3)^2 ≤ 2*(x 0^2+(x 1^2+(x 2^2+x 3^2)))
  nlinarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2-x 3)]

theorem complexScale_square (z : ℂ) : (complexScale z)^2 = Complex.exp z := by
  rw [complexScale,← Complex.exp_nat_mul]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem complexScale_norm_square (z : ℂ) : ‖complexScale z‖^2 = Real.exp z.re := by
  rw [complexScale,Complex.norm_exp,← Real.exp_nat_mul]
  congr 1
  simp only [Complex.div_ofNat_re,Nat.cast_ofNat]
  ring

theorem complexScale_im_square_bound (z : ℂ) : (complexScale z).im^2 ≤ Real.exp z.re := by
  have hb := (sq_le_sq₀ (abs_nonneg (complexScale z).im) (norm_nonneg (complexScale z))).mpr
    (Complex.abs_im_le_norm (complexScale z))
  simpa only [sq_abs,complexScale_norm_square] using hb

theorem quadratic_re (α β : ℝ) (z : ℂ) (x : Charged) (r : ℝ) :
    (quadratic α β z x r).re = α*(Complex.exp z).re*squared x +
      β*((r+shift z x)^2-(2*(complexScale z).im*mix x)^2) := by
  simp [quadratic,shift,pow_two,Complex.mul_re,Complex.mul_im]

theorem quadratic_re_lower (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Charged) (r : ℝ) :
    (α/4)*Real.exp z.re*squared x + β*(r+shift z x)^2 ≤ (quadratic α β z x r).re := by
  have hs := squared_nonnegative x
  have hmix := mix_square_bound x
  have him := complexScale_im_square_bound z
  have he : Real.exp z.re/2 ≤ (Complex.exp z).re := by
    rw [Complex.exp_re]
    have hc := cos_lower_third z.im hz
    nlinarith [mul_le_mul_of_nonneg_left hc (Real.exp_pos z.re).le]
  have ha := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he hα) hs
  have hl : (2*(complexScale z).im*mix x)^2 ≤ 8*Real.exp z.re*squared x := by
    have hm := mul_le_mul him hmix (sq_nonneg (mix x)) (Real.exp_pos z.re).le
    nlinarith
  have hlβ := mul_le_mul_of_nonneg_left hl hβ
  have hw' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hw (Real.exp_pos z.re).le) hs
  rw [quadratic_re]
  nlinarith

theorem quadratic_re_nonnegative (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Charged) (r : ℝ) :
    0 ≤ (quadratic α β z x r).re := by
  apply le_trans _ (quadratic_re_lower α β hα hβ hw z hz x r)
  have hs := squared_nonnegative x
  positivity

theorem packet_continuous (α β : ℝ) (z : ℂ) : Continuous (packet α β z) := by
  unfold packet quadratic squared mix
  fun_prop

theorem packet_analytic (α β : ℝ) (x : Grouped) (z : ℂ) :
    AnalyticAt ℂ (fun z => packet α β z x) z := by
  unfold packet quadratic complexScale
  fun_prop

theorem packet_norm_square (α β : ℝ) (z : ℂ) (x : Grouped) :
    ‖packet α β z x‖^2 = Real.exp (-2*(quadratic α β z x.1 x.2).re) := by
  rw [packet,Complex.norm_exp,Complex.neg_re,← Real.exp_nat_mul]
  congr 1
  norm_num

theorem packet_norm_le_one (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) : ‖packet α β z x‖ ≤ 1 := by
  rw [packet,Complex.norm_exp,Complex.neg_re,Real.exp_le_one_iff]
  exact neg_nonpos.mpr (quadratic_re_nonnegative α β hα hβ hw z hz x.1 x.2)

def majorant (k b d : ℝ) (x : Grouped) : ℝ :=
  Real.exp (-k*squared x.1)*Real.exp (-b*(x.2+d*mix x.1)^2)

theorem packet_square_bound (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) :
    ‖packet α β z x‖^2 ≤ majorant ((α/2)*Real.exp z.re) (2*β)
      (2*((complexScale z).re-1)) x := by
  rw [packet_norm_square,majorant,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := quadratic_re_lower α β hα hβ hw z hz x.1 x.2
  dsimp [shift] at hl
  nlinarith

def physicalGaussian (α β : ℝ) (x : Transverse) : ℂ :=
  Complex.exp (-((α*∑ i : Fin 4, (x i.castSucc)^2 + β*(x 4)^2:ℝ):ℂ))

theorem packet_real_flow (α β s : ℝ) (x : Charged) (r : ℝ) :
    packet α β (s:ℂ) (x,r) = physicalGaussian α β (flow s ![x 0,x 1,x 2,x 3,r]) := by
  have hscale : complexScale (s:ℂ) = (scale s:ℂ) := by
    simp [complexScale,scale,Complex.ofReal_exp]
  have hsquare : Real.exp s = (scale s)^2 := by
    rw [scale,← Real.exp_nat_mul]
    congr 1
    ring
  unfold packet physicalGaussian quadratic
  rw [hscale,← Complex.ofReal_exp,hsquare]
  simp [squared,mix,flow,Fin.sum_univ_succ]
  congr 1
  ring

#print axioms squared_nonnegative
#print axioms mix_square_bound
#print axioms complexScale_square
#print axioms complexScale_norm_square
#print axioms complexScale_im_square_bound
#print axioms quadratic_re
#print axioms quadratic_re_lower
#print axioms quadratic_re_nonnegative
#print axioms packet_continuous
#print axioms packet_analytic
#print axioms packet_norm_square
#print axioms packet_norm_le_one
#print axioms packet_square_bound
#print axioms packet_real_flow

end
end UnifiedTheory.Audit.KFCausalClockFloorShearBounds
