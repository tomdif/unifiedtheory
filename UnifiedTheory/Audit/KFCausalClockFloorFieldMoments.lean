/- Quadratic field moments of the full sheared Gaussian remain in joint
L2. Polynomial growth is absorbed by halving both transverse Gaussian
widths; the clock profile and its strip width are unchanged. -/
import UnifiedTheory.Audit.KFCausalClockFloorFieldBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorFieldBounds
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow

theorem quadratic_half (α β : ℝ) (z : ℂ) (x : Charged) (r : ℝ) :
    quadratic (α/2) (β/2) z x r = quadratic α β z x r/2 := by
  unfold quadratic
  push_cast
  ring

theorem packet_half_norm (α β : ℝ) (z : ℂ) (x : Grouped) :
    ‖packet (α/2) (β/2) z x‖ = Real.exp (-(quadratic α β z x.1 x.2).re/2) := by
  rw [packet,Complex.norm_exp,Complex.neg_re,quadratic_half,Complex.div_ofNat_re,neg_div]

theorem linear_exp_absorption (R : ℝ) : R*Real.exp (-R) ≤ 2*Real.exp (-R/2) := by
  have he : R ≤ 2*Real.exp (R/2) := by linarith [Real.add_one_le_exp (R/2)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-R)).le
  have hid : Real.exp (R/2)*Real.exp (-R) = Real.exp (-R/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc,hid] using hm

theorem field_packet_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3)
    (he : Real.exp s ≤ Real.exp (Real.pi/3)*Real.exp z.re) (x : Grouped)
    (l : Transverse →L[ℝ] ℝ) :
    ‖(l (flow s ![x.1 0,x.1 1,x.1 2,x.1 3,x.2]):ℂ)^2*packet α β z x‖ ≤
      (2*‖l‖^2*momentBound α β)*‖packet (α/2) (β/2) z x‖ := by
  have hf := field_quadratic_bound α β hα hβ hw s z hz he x.1 x.2 l
  have hn : 0 ≤ ‖l‖^2*momentBound α β :=
    mul_nonneg (sq_nonneg _) (momentBound_positive α β hα hβ).le
  have hb := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-(quadratic α β z x.1 x.2).re)).le
  have ha := mul_le_mul_of_nonneg_left (linear_exp_absorption (quadratic α β z x.1 x.2).re) hn
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,packet_half_norm]
  rw [packet,Complex.norm_exp,Complex.neg_re]
  nlinarith

def fieldLine (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (w : ℝ × Grouped) : ℝ :=
  l (flow ((chartIso ε hε).symm w.1) ![w.2.1 0,w.2.1 1,w.2.1 2,w.2.1 3,w.2.2])

theorem fieldLine_continuous (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fieldLine ε hε l) := by
  have hs : Continuous (fun w : ℝ × Grouped => (chartIso ε hε).symm w.1) :=
    (chartIso ε hε).symm.toHomeomorph.continuous.comp continuous_fst
  have hx : Continuous (fun w : ℝ × Grouped =>
      (![w.2.1 0,w.2.1 1,w.2.1 2,w.2.1 3,w.2.2]:Transverse)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact l.continuous.comp (KFCausalCoupledCoordinateHomeomorph.flow_joint_continuous.comp (hs.prodMk hx))

theorem quadratic_line_bound (ε a α β y : ℝ) (hε : 0 < ε)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (w : ℝ × Grouped) :
    ‖(fieldLine ε hε l w:ℂ)^2*line ε a α β y w‖ ≤
      (2*‖l‖^2*momentBound α β)*‖line ε a (α/2) (β/2) y w‖ := by
  let q : ℂ := (w.1:ℂ)+(y:ℂ)*Complex.I
  have hq : |q.im| ≤ Real.pi*ε/3 := by simpa only [q,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hy
  have hf := field_packet_bound α β hα hβ hw ((chartIso ε hε).symm q.re) (complexInverse ε q)
    (inverse_im_third_strip ε hε q hq) (inverse_real_exp_bound ε hε q hq) w.2 l
  have hb := mul_le_mul_of_nonneg_left hf (norm_nonneg (clockFactor a q))
  simpa only [q,line,trial,fieldLine,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    norm_mul,mul_left_comm,mul_assoc] using hb

theorem quadratic_line_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun w : ℝ × Grouped => (fieldLine ε hε l w:ℂ)^2*line ε a α β y w) 2 volume := by
  have hm := line_memLp ε a (α/2) (β/2) y hε ha (by positivity) (by positivity) (by linarith) hy
  have hc : Continuous (fun w : ℝ × Grouped => (fieldLine ε hε l w:ℂ)^2*line ε a α β y w) :=
    ((Complex.continuous_ofReal.comp (fieldLine_continuous ε hε l)).pow 2).mul (line_continuous ε a α β y hε hy)
  apply (hm.const_mul ((2*‖l‖^2*momentBound α β:ℝ):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with w
  conv_rhs => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg (by positivity) (momentBound_positive α β hα hβ).le)]
  exact quadratic_line_bound ε a α β y hε hα hβ hw hy l w

#print axioms quadratic_half
#print axioms packet_half_norm
#print axioms linear_exp_absorption
#print axioms field_packet_bound
#print axioms fieldLine_continuous
#print axioms quadratic_line_bound
#print axioms quadratic_line_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
