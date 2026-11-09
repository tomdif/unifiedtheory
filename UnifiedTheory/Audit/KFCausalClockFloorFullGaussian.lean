/- Six-dimensional horizontal L2 bounds for the optional clock-floor
Gaussian, with four equal charged widths and the actual neutral shear.
These are function-space estimates, not membership in a new Hamiltonian
domain or a proof of charge invariance. -/
import UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
import UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
noncomputable section
open MeasureTheory Set Filter
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests (quadratic_exp_integrable)

def clockFactor (a : ℝ) (q : ℂ) : ℂ := Complex.exp (-(a:ℂ)*q^2)
def trial (ε a α β : ℝ) (q : ℂ) (x : Grouped) : ℂ :=
  clockFactor a q * packet α β (complexInverse ε q) x
def line (ε a α β y : ℝ) (z : ℝ × Grouped) : ℂ :=
  trial ε a α β ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2

theorem third_strip_subset (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : q ∈ targetStrip ε := by
  change |q.im| ≤ Real.pi*ε/2
  nlinarith [Real.pi_pos]

theorem trial_analytic (ε a α β : ℝ) (hε : 0 < ε) (x : Grouped)
    (q : ℂ) (hq : q ∈ targetStrip ε) : AnalyticAt ℂ (fun q => trial ε a α β q x) q := by
  have hp := (packet_analytic α β x (complexInverse ε q)).comp
    (complexInverse_analytic ε hε q hq)
  exact (show AnalyticAt ℂ (clockFactor a) q by unfold clockFactor; fun_prop).mul hp

theorem inverse_line_continuous (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (fun q : ℝ => complexInverse ε ((q:ℂ)+(y:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hq : (q:ℂ)+(y:ℂ)*Complex.I ∈ targetStrip ε :=
    third_strip_subset ε hε _ (by simpa using hy)
  exact (complexInverse_analytic ε hε _ hq).continuousAt.comp
    (f := fun q : ℝ => (q:ℂ)+(y:ℂ)*Complex.I) (by fun_prop)

theorem line_continuous (ε a α β y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (line ε a α β y) := by
  have hi := (inverse_line_continuous ε y hε hy).comp (continuous_fst (Y := Grouped))
  unfold line trial clockFactor packet quadratic complexScale squared mix
  fun_prop

theorem clockFactor_norm (a q y : ℝ) :
    ‖clockFactor a ((q:ℂ)+(y:ℂ)*Complex.I)‖ = Real.exp (-a*(q^2-y^2)) := by
  rw [clockFactor,Complex.norm_exp]
  congr 1
  simp [pow_two,Complex.mul_re,Complex.mul_im]

theorem line_square (ε a α β y q : ℝ) (x : Grouped) :
    ‖line ε a α β y (q,x)‖^2 = Real.exp (2*a*y^2)*Real.exp (-2*a*q^2)*
      ‖packet α β (complexInverse ε ((q:ℂ)+(y:ℂ)*Complex.I)) x‖^2 := by
  rw [line,trial,norm_mul,mul_pow,clockFactor_norm,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem line_slice_memLp (ε a α β y q : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun x : Grouped => line ε a α β y (q,x)) 2 volume := by
  simpa only [line,trial] using
    (packet_memLp α β hα hβ hw (complexInverse ε ((q:ℂ)+(y:ℂ)*Complex.I))
      (inverse_im_third_strip ε hε ((q:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy))).const_mul
        (clockFactor a ((q:ℂ)+(y:ℂ)*Complex.I))

def clockEnvelope (ε a q : ℝ) : ℝ :=
  Real.exp (-2*a*q^2)*(1+Real.exp (2*(1-q)/ε))

theorem clockEnvelope_integrable (ε a : ℝ) (ha : 0 < a) : Integrable (clockEnvelope ε a) := by
  have h0 := integrable_exp_neg_mul_sq (by positivity : 0 < 2*a)
  have h1 := quadratic_exp_integrable (2*a) (-2/ε) (2/ε) (by positivity)
  convert h0.add h1 using 1
  funext q
  dsimp only [clockEnvelope,Pi.add_apply]
  rw [mul_add,mul_one,← Real.exp_add]
  congr 2 <;> ring

theorem line_inner_bound (ε a α β y q : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    (∫ x : Grouped, ‖line ε a α β y (q,x)‖^2) ≤
      (Real.exp (2*a*y^2)*transverseConstant α β)*clockEnvelope ε a q := by
  let z : ℂ := (q:ℂ)+(y:ℂ)*Complex.I
  have hz : z ∈ targetStrip ε := third_strip_subset ε hε z (by simpa [z] using hy)
  have hp := packet_square_integral_bound α β hα hβ hw (complexInverse ε z)
    (inverse_im_third_strip ε hε z (by simpa [z] using hy))
  have hc := inverse_negative_power_bound ε 2 hε (by norm_num) z hz
  have hb := hp.trans (mul_le_mul_of_nonneg_left hc (transverseConstant_nonnegative α β))
  simp_rw [line_square]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ Real.exp (2*a*y^2)*Real.exp (-2*a*q^2))
  convert h using 1
  simp only [clockEnvelope,z,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  ring

theorem line_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (line ε a α β y) 2 volume := by
  have hcont := line_continuous ε a α β y hε hy
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  rw [Measure.volume_eq_prod ℝ Grouped]
  have hm : AEStronglyMeasurable (fun z : ℝ × Grouped => ‖line ε a α β y z‖^2)
      ((volume : Measure ℝ).prod (volume : Measure Grouped)) :=
    (hcont.norm.pow 2).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · apply ae_of_all
    intro q
    have hs := line_slice_memLp ε a α β y q hε hα hβ hw hy
    exact (memLp_two_iff_integrable_sq_norm hs.1).mp hs
  · simp only [Real.norm_eq_abs,abs_sq]
    apply ((clockEnvelope_integrable ε a ha).const_mul
      (Real.exp (2*a*y^2)*transverseConstant α β)).mono' hm.integral_prod_right'
    filter_upwards [] with q
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun x => sq_nonneg ‖line ε a α β y (q,x)‖))]
    exact line_inner_bound ε a α β y q hε hα hβ hw hy

theorem line_ne_zero (ε a α β y : ℝ) (z : ℝ × Grouped) : line ε a α β y z ≠ 0 := by
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

def lineState (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    Lp ℂ 2 (volume : Measure (ℝ × Grouped)) :=
  (line_memLp ε a α β y hε ha hα hβ hw hy).toLp (line ε a α β y)

theorem lineState_ne_zero (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    lineState ε a α β y hε ha hα hβ hw hy ≠ 0 := by
  intro h
  have hae := (line_memLp ε a α β y hε ha hα hβ hw hy).coeFn_toLp
  change lineState ε a α β y hε ha hα hβ hw hy =ᵐ[volume] line ε a α β y at hae
  rw [h] at hae
  have hzero : line ε a α β y =ᵐ[volume] (fun _ => (0:ℂ)) := by
    filter_upwards [hae,Lp.coeFn_zero (ℂ) 2 (volume : Measure (ℝ × Grouped))] with x hx hz
    exact hx.symm.trans hz
  have he := Measure.eq_of_ae_eq hzero (line_continuous ε a α β y hε hy) continuous_const
  exact line_ne_zero ε a α β y (0,(0,0)) (congrFun he _)

#print axioms third_strip_subset
#print axioms trial_analytic
#print axioms inverse_line_continuous
#print axioms line_continuous
#print axioms clockFactor_norm
#print axioms line_square
#print axioms line_slice_memLp
#print axioms clockEnvelope_integrable
#print axioms line_inner_bound
#print axioms line_memLp
#print axioms line_ne_zero
#print axioms lineState_ne_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
