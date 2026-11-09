/- The actual analytic neutral-position phase is unbounded on every
nonreal clock slice. A charged-position Gaussian localizer gives a bounded
analytic multiplier, with a quantitative bound on the same clock strip.
This is a multiplier estimate, not a full averaged-domain assertion. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
import UnifiedTheory.Audit.KFCausalNeutralPositionCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (neutral)
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds (complexScale_im_square_small)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (flow scale)

def phase (v : ℝ) (z : ℂ) (x : Grouped) : ℂ :=
  Complex.exp ((v:ℂ)*Complex.I*neutral z x)

def localized (δ v : ℝ) (z : ℂ) (x : Grouped) : ℂ :=
  Complex.exp (-(δ:ℂ)*Complex.exp z*(mix x.1:ℂ)^2)*phase v z x

def multiplier (ε δ v : ℝ) (q : ℂ) (x : Grouped) : ℂ :=
  localized δ v (complexInverse ε q) x

theorem phase_norm (v : ℝ) (z : ℂ) (x : Grouped) :
    ‖phase v z x‖ = Real.exp (-2*v*(complexScale z).im*mix x.1) := by
  rw [phase,Complex.norm_exp]
  congr 1
  simp [neutral,Complex.mul_re,Complex.mul_im]
  ring

theorem phase_real (v s : ℝ) (x : Grouped) :
    phase v (s:ℂ) x = KFCausalCanonicalWeylAlgebra.scalar
      (v*(flow s ![x.1 0,x.1 1,x.1 2,x.1 3,x.2]) 4) := by
  have hs : complexScale (s:ℂ) = (scale s:ℂ) := by
    simp [complexScale,scale,Complex.ofReal_exp]
  simp only [phase,neutral,hs,KFCausalCanonicalWeylAlgebra.scalar,flow,mix]
  norm_num
  congr 1
  push_cast
  ring

theorem phase_unbounded (v : ℝ) (z : ℂ) (hn : v*(complexScale z).im ≠ 0) (M : ℝ) :
    ∃ x : Grouped, M < ‖phase v z x‖ := by
  let r := -(|M|+1)/(2*(v*(complexScale z).im))
  refine ⟨(Pi.single 2 r,0),?_⟩
  rw [phase_norm]
  have hm : mix (Pi.single 2 r) = r := by simp [mix]
  rw [hm]
  have he : -2*v*(complexScale z).im*r = |M|+1 := by
    dsimp [r]
    have hv := (mul_ne_zero_iff.mp hn).1
    have hz := (mul_ne_zero_iff.mp hn).2
    field_simp [hv,hz]
  rw [he]
  linarith [Real.add_one_le_exp (|M|+1),le_abs_self M]

theorem inverse_scale_im_ne_zero (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (hi : q.im ≠ 0) : (complexScale (complexInverse ε q)).im ≠ 0 := by
  let z := complexInverse ε q
  have hz : |z.im| < Real.pi/2 := complexInverse_mem ε hε q hq
  have hzi : z.im ≠ 0 := by
    intro he
    have hq' := congrArg Complex.im (complexInverse_right ε hε q hq)
    rw [complexChart_im] at hq'
    change Real.exp z.re*Real.sin z.im+ε*z.im=q.im at hq'
    simp only [he,Real.sin_zero,mul_zero,add_zero] at hq'
    exact hi hq'.symm
  change (Complex.exp (z/2)).im ≠ 0
  rw [Complex.exp_im,Complex.div_ofNat_re,Complex.div_ofNat_im]
  apply mul_ne_zero (Real.exp_ne_zero _)
  intro hs
  have hz0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (show -Real.pi < z.im/2 by linarith [(abs_lt.mp hz).1,Real.pi_pos])
    (show z.im/2 < Real.pi by linarith [(abs_lt.mp hz).2,Real.pi_pos])).mp hs
  exact hzi (by linarith)

theorem actual_phase_unbounded (ε : ℝ) (hε : 0 < ε) (v : ℝ) (hv : v ≠ 0)
    (q : ℂ) (hq : q ∈ targetStrip ε) (hi : q.im ≠ 0) (M : ℝ) :
    ∃ x : Grouped, M < ‖phase v (complexInverse ε q) x‖ :=
  phase_unbounded v _ (mul_ne_zero hv (inverse_scale_im_ne_zero ε hε q hq hi)) M

theorem localized_norm (δ v : ℝ) (z : ℂ) (x : Grouped) :
    ‖localized δ v z x‖ =
      Real.exp (-δ*(Complex.exp z).re*(mix x.1)^2-2*v*(complexScale z).im*mix x.1) := by
  rw [localized,norm_mul,Complex.norm_exp,phase_norm,← Real.exp_add]
  congr 1
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.mul_im,Complex.neg_re,
    Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

theorem localized_bound (δ v : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3)
    (x : Grouped) : ‖localized δ v z x‖ ≤ Real.exp (v^2*z.im^2/(2*δ)) := by
  have he : Real.exp z.re/2 ≤ (Complex.exp z).re := by
    rw [Complex.exp_re]
    nlinarith [mul_le_mul_of_nonneg_left (cos_lower_third z.im hz) (Real.exp_pos z.re).le]
  have hs := complexScale_im_square_small z
  have hp := mul_le_mul_of_nonneg_left he (mul_nonneg hδ.le (sq_nonneg (mix x.1)))
  have hv := mul_le_mul_of_nonneg_left hs (sq_nonneg v)
  have hsq := sq_nonneg (δ*Real.exp z.re*mix x.1+2*v*(complexScale z).im)
  have hd : 0 < 2*δ := by positivity
  rw [localized_norm]
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ hd).mpr
  have hR : 0 < Real.exp z.re := Real.exp_pos _
  apply (mul_le_mul_iff_right₀ hR).mp
  have hp2 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*δ*Real.exp z.re)
  nlinarith only [hp2,hsq,hv]

theorem localized_analytic (δ v : ℝ) (x : Grouped) (z : ℂ) :
    AnalyticAt ℂ (fun z => localized δ v z x) z := by
  unfold localized phase neutral complexScale
  fun_prop

theorem multiplier_analytic (ε δ v : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (x : Grouped) : AnalyticAt ℂ (fun q => multiplier ε δ v q x) q :=
  (localized_analytic δ v x _).comp (complexInverse_analytic ε hε q hq)

theorem multiplier_bound (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) (x : Grouped) :
    ‖multiplier ε δ v q x‖ ≤ Real.exp (v^2*q.im^2/(2*δ*ε^2)) := by
  have ht := KFCausalClockFloorFullGaussian.third_strip_subset ε hε q hq
  have hi := pow_le_pow_left₀ (abs_nonneg _) (inverse_im_bound ε hε q ht) 2
  rw [sq_abs,div_pow,sq_abs] at hi
  apply (localized_bound δ v hδ _ (inverse_im_third_strip ε hε q hq) x).trans
  apply Real.exp_le_exp.mpr
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (sq_nonneg v))
    (by positivity : 0 ≤ 2*δ)).trans_eq (by ring)

#print axioms phase_norm
#print axioms phase_real
#print axioms phase_unbounded
#print axioms inverse_scale_im_ne_zero
#print axioms actual_phase_unbounded
#print axioms localized_norm
#print axioms localized_bound
#print axioms localized_analytic
#print axioms multiplier_analytic
#print axioms multiplier_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase
