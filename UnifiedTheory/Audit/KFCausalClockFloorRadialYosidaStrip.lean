/- Actual complex continuation of the rational charged-radius cutoff.
On the half-clock strip its symbol is bounded and accretive. The real
slice is identified with the physical charge-coordinate multiplier. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSymbol
import UnifiedTheory.Audit.KFCausalClockFloorMixedSymbols
import UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefect

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrip
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block split)
open KFCausalClockFloorRadialYosidaSymbol (radial symbol action action_coe)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_relation)
open KFCausalClockFloorPairedStraightening (clockInverse dilation)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorMixedSymbols (dilation_square inverse_dilation_square)
open KFCausalClockFloorFlow (clock)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalComplexClockChart (targetStrip)
open KFCausalComplexClockInverse
open KFCausalClockInverseStripBounds
open KFCausalClockFloorComplexDefect (complexClock complexClock_ne_zero)

def base (ε A B : ℝ) (z : ℂ) : ℂ :=
  ((A:ℂ)/(z*(z+(ε:ℂ)))+(B:ℂ)*z/(z+(ε:ℂ)))/2

def cutoff (N : ℝ) (z : ℂ) : ℂ := (N:ℂ)*z/((N:ℂ)+z)

private theorem base_re (ε A B : ℝ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (z : ℂ) (hz : 0 ≤ z.re) (hz2 : 0 ≤ (z^2).re) : 0 ≤ (base ε A B z).re := by
  have hp : 0 ≤ (z*(z+(ε:ℂ))).re := by
    simp only [pow_two,Complex.mul_re] at hz2
    simp only [Complex.mul_re,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,add_zero]
    nlinarith [mul_nonneg hε hz]
  have h1 : 0 ≤ ((A:ℂ)/(z*(z+(ε:ℂ)))).re := by
    simp only [Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
    exact div_nonneg (mul_nonneg hA hp) (Complex.normSq_nonneg _)
  have h2 : 0 ≤ ((B:ℂ)*z/(z+(ε:ℂ))).re := by
    simp only [Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,add_zero,Complex.add_re,Complex.add_im]
    apply add_nonneg
    · exact div_nonneg (mul_nonneg (mul_nonneg hB hz) (add_nonneg hz hε))
        (Complex.normSq_nonneg _)
    · exact div_nonneg (by nlinarith [mul_nonneg hB (sq_nonneg z.im)]) (Complex.normSq_nonneg _)
  simpa only [base,Complex.div_ofNat_re,Complex.add_re] using div_nonneg (add_nonneg h1 h2)
    (by norm_num : (0:ℝ) ≤ 2)

private theorem cutoff_denominator (N : ℝ) (hN : 0 < N) (z : ℂ) (hz : 0 ≤ z.re) :
    (N:ℂ)+z ≠ 0 := by
  intro he
  have hi := congrArg Complex.re he
  simp only [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hi
  linarith

private theorem cutoff_re (N : ℝ) (hN : 0 < N) (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ (cutoff N z).re := by
  simp only [cutoff,Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,add_zero,Complex.add_re,Complex.add_im,zero_add]
  apply add_nonneg
  · exact div_nonneg (mul_nonneg (mul_nonneg hN.le hz) (add_nonneg hN.le hz))
      (Complex.normSq_nonneg _)
  · exact div_nonneg (by nlinarith [mul_nonneg hN.le (sq_nonneg z.im)]) (Complex.normSq_nonneg _)

private theorem cutoff_norm (N : ℝ) (hN : 0 < N) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖cutoff N z‖ ≤ N := by
  have hd := cutoff_denominator N hN z hz
  have hn : ‖z‖ ≤ ‖(N:ℂ)+z‖ := by
    have he : ‖(N:ℂ)+z‖^2 = N^2+‖z‖^2+2*N*z.re := by
      rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_add]
      ring
    nlinarith [norm_nonneg z,norm_nonneg ((N:ℂ)+z),mul_nonneg hN.le hz,sq_nonneg N]
  rw [cutoff,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  exact (div_le_iff₀ (norm_pos_iff.mpr hd)).mpr (mul_le_mul_of_nonneg_left hn hN.le)

theorem sixth_strip_subset (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) : q ∈ targetStrip ε := by
  change |q.im| ≤ Real.pi*ε/2
  nlinarith [Real.pi_pos]

theorem inverse_im_sixth (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) : |(complexInverse ε q).im| ≤ Real.pi/6 :=
  (inverse_im_bound ε hε q (sixth_strip_subset ε hε q hq)).trans
    ((div_le_iff₀ hε).mpr (by nlinarith))

private theorem exp_sector (s : ℂ) (hs : |s.im| ≤ Real.pi/6) :
    0 ≤ (Complex.exp s).re ∧ 0 ≤ ((Complex.exp s)^2).re := by
  obtain ⟨hl,hu⟩ := abs_le.mp hs
  have hc : 0 ≤ Real.cos s.im := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc2 : 0 ≤ Real.cos (2*s.im) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  constructor
  · rw [Complex.exp_re]
    exact mul_nonneg (Real.exp_pos _).le hc
  · rw [pow_two,← Complex.exp_add,Complex.exp_re,Complex.add_im]
    rw [show s.im+s.im=2*s.im by ring]
    exact mul_nonneg (Real.exp_pos (s+s).re).le hc2

def radialComplex (ε h : ℝ) (q : ℂ) (x : Block 2 × Block 4) : ℂ :=
  base ε (momentumScale h^2*(x.1 0^2+x.1 1^2)) (x.2 1^2+x.2 2^2)
    (Complex.exp (complexInverse ε q))

def multiplier (ε h N : ℝ) (q : ℂ) (x : Block 2 × Block 4) : ℂ :=
  cutoff N (radialComplex ε h q x)

theorem radialComplex_re (ε : ℝ) (hε : 0 < ε) (h : ℝ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (x : Block 2 × Block 4) :
    0 ≤ (radialComplex ε h q x).re := by
  have hs := exp_sector (complexInverse ε q) (inverse_im_sixth ε hε q hq)
  exact base_re ε _ _ hε.le (by positivity) (by positivity) _ hs.1 hs.2

theorem multiplier_re (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (x : Block 2 × Block 4) :
    0 ≤ (multiplier ε h N q x).re :=
  cutoff_re N hN _ (radialComplex_re ε hε h q hq x)

theorem multiplier_norm (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (x : Block 2 × Block 4) :
    ‖multiplier ε h N q x‖ ≤ N :=
  cutoff_norm N hN _ (radialComplex_re ε hε h q hq x)

theorem multiplier_analytic (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (x : Block 2 × Block 4) :
    AnalyticAt ℂ (fun q => multiplier ε h N q x) q := by
  have hz := (complexInverse_analytic ε hε q (sixth_strip_subset ε hε q hq)).cexp
  have hc := complexClock_ne_zero ε hε q (sixth_strip_subset ε hε q hq)
  have he := Complex.exp_ne_zero (complexInverse ε q)
  have hr : AnalyticAt ℂ (fun q => radialComplex ε h q x) q := by
    unfold radialComplex base
    exact ((analyticAt_const.div (hz.mul (hz.add analyticAt_const)) (mul_ne_zero he hc)).add
      ((analyticAt_const.mul hz).div (hz.add analyticAt_const) hc)).div_const
  exact (analyticAt_const.mul hr).div (analyticAt_const.add hr)
    (cutoff_denominator N hN _ (radialComplex_re ε hε h q hq x))

theorem multiplier_line_continuous (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) :
    Continuous (fun z : ℝ × (Block 2 × Block 4) =>
      multiplier ε h N ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) := by
  have hy3 : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  have hi := (KFCausalClockFloorFullGaussian.inverse_line_continuous ε y hε hy3).comp
    (continuous_fst (Y := Block 2 × Block 4))
  have hc (z : ℝ × (Block 2 × Block 4)) :
      Complex.exp (complexInverse ε ((z.1:ℂ)+(y:ℂ)*Complex.I))+(ε:ℂ) ≠ 0 :=
    complexClock_ne_zero ε hε _ (sixth_strip_subset ε hε _ (by simpa using hy))
  have hr : Continuous (fun z : ℝ × (Block 2 × Block 4) =>
      radialComplex ε h ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) := by
    unfold radialComplex base
    have hA : Continuous (fun z : ℝ × (Block 2 × Block 4) =>
        ((momentumScale h^2*(z.2.1 0^2+z.2.1 1^2):ℝ):ℂ)) := by fun_prop
    have hB : Continuous (fun z : ℝ × (Block 2 × Block 4) =>
        ((z.2.2 1^2+z.2.2 2^2:ℝ):ℂ)) := by fun_prop
    apply Continuous.div_const
    apply Continuous.add
    · exact hA.div ((Complex.continuous_exp.comp hi).mul
        ((Complex.continuous_exp.comp hi).add continuous_const))
        (fun z => mul_ne_zero (Complex.exp_ne_zero _) (hc z))
    · exact (hB.mul (Complex.continuous_exp.comp hi)).div
        ((Complex.continuous_exp.comp hi).add continuous_const) hc
  exact (continuous_const.mul hr).div (continuous_const.add hr)
    (fun z => cutoff_denominator N hN _
      (radialComplex_re ε hε h _ (by simpa using hy) z.2))

theorem radial_transformed (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Block 2 × Block 4) :
    radial ε h ((split 2 4).symm (mixedMap ε hε x)) =
      (Real.exp (-clockInverse ε hε x.2)*momentumScale h^2*(x.1 0^2+x.1 1^2)+
        Real.exp (clockInverse ε hε x.2)*(x.2 1^2+x.2 2^2))/(2*clock ε (clockInverse ε hε x.2)) := by
  rw [KFCausalClockFloorRadialYosidaSymbol.radial_coordinates]
  change (momentumScale h^2*(((dilation ε hε x.2)⁻¹*x.1 0)^2+
      ((dilation ε hε x.2)⁻¹*x.1 1)^2)+(dilation ε hε x.2*x.2 1)^2+
      (dilation ε hε x.2*x.2 2)^2)/(2*clock ε (clockInverse ε hε x.2)) = _
  simp only [mul_pow,inverse_dilation_square,dilation_square]
  ring

theorem radialComplex_real (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Block 2 × Block 4) :
    radialComplex ε h (x.2 0:ℂ) x =
      (radial ε h ((split 2 4).symm (mixedMap ε hε x)):ℂ) := by
  rw [radialComplex,complexInverse_real ε hε,radial_transformed]
  change base ε _ _ (Complex.exp (clockInverse ε hε x.2:ℂ)) = _
  unfold base clock
  rw [← Complex.ofReal_exp,Real.exp_neg]
  have he : (Real.exp (clockInverse ε hε x.2):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hc : ((Real.exp (clockInverse ε hε x.2):ℂ)+(ε:ℂ)) ≠ 0 :=
    by rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast
  field_simp

theorem multiplier_real (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (x : Block 2 × Block 4) :
    multiplier ε h N (x.2 0:ℂ) x =
      (symbol ε h N ((split 2 4).symm (mixedMap ε hε x)):ℂ) := by
  rw [multiplier,radialComplex_real ε hε]
  simp only [cutoff,symbol,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_add]

theorem action_transformed (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (f : Hilbert) :
    clockMixed ε hε (action ε hε h N hN f) =ᵐ[volume] fun x =>
      multiplier ε h N (x.2 0:ℂ) x*(clockMixed ε hε f) x := by
  simpa only [multiplier_real ε hε] using
    clockMixed_relation ε hε (fun x => (symbol ε h N x:ℂ)) f _
      (action_coe ε hε h N hN f)

#print axioms sixth_strip_subset
#print axioms inverse_im_sixth
#print axioms radialComplex_re
#print axioms multiplier_re
#print axioms multiplier_norm
#print axioms multiplier_analytic
#print axioms multiplier_line_continuous
#print axioms radial_transformed
#print axioms radialComplex_real
#print axioms multiplier_real
#print axioms action_transformed
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrip
