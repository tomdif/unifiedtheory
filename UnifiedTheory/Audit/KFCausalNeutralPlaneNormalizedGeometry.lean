/- Normalize the unbounded clock variable by E/(epsilon+E). The
coefficients used below have denominators that extend across Im(r)=0. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2500000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneNormalizedGeometry
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates (fieldSlope)

def fraction (ε s : ℝ) : ℝ := Real.exp s/(ε+Real.exp s)
def realNumerator (t : ℝ) (r : ℂ) : ℝ :=
  (1-t)*(1-r.re^2+3*r.im^2)+t*(r.re^2+r.im^2)*(1-(r.re^2+r.im^2))
def imagNumerator (t : ℝ) (r : ℂ) : ℝ :=
  (1-t)*(1-3*r.re^2+r.im^2)-t*(r.re^2+r.im^2)*(1+(r.re^2+r.im^2))
def shearNumerator (t : ℝ) (r : ℂ) : ℝ :=
  -2*r.re*realNumerator t r-(3-2*r.re)*imagNumerator t r
def normalizedWidthSlope (α t : ℝ) (r : ℂ) : ℝ :=
  α*t*r.re^2*(r.re^2+r.im^2)/(2*r.im^2*denominator (1-t) t r)
def logPrefactorSlope (t : ℝ) (r : ℂ) : ℝ :=
  -t/(2*denominator (1-t) t r) *
    (3*(r.re^2*realNumerator t r-r.im^2*imagNumerator t r)/(r.re^2-r.im^2)+
      imagNumerator t r)
def regularScore (α t : ℝ) (r : ℂ) : ℝ :=
  logPrefactorSlope t r+
    t*(shearNumerator t r)^2/(8*α*r.re^2*(r.re^2+r.im^2)*denominator (1-t) t r)

theorem fraction_bounds (ε s : ℝ) (hε : 0 < ε) :
    0 < fraction ε s ∧ fraction ε s < 1 := by
  unfold fraction
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).mpr
    linarith

theorem normalized_denominator_positive (t : ℝ) (r : ℂ)
    (ht : t ∈ Set.Icc 0 1) (hA : 0 < r.re^2-r.im^2) :
    0 < denominator (1-t) t r := by
  have hd : 0 < 1-t+t*(r.re^2-r.im^2) := by
    by_cases h : t=1
    · simpa [h] using hA
    · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h
      nlinarith [mul_nonneg ht.1 hA.le]
  unfold denominator
  positivity

theorem normalized_velocity_re (t : ℝ) (r : ℂ) :
    (velocity (1-t) t r).re =
      t*r.re*realNumerator t r/(2*denominator (1-t) t r) := by
  unfold velocity realNumerator denominator
  simp only [Complex.div_ofNat_re,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,pow_two,Complex.normSq_apply]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem normalized_velocity_im (t : ℝ) (r : ℂ) :
    (velocity (1-t) t r).im =
      t*r.im*imagNumerator t r/(2*denominator (1-t) t r) := by
  unfold velocity imagNumerator denominator
  simp only [Complex.div_ofNat_im,Complex.div_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,pow_two,Complex.normSq_apply]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem velocity_normalize (ε E : ℝ) (r : ℂ) (hc : ε+E ≠ 0)
    (hd : (ε:ℂ)+(E:ℂ)*r^2 ≠ 0) :
    velocity ε E r = velocity (1-E/(ε+E)) (E/(ε+E)) r := by
  have hc' : ((ε+E:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hc'' : (ε:ℂ)+(E:ℂ) ≠ 0 := by exact_mod_cast hc
  have hn : ((1-E/(ε+E):ℝ):ℂ)+((E/(ε+E):ℝ):ℂ)*r^2 =
      ((ε:ℂ)+(E:ℂ)*r^2)/((ε+E:ℝ):ℂ) := by
    push_cast
    field_simp [hc'']
    ring
  have hn0 : ((1-E/(ε+E):ℝ):ℂ)+((E/(ε+E):ℝ):ℂ)*r^2 ≠ 0 := by
    rw [hn]
    exact div_ne_zero hd hc'
  unfold velocity
  rw [hn,Complex.ofReal_div]
  field_simp

theorem denominator_normalize (ε E : ℝ) (r : ℂ) (hc : ε+E ≠ 0) :
    denominator (1-E/(ε+E)) (E/(ε+E)) r = denominator ε E r/(ε+E)^2 := by
  unfold denominator
  field_simp
  ring

theorem widthSlope_normalize (α ε E : ℝ) (r : ℂ) (hc : ε+E ≠ 0)
    (hd : denominator ε E r ≠ 0) :
    widthSlope α ε E r = normalizedWidthSlope α (E/(ε+E)) r := by
  unfold normalizedWidthSlope
  rw [denominator_normalize ε E r hc]
  unfold widthSlope
  field_simp

theorem actual_normalized_velocity (ε y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (scale ε y)
      (velocity (1-fraction ε s) (fraction ε s) (scale ε y s)) s := by
  have hd := scale_velocity ε y s hε hy
  have hc : ε+Real.exp s ≠ 0 := by positivity
  have hn : (ε:ℂ)+(Real.exp s:ℂ)*(scale ε y s)^2 ≠ 0 := by
    rw [scale_square]
    rw [add_comm]
    exact KFCausalClockFloorComplexDefect.complexClock_ne_zero ε hε _
      (argument_mem ε y s hε hy)
  rwa [velocity_normalize ε (Real.exp s) _ hc hn] at hd

theorem fieldSlope_derivative (r : ℝ → ℂ) (v : ℂ) (s : ℝ)
    (hr : HasDerivAt r v s) (hb : (r s).im ≠ 0) :
    HasDerivAt (fun t => fieldSlope (r t))
      ((-2*v.re*(r s).im-(3-2*(r s).re)*v.im)/(2*(r s).im^2)) s := by
  have ha := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hd := ((ha.const_mul 2).const_sub 3).div (hi.const_mul 2) (by simpa using hb)
  convert hd using 1
  dsimp
  field_simp

theorem normalized_fieldSlope_derivative (r : ℝ → ℂ) (t s : ℝ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s) (hb : (r s).im ≠ 0)
    (hd : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => fieldSlope (r u))
      (t*shearNumerator t (r s)/(4*(r s).im*denominator (1-t) t (r s))) s := by
  have he := fieldSlope_derivative r _ s hr hb
  rw [normalized_velocity_re,normalized_velocity_im] at he
  convert he using 1
  unfold shearNumerator
  field_simp
  ring

theorem normalized_shear_quotient (α t : ℝ) (r : ℂ)
    (hα : α ≠ 0) (ht : t ≠ 0) (ha : r.re ≠ 0) (hb : r.im ≠ 0)
    (hS : r.re^2+r.im^2 ≠ 0) (hd : denominator (1-t) t r ≠ 0) :
    (t*shearNumerator t r/(4*r.im*denominator (1-t) t r))^2 /
        normalizedWidthSlope α t r =
      t*(shearNumerator t r)^2/(8*α*r.re^2*(r.re^2+r.im^2)*denominator (1-t) t r) := by
  unfold normalizedWidthSlope
  field_simp
  ring

#print axioms fraction_bounds
#print axioms normalized_denominator_positive
#print axioms normalized_velocity_re
#print axioms normalized_velocity_im
#print axioms velocity_normalize
#print axioms denominator_normalize
#print axioms widthSlope_normalize
#print axioms actual_normalized_velocity
#print axioms fieldSlope_derivative
#print axioms normalized_fieldSlope_derivative
#print axioms normalized_shear_quotient
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneNormalizedGeometry
