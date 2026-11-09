/- The positive radial term in the quartic angular tilt follows from
the actual entire circle number form. Multiplication by z^2 removes
the two negative Fourier modes of the real quadratic amplitude. -/
import UnifiedTheory.Audit.KFCausalAngularEntireNumber
import UnifiedTheory.Audit.KFCausalAngularQuarticQuadraticTilt

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularQuarticHardy
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

def exponent (d q : ℝ) : Polynomial ℂ :=
  Polynomial.C ((d/4:ℝ):ℂ)*Polynomial.X^2-Polynomial.C ((q/2:ℝ):ℂ)*Polynomial.X
def amplitude (mu L : ℝ) : Polynomial ℂ :=
  Polynomial.C (mu:ℂ)*Polynomial.X+Polynomial.C ((L/2:ℝ):ℂ)*(Polynomial.X^2+1)

private theorem exponent_eval (d q : ℝ) (z : ℂ) :
    (exponent d q).eval z=(d:ℂ)/4*z^2-(q:ℂ)/2*z := by
  simp [exponent]
private theorem exponent_derivative (d q : ℝ) (z : ℂ) :
    (exponent d q).derivative.eval z=(d:ℂ)/2*z-(q:ℂ)/2 := by
  simp [exponent]
  ring
private theorem amplitude_derivative (mu L : ℝ) (z : ℂ) :
    (amplitude mu L).derivative.eval z=(mu:ℂ)+(L:ℂ)*z := by
  simp [amplitude]
  ring

theorem amplitude_circle (mu L : ℝ) (z : ℂ) (hz : z.re^2+z.im^2=1) :
    (amplitude mu L).eval z=z*((mu+L*z.re:ℝ):ℂ) := by
  simp only [amplitude,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_one]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,pow_two,Complex.add_im,Complex.mul_im,Complex.one_re]
    linear_combination -(L/2)*hz
  · simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,pow_two,Complex.add_re,Complex.mul_re,Complex.one_im]
    ring

def numberDensity (d q mu L : ℝ) (z : ℂ) : ℂ :=
  conj (Complex.exp ((exponent d q).eval z)*((amplitude mu L)^2).eval z)*
    (z*Complex.exp ((exponent d q).eval z)*
      ((exponent d q).derivative.eval z*((amplitude mu L)^2).eval z+
        ((amplitude mu L)^2).derivative.eval z))

theorem density_identity (d q mu L : ℝ) (z : ℂ) (hz : z.re^2+z.im^2=1) :
    (numberDensity d q mu L z).re=Real.exp (-d/2)/2*
      ((2*d*z.re^2-q*z.re-d+4)*Real.exp (d*z.re^2-q*z.re)*(mu+L*z.re)^4) := by
  let W : ℝ := mu+L*z.re
  have hzz : conj z*z=1 := by
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.one_re]
      nlinarith [hz]
    · simp [Complex.mul_im]
      ring
  have hA : 2*((exponent d q).eval z).re=-d/2+(d*z.re^2-q*z.re) := by
    rw [exponent_eval]
    simp only [Complex.sub_re,Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,
      Complex.ofReal_re,Complex.ofReal_im,pow_two,zero_div,zero_mul,sub_zero]
    linear_combination -(d/2)*hz
  have hDA : (z*(exponent d q).derivative.eval z).re=d*z.re^2-q*z.re/2-d/2 := by
    rw [exponent_derivative]
    simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.mul_im,
      Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_div,zero_mul,sub_zero]
    linear_combination -(d/2)*hz
  have hB : ((amplitude mu L)^2).eval z=(z*(W:ℂ))^2 := by
    rw [Polynomial.eval_pow,amplitude_circle mu L z hz]
  have hDB : ((amplitude mu L)^2).derivative.eval z=
      2*(z*(W:ℂ))*((mu:ℂ)+(L:ℂ)*z) := by
    simp only [Polynomial.derivative_pow,Polynomial.eval_mul,Polynomial.eval_C,
      show (2:ℕ)-1=1 by norm_num,pow_one,
      amplitude_circle mu L z hz,amplitude_derivative]
    rfl
  have hpair :
      conj (((amplitude mu L)^2).eval z)*
        (z*((exponent d q).derivative.eval z*((amplitude mu L)^2).eval z+
          ((amplitude mu L)^2).derivative.eval z))=
        (W:ℂ)^4*(z*(exponent d q).derivative.eval z)+
          2*(W:ℂ)^3*((mu:ℂ)+(L:ℂ)*z) := by
    rw [hB,hDB]
    simp only [map_pow,map_mul,Complex.conj_ofReal]
    calc
      _ = (conj z*z)^2*(W:ℂ)^4*(z*(exponent d q).derivative.eval z)+
          2*(conj z*z)^2*(W:ℂ)^3*((mu:ℂ)+(L:ℂ)*z) := by ring
      _ = _ := by rw [hzz]; ring
  have hexp : conj (Complex.exp ((exponent d q).eval z))*Complex.exp ((exponent d q).eval z)=
      ((Real.exp (-d/2)*Real.exp (d*z.re^2-q*z.re):ℝ):ℂ) := by
    rw [Complex.conj_mul',Complex.norm_exp,←Complex.ofReal_pow,←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [hA,Real.exp_add]
  have he : numberDensity d q mu L z=
      (conj (Complex.exp ((exponent d q).eval z))*Complex.exp ((exponent d q).eval z))*
        (conj (((amplitude mu L)^2).eval z)*
          (z*((exponent d q).derivative.eval z*((amplitude mu L)^2).eval z+
            ((amplitude mu L)^2).derivative.eval z))) := by
    unfold numberDensity
    rw [map_mul]
    ring
  rw [he,hexp,hpair]
  simp only [←Complex.ofReal_pow]
  rw [show (2:ℂ)*((W^3:ℝ):ℂ)=((2*W^3:ℝ):ℂ) by push_cast; rfl]
  simp only [Complex.re_ofReal_mul,Complex.add_re,hDA,Complex.ofReal_re]
  dsimp only [W]
  ring

theorem unsmoothed_bound (d q mu L : ℝ) :
    (d-4)*KFCausalAngularQuarticQuadraticTilt.energy 0 d q mu L ≤
      KFCausalAngularQuarticQuadraticTilt.tilt 0 d q mu L := by
  have hp := KFCausalAngularEntireNumber.number_nonnegative (exponent d q) ((amplitude mu L)^2) 1
  have hd (theta : ℝ) : (numberDensity d q mu L (circleMap 0 1 theta)).re=
      Real.exp (-d/2)/2*((2*d*(Real.cos theta)^2-q*Real.cos theta-d+4)*
        Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*(mu+L*Real.cos theta)^4) := by
    have hz : (circleMap 0 1 theta).re=Real.cos theta ∧
        (circleMap 0 1 theta).im=Real.sin theta := by
      simp [circleMap_zero,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
    rw [density_identity d q mu L _ (by rw [hz.1,hz.2]; exact Real.cos_sq_add_sin_sq theta),hz.1]
  have hc : Continuous (fun theta : ℝ => numberDensity d q mu L (circleMap 0 1 theta)) := by
    unfold numberDensity
    fun_prop
  have hr : (∫theta in 0..(2*Real.pi),numberDensity d q mu L (circleMap 0 1 theta)).re=
      ∫theta in 0..(2*Real.pi),(numberDensity d q mu L (circleMap 0 1 theta)).re := by
    simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
    exact (integral_re (hc.intervalIntegrable _ _ |>.1)).symm
  change 0≤(∫theta in 0..(2*Real.pi),numberDensity d q mu L (circleMap 0 1 theta)).re at hp
  rw [hr] at hp
  simp_rw [hd] at hp
  rw [intervalIntegral.integral_const_mul] at hp
  have hpos := nonneg_of_mul_nonneg_right hp (by positivity : 0<Real.exp (-d/2)/2)
  have he : IntervalIntegrable (fun theta : ℝ => Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*
      (mu+L*Real.cos theta)^4) volume 0 (2*Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have ht : IntervalIntegrable (fun theta : ℝ => (2*d*(Real.cos theta)^2-q*Real.cos theta)*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*(mu+L*Real.cos theta)^4)
      volume 0 (2*Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi : (∫theta in 0..(2*Real.pi),(2*d*(Real.cos theta)^2-q*Real.cos theta-d+4)*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*(mu+L*Real.cos theta)^4)=
      KFCausalAngularQuarticQuadraticTilt.tilt 0 d q mu L-
        (d-4)*KFCausalAngularQuarticQuadraticTilt.energy 0 d q mu L := by
    unfold KFCausalAngularQuarticQuadraticTilt.tilt KFCausalAngularQuarticQuadraticTilt.energy
      KFCausalAngularQuarticGaussianSmoothing.weight
    simp only [mul_zero,zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub ht (he.const_mul (d-4))]
    apply intervalIntegral.integral_congr
    intro theta _
    ring
  rw [hi] at hpos
  linarith

theorem weight_cubature (sigma x : ℝ) (hs : 0≤sigma) :
    KFCausalAngularQuarticGaussianSmoothing.weight sigma x=
      (x+Real.sqrt (3*sigma))^4/6+2*x^4/3+(x-Real.sqrt (3*sigma))^4/6 := by
  have hr : (Real.sqrt (3*sigma))^2=3*sigma := Real.sq_sqrt (by positivity)
  calc
    _ = x^4+2*(Real.sqrt (3*sigma))^2*x^2+(Real.sqrt (3*sigma))^4/3 := by
      rw [show (Real.sqrt (3*sigma))^4=((Real.sqrt (3*sigma))^2)^2 by ring,hr]
      unfold KFCausalAngularQuarticGaussianSmoothing.weight
      ring
    _ = _ := by ring

private theorem weighted_cubature (sigma mu L : ℝ) (hs : 0≤sigma)
    (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ theta in 0..(2*Real.pi),f theta*KFCausalAngularQuarticGaussianSmoothing.weight
      sigma (mu+L*Real.cos theta))=
      (1/6:ℝ)*(∫theta in 0..(2*Real.pi),f theta*(mu+Real.sqrt (3*sigma)+L*Real.cos theta)^4)+
      (2/3:ℝ)*(∫theta in 0..(2*Real.pi),f theta*(mu+L*Real.cos theta)^4)+
      (1/6:ℝ)*(∫theta in 0..(2*Real.pi),f theta*(mu-Real.sqrt (3*sigma)+L*Real.cos theta)^4) := by
  have hi (m : ℝ) : IntervalIntegrable (fun theta : ℝ => f theta*(m+L*Real.cos theta)^4)
      volume 0 (2*Real.pi) := (hf.mul (by fun_prop)).intervalIntegrable _ _
  rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_add ((hi _).const_mul (1/6)) ((hi _).const_mul (2/3)),
    ←intervalIntegral.integral_add (((hi _).const_mul (1/6)).add ((hi _).const_mul (2/3)))
      ((hi _).const_mul (1/6))]
  apply intervalIntegral.integral_congr
  intro theta _
  dsimp only
  rw [weight_cubature sigma _ hs]
  ring

theorem smoothed_bound (sigma d q mu L : ℝ) (hs : 0≤sigma) :
    (d-4)*KFCausalAngularQuarticQuadraticTilt.energy sigma d q mu L ≤
      KFCausalAngularQuarticQuadraticTilt.tilt sigma d q mu L := by
  have he := weighted_cubature sigma mu L hs
    (fun theta => Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)) (by fun_prop)
  have ht := weighted_cubature sigma mu L hs
    (fun theta => (2*d*(Real.cos theta)^2-q*Real.cos theta)*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)) (by fun_prop)
  have h0 (x : ℝ) : KFCausalAngularQuarticGaussianSmoothing.weight 0 x=x^4 := by
    simp [KFCausalAngularQuarticGaussianSmoothing.weight]
  have he' : KFCausalAngularQuarticQuadraticTilt.energy sigma d q mu L=
      (1/6:ℝ)*KFCausalAngularQuarticQuadraticTilt.energy 0 d q (mu+Real.sqrt (3*sigma)) L+
      (2/3:ℝ)*KFCausalAngularQuarticQuadraticTilt.energy 0 d q mu L+
      (1/6:ℝ)*KFCausalAngularQuarticQuadraticTilt.energy 0 d q (mu-Real.sqrt (3*sigma)) L := by
    simpa only [KFCausalAngularQuarticQuadraticTilt.energy,h0] using he
  have ht' : KFCausalAngularQuarticQuadraticTilt.tilt sigma d q mu L=
      (1/6:ℝ)*KFCausalAngularQuarticQuadraticTilt.tilt 0 d q (mu+Real.sqrt (3*sigma)) L+
      (2/3:ℝ)*KFCausalAngularQuarticQuadraticTilt.tilt 0 d q mu L+
      (1/6:ℝ)*KFCausalAngularQuarticQuadraticTilt.tilt 0 d q (mu-Real.sqrt (3*sigma)) L := by
    simpa only [KFCausalAngularQuarticQuadraticTilt.tilt,h0] using ht
  rw [he',ht']
  nlinarith [unsmoothed_bound d q (mu+Real.sqrt (3*sigma)) L,
    unsmoothed_bound d q mu L,unsmoothed_bound d q (mu-Real.sqrt (3*sigma)) L]

#print axioms amplitude_circle
#print axioms density_identity
#print axioms unsmoothed_bound
#print axioms weight_cubature
#print axioms smoothed_bound
end
end UnifiedTheory.Audit.KFCausalAngularQuarticHardy
