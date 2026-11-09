/- The positive radial term in the quadratic angular tilt follows from
the actual entire circle number form. Multiplication by z removes
the one negative Fourier mode of the real quadratic amplitude. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticHardy
import UnifiedTheory.Audit.KFCausalAngularMassQuadraticTilt

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularMassHardy
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

open KFCausalAngularQuarticHardy (exponent amplitude amplitude_circle)

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

def numberDensity (d q mu L : ℝ) (z : ℂ) : ℂ :=
  conj (Complex.exp ((exponent d q).eval z)*(amplitude mu L).eval z)*
    (z*Complex.exp ((exponent d q).eval z)*
      ((exponent d q).derivative.eval z*(amplitude mu L).eval z+
        (amplitude mu L).derivative.eval z))

theorem density_identity (d q mu L : ℝ) (z : ℂ) (hz : z.re^2+z.im^2=1) :
    (numberDensity d q mu L z).re=Real.exp (-d/2)/2*
      ((2*d*z.re^2-q*z.re-d+2)*Real.exp (d*z.re^2-q*z.re)*(mu+L*z.re)^2) := by
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
  have hB : (amplitude mu L).eval z=z*(W:ℂ) := amplitude_circle mu L z hz
  have hDB : (amplitude mu L).derivative.eval z=(mu:ℂ)+(L:ℂ)*z :=
    amplitude_derivative mu L z
  have hpair :
      conj ((amplitude mu L).eval z)*
        (z*((exponent d q).derivative.eval z*(amplitude mu L).eval z+
          (amplitude mu L).derivative.eval z))=
        (W:ℂ)^2*(z*(exponent d q).derivative.eval z)+
          (W:ℂ)*((mu:ℂ)+(L:ℂ)*z) := by
    rw [hB,hDB]
    simp only [map_mul,Complex.conj_ofReal]
    calc
      _ = (conj z*z)*(W:ℂ)^2*(z*(exponent d q).derivative.eval z)+
          (conj z*z)*(W:ℂ)*((mu:ℂ)+(L:ℂ)*z) := by ring
      _ = _ := by rw [hzz]; ring
  have hexp : conj (Complex.exp ((exponent d q).eval z))*Complex.exp ((exponent d q).eval z)=
      ((Real.exp (-d/2)*Real.exp (d*z.re^2-q*z.re):ℝ):ℂ) := by
    rw [Complex.conj_mul',Complex.norm_exp,←Complex.ofReal_pow,←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [hA,Real.exp_add]
  have he : numberDensity d q mu L z=
      (conj (Complex.exp ((exponent d q).eval z))*Complex.exp ((exponent d q).eval z))*
        (conj ((amplitude mu L).eval z)*
          (z*((exponent d q).derivative.eval z*(amplitude mu L).eval z+
            (amplitude mu L).derivative.eval z))) := by
    unfold numberDensity
    rw [map_mul]
    ring
  rw [he,hexp,hpair]
  simp only [←Complex.ofReal_pow]
  simp only [Complex.re_ofReal_mul,Complex.add_re,hDA,Complex.ofReal_re]
  dsimp only [W]
  ring

theorem unsmoothed_bound (d q mu L : ℝ) :
    (d-2)*KFCausalAngularMassQuadraticTilt.energy 0 d q mu L ≤
      KFCausalAngularMassQuadraticTilt.tilt 0 d q mu L := by
  have hp := KFCausalAngularEntireNumber.number_nonnegative (exponent d q) (amplitude mu L) 1
  have hd (theta : ℝ) : (numberDensity d q mu L (circleMap 0 1 theta)).re=
      Real.exp (-d/2)/2*((2*d*(Real.cos theta)^2-q*Real.cos theta-d+2)*
        Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*(mu+L*Real.cos theta)^2) := by
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
      (mu+L*Real.cos theta)^2) volume 0 (2*Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have ht : IntervalIntegrable (fun theta : ℝ => (2*d*(Real.cos theta)^2-q*Real.cos theta)*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*(mu+L*Real.cos theta)^2)
      volume 0 (2*Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi : (∫theta in 0..(2*Real.pi),(2*d*(Real.cos theta)^2-q*Real.cos theta-d+2)*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*(mu+L*Real.cos theta)^2)=
      KFCausalAngularMassQuadraticTilt.tilt 0 d q mu L-
        (d-2)*KFCausalAngularMassQuadraticTilt.energy 0 d q mu L := by
    unfold KFCausalAngularMassQuadraticTilt.tilt KFCausalAngularMassQuadraticTilt.energy
      KFCausalAngularMassGaussianSmoothing.weight
    simp only [add_zero]
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub ht (he.const_mul (d-2))]
    apply intervalIntegral.integral_congr
    intro theta _
    ring
  rw [hi] at hpos
  linarith

theorem weight_cubature (sigma x : ℝ) (hs : 0≤sigma) :
    KFCausalAngularMassGaussianSmoothing.weight sigma x=
      (x+Real.sqrt sigma)^2/2+(x-Real.sqrt sigma)^2/2 := by
  have hr : (Real.sqrt sigma)^2=sigma := Real.sq_sqrt hs
  unfold KFCausalAngularMassGaussianSmoothing.weight
  nlinarith

private theorem weighted_cubature (sigma mu L : ℝ) (hs : 0≤sigma)
    (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ theta in 0..(2*Real.pi),f theta*KFCausalAngularMassGaussianSmoothing.weight
      sigma (mu+L*Real.cos theta))=
      (1/2:ℝ)*(∫theta in 0..(2*Real.pi),f theta*(mu+Real.sqrt sigma+L*Real.cos theta)^2)+
      (1/2:ℝ)*(∫theta in 0..(2*Real.pi),f theta*(mu-Real.sqrt sigma+L*Real.cos theta)^2) := by
  have hi (m : ℝ) : IntervalIntegrable (fun theta : ℝ => f theta*(m+L*Real.cos theta)^2)
      volume 0 (2*Real.pi) := (hf.mul (by fun_prop)).intervalIntegrable _ _
  rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_add ((hi _).const_mul (1/2)) ((hi _).const_mul (1/2))]
  apply intervalIntegral.integral_congr
  intro theta _
  dsimp only
  rw [weight_cubature sigma _ hs]
  ring

theorem smoothed_bound (sigma d q mu L : ℝ) (hs : 0≤sigma) :
    (d-2)*KFCausalAngularMassQuadraticTilt.energy sigma d q mu L ≤
      KFCausalAngularMassQuadraticTilt.tilt sigma d q mu L := by
  have he := weighted_cubature sigma mu L hs
    (fun theta => Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)) (by fun_prop)
  have ht := weighted_cubature sigma mu L hs
    (fun theta => (2*d*(Real.cos theta)^2-q*Real.cos theta)*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)) (by fun_prop)
  have h0 (x : ℝ) : KFCausalAngularMassGaussianSmoothing.weight 0 x=x^2 := by
    simp [KFCausalAngularMassGaussianSmoothing.weight]
  have he' : KFCausalAngularMassQuadraticTilt.energy sigma d q mu L=
      (1/2:ℝ)*KFCausalAngularMassQuadraticTilt.energy 0 d q (mu+Real.sqrt sigma) L+
      (1/2:ℝ)*KFCausalAngularMassQuadraticTilt.energy 0 d q (mu-Real.sqrt sigma) L := by
    simpa only [KFCausalAngularMassQuadraticTilt.energy,h0] using he
  have ht' : KFCausalAngularMassQuadraticTilt.tilt sigma d q mu L=
      (1/2:ℝ)*KFCausalAngularMassQuadraticTilt.tilt 0 d q (mu+Real.sqrt sigma) L+
      (1/2:ℝ)*KFCausalAngularMassQuadraticTilt.tilt 0 d q (mu-Real.sqrt sigma) L := by
    simpa only [KFCausalAngularMassQuadraticTilt.tilt,h0] using ht
  rw [he',ht']
  nlinarith [unsmoothed_bound d q (mu+Real.sqrt sigma) L,
    unsmoothed_bound d q (mu-Real.sqrt sigma) L]

#print axioms density_identity
#print axioms unsmoothed_bound
#print axioms weight_cubature
#print axioms smoothed_bound
end
end UnifiedTheory.Audit.KFCausalAngularMassHardy
